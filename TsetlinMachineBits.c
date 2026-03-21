/*

Copyright (c) 2019 Ole-Christoffer Granmo

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

This code implements a multiclass version of the Tsetlin Machine from paper arXiv:1804.01508
https://arxiv.org/abs/1804.01508

*/

#include <stdio.h>
#include <stdlib.h>
#include <limits.h>
#include <math.h>
#include <string.h>

#include "fast_rand.h"

#include "TsetlinMachineBits.h"

struct TsetlinMachine *CreateTsetlinMachine()
{
	/* Set up the Tsetlin Machine structure */

	struct TsetlinMachine *tm = (void *)malloc(sizeof(struct TsetlinMachine));

	tm_initialize(tm);

	return tm;
}

// 32 bits here (unsigned int) for 32 automata (1 chunk), each wth 8 state bits
void tm_initialize(struct TsetlinMachine *tm)
{
	/* Set up the Tsetlin Machine structure */

	for (int j = 0; j < CLAUSES; ++j) {
		for (int k = 0; k < LA_CHUNKS; ++k) {
			for (int b = 0; b < STATE_BITS-1; ++b) {											
				(*tm).ta_state[j][k][b] = ~0;
			}
			(*tm).ta_state[j][k][STATE_BITS-1] = 0;
		}
	}
}

static inline void tm_initialize_random_streams(struct TsetlinMachine *tm)
{
	// Initialize all bits to zero	
	memset((*tm).feedback_to_la, 0, LA_CHUNKS*sizeof(unsigned int));

	int n = 2 * FEATURES;
	double p = 1.0 / S;
	int active = normal(n * p, n * p * (1 - p));
	active = active >= n ? n : active;
	active = active < 0 ? 0 : active;
	while (active--) {
		int f = fast_rand() % (2 * FEATURES);
		while ((*tm).feedback_to_la[f / INT_SIZE] & (1 << (f % INT_SIZE))) {
			f = fast_rand() % (2 * FEATURES);
	    	}
		(*tm).feedback_to_la[f / INT_SIZE] |= 1 << (f % INT_SIZE);
	}
}

// Increment the states of each of those 32 Tsetlin Automata flagged in the active bit vector.
static inline void tm_inc(struct TsetlinMachine *tm, int clause, int chunk, unsigned int active)
{
	unsigned int carry, carry_next;

	carry = active;
	for (int b = 0; b < STATE_BITS; ++b) {
		if (carry == 0)
			break;

		carry_next = (*tm).ta_state[clause][chunk][b] & carry; // Sets carry bits (overflow) passing on to next bit
		(*tm).ta_state[clause][chunk][b] = (*tm).ta_state[clause][chunk][b] ^ carry; // Performs increments with XOR
		carry = carry_next;
	}
    // This undoes any overflows by setting all bits to 1 where carry == 1
	if (carry > 0) {
		for (int b = 0; b < STATE_BITS; ++b) {
			(*tm).ta_state[clause][chunk][b] |= carry;
		}
	} 	
}

// Decrement the states of each of those 32 Tsetlin Automata flagged in the active bit vector.
static inline void tm_dec(struct TsetlinMachine *tm, int clause, int chunk, unsigned int active)
{
	unsigned int carry, carry_next;

	carry = active;
	for (int b = 0; b < STATE_BITS; ++b) {
		if (carry == 0)
			break;

		carry_next = (~(*tm).ta_state[clause][chunk][b]) & carry; // Sets carry bits (overflow) passing on to next bit
		(*tm).ta_state[clause][chunk][b] = (*tm).ta_state[clause][chunk][b] ^ carry; // Performs increments with XOR
		carry = carry_next;
	}
    // This undoes any underflows by setting all bits to 0 where borrow == 1
	if (carry > 0) {
		for (int b = 0; b < STATE_BITS; ++b) {
			(*tm).ta_state[clause][chunk][b] &= ~carry;
		}
	} 
}

/* Sum up the votes for each class */
static inline int sum_up_class_votes(struct TsetlinMachine *tm)
{
	int class_sum = 0;

	for (int j = 0; j < CLAUSE_CHUNKS; j++) {
		class_sum += __builtin_popcount((*tm).clause_output[j] & 0x55555555); // 0101
		class_sum -= __builtin_popcount((*tm).clause_output[j] & 0xaaaaaaaa); // 1010
	}

	class_sum = (class_sum > THRESHOLD) ? THRESHOLD : class_sum;
	class_sum = (class_sum < -THRESHOLD) ? -THRESHOLD : class_sum;

	return class_sum;
}

/* Calculate the output of each clause using the actions of each Tsetline Automaton. */
static inline void tm_calculate_clause_output(struct TsetlinMachine *tm, unsigned int Xi[], int predict)
{
	memset((*tm).clause_output, 0, CLAUSE_CHUNKS*sizeof(unsigned int));

	for (int j = 0; j < CLAUSES; j++) {
		unsigned int output = 1;
		unsigned int all_exclude = 1;

		// First LA_CHUNKS-1 words
		for (int k = 0; k < LA_CHUNKS-1; k++) {
			//                                included              literal                 included
			output = output && ((*tm).ta_state[j][k][STATE_BITS-1] & Xi[k]) == (*tm).ta_state[j][k][STATE_BITS-1];

			if (!output) {
				break;
			}
			//            current val                  excluded
			all_exclude = all_exclude && ((*tm).ta_state[j][k][STATE_BITS-1] == 0);
		}

        // Last LA_CHUNKS word with filter

        // These bitwise filter off stragglng values if % INTSIZE != 0
		output = output &&
			((*tm).ta_state[j][LA_CHUNKS-1][STATE_BITS-1] & Xi[LA_CHUNKS-1] & FILTER) ==
			((*tm).ta_state[j][LA_CHUNKS-1][STATE_BITS-1] & FILTER);

		all_exclude = all_exclude && (((*tm).ta_state[j][LA_CHUNKS-1][STATE_BITS-1] & FILTER) == 0);
        
        // This prevents the clause output from being 1 if all literals excluded and inference is being performed
		output = output && !(predict == PREDICT && all_exclude == 1);
	
	    // Set Relevent Output
		if (output) {
			unsigned int clause_chunk = j / INT_SIZE;
			unsigned int clause_chunk_pos = j % INT_SIZE;

 			(*tm).clause_output[clause_chunk] |= (1 << clause_chunk_pos);
 		}
 	}
}

/******************************************/
/*** Online Training of Tsetlin Machine ***/
/******************************************/

// The Tsetlin Machine can be trained incrementally, one training example at a time.
// Use this method directly for online and incremental training.

void tm_update(struct TsetlinMachine *tm, unsigned int Xi[], int target)
{
	/*******************************/
	/*** Calculate Clause Output ***/
	/*******************************/

	tm_calculate_clause_output(tm, Xi, UPDATE);

	/***************************/
	/*** Sum up Clause Votes ***/
	/***************************/

	int class_sum = sum_up_class_votes(tm);

	/*********************************/
	/*** Train Individual Automata ***/
	/*********************************/
	
	// Calculate feedback to clauses

    // Feedback Part 2 probability
	float p = (1.0/(THRESHOLD*2))*(THRESHOLD + (1 - 2*target)*class_sum);
	memset((*tm).feedback_to_clauses, 0, CLAUSE_CHUNKS*sizeof(int));
  	for (int j = 0; j < CLAUSES; j++) {
    	unsigned int clause_chunk = j / INT_SIZE;
        unsigned int clause_chunk_pos = j % INT_SIZE;

        (*tm).feedback_to_clauses[clause_chunk] |= (((float)fast_rand())/((float)FAST_RAND_MAX) <= p) << clause_chunk_pos;
    }

	for (int j = 0; j < CLAUSES; j++) {
		unsigned int clause_chunk = j / INT_SIZE;
		unsigned int clause_chunk_pos = j % INT_SIZE;

        // Skip clause if feedback probability
		if (!((*tm).feedback_to_clauses[clause_chunk] & (1 << clause_chunk_pos))) {
			continue;
		}
		
		// inverse the decision for negatively-voting clauses
		if ((2*target-1) * (1 - 2 * (j & 1)) == -1) {
			// If clause = 1
			if (((*tm).clause_output[clause_chunk] & (1 << clause_chunk_pos)) > 0) {
				// Type II Feedback

				for (int k = 0; k < LA_CHUNKS; ++k) {
					// if            (Lit == 0 &               Excluded)
					tm_inc(tm, j, k, (~Xi[k]) & (~(*tm).ta_state[j][k][STATE_BITS-1]));
				}
			}
		} else if ((2*target-1) * (1 - 2 * (j & 1)) == 1) {
			// Type I Feedback

			tm_initialize_random_streams(tm);
            
            // If clause = 1
			if (((*tm).clause_output[clause_chunk] & (1 << clause_chunk_pos)) > 0) {
				for (int k = 0; k < LA_CHUNKS; ++k) {
					#ifdef BOOST_TRUE_POSITIVE_FEEDBACK
					    // if literal == 1
		 				tm_inc(tm, j, k, Xi[k]);
					#else
		 				// if literal == 1 && feedback high == true
						tm_inc(tm, j, k, Xi[k] & (~tm->feedback_to_la[k]));
					#endif
		 			// if literal == 0 && feedback low == true
		 			tm_dec(tm, j, k, (~Xi[k]) & tm->feedback_to_la[k]);
				}
			} else {
				// Clause == 0
				for (int k = 0; k < LA_CHUNKS; ++k) {
					// if feedback low = true
					tm_dec(tm, j, k, tm->feedback_to_la[k]);
				}
			}
		}
	}
}

int tm_score(struct TsetlinMachine *tm, unsigned int Xi[]) {
	/*******************************/
	/*** Calculate Clause Output ***/
	/*******************************/

	tm_calculate_clause_output(tm, Xi, PREDICT);

	/***************************/
	/*** Sum up Clause Votes ***/
	/***************************/

	return sum_up_class_votes(tm);
}

int tm_get_state(struct TsetlinMachine *tm, int clause, int la)
{
	int la_chunk = la / INT_SIZE;
	int chunk_pos = la % INT_SIZE;

	int state = 0;
	for (int b = 0; b < STATE_BITS; ++b) {
		if ((*tm).ta_state[clause][la_chunk][b] & (1 << chunk_pos)) {
			state |= 1 << b; 
		}
	}

	return state;
}

int tm_action(struct TsetlinMachine *tm, int clause, int la)
{
	int la_chunk = la / INT_SIZE;
	int chunk_pos = la % INT_SIZE;

	return ((*tm).ta_state[clause][la_chunk][STATE_BITS-1] & (1 << chunk_pos)) > 0;
}


