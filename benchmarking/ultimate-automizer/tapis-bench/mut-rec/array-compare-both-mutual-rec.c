//
// Copyright (c) 2024 Wael-Amine Boutglay
//

extern void abort(void);

extern void __assert_fail(const char *, const char *, unsigned int,
                          const char *) __attribute__ ((__nothrow__, __leaf__)) __attribute__ ((__noreturn__));

void reach_error() { __assert_fail("0", "array-compare-both-mutual-rec.c", 3, "reach_error"); }

extern void abort(void);

void assume_abort_if_not(int cond) {
  if(!cond) { abort(); }
}

void __VERIFIER_assert(int cond) {
  if(!(cond)) {
    ERROR:
    {
      reach_error();
      abort();
    }
  }
}

extern int __VERIFIER_nondet_int();

typedef enum {
  true = 1,
  false = 0
} bool;

bool rec_array_compare_left(int array1[], int array2[], int i, int j, int N);

bool rec_array_compare_right(int array1[], int array2[], int i, int j, int N) {
  if(i < N && j > 0 && i <= j) {
    if(array1[j - 1] != array2[j - 1]) {
      return false;
    }
    return rec_array_compare_left(array1, array2, i, j - 1, N);
  }
  return true;
}

bool rec_array_compare_left(int array1[], int array2[], int i, int j, int N) {
  if(i < N && j > 0 && i <= j) {
    if(array1[i] != array2[i]) {
      return false;
    }
    return rec_array_compare_right(array1, array2, i + 1, j, N);
  }
  return true;
}

int main() {

  //*-- precondition
  int N = __VERIFIER_nondet_int();
  assume_abort_if_not(N > 0);
  int array1[N];
  int array2[N];
  for(int k = 0; k < N; k++) {
    array1[k] = __VERIFIER_nondet_int();
    array2[k] = __VERIFIER_nondet_int();
  }
  //*-- computation
  bool equal = rec_array_compare_left(array1, array2, 0, N, N);
  //*-- specification
  if(equal == true) {
    for(int k = 0; k < N; k++) {
      __VERIFIER_assert(array1[k] == array2[k]);
    }
  }

  return 0;
}
