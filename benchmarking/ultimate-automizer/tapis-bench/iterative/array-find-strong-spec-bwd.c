//
// Copyright (c) 2024 Wael-Amine Boutglay
//

extern void abort(void);

extern void __assert_fail(const char *, const char *, unsigned int,
                          const char *) __attribute__ ((__nothrow__, __leaf__)) __attribute__ ((__noreturn__));

void reach_error() { __assert_fail("0", "array-find-strong-spec-bwd.c", 3, "reach_error"); }

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

int main() {

  //*-- precondition
  int N = __VERIFIER_nondet_int();
  assume_abort_if_not(N > 0);
  int array[N];
  for(int k = 0; k < N; k++) {
    array[k] = __VERIFIER_nondet_int();
  }
  int v = __VERIFIER_nondet_int();
  //*-- computation
  int idx = -1;
  int j = N;
  while(j > 0) {
    if(array[j - 1] == v) {
      idx = j - 1;
    }
    j--;
  }
  //*-- specification
  if(idx != -1) {
    __VERIFIER_assert(v == array[idx]);
  } else {
    for(int k = 0; k < N; k++) {
      __VERIFIER_assert(v != array[k]);
    }
  }

  return 0;
}
