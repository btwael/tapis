extern void abort(void);

extern void __assert_fail(const char *, const char *, unsigned int,
                          const char *) __attribute__ ((__nothrow__, __leaf__)) __attribute__ ((__noreturn__));

void reach_error() { __assert_fail("0", "array_min_and_copy_shift_sum_add.c", 3, "reach_error"); }

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
  int N = __VERIFIER_nondet_int();
  assume_abort_if_not(N > 0);
  int k = 0;
  int a[N + 1];
  int b[N];

  int j = __VERIFIER_nondet_int();
  int i;
  for(i = 0; i < N; i++) {
    if(j > a[i]) {
      j = a[i];
    }
  }

  for(i = 0; i < N; i++) {
    b[i] = a[i] - j;
  }

  for(i = 0; i < N; i++) {
    k = k + b[i] + i;
  }

  __VERIFIER_assert(k >= 0);
  return 0;
}
