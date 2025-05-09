extern void abort(void);

extern void __assert_fail(const char *, const char *, unsigned int,
                          const char *) __attribute__ ((__nothrow__, __leaf__)) __attribute__ ((__noreturn__));

void reach_error() { __assert_fail("0", "array_init_pair_symmetr2.c", 3, "reach_error"); }

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
  int a[N];
  int b[N];

  int i;
  for(i = 0; i < N; i++) {
    int x = __VERIFIER_nondet_int();
    int y = __VERIFIER_nondet_int();
    assume_abort_if_not(x > y);
    a[i] = x;
    b[i] = y;
  }

  int c[N];
  for(i = 0; i < N; i++) {
    c[i] = a[i] - b[i];
  }

  for(int k = 1; k < N; k++) {
    __VERIFIER_assert(c[k] > 0);
  }
  return 0;
}
