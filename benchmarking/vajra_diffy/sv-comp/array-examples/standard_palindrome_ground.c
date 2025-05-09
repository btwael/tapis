extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
extern int __VERIFIER_nondet_int();

int N;

int main() {
  N = __VERIFIER_nondet_int();
  int A[N];
  int i;
  for(i = 0; i < N; i++) {
    A[i] = __VERIFIER_nondet_int();
  }
  for(i = 0; i < N / 2; i++) {
    A[i] = A[N - i - 1];
  }

  int x;
  for(x = 0; x < N / 2; x++) {
    __VERIFIER_assert(A[x] == A[N - x - 1]);
  }
  return 0;
}
