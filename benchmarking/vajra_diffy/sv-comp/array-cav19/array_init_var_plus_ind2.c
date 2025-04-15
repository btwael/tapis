extern void __VERIFIER_error() __attribute__ ((__noreturn__));

void __VERIFIER_assert(int cond) {
  if(!(cond)) {
    ERROR:
    __VERIFIER_error();
  }
}

extern int __VERIFIER_nondet_int();

int N;

int main() {
  N = __VERIFIER_nondet_int();
  int j = 0;
  int k = 0;
  int a[N];

  int br[1];
  br[0] = 0;

  int i;
  for(i = 0; i < N; i++) {
    int x = __VERIFIER_nondet_int();
    if(x != 0) {
      br[0] = 1;
    }
    if(br[0] == 0) {
      a[i] = j;
      j = j + i;
      k = k - i;
    }
  }

  for(int l = 1; l < i; l++) {
    __VERIFIER_assert(a[l] >= k);
  }
  return 0;
}

