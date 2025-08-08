
void assume(int);
void assert_exp(const char *);

int main() {

int N;
assume(N > 0);
int a[N], b[N];
long s = 0;

int i;
for (i = 0; i < N; i++) {
    s = s + a[i];
    b[i] = s;
}

// assert_exp("(= s (sum a 0 N))");
assert_exp("(forall ((k Int)) (=> (and (>= k 0) (< k N)) (= ([] b k) (sum a 0  k))))");

  return 0;
}