
void assume(int);
void assert_exp(const char *);

int main() {

int N;
assume(N > 0);
int a[N], b[N];
long s = 0;

int i;
for (i = 0; i < N; i++) {
    b[i] = s;
    s = s + a[i];
// assert_exp("(= ([] b i) (sum a 0 (+ i 1)))");


}

// assert_exp("(= s (sum a 0 N))");
assert_exp("(forall ((k Int)) (=> (and (>= k 0) (< k N)) (= ([] b k) (sum a 0 k ))))");

  return 0;
}