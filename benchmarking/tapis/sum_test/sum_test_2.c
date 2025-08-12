int main() {

int N;
assume(N > 0);
int a[N];
long s = 0;

int i;

// for (int k = 0; k < N; k++) {
//   assume(a[k] == 1);

// }

for (i = 0; i < N; i++) {
    s = s + a[i];
// assert_exp("(= ([] b i) (sum a 0 (+ i 1)))");

}

// assert_exp("(forall ((k Int)) (=> (and (>= k 0) (< k N)) (= ([] b k) (sum a 0 (+ k ))))");

assert_exp("(= s (sum a 0 N))");

  return 0;
}