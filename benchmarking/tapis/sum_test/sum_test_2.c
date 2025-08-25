int main() {

int N;
assume(N > 0);
int a[N]; 
int  b[N];
long s = 0;

int i;



for (i = 0; i < N; i++) {
    b[i] = s;
    s = s + a[i];

}

// for (i = 0; i < N; i++) {
//     // b[i] = s;
//     s = s - a[i];

// }



assert_exp("(forall ((k Int)) (=> (and (>= k 0) (< k N)) (= ([] b k) (sum a 0 k))))");

// assert_exp("(= s 0)");

  return 0;
}