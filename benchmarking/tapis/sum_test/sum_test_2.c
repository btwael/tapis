
void assume(int);
void assert_exp(const char *);

int main() {

int N;
assume(N > 0);
int a[N], b[N];
assume(a[0] == 1);
long s = 0;

int i;
for (i = 0; i < N; i++) {
    s = s + a[i] - b[i];
}
for (i = 0; i < N; i++) {
    s = s + b[i];
}


assert_exp("(= s (sum a 0 N))");
  return 0;
}