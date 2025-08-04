
void assume(int);
void assert_exp(const char *);

int main() {

int N;
assume(N > 0);
int a[N], b[N];
int s = 0;

int s_initial = s;
int acc_s_0 = 0; int acc_s_1 = 0;
int i;

for (i = 0; i < N; i++) {
    acc_s_0 = acc_s_0 + a[i];
    acc_s_1 = acc_s_1 + b[i];
    s = s_initial + acc_s_0 - acc_s_1;
}

assert(s == 0);
  return 0;
}