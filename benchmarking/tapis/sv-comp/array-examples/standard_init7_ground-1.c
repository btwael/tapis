int main() {
  int N;
  assume(N > 0);
  int a[N];
  int i = 0;
  while(i < N) {
    a[i] = 42;
    i = i + 1;
  }
  i = 0;
  while(i < N) {
    a[i] = 43;
    i = i + 1;
  }
  i = 0;
  while(i < N) {
    a[i] = 44;
    i = i + 1;
  }
  i = 0;
  while(i < N) {
    a[i] = 45;
    i = i + 1;
  }
  i = 0;
  while(i < N) {
    a[i] = 46;
    i = i + 1;
  }
  i = 0;
  while(i < N) {
    a[i] = 47;
    i = i + 1;
  }
  i = 0;
  while(i < N) {
    a[i] = 48;
    i = i + 1;
  }

  for(int x = 0; x < N; x++) {
    assert(a[x] == 47);
  }
  return 0;
}
