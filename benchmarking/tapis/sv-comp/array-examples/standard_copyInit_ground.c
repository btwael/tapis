int main() {
  int N;
  assume(N > 0);
  int a[N];
  int b[N];
  int i = 0;
  while(i < N) {
    a[i] = 42;
    i = i + 1;
  }

  for(i = 0; i < N; i++) {
    b[i] = a[i];
  }

  for(int x = 0; x < N; x++) {
    assert(b[x] == 42);
  }
  return 0;
}
