int main() {
  int N;
  assume(N > 0);
  int a[N];
  bool b[N];
  int i = 0;

  i = 0;
  while(i < N) {
    if(a[i] >= 0) b[i] = true;
    else b[i] = false;
    i = i + 1;
  }
  bool f = true;
  i = 0;
  while(i < N) {
    if(a[i] >= 0 && !b[i]) f = false;
    if(a[i] < 0 && b[i]) f = false;
    i = i + 1;
  }
  assert(f);
  return 0;
}
