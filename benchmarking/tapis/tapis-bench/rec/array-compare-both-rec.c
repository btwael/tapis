//
// Copyright (c) 2023 Wael-Amine Boutglay
//

bool rec_array_compare(int array1[], int array2[], unsigned int i, int j, unsigned int N) {
  if(i < N && j > 0 && i <= j) {
    if(array1[i] != array2[i] || array1[j - 1] != array2[j - 1]) {
      return false;
    }
    return rec_array_compare(array1, array2, i + 1, j - 1, N);
  }
  return true;
}

int main() {

  //*-- precondition
  unsigned int N;
  assume(N > 0);
  int array1[N];
  int array2[N];
  //*-- computation
  bool equal = rec_array_compare(array1, array2, 0, N, N);
  //*-- specification
  if(equal == true) {
    for(unsigned int k = 0; k < N; k++) {
      assert(array1[k] == array2[k]);
    }
  }

  return 0;
}
