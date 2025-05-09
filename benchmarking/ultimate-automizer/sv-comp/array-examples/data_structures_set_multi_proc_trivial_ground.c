extern void abort(void);

extern void __assert_fail(const char *, const char *, unsigned int,
                          const char *) __attribute__ ((__nothrow__, __leaf__)) __attribute__ ((__noreturn__));

void reach_error() { __assert_fail("0", "data_structures_set_multi_proc_trivial_ground.c", 3, "reach_error"); }

void __VERIFIER_assert(int cond) {
  if(!(cond)) {
    ERROR:
    {
      reach_error();
      abort();
    }
  }
}

extern int __VERIFIER_nondet_int();

// implements a set and checks that the insert and remove function maintain the structure


int insert(int set[], int size, int value) {
  set[size] = value;
  return size + 1;
}

int elem_exists(int set[], int size, int value) {
  int i;
  for(i = 0; i < size; i++) {
    if(set[i] == value) return 1;
  }
  return 0;
}

int main() {
  int SIZE = __VERIFIER_nondet_int();
  int n = 0;
  int set[SIZE];

  // this is trivial
  int x;
  int y;

  for(x = 0; x < SIZE; x++) {
    set[x] = __VERIFIER_nondet_int();
  }

  for(x = 0; x < n; x++) {
    for(y = x + 1; y < n; y++) {
      __VERIFIER_assert(set[x] != set[y]);
    }
  }

  // we have an array of values to insert
  int values[SIZE];

  // insert them in the array -- note that nothing ensures that values is not containing duplicates!
  int v;
  for(v = 0; v < SIZE; v++) {
    values[v] = __VERIFIER_nondet_int();
  }
  for(v = 0; v < SIZE; v++) {
    // check if the element exists, if not insert it.
    if(elem_exists(set, n, values[v])) {
      // parametes are passed by reference
      n = insert(set, n, values[v]);
    }
    for(x = 0; x < n; x++) {
      for(y = x + 1; y < n; y++) {
        __VERIFIER_assert(set[x] != set[y]);
      }
    }
  }

  // this is not trivial!
  for(x = 0; x < n; x++) {
    for(y = x + 1; y < n; y++) {
      __VERIFIER_assert(set[x] != set[y]);
    }
  }
  return 0;
}
