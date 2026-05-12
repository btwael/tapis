# Tapis
Tapis is a data-driven verification tool for iterative and recursive array-manipulating programs (with parametric size), based on the method presented in the CAV'25 paper _Data-driven Verification of Procedural Programs with Integer Arrays_.
This repository also includes all the benchmarks and scripts used in the experimental study presented in the paper.

> [!important]
> For the version used in our CAV'25 paper, check out this branch '[artifact/cav-25](https://github.com/btwael/tapis/tree/artifact/cav-25)'

**Table of content:**
 - [Overview](#overview)
 - [Installation](#installation)
   - [Dependencies](#dependencies)
   - [Build from source](#build)
 - [Usage](#usage)
 - [Contact](#contact)
 - [License](#license)

<a id="overview"></a>
## Overview

To illustrate Tapis's usage, consider the following program (available in `./benchmarking/tapis/tapis-bench/iterative/array-bubble-sort-fwd.c`), which performs a **bubble sort** and verifies that the output array is sorted.

```c
int main() {

  //*-- precondition
  unsigned int N;
  assume(N > 0);
  int array[N];

  //*-- computation
  bool swapped = true;
  while(swapped) {
    swapped = false;
    unsigned int i = 1;
    while(i < N) {
      if(array[i - 1] > array[i]) {
        int tmp = array[i];
        array[i] = array[i - 1];
        array[i - 1] = tmp;
        swapped = true;
      }
      i++;
    }
  }

  //*-- postcondition
  for(unsigned int k = 0; k < N - 1; k++) {
    for(unsigned int l = k + 1; l < N; l++) {
      assert(array[k] <= array[l]);
    }
  }

  return 0;
}
```

The nested `for` loops express a **universal assertion** over all pairs of indices `k < l`, ensuring that `array[k] <= array[l]`. This verifies that the array is sorted in non-decreasing order after the computation.

Tapis interprets such `for` loops as universally quantified assertions and attempts to prove them for all admissible values of `k` and `l`.

To verify the program above using Tapis, run the following command from the root of your build directory:

```bash
time ./tapis ../benchmarking/tapis/tapis-bench/iterative/array-bubble-sort-fwd.c
```

By default, Tapis begins verification using a single universally quantified variable. In this case, that’s insufficient to prove the correctness of the bubble sort, so Tapis will automatically increase the number of quantifiers to two before printing `SAFE`, indicating that the program satisfies its specification.

The `time` command is used to measure the verification duration.

You can speed up the process by directly specifying the required number of quantifier variables:

```bash
time ./tapis --qdt.quantifiers 2 ../benchmarking/tapis/tapis-bench/iterative/array-bubble-sort-fwd.c
```

This avoids the need for incremental adjustment and may reduce verification time.

If you also want to print the inferred loop invariants and procedure pre-/post-conditions, add the `--print-invs` option:

```bash
time ./tapis --qdt.quantifiers 2 --print-invs ../benchmarking/tapis/tapis-bench/iterative/array-bubble-sort-fwd.c
```


<a id="installation"></a>
## Installation

<a id="dependencies"></a>
### Dependencies
To build Tapis, the following dependencies are required:

- A C++ compiler with C++17 support
- CMake (v3.17 or up)
- GNU Make
- [Z3](https://github.com/Z3Prover/z3/releases/tag/z3-4.13.4), preferably version 4.13.4  
- [APRON](https://github.com/antoinemine/apron), including the C++ API  
- LLVM 13, including Clang

<a id="build"></a>
### Build from source
Once all dependencies are correctly installed, building Tapis is straightforward using CMake and Make.

From the project's root directory, create a new folder for an out-of-source build and navigate into it:

```bash
mkdir build; cd build
```
Then, configure the project using CMake and build it with Make:

```bash
cmake ..
make -j
```

This will compile Tapis and generate the executable binary (`./tapis`) in the `build` directory.

If you want Tapis to print detailed logs to the terminal during verification, build the debug version by passing the `CMAKE_BUILD_TYPE=Debug` flag to CMake:

```bash
cmake -DCMAKE_BUILD_TYPE=Debug ..
make -j
```


<a id="usage"></a>
## Usage

Once Tapis is built, it can be run from the command line to verify C programs. The tool supports a variety of command-line options to configure analysis behavior and customize learning parameters.

### Basic Usage

```bash
./tapis [OPTIONS] path/to/program.c
```

At a minimum, you must provide the path to a C source file as input.
Tapis accepts a subset of the C language with support for procedure calls. For examples of supported programs, see the files in `./benchmarking/tapis`.

### Options:

- `--print-invs`
  If the program is verified as safe, this option prints the inferred loop invariants and procedure pre-/post-conditions.

- `--absint-domain [box|oct|polka]`  
  Select the abstract domain used in the optional abstract interpretation pre-analysis (requires APRON with the corresponding domain support).  
  **Default:** `oct`

- `--no-absint.perform`  
  Disable abstract interpretation pre-analysis entirely.

- `--ice.learner.index_domains [domains]`  
  Set the attribute domains for index variables.  
  **Default:** `int+ub`

- `--ice.learner.data_domains [domains]`  
  Set the attribute domains for data variables.  
  **Default:** `int+ub`

- `--no-ice.learner.attr_from_program`  
  Disable automatic extraction of attribute patterns from the input program.

- `--ice.learner.mix_data_indexes`  
  Enable mixing of index and data domains for attribute generation.  
  In this mode, attributes are enumerated from the set specified by `--ice.learner.index_domains`.

- `--qdt.quantifiers [number]`  
  Set the initial number of quantifier variables per array.  
  If this number is insufficient, Tapis will automatically increase it during learning.  
  **Default:** `1`

- `--no-qdt.bounded_data_values`  
  Disable bounding of data values in generated counterexamples.

Attribute domains specify the types of predicates enumerated for learning invariants.  
They can be combined using `+` (e.g., `int+ub+eq`). The supported domain keywords are:

- `emp` — Empty domain (no attributes)  
- `eq` — Equality  
- `ub` — Upper bound  
- `int` — Intervals  
- `db` — Difference bounds  
- `oct` — Octagon  
- `poly` — Polyhedra

Tapis will output `SAFE` if the program satisfies its specification and no counterexamples are found.
If a violation is detected, it will output `UNSAFE`.


<a id="contact"></a>
## Contact
Kindly write to boutglay@irif.fr for any feedback, suggestions, queries and issues.


<a id="license"></a>
## License
- The source code of Tapis is licensed under the terms of the GPL-3.0 License.  
- The TAPIS-Bench benchmark set, located in the `./benchmarking/*/tapis-bench` directories, is licensed under the MIT License.  
- The benchmarks in `./benchmarking/*/sv-comp` are adapted from SV-COMP; for licensing details, see the [SV-COMP benchmark repository](https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks).
