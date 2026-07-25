# verus-study-cases-leetcode


## Overview

This project contains selected LeetCode problems verified with [Verus](https://github.com/verus-lang/verus?tab=readme-ov-file). For each problem, we provide a non-brute-force solution and prove its correctness using formal verification.


## Verus

Verus is a formal verification tool for Rust programs. See the [Verus official repository](https://github.com/verus-lang/verus?tab=readme-ov-file) for installation and usage instructions.

The Verus version used by this project is recorded in [VERSIONS.md](./VERSIONS.md).


## Verification

Install Verus first.

Each problem is a standalone example with its own Makefile. To verify a single example, update the `Verifier` path in that example's Makefile, then run:

```bash
make
```

To verify all standalone examples with one command, use [scripts/verify_all.sh](./scripts/verify_all.sh):

```bash
scripts/verify_all.sh
```

The script reports which examples succeed or fail during verification and prints a final summary.

The full problem list is available in [ProblemList.md](./ProblemList.md).

## Contribution

Contributions are welcome.
