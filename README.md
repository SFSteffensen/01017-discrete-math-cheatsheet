# Seb's Discrete Mathematics Cheat Sheet

A comprehensive exam reference for **01017 Discrete Mathematics** at DTU, written in [Typst](https://typst.app/).

[![Build](https://github.com/SFSteffensen/01017-discrete-math-cheatsheet/actions/workflows/build-release.yml/badge.svg)](https://github.com/SFSteffensen/01017-discrete-math-cheatsheet/actions/workflows/build-release.yml)
[![Tests](https://github.com/SFSteffensen/01017-discrete-math-cheatsheet/actions/workflows/pr-tests.yml/badge.svg)](https://github.com/SFSteffensen/01017-discrete-math-cheatsheet/actions/workflows/pr-tests.yml)

## Overview

This cheat sheet provides:

- Quick-reference formulas and theorems
- Built-in calculation functions for live computation
- Worked exam-style examples with solutions

## Topics Covered

| Area              | Contents                                                                   |
| ----------------- | -------------------------------------------------------------------------- |
| **Number Theory** | GCD, LCM, Bézout's identity, modular arithmetic, Fermat's Little Theorem   |
| **Combinatorics** | Binomial coefficients, permutations, derangements, Stirling numbers        |
| **Graph Theory**  | Handshaking lemma, Euler circuits, hypercubes, complete graphs             |
| **Set Theory**    | De Morgan's laws, power sets, inclusion-exclusion                          |
| **Relations**     | Reflexivity, symmetry, transitivity, equivalence relations, partial orders |

## Built-in Functions

The document includes Typst functions for live calculations:

```typ
derangement(n)              // Derangement D_n
extended-gcd(a, b)          // Extended Euclidean Algorithm
mod-inverse(n, m)           // Modular multiplicative inverse
crt-solve(remainders, mods) // Chinese Remainder Theorem
euler-phi(n)                // Euler's totient φ(n)
stirling2(n, k)             // Stirling numbers S(n,k)
gcd-steps(a, b)             // Step-by-step Euclidean algorithm
```

## Usage

### Compile the Document

```sh
typst compile Discrete_Cheat_Sheet.typ
```

### Run Tests

```sh
typst compile tests.typ
```

The test suite includes **193 assertions** validating all custom functions.

## Download

Pre-built PDFs are available on the [Releases](https://github.com/SFSteffensen/01017-discrete-math-cheatsheet/releases) page.

## Contributing

1. Implement new functions in `Discrete_Cheat_Sheet.typ`
2. Add corresponding tests in `tests.typ`
3. Verify tests pass locally
4. Submit a pull request

All PRs require passing test coverage and compilation checks before merge.

## Author

**Sebastian Faber Steffensen** (s255609)
[GitHub](https://github.com/SFSteffensen)

## License

Personal study notes. Please credit the original author if adapting or sharing.
