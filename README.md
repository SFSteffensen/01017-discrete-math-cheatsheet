# Seb's Discrete Mathematics Cheat Sheet

A comprehensive exam reference document for **01017 Discrete Mathematics** at DTU (Technical University of Denmark). Written in [Typst](https://typst.app/), this cheat sheet provides formulas, calculation tools, and worked examples for exam preparation.

---

## Purpose

- Provide a complete quick-reference of key formulas and theorems for 01017
- Include built-in calculation functions for common discrete math operations
- Document worked exam-style examples with detailed solutions
- Serve as a compact, printable cheat sheet for exam use

---

## Contents

### Key Formulas & Quick Reference

- **Number Theory** — GCD, LCM, Bézout's identity, modular arithmetic, Fermat's Little Theorem
- **Combinatorics** — Binomial coefficients, permutations, derangements, Stirling numbers
- **Graph Theory** — Handshaking lemma, Euler circuits, hypercubes, complete graphs
- **Set Theory & Inclusion-Exclusion** — De Morgan's laws, power sets, counting formulas
- **Relations** — Reflexivity, symmetry, transitivity, equivalence relations, partial orders

### Built-in Calculation Functions

The document includes Typst functions for live calculations:

**Core Functions:**

- `calc.gcd(a, b)`, `calc.lcm(a, b)` — GCD and LCM
- `calc.binom(n, k)`, `calc.fact(n)` — Binomial coefficients and factorials
- `derangement(n)` — Derangement calculator (D_n)
- `extended-gcd(a, b)` — Extended Euclidean Algorithm (returns gcd, s, t)
- `mod-inverse(n, m)` — Modular multiplicative inverse
- `crt-solve(remainders, moduli)` — Chinese Remainder Theorem solver

**New Functions:**

- `euler-phi(n)` — Euler's totient function φ(n)
- `stirling2(n, k)` — Stirling numbers of the second kind S(n,k)
- `is-perfect(n)` — Check if n is a perfect number
- `sum-proper-divisors(n)` — Sum of proper divisors of n
- `ie2(a, b, ab)` — Inclusion-exclusion for 2 sets
- `ie3(a, b, c, ab, ac, bc, abc)` — Inclusion-exclusion for 3 sets
- `gcd-steps(a, b)` — GCD with step-by-step Euclidean algorithm display

**Display Helpers:**

- `show-gcd`, `show-bezout`, `show-mod-inverse`, `show-crt`, `show-binom`, `show-fact`, `show-derangement`

**External Packages:**

- `poly-div`, `poly-div-working` — Polynomial long division (from [auto-div](https://typst.app/universe/package/auto-div))
- `venn2`, `venn3` — Venn diagram drawing (from [cetz-venn](https://typst.app/universe/package/cetz-venn))

### Worked Examples & Solutions

- **Number Theory** — Divisibility proofs, GCD constraints, modular arithmetic, CRT
- **Functions** — Injective/surjective analysis
- **Graph Theory** — Hypercube edges, degree sequences, Euler circuits
- **Combinatorics** — Binomial theorem, inclusion-exclusion, derangements, circular permutations
- **Relations** — Equivalence classes, partial orders
- **Proof Techniques** — Mathematical induction, pigeonhole principle
- **Matching** — Hall's theorem applications
- **Propositional Logic** — Truth sayer/liar puzzles with truth tables
- **Perfect Numbers** — Verification and Mersenne prime theorem
- **Set Operations** — Algebraic proofs of set identities
- **Equivalence Relations** — Cardinality equivalence, rational equivalence

### Calculation Workspace

A dedicated section for performing calculations during the exam with pre-configured helper functions.

---

## Testing

The repository includes a test suite (`tests.typ`) with **97 assertions** that validate all custom functions:

```sh
typst compile tests.typ
```

If compilation succeeds, all tests pass.

---

## Language

The document is written in **English**.

---

## Format

This is a [Typst](https://typst.app/) document (`.typ` file) using a custom DTU template. To compile:

```sh
typst compile "Discrete_Cheat_Sheet.typ"
```

Or use the Typst web app / VS Code extension for live preview.

---

## CI/CD

This repository includes a GitHub Actions workflow that:

1. Runs the test suite to validate all functions
2. Compiles the document to PDF
3. Creates a timestamped release with the PDF attached

See the [Releases](https://github.com/SFSteffensen/01017-discrete-math-cheatsheet/releases) page for the latest PDF.

---

## Author

**Sebastian Faber Steffensen** (s255609)
GitHub: [SFSteffensen](https://github.com/SFSteffensen)

---

## License

Personal study notes. If you wish to adapt or share, please credit the original author.
