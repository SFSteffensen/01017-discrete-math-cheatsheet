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

- `calc.gcd(a, b)`, `calc.lcm(a, b)` — GCD and LCM
- `calc.binom(n, k)`, `calc.fact(n)` — Binomial coefficients and factorials
- `derangement(n)` — Derangement calculator (D_n)
- `extended-gcd(a, b)` — Extended Euclidean Algorithm (returns gcd, s, t)
- `mod-inverse(n, m)` — Modular multiplicative inverse
- `crt-solve(remainders, moduli)` — Chinese Remainder Theorem solver

Display helpers: `show-gcd`, `show-bezout`, `show-mod-inverse`, `show-crt`, `show-binom`, `show-fact`, `show-derangement`

### Worked Examples & Solutions

- **Number Theory** — Divisibility proofs, GCD constraints, modular arithmetic, CRT
- **Functions** — Injective/surjective analysis
- **Graph Theory** — Hypercube edges, degree sequences, Euler circuits
- **Combinatorics** — Binomial theorem, inclusion-exclusion, derangements, circular permutations
- **Relations** — Equivalence classes, partial orders
- **Proof Techniques** — Mathematical induction, pigeonhole principle
- **Matching** — Hall's theorem applications

### Calculation Workspace

A dedicated section for performing calculations during the exam with pre-configured helper functions.

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

## Author

**Sebastian Faber Steffensen** (s255609)
GitHub: [SFSteffensen](https://github.com/SFSteffensen)

---

## License

Personal study notes. If you wish to adapt or share, please credit the original author.
