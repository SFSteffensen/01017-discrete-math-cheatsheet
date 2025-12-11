#import "@local/dtu-template:0.5.1":*
#import "@preview/cetz:0.4.2"
#import "@preview/cetz-venn:0.1.4": venn2, venn3
#import "@preview/auto-div:0.1.0": poly-div, poly-div-working

#show: dtu-note.with(
  course: "01017",
  course-name: "Discrete Mathematics",
  title: "Discrete Mathematics - Exam Cheat Sheet",
  date: datetime.today(),
  author: "Sebastian Faber Steffensen (s255609)",
  semester: "2025 Fall",
)

// ═══════════════════════════════════════════════════════════════════════════════
// EXAM STRATEGY GUIDE - Based on E24 Exam Analysis
// ═══════════════════════════════════════════════════════════════════════════════

= Exam Strategy Guide

#rect(inset: 12pt, fill: blue.lighten(90%), width: 100%)[
  *Key Exam Information:*
  - One correct answer per question
  - No negative points for wrong answers
  - Always attempt every question!
  - Use CAS tools (Typst functions, Wolfram Mathematica) to verify answers
]

== Question Type Recognition

#table(
  columns: (1fr, 1.5fr, 1.5fr),
  stroke: 0.5pt,
  inset: 6pt,
  [*Question Type*],
  [*Key Words/Patterns*],
  [*Go-To Strategy*],
  [Divisibility],
  [$a|b$, $gcd$, $lcm$, prime factors],
  [Factor decomposition, Euclid's lemma],
  [Modular Arithmetic],
  [$equiv$, $mod$, inverse],
  [Extended Euclidean, CRT],
  [Function Properties],
  [injective, surjective, well-defined],
  [Test values, check domain/codomain],
  [Graph Theory],
  [vertices, edges, $K_n$, $Q_n$, degree],
  [Handshaking lemma, formulas],
  [Combinatorics],
  [count, choose, arrange, $(a+b)^n$],
  [Binomial theorem, I-E],
  [Relations],
  [reflexive, symmetric, transitive],
  [Check all pairs systematically],
  [Partitions],
  [disjoint, exhaustive, cover],
  [Verify: no overlap + covers all],
  [Induction],
  [prove for all $n$],
  [Base case + inductive step],
)

== Wolfram Mathematica Quick Reference

#rect(inset: 8pt, fill: gray.lighten(90%), width: 100%)[
*Essential Mathematica Commands for Exam:*
```mathematica
  (* Number Theory *)
  GCD[a, b]                    (* Greatest common divisor *)
  LCM[a, b]                    (* Least common multiple *)
  ExtendedGCD[a, b]            (* Returns {gcd, {s, t}} where gcd = a*s + b*t *)
  Mod[a, m]                    (* a mod m *)
  PowerMod[a, -1, m]           (* Modular inverse of a mod m *)
  ChineseRemainder[{r1,r2,...}, {m1,m2,...}]  (* CRT solver *)
  PrimeQ[n]                    (* Is n prime? *)
  FactorInteger[n]             (* Prime factorization *)
  Divisors[n]                  (* All divisors of n *)

  (* Combinatorics *)
  Binomial[n, k]               (* n choose k *)
  n!                           (* Factorial *)
  Subfactorial[n]              (* Derangements D_n *)

  (* Algebra *)
  Expand[(a + b)^n]            (* Expand polynomial *)
  Coefficient[expr, x^k]       (* Extract coefficient *)
  PolynomialQuotientRemainder[p, q, x]  (* Polynomial division *)

  (* Verification *)
  Simplify[expr1 == expr2]     (* Check if expressions are equal *)
  Table[f[x], {x, 1, n}]       (* Generate list of values *)
  ```
]

// Typst built-in functions (calc module):
// - calc.gcd(a, b) - Greatest Common Divisor
// - calc.lcm(a, b) - Least Common Multiple
// - calc.fact(n) - Factorial n!
// - calc.perm(n, k) - Permutations P(n,k)
// - calc.binom(n, k) - Binomial coefficient C(n,k)
// - calc.rem(a, b) - Remainder (modulo)
// - calc.quo(a, b) - Quotient (integer division)
// - calc.pow(a, b) - Exponentiation
// - calc.abs(x) - Absolute value
// - calc.floor(x), calc.ceil(x) - Floor and ceiling

// Custom calculation functions

// pmod: LaTeX-style "parenthesized mod" notation: a ≡ b (mod m)
#let pmod(m) = $space (mod #m)$

// Perfect number checker: n is perfect if it equals sum of its proper divisors
#let is-perfect(n) = {
  let sum = 0
  for d in range(1, n) {
    if calc.rem(n, d) == 0 { sum = sum + d }
  }
  sum == n
}

// Sum of divisors (excluding n itself)
#let sum-proper-divisors(n) = {
  let sum = 0
  for d in range(1, n) {
    if calc.rem(n, d) == 0 { sum = sum + d }
  }
  sum
}

// Euler's totient function φ(n): count of integers 1 to n coprime with n
#let euler-phi(n) = {
  let count = 0
  for k in range(1, n + 1) {
    if calc.gcd(k, n) == 1 { count = count + 1 }
  }
  count
}

// Stirling numbers of the second kind S(n,k): ways to partition n elements into k non-empty subsets
#let stirling2(n, k) = {
  if k == 0 and n == 0 { return 1 }
  if k == 0 or n == 0 or k > n { return 0 }
  if k == 1 or k == n { return 1 }
  // Recurrence: S(n,k) = k*S(n-1,k) + S(n-1,k-1)
  k * stirling2(n - 1, k) + stirling2(n - 1, k - 1)
}

// Inclusion-exclusion for 2 sets
#let ie2(a, b, ab) = a + b - ab

// Inclusion-exclusion for 3 sets
#let ie3(a, b, c, ab, ac, bc, abc) = a + b + c - ab - ac - bc + abc

// Inclusion-exclusion for 4 sets
#let ie4(singles, pairs, triples, quad) = 4 * singles - 6 * pairs + 4 * triples - quad

// Check if a sequence is a valid degree sequence (Erdős–Gallai theorem simplified check)
#let sum-degrees(seq) = seq.fold(0, (acc, x) => acc + x)

// GCD with steps display (Euclidean algorithm)
#let gcd-steps(a, b) = {
  let (larger, smaller) = if a >= b { (a, b) } else { (b, a) }
  let steps = ()
  let current-a = larger
  let current-b = smaller

  while current-b != 0 {
    let quotient = calc.quo(current-a, current-b)
    let remainder = calc.rem(current-a, current-b)
    steps.push((current-a, current-b, quotient, remainder))
    current-a = current-b
    current-b = remainder
  }

  let result = current-a
  let math-lines = steps.map(step =>
  $#str(step.at(0)) &= #str(step.at(1)) dot #str(step.at(2)) + #str(step.at(3))$).join($ \ $)

  [
    Finding $gcd(#str(a), #str(b))$:
    $ #math-lines $
    Therefore, $gcd(#str(a), #str(b)) = #str(result)$
  ]
}

// Derangement calculator: D_n = n! * Σ(-1)^k/k! for k=0 to n
#let derangement(n) = {
  let nfact = calc.fact(n)
  let sum = 0.0
  for k in range(n + 1) {
    let sign = if calc.rem(k, 2) == 0 { 1.0 } else { -1.0 }
    sum = sum + sign / calc.fact(k)
  }
  return int(calc.round(nfact * sum))
}

// Extended Euclidean Algorithm: returns (gcd, s, t) where gcd = a*s + b*t
#let extended-gcd(a, b) = {
  if b == 0 { return (a, 1, 0) }
  let (g, s1, t1) = extended-gcd(b, calc.rem(a, b))
  let s = t1
  let t = s1 - calc.quo(a, b) * t1
  return (g, s, t)
}

// Modular inverse: returns n^(-1) mod m, or none if it doesn't exist
#let mod-inverse(n, m) = {
  let (g, s, t) = extended-gcd(n, m)
  if g != 1 { return none }
  let inv = calc.rem(s, m)
  if inv < 0 { inv = inv + m }
  return inv
}

// Chinese Remainder Theorem solver
#let crt-solve(remainders, moduli) = {
  let n = remainders.len()
  let M = moduli.fold(1, (acc, m) => acc * m)
  let x = 0
  for i in range(n) {
    let Mi = calc.quo(M, moduli.at(i))
    let yi = mod-inverse(Mi, moduli.at(i))
    if yi == none { return none }
    x = x + remainders.at(i) * Mi * yi
  }
  x = calc.rem(x, M)
  if x < 0 { x = x + M }
  return (x, M)
}

// Hypercube edges: Q_n has n * 2^(n-1) edges
#let hypercube-edges(n) = n * calc.pow(2, n - 1)

// Complete graph edges: K_n has n(n-1)/2 edges
#let complete-edges(n) = calc.quo(n * (n - 1), 2)

// Additional functions ported from Python tools

// Primality test: check if n is prime
#let is-prime(n) = {
  if n <= 1 { return false }
  if n <= 3 { return true }
  if calc.rem(n, 2) == 0 or calc.rem(n, 3) == 0 { return false }
  let i = 5
  while i * i <= n {
    if calc.rem(n, i) == 0 or calc.rem(n, i + 2) == 0 { return false }
    i = i + 6
  }
  return true
}

// Get list of primes below n
#let primes-below(n) = {
  let primes = ()
  for i in range(2, n) {
    if is-prime(i) { primes.push(i) }
  }
  primes
}

// Count primes below n
#let count-primes-below(n) = primes-below(n).len()

// Solve general linear congruence: ax ≡ c (mod m)
// Returns (x0, step) where solutions are x ≡ x0 (mod step), or none if no solution
#let solve-congruence(a, c, m) = {
  let g = calc.gcd(a, m)
  if calc.rem(c, g) != 0 { return none }
  let a-reduced = calc.quo(a, g)
  let c-reduced = calc.quo(c, g)
  let m-reduced = calc.quo(m, g)
  let inv = mod-inverse(a-reduced, m-reduced)
  if inv == none { return none }
  let x0 = calc.rem(c-reduced * inv, m-reduced)
  if x0 < 0 { x0 = x0 + m-reduced }
  return (x0, m-reduced)
}

// Relation property checkers (relations given as arrays of pairs)

// Check if relation R on set S is reflexive: ∀x ∈ S: (x,x) ∈ R
#let is-reflexive(S, R) = {
  for x in S {
    if not R.contains((x, x)) { return false }
  }
  return true
}

// Check if relation R is symmetric: (x,y) ∈ R ⟹ (y,x) ∈ R
#let is-symmetric(R) = {
  for pair in R {
    let (x, y) = pair
    if not R.contains((y, x)) { return false }
  }
  return true
}

// Check if relation R is antisymmetric: (x,y) ∈ R ∧ (y,x) ∈ R ⟹ x = y
#let is-antisymmetric(R) = {
  for pair in R {
    let (x, y) = pair
    if x != y and R.contains((y, x)) { return false }
  }
  return true
}

// Check if relation R is transitive: (x,y) ∈ R ∧ (y,z) ∈ R ⟹ (x,z) ∈ R
#let is-transitive(R) = {
  for pair1 in R {
    let (a, b) = pair1
    for pair2 in R {
      let (c, d) = pair2
      if b == c and not R.contains((a, d)) { return false }
    }
  }
  return true
}

// Check if R is an equivalence relation on S (reflexive + symmetric + transitive)
#let is-equivalence-relation(S, R) = {
  is-reflexive(S, R) and is-symmetric(R) and is-transitive(R)
}

// Check if R is a partial order on S (reflexive + antisymmetric + transitive)
#let is-partial-order(S, R) = {
  is-reflexive(S, R) and is-antisymmetric(R) and is-transitive(R)
}

// Division with quotient and remainder display
#let divide-with-remainder(a, b) = {
  let q = calc.quo(a, b)
  let r = calc.rem(a, b)
  (q, r)
}

// Display helper functions

#let show-gcd(a, b) = {
  let result = calc.gcd(a, b)
  [$ gcd(#str(a), #str(b)) = #result $]
}
#let show-lcm(a, b) = {
  let result = calc.lcm(a, b)
  [$ "lcm"(#str(a), #str(b)) = #result $]
}
#let show-binom(n, k) = {
  let result = calc.binom(n, k)
  [$ binom(#str(n), #str(k)) = #result $]
}
#let show-fact(n) = {
  let result = calc.fact(n)
  [$ #str(n) ! = #result $]
}
#let show-derangement(n) = {
  let result = derangement(n)
  [$ D_#str(n) = #result $]
}

#let show-bezout(a, b) = {
  let (g, s, t) = extended-gcd(a, b)
  [$ gcd(#str(a), #str(b)) = #g = (#str(a))(#s) + (#str(b))(#t) $]
}

#let show-mod-inverse(n, m) = {
  let inv = mod-inverse(n, m)
  if inv == none {
    let g = calc.gcd(n, m)
    [$ #str(n)^(-1) mod #str(m) $ does not exist (since $gcd(#str(n), #str(m)) = #g != 1$)]
  } else {
    [$ #str(n)^(-1) equiv #inv pmod(#m) $]
  }
}

#let show-crt(remainders, moduli) = {
  let result = crt-solve(remainders, moduli)
  if result == none {
    [CRT: No solution (moduli not coprime)]
  } else {
    let (x, M) = result
    let verifications = range(remainders.len()).map(i => {
      let r = calc.rem(x, moduli.at(i))
      [#x ≡ #r (mod #(moduli.at(i)))]
    })
    [#rect(inset: 6pt)[*CRT Solution:* $x equiv #x pmod(#M)$] #h(1em) Verify: #verifications.join(", ")]
  }
}

// Display helper for primality check
#let show-is-prime(n) = {
  let result = is-prime(n)
  if result {
    [$ #n "is prime" $]
  } else {
    [$ #n "is not prime" $]
  }
}

// Display helper for primes below n
#let show-primes-below(n) = {
  let primes = primes-below(n)
  let count = primes.len()
  [There are #count primes below #n: #primes.map(p => str(p)).join(", ")]
}

// Display helper for solving ax ≡ c (mod m)
#let show-solve-congruence(a, c, m) = {
  let result = solve-congruence(a, c, m)
  if result == none {
    [$ #a x equiv #c pmod(#m) $ has no solution (since $gcd(#a, #m) = #calc.gcd(a, m)$ does not divide $#c$)]
  } else {
    let (x0, step) = result
    [$ #a x equiv #c pmod(#m) arrow.double x equiv #x0 pmod(#step) $]
  }
}

// Display helper for relation properties
#let show-relation-properties(S, R, name: "R") = {
  let refl = is-reflexive(S, R)
  let sym = is-symmetric(R)
  let antisym = is-antisymmetric(R)
  let trans = is-transitive(R)
  let equiv = refl and sym and trans
  let partial = refl and antisym and trans

  [
    *Relation #name on set #S:*
    - Reflexive: #if refl [Yes] else [No]
    - Symmetric: #if sym [Yes] else [No]
    - Antisymmetric: #if antisym [Yes] else [No]
    - Transitive: #if trans [Yes] else [No]
    - #if equiv [#rect(inset: 4pt)[*Equivalence relation*]] else if partial [#rect(inset: 4pt)[*Partial order*]] else [Neither equivalence relation nor partial order]
  ]
}

// Display helper for division with remainder
#let show-division(a, b) = {
  let (q, r) = divide-with-remainder(a, b)
  [$ #a = #b dot #q + #r $]
}

// Function property checkers (Injective, Surjective, Bijective)

// Check if a function (represented as a dictionary/map) is injective
// A function is injective if distinct domain elements map to distinct codomain elements
// mapping: dictionary where keys are domain elements, values are codomain elements
// Returns: (is_injective: bool, counterexample: none or (x1, x2, y))
#let is-injective(mapping) = {
  let pairs = mapping.pairs()
  let n = pairs.len()

  // Check all pairs of domain elements
  for i in range(n) {
    for j in range(i + 1, n) {
      let (x1, y1) = pairs.at(i)
      let (x2, y2) = pairs.at(j)
      // If two different inputs map to same output, not injective
      if y1 == y2 {
        return (false, (x1, x2, y1))
      }
    }
  }
  return (true, none)
}

// Check if a function is surjective onto a given codomain
// A function is surjective if every element of the codomain is mapped to
// mapping: dictionary where keys are domain elements, values are codomain elements
// codomain: array of codomain elements
// Returns: (is_surjective: bool, counterexample: none or array of unmapped elements)
#let is-surjective(mapping, codomain) = {
  let image = mapping.values()
  let unmapped = ()

  for y in codomain {
    if not image.contains(y) {
      unmapped.push(y)
    }
  }

  if unmapped.len() > 0 {
    return (false, unmapped)
  }
  return (true, none)
}

// Check if a function is bijective (both injective and surjective)
// Returns: (is_bijective: bool, reason: string, counterexample)
#let is-bijective(mapping, codomain) = {
  let (inj, inj-counter) = is-injective(mapping)
  let (surj, surj-counter) = is-surjective(mapping, codomain)

  if not inj and not surj {
    return (false, "not injective and not surjective", (inj-counter, surj-counter))
  } else if not inj {
    return (false, "not injective", inj-counter)
  } else if not surj {
    return (false, "not surjective", surj-counter)
  }

  return (true, "bijective", none)
}

// Helper: build a function mapping from a callable and explicit domain
// func: a function that takes one argument
// domain: array of domain elements
// Returns: dictionary mapping domain -> codomain
#let function-from-callable(func, domain) = {
  let mapping = (:)
  for x in domain {
    mapping.insert(str(x), func(x))
  }
  return mapping
}

// High-level function checker: check all properties of a callable function
// func: a callable function (lambda or named function)
// domain: array of domain elements to evaluate on
// codomain: array of codomain elements (optional, defaults to none)
// Returns: dictionary with keys "injective", "surjective", "bijective", "mapping", "details"
#let check-function(func, domain, codomain: none) = {
  // Build the mapping by evaluating func on domain
  let mapping = function-from-callable(func, domain)

  // Check injectivity
  let (is_inj, inj_counter) = is-injective(mapping)

  // Check surjectivity (only if codomain provided)
  let is_surj = none
  let surj_counter = none
  if codomain != none {
    (is_surj, surj_counter) = is-surjective(mapping, codomain)
  }

  // Check bijectivity (only if codomain provided)
  let is_bij = none
  let bij_reason = none
  let bij_counter = none
  if codomain != none {
    (is_bij, bij_reason, bij_counter) = is-bijective(mapping, codomain)
  }

  return (
    injective: is_inj,
    surjective: is_surj,
    bijective: is_bij,
    mapping: mapping,
    inj_counterexample: inj_counter,
    surj_counterexample: surj_counter,
    bij_details: (reason: bij_reason, counterexample: bij_counter),
  )
}

// Display helper for function checker results
#let show-function-check(result, func-name: "f") = {
  let inj-text = if result.injective { [Injective: Yes] } else { [Injective: No] }
  let surj-text = if result.surjective == none { [Surjective: Unknown (no codomain)] } else if result.surjective { [Surjective: Yes] } else { [Surjective: No] }
  let bij-text = if result.bijective == none { [Bijective: Unknown (no codomain)] } else if result.bijective { [Bijective: Yes] } else { [Bijective: No] }

  [
    *Function #func-name:* #inj-text, #surj-text, #bij-text

    #if result.inj_counterexample != none {
      let (x1, x2, y) = result.inj_counterexample
      [_Injectivity fails:_ $#func-name (#x1) = #func-name (#x2) = #y$]
    }

    #if result.surj_counterexample != none {
      [_Surjectivity fails:_ unmapped elements: #{ result.surj_counterexample.map(x => $#x$).join(", ") }]
    }
  ]
}

= Exam Question Types with E24 Examples

== Type 1: Prime Divisibility & Product Divisibility (E24 Q1)

#rect(inset: 8pt, fill: yellow.lighten(85%), width: 100%)[
  *Pattern Recognition:* "If $a b | c d$, then which must be true?"
]

#example(title: [E24 Q1: Prime divisibility in products])[
*Question:* If $a, b, c, d$ are positive integers such that $a b | c d$, which must be true?

*Strategy:*
1. $a b | c d$ means every prime factor in $a b$ appears in $c d$
2. Use Euclid's Lemma: If prime $p | x y$, then $p|x$ or $p|y$

*Typst Verification:*
```typst
  // Counterexample: a=6, b=1, c=2, d=3
  #let a = 6; #let b = 1; #let c = 2; #let d = 3
  #(a * b)  // = 6
  #(c * d)  // = 6, so ab | cd ✓
  #calc.gcd(a, b)  // = 1
  #calc.gcd(c, d)  // = 1, but gcd(a,b)=6 does NOT divide gcd(c,d)=1
  ```

*Mathematica:*
```mathematica
  (* Verify counterexample *)
  a = 6; b = 1; c = 2; d = 3;
  Divisible[c*d, a*b]       (* True *)
  Divisible[GCD[c,d], GCD[a,b]]  (* False - option 5 fails *)
  ```

*Answer:* "If $p$ is a prime that divides $a$, then $p|c$ or $p|d$" (by Euclid's Lemma)
]

== Type 2: Graph Edge Counting (E24 Q2, Q4, Q5)

#rect(inset: 8pt, fill: yellow.lighten(85%), width: 100%)[
  *Key Formulas:*
  - Hypercube $Q_n$: vertices $= 2^n$, edges $= n dot 2^(n-1)$
  - Complete graph $K_n$: edges $= binom(n, 2) = n(n-1)/2$
  - Handshaking Lemma: $sum deg(v) = 2|E|$ (must be even!)
]

#example(title: [E24 Q2: Hypercube edges])[
*Question:* For $n >= 4$, the number of edges in $Q_n$ is?

*Quick Check:*
- $Q_4$: $4 dot 2^3 = 32$ edges
- $Q_5$: $5 dot 2^4 = 80$ edges

*Typst:*
```typst
  #let hypercube-edges(n) = n * calc.pow(2, n - 1)
  #hypercube-edges(4)  // = 32
  #hypercube-edges(5)  // = 80
  ```

*Mathematica:*
```mathematica
  hypercubeEdges[n_] := n * 2^(n-1)
  Table[hypercubeEdges[n], {n, 4, 8}]
  (* {32, 80, 192, 448, 1024} *)
  ```

*Answer:* $n dot 2^(n-1)$
]

#example(title: [E24 Q4: Complete graph equivalences])[
*Question:* Are these equal for $K_(2n)$? (a) $binom(2n, 2)$, (b) $2binom(n, 2) + n^2$, (c) $n(2n-1)$

*Mathematica Verification:*
```mathematica
  n = 6;
  a = Binomial[2n, 2]
  b = 2*Binomial[n, 2] + n^2
  c = n*(2n - 1)
  a == b == c  (* True *)

  (* Algebraic proof *)
  Simplify[Binomial[2n, 2] - n*(2n-1)]  (* 0 *)
  ```

*Answer:* All three are equal
]

#example(title: [E24 Q5: Invalid degree sequence])[
*Question:* Does a graph with degrees $2,2,3,3,3,3,3$ exist?

*Strategy:* Sum of degrees must be EVEN (Handshaking Lemma)

*Typst:*
```typst
  #let degrees = (2, 2, 3, 3, 3, 3, 3)
  #degrees.fold(0, (a, x) => a + x)  // = 19 (ODD!)
  ```

*Mathematica:*
```mathematica
  Total[{2, 2, 3, 3, 3, 3, 3}]  (* 19 - odd, impossible! *)
  ```

*Answer:* Such a graph does NOT exist (odd sum violates handshaking lemma)
]

== Type 3: Function Properties (E24 Q3)

#rect(inset: 8pt, fill: yellow.lighten(85%), width: 100%)[
  *Checklist:*
  1. *Well-defined?* Does every domain element map to exactly one codomain element?
  2. *Injective?* Different inputs → different outputs? Find counterexample if not.
  3. *Surjective?* Every codomain element is hit? Find unmapped element if not.
]

#example(title: [E24 Q3: Function classification])[
*Function:* $f: ZZ^+ -> NN$ given by $f(x) = floor(log_2(x))$

*Analysis:*
- $f(1) = 0, f(2) = 1, f(3) = 1, f(4) = 2, ...$
- Not injective: $f(2) = f(3) = 1$
- Surjective: For any $n in NN$, $f(2^n) = n$

*Typst Check:*
```typst
  #let f = (x) => calc.floor(calc.log(x, base: 2))
  #(f(1), f(2), f(3), f(4), f(5), f(6), f(7), f(8))
  // (0, 1, 1, 2, 2, 2, 2, 3)
  ```

*Mathematica:*
```mathematica
  f[x_] := Floor[Log2[x]]
  Table[f[x], {x, 1, 10}]
  (* {0, 1, 1, 2, 2, 2, 2, 3, 3, 3} *)
  (* f[2] == f[3] → not injective *)
  ```

*Answer:* Surjective but not injective
]

#example(title: [E24 Q3: Well-defined check])[
*Function:* $f: RR -> ZZ^+$ given by $f(x) = floor(|x|)$

*Problem:* $f(0) = floor(0) = 0$, but $0 in.not ZZ^+$!

*Typst:*
```typst
  #calc.floor(calc.abs(0))  // = 0, not in ℤ⁺
  #calc.floor(calc.abs(0.5))  // = 0, not in ℤ⁺
  ```

*Answer:* NOT well-defined (outputs fall outside codomain)
]

== Type 4: Inclusion-Exclusion (E24 Q6)

#rect(
  inset: 8pt,
  fill: yellow.lighten(85%),
  width: 100%,
)[
  *Formula Pattern:* $|A_1 union ... union A_n| = sum|A_i| - sum|A_i inter A_j| + sum|A_i inter A_j inter A_k| - ...$

  *Coefficient Pattern:* $binom(n, 1), -binom(n, 2), +binom(n, 3), -binom(n, 4), ...$
]

#example(title: [E24 Q6: Four sets with symmetric intersections])[
*Given:* 4 sets, each has 200 elements, pairs share 50, triples share 25, all four share 5.

*Formula:*
$ |A union B union C union D| = 4(200) - 6(50) + 4(25) - 1(5) $

*Typst:*
```typst
  #let ie4(singles, pairs, triples, quad) = {
    4 * singles - 6 * pairs + 4 * triples - quad
  }
  #ie4(200, 50, 25, 5)  // = 595
  ```

*Mathematica:*
```mathematica
  ie4[s_, p_, t_, q_] := 4*s - 6*p + 4*t - q
  ie4[200, 50, 25, 5]  (* 595 *)
  ```

*Answer:* 595
]

== Type 5: Modular Arithmetic & Cancellation (E24 Q7, Q8)

#rect(inset: 8pt, fill: yellow.lighten(85%), width: 100%)[
  *Cancellation Law:* $a c equiv b c pmod(m)$ and $gcd(c, m) = 1$ $arrow.double$ $a equiv b pmod(m)$

  *Warning:* Cannot cancel if $gcd(c, m) != 1$!
]

#example(title: [E24 Q7: Congruence cancellation])[
*Question:* If $a c equiv b c pmod(m)$, which must be true?

*Key insight:* $m | c(a-b)$, but we can only cancel $c$ if $gcd(c, m) = 1$

*Counterexample:* $2 dot 3 equiv 2 dot 6 pmod(6)$ (both $equiv 0$), but $3 equiv.not 6 pmod(6)$

*Typst:*
```typst
  #calc.rem(2 * 3, 6)  // = 0
  #calc.rem(2 * 6, 6)  // = 0
  #calc.gcd(2, 6)  // = 2 ≠ 1, so can't cancel!
  ```

*Answer:* $a - b in {k m : k in ZZ}$ IF $gcd(c, m) = 1$
]

== Type 6: Partitions (E24 Q9)

#rect(inset: 8pt, fill: yellow.lighten(85%), width: 100%)[
  *Partition Requirements:*
  1. *Disjoint:* No element in multiple sets
  2. *Exhaustive:* Every element in at least one set
]

#example(title: [E24 Q9: Partitions of $ZZ times ZZ$])[
  *Test each option by checking all 4 pair types:* (O,O), (O,E), (E,O), (E,E)

  *Option (a):* "at least one odd" ∪ "both even"
  - Set 1: (O,O), (O,E), (E,O) ← at least one odd
  - Set 2: (E,E) ← both even
  - Disjoint? ✓ Exhaustive? ✓ → *IS a partition*

  *Option (b):* "both odd" ∪ "both even"
  - Set 1: (O,O) only
  - Set 2: (E,E) only
  - Missing (O,E) and (E,O)! → *NOT a partition*

  *Answer:* (a) is a partition but (b),(c) are not
]

== Type 7: Binomial Coefficients & Polynomial Expansion (E24 Q11)

#rect(inset: 8pt, fill: yellow.lighten(85%), width: 100%)[
  *General Term:* $(a + b)^n$ has term $binom(n, k) a^k b^(n-k)$

  *Strategy:* Set up equations for exponents, solve for $k$, check consistency
]

#example(title: [E24 Q11: Coefficients in $(2x^2 - 3y^3)^8$])[
*General term:* $binom(8, k)(2x^2)^k(-3y^3)^(8-k) = binom(8, k) 2^k (-3)^(8-k) x^(2k) y^(3(8-k))$

*For $x^8 y^(12)$:*
- Need $2k = 8 arrow.double k = 4$
- Need $3(8-k) = 12 arrow.double k = 4$ ✓
- Coefficient: $binom(8, 4) dot 2^4 dot (-3)^4 = 70 dot 16 dot 81$

*For $x^6 y^9$:*
- Need $2k = 6 arrow.double k = 3$
- Need $3(8-k) = 9 arrow.double 8-k = 3 arrow.double k = 5$ ✗
- Coefficient: *0* (impossible)

*Mathematica:*
```mathematica
  Expand[(2x^2 - 3y^3)^8];
  Coefficient[%, x^8 y^12]   (* 90720 = 70*16*81 *)
  Coefficient[%, x^6 y^9]    (* 0 *)
  ```

*Answer:* $x^8 y^(12)$: $2^4 3^4 binom(8, 4)$; $x^6 y^9$: 0
]

== Type 8: Polynomial Divisibility (E24 Q12)

#rect(inset: 8pt, fill: yellow.lighten(85%), width: 100%)[
  *Key Theorem:* $(x - r) | p(x)$ iff $p(r) = 0$

  *For $x + 1$:* Check if $p(-1) = 0$
]

#example(title: [E24 Q12: When does $x+1$ divide $x^n + 1$?])[
*Evaluate at $x = -1$:*
- $(-1)^n + 1 = 0$ iff $(-1)^n = -1$ iff $n$ is odd

*Typst verification:*
```typst
  #for n in range(1, 7) {
    let val = calc.pow(-1, n) + 1
    [n=#n: #val #if val == 0 [(divisible)] else [(not divisible)] \ ]
  }
  ```

*Mathematica:*
```mathematica
  Table[{n, (-1)^n + 1}, {n, 1, 10}]
  (* n odd → 0, n even → 2 *)
  ```

*Answer:* Divisible for each odd $n >= 1$, and for no even $n$
]

== Type 9: Hall's Theorem / Bipartite Matching (E24 Q13)

#rect(inset: 8pt, fill: yellow.lighten(85%), width: 100%)[
  *Hall's Condition:* For every subset $S$ of one side, $|N(S)| >= |S|$
]

#example(
  title: [E24 Q13: Minimum cables for computers to printers],
)[
  *Setup:* 10 computers, 5 printers. Any 5 computers must access 5 different printers.

  *Analysis:* If printer $P$ connects to $< 6$ computers, we could pick 5 computers not connected to $P$, violating Hall's condition.

  *Each printer needs $>= 6$ connections.*

  *Minimum cables:* $5 times 6 = 30$

  *Answer:* 30
]

== Type 10: Relation Properties (E24 Q14)

#rect(inset: 8pt, fill: yellow.lighten(85%), width: 100%)[
  *Classification:*
  - *Equivalence:* Reflexive + Symmetric + Transitive
  - *Partial Order:* Reflexive + Antisymmetric + Transitive
]

#example(title: [E24 Q14: Classify relations])[
*For $R_1 = {(1,2),(2,3),(1,3),(4,5),(5,6),(4,6)}$:*

*Typst Check:*
```typst
  #show-relation-properties(
    (1, 2, 3, 4, 5, 6),
    ((1, 2), (2, 3), (1, 3), (4, 5), (5, 6), (4, 6)),
    name: [R_1]
  )
  ```

- Reflexive: No (missing $(1,1), (2,2), ...$)
- Symmetric: No ($(1,2)$ but no $(2,1)$)
- Antisymmetric: Yes (no symmetric pairs with $x != y$)
- Transitive: Yes ($(1,2),(2,3) arrow.double (1,3)$ ✓)

*Answer:* Transitive and antisymmetric but not reflexive
]

== Type 11: Modular Inverse (E24 Q15)

#rect(inset: 8pt, fill: yellow.lighten(85%), width: 100%)[
  *Inverse exists iff $gcd(n, m) = 1$*

  *Finding inverse:* Use Extended Euclidean Algorithm
]

#example(title: [E24 Q15: Inverses mod 9])[
*Typst:*
```typst
  #show-mod-inverse(6, 9)  // Does not exist (gcd = 3)
  #show-mod-inverse(2, 9)  // = 5 (since 2×5 = 10 ≡ 1)
  #show-mod-inverse(7, 9)  // = 4 (since 7×4 = 28 ≡ 1)
  ```

*Mathematica:*
```mathematica
  PowerMod[6, -1, 9]   (* Error - no inverse *)
  PowerMod[2, -1, 9]   (* 5 *)
  PowerMod[7, -1, 9]   (* 4 *)
  ```
]

== Type 12: Circular Permutations (E24 Q17)

#rect(inset: 8pt, fill: yellow.lighten(85%), width: 100%)[
  *Standard circular:* $(n-1)!$ (fix one position)

  *If reflections are same:* $(n-1)!/2$
]

#example(title: [E24 Q17: Round table seatings])[
  20 people around a table:

  1. *Same left AND right neighbor:* Standard circular = $19!$
  2. *Same two neighbors (direction ignored):* Divide by 2 = $19!/2$
  3. *Same left neighbor only:* Still $19!$ (same as case 1)
]

== Type 13: Bézout's Identity (E24 Q18)

#rect(inset: 8pt, fill: yellow.lighten(85%), width: 100%)[
  *Key:* $gcd(a, b) = a s + b t$ for some integers $s, t$

  *Corollary:* Any integer $k dot gcd(a, b)$ can be written as $a s + b t$
]

#example(title: [E24 Q18: Linear combinations])[
  *Question:* Which CANNOT be written as $a s + b t$?

  *Analysis:* Only multiples of $gcd(a, b)$ can be written as $a s + b t$.

  $"lcm"(a,b)/gcd(a, b) = (a b)/(gcd(a, b)^2)$ is NOT necessarily a multiple of $gcd(a, b)$.

  *Answer:* $"lcm"(a,b)/gcd(a, b)$
]

== Type 14: Chinese Remainder Theorem (E24 Q22)

#rect(inset: 8pt, fill: yellow.lighten(85%), width: 100%)[
  *Conditions:* Moduli must be pairwise coprime

  *Solution is unique mod* $m_1 dot m_2 dot ... dot m_k$
]

#example(title: [E24 Q22: System of congruences])[
*Solve:* $x equiv 1 pmod(2)$, $x equiv 4 pmod(5)$, $x equiv 3 pmod(7)$

*Typst:*
```typst
  #crt-solve((1, 4, 3), (2, 5, 7))  // (59, 70)
  ```

*Mathematica:*
```mathematica
  ChineseRemainder[{1, 4, 3}, {2, 5, 7}]  (* 59 *)
  ```

*Verify:* $59 = 29(2)+1$, $59 = 11(5)+4$, $59 = 8(7)+3$ ✓

*Answer:* ${59 + 70k : k in ZZ}$
]

== Type 15: GCD Constraints on Products (E24 Q24)

#rect(inset: 8pt, fill: yellow.lighten(85%), width: 100%)[
  *Key Theorem:* If $gcd(a, b) = d$, then $d^2 | a b$
]

#example(title: [E24 Q24: Impossible GCD values])[
*Given:* $a b = 5292 = 2^2 dot 3^3 dot 7^2$

*For $d = gcd(a, b)$, need $d^2 | 5292$*

Check $d = 36 = 2^2 dot 3^2$:
- $d^2 = 2^4 dot 3^4$
- But $5292$ only has $2^2$, so $2^4 divides.not 2^2$ ✗

*Mathematica:*
```mathematica
  FactorInteger[5292]  (* {{2,2}, {3,3}, {7,2}} *)
  Divisible[5292, 36^2]  (* False *)
  ```

*Answer:* 36 cannot be the GCD
]

== Type 16: Proof by Induction (E24 Q25)

#rect(inset: 8pt, fill: yellow.lighten(85%), width: 100%)[
  *Structure:*
  1. State what you're proving
  2. Base case (usually $n=1$ or $n=0$)
  3. Inductive hypothesis: "Assume true for $n$" or "for all $k <= n$"
  4. Inductive step: Prove for $n+1$
  5. Conclusion by principle of induction
]

#example(title: [E24 Q25: Graph edges by induction])[
  *Prove:* Simple graph on $n$ vertices has at most $binom(n, 2)$ edges

  *Correct fragment order:*
  1. E: Base case ($n=1$, 0 edges $<= binom(1, 2) = 0$)
  2. B: Inductive hypothesis (assume for some fixed $n >= 1$)
  3. F: Remove vertex $v$, apply IH to remaining $n$ vertices
  4. D: Count: at most $n + binom(n, 2) = binom(n+1, 2)$ edges
  5. C: Conclusion by induction
]

== Type 17: Derangements (E24 Q21)

#rect(inset: 8pt, fill: yellow.lighten(85%), width: 100%)[
  *Formula:* $D_n = n! sum_(k=0)^n (-1)^k / k!$

  *Values:* $D_0=1, D_1=0, D_2=1, D_3=2, D_4=9, D_5=44, D_6=265, D_7=1854$
]

#example(title: [E24 Q21: Constrained derangements])[
*Question:* Derangements of ${1,...,7}$ ending with ${1,2,3}$ in some order

*Analysis:*
- Positions 5,6,7 must contain 1,2,3 (not in original places anyway) → $3!$ ways
- Positions 1,2,3,4 must contain 4,5,6,7 with no element in its original place
- But 4,5,6,7 going to positions 1,2,3,4 means only position 4 is "dangerous" for element 4

*Count arrangements where 4 is NOT in position 4:*
- Total: $4! = 24$
- With 4 in position 4: $3! = 6$
- Valid: $24 - 6 = 18 = 4! - 3!$

*Total:* $3!(4! - 3!) = 6 times 18 = 108$

*Typst:*
```typst
  #(calc.fact(3) * (calc.fact(4) - calc.fact(3)))  // = 108
  ```
]

== Type 18: Balls into Boxes (E24 Q26)

#rect(inset: 8pt, fill: yellow.lighten(85%), width: 100%)[
  *Distinguishable balls, distinct boxes:*
  - Total ways: $n^k$ (each of $k$ balls has $n$ choices)
  - With constraints: Use inclusion-exclusion or direct counting
]

#example(title: [E24 Q26: $n+1$ balls into $n$ boxes])[
*Total ways:* $n^(n+1)$

*No box empty:* Choose 2 balls for one box (which gets 2), then assign: $binom(n+1, 2) dot n!$

*At least one empty:* Total - No empty = $n^(n+1) - binom(n+1, 2) dot n!$

*Mathematica:*
```mathematica
  n = 5;
  total = n^(n+1)              (* 15625 *)
  noEmpty = Binomial[n+1, 2] * n!  (* 1800 *)
  atLeastOneEmpty = total - noEmpty  (* 13825 *)
  ```
]

#pagebreak()

= Key Formulas & Quick Reference

== Number Theory

#table(
  columns: (1fr, 1.2fr),
  stroke: 0.5pt,
  inset: 6pt,
  [*Formula*],
  [*Description*],
  [$a b = gcd(a, b) dot "lcm"(a,b)$],
  [Fundamental GCD-LCM relation],
  [$gcd(a, b) = s a + t b$ for some $s,t in ZZ$],
  [Bézout's identity],
  [$a equiv b pmod(m) <==> m | (a-b)$],
  [Congruence definition],
  [$a^(-1) mod m$ exists $<==> gcd(a, m) = 1$],
  [Multiplicative inverse exists],
  [$d = gcd(a, b) => d^2 | a b$],
  [GCD constraint on product],
  [$a^(p-1) equiv 1 pmod(p)$ if $p divides.not a$],
  [Fermat's Little Theorem],
  [$a^p equiv a pmod(p)$],
  [Fermat's Little Theorem (alt)],
)

== Combinatorics

#table(
  columns: (1fr, 1.2fr),
  stroke: 0.5pt,
  inset: 6pt,
  [*Formula*],
  [*Description*],
  [$binom(n, k) = n! / (k!(n-k)!)$],
  [Binomial coefficient],
  [$(a+b)^n = sum_(k=0)^n binom(n, k) a^k b^(n-k)$],
  [Binomial theorem],
  [$D_n = n! sum_(k=0)^n (-1)^k / k! approx n!/e$],
  [Derangements (no fixed points)],
  [$k dot binom(n, k) = n dot binom(n-1, k-1)$],
  [Absorption identity],
  [$sum_(k=0)^n binom(n, k) = 2^n$],
  [Sum of binomial coefficients],
  [$binom(n, k) = binom(n-1, k-1) + binom(n-1, k)$],
  [Pascal's identity],
  [$binom(m+n, r) = sum_(k=0)^r binom(m, k) binom(n, r-k)$],
  [Vandermonde's identity],
  [Circular permutations: $(n-1)!$],
  [Arrangements around a circle],
)

== Graph Theory

#table(
  columns: (1fr, 1.2fr),
  stroke: 0.5pt,
  inset: 6pt,
  [*Formula*],
  [*Description*],
  [$Q_n$: vertices $= 2^n$, edges $= n dot 2^(n-1)$],
  [n-cube (hypercube)],
  [$K_n$: edges $= binom(n, 2) = n(n-1)/2$],
  [Complete graph],
  [$sum_(v in V) deg(v) = 2|E|$],
  [Handshaking lemma],
  [Euler circuit exists $<==>$ all degrees even],
  [Euler's theorem],
  [Euler path exists $<==>$ exactly 0 or 2 odd vertices],
  [Euler path condition],
  [Tree on $n$ vertices has $n-1$ edges],
  [Tree edge count],
)

== Set Theory & Inclusion-Exclusion

#table(
  columns: (1fr, 1.2fr),
  stroke: 0.5pt,
  inset: 6pt,
  [*Formula*],
  [*Description*],
  [$|A union B| = |A| + |B| - |A inter B|$],
  [Inclusion-exclusion (2 sets)],
  [$|A union B union C| = sum|A_i| - sum|A_i inter A_j| + |A inter B inter C|$],
  [Inclusion-exclusion (3 sets)],
  [$overline(A inter B) = overline(A) union overline(B)$],
  [De Morgan's law],
  [$overline(A union B) = overline(A) inter overline(B)$],
  [De Morgan's law],
  [Subsets of $n$-element set: $2^n$],
  [Power set cardinality],
  [Even-sized subsets: $2^(n-1)$],
  [Half of all subsets],
)

== Relations

#table(
  columns: (1fr, 1.5fr),
  stroke: 0.5pt,
  inset: 6pt,
  [*Property*],
  [*Definition*],
  [Reflexive],
  [$forall x: (x,x) in R$],
  [Symmetric],
  [$forall x,y: (x,y) in R => (y,x) in R$],
  [Antisymmetric],
  [$forall x,y: [(x,y) in R and (y,x) in R] => x = y$],
  [Transitive],
  [$forall x,y,z: [(x,y) in R and (y,z) in R] => (x,z) in R$],
  [Equivalence relation],
  [Reflexive + Symmetric + Transitive],
  [Partial order],
  [Reflexive + Antisymmetric + Transitive],
)

#pagebreak()

= Core Theorems & Lemmas (from Lectures)

#rect(inset: 10pt, fill: purple.lighten(90%), width: 100%)[
  *Note:* These theorems are organized by topic with lecture date references. Know these for the exam!
]

== Number Theory Theorems

#theorem(title: "Fundamental Theorem of Arithmetic (Oct 2)")[
  Every positive integer $n > 1$ can be factored into primes in a *unique way* (up to ordering).

  $ n = p_1^(alpha_1) dot p_2^(alpha_2) dot dots.c dot p_k^(alpha_k) $
]

#theorem(
  title: "Infinitude of Primes (Oct 2)",
)[
  There are infinitely many primes.

  *Proof idea:* Assume finitely many primes $p_1, dots, p_n$. Consider $N = p_1 dot dots.c dot p_n + 1$. Then $N$ has a prime factor not in our list (contradiction).
]

#theorem(title: "Prime Factor Bound (Oct 2)")[
  If $k = p_1 dot p_2 dot dots.c dot p_n$ (product of $n >= 2$ primes), then some $p_i <= sqrt(k)$.
]

#theorem(title: "Bézout's Identity (Oct 2)")[
  For any $a, b in ZZ$, there exist integers $s, t in ZZ$ such that:
  $ gcd(a, b) = s a + t b $

  The integers $s$ and $t$ are called *Bézout coefficients*.
]

#theorem(
  title: "Divisibility with Coprime Numbers (Oct 2)",
)[
  If $gcd(a, b) = 1$ and $a | b dot c$, then $a | c$.

  *Proof:* Since $gcd(a, b)=1$, by Bézout: $1 = alpha a + beta b$. Multiply by $c$: $c = alpha a c + beta b c$. Since $a | b c$, we have $a | c$.
]

#theorem(title: "Cancellation Law in Modular Arithmetic (Oct 2)")[
  If $gcd(a, m) = 1$, then:
  $ a dot b equiv a dot c pmod(m) arrow.double b equiv c pmod(m) $

  *Warning:* This does NOT hold if $gcd(a, m) != 1$.
]

#theorem(
  title: "Modular Inverse Existence (Oct 9)",
)[
  If $a$ and $m$ are relatively prime (i.e., $gcd(a, m) = 1$), then an inverse of $a mod m$ exists and is unique $mod m$.

  *Finding it:* Use Extended Euclidean Algorithm to find $s$ where $a s + m t = 1$, then $a^(-1) equiv s pmod(m)$.
]

#theorem(title: "Chinese Remainder Theorem (Oct 9)")[
  Let $m_1, m_2, dots, m_n$ be pairwise relatively prime positive integers. The system:
  $ x equiv a_1 pmod(m_1), quad x equiv a_2 pmod(m_2), quad dots, quad x equiv a_n pmod(m_n) $
  has a unique solution modulo $M = m_1 dot m_2 dot dots.c dot m_n$.

  *Formula:* $x = sum_(k=1)^n a_k M_k y_k$ where $M_k = M/m_k$ and $y_k equiv M_k^(-1) pmod(m_k)$.
]

#theorem(title: "Fermat's Little Theorem (Oct 9)")[
  If $p$ is prime and $gcd(a, p) = 1$, then:
  $ a^(p-1) equiv 1 pmod(p) $

  Equivalently, for any integer $a$: $a^p equiv a pmod(p)$

  *Application:* To compute $a^k mod p$, reduce exponent: $a^k equiv a^(k mod (p-1)) pmod(p)$
]

#definition(title: "Pseudoprime and Carmichael Number (Oct 9)")[
  - *Pseudoprime to base $b$*: A composite $n$ with $b^(n-1) equiv 1 pmod(n)$
  - *Carmichael number*: A composite $n$ that is a pseudoprime for ALL bases $b$ with $gcd(b, n)=1$

  Example: $561 = 3 dot 11 dot 17$ is a Carmichael number.
]

== Counting & Combinatorics Theorems

#theorem(
  title: "Product Rule (Oct 30)",
)[
  If a procedure has two independent tasks with $n_1$ and $n_2$ ways respectively, the total ways is $n_1 dot n_2$.

  *Extended:* For $m$ tasks: $n_1 dot n_2 dot dots.c dot n_m$ ways.
]

#theorem(title: "Sum Rule (Oct 30)")[
  If a task can be done in $n_1$ ways OR in $n_2$ ways (disjoint), total ways is $n_1 + n_2$.
]

#theorem(title: "Subtraction Rule / Inclusion-Exclusion (Oct 30)")[
  $ |A_1 union A_2| = |A_1| + |A_2| - |A_1 inter A_2| $
]

#theorem(
  title: "Division Rule (Oct 30)",
)[
  If a procedure can be done in $n$ ways, but every outcome corresponds to exactly $d$ ways, there are $n/d$ distinct outcomes.

  *Application:* Circular permutations of $n$ objects $= n!/n = (n-1)!$
]

#theorem(title: "Pigeonhole Principle (Oct 30)")[
  If $k+1$ objects are placed into $k$ boxes, at least one box contains $>= 2$ objects.
]

#theorem(title: "Generalized Pigeonhole Principle (Oct 30)")[
  If $N$ objects are placed into $k$ boxes, at least one box contains $>= ceil(N/k)$ objects.

  *To guarantee $r$ objects in one box:* Need $N = k(r-1) + 1$ objects.
]

#theorem(title: "Binomial Theorem (Nov 6)")[
  $ (x+y)^n = sum_(k=0)^n binom(n, k) x^(n-k) y^k $
]

#theorem(title: "Pascal's Identity (Nov 6)")[
  $ binom(n, k) = binom(n-1, k) + binom(n-1, k-1) $
]

#theorem(title: "Vandermonde's Identity (Nov 6)")[
  $ binom(m+n, r) = sum_(k=0)^r binom(m, k) binom(n, r-k) $

  *Special case (sum of squares):* $binom(2n, n) = sum_(k=0)^n binom(n, k)^2$
]

#theorem(title: "Hockey Stick Identity (Nov 6)")[
  $ binom(n+1, r+1) = sum_(k=r)^n binom(k, r) $

  *Visual:* Sum diagonally down Pascal's triangle, result is one step down-right.
]

#definition(title: "Derangement Formula (Nov 13)")[
  The number of permutations of $n$ elements with *no fixed points*:
  $ D_n = n! sum_(k=0)^n (-1)^k / k! = n! [1 - 1/1! + 1/2! - 1/3! + dots + (-1)^n / n!] $

  *Approximation:* $D_n approx n!/e approx 0.368 dot n!$
]

#theorem(
  title: "Inclusion-Exclusion Principle (Nov 13)",
)[
  $ |A_1 union dots union A_n| = sum_(i)|A_i| - sum_(i<j)|A_i inter A_j| + sum_(i<j<k)|A_i inter A_j inter A_k| - dots + (-1)^(n+1)|A_1 inter dots inter A_n| $
]

== Induction Theorems

#theorem(title: "Principle of Mathematical Induction (Oct 9/23)")[
  To prove $P(n)$ for all $n >= n_0$:
  1. *Base case:* Prove $P(n_0)$
  2. *Inductive step:* Prove $P(k) arrow.double P(k+1)$ for all $k >= n_0$
]

#theorem(title: "Strong Induction (Oct 23)")[
  To prove $P(n)$ for all $n >= n_0$:
  1. *Base case:* Prove $P(n_0)$ (and possibly $P(n_0+1), dots$)
  2. *Inductive step:* Prove $[P(n_0) and P(n_0+1) and dots and P(k)] arrow.double P(k+1)$

  *Use when:* The proof of $P(k+1)$ requires $P(j)$ for some $j < k$.
]

#theorem(title: "Fibonacci Bound (Oct 23)")[
  For $n >= 3$: $F_n > alpha^(n-2)$ where $alpha = (1+sqrt(5))/2$ (golden ratio).

  *Key property:* $alpha^2 = alpha + 1$
]

== Relations & Partial Orders

#theorem(title: "Equivalence Class Properties (Nov 20)")[
  Let $tilde$ be an equivalence relation on $S$. For any $a, b in S$, the following are equivalent:
  1. $a tilde b$
  2. $[a]_tilde = [b]_tilde$
  3. $[a]_tilde inter [b]_tilde != emptyset$
]

#theorem(title: "Partition Theorem (Nov 20)")[
  The equivalence classes of an equivalence relation on $S$ form a *partition* of $S$:
  - Every element belongs to exactly one equivalence class
  - Distinct equivalence classes are disjoint
  - The union of all equivalence classes equals $S$
]

== Graph Theory Theorems

#lemma(name: "Handshaking Lemma (Nov 27)")[
  In any graph: $ sum_(v in V(G)) deg(v) = 2 |E(G)| $

  *Corollary:* The number of vertices with odd degree is always even.
]

#theorem(title: "Euler Circuit Theorem (Nov 27)")[
  A connected graph has a closed Euler circuit if and only if *every vertex has even degree*.
]

#theorem(title: "Euler Path Theorem (Nov 27)")[
  A connected graph has an Euler path if and only if it has *exactly 0 or 2 vertices of odd degree*.
  - 0 odd vertices: Euler circuit (closed path)
  - 2 odd vertices: Euler path starts/ends at the odd-degree vertices
]

#theorem(
  title: "Hall's Marriage Theorem (Nov 27)",
)[
  A bipartite graph $G = (U union V, E)$ has a matching that covers all vertices in $U$ if and only if for every subset $S subset.eq U$:
  $ |N(S)| >= |S| $
  where $N(S)$ is the set of all neighbors of vertices in $S$.

  *Hall's Condition:* Every subset of $k$ vertices in $U$ must collectively have at least $k$ neighbors in $V$.
]

#definition(
  title: "Graph Isomorphism (Nov 27)",
)[
  Two graphs $G$ and $H$ are *isomorphic* ($G tilde.eq H$) if there exists a bijection $phi: V(G) -> V(H)$ that preserves adjacency:
  $ {u, v} in E(G) arrow.l.r.double {phi(u), phi(v)} in E(H) $

  *Necessary conditions (not sufficient):*
  - Same number of vertices
  - Same number of edges
  - Same degree sequence
]

#definition(
  title: "Bipartite Graph (Nov 27)",
)[
  A graph is *bipartite* if its vertices can be partitioned into two sets $U$ and $V$ such that every edge connects a vertex in $U$ to one in $V$.

  *Characterization:* A graph is bipartite $arrow.l.r.double$ it contains no odd-length cycles.
]

#definition(title: "Tree (Nov 27)")[
  A *tree* is a connected graph with no cycles.

  *Properties:*
  - A tree with $n$ vertices has exactly $n-1$ edges
  - There is exactly one path between any two vertices
  - Removing any edge disconnects the tree
]

== Additional Important Results

#theorem(
  title: "Erdős–Szekeres Theorem / Monotone Subsequences (Oct 30)",
)[
  Every sequence of $n^2 + 1$ distinct real numbers contains a monotone subsequence of length $n+1$ (either strictly increasing or strictly decreasing).

  *Proof idea:* Associate each term with pair $(i_k, d_k)$ = (longest increasing from $k$, longest decreasing from $k$). If both $<= n$, at most $n^2$ pairs, but we have $n^2+1$ terms → contradiction by pigeonhole.
]

#theorem(
  title: "Ramsey's Theorem R(3,3) = 6 (Oct 30)",
)[
  In any group of 6 people, there exist either 3 mutual friends or 3 mutual enemies.

  *Proof:* Pick any person A. Of 5 others, $>= 3$ are friends OR $>= 3$ are enemies of A (pigeonhole with $ceil(5/2)=3$). If 3 are friends of A, either two of them are friends (giving 3 mutual friends with A), or all three are mutual enemies.
]

#theorem(title: "GCD Constraint on Products (Oct 2)")[
  If $gcd(a, b) = d$, then $d^2 | a b$.

  *Application:* Given $a b = N$, to check if $d$ can be $gcd(a, b)$, verify $d^2 | N$.
]

#theorem(title: "LCM-GCD Relationship (Oct 2)")[
  $ gcd(a, b) dot "lcm"(a, b) = a dot b $

  Using prime factorizations: $gcd$ takes minimum exponents, $"lcm"$ takes maximum exponents.
]

#pagebreak()

= Additional Examples + Solutions

#rect(inset: 8pt, fill: green.lighten(90%), width: 100%)[
  *Tip:* The examples below complement the exam question types above. Use both sections together!
]

== Number Theory

=== Divisibility

#example(title: [Divisibility with $a b | c d$])[
  If $a,b,c,d$ are positive integers such that $a b | c d$, which must be true?

  #solution[
    *Key insight:* $a b | c d$ does NOT imply $a|c$ or $a|d$ individually.

    *True statement:* "If $p$ is a prime that divides $a$, then $p|c$ or $p|d$"

    *Proof:* If $p|a$ and $a b | c d$, then $p | c d$. Since $p$ is prime, $p|c$ or $p|d$.

    *Counterexample:* Let $a=6, b=1, c=2, d=3$. Then $a b = 6 | 6 = c d$.
    - But $gcd(a, b) = 6$ does not divide $gcd(c, d) = 1$
    - And $6 divides.not c$ and $6 divides.not d$
  ]
]

#example(title: [GCD as linear combination])[
  Let $a,b$ be positive integers. Which can NOT necessarily be written as $a s + b t$ for $s,t in ZZ$?

  #solution[
    *Bézout's identity:* $gcd(a, b) = a s + b t$ for some $s,t in ZZ$.

    Any *multiple* of $gcd(a, b)$ can be written as $a s + b t$.

    *Answer:* $"lcm"(a,b)/gcd(a, b) = a b / gcd(a, b)^2$ is NOT necessarily a multiple of $gcd(a, b)$.
  ]
]

=== GCD Constraints

#example(title: [Possible GCD values given product])[
  Let $a,b$ be positive integers with $a b = 5292 = 2^2 dot 3^3 dot 7^2$. Which CANNOT be $gcd(a, b)$?

  Options: 1, 3, 36, 42

  #solution[
    *Key fact:* If $gcd(a, b) = d$, then $d^2 | a b$.

    Check each:
    - $d = 1$: $1^2 = 1 | 5292$ (valid)
    - $d = 3$: $3^2 = 9 | 5292$ (valid, since $3^3 | 5292$)
    - $d = 36 = 2^2 dot 3^2$: Need $36^2 = 2^4 dot 3^4 | 2^2 dot 3^3 dot 7^2$. But $2^4 divides.not 2^2$!
    - $d = 42 = 2 dot 3 dot 7$: $42^2 = 2^2 dot 3^2 dot 7^2 | 2^2 dot 3^3 dot 7^2$ (valid)

    #rect(inset: 6pt)[*Answer:* 36 cannot be the GCD.]
  ]
]

=== Modular Arithmetic

#example(title: [Congruence cancellation])[
  If $a c equiv b c pmod(m)$, when can we conclude $a equiv b pmod(m)$?

  #solution[
    $a c equiv b c pmod(m)$ means $m | c(a-b)$.

    *Cancellation Law:* If $gcd(c, m) = 1$, then $a equiv b pmod(m)$.

    *Counterexample when $gcd(c, m) != 1$:*
    $2 dot 3 equiv 2 dot 6 pmod(6)$ (both $equiv 0$), but $3 equiv.not 6 pmod(6)$.
  ]
]

#example(title: [Finding multiplicative inverses mod 9])[
  Find the multiplicative inverse of $n mod 9$ for $n = 2, 6, 7$.

  #solution[
    Inverse exists iff $gcd(n, 9) = 1$.

    *For $n = 6$:* $gcd(6, 9) = 3 != 1$ → #rect(inset: 4pt)[Does not exist]

    *For $n = 2$:* $gcd(2, 9) = 1$. Find $x$ with $2x equiv 1 pmod(9)$:
    - $2 dot 5 = 10 equiv 1 pmod(9)$ → #rect(inset: 4pt)[*5*]

    *For $n = 7$:* $gcd(7, 9) = 1$. Find $x$ with $7x equiv 1 pmod(9)$:
    - $7 dot 4 = 28 equiv 1 pmod(9)$ → #rect(inset: 4pt)[*4*]
  ]
]

=== Chinese Remainder Theorem

#example(title: [System of congruences])[
  Solve: $x equiv 1 pmod(2)$, $x equiv 4 pmod(5)$, $x equiv 3 pmod(7)$

  #solution[
    Moduli 2, 5, 7 are pairwise coprime, so unique solution mod $2 dot 5 dot 7 = 70$.

    *Method: Back substitution*

    *Step 1:* From $x equiv 1 pmod(2)$: $x = 1 + 2t_1$

    *Step 2:* Substitute into $x equiv 4 pmod(5)$:
    $1 + 2t_1 equiv 4 pmod(5) ==> 2t_1 equiv 3 pmod(5)$

    Inverse of 2 mod 5: $2 dot 3 = 6 equiv 1$, so $t_1 equiv 3 dot 3 = 9 equiv 4 pmod(5)$

    Thus $t_1 = 4 + 5t_2$, giving $x = 1 + 2(4 + 5t_2) = 9 + 10t_2$

    *Step 3:* Substitute into $x equiv 3 pmod(7)$:
    $9 + 10t_2 equiv 3 pmod(7) ==> 2 + 3t_2 equiv 3 pmod(7) ==> 3t_2 equiv 1 pmod(7)$

    Inverse of 3 mod 7: $3 dot 5 = 15 equiv 1$, so $t_2 equiv 5 pmod(7)$

    Thus $t_2 = 5 + 7t_3$, giving $x = 9 + 10(5) = 59$

    #rect(inset: 6pt)[*Answer:* $x equiv 59 pmod(70)$]

    *Verify:* $59 = 29 dot 2 + 1$, $59 = 11 dot 5 + 4$, $59 = 8 dot 7 + 3$
  ]
]

== Functions: Injective/Surjective Analysis

#example(title: [Function classification])[
  Classify each function:
  1. $f: ZZ^+ -> NN$ given by $f(x) = floor(log_2(x))$
  2. $f: NN -> ZZ$ given by $f(x) = cases(ceil(x\/2) "if" x "even", -ceil(x\/2) "if" x "odd")$
  3. $f: NN -> NN$ given by $f(x) = x^3 + 1$

  #solution[
    *1. $f(x) = floor(log_2(x))$, $ZZ^+ -> NN$:*
    - Surjective? Every $n in NN$ is hit by $x = 2^n$. Yes
    - Injective? $f(2) = f(3) = 1$. No
    - *Surjective but not injective*

    *2. Alternating function $NN -> ZZ$:*
    - $f(0) = 0, f(1) = -1, f(2) = 1, f(3) = -2, f(4) = 2, ...$
    - Surjective? Hits all of $ZZ$. Yes
    - Injective? Each output appears exactly once. Yes
    - *Bijection*

    *3. $f(x) = x^3 + 1$, $NN -> NN$:*
    - Injective? $x^3$ is strictly increasing. Yes
    - Surjective? $f(0) = 1, f(1) = 2, f(2) = 9, ...$ — skips 3,4,5,6,7,8. No
    - *Injective but not surjective*
  ]
]

=== Using the Function Checker

#example(title: [Checking function properties with `check-function`])[
  Verify properties of $f(x) = floor(log_2(x))$ on domain ${1,2,...,8}$ onto ${0,1,2,3}$:

  #solution[
    #let floor_log2 = (x) => {
      if x <= 0 { return none }
      calc.floor(calc.log(x, base: 2))
    }
    #let result = check-function(floor_log2, (1, 2, 3, 4, 5, 6, 7, 8), codomain: (0, 1, 2, 3))

    #show-function-check(result, func-name: "f")

    *Analysis:*
    - Mapping: $f(1)=0, f(2)=1, f(3)=1, f(4)=2, f(5)=2, f(6)=2, f(7)=2, f(8)=3$
    - Not injective because $f(2) = f(3) = 1$ (and others)
    - Surjective because all outputs ${0,1,2,3}$ are hit

    *More examples:*

    #let sq_result = check-function((x) => x * x, (0, 1, 2, 3), codomain: (0, 1, 4, 9))
    #let mod_result = check-function((x) => calc.rem(x, 5), (0, 1, 2, 3, 4), codomain: (0, 1, 2, 3, 4))
    #let abs_result = check-function(calc.abs, (-2, -1, 0, 1, 2), codomain: (0, 1, 2))

    #table(
      columns: (1.5fr, 1fr, 1fr, 1fr),
      stroke: 0.5pt,
      inset: 6pt,
      [*Function*],
      [*Injective*],
      [*Surjective*],
      [*Bijective*],
      [$f(x) = x^2$ on ${0,1,2,3}$ #linebreak() onto ${0,1,4,9}$],
      [#{ if sq_result.injective [Yes] else [No] }],
      [#{ if sq_result.surjective [Yes] else [No] }],
      [#{ if sq_result.bijective [Yes] else [No] }],
      [$f(x) = x mod 5$ on ${0,1,2,3,4}$],
      [#{ if mod_result.injective [Yes] else [No] }],
      [#{ if mod_result.surjective [Yes] else [No] }],
      [#{ if mod_result.bijective [Yes] else [No] }],
      [$f(x) = |x|$ on ${-2,-1,0,1,2}$ #linebreak() onto ${0,1,2}$],
      [#{ if abs_result.injective [Yes] else [No] }],
      [#{ if abs_result.surjective [Yes] else [No] }],
      [#{ if abs_result.bijective [Yes] else [No] }],
    )
  ]
]

== Graph Theory

=== Hypercube and Complete Graphs

#example(title: [Edges in $Q_n$ and $K_n$])[
  *Hypercube $Q_n$:*
  - Vertices: $2^n$ (all $n$-bit binary strings)
  - Each vertex has degree $n$ (can flip any of $n$ bits)
  - By handshaking: $2|E| = 2^n dot n$, so $|E| = n dot 2^(n-1)$

  *Complete graph $K_n$:*
  - Every pair of vertices connected: $|E| = binom(n, 2) = n(n-1)/2$

  *For $K_(2n)$:* edges $= binom(2n, 2) = (2n)(2n-1)/2 = n(2n-1)$

  Alternative form: $2binom(n, 2) + n^2 = n(n-1) + n^2 = n(2n-1)$
]

=== Degree Sequences

#example(title: [Valid degree sequence?])[
  Does a simple graph with degrees $2,2,3,3,3,3,3$ exist?

  #solution[
    Sum of degrees $= 2+2+3+3+3+3+3 = 19$.

    By handshaking lemma: $sum deg(v) = 2|E|$ must be even.

    Since $19$ is odd, #rect(inset: 4pt)[such a graph does not exist.]
  ]
]

=== Euler Circuits

#example(title: [Königsberg Bridge Problem])[
  A graph has an Euler circuit iff:
  1. The graph is connected
  2. Every vertex has even degree

  A graph has an Euler path iff:
  1. The graph is connected
  2. Exactly 0 or 2 vertices have odd degree

  In Königsberg: degrees are 5, 3, 3, 3 (all odd) → No Euler path or circuit.
]

== Combinatorics

=== Binomial Theorem

#example(title: [Coefficient in $(2x^2 - 3y^3)^8$])[
  Find coefficients of $x^8 y^{12}$ and $x^6 y^9$.

  #solution[
    General term: $binom(8, k)(2x^2)^k (-3y^3)^(8-k) = binom(8, k) 2^k (-3)^(8-k) x^(2k) y^(3(8-k))$

    *For $x^8 y^{12}$:* Need $2k = 8$ and $3(8-k) = 12$.
    - $k = 4$ (valid)
    - #rect(inset: 4pt)[Coefficient: $binom(8, 4) dot 2^4 dot (-3)^4 = 70 dot 16 dot 81 = 90720$]

    *For $x^6 y^9$:* Need $2k = 6$ and $3(8-k) = 9$.
    - $k = 3$ but $8-k = 5$, and $3 dot 5 = 15 != 9$ (invalid)
    - #rect(inset: 4pt)[Coefficient is 0]
  ]
]

=== Inclusion-Exclusion

#example(
  title: [Union of four sets],
)[
  Each of 4 sets has 200 elements, each pair shares 50, each triple shares 25, all four share 5. Find $|A union B union C union D|$.

  #solution[
    $|A union B union C union D| = binom(4, 1) dot 200 - binom(4, 2) dot 50 + binom(4, 3) dot 25 - binom(4, 4) dot 5$

    $= 4(200) - 6(50) + 4(25) - 1(5) = 800 - 300 + 100 - 5 = 595$
  ]
]

=== Derangements

#example(title: [Derangement formula and values])[
  $D_n = n! sum_(k=0)^n (-1)^k / k! = n! (1 - 1/1! + 1/2! - 1/3! + ...)$

  First few values:
  - $D_0 = 1$, $D_1 = 0$, $D_2 = 1$, $D_3 = 2$
  - $D_4 = 9$, $D_5 = 44$, $D_6 = 265$, $D_7 = 1854$

  *Recurrence:* $D_n = (n-1)(D_(n-1) + D_(n-2))$

  *Approximation:* $D_n approx n!/e$ (rounds to nearest integer for $n >= 1$)
]

=== Circular Permutations

#example(title: [20 people around a round table])[
  Count seatings where two arrangements are identical if:
  1. Each person has same two neighbors (ignoring direction)
  2. Each person has same left AND right neighbor

  #solution[
    *Case 2 (same left AND right neighbor):*
    - Standard circular permutation: $(n-1)! = 19!$
    - Fix one person's position, arrange remaining $19$ people.

    *Case 1 (same two neighbors, ignoring direction):*
    - Each arrangement counted twice (clockwise vs counterclockwise)
    - Answer: $19!/2$
  ]
]

== Relations

#example(title: [Classify relations on ${1,2,3,4,5,6}$])[
  $R_1 = {(1,2),(2,3),(1,3),(4,5),(5,6),(4,6)}$

  #solution[
    - Reflexive? Missing $(1,1), (2,2), ...$ (no)
    - Symmetric? $(1,2) in R$ but $(2,1) in.not R$ (no)
    - Antisymmetric? No pair $(x,y), (y,x)$ with $x != y$ both present (yes)
    - Transitive? $(1,2),(2,3) in R$ and $(1,3) in R$; $(4,5),(5,6) in R$ and $(4,6) in R$ (yes)
    - #rect(inset: 4pt)[Transitive and antisymmetric only]
  ]
]

#example(title: [Equivalence classes mod 4])[
  The equivalence relation of congruence modulo 4 on $ZZ$:
  $
    [0]_(mod 4) &= {..., -8, -4, 0, 4, 8, ...} \
    [1]_(mod 4) &= {..., -7, -3, 1, 5, 9, ...} \
    [2]_(mod 4) &= {..., -6, -2, 2, 6, 10, ...} \
    [3]_(mod 4) &= {..., -5, -1, 3, 7, 11, ...}
  $
  These four equivalence classes *partition* the integers.
]

== Partitions of Sets

#example(title: [Partitions of $ZZ times ZZ$])[
  Which are partitions?

  (a) ${(x,y): x "or" y "odd"}$ and ${(x,y): x "and" y "even"}$

  (b) ${(x,y): x "and" y "odd"}$ and ${(x,y): x "and" y "even"}$

  #solution[
    Every $(x,y)$ falls into one of 4 categories: EE, OO, EO, OE

    *(a):* "$x$ or $y$ odd" = OO ∪ EO ∪ OE. "$x$ and $y$ even" = EE.
    - Disjoint? Yes. Cover everything? Yes.
    - *YES, this is a partition*

    *(b):* "$x$ and $y$ odd" = OO. "$x$ and $y$ even" = EE.
    - Missing EO and OE!
    - *NO, doesn't cover everything*
  ]
]

== Proof by Induction

#example(
  title: [Strong induction: Pie-throwing problem],
)[
  Prove: If $2n+1$ people throw pies at their nearest neighbor, at least one survives.

  #solution[
    *Base case ($n=1$):* 3 people. Closest pair (A, B) throw at each other. Third person C's nearest is either A or B. So A and B each receive one pie, C receives 0. C survives.

    *Inductive step:* Assume true for $2k+1$ people. Consider $2(k+1)+1 = 2k+3$ people.

    Let A and B be the closest pair (they throw at each other).

    *Case 1:* No one else throws at A or B. The remaining $2k+1$ people form an independent group → by IH, at least one survivor.

    *Case 2:* At least one other person throws at A or B. Then $>= 3$ pies hit A or B combined. Remaining pies: $<= 2k+3-3 = 2k$ for $2k+1$ people. By pigeonhole, someone survives.
  ]
]

#example(title: [Checkerboard tiling with L-triominoes])[
  Every $2^n times 2^n$ checkerboard with one square removed can be tiled by L-triominoes.

  #solution[
    *Base case ($n=1$):* $2 times 2$ board with one square removed = L-triomino.

    *Inductive step:* Assume true for $2^k times 2^k$. For $2^(k+1) times 2^(k+1)$ board:

    1. Divide into four $2^k times 2^k$ quadrants
    2. The removed square is in one quadrant
    3. Place one L-triomino at the center, covering one square from each of the other three quadrants
    4. Now each quadrant is a $2^k times 2^k$ board with one square removed
    5. By IH, each can be tiled.
  ]
]

== Polynomial Divisibility

#example(title: [$x^n + 1$ divisible by $x + 1$])[
  For which positive integers $n$ is $x^n + 1$ divisible by $x + 1$?

  #solution[
    $x + 1 | x^n + 1$ iff $x = -1$ is a root of $x^n + 1$.

    Evaluate at $x = -1$: $(-1)^n + 1$
    - If $n$ odd: $(-1)^n = -1$, so $-1 + 1 = 0$ (root)
    - If $n$ even: $(-1)^n = 1$, so $1 + 1 = 2 != 0$ (not a root)

    #rect(inset: 6pt)[Divisible for all odd $n$, not divisible for any even $n$.]
  ]
]

== Pigeonhole Principle

#example(title: [Simple graphs with all distinct degrees])[
  Can a simple graph on $n >= 2$ vertices have all distinct degrees?

  #solution[
    *Claim: NO* (by pigeonhole)

    In a simple graph on $n$ vertices:
    - Possible degrees: $0, 1, 2, ..., n-1$ (that's $n$ values)
    - For all degrees distinct, we need exactly ${0, 1, 2, ..., n-1}$

    *But:*
    - Degree 0 means isolated (no neighbors)
    - Degree $n-1$ means connected to all others
    - These can't coexist! (vertex with degree $n-1$ would connect to the isolated vertex)

    *Conclusion:* No simple graph on $n >= 2$ vertices has all distinct degrees.
  ]
]

== Hall's Theorem / Matching

#example(
  title: [Bipartite matching condition],
)[
  *Hall's Marriage Theorem:* A bipartite graph with parts $X$ and $Y$ has a matching saturating $X$ iff for every subset $S subset.eq X$:
  $ |N(S)| >= |S| $
  where $N(S)$ = neighbors of $S$ in $Y$.

  *Application:* 10 computers, 5 printers. Minimum cables so any 5 computers can print to 5 different printers?

  #solution[
    Need: every subset of 5 computers has 5 distinct printer neighbors.

    If a printer connects to $< 6$ computers, we could choose 5 computers that don't include any connected to that printer, violating Hall's condition.

    Each printer must connect to $>= 6$ computers.

    *Minimum cables:* $5 times 6 = 30$
  ]
]

== Propositional Logic (Truth Sayer/Liar Puzzles)

#example(title: [Truth Sayer and Liar Logic])[
  Peter says: "At least one of us is a liar." What are Peter and Signe?

  #solution[
    Let $P$ = "Peter is truth sayer", $S$ = "Signe is truth sayer"

    Peter's claim: $not P or not S$

    *Key:* If Peter is a truth sayer, his claim must be true. If he's a liar, his claim must be false.

    $ P arrow.l.r.double (not P or not S) $

    #table(
      columns: 4,
      [$P$],
      [$S$],
      [$not P or not S$],
      [$P arrow.l.r.double (not P or not S)$],
      [T],
      [T],
      [F],
      [F],
      [T],
      [F],
      [T],
      [*T*],
      [F],
      [T],
      [T],
      [F],
      [F],
      [F],
      [T],
      [F],
    )

    *Answer:* Peter is a truth sayer, Signe is a liar.
  ]
]

== Perfect Numbers

#example(title: [Verify perfect numbers])[
  Show that 6 and 28 are perfect numbers (equal to sum of proper divisors).

  #solution[
    *For 6:* Divisors (excluding 6): $1, 2, 3$
    $ 1 + 2 + 3 = 6 $

    *For 28:* Divisors (excluding 28): $1, 2, 4, 7, 14$
    $ 1 + 2 + 4 + 7 + 14 = 28 $

    *Theorem:* $2^(p-1)(2^p - 1)$ is perfect when $2^p - 1$ is prime (Mersenne prime).

    Example: $p = 3$, $2^3 - 1 = 7$ (prime), so $2^2 dot 7 = 28$ is perfect.
  ]
]

== Set Operations Proofs

#example(title: [Prove $(A - C) inter (C - B) = emptyset$])[
  #solution[
    $(A - C)$ = elements in $A$ but not in $C$

    $(C - B)$ = elements in $C$ but not in $B$

    For $x in (A - C) inter (C - B)$:
    - $x in A - C$ means $x in A$ and $x in.not C$
    - $x in C - B$ means $x in C$ and $x in.not B$

    *Contradiction:* $x in.not C$ and $x in C$ cannot both be true.

    Therefore $(A - C) inter (C - B) = emptyset$.
  ]
]

#example(title: [Prove $(B - A) union (C - A) = (B union C) - A$])[
  #solution[
    *LHS:* $x in (B - A) union (C - A)$
    - $x in B - A$ or $x in C - A$
    - $(x in B and x in.not A)$ or $(x in C and x in.not A)$
    - $(x in B or x in C)$ and $x in.not A$

    *RHS:* $x in (B union C) - A$
    - $x in B union C$ and $x in.not A$
    - $(x in B or x in C)$ and $x in.not A$

    #rect(inset: 6pt)[Both sides are equivalent.]
  ]
]

== Equivalence Relations

#example(title: [Cardinality as equivalence relation])[
  Let $R$ on sets of real numbers: $S R T$ iff $|S| = |T|$.

  #solution[
    *Reflexive:* $|S| = |S|$ (yes)

    *Symmetric:* $|S| = |T| arrow.double |T| = |S|$ (yes)

    *Transitive:* $|S| = |T|$ and $|T| = |U| arrow.double |S| = |U|$ (yes)

    #rect(inset: 4pt)[This is an equivalence relation.]

    *Equivalence classes:*
    - $[{0, 1, 2}]$ = all sets with exactly 3 elements
    - $[ZZ]$ = all countably infinite sets (includes $NN$, $QQ$)
  ]
]

#example(title: [Rational equivalence: $(a,b) R (c,d)$ iff $a d = b c$])[
  #solution[
    This is an equivalence relation (represents fractions $a/b = c/d$).

    *Reflexive:* $a dot b = b dot a$ (yes)

    *Symmetric:* $a d = b c arrow.double c b = d a$ (yes)

    *Transitive:* If $a d = b c$ and $c f = d e$, then:
    - Multiply: $a d f = b c f = b d e$
    - Since $d > 0$: $a f = b e$ (yes)

    #rect(inset: 4pt)[This is an equivalence relation.]

    Equivalence class of $(1, 2)$: all pairs $(k, 2k)$ for $k in ZZ^+$
  ]
]

== Generalized Pigeonhole

#example(
  title: [Generalized pigeonhole for $n$ boxes],
)[
  If $n_1 + n_2 + ... + n_t - t + 1$ objects are placed in $t$ boxes, then some box $i$ contains at least $n_i$ objects.

  #solution[
    *Proof by contradiction:*

    Assume each box $i$ contains fewer than $n_i$ objects (at most $n_i - 1$).

    Total objects $<= (n_1 - 1) + (n_2 - 1) + ... + (n_t - 1) = sum n_i - t$

    But we have $sum n_i - t + 1$ objects.

    $sum n_i - t + 1 <= sum n_i - t$ implies $1 <= 0$. Contradiction!
  ]
]

== Polynomial Division (using auto-div)

#example(title: [Polynomial division with auto-div])[
  Divide $x^4 + 3x^3 + 5/2 x + 6$ by $x + 2$:

  $ #poly-div-working((1, 3, 0, "5/2", 6), (1, 2)) $
]

= Calculation Workspace

== Quick Reference: Built-in Typst Functions

#table(
  columns: 3,
  stroke: 0.5pt,
  inset: 6pt,
  [*Function*],
  [*Example*],
  [*Result*],
  [`calc.gcd(a, b)`],
  [`calc.gcd(48, 18)`],
  [#calc.gcd(48, 18)],
  [`calc.lcm(a, b)`],
  [`calc.lcm(12, 18)`],
  [#calc.lcm(12, 18)],
  [`calc.fact(n)`],
  [`calc.fact(6)`],
  [#calc.fact(6)],
  [`calc.binom(n, k)`],
  [`calc.binom(10, 3)`],
  [#calc.binom(10, 3)],
  [`calc.perm(n, k)`],
  [`calc.perm(5, 3)`],
  [#calc.perm(5, 3)],
  [`calc.rem(a, b)`],
  [`calc.rem(17, 5)`],
  [#calc.rem(17, 5)],
  [`calc.quo(a, b)`],
  [`calc.quo(17, 5)`],
  [#calc.quo(17, 5)],
  [`calc.pow(a, b)`],
  [`calc.pow(2, 10)`],
  [#calc.pow(2, 10)],
)

== Binomial Coefficients

#show-binom(10, 5)
#show-binom(8, 4)
#show-binom(20, 10)
#show-binom(15, 7)

== Factorials

#show-fact(5)
#show-fact(7)
#show-fact(10)

== Derangements

#show-derangement(4)
#show-derangement(5)
#show-derangement(6)
#show-derangement(7)

== GCD and LCM

#show-gcd(48, 18)
#show-gcd(5292, 36)
#show-gcd(662, 414)
#show-lcm(12, 18)
#show-lcm(24, 36)

== Bézout Coefficients (Extended Euclidean Algorithm)

#show-bezout(48, 18)
#show-bezout(35, 15)
#show-bezout(662, 414)

== Modular Inverses

#show-mod-inverse(2, 9)
#show-mod-inverse(6, 9)
#show-mod-inverse(7, 9)
#show-mod-inverse(3, 7)
#show-mod-inverse(5, 12)

== Chinese Remainder Theorem

#show-crt((1, 4, 3), (2, 5, 7))
#show-crt((2, 3, 5), (3, 5, 7))

== Graph Theory Quick Calculations

$ Q_4: #calc.pow(2, 4) "vertices", #hypercube-edges(4) "edges" $
$ Q_5: #calc.pow(2, 5) "vertices", #hypercube-edges(5) "edges" $
$ K_6: 6 "vertices", #complete-edges(6) "edges" $
$ K_(10): 10 "vertices", #complete-edges(10) "edges" $
$ K_(20): 20 "vertices", #complete-edges(20) "edges" $

== Inclusion-Exclusion (4 sets with equal intersections)

#let ie4(singles, pairs, triples, quad) = {
  4 * singles - 6 * pairs + 4 * triples - quad
}

$ |A union B union C union D| = 4(200) - 6(50) + 4(25) - 5 = #ie4(200, 50, 25, 5) $

== Primality and Primes

#show-is-prime(17)
#show-is-prime(91)
#show-is-prime(97)
#show-primes-below(30)

== General Linear Congruences

Solve $a x equiv c pmod(m)$:

#show-solve-congruence(3, 6, 9)
#show-solve-congruence(4, 5, 9)
#show-solve-congruence(6, 15, 21)

== Division with Remainder

#show-division(17, 5)
#show-division(100, 7)
#show-division(5292, 36)

== Relation Properties

#show-relation-properties((1, 2, 3), ((1, 1), (2, 2), (3, 3), (1, 2), (2, 1)), name: "R₁")

#show-relation-properties((1, 2, 3), ((1, 1), (2, 2), (3, 3), (1, 2), (2, 3), (1, 3)), name: "R₂")

== Function Property Checker

Check if functions are injective/surjective/bijective on finite domains:

#table(columns: (2fr, 3fr), stroke: 0.5pt, inset: 8pt, [*Usage*], [*Code*], [Define function], [```typst
#let my_func = (x) => calc.floor(calc.log(x, base: 2))
```], [Check properties], [```typst
#let result = check-function(
  my_func,
  (1, 2, 3, 4, 5, 6, 7, 8),  // domain
  codomain: (0, 1, 2, 3)      // codomain (optional)
)
```], [Display results], [```typst
#show-function-check(result, func-name: "f")
```])

*Quick examples:*

#let floor_log2 = (x) => calc.floor(calc.log(x, base: 2))
#let r1 = check-function(floor_log2, (1, 2, 3, 4, 5, 6, 7, 8), codomain: (0, 1, 2, 3))
- $f(x) = floor(log_2(x))$: Inj: #if r1.injective [Yes] else [No], Surj: #if r1.surjective [Yes] else [No], Bij: #if r1.bijective [Yes] else [No]

#let r2 = check-function((x) => x * x, (0, 1, 2, 3), codomain: (0, 1, 4, 9))
- $g(x) = x^2$ on ${0,1,2,3}$: Inj: #if r2.injective [Yes] else [No], Surj: #if r2.surjective [Yes] else [No], Bij: #if r2.bijective [Yes] else [No]

#let r3 = check-function(calc.abs, (-2, -1, 0, 1, 2), codomain: (0, 1, 2))
- $h(x) = |x|$ on ${-2,...,2}$: Inj: #if r3.injective [Yes] else [No], Surj: #if r3.surjective [Yes] else [No], Bij: #if r3.bijective [Yes] else [No]

*Note:* Only works for finite domains. For infinite domains (ℤ, ℕ, ℝ), use mathematical proofs.

== Your Calculations Here

// Add your exam calculations below

// GCD and Bézout coefficients:
// #show-bezout(your_a, your_b)

// Modular inverse:
// #show-mod-inverse(n, m)

// Chinese Remainder Theorem:
// #show-crt((r1, r2, r3), (m1, m2, m3))

// Binomial coefficient:
// #show-binom(n, k)

// Derangement:
// #show-derangement(n)

// Primality check:
// #show-is-prime(n)

// Primes below n:
// #show-primes-below(n)

// General linear congruence ax ≡ c (mod m):
// #show-solve-congruence(a, c, m)

#pagebreak()

= 2025 Exam Examples with SymPy & Mathematica Code

#rect(inset: 12pt, fill: red.lighten(85%), width: 100%)[
*COMMON MISTAKES TO AVOID:*
- Always put the POLYNOMIAL inside `Coefficient[]`, not the monomial you're looking for!
- Wrong: `Coefficient[Expand[x^15 y^20], ...]` ← This just gives you `x^15 y^20`
- Right: `Coefficient[Expand[(2x^3 - y^4)^10], x^15 y^20]`
]

== Euler's Totient Function (2025 Q1)

#rect(inset: 8pt, fill: yellow.lighten(85%), width: 100%)[
  *Formula:* For distinct primes $p, q$: $phi(p q) = (p-1)(q-1) = p q - p - q + 1$
]

#example(
  title: [2025 Q1: φ(pq) for primes p < q],
)[
*Question:* If $p,q$ are primes with $100 < p < q$, how many positive integers less than $p q$ are relatively prime to $p q$?

*Solution:* This is Euler's totient function!
$ phi(p q) = (p-1)(q-1) = p q - p - q + 1 $

*SymPy:*
```python
  from sympy import symbols, expand
  p, q = symbols('p q')
  phi_pq = (p - 1) * (q - 1)
  print(expand(phi_pq))  # p*q - p - q + 1
  ```

*Mathematica:*
```mathematica
  Expand[(p - 1)(q - 1)]  (* p q - p - q + 1 *)
  EulerPhi[101 * 103]     (* Verify with specific primes: 10200 *)
  (101-1)*(103-1)         (* 10200 ✓ *)
  ```

*Answer:* $p q - p - q + 1$ (Option 1)
]

== Modular Exponentiation (2025 Q2)

#example(title: [2025 Q2: $(4^100 mod 6)^100 mod 10$])[
*Step-by-step:*
1. First: $4^100 mod 6$
2. Then: $(text("result"))^100 mod 10$

*SymPy:*
```python
  step1 = pow(4, 100, 6)   # 4
  step2 = pow(step1, 100, 10)  # 6
  print(f"Answer: {step2}")  # 6
  ```

*Mathematica:*
```mathematica
  PowerMod[4, 100, 6]      (* 4 *)
  PowerMod[4, 100, 10]     (* 6 *)
  ```

*Answer:* 6 (Option 2)
]

== Subset Counting with Parity Constraints (2025 Q3)

#rect(
  inset: 8pt,
  fill: yellow.lighten(85%),
  width: 100%,
)[
  *Key Insight:* In a set of $n$ elements, exactly half the subsets have an odd number of elements, half have even.

  For $n$ odd elements: $2^(n-1)$ subsets with odd count, $2^(n-1)$ with even count.

  For $n$ even elements: $2^(n-1)$ subsets with odd count, $2^(n-1)$ with even count.
]

#example(title: [2025 Q3: Subsets of {1,...,99}])[
*Setup:* {1,...,99} has 50 odd numbers and 49 even numbers.

*Part a: Odd \# of odds AND even \# of evens*
- Odd \# from 50 odds: $2^(50-1) = 2^49$ ways
- Even \# from 49 evens: $2^(49-1) = 2^48$ ways
- Total: $2^49 times 2^48 = 2^97$
- *Answer:* $2^97$

*Part b: Odd \# of evens AND even \# of odds*
- Odd \# from 49 evens: $2^48$ ways
- Even \# from 50 odds: $2^49$ ways
- Total: $2^48 times 2^49 = 2^97$
- *Answer:* $2^97$ (NOT "None of these"!)

*Part c: Subsets with 49 elements*
- Simply $binom(99, 49)$
- This is NOT $2^49$ or any other listed option
- *Answer:* None of these (Option 5)

*Part d: Odd \# of odd numbers*
- Odd \# from 50 odds: $2^49$ ways
- Any subset of 49 evens: $2^49$ ways
- Total: $2^49 times 2^49 = 2^98$
- *Answer:* $2^98$

*SymPy:*
```python
  from math import comb
  # Part c verification
  print(comb(99, 49))  # 4.96e28, not 2^49 = 5.6e14
  print(2**49)  # 562949953421312
  ```
]

== Chinese Remainder Theorem (2025 Q4)

#example(title: [2025 Q4: Solve system of congruences])[
*System:*
$ x &equiv 1 pmod(2) \
x &equiv 1 pmod(5) \
x &equiv 7 pmod(9) $

*SymPy:*
```python
  from sympy.ntheory.modular import solve_congruence
  result = solve_congruence((1, 2), (1, 5), (7, 9))
  print(result)  # (61, 90)
  # Answer: x ≡ 61 (mod 90)
  ```

*Mathematica:*
```mathematica
  ChineseRemainder[{1, 1, 7}, {2, 5, 9}]  (* 61 *)
  LCM[2, 5, 9]  (* 90 *)
  ```

*Verify:* $61 mod 2 = 1$ ✓, $61 mod 5 = 1$ ✓, $61 mod 9 = 7$ ✓

*Answer:* ${61 + 90k | k in ZZ}$ (Option 5)
]

== Polynomial GCD (2025 Q5)

#example(title: [2025 Q5: GCD of $x^3 - 1$ and $x^3 + 2x^2 + 2x + 1$])[
*SymPy:*
```python
  from sympy import Symbol, gcd, factor
  x = Symbol('x')
  p1 = x**3 - 1
  p2 = x**3 + 2*x**2 + 2*x + 1
  print(factor(p1))  # (x - 1)*(x**2 + x + 1)
  print(factor(p2))  # (x + 1)*(x**2 + x + 1)
  print(gcd(p1, p2))  # x**2 + x + 1
  ```

*Mathematica:*
```mathematica
  Factor[x^3 - 1]              (* (x-1)(x^2+x+1) *)
  Factor[x^3 + 2x^2 + 2x + 1]  (* (x+1)(x^2+x+1) *)
  PolynomialGCD[x^3 - 1, x^3 + 2x^2 + 2x + 1]  (* x^2 + x + 1 *)
  ```

*Answer:* $x^2 + x + 1$ (Option 4)
]

== Induction Proof Structure (2025 Q6)

#rect(inset: 8pt, fill: yellow.lighten(85%), width: 100%)[
  *Standard Induction Proof Order:*
  1. *Base case* (usually $n = 0$ for statements about $NN$)
  2. *Induction hypothesis*: Assume $P(n)$ holds for SOME $n$
  3. *Induction step*: Prove $P(n+1)$ using the hypothesis
  4. *Conclusion*: Invoke principle of mathematical induction
]

#example(title: [2025 Q6: Prove $f(n) = (n+1)! - 1$])[
  *Statement:* $f(n) = sum_(k=0)^n k dot k! = (n+1)! - 1$

  *Correct fragment order:*
  1. *F* - Base case $n=0$: $f(0) = 0$ and $(0+1)! - 1 = 0$ ✓
  2. *B* - Assume $f(n) = (n+1)! - 1$ for SOME $n$ (not all!)
  3. *H* - Prove $f(n+1)$ by adding $(n+1)(n+1)!$ to $f(n)$
  4. *D* - Conclusion: statement follows by induction

  *Common mistakes:*
  - Using $n=1$ as base when $n=0$ is in domain
  - Assuming formula for ALL $n$ (circular reasoning)
  - Working backwards instead of forwards

  *Answer:* F, B, H, D
]

== Recursive Sequence (2025 Q7)

#example(title: [2025 Q7: Compute $a_n$])[
*Recurrence:*
$ a_0 = 2, quad a_1 = 3 $
$ a_n = cases(a_(n-1) + n & "if" n "even", a_(n-1) + 2a_(n-2) & "if" n "odd") $

*SymPy:*
```python
  a = [0] * 10
  a[0], a[1] = 2, 3
  for n in range(2, 10):
      if n % 2 == 0:
          a[n] = a[n-1] + n
      else:
          a[n] = a[n-1] + 2*a[n-2]
  print(a)  # [2, 3, 5, 11, 15, 37, 43, 117, ...]
  # a_5 = 37
  ```

*Answer:* 37 (Option 1)
]

== Bipartite Graph Degree Sequences (2025 Q8)

#rect(
  inset: 8pt,
  fill: red.lighten(85%),
  width: 100%,
)[
  *CRITICAL:* In a bipartite graph, the sum of degrees on BOTH sides must be EQUAL (both equal the number of edges).
]

#example(title: [2025 Q8: Bipartite graph existence])[
*Part a:* $V_1 = [4,4,4,4]$, $V_2 = [5,5,5,5,5]$
- Sum of $V_1$: $16$, Sum of $V_2$: $25$
- $16 != 25$ → *Graph does NOT exist*
- *Answer:* None of these (Option 5)

*Part b:* $V_1 = [1,2,2,2]$, $V_2 = [1,2,2,2,2]$
- Sum of $V_1$: $7$, Sum of $V_2$: $9$
- $7 != 9$ → *Graph does NOT exist*
- *Answer:* None of these (Option 5)

*Part c:* $V_1 = [5,5,5,5]$, $V_2 = [4,4,4,4,4]$
- Sum of $V_1$: $20$, Sum of $V_2$: $20$ ✓
- Max degree in $V_1$ is 5 = $|V_2|$: each must connect to all of $V_2$
- Max degree in $V_2$ is 4 = $|V_1|$: each connects to all of $V_1$
- *This works!* Graph exists without multiple edges.
- *Answer:* Option 1

*SymPy:*
```python
  V1 = [5,5,5,5]
  V2 = [4,4,4,4,4]
  print(f"Sum V1: {sum(V1)}, Sum V2: {sum(V2)}")
  print(f"Equal: {sum(V1) == sum(V2)}")  # True
  ```
]

== Vandermonde's Identity (2025 Q9)

#rect(inset: 8pt, fill: yellow.lighten(85%), width: 100%)[
  *Vandermonde:* $binom(m+n, r) = sum_(k=0)^r binom(m, r-k) binom(n, k)$

  *Non-zero terms:* $max(0, r-m) <= k <= min(r, n)$
]

#example(title: [2025 Q9: Lower bound of summation])[
  *Given:* $0 < m < r < n$

  For $binom(m, r-k)$ to be non-zero: $0 <= r-k <= m$, i.e., $r-m <= k <= r$

  For $binom(n, k)$ to be non-zero: $0 <= k <= n$

  Combined: $max(0, r-m) <= k <= min(r, n)$

  Since $r > m > 0$, we have $r - m > 0$, so lower bound is $r - m$.

  *Answer:* $a = r - m$ (Option 6)
]

== Set Operations (2025 Q10)

#example(title: [2025 Q10: $((A sect B) backslash C) union ((B sect C) backslash A) union ((C sect A) backslash B)$])[
*Given:* $A = {0,1,2,4}$, $B = {0,1,3,5}$, $C = {0,2,3,6}$

*SymPy:*
```python
  A = {0,1,2,4}
  B = {0,1,3,5}
  C = {0,2,3,6}
  result = ((A & B) - C) | ((B & C) - A) | ((C & A) - B)
  print(result)  # {1, 2, 3}
  ```

*Step by step:*
- $A sect B = {0, 1}$
- $B sect C = {0, 3}$
- $C sect A = {0, 2}$
- $(A sect B) backslash C = {1}$
- $(B sect C) backslash A = {3}$
- $(C sect A) backslash B = {2}$
- Union: ${1, 2, 3}$

*Answer:* ${1, 2, 3}$ (Option 7)
]

== Predicate Logic Translation (2025 Q11)

#rect(inset: 8pt, fill: red.lighten(85%), width: 100%)[
  *Key:* Mathematical statements CAN be translated to predicate logic. Don't give up!
]

#example(
  title: [2025 Q11: "Every positive rational has coprime representation"],
)[
  *Statement:* For every positive rational $x$, there exist positive integers $a, b$ such that $x = a/b$ and $gcd(a, b) = 1$.

  *Translation:* $forall x in QQ^+ exists a in ZZ^+ exists b in ZZ^+ (x = a/b and G(a,b))$

  This is exactly Option 2!

  *Answer:* Option 2
]

== Set Algebra (2025 Q12)

#example(title: [2025 Q12: $A sect overline((B backslash C))$])[
  *Simplify:*
  $ A sect overline((B backslash C)) &= A sect overline((B sect overline(C))) \
                                   &= A sect (overline(B) union C) quad "(De Morgan)" \
                                   &= (A sect overline(B)) union (A sect C) quad "(Distributive)" $

  *Answer:* $(A sect overline(B)) union (A sect C)$ (Option 4)

  *NOT* $A sect (C backslash B)$ which equals $A sect C sect overline(B)$
]

== Tautologies (2025 Q14)

#example(title: [2025 Q14: Which is a tautology?])[
*SymPy:*
```python
  from itertools import product

  def check(f):
      return all(f(p,q,r) for p,q,r in product([True,False], repeat=3))

  # Option 1: (p→q) ∨ (¬q→¬p)
  opt1 = lambda p,q,r: ((not p) or q) or (q or (not p))
  print(f"Option 1: {check(opt1)}")  # False!

  # Option 5: (¬p∨¬q) → ¬(p∧q)
  opt5 = lambda p,q,r: (not ((not p) or (not q))) or (not (p and q))
  print(f"Option 5: {check(opt5)}")  # True!
  ```

*Analysis:*
- Option 1: $(p -> q) or (not q -> not p)$ — NOT a tautology! When $p=T, q=F$: $(F) or (T -> F) = F or F = F$
- Option 5: $(not p or not q) -> not(p and q)$ — This is $(not(p and q)) -> (not(p and q))$, always true!

*Answer:* Option 5: $(not p or not q) -> not(p and q)$
]

== Circular Permutations (2025 Q15)

#rect(inset: 8pt, fill: yellow.lighten(85%), width: 100%)[
  *Circular arrangements of $n$ people:*
  - Oriented (left/right matters): $(n-1)!$
  - Unoriented (only neighbors matter): $(n-1)!/2$
]

#example(title: [2025 Q15: Two tables with n and 2n seats])[
*Setup:* $3n$ people, tables with $n$ and $2n$ seats.

*Part a: Same left AND right neighbors*
- Choose $n$ for small table: $binom(3n, n)$
- Arrange at small table (oriented): $(n-1)!$
- Arrange at large table (oriented): $(2n-1)!$
- Total: $binom(3n, n) (n-1)! (2n-1)! = (3n)!/(2n^2)$
- *Answer:* $(3n)!/(2n^2)$ (Option 5)

*Part b: Same neighbors (don't care left/right)*
- Divide by 2 for each table (orientation)
- Total: $(3n)!/(2n^2) times 1/2 times 1/2 = (3n)!/(4n^2)$
- *Answer:* $(3n)!/(4n^2)$ (Option 6)

*SymPy verification with n=2:*
```python
  from math import factorial, comb
  n = 2
  part_a = comb(6, 2) * factorial(1) * factorial(3)  # 15*1*6 = 90
  formula_a = factorial(6) // (2 * n**2)  # 720/8 = 90 ✓
  ```
]

== Function Properties (2025 Q16)

#rect(inset: 8pt, fill: red.lighten(85%), width: 100%)[
  *Check list:*
  1. *Well-defined:* Every input maps to exactly one output IN THE CODOMAIN
  2. *Injective:* Different inputs → different outputs
  3. *Surjective:* Every codomain element is hit
]

#example(title: [2025 Q16: Function property analysis])[
  *f: ℝ → ℤ, f(x) = 2⌊x/2⌋*
  - Well-defined? Yes! Always produces an even integer.
  - Injective? No: $f(0) = f(1) = 0$
  - Surjective? No: odd integers never produced
  - *Answer:* Neither injective nor surjective (Option 2)

  *f: ℝ → {x ≥ 0}, f(x) = √(x²) = |x|*
  - Well-defined? Yes
  - Injective? No: $f(1) = f(-1) = 1$
  - Surjective? Yes! For any $y >= 0$, $f(y) = y$
  - *Answer:* Surjective (Option 3)

  *f: ℕ → ℕ, f(x) = 2x + 7*
  - Well-defined? Yes: $2x + 7 >= 7 > 0$ for $x >= 0$
  - Injective? Yes
  - Surjective? No: 0,1,2,3,4,5,6 never hit
  - *Answer:* Injective (Option 4)

  *f: ℕ → ℕ, f(x) = x - x²*
  - Well-defined? $f(2) = 2 - 4 = -2 in.not NN$
  - *Answer:* Not well-defined (Option 1)

  *f: ℝ → ℝ, f(x) = x if x ∈ ℚ, -x if x ∉ ℚ*
  - Injective? Yes (proof by cases)
  - Surjective? Yes: $f(y) = y$ for rational $y$; $f(-y) = y$ for irrational $y$
  - *Answer:* Both injective AND surjective (Option 5)
]

== Permutations with Forbidden Patterns (2025 Q17)

#example(title: [2025 Q17: Permutations of ABCDE])[
*SymPy (brute force):*
```python
  from itertools import permutations

  def has(p, sub):
      return sub in ''.join(p)

  perms = list(permutations('ABCDE'))

  # Q17a: None of AB, BC, CD
  count_a = sum(1 for p in perms if not (has(p,'AB') or has(p,'BC') or has(p,'CD')))
  print(f"Without AB,BC,CD: {count_a}")  # 64

  # Q17b: Contains ACE as substring
  count_b = sum(1 for p in perms if has(p, 'ACE'))
  print(f"With ACE: {count_b}")  # 6

  # Q17c: Exactly one of AB, CD
  count_c = sum(1 for p in perms if has(p,'AB') != has(p,'CD'))
  print(f"Exactly one of AB,CD: {count_c}")  # 36
  ```

*Answers:* (a) 64, (b) 6, (c) 36
]

== Relation Properties (2025 Q18)

#rect(inset: 8pt, fill: yellow.lighten(85%), width: 100%)[
  *Definitions on set S:*
  - *Reflexive:* $(a,a) in R$ for all $a in S$
  - *Symmetric:* $(a,b) in R => (b,a) in R$
  - *Antisymmetric:* $(a,b) in R and (b,a) in R => a = b$
  - *Transitive:* $(a,b) in R and (b,c) in R => (a,c) in R$
  - *Equivalence:* Reflexive + Symmetric + Transitive
  - *Partial Order:* Reflexive + Antisymmetric + Transitive
  - *Total Order:* Partial order where any two elements are comparable
  - *Well-Order:* Total order where every non-empty subset has minimum
  - *Hasse Diagram Edges:* Covering relations of a partial order (not the full order!)
]

#example(title: [2025 Q18: Classify relations on {a,b,c,d}])[
  *R₁ = {(a,a),(a,b),(a,c),(a,d)}*
  - Not reflexive (missing (b,b), (c,c), (d,d))
  - *Answer:* None of these (Option 5)

  *R₂ = {(a,b),(b,c),(c,d)}*
  - Not reflexive, but these ARE the covering relations
  - If we add reflexive closure and transitive closure, we get $a < b < c < d$
  - *Answer:* Hasse diagram edges (Option 1)

  *R₃ = {(a,a),(b,b),(c,c),(d,d),(a,d),(d,a)}*
  - Reflexive ✓, Symmetric ✓, Transitive ✓
  - *Answer:* Equivalence relation (Option 7)

  *R₄ = {(a,a),(b,b),(c,c),(d,d),(d,c)}*
  - Reflexive ✓, Antisymmetric ✓, Transitive ✓
  - But NOT total: $a$ and $b$ are incomparable
  - *Answer:* Partial order (Option 2)

  *R₅ = {(a,a),...,(d,d),(a,b),(a,c),(a,d),(b,c),(b,d),(c,d)}*
  - This is $<=$ on $a < b < c < d$
  - Partial order ✓, Total ✓, Well-ordered ✓
  - *Answer:* Well-order (Option 4)
]

== Polynomial Coefficients (2025 Q20) — CRITICAL!

#rect(inset: 12pt, fill: red.lighten(85%), width: 100%)[
*COMMON WOLFRAM MISTAKE:*
```mathematica
  (* WRONG - this expands the monomial, not the polynomial! *)
  Coefficient[Expand[x^15 y^20], (2x^3 - y^4)^10]

  (* CORRECT - expand the polynomial, find coefficient of monomial *)
  Coefficient[Expand[(2x^3 - y^4)^10], x^15 y^20]
  ```
]

#example(title: [2025 Q20: Coefficient of $x^15 y^20$])[
*General approach:* $(a x^m + b y^n)^N$ has term $binom(N, k) a^(N-k) b^k x^(m(N-k)) y^(n k)$

*$(2x^3 - y^4)^10$:*
- Term: $binom(10, k) (2x^3)^(10-k) (-y^4)^k = binom(10, k) 2^(10-k) (-1)^k x^(3(10-k)) y^(4k)$
- For $x^15$: $3(10-k) = 15 => k = 5$
- For $y^20$: $4k = 20 => k = 5$ ✓
- Coefficient: $binom(10, 5) dot 2^5 dot (-1)^5 = 252 dot 32 dot (-1) = -8064$
- $= -binom(10, 5) dot 2^5$

*SymPy:*
```python
  from sympy import symbols, expand, Poly
  x, y = symbols('x y')

  # Method 1: expand and extract
  p1 = expand((2*x**3 - y**4)**10)
  coef1 = Poly(p1, x, y).coeff_monomial(x**15 * y**20)
  print(coef1)  # -8064

  # Method 2: direct coefficient
  from sympy import binomial
  k = 5  # solved from exponent equations
  coef = binomial(10, k) * 2**(10-k) * (-1)**k
  print(coef)  # -8064
  ```

*Mathematica (CORRECT SYNTAX):*
```mathematica
  (* For (2x^3 - y^4)^10 *)
  Coefficient[Expand[(2x^3 - y^4)^10], x^15 y^20]   (* -8064 *)

  (* For (1 - 2x^3 y^4)^10 *)
  Coefficient[Expand[(1 - 2x^3 y^4)^10], x^15 y^20] (* -8064 *)

  (* For (x^3 - 2y^4)^10 *)
  Coefficient[Expand[(x^3 - 2y^4)^10], x^15 y^20]   (* -8064 *)

  (* All three equal -Binomial[10,5] * 2^5 = -8064 *)
  -Binomial[10, 5] * 2^5  (* -8064 ✓ *)
  ```

*Answer for all three:* $-binom(10, 5) dot 2^5$ (Option 1)
]

== Logical Equivalence (2025 Q21)

#example(title: [2025 Q21: "$a$ and $b$ are relatively prime"])[
  *Statement:* $gcd(a, b) = 1$, i.e., no common divisor $> 1$

  *Three equivalent formulations:*
  1. $forall c ((c | a and c | b) -> c <= 1)$ — Option 5
  2. $not(exists c (c | a and c | b and c > 1))$ — Option 2
  3. $forall c (not(c | a) or not(c | b) or c <= 1)$ — Option 3

  These are ALL equivalent by De Morgan's laws and logical transformations!

  *Answer:* All three are equivalent (Option 4)
]

#pagebreak()

= Wolfram Mathematica Complete Reference

#rect(inset: 8pt, fill: orange.lighten(85%), width: 100%)[
  *Copy-paste ready code for your exam!* Open Mathematica and use these.
]

== Number Theory Commands

```mathematica
(* === GCD, LCM, and Bézout === *)
GCD[48, 18]                          (* 6 *)
LCM[12, 18]                          (* 36 *)
ExtendedGCD[48, 18]                  (* {6, {-1, 3}} means 6 = 48*(-1) + 18*3 *)

(* === Modular Arithmetic === *)
Mod[17, 5]                           (* 2 *)
PowerMod[3, 100, 7]                  (* 3^100 mod 7 *)
PowerMod[5, -1, 17]                  (* Modular inverse: 5^(-1) mod 17 = 7 *)

(* === Chinese Remainder Theorem === *)
ChineseRemainder[{1, 4, 3}, {2, 5, 7}]   (* 59 *)

(* === Primality === *)
PrimeQ[97]                           (* True *)
FactorInteger[5292]                  (* {{2, 2}, {3, 3}, {7, 2}} *)
Divisors[28]                         (* {1, 2, 4, 7, 14, 28} *)
Prime[100]                           (* 541 - the 100th prime *)
PrimePi[100]                         (* 25 - count of primes ≤ 100 *)

(* === Euler's Totient === *)
EulerPhi[12]                         (* 4 *)
```

== Combinatorics Commands

```mathematica
(* === Basic Counting === *)
Binomial[10, 3]                      (* 120 *)
10!                                  (* 3628800 *)
Multinomial[3, 2, 2]                 (* 7!/(3!2!2!) = 210 *)

(* === Derangements === *)
Subfactorial[5]                      (* 44 *)
Subfactorial[7]                      (* 1854 *)

(* === Stirling Numbers === *)
StirlingS2[5, 3]                     (* Partitions of 5 into 3 non-empty subsets *)

(* === Permutations and Combinations === *)
Permutations[{a, b, c}]              (* All 6 permutations *)
Subsets[{1, 2, 3, 4}, {2}]           (* All 2-element subsets *)
```

== Polynomial Operations

#rect(inset: 8pt, fill: red.lighten(85%), width: 100%)[
*⚠️ CRITICAL: Coefficient Syntax*

*WRONG:* `Coefficient[Expand[x^15 y^20], (2x^3 - y^4)^10]`
- This expands `x^15 y^20` (which is just itself) and finds nothing!

*CORRECT:* `Coefficient[Expand[(2x^3 - y^4)^10], x^15 y^20]`
- First argument: the POLYNOMIAL you're expanding
- Second argument: the MONOMIAL whose coefficient you want
]

```mathematica
(* === Expansion === *)
Expand[(2x^2 - 3y^3)^8]

(* === Extract Coefficient - CORRECT SYNTAX === *)
(* Coefficient[POLYNOMIAL, MONOMIAL] *)
Coefficient[Expand[(2x^2 - 3y^3)^8], x^8 y^12]   (* 90720 *)
Coefficient[(2x^3 - y^4)^10, x^15 y^20]          (* -8064 — works without Expand too! *)

(* === Multiple examples from 2025 exam === *)
Coefficient[Expand[(2x^3 - y^4)^10], x^15 y^20]     (* -8064 = -Binomial[10,5]*2^5 *)
Coefficient[Expand[(1 - 2x^3 y^4)^10], x^15 y^20]   (* -8064 *)
Coefficient[Expand[(x^3 - 2y^4)^10], x^15 y^20]     (* -8064 *)

(* === Polynomial Division === *)
PolynomialQuotientRemainder[x^4 + 3x^3 + 5x/2 + 6, x + 2, x]

(* === Divisibility Check === *)
PolynomialRemainder[x^5 + 1, x + 1, x]   (* 0 means divisible *)

(* === Polynomial GCD === *)
PolynomialGCD[x^3 - 1, x^3 + 2x^2 + 2x + 1]  (* x^2 + x + 1 *)
Factor[x^3 - 1]                               (* (x-1)(x^2+x+1) *)
```

== Graph Theory Calculations

#rect(inset: 8pt, fill: red.lighten(85%), width: 100%)[
  *⚠️ BIPARTITE GRAPH CHECK:* In a bipartite graph with parts $V_1$ and $V_2$:
  - Sum of degrees in $V_1$ MUST equal sum of degrees in $V_2$
  - Both sums equal the number of edges
  - If sums don't match, the graph CANNOT exist!
]

```mathematica
(* === Hypercube Q_n === *)
hypercubeVertices[n_] := 2^n
hypercubeEdges[n_] := n * 2^(n-1)

(* === Complete Graph K_n === *)
completeEdges[n_] := n(n-1)/2

(* === Verify Degree Sequence === *)
degreeSequence = {2, 2, 3, 3, 3, 3, 3};
Total[degreeSequence]                (* 19 - odd, so invalid! *)
EvenQ[Total[degreeSequence]]         (* False *)

(* === Bipartite Graph Degree Check (2025 Exam!) === *)
V1 = {4, 4, 4, 4};
V2 = {5, 5, 5, 5, 5};
Total[V1]                            (* 16 *)
Total[V2]                            (* 25 *)
Total[V1] == Total[V2]               (* False - graph CANNOT exist! *)

(* Example that DOES work *)
V1good = {5, 5, 5, 5};
V2good = {4, 4, 4, 4, 4};
Total[V1good] == Total[V2good]       (* True - 20 = 20, may exist *)
```

== Inclusion-Exclusion Templates

```mathematica
(* === 2 Sets === *)
ie2[a_, b_, ab_] := a + b - ab

(* === 3 Sets === *)
ie3[a_, b_, c_, ab_, ac_, bc_, abc_] := a + b + c - ab - ac - bc + abc

(* === 4 Sets (symmetric case) === *)
ie4[single_, pair_, triple_, quad_] := 4*single - 6*pair + 4*triple - quad
ie4[200, 50, 25, 5]                  (* 595 *)
```

== Relation Property Checker

```mathematica
(* Define a relation as list of pairs *)
R = {{1,2}, {2,3}, {1,3}, {4,5}, {5,6}, {4,6}};
S = {1, 2, 3, 4, 5, 6};

(* Reflexive: all (x,x) present? *)
reflexiveQ[set_, rel_] := AllTrue[set, MemberQ[rel, {#, #}] &]
reflexiveQ[S, R]                     (* False *)

(* Symmetric: (x,y) ∈ R ⟹ (y,x) ∈ R? *)
symmetricQ[rel_] := AllTrue[rel, MemberQ[rel, Reverse[#]] &]
symmetricQ[R]                        (* False *)

(* Antisymmetric: (x,y) ∈ R ∧ (y,x) ∈ R ⟹ x = y? *)
antisymmetricQ[rel_] := !AnyTrue[rel, (#[[1]] != #[[2]] && MemberQ[rel, Reverse[#]]) &]
antisymmetricQ[R]                    (* True *)

(* Transitive: (x,y) ∈ R ∧ (y,z) ∈ R ⟹ (x,z) ∈ R? *)
transitiveQ[rel_] := AllTrue[
  Tuples[rel, 2],
  (#[[1, 2]] != #[[2, 1]] || MemberQ[rel, {#[[1, 1]], #[[2, 2]]}]) &
]
```

== Quick Verification Templates

```mathematica
(* === Verify CRT Solution === *)
x = 59; moduli = {2, 5, 7}; remainders = {1, 4, 3};
Table[Mod[x, moduli[[i]]] == remainders[[i]], {i, 3}]
(* {True, True, True} *)

(* === Check if d can be gcd(a,b) given ab = N === *)
canBeGCD[d_, N_] := Divisible[N, d^2]
canBeGCD[36, 5292]                   (* False *)
canBeGCD[42, 5292]                   (* True *)

(* === Function injectivity check on finite domain === *)
f[x_] := Floor[Log2[x]]
domain = Range[1, 8];
image = f /@ domain;
Length[image] == Length[DeleteDuplicates[image]]  (* False - not injective *)
```

#rect(inset: 12pt, fill: blue.lighten(90%), width: 100%)[
  *Good luck on your exam!* Remember:
  - Always attempt every question (no negative points)
  - Use these tools to verify your work
  - When stuck, try small examples first
  - Check your arithmetic with CAS tools
]

// Relation properties:
// #show-relation-properties(S, R, name: "R")

// Direct calculations using built-ins:
// $ gcd(a, b) = #calc.gcd(a, b) $
// $ binom(n, k) = #calc.binom(n, k) $
// $ n! = #calc.fact(n) $

// Manual Euclidean Algorithm workspace:
// $
//   a &= b dot q_1 + r_1 \
//   b &= r_1 dot q_2 + r_2 \
//   & dots.v
// $
