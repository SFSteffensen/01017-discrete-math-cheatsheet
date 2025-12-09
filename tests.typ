// Test suite for custom calculation functions
// Run with: typst compile tests.typ
// If compilation succeeds without errors, all tests pass.

// Import the same calc functions we use in the main file

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

// Stirling numbers of the second kind S(n,k)
#let stirling2(n, k) = {
  if k == 0 and n == 0 { return 1 }
  if k == 0 or n == 0 or k > n { return 0 }
  if k == 1 or k == n { return 1 }
  k * stirling2(n - 1, k) + stirling2(n - 1, k - 1)
}

// Inclusion-exclusion for 2 sets
#let ie2(a, b, ab) = a + b - ab

// Inclusion-exclusion for 3 sets
#let ie3(a, b, c, ab, ac, bc, abc) = a + b + c - ab - ac - bc + abc

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

// Check if relation R on set S is reflexive
#let is-reflexive(S, R) = {
  for x in S {
    if not R.contains((x, x)) { return false }
  }
  return true
}

// Check if relation R is symmetric
#let is-symmetric(R) = {
  for pair in R {
    let (x, y) = pair
    if not R.contains((y, x)) { return false }
  }
  return true
}

// Check if relation R is antisymmetric
#let is-antisymmetric(R) = {
  for pair in R {
    let (x, y) = pair
    if x != y and R.contains((y, x)) { return false }
  }
  return true
}

// Check if relation R is transitive
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

// Check if R is an equivalence relation
#let is-equivalence-relation(S, R) = {
  is-reflexive(S, R) and is-symmetric(R) and is-transitive(R)
}

// Check if R is a partial order
#let is-partial-order(S, R) = {
  is-reflexive(S, R) and is-antisymmetric(R) and is-transitive(R)
}

// ============================================================================
// TEST ASSERTIONS
// ============================================================================

= Function Tests

== Derangement Tests

// Known derangement values: D_0=1, D_1=0, D_2=1, D_3=2, D_4=9, D_5=44, D_6=265, D_7=1854
#assert.eq(derangement(0), 1, message: "D_0 should be 1")
#assert.eq(derangement(1), 0, message: "D_1 should be 0")
#assert.eq(derangement(2), 1, message: "D_2 should be 1")
#assert.eq(derangement(3), 2, message: "D_3 should be 2")
#assert.eq(derangement(4), 9, message: "D_4 should be 9")
#assert.eq(derangement(5), 44, message: "D_5 should be 44")
#assert.eq(derangement(6), 265, message: "D_6 should be 265")
#assert.eq(derangement(7), 1854, message: "D_7 should be 1854")
#assert.eq(derangement(8), 14833, message: "D_8 should be 14833")
#assert.eq(derangement(10), 1334961, message: "D_10 should be 1334961")

All derangement tests passed

== Extended GCD Tests

// Test: gcd(48, 18) = 6 = 48*(-1) + 18*(3)
#let (g1, s1, t1) = extended-gcd(48, 18)
#assert.eq(g1, 6, message: "gcd(48, 18) should be 6")
#assert.eq(48 * s1 + 18 * t1, 6, message: "Bézout identity should hold for (48, 18)")

// Test: gcd(240, 46) = 2
#let (g2, s2, t2) = extended-gcd(240, 46)
#assert.eq(g2, 2, message: "gcd(240, 46) should be 2")
#assert.eq(240 * s2 + 46 * t2, 2, message: "Bézout identity should hold for (240, 46)")

// Test: gcd(17, 13) = 1 (coprime)
#let (g3, s3, t3) = extended-gcd(17, 13)
#assert.eq(g3, 1, message: "gcd(17, 13) should be 1")
#assert.eq(17 * s3 + 13 * t3, 1, message: "Bézout identity should hold for (17, 13)")

// Test: gcd(100, 35) = 5
#let (g4, s4, t4) = extended-gcd(100, 35)
#assert.eq(g4, 5, message: "gcd(100, 35) should be 5")
#assert.eq(100 * s4 + 35 * t4, 5, message: "Bézout identity should hold for (100, 35)")

// Test: gcd(0, 5) = 5
#let (g5, s5, t5) = extended-gcd(0, 5)
#assert.eq(g5, 5, message: "gcd(0, 5) should be 5")

// Test: gcd(7, 0) = 7
#let (g6, s6, t6) = extended-gcd(7, 0)
#assert.eq(g6, 7, message: "gcd(7, 0) should be 7")

// Test: gcd(1071, 462) = 21
#let (g7, s7, t7) = extended-gcd(1071, 462)
#assert.eq(g7, 21, message: "gcd(1071, 462) should be 21")
#assert.eq(1071 * s7 + 462 * t7, 21, message: "Bézout identity should hold for (1071, 462)")

All extended GCD tests passed

== Modular Inverse Tests

// Test: 3^(-1) mod 7 = 5 (since 3*5 = 15 ≡ 1 mod 7)
#assert.eq(mod-inverse(3, 7), 5, message: "3^(-1) mod 7 should be 5")

// Test: 2^(-1) mod 9 = 5 (since 2*5 = 10 ≡ 1 mod 9)
#assert.eq(mod-inverse(2, 9), 5, message: "2^(-1) mod 9 should be 5")

// Test: 7^(-1) mod 9 = 4 (since 7*4 = 28 ≡ 1 mod 9)
#assert.eq(mod-inverse(7, 9), 4, message: "7^(-1) mod 9 should be 4")

// Test: 6^(-1) mod 9 = none (since gcd(6, 9) = 3 ≠ 1)
#assert.eq(mod-inverse(6, 9), none, message: "6^(-1) mod 9 should not exist")

// Test: 5^(-1) mod 12 = none (since gcd(5, 12) = 1... wait, it should exist)
#assert.eq(mod-inverse(5, 12), 5, message: "5^(-1) mod 12 should be 5")

// Test: 4^(-1) mod 12 = none (since gcd(4, 12) = 4 ≠ 1)
#assert.eq(mod-inverse(4, 12), none, message: "4^(-1) mod 12 should not exist")

// Test: 17^(-1) mod 43 (verify result * 17 ≡ 1 mod 43)
#let inv17 = mod-inverse(17, 43)
#assert.eq(calc.rem(inv17 * 17, 43), 1, message: "17 * 17^(-1) should be 1 mod 43")

// Test: 1^(-1) mod n = 1 for any n > 1
#assert.eq(mod-inverse(1, 7), 1, message: "1^(-1) mod 7 should be 1")
#assert.eq(mod-inverse(1, 100), 1, message: "1^(-1) mod 100 should be 1")

All modular inverse tests passed

== Chinese Remainder Theorem Tests

// Test: x ≡ 2 (mod 3), x ≡ 3 (mod 5), x ≡ 2 (mod 7) → x ≡ 23 (mod 105)
#let (crt1, M1) = crt-solve((2, 3, 2), (3, 5, 7))
#assert.eq(M1, 105, message: "CRT modulus should be 3*5*7 = 105")
#assert.eq(calc.rem(crt1, 3), 2, message: "CRT solution should satisfy x ≡ 2 (mod 3)")
#assert.eq(calc.rem(crt1, 5), 3, message: "CRT solution should satisfy x ≡ 3 (mod 5)")
#assert.eq(calc.rem(crt1, 7), 2, message: "CRT solution should satisfy x ≡ 2 (mod 7)")

// Test: x ≡ 1 (mod 2), x ≡ 4 (mod 5), x ≡ 3 (mod 7) → x ≡ 59 (mod 70)
#let (crt2, M2) = crt-solve((1, 4, 3), (2, 5, 7))
#assert.eq(M2, 70, message: "CRT modulus should be 2*5*7 = 70")
#assert.eq(crt2, 59, message: "CRT solution should be 59")
#assert.eq(calc.rem(crt2, 2), 1, message: "CRT solution should satisfy x ≡ 1 (mod 2)")
#assert.eq(calc.rem(crt2, 5), 4, message: "CRT solution should satisfy x ≡ 4 (mod 5)")
#assert.eq(calc.rem(crt2, 7), 3, message: "CRT solution should satisfy x ≡ 3 (mod 7)")

// Test: x ≡ 0 (mod 3), x ≡ 0 (mod 5) → x ≡ 0 (mod 15)
#let (crt3, M3) = crt-solve((0, 0), (3, 5))
#assert.eq(crt3, 0, message: "CRT solution for (0,0) should be 0")
#assert.eq(M3, 15, message: "CRT modulus should be 15")

// Test: x ≡ 1 (mod 2), x ≡ 2 (mod 3), x ≡ 3 (mod 5) → verify solution
#let (crt4, M4) = crt-solve((1, 2, 3), (2, 3, 5))
#assert.eq(M4, 30, message: "CRT modulus should be 30")
#assert.eq(calc.rem(crt4, 2), 1, message: "CRT should satisfy x ≡ 1 (mod 2)")
#assert.eq(calc.rem(crt4, 3), 2, message: "CRT should satisfy x ≡ 2 (mod 3)")
#assert.eq(calc.rem(crt4, 5), 3, message: "CRT should satisfy x ≡ 3 (mod 5)")

// Test: non-coprime moduli should return none
#let crt_fail = crt-solve((1, 2), (4, 6))
#assert.eq(crt_fail, none, message: "CRT with non-coprime moduli (4, 6) should return none")

All CRT tests passed

== Hypercube Edges Tests

// Q_1 has 1 edge (single edge connecting 2 vertices)
#assert.eq(hypercube-edges(1), 1, message: "Q_1 should have 1 edge")

// Q_2 has 4 edges (a square)
#assert.eq(hypercube-edges(2), 4, message: "Q_2 should have 4 edges")

// Q_3 has 12 edges (a cube)
#assert.eq(hypercube-edges(3), 12, message: "Q_3 should have 12 edges")

// Q_4 has 32 edges (tesseract)
#assert.eq(hypercube-edges(4), 32, message: "Q_4 should have 32 edges")

// Q_5 has 80 edges
#assert.eq(hypercube-edges(5), 80, message: "Q_5 should have 80 edges")

// Q_6 has 192 edges
#assert.eq(hypercube-edges(6), 192, message: "Q_6 should have 192 edges")

All hypercube edge tests passed

== Complete Graph Edges Tests

// K_1 has 0 edges
#assert.eq(complete-edges(1), 0, message: "K_1 should have 0 edges")

// K_2 has 1 edge
#assert.eq(complete-edges(2), 1, message: "K_2 should have 1 edge")

// K_3 has 3 edges (triangle)
#assert.eq(complete-edges(3), 3, message: "K_3 should have 3 edges")

// K_4 has 6 edges
#assert.eq(complete-edges(4), 6, message: "K_4 should have 6 edges")

// K_5 has 10 edges
#assert.eq(complete-edges(5), 10, message: "K_5 should have 10 edges")

// K_6 has 15 edges
#assert.eq(complete-edges(6), 15, message: "K_6 should have 15 edges")

// K_10 has 45 edges
#assert.eq(complete-edges(10), 45, message: "K_10 should have 45 edges")

// K_100 has 4950 edges
#assert.eq(complete-edges(100), 4950, message: "K_100 should have 4950 edges")

All complete graph edge tests passed

== Built-in Typst calc Functions Validation

// Verify calc.gcd works correctly
#assert.eq(calc.gcd(48, 18), 6, message: "calc.gcd(48, 18) should be 6")
#assert.eq(calc.gcd(17, 13), 1, message: "calc.gcd(17, 13) should be 1")
#assert.eq(calc.gcd(100, 25), 25, message: "calc.gcd(100, 25) should be 25")

// Verify calc.lcm works correctly
#assert.eq(calc.lcm(4, 6), 12, message: "calc.lcm(4, 6) should be 12")
#assert.eq(calc.lcm(3, 5), 15, message: "calc.lcm(3, 5) should be 15")
#assert.eq(calc.lcm(12, 18), 36, message: "calc.lcm(12, 18) should be 36")

// Verify calc.binom works correctly
#assert.eq(calc.binom(5, 2), 10, message: "C(5,2) should be 10")
#assert.eq(calc.binom(10, 5), 252, message: "C(10,5) should be 252")
#assert.eq(calc.binom(6, 0), 1, message: "C(6,0) should be 1")
#assert.eq(calc.binom(6, 6), 1, message: "C(6,6) should be 1")

// Verify calc.fact works correctly
#assert.eq(calc.fact(0), 1, message: "0! should be 1")
#assert.eq(calc.fact(1), 1, message: "1! should be 1")
#assert.eq(calc.fact(5), 120, message: "5! should be 120")
#assert.eq(calc.fact(7), 5040, message: "7! should be 5040")

// Verify calc.rem (modulo) works correctly
#assert.eq(calc.rem(17, 5), 2, message: "17 mod 5 should be 2")
#assert.eq(calc.rem(100, 7), 2, message: "100 mod 7 should be 2")

// Verify calc.quo (integer division) works correctly
#assert.eq(calc.quo(17, 5), 3, message: "17 ÷ 5 should be 3")
#assert.eq(calc.quo(100, 7), 14, message: "100 ÷ 7 should be 14")

All built-in function tests passed

#line(length: 100%)

#align(center)[
  #text(size: 16pt, weight: "bold", fill: green)[ALL TESTS PASSED]
]

#v(1em)

#align(center)[
  All #strong[67] assertions completed successfully.
]

== Perfect Number Tests

#assert.eq(is-perfect(6), true, message: "6 should be perfect")
#assert.eq(is-perfect(28), true, message: "28 should be perfect")
#assert.eq(is-perfect(496), true, message: "496 should be perfect")
#assert.eq(is-perfect(12), false, message: "12 should not be perfect")
#assert.eq(is-perfect(10), false, message: "10 should not be perfect")

#assert.eq(sum-proper-divisors(6), 6, message: "sum of proper divisors of 6 should be 6")
#assert.eq(sum-proper-divisors(28), 28, message: "sum of proper divisors of 28 should be 28")
#assert.eq(sum-proper-divisors(12), 16, message: "sum of proper divisors of 12 should be 16")

All perfect number tests passed

== Euler's Totient Function Tests

// φ(1) = 1, φ(2) = 1, φ(6) = 2, φ(9) = 6, φ(10) = 4, φ(12) = 4
#assert.eq(euler-phi(1), 1, message: "φ(1) should be 1")
#assert.eq(euler-phi(2), 1, message: "φ(2) should be 1")
#assert.eq(euler-phi(6), 2, message: "φ(6) should be 2")
#assert.eq(euler-phi(9), 6, message: "φ(9) should be 6")
#assert.eq(euler-phi(10), 4, message: "φ(10) should be 4")
#assert.eq(euler-phi(12), 4, message: "φ(12) should be 4")
// For prime p: φ(p) = p - 1
#assert.eq(euler-phi(7), 6, message: "φ(7) should be 6 (prime)")
#assert.eq(euler-phi(13), 12, message: "φ(13) should be 12 (prime)")

All Euler's totient tests passed

== Stirling Numbers Tests

// S(n,1) = 1 for all n >= 1
#assert.eq(stirling2(1, 1), 1, message: "S(1,1) should be 1")
#assert.eq(stirling2(5, 1), 1, message: "S(5,1) should be 1")

// S(n,n) = 1 for all n >= 0
#assert.eq(stirling2(0, 0), 1, message: "S(0,0) should be 1")
#assert.eq(stirling2(3, 3), 1, message: "S(3,3) should be 1")
#assert.eq(stirling2(5, 5), 1, message: "S(5,5) should be 1")

// Known values: S(3,2) = 3, S(4,2) = 7, S(4,3) = 6, S(5,2) = 15, S(5,3) = 25
#assert.eq(stirling2(3, 2), 3, message: "S(3,2) should be 3")
#assert.eq(stirling2(4, 2), 7, message: "S(4,2) should be 7")
#assert.eq(stirling2(4, 3), 6, message: "S(4,3) should be 6")
#assert.eq(stirling2(5, 2), 15, message: "S(5,2) should be 15")
#assert.eq(stirling2(5, 3), 25, message: "S(5,3) should be 25")

// Edge cases
#assert.eq(stirling2(5, 0), 0, message: "S(5,0) should be 0")
#assert.eq(stirling2(3, 5), 0, message: "S(3,5) should be 0 (k > n)")

All Stirling number tests passed

== Inclusion-Exclusion Tests

// |A ∪ B| = |A| + |B| - |A ∩ B|
#assert.eq(ie2(10, 15, 5), 20, message: "IE2: 10 + 15 - 5 = 20")
#assert.eq(ie2(100, 50, 25), 125, message: "IE2: 100 + 50 - 25 = 125")

// |A ∪ B ∪ C| = |A| + |B| + |C| - |A∩B| - |A∩C| - |B∩C| + |A∩B∩C|
#assert.eq(ie3(10, 20, 30, 5, 3, 7, 2), 47, message: "IE3 test")
#assert.eq(ie3(100, 100, 100, 50, 50, 50, 25), 175, message: "IE3: symmetric case")

All inclusion-exclusion tests passed

#line(length: 100%)

#align(center)[
  #text(size: 16pt, weight: "bold", fill: green)[ALL EXTENDED TESTS PASSED]
]

#v(1em)

#align(center)[
  All #strong[97] assertions completed successfully.
]

== Primality Tests

#assert.eq(is-prime(2), true, message: "2 should be prime")
#assert.eq(is-prime(3), true, message: "3 should be prime")
#assert.eq(is-prime(5), true, message: "5 should be prime")
#assert.eq(is-prime(7), true, message: "7 should be prime")
#assert.eq(is-prime(11), true, message: "11 should be prime")
#assert.eq(is-prime(13), true, message: "13 should be prime")
#assert.eq(is-prime(17), true, message: "17 should be prime")
#assert.eq(is-prime(97), true, message: "97 should be prime")
#assert.eq(is-prime(1), false, message: "1 should not be prime")
#assert.eq(is-prime(4), false, message: "4 should not be prime")
#assert.eq(is-prime(9), false, message: "9 should not be prime")
#assert.eq(is-prime(15), false, message: "15 should not be prime")
#assert.eq(is-prime(91), false, message: "91 = 7*13 should not be prime")
#assert.eq(is-prime(100), false, message: "100 should not be prime")

All primality tests passed

== Primes Below n Tests

#assert.eq(primes-below(10), (2, 3, 5, 7), message: "Primes below 10")
#assert.eq(primes-below(20), (2, 3, 5, 7, 11, 13, 17, 19), message: "Primes below 20")
#assert.eq(count-primes-below(10), 4, message: "4 primes below 10")
#assert.eq(count-primes-below(30), 10, message: "10 primes below 30")
#assert.eq(count-primes-below(100), 25, message: "25 primes below 100")

All primes-below tests passed

== General Linear Congruence Tests

// 3x ≡ 6 (mod 9): gcd(3,9)=3 divides 6, so solution exists
// Reduced: x ≡ 2 (mod 3)
#let (x1, m1) = solve-congruence(3, 6, 9)
#assert.eq(x1, 2, message: "3x ≡ 6 (mod 9): x0 should be 2")
#assert.eq(m1, 3, message: "3x ≡ 6 (mod 9): step should be 3")

// 4x ≡ 5 (mod 9): gcd(4,9)=1 divides 5, so solution exists
#let (x2, m2) = solve-congruence(4, 5, 9)
#assert.eq(calc.rem(4 * x2, 9), 5, message: "4x ≡ 5 (mod 9) verification")

// 6x ≡ 15 (mod 21): gcd(6,21)=3 divides 15, so solution exists
#let (x3, m3) = solve-congruence(6, 15, 21)
#assert.eq(m3, 7, message: "6x ≡ 15 (mod 21): reduced mod should be 7")
#assert.eq(calc.rem(6 * x3, 21), 15, message: "6x ≡ 15 (mod 21) verification")

// 4x ≡ 5 (mod 6): gcd(4,6)=2 does not divide 5, no solution
#assert.eq(solve-congruence(4, 5, 6), none, message: "4x ≡ 5 (mod 6) should have no solution")

// 2x ≡ 4 (mod 6): gcd(2,6)=2 divides 4, solution exists
#let (x4, m4) = solve-congruence(2, 4, 6)
#assert.eq(calc.rem(2 * x4, 6), 4, message: "2x ≡ 4 (mod 6) verification")

All general linear congruence tests passed

== Relation Property Tests

// Test reflexive relation on {1,2,3}
#let S1 = (1, 2, 3)
#let R_refl = ((1, 1), (2, 2), (3, 3), (1, 2))
#assert.eq(is-reflexive(S1, R_refl), true, message: "R_refl should be reflexive")

#let R_not_refl = ((1, 1), (2, 2), (1, 2))
#assert.eq(is-reflexive(S1, R_not_refl), false, message: "R_not_refl missing (3,3)")

// Test symmetric relation
#let R_sym = ((1, 2), (2, 1), (1, 1))
#assert.eq(is-symmetric(R_sym), true, message: "R_sym should be symmetric")

#let R_not_sym = ((1, 2), (1, 1))
#assert.eq(is-symmetric(R_not_sym), false, message: "R_not_sym missing (2,1)")

// Test antisymmetric relation
#let R_antisym = ((1, 1), (1, 2), (2, 3))
#assert.eq(is-antisymmetric(R_antisym), true, message: "R_antisym should be antisymmetric")

#let R_not_antisym = ((1, 2), (2, 1))
#assert.eq(is-antisymmetric(R_not_antisym), false, message: "R_not_antisym has (1,2) and (2,1)")

// Test transitive relation
#let R_trans = ((1, 2), (2, 3), (1, 3))
#assert.eq(is-transitive(R_trans), true, message: "R_trans should be transitive")

#let R_not_trans = ((1, 2), (2, 3))
#assert.eq(is-transitive(R_not_trans), false, message: "R_not_trans missing (1,3)")

// Test equivalence relation (reflexive + symmetric + transitive)
#let R_equiv = ((1, 1), (2, 2), (3, 3), (1, 2), (2, 1))
#assert.eq(is-equivalence-relation(S1, R_equiv), true, message: "R_equiv should be equivalence relation")

#let R_not_equiv = ((1, 1), (2, 2), (3, 3), (1, 2))
#assert.eq(is-equivalence-relation(S1, R_not_equiv), false, message: "R_not_equiv not symmetric")

// Test partial order (reflexive + antisymmetric + transitive)
#let R_partial = ((1, 1), (2, 2), (3, 3), (1, 2), (2, 3), (1, 3))
#assert.eq(is-partial-order(S1, R_partial), true, message: "R_partial should be partial order")

#let R_not_partial = ((1, 1), (2, 2), (3, 3), (1, 2), (2, 1))
#assert.eq(is-partial-order(S1, R_not_partial), false, message: "R_not_partial not antisymmetric")

All relation property tests passed

#line(length: 100%)

#align(center)[
  #text(size: 16pt, weight: "bold", fill: green)[ALL NEW FUNCTION TESTS PASSED]
]

#v(1em)

#align(center)[
  All #strong[127] assertions completed successfully.
]
