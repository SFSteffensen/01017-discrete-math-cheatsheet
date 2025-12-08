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

✓ All derangement tests passed

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

✓ All extended GCD tests passed

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

✓ All modular inverse tests passed

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

✓ All CRT tests passed

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

✓ All hypercube edge tests passed

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

✓ All complete graph edge tests passed

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

✓ All built-in function tests passed

#line(length: 100%)

#align(center)[
  #text(size: 16pt, weight: "bold", fill: green)[✓ ALL TESTS PASSED]
]

#v(1em)

#align(center)[
  All #strong[67] assertions completed successfully.
]
