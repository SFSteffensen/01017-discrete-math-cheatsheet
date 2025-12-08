#import "@local/dtu-template:0.5.1":*
#import "@preview/cetz:0.4.2"

#show: dtu-note.with(
  course: "01017",
  course-name: "Discrete Mathematics",
  title: "Discrete Mathematics - Exam Cheat Sheet",
  date: datetime.today(),
  author: "Sebastian Faber Steffensen (s255609)",
  semester: "2025 Fall",
)

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
      let want = remainders.at(i)
      let check = if r == want { [✓] } else { [✗] }
      [#x ≡ #r (mod #(moduli.at(i))) #check]
    })
    [*CRT Solution:* $x equiv #x pmod(#M)$ #h(1em) Verify: #verifications.join(", ")]
  }
}

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

= Examples + Solutions

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
    - $d = 1$: $1^2 = 1 | 5292$ ✓
    - $d = 3$: $3^2 = 9 | 5292$ ✓ (since $3^3 | 5292$)
    - $d = 36 = 2^2 dot 3^2$: Need $36^2 = 2^4 dot 3^4 | 2^2 dot 3^3 dot 7^2$. But $2^4 divides.not 2^2$! ✗
    - $d = 42 = 2 dot 3 dot 7$: $42^2 = 2^2 dot 3^2 dot 7^2 | 2^2 dot 3^3 dot 7^2$ ✓

    *Answer:* 36 cannot be the GCD.
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

    *For $n = 6$:* $gcd(6, 9) = 3 != 1$ → *Does not exist*

    *For $n = 2$:* $gcd(2, 9) = 1$ ✓. Find $x$ with $2x equiv 1 pmod(9)$:
    - $2 dot 5 = 10 equiv 1 pmod(9)$ → *Answer: 5*

    *For $n = 7$:* $gcd(7, 9) = 1$ ✓. Find $x$ with $7x equiv 1 pmod(9)$:
    - $7 dot 4 = 28 equiv 1 pmod(9)$ → *Answer: 4*
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

    *Answer:* $x equiv 59 pmod(70)$

    *Verify:* $59 = 29 dot 2 + 1$ ✓, $59 = 11 dot 5 + 4$ ✓, $59 = 8 dot 7 + 3$ ✓
  ]
]

#pagebreak()

== Functions: Injective/Surjective Analysis

#example(title: [Function classification])[
  Classify each function:
  1. $f: ZZ^+ -> NN$ given by $f(x) = floor(log_2(x))$
  2. $f: NN -> ZZ$ given by $f(x) = cases(ceil(x\/2) "if" x "even", -ceil(x\/2) "if" x "odd")$
  3. $f: NN -> NN$ given by $f(x) = x^3 + 1$

  #solution[
    *1. $f(x) = floor(log_2(x))$, $ZZ^+ -> NN$:*
    - Surjective? Every $n in NN$ is hit by $x = 2^n$. ✓
    - Injective? $f(2) = f(3) = 1$. ✗
    - *Surjective but not injective*

    *2. Alternating function $NN -> ZZ$:*
    - $f(0) = 0, f(1) = -1, f(2) = 1, f(3) = -2, f(4) = 2, ...$
    - Surjective? Hits all of $ZZ$. ✓
    - Injective? Each output appears exactly once. ✓
    - *Bijection*

    *3. $f(x) = x^3 + 1$, $NN -> NN$:*
    - Injective? $x^3$ is strictly increasing. ✓
    - Surjective? $f(0) = 1, f(1) = 2, f(2) = 9, ...$ — skips 3,4,5,6,7,8. ✗
    - *Injective but not surjective*
  ]
]

#pagebreak()

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

  Alternative form: $2binom(n, 2) + n^2 = n(n-1) + n^2 = n(2n-1)$ ✓
]

=== Degree Sequences

#example(title: [Valid degree sequence?])[
  Does a simple graph with degrees $2,2,3,3,3,3,3$ exist?

  #solution[
    Sum of degrees $= 2+2+3+3+3+3+3 = 19$.

    By handshaking lemma: $sum deg(v) = 2|E|$ must be even.

    Since $19$ is odd, *such a graph does not exist.*
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

#pagebreak()

== Combinatorics

=== Binomial Theorem

#example(title: [Coefficient in $(2x^2 - 3y^3)^8$])[
  Find coefficients of $x^8 y^{12}$ and $x^6 y^9$.

  #solution[
    General term: $binom(8, k)(2x^2)^k (-3y^3)^(8-k) = binom(8, k) 2^k (-3)^(8-k) x^(2k) y^(3(8-k))$

    *For $x^8 y^{12}$:* Need $2k = 8$ and $3(8-k) = 12$.
    - $k = 4$ ✓
    - Coefficient: $binom(8, 4) dot 2^4 dot (-3)^4 = 70 dot 16 dot 81 = 90720$

    *For $x^6 y^9$:* Need $2k = 6$ and $3(8-k) = 9$.
    - $k = 3$ but $8-k = 5$, and $3 dot 5 = 15 != 9$ ✗
    - *Coefficient is 0*
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

#pagebreak()

== Relations

#example(title: [Classify relations on ${1,2,3,4,5,6}$])[
  $R_1 = {(1,2),(2,3),(1,3),(4,5),(5,6),(4,6)}$

  #solution[
    - Reflexive? Missing $(1,1), (2,2), ...$ ✗
    - Symmetric? $(1,2) in R$ but $(2,1) in.not R$ ✗
    - Antisymmetric? No pair $(x,y), (y,x)$ with $x != y$ both present. ✓
    - Transitive? Check: $(1,2),(2,3) in R$ and $(1,3) in R$ ✓; $(4,5),(5,6) in R$ and $(4,6) in R$ ✓
    - *Transitive and antisymmetric only*
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

#pagebreak()

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

#pagebreak()

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
    *Base case ($n=1$):* $2 times 2$ board with one square removed = L-triomino. ✓

    *Inductive step:* Assume true for $2^k times 2^k$. For $2^(k+1) times 2^(k+1)$ board:

    1. Divide into four $2^k times 2^k$ quadrants
    2. The removed square is in one quadrant
    3. Place one L-triomino at the center, covering one square from each of the other three quadrants
    4. Now each quadrant is a $2^k times 2^k$ board with one square removed
    5. By IH, each can be tiled. ✓
  ]
]

#pagebreak()

== Polynomial Divisibility

#example(title: [$x^n + 1$ divisible by $x + 1$])[
  For which positive integers $n$ is $x^n + 1$ divisible by $x + 1$?

  #solution[
    $x + 1 | x^n + 1$ iff $x = -1$ is a root of $x^n + 1$.

    Evaluate at $x = -1$: $(-1)^n + 1$
    - If $n$ odd: $(-1)^n = -1$, so $-1 + 1 = 0$ ✓
    - If $n$ even: $(-1)^n = 1$, so $1 + 1 = 2 != 0$ ✗

    *Answer:* Divisible for all odd $n$, not divisible for any even $n$.
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

#pagebreak()

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

#pagebreak()

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

#pagebreak()

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
