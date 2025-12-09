#import "@local/dtu-template:0.5.1":*
#import "@preview/cetz:0.4.2"
#import "@preview/cetz-venn:0.1.4": venn2, venn3
#import "@preview/auto-div:0.1.0": poly-div, poly-div-working

// Small circle for marking answers
#let mark-circle = box(width: 0.8em, height: 0.8em, stroke: 0.5pt + black, radius: 50%)

// Answer option with circle
#let ans(body) = grid(columns: (auto, 1fr), column-gutter: 0.5em, align: (center, left), mark-circle, body)

#show: dtu-note.with(
  course: "01017",
  course-name: "Discrete Mathematics",
  title: "01019 E24 Exam - Discrete Mathematics",
  date: datetime.today(),
  author: "DTU (Technical University of Denmark)",
  semester: "2024 Fall",
)

= 01019 E24 Exam Discrete Mathematics

Der anvendes en scoringsalgoritme, som er baseret på "One correct answer"

Dette betyder følgende:
- Der er altid præcist ét korrekt svar
- Studerende kan kun vælge ét svar per spørgsmål
- Hvert rigtigt svar giver 1 point. Så et spørgsmål, der består af f.eks. 3 del-spørgsmål, giver 3 points, hvis alle 3 er korrekte.
- Hvert forkert svar giver 0 point (der benyttes IKKE negative point)

The following approach to scoring responses is implemented and is based on "One correct answer":
- There is always only one correct answer
- Students are only able to select one answer per question
- Every correct answer that you click on corresponds to 1 point, so a question with 3 parts is worth 3 points if you get every part correct.
- Every incorrect answer corresponds to 0 points (incorrect answers do not result in subtraction of points)

== Question 1
If $a, b, c$, and $d$ are positive integers such that $a b | c d$, then which of the following must be true?

*Vælg en svarmulighed*
#ans[$a|"lcm"(c, d)$ or $b|"lcm"(c, d)$]
#ans[If $p$ is a prime that divides $a$, then $p|c$ or $p|d$]
#ans[None of these]
#ans[If $b$ is prime, then $b|"gcd"(c, d)$]
#ans[$"gcd"(a, b)| "gcd"(c, d)$]
#ans[$a|c$ or $a|d$ or $b|c$ or $b|d$]

== Question 2
For $n >= 4$, the number of edges in the $n$-cube $Q_n$ is

*Vælg en svarmulighed*
#ans[None of these]
#ans[$2^n + 16$]
#ans[$n 2^(n-1)$]
#ans[$2^(n+1)$]
#ans[$n! + 8$]

== Question 3
For each of the following, determine whether it is surjective/injective, or not a well defined function. Recall that $NN$ is the set of natural numbers, in other words the set of nonnegative integers, and $ZZ^+$ is the set of positive integers.

*Vælg de rigtige svarmuligheder*

#table(
  columns: (40%, 1fr, 1fr, 1fr, 1fr, 1fr),
  align: (left, center, center, center, center, center),
  [*Function*],
  [*Not well defined*],
  [*Well defined but neither*],
  [*Surjective but not injective*],
  [*Injective but not surjective*],
  [*Both surjective and injective*],
  [$f: ZZ^+ -> NN$ given by $f(x) = floor(log_2(x))$],
  mark-circle,
  mark-circle,
  mark-circle,
  mark-circle,
  mark-circle,
  [$f: RR -> ZZ^+$ given by $f(x) = floor(|x|)$],
  mark-circle,
  mark-circle,
  mark-circle,
  mark-circle,
  mark-circle,
  [$f: NN -> ZZ$ given by $f(x) = cases(ceil(x\/2) "if" x "is even", -ceil(x\/2) "if" x "is odd")$],
  mark-circle,
  mark-circle,
  mark-circle,
  mark-circle,
  mark-circle,
  [$f: RR -> {-1, 0, 1}$ given by $f(x) = floor(x) - ceil(x)$],
  mark-circle,
  mark-circle,
  mark-circle,
  mark-circle,
  mark-circle,
  [$f: NN -> NN$ given by $f(x) = x^3 + 1$],
  mark-circle,
  mark-circle,
  mark-circle,
  mark-circle,
  mark-circle,
)

== Question 4
Consider the following three statements on the complete graph $K_(2n)$:

(a): $K_(2n)$ has $binom(2n, 2)$ edges

(b): $K_(2n)$ has $2binom(n, 2) + n^2$ edges

(c): $K_(2n)$ has $n(2n - 1)$ edges

*Vælg en svarmulighed*
#ans[(a) and (b) are true, but (c) is false]
#ans[(a) and (b) and (c) are all true]
#ans[(a) and (c) are true, but (b) is false]
#ans[(b) and (c) are true, but (a) is false]
#ans[Precisely one of (a),(b),(c) is true]

== Question 5
Consider a simple graph with degrees 2,2,3,3,3,3,3.

*Vælg en svarmulighed*
#ans[Such a graph exists, and any such graph has less than 19 edges]
#ans[Such a graph does not exist]
#ans[Such a graph exists, and any such graph has precisely 19 edges]
#ans[Such a graph exists, and any such graph has more than 19 edges]
#ans[There exists such a graph with more than 19 edges and another with less than 19 edges]

== Question 6
How many elements are in the union of four sets if each set has 200 elements, each pair of sets share 50 elements, each three of the sets share 25 elements, and there are 5 elements in all four sets.

*Vælg en svarmulighed*
#ans[395]
#ans[695]
#ans[495]
#ans[595]
#ans[None of these]

== Question 7
Suppose that $a, b, c$, and $m$ are positive integers such that $a c equiv b c mod m$. Which of the following must be true?

*Vælg en svarmulighed*
#ans[$a equiv b mod m$]
#ans[$a - b in {k m : k in ZZ}$ if $"gcd"(c, m) = 1$]
#ans[$c|m(a - b)$]
#ans[$a equiv b mod c m$]
#ans[None of these]

== Question 8
If $2a + 3 equiv 2b + 3 mod m$, for positive integers $a, b$, and $m$, then which of the following does NOT necessarily have to be true?

*Vælg en svarmulighed*
#ans[$2a equiv 2b mod m$]
#ans[$a = k m + b$ for some $k in ZZ$]
#ans[$14a equiv 14b + 7m mod m$]
#ans[All of these are true]
#ans[$m|2(a - b)$]

== Question 9
Which of these three are partitions of $ZZ times ZZ$, that is, the set of ordered pairs of integers:

(a): the set of pairs $(x, y)$ where $x$ or $y$ (or both) are odd; the set of pairs $(x, y)$ where $x$ and $y$ are even;

(b): the set of pairs $(x, y)$ where $x$ and $y$ are odd; the set of pairs $(x, y)$ where $x$ and $y$ are even;

(c): the set of pairs $(x, y)$ where $x$ or $y$ (or both) are odd; the set of pairs $(x, y)$ where $x$ or $y$ (or both) are even.

*Vælg en svarmulighed*
#ans[None of them are]
#ans[(a) is a partition but (b),(c) are not]
#ans[Precisely two of them are]
#ans[(b) is a partition but (a),(c) are not]
#ans[(c) is a partition but (a),(b) are not]

== Question 10
Consider the statement: There exist infinitely many simple graphs (that is, graphs with no loops and no multiple edges) such that all degrees are distinct. This statement can be proved to be

*Vælg en svarmulighed*
#ans[neither true nor false because some graphs have all degrees distinct and others do not]
#ans[false by the pigeonhole principle]
#ans[false by giving a counterexample]
#ans[true by the pigeonhole principle]
#ans[true by induction]

== Question 11
Consider the polynomial $(2x^2 - 3y^3)^8$.

*Vælg de rigtige svarmuligheder*

#table(
  columns: (1fr, auto, auto, auto, auto, auto),
  align: (left, center, center, center, center, center),
  [ ],
  [*0*],
  [$2^4 3^4 binom(8, 4)$],
  [$-2^4 3^4 binom(8, 4)$],
  [$2^3 3^6 binom(8, 4)$],
  [$-2^4 3^6 binom(8, 4)$],
  [The coefficient of $x^8 y^12$ is],
  mark-circle,
  mark-circle,
  mark-circle,
  mark-circle,
  mark-circle,
  [The coefficient of $x^6 y^9$ is],
  mark-circle,
  mark-circle,
  mark-circle,
  mark-circle,
  mark-circle,
)

== Question 12
The polynomial $x^n + 1$ is divisible by the polynomial $x + 1$ (where $n$ is a positive integer)

*Vælg en svarmulighed*
#ans[for each $n >= 1$]
#ans[for each odd $n >= 1$, and for no even $n$]
#ans[for each even $n >= 4$, and for no odd $n$]
#ans[for infinitely many, but not all, even $n$, and for no odd $n$]
#ans[for $n = 1$ only]

== Question 13
The least number of cables required to connect ten computers to five printers to guarantee that, for every choice of five of the ten computers, these five computers can directly access five different printers is

*Vælg en svarmulighed*
#ans[40]
#ans[None of these]
#ans[$binom(10, 5)$]
#ans[30]
#ans[50]

== Question 14
Consider the following relations on ${1, 2, 3, 4, 5, 6}$:

$R_1$: ${(1, 2),(2, 3),(1, 3),(4, 5),(5, 6),(4, 6)}$.

$R_2$: ${(1, 1),(2, 2),(3, 3),(4, 4),(5, 5),(6, 6),(1, 2),(3, 4),(5, 6),(1, 6)}$.

$R_3$: ${(1, 2),(2, 3),(3, 4),(4, 5),(5, 6),(1, 3),(2, 4),(3, 5),(4, 6)}$.

Recall that questions below may appear in random order.

*Vælg de rigtige svarmuligheder*

#table(
  columns: (15%, 1fr, 1fr, 1fr, 1fr, 1fr),
  align: (left, center, center, center, center, center),
  [ ],
  [*an equivalence relation*],
  [*a partial ordering*],
  [*transitive and reflexive but not antisymmetric*],
  [*transitive and antisymmetric but not reflexive*],
  [*none of these*],
  [$R_3$ is],
  mark-circle,
  mark-circle,
  mark-circle,
  mark-circle,
  mark-circle,
  [$R_2$ is],
  mark-circle,
  mark-circle,
  mark-circle,
  mark-circle,
  mark-circle,
  [$R_1$ is],
  mark-circle,
  mark-circle,
  mark-circle,
  mark-circle,
  mark-circle,
)

== Question 15
For each of the following values of $n$, determine the multiplicative inverse of $n mod 9$ or indicate that it does not exist.

*Vælg de rigtige svarmuligheder*

#table(
  columns: (auto, auto, auto, auto, auto, auto, auto, auto, auto),
  align: (left, center, center, center, center, center, center, center, center),
  [ ],
  [*Does not exist*],
  [*0*],
  [*1*],
  [*2*],
  [*3*],
  [*4*],
  [*5*],
  [*6*],
  [$n = 6$],
  mark-circle,
  mark-circle,
  mark-circle,
  mark-circle,
  mark-circle,
  mark-circle,
  mark-circle,
  mark-circle,
  [$n = 2$],
  mark-circle,
  mark-circle,
  mark-circle,
  mark-circle,
  mark-circle,
  mark-circle,
  mark-circle,
  mark-circle,
  [$n = 7$],
  mark-circle,
  mark-circle,
  mark-circle,
  mark-circle,
  mark-circle,
  mark-circle,
  mark-circle,
  mark-circle,
)

== Question 16
Given a universal set $U$, which of the following sets are necessarily equal to $(B - A) union (overline(C) - A)$?

*Vælg en svarmulighed*
#ans[$emptyset$]
#ans[$(B union C) - A$]
#ans[$((U - B) union (U - C)) sect A$]
#ans[$(B sect C) - A$]
#ans[None of these]

== Question 17
20 people are seated around a round table.

*Vælg de rigtige svarmuligheder*

#table(
  columns: (1fr, auto, auto, auto, auto, auto),
  align: (left, center, center, center, center, center),
  [ ],
  [$2^20$],
  [$2^19$],
  [$20!$],
  [$19!$],
  [$19!\/2$],
  [Two seatings are considered identical if each person has the same two neighbors in the two seatings (but we don't care about left and right). The number of seatings is],
  mark-circle,
  mark-circle,
  mark-circle,
  mark-circle,
  mark-circle,
  [Two seatings are considered identical if each person has the same left neighbor and the same right neighbor in the two seatings. The number of seatings is],
  mark-circle,
  mark-circle,
  mark-circle,
  mark-circle,
  mark-circle,
  [Two seatings are considered identical if each person has the same left neighbor in the two seatings. The number of seatings is],
  mark-circle,
  mark-circle,
  mark-circle,
  mark-circle,
  mark-circle,
)

== Question 18
Let $a$ and $b$ be positive integers. Which of the following integers can NOT necessarily be written as $a s + b t$ for some integers $s$ and $t$?

*Vælg en svarmulighed*
#ans[All of these can be written as $a s + b t$ for some integers $s$ and $t$]
#ans[$"gcd"(a, b)^2 - 17 "lcm"(a, b)$]
#ans[$("lcm"(a,b))/("gcd"(a,b))$]
#ans[$"gcd"(2a, 6b)$]
#ans[$"gcd"(a, b)$]

== Question 19
Which of the following gives a recursive definition of the number of ways to choose 3 elements from an $n$ element set for $n >= 3$?

*Vælg en svarmulighed*
#ans[$f(3) = 1$ and $f(n + 1) = binom(n, 2)f(n - 1)$ for $n >= 3$]
#ans[None of these]
#ans[$f(4) = 1$ and $f(n) = n^4 + f(n - 1)$ for $n > 4$]
#ans[$f(3) = 1$ and $f(n) = binom(n, 3) + f(n - 1)$ for $n > 3$]
#ans[$f(n) = n^3$]
#ans[$f(3) = 1$ and $f(n) = ((n-1)(n-2))/2 + f(n - 1)$ for $n > 3$]

== Question 20
For any integers $n, m$, where $2 <= n <= m$, the binomial coefficient $binom(n+m, m+2)$ equals

*Vælg en svarmulighed*
#ans[$sum_(k=0)^n binom(n, k)binom(m, m-k)$]
#ans[$sum_(k=2)^n binom(n, k)binom(m, m+2-k)$]
#ans[$sum_(k=0)^(n+2) binom(n, k)binom(m, n-k)$]
#ans[None of these because we cannot use Vandermonde's identity in this case]
#ans[$sum_(k=1)^n binom(n, k)binom(m, m+1-k)$]

== Question 21
The number of derangements of 1,2,3,4,5,6,7 ending with 1,2,3 in some order is

*Vælg en svarmulighed*
#ans[$3!(4! - 1)$]
#ans[$3!4!\/2$]
#ans[$3!4!$]
#ans[$3!(4! - 3!)$]
#ans[None of these]

== Question 22
Consider the following system of congruences:

$x equiv 1 mod 2$

$x equiv 4 mod 5$

$x equiv 3 mod 7$

Indicate the set of all solutions to the above system of congruences.

*Vælg en svarmulighed*
#ans[${12 + 70k | k in ZZ}$]
#ans[${8 + 70k | k in ZZ}$]
#ans[${1 + 2k | k in ZZ} union {4 + 5k | k in ZZ} union {3 + 7k | k in ZZ}$]
#ans[${70 + 12k | k in ZZ}$]
#ans[${8 + 14k | k in ZZ}$]
#ans[${59 + 70k | k in ZZ}$]
#ans[None of these]

== Question 23
Let $P(x)$ denote the statement "$x$ is prime". Which of the following statements can be written in predicate logic as the following:

$forall x in ZZ (x > 1 -> (exists y in NN (P(y) and x < y < 2x)))$

*Vælg en svarmulighed*
#ans[For every integer $x$ greater than 1, every number strictly between $x$ and $2x$ is prime.]
#ans[None of these]
#ans[For every integer $x$, either $x > 1$ or there is a prime $y$ such that $x < y < 2x$.]
#ans[For any integer $x > 1$ and any prime $y$, if $x > 1$ then $x < y < 2x$.]
#ans[For every integer $x > 1$, there is a prime $y$ such that $x < y < 2x$.]
#ans[There exist infinitely many primes.]

== Question 24
Let $a$ and $b$ be two positive integers with $a b = 5292 = 2^2 3^3 7^2$. Which of the following values CANNOT be the greatest common divisor of $a$ and $b$?

*Vælg en svarmulighed*
#ans[1]
#ans[3]
#ans[36]
#ans[42]
#ans[All of these are possible values for $"gcd"(a, b)$]

== Question 25
It is possible to prove that a simple graph on $n >= 1$ vertices has at most $binom(n, 2)$ edges using mathematical induction. Here we take $binom(1, 2)$ to be equal to zero.

By choosing some of the following text fragments and putting them in the correct order, a proof by induction for the above statement can be created.

*A)* To prove the inductive step, assume that every simple graph on $n$ vertices has at most $binom(n, 2)$ edges, for every integer $n >= 1$. We will show that this implies that every simple graph on $n + 1$ vertices has at most $binom(n+1, 2)$ edges.

*B)* To prove the inductive step, assume that every simple graph on $n$ vertices has at most $binom(n, 2)$ edges, for some fixed integer $n >= 1$. We will show that this implies that every simple graph on $n + 1$ vertices has at most $binom(n+1, 2)$ edges.

*C)* The statement now follows from the principle of mathematical induction.

*D)* Since $v$ had at most $n$ edges incident to it, we have that $G$ has at most $n + binom(n, 2)$ edges. Moreover, $n + binom(n, 2) = n + (n(n-1))/2 = 1/2(2n + n^2 - n) = 1/2(n^2 + n) = ((n+1)n)/2 = binom(n+1, 2)$.

*E)* We prove the statement by induction. The base case is $n = 1$. A simple graph on 1 vertex cannot have any edges, so it has at most $binom(1, 2) = 0$ edges.

*F)* Let $G$ be a simple graph on $n + 1$ vertices. Pick any vertex $v in V(G)$ and note that $v$ has at most $n$ edges incident to it since there are $n$ vertices it could be adjacent to. Let $G'$ be the graph obtained from $G$ by removing $v$ and all the edges incident to $v$. Then $G'$ is a simple graph on $n$ vertices and thus it has at most $binom(n, 2)$ edges by our induction hypothesis.

*G)* Let $G$ be a simple graph on $n$ vertices. Construct a simple graph $G'$ on $n + 1$ vertices by adding a new vertex $v$ to $G$ and making it adjacent to an arbitrary subset $S$ of vertices of $G$. Since $G$ has $n$ vertices, we have that $|S| <= n$ and so $v$ is incident to at most $n$ edges. Therefore $G'$ has at most $n + binom(n, 2) = n + (n(n-1))/2 = 1/2(2n + n^2 - n) = 1/2(n^2 + n) = ((n+1)n)/2 = binom(n+1, 2)$ edges.

*PLEASE NOTE THAT THE QUESTIONS AND ANSWERS BELOW APPEAR IN RANDOM ORDER. PLEASE READ THEM CAREFULLY.*

*Vælg de rigtige svarmuligheder*

#block(width: 100%, breakable: false)[
  #table(
    columns: (20%, 0.5fr, 0.5fr, 0.5fr, 0.5fr, 0.5fr, 0.5fr, 0.5fr, 1fr),
    align: (left, center, center, center, center, center, center, center, center),
    [ ],
    [*A*],
    [*B*],
    [*C*],
    [*D*],
    [*E*],
    [*F*],
    [*G*],
    [*No more fragments*],
    [The first text fragment of the proof is],
    mark-circle,
    mark-circle,
    mark-circle,
    mark-circle,
    mark-circle,
    mark-circle,
    mark-circle,
    mark-circle,
    [The second text fragment of the proof is],
    mark-circle,
    mark-circle,
    mark-circle,
    mark-circle,
    mark-circle,
    mark-circle,
    mark-circle,
    mark-circle,
    [The third text fragment of the proof is],
    mark-circle,
    mark-circle,
    mark-circle,
    mark-circle,
    mark-circle,
    mark-circle,
    mark-circle,
    mark-circle,
    [The fourth text fragment of the proof is],
    mark-circle,
    mark-circle,
    mark-circle,
    mark-circle,
    mark-circle,
    mark-circle,
    mark-circle,
    mark-circle,
    [The fifth text fragment of the proof is],
    mark-circle,
    mark-circle,
    mark-circle,
    mark-circle,
    mark-circle,
    mark-circle,
    mark-circle,
    mark-circle,
  )
]

== Question 26
Consider the number of ways we can put $n + 1$ distinguishable balls (meaning that we can tell the difference between them) into $n$ distinct boxes.

*Vælg de rigtige svarmuligheder*

#table(
  columns: (1fr, auto, auto, auto, auto, auto),
  align: (left, center, center, center, center, center),
  [ ],
  [*none of these*],
  [$2n!$],
  [$binom(n+1, 2)n!$],
  [$n^(n+1) - 2n!$],
  [$n^(n+1) - binom(n+1, 2)n!$],
  [If at least one box is empty, the number of ways is],
  mark-circle,
  mark-circle,
  mark-circle,
  mark-circle,
  mark-circle,
  [If no box is empty, the number of ways is],
  mark-circle,
  mark-circle,
  mark-circle,
  mark-circle,
  mark-circle,
)
