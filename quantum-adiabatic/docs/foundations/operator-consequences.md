# Operator consequences and the finite-choice limit

The [Banach-to-Hilbert bounded inverse principle](bounded-inverses.md)
has the closed graph, uniform boundedness, and finite-choice consequences
proved below. Through its equivalence with the exact common-domain
adiabatic assertion, each is also a consequence of that assertion.
All analytic arguments here are written in classical ZF, with
completeness meaning convergence of every proper Cauchy filter.

The finite-choice conclusion is **infinite partial choice** for sets of
uniformly bounded finite size. The arguments do not establish full
countable choice, even for pairs, or identify the exact weakest choice
principle for the adiabatic theorem.

## A restricted closed graph theorem

The bounded inverse principle is equivalent to the following assertion:
every everywhere-defined complex-linear map from a uniformly complete
complex Hilbert space to a uniformly complete complex Banach space, with
closed graph, is bounded.

For one direction, let $A:H\to X$ have closed graph $G\subseteq H\times X$,
using the sum norm. Then $G$ is uniformly complete, and the coordinate
projection $\pi:G\to H$ is a bounded bijection. The inverse principle
makes $\pi^{-1}$ bounded, hence $A=\pi_X\pi^{-1}$ is bounded.

Conversely, let $j:X\to H$ be a bounded bijection. Its algebraic inverse
exists by unique specification. Its graph is closed, being the zero set
of the continuous map $(h,x)\mapsto h-jx$. The displayed closed graph
principle makes this inverse bounded. This equivalence has Hilbert
domain and Banach target; it does not assert the unrestricted
Banach-space closed graph theorem.

## Uniform boundedness on a Hilbert domain

**Proposition (ZF).** The bounded inverse principle implies uniform
boundedness for every set-indexed, pointwise bounded family of bounded
complex-linear maps on a uniformly complete Hilbert space. The normed
target spaces may depend on the index and need not be complete.

Let $T_i:H\to Y_i$ be such a family and put

$$
p(x)=\sup\bigl(\{0\}\cup\{\|T_ix\|:i\in I\}\bigr),\qquad
\|x\|_D=\|x\|_H+p(x).
$$

Pointwise boundedness gives a uniquely specified finite supremum.
The triangle inequality and absolute homogeneity make the second
expression a norm on the underlying vector space. The identity
$j:D\to H$ is a bounded bijection.

To prove completeness of $D$, let $\mathcal F$ be a proper Cauchy
filter in this norm. Its image in $H$ converges to a unique $x$.
For $\varepsilon>0$, fix one $A\in\mathcal F$ with $D$-diameter at
most $\varepsilon$. For each $a\in A$, the set

$$
C_a=\{z:\|a-z\|_H+p(a-z)\le\varepsilon\}
$$

is closed in $H$: it is the intersection of the closed sublevel sets
for $\|a-z\|_H$ and all $\|a-z\|_H+\|T_i(a-z)\|$. The first
sublevel also handles an empty index set. Since $A\subseteq C_a$,
the filter limit belongs to $C_a$. Hence $\|a-x\|_D\le\varepsilon$
for every $a\in A$. This proves convergence in $D$, without choosing
a sequence of filter members or vectors.

The bounded inverse principle now gives a finite $C$ with
$\|x\|_D\le C\|x\|_H$. Thus
$\|T_ix\|\le C\|x\|_H$ for all $i,x$, the required uniform bound.
No converse to this consequence is proved here.

## Everywhere-defined symmetric operators

**Corollary (ZF).** The same principle implies the Hellinger–Toeplitz
conclusion: every everywhere-defined symmetric complex-linear map
$A:H\to H$ is bounded, for uniformly complete $H$.

Use the convention that the inner product is linear in its first
argument. For $y$ in the unit ball, the map

$$
f_y(x)=\langle x,Ay\rangle=\langle Ax,y\rangle
$$

is a bounded linear functional; the single vector $Ay$ supplies its
bound. For fixed $x$, Cauchy–Schwarz gives $|f_y(x)|\le\|Ax\|$.
Uniform boundedness therefore gives a common $C$ with
$|\langle Ax,y\rangle|\le C\|x\|$ on the unit ball. If $Ax\ne0$,
take $y=Ax/\|Ax\|$; the zero case is immediate. Thus $A$ is bounded.

## Infinite partial choice for bounded finite sizes

Write $\mathrm{PC}(\aleph_0,\le m)$ for this assertion: every sequence
$(S_n)$ of nonempty sets of size at most $m$ has a choice function
on an infinite subset of $\mathbb N$.

**Corollary (ZF).** The exact common-domain adiabatic assertion implies
$\mathrm{PC}(\aleph_0,\le m)$ for every natural number $m$.

Prove this by finite induction on $m$. The case $m=0$ is vacuous,
and singleton fibers have uniquely specified elements. If infinitely
many fibers are singletons, their unique elements give the conclusion.
Otherwise infinitely many have size at least two. Form the
filter-complete Hilbert space $H=\ell^2(\{(n,a):a\in S_n\};\mathbb C)$
and define the bounded projection $Q_n$ onto the zero-sum functions
in the $n$th fiber:

$$
(Q_nx)(n,a)=x(n,a)-\frac1{|S_n|}\sum_{b\in S_n}x(n,b),
$$

with zero coordinates outside that fiber. This is canonical. When
$|S_n|\ge2$, the nonzero orthogonal projection has norm one, so the
operators $T_n=(n+1)Q_n$ have unbounded norms. The uniform boundedness
proposition gives a single $x$ for which $\|T_nx\|$ is unbounded.
Consequently the active set $J=\{n:Q_nx\ne0\}$ is infinite.

On each active fiber, $a\mapsto x(n,a)$ is nonconstant. Its finite
set of complex values has a largest value in the lexicographic order
on real and imaginary parts. Let $S'_n$ be the preimage of that value.
It is a uniquely specified nonempty proper subset of $S_n$, hence
$|S'_n|\le m-1$. The active indices have a canonical increasing
enumeration. Apply the induction hypothesis to the resulting sequence
of $S'_n$ to obtain an infinite partial selector for the original
sequence. This is a finite induction, not a countable dependent
selection.

This conclusion accompanies the separate
[CMC lower bound](countable-multiple-choice.md). No strict improvement
over CMC alone is asserted here.

## Why this does not establish full finite choice

Hall and Shelah prove, relative to consistency of ZF, that for any prime
$p$ there is a model of ZF satisfying
$\mathrm{PC}(\aleph_0,\le m)$ for every $m$, but failing full countable
choice for $p$-element sets. This includes pairs. Their construction
explicitly transfers from atoms to pure ZF.
[Published Theorem 2.1, p. 208](https://www.impan.pl/shop/en/publication/transaction/download/product/88931).

Fellhauer's published Theorem 3.3.12 states a full bounded-finite-choice
consequence of uniform boundedness. Its displayed proof extracts smaller
subsets on an infinite set of indices and repeats finitely many times.
That step gives partial choice; promotion to a selector on every index
requires another argument. The original arXiv version states the partial
conclusion. This review therefore uses only the direct partial-choice
proof above.
[Published proof, pp. 18–19](https://math.hawaii.edu/home/jla/258-968-1-PB.pdf),
[original version, Theorem 3.2.4, p. 16](https://arxiv.org/pdf/1509.01078v1).

This identifies a gap in the inspected promotion, not a counterexample
to its conclusion by every possible argument. The Hall–Shelah model
is not shown here to satisfy QAT or Hilbert-domain uniform boundedness.
Neither full pair choice nor its failure follows from this review.

## Limits of the attempted symmetry constructions

Three proposed encodings fail for explicit reasons.

For a sequence of pairs, let $B_n=\prod_{k<n}A_k$. Passing to zero-sum
functions on $B_n$ does not force finite active levels under failure of
pair choice. Orient the single pair $A_0$. For every $n\ge1$, the
function taking values $\pm1$ according only to $b(0)$ is nonzero
and centered on $B_n$. Divide by $\sqrt{|B_n|}$ and multiply by
$2^{-n}$. The resulting square-summable vector is active at every level,
without orientations of the remaining pairs.

The tensor sign representation also fails to select a prefix: a nonzero
vector that changes sign under each coordinate flip distinguishes a
parity class. With at least two coordinates, simultaneous flips preserve
the vector while moving every prefix. Likewise, an alternating function
on the orderings of an $m$-element set specifies an orientation. For
$m\ge3$, the alternating group is still transitive on the set, so an
orientation supplies no equivariant point selector. For $m=2$, it does.

More generally, an additive representation cannot repair the two-pair
construction by making every nonzero vector select a prefix equivariantly.
Let $A,B$ be additive involutions on an abelian group $V$. If $A$ has
only zero as a fixed vector, then

$$
A(x+Ax)=Ax+x=x+Ax
$$

forces $Ax=-x$ for every $x$. If $B$ also has only zero fixed, then
$A=B=-I$, so $AB=I$. If $AB$ also has only zero fixed, $V$ is trivial.
No commuting assumption, field, or division by two is needed.

For two independent coordinate flips of a pair-prefix set, each of
$A,B,AB$ has no fixed prefix. An equivariant selector on every nonzero
vector would force each corresponding additive map to have only zero
fixed; the lemma rules this out for nontrivial $V$. It does not rule out
selectors on a more restricted class of uniform-boundedness witnesses,
or another route to full finite choice.

## Formalization and remaining scope

The analytic implications and partial-choice conclusion above are not
Lean formalizations of ZF. The finite symmetry calculations are checked
in [SymmetryObstruction.lean](../../Adiabatic/ChoiceReduction/SymmetryObstruction.lean).
The four additive involution results in
[InvolutionObstruction.lean](../../Adiabatic/ChoiceReduction/InvolutionObstruction.lean)
have only `propext` in their axiom reports; the final result explicitly
takes `DecidableEq V`. These results verify the stated obstruction,
not a theorem that all stronger choice reductions are impossible.
The [Lean audit](lean-audit.md) records their exact scope.

The unresolved directions remain whether CMC suffices for QAT and
whether QAT implies full countable choice. The written bounds and
bounded inverse characterization do not settle either direction.
