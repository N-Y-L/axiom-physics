# Separable physical spaces and well-orderable dense subsets

**Theorem (ZF).** Suppose the physical Hilbert space $E$ has a
well-orderable dense subset. Under the remaining original hypotheses,
the full common-domain adiabatic theorem holds for an arbitrary supplied
uniformly complete Banach domain $D$. In particular, a specified dense
sequence in $E$ suffices; no separability assumption on $D$ is added.

This is a written mathematical result, not a Lean formalization. Its
additional foundation is Elliot Glazer's public proof of the closed graph
theorem for a Banach domain with a well-orderable dense subset, reconstructed
below using relative constructibility. It does not follow merely from
the separable bounded inverse theorem.

Throughout, uniform completeness means convergence of every proper Cauchy
filter. A well-orderable dense subset means that a dense subset and a
well-order on it can be fixed for the argument. It does not assert that
the whole space is well-orderable.

## Closed graph with a well-orderable dense domain

**Lemma (ZF; Glazer).** Let $X,Y$ be uniformly complete real or complex
Banach spaces. If $X$ has a well-orderable dense subset, every
everywhere-defined linear map $T:X\to Y$ with closed graph is bounded.

The source is Glazer's answer of 20 June 2025, revised on 24 June.
It is an authored public proof; no journal refereeing status is asserted.
[Glazer's proof](https://math.stackexchange.com/questions/146910/does-the-open-mapping-theorem-imply-the-baire-category-theorem#5077044)

**Proof.** Regard complex spaces as real spaces. Enlarge the dense subset
to its rational linear span. Finite tuples from a well-ordered set and
rational coefficients form a well-orderable set; taking the least
representation of each vector well-orders the span. Enumerate it without
repetition as $V=\{x_\alpha:\alpha<\kappa\}$.

Record the addition and rational scalar operations on these indices and
the norm cuts

$$
R=\{(\alpha,q):\alpha<\kappa,\ q\in\mathbb Q,\ q<\|x_\alpha\|\}.
$$

Also record the predicate

$$
S=\{(s,q):s\in\kappa^\omega,\ q\in\mathbb Q,\
     x_{s(n)}\longrightarrow x\text{ in }X
     \text{ for some }x,\ q<\|Tx\|\}.
$$

The limit, when it exists, is unique, so this defines a set without
selecting limits. Encode the finitely many predicates as one tagged set
$A$, and form $M=L[A]$.

For an arbitrary set predicate $A$, relative constructibility gives
$M\models\mathrm{ZFC}$ and $A\cap M\in M$. It does **not** imply that
$A\in M$, or that every external sequence belongs to $M$.
This is Jech, *Set Theory*, third millennium edition, Theorem 13.22
and Lemma 13.23, pp. 192–193.
[Textbook](https://daiwz.net/course/disc_math/2023/set_theory_jech.pdf#page=192)

All finite tuples of ordinals and rationals are in $M$. Consequently
the operation predicates and $R$ are available in full. For $S$, only
sections belonging to sequences $s\in(\kappa^\omega)^M$ are needed.
Each such section contains all the external rational comparisons with
$\|T\lim x_{s(n)}\|$. Its cut defines the same real value internally.
The existence of the external limit follows from completeness whenever
the sequence is internally Cauchy, because its norm comparisons are
absolute.

Inside $M$, complete the coded rational normed space $V$ to a real
Banach space $X'$. Its points are equivalence classes of internally
coded Cauchy sequences. Taking the unique external limit defines an
isometric embedding

$$
J_X:X'\longrightarrow X.
$$

This embedding need not be onto. Let $\mathcal C$ be the internal
space of Cauchy sequence codes in $V$, with seminorm

$$
p(s)=\|T(J_X[s])\|,
$$

defined internally by the $S$-section. Pointwise addition and rational
scaling give the seminorm laws, since they hold externally. Quotient by
the zero seminorm and take the completion in $M$, obtaining a Banach
space $Y'$. The map from the quotient into $Y$ sends a code to
$T(\lim x_{s(n)})$; it is an isometry. Unique external limits extend
it to an isometric embedding $J_Y:Y'\to Y$.

Assigning to a point of $X'$ the class of any representing sequence
defines $T':X'\to Y'$. Different representatives have the same
external $X$-limit, hence zero seminorm difference after applying
$T$. Thus the definition is independent of the representative, and

$$
J_YT'=TJ_X.
\tag{1}
$$

The map $T'$ is internally real-linear, not just rational-linear.
For a scalar in $\mathbb R^M$, use its specified rational approximations
in the completion. Under $J_X$ and $J_Y$ these are the ordinary
external scalar operations. External real-linearity of $T$ and
injectivity of $J_Y$ then give the required identity for $T'$.
This argument does not presume continuity of $T$.

To prove its graph closed in $M$, take an internal sequence
$a_n\to0$ in $X'$ for which $T'a_n$ converges in $Y'$.
Choice within $M$ supplies a matrix of internal representing sequences
for the $a_n$. Their external row limits
$b_n=J_Xa_n$ are uniquely specified, so Replacement forms the
sequence $(b_n)$ in the surrounding ZF universe. The isometries give
$b_n\to0$ and $Tb_n=J_YT'a_n$ convergent in $Y$. Since the
external graph of $T$ is closed, this last limit is zero. Therefore
$\|T'a_n\|\to0$. This verifies sequential closedness internally,
which in the ZFC model $M$ is equivalent to closedness.

The ordinary closed graph theorem in $M$ now supplies an integer
$N$ with

$$
\|T'a\|\le N\|a\|\qquad(a\in X').
$$

For every $\alpha<\kappa$, the constant code for $x_\alpha$ belongs
to $M$. The norm cuts and (1) transfer the same integer bound to the
entire original dense rational subspace:

$$
\|Tv\|\le N\|v\|\qquad(v\in V).
\tag{2}
$$

It remains to pass from $V$ to all of the external $X$. For fixed
$x\in X$, the nonempty closed sets

$$
C_n(x)=\overline{\{Tv:v\in V,\ \|v-x\|<1/n\}}
$$

decrease and have diameter at most $2N/n$. Uniform completeness of
$Y$ gives a unique common point $\widetilde T x$. Finite
approximations and (2) give
$\|\widetilde T x\|\le N\|x\|$ and show that
$(x,\widetilde T x)$ is in the closure of the graph of $T|_V$.
Closedness of the full graph forces $\widetilde T x=Tx$. Hence
$T$ is bounded on $X$. This last step selects no sequence of dense
approximants and needs no second inner model. $\square$

Uniform completeness and the shrinking-closed-sets criterion used here
are equivalent in ZF by Blackadar–Farah–Karagila, Theorem 1.0.2.
[Hilbert Spaces Without the Countable Axiom of Choice](https://arxiv.org/html/2304.09602v3)

## Application to the self-adjoint graph

Fix data for the original theorem and a time $t\in[0,1]$. Its
self-adjoint graph

$$
G_t=\{(jd,H(t)d):d\in D\}\subseteq E\oplus_2E
$$

is a closed, uniformly complete Hilbert subspace. This follows directly
from the maximal adjoint-domain identity, as in the
[bounded inverse reduction](bounded-inverses.md).

Let $W\subseteq E$ be the fixed well-orderable dense subset.
The finite product $W\times W$ is dense and well-orderable in
$E\oplus_2E$. Orthogonal projection onto $G_t$ maps it to a dense
subset of $G_t$; order each image point by its least preimage.
This gives a well-orderable dense subset of $G_t$ without selecting
representatives from an arbitrary family. Orthogonal projection onto
closed subspaces of uniformly complete Hilbert spaces is valid in ZF
by Blackadar–Farah–Karagila, Theorem 2.0.4 and Corollary 2.0.5.
[Primary paper](https://arxiv.org/html/2304.09602v3)

The graph map $F_t:D\to G_t$, $d\mapsto(jd,H(t)d)$, is a bounded
bijection. Its algebraic inverse is uniquely defined. Its graph is
closed, being the coordinate interchange of the closed graph of $F_t$.
Apply the preceding lemma to $F_t^{-1}:G_t\to D$. The lemma requires a
well-orderable dense subset only in its **domain**, which is $G_t$;
it places no such requirement on its Banach target $D$. Thus

$$
\forall t\in[0,1]\ \exists c_t\ge0\ \forall d\in D,\qquad
\|d\|_D\le c_t(\|jd\|+\|H(t)d\|).
$$

These pointwise bounds suffice for the
[graph-controlled ZF theorem](graph-control.md). The
[analytic construction](analytic-constructions.md) retains the original
algebraic gap and contour inverse convention, constructs the projection
and the strong unitary evolution with both bounded domain lifts, proves
uniqueness on $[0,1]$, and proves both uniform $C/T$ estimates.
This proves the stated corollary for arbitrary supplied $D$.

## Elementary separable domain cases

A simpler route is available if $D$ itself has a specified dense
sequence. Its image under $j$ is dense in $E$. Projecting the resulting
product dense sequence onto $G_t$ makes $G_t$ explicitly separable.
Then $F_t:D\to G_t$ is a bounded bijection between separable Banach
spaces. The separable bounded inverse theorem in ZF supplies graph
control. This uses Blackadar–Farah, Proposition 2.0.1(6).
[Separable C*-algebras Without the Countable Axiom of Choice](https://arxiv.org/html/2602.15812v1)

In particular, if $E$ has a specified dense sequence and $D$ carries
its actual initial graph norm, the graph isometry $D\to G_0$ and its
unique inverse transfer a dense sequence from $G_0$ to $D$.
These elementary cases do not need the inner-model lemma. The stronger
result for separable $E$ and an arbitrary supplied Banach norm on $D$
does need that additional argument.

The restrictions on $E$ here do not classify the theorem over all
Hilbert spaces. Neither the closed graph lemma nor these adiabatic
corollaries have been checked in Lean.
