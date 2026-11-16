# Countable choice suffices

Countable choice, denoted $\mathrm{AC}_\omega$, says that every sequence
of nonempty sets has a choice function. In classical ZF plus this
principle, the full common-domain adiabatic theorem holds with its original
supplied domain norm. This is a written mathematical proof, not a Lean
formalization of ZF or a removal of `Classical.choice` from the Lean theorem.

All Banach and Hilbert spaces below are uniformly complete: every proper
Cauchy filter converges. This implies the sequential completeness needed
for the series below, and closed subspaces retain uniform completeness.
The [analytic construction](analytic-constructions.md) uses this convention
throughout.

## Open mapping from countable choice

**Theorem ($\mathrm{ZF}+\mathrm{AC}_\omega$).** Every bounded surjective
linear map between Banach spaces is open.

The following is the direct argument of K. Hirao, with the choices and
correction recursion written explicitly. Hirao's public answer was posted
on 21 April 2026 and revised on 20 June 2026. Elliot Glazer's answer of
20 June 2025 gives a different proof through a restricted closed graph
theorem. These are authored public proofs; no journal refereeing status is
asserted here.
[Original proofs](https://math.stackexchange.com/questions/146910/does-the-open-mapping-theorem-imply-the-baire-category-theorem)

**Proof.** Let $T:X\to Y$ be bounded and onto. If it is not open, no
neighborhood of zero is contained in $T(B_X(0,1))$. Countable choice
therefore gives

$$
\|y_n\|<2^{-n},\qquad y_n\notin T(B_X(0,1)).
$$

Let $Y_0$ be their closed linear span and $X_0=T^{-1}(Y_0)$.
These are closed, hence uniformly complete, subspaces. The restriction
$T_0:X_0\to Y_0$ is surjective and still not open. Finite rational
linear combinations of the $y_n$ give a specified dense sequence in
$Y_0$; over $\mathbb C$, use rational real and imaginary parts.
Thus it suffices to treat a codomain with a specified dense sequence.
No separability of $X_0$ is inferred.

Baire's theorem for a complete metric space with a specified dense
sequence is provable in ZF: enumerate the rational balls and at each
stage use the least ball whose closure lies in the preceding ball and
the next dense open set, with diameter tending to zero. This is a
recursion with a uniquely specified next step. Apply it to

$$
Y=\bigcup_{m\ge1}\overline{T(B_X(0,m))}.
$$

Some set on the right has interior. Subtracting two points in that
interior and approximating each by an image point gives numbers
$r,M>0$ such that

$$
B_Y(0,r)\subseteq\overline{T(B_X(0,M))}.
\tag{1}
$$

Fix a countable basis $(O_k)$ of $Y$. For each basis member meeting
$T(B_X(0,M))$, countable choice supplies
$a_k\in B_X(0,M)$ with $Ta_k\in O_k$; use $a_k=0$ for a basis
member not meeting that image. The resulting images are dense in
$T(B_X(0,M))$. All these bounded preimages are fixed before the
following recursion.

For $y\in B_Y(0,r)$, set $e_0=y$. Given $e_n$ with
$\|e_n\|<2^{-n}r$, let $k_n$ be the least index satisfying

$$
\|2^n e_n-Ta_{k_n}\|<r/2,
\qquad e_{n+1}=e_n-2^{-n}Ta_{k_n}.
$$

Such an index exists by (1) and density. Induction gives
$\|e_{n+1}\|<2^{-n-1}r$. The specified series

$$
x=\sum_{n=0}^{\infty}2^{-n}a_{k_n}
$$

converges in $X$, satisfies $\|x\|\le2M$, and has $Tx=y$.
Scaling by $1/(4M)$ yields

$$
B_Y(0,r/(4M))\subseteq T(B_X(0,1)),
$$

contradicting nonopenness. Dependent choice is unnecessary: the only
selections were countable families fixed before the least-index
recursion. $\square$

In particular, every bounded linear bijection between these spaces has
a bounded inverse. This proof applies to arbitrary Banach targets; its
use for Hilbert targets below is a restriction of that result.

## Application to the adiabatic theorem

Take the original common-domain hypotheses: a uniformly complete complex
Hilbert space $E$, a uniformly complete complex Banach space $D$,
a bounded injective dense inclusion $j:D\to E$, and a $C^2$ family
$H(t):D\to E$ whose physical operators on $j(D)$ are self-adjoint.
The band endpoints are continuous and have a uniform positive gap from
the algebraic spectrum, as in
[the formal statement](../../Adiabatic/Unbounded/Statement.lean).

For each fixed $t$, the self-adjoint graph

$$
G_t=\{(jd,H(t)d):d\in D\}\subseteq E\oplus_2E
$$

is a closed Hilbert subspace. Indeed, every point $(u,v)$ in its closure
satisfies the adjoint-domain identity
$\langle v,jd\rangle=\langle u,H(t)d\rangle$ for all $d\in D$;
maximal self-adjointness puts $(u,v)$ in the graph. No approximating
sequence or closed graph theorem is needed for this assertion.

The bounded bijection

$$
F_t:D\longrightarrow G_t,\qquad F_td=(jd,H(t)d)
$$

therefore has a bounded inverse. It follows that

$$
\forall t\in[0,1]\ \exists c_t\ge0\ \forall d\in D,\qquad
\|d\|_D\le c_t(\|jd\|+\|H(t)d\|).
\tag{2}
$$

Only one time is fixed in this argument; a function $t\mapsto c_t$
is neither supplied nor selected. The
[graph-controlled ZF theorem](graph-control.md) and its
[analytic proof](analytic-constructions.md) now construct the specified
orthogonal spectral projection and the normalized unitary strong evolution,
with bounded forward and inverse domain lifts and strong forward domain
continuity. They prove uniqueness on $[0,1]$ and both uniform $C/T$
operator-norm bounds, with one $C$ independent of positive $T$ and time.
The algebraic gap and the totalized bounded inverse used by the original
contour definition are retained.

Combined with the [bounded inverse equivalence](bounded-inverses.md) and
the [countable multiple choice consequence](countable-multiple-choice.md),
the written implications are

$$
\mathrm{AC}_\omega
\ \Longrightarrow\
\text{Banach-to-Hilbert bounded inverse principle}
\ \Longleftrightarrow\ \mathrm{QAT}
\ \Longrightarrow\ \mathrm{CMC}.
$$

Here CMC requires a finite nonempty subset of each member of a sequence of
nonempty sets. Neither converse at the ends of this chain is established.
In particular, the chain does not identify the weakest choice principle
equivalent to the exact theorem.
