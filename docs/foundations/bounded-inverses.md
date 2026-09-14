# The adiabatic theorem and bounded inverses

The exact common-domain adiabatic assertion is equivalent, in classical
ZF, to a static bounded inverse principle. The forward implication uses
only the existence of a bounded domain lift for a constant Hamiltonian.
The reverse implication supplies graph control to the analytic proof in
[graph-control.md](graph-control.md).

These are written mathematical arguments. The separate Lean reduction
described below uses ordinary mathlib foundations; it is not a
formalization of this equivalence over ZF.

## Statement and conventions

Completeness throughout means convergence of every proper Cauchy filter,
equivalently uniform/Cantor completeness in the metric setting. Let QAT
denote the universal classical-ZF formulation of the common-domain
[statement](../../Adiabatic/Unbounded/Statement.lean), including its
projection construction, bounded forward and inverse domain lifts,
both uniform operator-norm estimates, and uniqueness on the unit interval.
The supplied domain is Banach; it need not be Hilbert. The spectral gap
uses algebraic bijectivity of $H-zj$. The contour uses the unique bounded
inverse $E\to D$ when it exists and zero otherwise.

**Theorem (ZF).** QAT holds if and only if every bounded complex-linear
bijection from a uniformly complete complex Banach space to a uniformly
complete complex Hilbert space has a bounded inverse.

This assertion specifies the Banach/Hilbert direction. It does not refer
to the unrestricted Banach-space bounded inverse theorem.

## From evolution existence to a bounded inverse

Let $S:X\to Y$ be a bounded linear bijection, with $X$ Banach and $Y$
Hilbert. If $Y=\{0\}$, injectivity makes $X=\{0\}$ and the inverse is
bounded. Otherwise form

$$
D=Y\oplus_2X,\qquad E=Y\oplus_2Y,\qquad
j(y,x)=(y,Sx),\qquad B(y_1,y_2)=(y_2,y_1),\qquad H(t)=Bj.
$$

The norm $\|(y,x)\|_D=(\|y\|^2+\|x\|^2)^{1/2}$ makes $D$ a
Banach space. Finite products preserve filter completeness in ZF.
The inclusion $j$ is bounded, injective, and onto. The physical operator
on $j(D)=E$ is the self-adjoint unitary $B$; the family $H:D\to E$ is
constant and hence $C^2$.

The algebraic spectrum is exactly $\{-1,1\}$. Indeed, for $z\ne\pm1$,

$$
(B-zI)^{-1}=\frac{B+zI}{1-z^2},
$$

whereas $(y,y)$ and $(y,-y)$ are eigenvectors when $y\ne0$.
The fixed band $(0,2)$ and gap $1/2$ satisfy the exact hypotheses.

Apply QAT with $T=\pi/2$. Its actual strong propagator $U(t)$ has a
bounded domain lift $L(t):D\to D$. Since $j$ is onto, the lift identity
and strong equation imply, for each $v\in E$,

$$
\frac{d}{dt}U(t)v=-iTBU(t)v,\qquad U(0)v=v.
$$

The derivative of $(\cos(Tt)I+i\sin(Tt)B)U(t)v$ is zero. Scalar testing
and the real mean value theorem give
$U(t)=\cos(Tt)I-i\sin(Tt)B$, so $U(1)=-iB$. This calculation does not
assume that the explicit exponential already has a bounded domain lift.
Consequently

$$
jL(1)(y,0)=(0,-iy),\qquad
S^{-1}=i\,\pi_X L(1)\iota_Y.
$$

The displayed inverse is bounded and linear. Neither the error estimates
nor identification of the totalized contour projection was needed.

## From bounded inverses to the full theorem

Assume the bounded inverse principle and fix an input to QAT. At each
time $t$, let $A_t$ be the physical self-adjoint operator on $j(D)$ and
set

$$
G_t=\{(jd,H(t)d):d\in D\}\subseteq E\oplus_2E.
$$

Its graph is closed without an application of the closed graph theorem.
If $(u,v)$ belongs to its closure, continuity of inner products and
symmetry imply

$$
\langle v,jd\rangle=\langle u,H(t)d\rangle\qquad(d\in D),
$$

with the inner product linear in its first argument. Thus $u$ lies in
the maximal adjoint domain, represented by $v$. Self-adjointness gives
$u\in j(D)$ and $A_tu=v$, as required. No approximating sequence was
chosen.

The closed subspace $G_t$ is a uniformly complete Hilbert space, and
$F_t:D\to G_t$, $F_td=(jd,H(t)d)$, is a bounded bijection. Its bounded
inverse yields a finite $c_t\ge0$ such that

$$
\|d\|_D\le c_t\sqrt{\|jd\|^2+\|H(t)d\|^2}
\le c_t(\|jd\|+\|H(t)d\|).
$$

These are precisely the pointwise graph bounds in
[the graph-controlled ZF proof](graph-control.md). That proof retains
the algebraic spectral gap, constructs the projection and both
evolutions, and proves both estimates and uniqueness. It uses
$\forall t\,\exists c_t$, not a selected function $t\mapsto c_t$:
unique nonreal inverses and compactness supply the uniform control.
Applying it proves the reverse implication. This implication depends on
that written analytic proof and its
[explicit analytic constructions](analytic-constructions.md).

One extension step used there can be proved directly in ZF. If $V$ is
dense in a normed space and $A:V\to F$ is linear with
$\|Av\|\le M\|v\|$, where $F$ is uniformly complete, define

$$
C_n(x)=\overline{\{Av:v\in V,\ \|v-x\|<1/n\}}\qquad(n\ge1).
$$

These are nonempty closed nested sets with diameter at most $2M/n$.
Cantor completeness gives a unique common point. Unique specification
defines the extension at every $x$. Testing one approximation at a time
proves linearity and the bound; density proves uniqueness. This avoids
selecting approximating sequences. In particular, the argument requires
no appeal to a theorem stated only for extension of isometries.

## Lean verification

[DoubledSwap.lean](../../Adiabatic/Foundations/DoubledSwap.lean) constructs
the doubled common domain, checks self-adjointness and the spectrum containment in $\{-1,1\}$
(with equality for nonzero physical space), and supplies a `GappedHamiltonian` satisfying the
original interface. Its theorem
`bounded_inverse_of_doubled_adiabatic_theorem` applies the exact
adiabatic assertion and extracts the bounded inverse from its actual
strong propagator. The code uses the product $X\times Y$ with its
standard Banach norm, a harmless reordering and equivalent finite-product
norm compared with the display above.

The formal construction builds on
[StrongSwapInverse.lean](../../Adiabatic/Foundations/StrongSwapInverse.lean).
These theorems have ordinary mathlib dependencies, including
`Classical.choice`. They check the explicit example and inverse
extraction, not a model of ZF, not the reverse analytic implication over
ZF, and not the necessity of a choice principle. See the
[axiom audit](lean-audit.md).

## Choice bounds and references

Together with the [countable-choice sufficiency proof](countable-choice.md)
and [CMC necessity proof](countable-multiple-choice.md), the written
arguments give

$$
\mathrm{AC}_{\omega}\ \Longrightarrow\
\text{Banach-to-Hilbert bounded inverse principle}
\ \Longleftrightarrow\ \mathrm{QAT}
\ \Longrightarrow\ \mathrm{CMC}.
$$

Further [operator consequences](operator-consequences.md) include a
restricted closed graph theorem, Hilbert-domain uniform boundedness,
and bounded-size infinite partial choice. No equivalence with either
endpoint is established. In particular, uniqueness of trajectories alone does not establish their existence,
domain bounds, or adiabatic estimates.

Uniform completeness, Hilbert projection, and Riesz representation in
ZF are treated in Blackadar, Farah, and Karagila,
[*Hilbert Spaces Without the Countable Axiom of Choice*, Theorem 1.0.2
and §2](https://arxiv.org/html/2304.09602v3). The separable bounded
inverse theorem and self-adjoint spectral-radius identity used in the
graph-controlled proof are in Blackadar and Farah,
[*Separable C*-algebras Without the Countable Axiom of Choice*,
Proposition 2.0.1(6), Theorem 2.3.2, and Corollary 2.3.3](https://arxiv.org/html/2602.15812v1).
No novelty claim for the bounded inverse principle is made here.
