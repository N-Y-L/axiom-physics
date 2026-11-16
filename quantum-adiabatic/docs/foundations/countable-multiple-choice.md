# The common-domain theorem implies countable multiple choice

The common-domain adiabatic theorem implies countable multiple choice
(CMC). A constant bounded Hamiltonian proves this from evolution existence
alone when the domain norm is supplied arbitrarily. A second construction
proves necessity even when the domain norm is exactly the initial graph
norm: it violates projection regularity and both adiabatic estimates.

This is a mathematical proof in classical ZF. Completeness means that
every proper Cauchy filter converges. The assertion under discussion is
the classical set-theoretic formulation of the hypotheses and conclusions
in [Statement.lean](../../Adiabatic/Unbounded/Statement.lean), with the
supplied complete Banach domain and the bounded lifts in
`StrongPropagator`. It is not a model of the entire Lean environment.

The construction extends the repository's earlier
[bounded-lift reduction](bounded-lifts.md) by encoding an arbitrary
failure of countable multiple choice. Closely related bounded-inverse
and summable-coordinate constructions are established in the literature;
see the attribution below.

## Statement

**Countable multiple choice (CMC)** says that for every sequence
$(A_n)_{n\in\mathbb N}$ of nonempty sets, there is a family
$(F_n)_{n\in\mathbb N}$ with each $F_n\subseteq A_n$ finite and
nonempty.

**Theorem (ZF).** The universally quantified common-domain theorem's
evolution-existence conclusion, including a bounded domain lift for every
$T>0$, implies CMC.

## From failure of CMC to finite level support

Suppose that a sequence $(A_n)$ has no multiple choice family. Let

$$
B_n=\prod_{k\leq n}A_k.
$$

Each $B_n$ is nonempty by finite choice, which is provable in ZF.
There cannot be an infinite $S\subseteq\mathbb N$ and an actual
family of finite nonempty sets $F_n\subseteq B_n$ for $n\in S$.
Otherwise define

$$
m(k)=\min\{n\in S:k\leq n\},\qquad
G_k=\{b(k):b\in F_{m(k)}\}.
$$

Every $G_k$ is a finite nonempty subset of $A_k$, a contradiction.
The least index and set image are uniquely defined; no prefix or
enumeration of a finite set is selected.

Put

$$
I=\{(n,b,\varepsilon):n\in\mathbb N, b\in B_n,
\ \varepsilon\in\{0,1\}\},\qquad E=\ell^2(I).
$$

Here square summability and its norm are defined by

$$
\|x\|_E^2=
\sup_{F\subseteq I, F\text{ finite}}
\sum_{i\in F}|x_i|^2<\infty.
$$

For every positive $c$, the threshold set
$\{i:|x_i|\geq c\}$ is finite: an infinite set has arbitrarily large
finite subsets, contradicting the norm bound.

Call $n$ active for $x$ if some $x_{n,b,\varepsilon}\ne0$.
For an active $n$, let $r(n)\in\mathbb N$ be the least nonnegative integer for which some
coordinate at that level has magnitude at least $1/(r(n)+1)$.
The set

$$
F_n(x)=\{b\in B_n:
\exists\varepsilon\in\{0,1\},
\ |x_{n,b,\varepsilon}|\geq1/(r(n)+1)\}
$$

is finite and nonempty. If infinitely many levels were active, these
canonically defined sets would give the forbidden partial multiple
choice. Hence **each vector of $E$ has finitely many active levels**.
Its support inside a single level need not be finite.

## Completeness and the supplied domain

Arbitrary-index $\ell^2(I)$ is a complex Hilbert space in ZF, including
filter completeness. To check the latter, let $\mathcal F$ be a
proper Cauchy filter. Coordinate image filters have unique complex limits
$y_i$, defining a function $y$ by unique specification. For
$\epsilon>0$, take one $A\in\mathcal F$ with diameter at most
$\epsilon$, and one $x_0\in A$. Finite-coordinate convergence
implies, for every $x\in A$ and finite $J\subseteq I$,

$$
\sum_{i\in J}|x_i-y_i|^2\leq\epsilon^2.
$$

The finite-dimensional triangle inequality with $x_0$ bounds all
finite sums of $|y_i|^2$ by $(\|x_0\|+\epsilon)^2$, so
$y\in E$. Taking the supremum in the difference bound shows
$A\subseteq\overline B(y,\epsilon)$. Repeating the argument for
arbitrarily small $\epsilon$ gives $\mathcal F\to y$. No sequence
of choices from filter members is made. Inner products are the limits of
finite partial sums; the finite-sum Cauchy–Schwarz inequality justifies
their convergence.

Define the weights and domain by

$$
w(n,b,0)=1,\qquad w(n,b,1)=n+1,
\qquad D=\{x:wx\in\ell^2(I)\},\quad \|x\|_D=\|wx\|_E.
$$

Multiplication by $w$ is an explicit isometric bijection $D\to E$,
with inverse multiplication by $1/w$. Thus $D$ is complete.
As sets of functions, $D=E$: one inclusion follows from $w\geq1$,
and the reverse inclusion follows from finite active level support.
The identity $j:D\to E$ is consequently continuous, linear,
injective, and surjective, hence dense, with $\|j\|\leq1$.

## Hamiltonian and exact spectral hypotheses

Let $S:E\to E$ swap the last two coordinates within each $(n,b)$
fiber. Then $S^2=I$ and $S^*=S$; it is an isometry. Set

$$
H(t)=S\circ j:D\to E.
$$

This is a constant, hence $C^2$, family of bounded operators. The
associated physical operator has full domain $j(D)=E$ and equals
$S$. Self-adjointness follows directly from the pairing identity:
for every $y$, the representing vector in the adjoint definition is
$Sy$, and it is unique.

For $z\ne\pm1$,

$$
(S-zI)^{-1}=\frac{S+zI}{1-z^2}.
$$

This formula maps $E=D$ to itself algebraically. Thus $H-zj$ is
bijective. At $z=\pm1$, coordinate vectors
$e_{n,b,0}\pm e_{n,b,1}$ give nonzero kernels. The algebraic spectrum
used by the hypotheses is exactly $\{-1,1\}$. Constant band endpoints
$a=0,b=2$ and gap $g=1/2$ satisfy the endpoint separation
conditions, including strict room at the boundaries.

The inverse into the supplied normed domain need not be bounded. Indeed,
its value on $e_{n,b,0}$ has coordinate-one component
$(1-z^2)^{-1}e_{n,b,1}$, with $D$-norm growing as $n+1$.
This does not violate the stated algebraic bijectivity hypothesis.

If one first takes the algebraic inverse and composes with $j$, the
physical Riesz integral around the circle with center one and radius one
is $P=(I+S)/2$, a constant orthogonal projection. If one instead uses
the repository's totalized inverse convention, returning zero when a
bounded inverse $E\to D$ is absent, the contour integrand and
projection are zero here. Both projections are constant, self-adjoint,
and idempotent. The contradiction below uses the evolution conjunct and
does not depend on identifying these two different contour formulas.

## The bounded lift cannot exist

Suppose the theorem supplied a normalized strong propagator with bounded
domain lift $L_T(t):D\to D$. Since $j$ is onto, its strong equation
and $jL_T(t)=U_T(t)j$ imply, for each $v\in E$,

$$
\frac{d}{dt}U_T(t)v=-iTSU_T(t)v,\qquad U_T(0)v=v.
$$

The solution is forced to be

$$
U_T(t)=\cos(Tt)I-i\sin(Tt)S.
$$

For uniqueness, subtract this explicit solution from a proposed orbit.
The difference $v(t)$ satisfies $v'=-iTSv$, $v(0)=0$, and
$d\|v\|^2/dt=0$ by self-adjointness of $S$. The real mean value
theorem gives $v=0$.

Choose $T=\pi/2$ and $t=1$. Then $U_T(1)=-iS$, and injectivity
of $j$ forces $L_T(1)=-iS$ on the underlying vector space. For
every fixed $n$ and $b\in B_n$,

$$
\|e_{n,b,0}\|_D=1,
\qquad
\|L_T(1)e_{n,b,0}\|_D=n+1.
$$

Given a proposed operator bound, choose an integer exceeding it, and then
use nonemptiness of that single $B_n$. This contradicts boundedness
without selecting a sequence of vectors. Consequently no required
`StrongPropagator` exists. This proves the theorem by contraposition.

The explicit physical propagator itself exists and is unitary. Every
individual orbit is smooth in the domain norm because it remains within
finitely many levels. For the physical projection $(I+S)/2$, transport
is exact and leakage is zero. The obstruction is the bounded domain lift.

## Requiring the actual initial graph norm

The constant swap uses a supplied norm stronger than its initial physical
graph norm. The following construction removes that restriction. Assume
again that $(A_k)$ has no multiple-choice family, now index levels by
$n\ge1$, and put

$$
B_n=\prod_{k<n}A_k,\qquad
I=\{(n,b,j):n\ge1,\ b\in B_n,\ j\in\{0,1,2\}\},\qquad
E=\ell^2(I;\mathbb C).
$$

The threshold and completeness proofs above apply after this reindexing.
Every vector has finitely many active levels, although its support within
a level may be infinite. A specified finite matrix on each level therefore
defines a linear map on all of $E$, even if the matrix norms are unbounded
in $n$. A uniform matrix bound gives the same operator bound on $E$;
testing one element of one nonempty $B_n$ gives each converse lower bound.
No sequence of basis vectors is selected.

Set

$$
H_n(0)=\operatorname{diag}(0,n^4,2n^4),\qquad
W_n=\operatorname{diag}(1,\sqrt{1+n^8},\sqrt{1+4n^8}).
$$

Let $D$ be the same underlying vector space with norm

$$
\|x\|_D^2=\|x\|_E^2+\|H(0)x\|_E^2=\|Wx\|_E^2.
$$

Both $W$ and $W^{-1}$ preserve the underlying space by finite active
level support. Thus $W:D\to E$ is an explicit isometric bijection,
proving that $D$ is a uniformly complete Hilbert space with exactly the
initial graph norm. The coordinate inclusion $j:D\to E$ is contractive
and onto.

### A Hamiltonian with a discontinuous physical projection

Let $R_{ij}(\alpha)$ fix the remaining coordinate and send
$e_i$ to $\cos\alpha\,e_i+\sin\alpha\,e_j$ and $e_j$ to
$-\sin\alpha\,e_i+\cos\alpha\,e_j$. Put

$$
\begin{aligned}
p(u)&=10u^3-15u^4+6u^5,\\
\lambda_n(s)&=(1-p(3s))n^4+p(3s),\\
\theta(s)&=\frac\pi2p(3s-1),\qquad \phi(s)=(3s-2)^3,
\end{aligned}
$$

using each expression on its corresponding stage, and define

$$
H_n(s)=
\begin{cases}
\operatorname{diag}(0,\lambda_n(s),2\lambda_n(s)),&0\le s\le1/3,\\
R_{01}(\theta(s))\operatorname{diag}(0,1,2)R_{01}(\theta(s))^*,
  &1/3\le s\le2/3,\\
R_{12}(n\phi(s))\operatorname{diag}(1,0,2)R_{12}(n\phi(s))^*,
  &2/3\le s\le1.
\end{cases}
$$

The matrices agree at the joins. Each acts identically on every $b$ at
its level. Since $p'(u)=30u^2(1-u)^2$, the first-stage values satisfy
$\lambda_n(s)\ge1$, with $1-p(3s)>0$ before $1/3$.

Every physical operator is everywhere defined and self-adjoint. For
each $y\in E$, finite active levels give $H(s)y\in E$; the Hermitian
matrix identity, summed using the $\ell^2$ pairing within each level,
gives $\langle H(s)x,y\rangle=\langle x,H(s)y\rangle$ for all $x$.
This explicitly represents the adjoint at every $y$. The representing
vector is unique by testing a difference against itself. No closed graph
or general Riesz theorem is used.

To check norm $C^2(D,E)$, write $F_n(s)=H_n(s)W_n^{-1}$. On the first
stage these are polynomial combinations of two bounded diagonal maps;
the respective nonzero entries are

$$
\left(\frac{n^4}{\sqrt{1+n^8}},\frac{2n^4}{\sqrt{1+4n^8}}\right),
\qquad
\left(\frac1{\sqrt{1+n^8}},\frac2{\sqrt{1+4n^8}}\right).
$$

Their norms are at most one. The second-stage rotations are independent
of $n$, so that stage is also norm smooth. On the third stage the
coordinate-zero derivative vanishes. The other inverse weights are at
most $n^{-4}$, and $|\phi'|\le9$, $|\phi''|\le54$,
$\phi'''=162$. The $k$-fold rotation commutator of the norm-one
matrix $\operatorname{diag}(-1,1)$ has norm at most $2^k$, giving

$$
\begin{aligned}
\|F_n'(s)\|&\le18/n^3,\\
\|F_n''(s)\|&\le324/n^2+108/n^3\le432,\\
\|F_n'''(s)\|&\le5832/n+5832/n^2+324/n^3\le11988.
\end{aligned}
$$

For example the third numerator is
$8(9n)^3+12(9n)(54n)+2(162n)$. Finite-dimensional Taylor estimates
therefore bound the remainders for $F_n$ and $F_n'$ by $216h^2$ and
$5994h^2$, and make $F_n''$ Lipschitz with constant $11988$.
These bounds pass to the block-operator norm, establishing norm $C^2$,
not merely coordinatewise differentiability. The first two derivatives
of $p$ vanish at its endpoints; $\phi,\phi',\phi''$ vanish at $2/3$.
Thus the jets through order two agree at the joins. Constant extension
to the left of zero and continuation of the final formula past one give
the required local $C^2$ extension.

The algebraic spectrum is the union $\Sigma_s$ of the matrix eigenvalues.
Outside that union each inverse is explicit and preserves levels, so the
inverse maps $E$ into the underlying space $D$. At an eigenvalue one
level and one of its nonempty fibers give a nonzero kernel. This also
equals the physical spectrum: before $1/3$ the positive eigenvalues
diverge to infinity, and afterwards the union is $\{0,1,2\}$.
Hence $\Sigma_s$ is closed, and away from it the Hermitian inverse bound
$\|(H_n(s)-zI)^{-1}\|\le\operatorname{dist}(z,\Sigma_s)^{-1}$ is
uniform. The band $(-1/2,1/2)$ and gap $1/2$ satisfy both the algebraic
and physical spectral hypotheses. Its contour is $|z|=1/2$.

Let $P(s)$ act on each fiber as the zero-eigenvalue projection. This is
the physical Riesz projection: on the contour the physical resolvent has
norm at most two and is Lipschitz in $z$ with constant four. The space
of bounded operators with uniformly complete codomain is uniformly
complete, by unique pointwise limits and the uniform Cauchy bound.
Canonical dyadic Riemann sums thus converge in operator norm. Coordinate
evaluation and the finite-dimensional contour calculation identify the
integral with $P(s)$.

For $s_0=2/3$ and $n\ge2$, set

$$
s_n=\frac23+\frac13\left(\frac{\pi}{2n}\right)^{1/3}.
$$

Then $s_n\to s_0$ and $n\phi(s_n)=\pi/2$. On level $n$, $P(s_0)$
selects coordinate 1 and $P(s_n)$ selects coordinate 2. Testing one
fiber proves the lower bound one; the orthogonal-projection bound gives
the upper bound. Consequently $\|P(s_n)-P(s_0)\|=1$.

### Failure of both physical adiabatic estimates

For fixed $T>0$, solve the three-dimensional equations
$U_{T,n}'=-iTH_nU_{T,n}$, $U_{T,n}(0)=I$. Picard's specified iterated
integrals and factorial remainder bound construct the solution in ZF;
energy conservation proves unitarity and uniqueness. Unique specification
assembles the solutions for all $n$. Their block action defines a
unitary physical evolution $U_T(s)$ on $E$. For a fixed vector only
finitely many levels occur, and on each level one finite matrix acts on
all fibers. The finite-dimensional estimates therefore prove the strong
equation even for infinite support within those levels. Coordinate
equations give uniqueness among physical strong evolutions.

This argument does not assert boundedness of the evolution in the
initial graph norm at every time. Any bundled propagator supplied by QAT
would nevertheless have to give this physical evolution. On the final
stage $\|H_n(s)\|\le2$, so

$$
\|U_T(s)-U_T(t)\|\le2T|s-t|,\qquad
\|Q_T(s)-Q_T(t)\|\le4T|s-t|,
\quad Q_T(s)=U_T(s)P(0)U_T(s)^*.
$$

A uniform bound $\|Q_T(s)-P(s)\|\le C/T$ would imply
$1\le2C/T+4T|s_n-s_0|$. Taking $n\to\infty$ at fixed $T$ gives
$1\le2C/T$, a contradiction for $T>2C$. The supremum error is at
least $1/2$ for every $T$.

On each three-dimensional fiber both projections have rank one, where
$\|Q-P\|=\|(I-P)Q\|$. Taking the block supremum and multiplying by
the unitary gives

$$
\|Q_T(s)-P(s)\|=\|(I-P(s))U_T(s)P(0)\|.
$$

Thus the leakage estimate fails as well. Rank one is used fiberwise;
the projections on a whole level need not have finite rank.

### The literal totalized contour and a diagonal witness

Write $\widetilde P$ for the repository's contour formula, including the
sign in [RieszProjection.lean](../../Adiabatic/Unbounded/RieszProjection.lean),
and using zero when no bounded inverse $E\to D$ exists. Before $1/3$, put
$c=1-p(3s)>0$. On $|z|=1/2$, the initial graph weights give

$$
\|W_n(H_n(s)-zI)^{-1}\|
\le\max\left(2,\frac{2\sqrt2}{c},\frac{\sqrt5}{c}\right).
$$

Indeed $\lambda_n\ge cn^4$, $\lambda_n\ge1$,
$|\lambda_n-z|\ge\lambda_n/2$, and $|2\lambda_n-z|\ge\lambda_n$.
The contour inverse is therefore bounded into $D$ and its integral,
after inclusion in $E$, is the coordinate-zero projection $P_0$.
At every $s\ge1/3$, a putative inverse bound $K$ applied to
$(H(s)-zI)e_{n,b,1}$ would give
$\sqrt{1+n^8}\le(5/2)K$ for all $n$. This is impossible. Thus

$$
\widetilde P(s)=
\begin{cases}P_0,&s<1/3,\\0,&s\ge1/3.\end{cases}
$$

Before the collapse the inverse identity gives contour continuity;
afterwards the integrand is zero. Hence all integrals in this calculation
exist. The literal projection is discontinuous and cannot satisfy QAT's
regularity conclusion.

For the literal formula, both error estimates can also fail while all
strong-propagator lifts actually exist. Omit the rotations and define

$$
\rho(s)=
\begin{cases}p(3s),&0\le s\le1/3,\\1,&1/3\le s\le1,\end{cases}
\qquad
\widehat\lambda_n(s)=(1-\rho(s))n^4+\rho(s),
\qquad
\widehat H_n(s)=\operatorname{diag}(0,\widehat\lambda_n(s),
2\widehat\lambda_n(s)).
$$

Use the same initial graph norm. The self-adjointness, gap, completeness,
and $C^2(D,E)$ checks above still apply. Extend $\rho$ by zero to the
left and one to the right. The totalized projection again jumps from
$P_0$ to zero at $1/3$.

An explicit primitive and evolution are

$$
R(s)=
\begin{cases}
\frac13\left[\frac52(3s)^4-3(3s)^5+(3s)^6\right],&0\le s\le1/3,\\
s-\frac16,&1/3\le s\le1,
\end{cases}
\qquad \Lambda_n(s)=n^4s+(1-n^4)R(s),
$$

$$
\widehat U_{T,n}(s)=\operatorname{diag}
\left(1,e^{-iT\Lambda_n(s)},e^{-2iT\Lambda_n(s)}\right).
$$

Extend $R$ by zero before zero and by $s-1/6$ after one, so these
formulas define the evolution on all real times.
The phases commute with $W_n$, so both the forward and inverse actions
are isometries on $D$ as well as on $E$. They satisfy both lift
identities. Finite active levels give continuity of every orbit in both
norms. Since $\Lambda_n'=\widehat\lambda_n$, phase differentiation
gives the strong equation, including the endpoint within-derivatives;
normalization at zero is immediate. These verify all the mathematical
fields of [StrongPropagator](../../Adiabatic/Unbounded/Propagator.lean).

For $s\ge1/3$, diagonal evolution commutes with $P_0$ and both literal
errors equal one:

$$
\|\widehat U_T(s)\widetilde P(0)\widehat U_T(s)^*
-\widetilde P(s)\|=1,
\qquad
\|(I-\widetilde P(s))\widehat U_T(s)\widetilde P(0)\|=1.
$$

The actual physical projection for this diagonal variant remains $P_0$,
and its physical errors vanish. The three-stage family, by contrast,
disproves the physical estimates. These are distinct counterexamples.

Contraposition proves that both the initial-graph-norm physical QAT and
the literal common-domain assertion imply CMC. The construction still
uses failure of later graph-norm equivalence: after the collapse,
$\|x\|_E\le(\|x\|_E^2+\|H(s)x\|_E^2)^{1/2}\le\sqrt5\|x\|_E$,
whereas the initial graph norm of $e_{n,b,1}$ is $\sqrt{1+n^8}$.
Explicit comparison of every later graph norm with the initial one,
explicit graph control, or an input requirement for bounded $E\to D$
resolvents at all contour points excludes this example. All are stronger
than the repository's algebraic pencil-bijectivity hypothesis.

## Attribution, foundations, and limits

The swap mechanism is the one in the earlier
[bounded-lift appendix](bounded-lifts.md). Blackadar–Farah–Karagila,
*Hilbert Spaces Without Countable AC*, arXiv:2304.09602v3, §8.5.4,
p. 41, already exhibit bounded Hilbert-space bijections with unbounded
inverses using levelwise diagonal weights. Proposition 3.0.4 and
Theorem 1.0.2 address the requisite strong completeness.
[Primary manuscript](https://arxiv.org/pdf/2304.09602v3)

Fellhauer, *On the relation of three theorems of analysis to the axiom
of choice*, **Journal of Logic & Analysis 9:1** (2017), Lemma 3.3.4
and Theorem 3.3.5, pp. 15–16, derives CMC from uniform boundedness
using summable-coordinate finite selections.
[Published 2017 paper](https://math.hawaii.edu/home/jla/258-968-1-PB.pdf)

CMC implies that every infinite subset of $\mathbb R$ contains a
countably infinite subset: apply CMC to the sets of $n$-element
subsets, take the finite unions, and use their canonical increasing
enumerations. Cohen's first model has an infinite Dedekind-finite set
of reals, so CMC fails there. A detailed pure-ZF construction appears in
Karagila–Schlicht, *How to have more things by forgetting how to count
them*, **Proceedings of the Royal Society A 476** (2020), 20190782,
§§2.1–3, Proposition 3.2. Hamkins–Palumbo, *The rigid relation principle,
a new weak choice principle*, **Mathematical Logic Quarterly 58**
(2012), 394–398, Theorem 6 and following remarks, explicitly uses this
model under the assumption that ZF is consistent. Thus the theorem above
gives the relative conclusion

$$
\operatorname{Con}(\mathrm{ZF})\Longrightarrow
\text{the universal bounded-lift assertion is not provable in ZF}.
$$

[Karagila–Schlicht, version 2, pp. 3–4](https://arxiv.org/pdf/1910.14480v2)
[Hamkins–Palumbo, pp. 6–7](https://arxiv.org/pdf/1106.4635)

Neither construction shows necessity of full AC, DC, or countable
choice. The [countable-choice upper bound](countable-choice.md) and the
[bounded inverse equivalence](bounded-inverses.md) leave the exact weakest
choice principle unresolved. No equivalence between CMC and the adiabatic
theorem is claimed. Explicit graph control excludes the examples above;
no necessity result for that stronger hypothesis is established here.

The full set-theoretic construction, including both initial-graph-norm
examples, is not formalized in Lean. The three-stage matrices adapt the
earlier [Dedekind-finite-real example](necessity.md). Separate
components formalize the
[finite-prefix extraction](../../Adiabatic/Foundations/PrefixMultipleChoice.lean),
[finite active level support](../../Adiabatic/Foundations/PrefixSupport.lean),
and the
[obstruction to an actual strong propagator](../../Adiabatic/Foundations/StrongSwapObstruction.lean).
Their checked statements and axiom dependencies are documented in the
[Lean audit](lean-audit.md). These components are in `Adiabatic/Foundations`;
they are not members of the repository's stricter choice-reduction audit.
A `Classical.choice` dependency is not by itself the reverse-mathematical
result proved here.
