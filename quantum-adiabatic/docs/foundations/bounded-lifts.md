# Appendix: bounded domain lifts imply bounded inverses

The bounded domain lift in the common-domain theorem forces bounded linear
bijections between Hilbert spaces to have bounded inverses. This gives a
short obstruction in ZF when an arbitrary Banach domain norm is supplied.
The [necessity theorem](necessity.md) treats the initial graph norm and both
physical adiabatic estimates.

This is a mathematical reduction, not a Lean-checked independence proof.
It concerns the universally quantified theorem in
`Adiabatic/Unbounded/Statement.lean`, including its requirement that evolution
have a bounded lift on the supplied Banach domain. It does not show that the
adiabatic estimate alone implies the full axiom of choice.

Work in classical ZF. Completeness below means uniform completeness, rather
than merely convergence of Cauchy sequences. This matches the intended
set-theoretic reading of Lean's `CompleteSpace`.

For a proper Cauchy filter, closures of its members form a reverse-inclusion
directed family with arbitrarily small diameter. Total completeness supplies their
common point, which is the filter's limit. This comparison does not select
points from a sequence of sets.

## Reduction to the bounded inverse theorem

**Proposition.** The common-domain theorem's evolution-existence conclusion
implies that every bounded linear bijection between complex Hilbert spaces
has a bounded inverse.

**Proof.** Let $S:X\to Y$ be a bounded linear bijection. Use the Hilbert direct
sums with their $\ell^2$ product norms,

$$
D=Y\oplus X,\qquad E=Y\oplus Y,
$$

and define

$$
j(y,x)=(y,Sx),\qquad B(y_1,y_2)=(y_2,y_1),\qquad H(t)=Bj.
$$

The inclusion $j:D\to E$ is bounded, injective, and surjective, hence has dense
range. Its algebraic inverse exists by uniqueness of inverse images in ZF;
its continuity is not assumed. The operator represented by $H(t)$ on the
physical space is $B$. Thus it is everywhere defined and self-adjoint, and
$H$ is constant, hence $C^2$ as a map into the bounded operators $D\to E$.

If $Y=0$, the conclusion is immediate. Otherwise $\sigma(B)=\{-1,1\}$.
For example, $(B-zI)^{-1}=(B+zI)/(1-z^2)$ for $z\ne\pm1$, and both signs
are eigenvalues. Take constant band boundaries $0$ and $2$, and gap $1$.
These satisfy the exact gap assumptions of the common-domain theorem:
its `resolventSet` is defined by bijectivity of $H-zj=(B-zI)j$.
It does not impose boundedness of the inverse in the supplied domain norm.

Apply its evolution-existence conclusion with runtime $T=\pi/2$. Let $U(t)$
be the resulting physical evolution and $L(t):D\to D$ its bounded domain
lift. Domain preservation and the strong equation give, for each $v\in E$,

$$
\frac{d}{dt}U(t)v=-iTBU(t)v,\qquad U(0)v=v.
$$

Indeed, write $v=jd$ and use $jL(t)d=U(t)jd$. This requires only one inverse
image at a time.

The unique solution is

$$
U(t)v=\bigl(\cos(Tt)I-i\sin(Tt)B\bigr)v.
$$

No infinite-dimensional existence or uniqueness theorem is needed here:
differentiate
$\bigl(\cos(Tt)I+i\sin(Tt)B\bigr)U(t)v$ and use $B^2=I$.
Its derivative is zero. Taking its inner product with any fixed vector,
and applying the scalar mean value theorem to real and imaginary parts,
shows that it is constant. Consequently $U(1)=-iB$.

For $y\in Y$, domain preservation now yields

$$
jL(1)(y,0)=U(1)(y,0)=(0,-iy).
$$

Writing $\iota_1:Y\to Y\oplus X$ and $\pi_2:Y\oplus X\to X$ for the
canonical injection and projection, it follows that

$$
S^{-1}=i\,\pi_2L(1)\iota_1.
$$

The right side is a composition of bounded maps. This proves the proposition.
Neither the spectral projection nor the error estimate was used. $\square$

The [Lean component](../../Adiabatic/ChoiceReduction/LiftObstruction.lean)
checks the algebraic extraction and the induced bound with explicit sizes.
Its unphased swap uses the rescaled lift $iL(1)$ from this proof.
The ODE argument and the set-theoretic countermodel below are not Lean-checked.

## Consequence in models without choice

Blackadar, Farah, and Karagila give a uniformly complete Hilbert-space
counterexample to the bounded inverse theorem in §8.5.4: on $\ell^2(A)$,
where $A$ is Cohen-finite but not power Dedekind-finite, a diagonal bijection
with coefficients $1/n$ has an unbounded inverse. Proposition 6.0.3 supplies
the finite-support property that makes this map surjective. Proposition 3.0.4
proves completeness of $\ell^2(A)$. Their Theorem 1.0.2 identifies uniform
and Cantor completeness. Cohen's model supplies an infinite Dedekind-finite
subset of $\mathbb R$ (§5.5.2); Propositions 5.2.8 and 5.2.5 make it
Cohen-finite and not power Dedekind-finite, respectively. Section 10 recalls
the relative consistency construction. [Hilbert Spaces Without Countable AC](https://arxiv.org/abs/2304.09602)

Combining that counterexample with the proposition gives a relative
non-provability result for the classical set-theoretic reading of the
packaged common-domain theorem: if ZF is consistent, this universally
quantified statement is not a theorem of ZF. The obstruction is its bounded
lift requirement for an arbitrary supplied domain norm. Even the constant,
bounded physical Hamiltonian above is sufficient. The standard formulation
with the graph norm supplied as part of the hypotheses evades this
counterexample: the inclusion used here would not satisfy that requirement
when $S^{-1}$ is unbounded.

This does not contradict the checked Lean theorem, whose environment admits
`Classical.choice`. It also does not prove that full AC, dependent choice,
or countable choice is the weakest sufficient principle. No reduction from
arbitrary choice problems to this theorem has been established here.

## Limits of other necessity arguments

Orthogonal projections and Riesz representation for uniformly complete
Hilbert spaces hold in ZF; the cited paper proves this in §2. Counterexamples
using only sequential completeness do not establish a failure under the
repository's completeness hypothesis.

Likewise, the current proof's use of maximal ideals does not prove that
functional calculus requires AC. Blackadar and Farah establish continuous
functional calculus without choice, including the normal-element case in
Proposition 6.1.4. [Separable C*-algebras Without the Countable Axiom of
Choice](https://arxiv.org/abs/2602.15812)

The separate [dependent-choice proof](dependent-choice.md) supplies a weaker
sufficient foundation than full AC. Whether dependent choice or countable
choice is necessary is not settled by this obstruction.
