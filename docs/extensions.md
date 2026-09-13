# Possible extensions

The full common-domain theorem proves uniform projection-distance and
leakage bounds with an existential constant. The original finite-dimensional
theorem also obtains its constant by constructing a commutator solution and
bounding it on the compact time interval. Their proved arguments are in
the [proof guide](proof-guide.md); their exact scope is in
[Verification and scope](verification.md).

The calculations below are informal proposals for explicit constants in
the finite-dimensional setting. They are not Lean declarations and are not
inputs to either main theorem. In particular, physical operator-norm bounds
on $H'$ below do not follow merely from the common-domain hypotheses for an
unbounded Hamiltonian.

## General spectral cluster estimate

The finite-dimensional proof constructs an off-diagonal solution of
$[H,X]=K$, where $K=[P',P]$, using an inverse on the fixed operator space
$B(E)$. The spectral gap makes this inverse well-defined; compactness gives
runtime-independent bounds on $X$ and $X'$.

Informally, eigenbasis coordinates give

$$
\|X\|_{\mathrm{HS}}\le\|K\|_{\mathrm{HS}}/g
$$

in the Hilbert–Schmidt norm. Conversion to the operator norm introduces
dimension factors. This estimate is not formalized here. The proof does not
assume an operator-norm estimate $\|X\|\le\|K\|/g$ for arbitrary separated
spectral sets.

## Reduced-resolvent estimates

For one isolated eigenvalue, possibly degenerate, suppose $HP=eP$ for a
real $C^2$ function $e$, and the complementary spectrum is at distance at
least $g>0$ from $e$. Write $Q=I-P$ and

$$
A=H-eI+P,\qquad R=A^{-1}-P.
$$

Given the augmented inverse, the existing
[reduced-resolvent algebra](proof-guide.md#reduced-resolvent-algebra) proves
$RP=PR=0$, $(H-eI)R=R(H-eI)=Q$, and that

$$
X=RP'P+PP'R
$$

solves $[H,X]=[P',P]$. That algebraic special case is separate from the
general-cluster construction used by the original finite-dimensional
main theorem.

The proposed analytic extension would prove the spectral bound
$\|R\|\le1/g$. Put $r=1/g$ and assume uniform bounds
$\|P'\|\le p_1$, $\|P''\|\le p_2$, $\|H'\|\le h_1$, and $|e'|\le e_1$.
Differentiating the reduced-resolvent identities formally gives

$$
R'=-R(H'-e'I)R-RP'-P'R.
$$

The product rule and norm inequalities then give the nonoptimal candidate
bounds $\|X\|\le M_X$, $\|K\|\le M_K$, and $\|X'\|\le M_D$, with

$$
M_X=2rp_1,\qquad M_K=2p_1,
$$

$$
M_D=2r^2(h_1+e_1)p_1+6rp_1^2+2rp_2.
$$

Substitution into the proved comparison estimate
$\|U_T(s)-V_T(s)\|\le(2M_X+M_D+M_KM_X)/T$ would give the candidate constant

$$
C=4rp_1+2rp_2+10rp_1^2+2r^2(h_1+e_1)p_1.
$$

The reduced-resolvent derivative formula, the spectral norm bound, and
these explicit constants remain to be formalized. Jansen–Ruskai–Seiler,
Theorem 3, gives sharper derivative and gap dependence under its stated
assumptions. [Primary source, Section II](https://arxiv.org/pdf/quant-ph/0603175).

## Other mathematical directions

Formal probability and asymptotic-limit corollaries can build on the
operator leakage estimates. Changing operator domains, gapless evolution,
switching improvements, and exponentially small errors require additional
arguments and appropriately different hypotheses. These are separate
mathematical targets from the full common-domain theorem proved here.

Return to the [documentation index](README.md).
