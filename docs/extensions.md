# Possible extensions

The common-domain and finite-dimensional theorems prove bounds with
existential constants; see the [proof guide](proof-guide.md) and
[verification record](verification.md).

The calculations below propose explicit constants in finite dimension.
They are informal and are not inputs to either main theorem. Physical
operator-norm bounds on $H'$ do not follow from the common-domain
hypotheses for an unbounded Hamiltonian.

## General spectral cluster estimate

The finite-dimensional proof constructs an off-diagonal solution of
$[H,X]=K$, where $K=[P',P]$, using an inverse on the fixed operator space
$B(E)$. The spectral gap makes this inverse well-defined; compactness gives
runtime-independent bounds on $X$ and $X'$.

In eigenbasis coordinates,

$$
\|X\|_{\mathrm{HS}}\le\|K\|_{\mathrm{HS}}/g
$$

in the Hilbert–Schmidt norm. Conversion to the operator norm introduces
dimension factors. The proof does not assume the operator-norm estimate
$\|X\|\le\|K\|/g$ for arbitrary separated spectral sets.

## Reduced-resolvent estimates

For one isolated eigenvalue, possibly degenerate, suppose $HP=eP$ for a
real $C^2$ function $e$, and the complementary spectrum is at distance at
least $g>0$ from $e$. Write $Q=I-P$ and

$$
A=H-eI+P,\qquad R=A^{-1}-P.
$$

Given the augmented inverse, the
[reduced-resolvent algebra](proof-guide.md#reduced-resolvent-algebra) proves
$RP=PR=0$, $(H-eI)R=R(H-eI)=Q$, and that

$$
X=RP'P+PP'R
$$

solves $[H,X]=[P',P]$. This special case is separate from the
general-cluster construction in the finite-dimensional theorem.

The analytic extension would prove
$\|R\|\le1/g$. Put $r=1/g$ and assume uniform bounds
$\|P'\|\le p_1$, $\|P''\|\le p_2$, $\|H'\|\le h_1$, and $|e'|\le e_1$.
Differentiating the reduced-resolvent identities formally gives

$$
R'=-R(H'-e'I)R-RP'-P'R.
$$

The product rule and norm inequalities give nonoptimal bounds
$\|X\|\le M_X$, $\|K\|\le M_K$, and $\|X'\|\le M_D$, with

$$
M_X=2rp_1,\qquad M_K=2p_1,
$$

$$
M_D=2r^2(h_1+e_1)p_1+6rp_1^2+2rp_2.
$$

Substitution into the proved comparison estimate
$\|U_T(s)-V_T(s)\|\le(2M_X+M_D+M_KM_X)/T$ would give

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
switching improvements, and exponentially small errors require different
hypotheses and additional arguments.

Return to the [documentation index](README.md).
