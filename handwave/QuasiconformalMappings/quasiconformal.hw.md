# Quasiconformal Mappings

The planar library separates the almost-everywhere analytic condition from
the pointwise topological notions. A map has $K$-bounded distortion when it
belongs locally to $W^{1,2}$ and has a weak differential satisfying

$$
  \lVert Df(z)\rVert_{\mathrm{op}}^2
    \leq K\,\operatorname{Jac}f(z)
$$

almost everywhere. This condition is unchanged if the map or its weak
differential is replaced almost everywhere.

@include{lean:JJMath.Quasiconformal.HasKBoundedDistortionOn}

@include{lean:JJMath.Quasiconformal.HasKBoundedDistortionOn.distortion_of_weakDifferential}



A $K$-quasiregular map is a continuous, strictly nonconstant representative
with $K\geq1$ and $K$-bounded distortion. Requiring continuity here makes
ordinary pointwise nonconstancy appropriate and gives fibers and open-map
statements their intended literal meaning.



A homeomorphism between open planar domains is $K$-quasiconformal when it
preserves orientation and has $K$-bounded distortion. The orientation
condition is topological:
around every point there must be a positive-radius closed disk contained in
the domain whose positively oriented boundary is homotopic, after translation
and base-point normalization, to the positive unit circle in the punctured
plane.

@include{lean:JJMath.Quasiconformal.PreservesPlanarOrientation}

The normalized boundary class is unchanged when its positive radius varies
through circles contained in the domain. Orientation preservation is also
closed under composition: the first boundary can be shrunk into the second
orientation disk, its positive homotopy transported there, and the resulting
loop rotated and rescaled to the second positive boundary.

@include{lean:JJMath.Quasiconformal.normalizedBoundaryLoop_radius_homotopic}

@include{lean:JJMath.Quasiconformal.PreservesPlanarOrientation.trans}

For a homeomorphism between planar domains, bounded distortion is exposed as
a predicate on the homeomorphism itself. Its analytic content is still
computed from the associated complex-valued map on the source domain.

@include{lean:JJMath.Quasiconformal.HasKBoundedDistortionBetween}

The complete geometric predicate is local under restriction to open source
and target subdomains. Bounded distortion localizes to the source subdomain,
while orientation is inherited after shrinking each witness disk into it.

@include{lean:JJMath.Quasiconformal.IsKQuasiconformalBetween.restrict}

@include{lean:JJMath.Quasiconformal.IsLocalW12On}

@include{lean:JJMath.Quasiconformal.IsKQuasiconformalBetween}

On a nontrivial source, every quasiconformal homeomorphism is quasiregular.


## Real-linear distortion

For a real-linear map $L:\mathbb C\to\mathbb C$, write

$$
  L(\xi)=L_z\xi+L_{\bar z}\overline\xi.
$$

The operator norm and real Jacobian are

$$
  \lVert L\rVert_{\mathrm{op}}=|L_z|+|L_{\bar z}|,
  \qquad
  \det_{\mathbb R}L=|L_z|^2-|L_{\bar z}|^2.
$$

These identities give the exact conversion between the Beltrami ratio and
metric distortion:

$$
  |L_{\bar z}|\leq k|L_z|
  \quad\Longleftrightarrow\quad
  \lVert L\rVert_{\mathrm{op}}^2
    \leq \frac{1+k}{1-k}\det_{\mathbb R}L,
  \qquad 0\leq k<1.
$$

@include{lean:JJMath.Quasiconformal.apply_eq_weakDZ_mul_add_weakDBar_mul_conj}

@include{lean:JJMath.Quasiconformal.weakJacobian_eq_norm_weakDZ_sq_sub_norm_weakDBar_sq}

@include{lean:JJMath.Quasiconformal.norm_eq_norm_weakDZ_add_norm_weakDBar}

@include{lean:JJMath.Quasiconformal.norm_weakDBar_le_iff_norm_sq_le_distortion}

The affine family $z\mapsto az+b\overline z+c$ fixes all conventions: its weak
$z$ and $\bar z$ components are $a$ and $b$, its Jacobian is
$|a|^2-|b|^2$, and its operator norm is $|a|+|b|$.

@include{lean:JJMath.Quasiconformal.hasFDerivAt_affineMap}

Composition of two real-linear maps and the inverse of a positive-Jacobian
real-linear map also have explicit Wirtinger formulas. In particular,
complex-linear pre- and postcomposition scale both squared operator norm and
Jacobian by the same factor.

@include{lean:JJMath.Quasiconformal.realLinearMapOfWirtinger_comp}

@include{lean:JJMath.Quasiconformal.realLinearEquivOfWirtinger_symm_apply}

Positive-Jacobian inversion also preserves the quantitative distortion
constant. If $L$ satisfies
$\lVert L\rVert_{\mathrm{op}}^2\leq K\det_{\mathbb R}L$, then

$$
  \lVert L^{-1}\rVert_{\mathrm{op}}^2
    \leq K\det_{\mathbb R}(L^{-1}).
$$

@include{lean:JJMath.Quasiconformal.distortion_inverse_of_pos_weakJacobian}

For measure-theoretic inversion it is convenient to totalize this formula.
The Wirtinger pseudoinverse agrees with $L^{-1}$ when the Jacobian is positive
and is the zero map when the Jacobian vanishes. It is measurable as a function
of $L$, its Jacobian is reciprocal at positive Jacobian, and it obeys both the
inverse distortion inequality and the weighted estimate

$$
  \|L^\dagger\|_{\mathrm{op}}^2 J(L)\leq K.
$$

@include{lean:JJMath.Quasiconformal.realLinearPseudoInverse_eq_symm_toContinuousLinearMap}

@include{lean:JJMath.Quasiconformal.weakJacobian_realLinearPseudoInverse_mul}

The planar adjugate packages the numerator of the inverse formula. It has the
same operator norm as $L$, satisfies
$\operatorname{adj}(L)L=L\operatorname{adj}(L)=J(L)\operatorname{id}$,
and under the finite-distortion inequality satisfies
$\operatorname{adj}(L)=J(L)L^\dagger$ even on the zero-Jacobian branch.

@include{lean:JJMath.Quasiconformal.norm_realLinearAdjugate}

@include{lean:JJMath.Quasiconformal.realLinearAdjugate_eq_weakJacobian_smul_realLinearPseudoInverse_of_nonneg}

@include{lean:JJMath.Quasiconformal.realLinearPseudoInverse_eq_zero_of_weakJacobian_eq_zero}

@include{lean:JJMath.Quasiconformal.distortion_realLinearPseudoInverse_of_nonneg_weakJacobian}

@include{lean:JJMath.Quasiconformal.norm_sq_realLinearPseudoInverse_mul_weakJacobian_le_of_nonneg}

Consequently, the metric distortion inequality is unchanged by conformal
linear changes in either the source or target.

@include{lean:JJMath.Quasiconformal.distortion_comp_complexLinear}

@include{lean:JJMath.Quasiconformal.distortion_complexLinear_comp}

## Local Sobolev and Beltrami interfaces

Local Sobolev membership uses the existing distributional weak derivative and
requires square-integrability of the map and differential on every compact
subset. Weak differentials are unique almost everywhere, so the geometric
distortion inequality does not depend on its witness.

@include{lean:JJMath.Quasiconformal.IsLocalW12On.weakDifferential_ae_eq}

@include{lean:JJMath.Quasiconformal.isLocalW12On_affineMap}

Continuous real-linear postcomposition and locally bi-Lipschitz
precomposition preserve the local Sobolev class. For a coordinate change
$T:U\to\Omega$, the pulled-back weak differential is

$$
  D(f\circ T)(z)=Df(T(z))\circ DT(z).
$$

@include{lean:JJMath.Quasiconformal.IsLocalW12On.postcomp_realAffine}

@include{lean:JJMath.Quasiconformal.IsLocalW12On.comp_locallyBiLipschitz}

The first non-affine chart-change test is complex inversion on
$\mathbb C^\times$. It preserves null sets, is locally Lipschitz away from the
origin, and therefore preserves local Sobolev regularity. Writing
$\iota(z)=z^{-1}$, its differential is multiplication by $-z^{-2}$, so

$$
  \partial_z(f\circ\iota)(z)
    =(\partial_z f)(z^{-1})(-z^{-2}),
  \qquad
  \partial_{\bar z}(f\circ\iota)(z)
    =(\partial_{\bar z}f)(z^{-1})\overline{-z^{-2}}.
$$

@include{lean:JJMath.Quasiconformal.inversion_quasiMeasurePreserving}

@include{lean:JJMath.Quasiconformal.IsLocalW12On.comp_inversion}



More generally, suppose a conformal source-coordinate change $T$ has nonzero
complex derivative $a$. The Beltrami coefficient transforms by the
unit-modulus phase factor

$$
  \widetilde\mu(z)
    =\mu(T(z))\frac{\overline{a(z)}}{a(z)}.
$$

Thus its pointwise norm and essential bound are unchanged. The same
coordinate change preserves the metric distortion inequality, since both the
squared operator norm and Jacobian acquire the factor $|a(z)|^2$.

@include{lean:JJMath.Quasiconformal.WeakBeltramiEquationOn.comp_conformal}


@include{lean:JJMath.Quasiconformal.metricDistortion_comp_conformal}

For the reciprocal sphere-chart transition this becomes

$$
  \widetilde\mu(z)=\mu(z^{-1})
    \frac{\overline{-z^{-2}}}{-z^{-2}}.
$$

The weak Beltrami equation, its essential coefficient bound, and the metric
distortion inequality all pass through inversion on $\mathbb C^\times$.

@include{lean:JJMath.Quasiconformal.WeakBeltramiEquationOn.comp_inversion}


@include{lean:JJMath.Quasiconformal.metricDistortion_comp_inversion}

For a projective Möbius representative $A=(a_{ij})$, its finite-chart formula

$$
  T_A(z)=\frac{a_{00}z+a_{01}}{a_{10}z+a_{11}}
$$

is used on the punctured domain
$U_A=\{z:a_{10}z+a_{11}\ne0\}$. It is a locally bi-Lipschitz equivalence from
$U_A$ to $U_{A^{-1}}$, and its complex derivative is

$$
  T_A'(z)=\frac{\det A}{(a_{10}z+a_{11})^2}.
$$

The totalized finite formula still preserves null sets: the only discrepancy
from the finite-chart homeomorphism occurs at its pole, which is a null
singleton. Consequently the local Sobolev, Beltrami, essential-bound, and
metric-distortion coordinate-change laws apply to every projective Möbius
representative.

@include{lean:JJMath.Quasiconformal.fderiv_mobiusFiniteFormula}

@include{lean:JJMath.Quasiconformal.mobiusFiniteFormula_quasiMeasurePreserving}

@include{lean:JJMath.Quasiconformal.IsLocalW12On.comp_mobiusFiniteFormula}

The pole-free formula itself is an orientation-preserving homeomorphism
$T_A:U_A\to U_{A^{-1}}$. Its classical differential is complex linear, so its
operator norm squared is exactly its real Jacobian. It is therefore
$1$-quasiconformal.

@include{lean:JJMath.Quasiconformal.preservesPlanarOrientation_mobiusFiniteHomeomorph}

@include{lean:JJMath.Quasiconformal.isOneQuasiconformalBetween_mobiusFiniteHomeomorph}




## Sobolev change of variables and inversion

The analytic route from coordinate ACL to Lusin $N$, approximate
differentiability, the Sobolev area formula, and quasiconformality of the
inverse is developed separately in
[Sobolev Change of Variables for Planar Quasiconformal Maps](Quasiconformal/sobolev-area-inverse.hw.md).
The key conclusion is that the weak differential supports the full oriented
area formula, and the total Wirtinger pseudoinverse is the weak differential
of the inverse homeomorphism.  This yields both inverse quasiconformality and
Lusin $N^{-1}$ without assuming ambient Fréchet differentiability almost
everywhere.

## Condenser capacity

The capacity route to normalized compactness is developed in
[Condenser Capacity and Quasiconformal Pullback](Quasiconformal/capacity.hw.md).
Planar condenser capacity and the quasiconformal energy pullback inequality
are defined there.  Bounded scalar retractions and local smooth approximation
give the weak chain rule for continuous local Sobolev outer functions.
Consequently continuous condenser competitors pull back with controlled
energy, and applying this to the map and its quasiconformal inverse proves
the full two-sided $K$-distortion theorem for planar condenser capacity.  The
model-geometry layer proves complex-affine invariance and reduces concentric
ring capacity to a function of the radius ratio. The logarithmic radial
competitor is now admissible and has exact energy
$2\pi/(\log R-\log r)$, proving the corresponding ring-capacity upper bound.
The active remaining layer is the matching lower bound and spherical
separation theory needed for normalized equicontinuity.

## Riemann-sphere interface

A sphere homeomorphism is $K$-quasiconformal when each of its planar
representations in the finite and reciprocal standard charts satisfies the
geometric planar definition with the same $K$. The open-partial-homeomorphism
calculus automatically selects the planar source and target domains where a
given chart pair is valid.

@include{lean:JJMath.Quasiconformal.IsKQuasiconformalRiemannSphere}

For the projective action of $A$, the finite-to-finite chart representation
has source $U_A$, target $U_{A^{-1}}$, and is exactly $T_A$.




Let

$$
  J=\begin{pmatrix}0&1\\1&0\end{pmatrix}.
$$

Its projective action is spherical inversion. Consequently, changing the
source chart from finite to reciprocal replaces $A$ by $AJ$, changing the
target chart replaces it by $JA$, and changing both replaces it by $JAJ$.
Thus all four standard chart representations reduce to pole-free finite
Möbius homeomorphisms.



@include{lean:JJMath.Quasiconformal.IsKQuasiconformalBetween.distortion_of_weakDifferential}

The Beltrami equation is kept as an interface rather than placed in the
definition. If

$$
  \partial_{\bar z}f=\mu\,\partial_z f,
  \qquad |\mu|\leq k<1,
$$

then the geometric distortion inequality holds with
$K=(1+k)/(1-k)$.

@include{lean:JJMath.Quasiconformal.WeakBeltramiEquationOn}

@include{lean:JJMath.Quasiconformal.isKQuasiconformalBetween_of_weakBeltrami}

As an end-to-end check, every nonconstant complex-affine map of the plane is
$1$-quasiconformal: its normalized local boundary loop is positive, its weak
differential is complex linear, and its operator norm squared equals its
Jacobian.

@include{lean:JJMath.Quasiconformal.isOneQuasiconformalBetween_complexAffine}

## Riemann surfaces

The planar hierarchy has a chartwise counterpart for maps between
Riemann surfaces. It includes bounded-distortion and quasiregular maps,
quasiconformal homeomorphisms, inversion, and compatibility with both the
whole plane and the two standard charts of the Riemann sphere. The
construction and its role in the spherical existence theorem are developed
in [Quasiregular Maps Between Riemann Surfaces](Quasiconformal/riemann-surfaces.hw.md).

## Existence theory

The analytic principal-solution construction, including the near-$2$
Beurling resolvent, rough Cauchy transform, weak derivatives, distortion
bound, and normalization at infinity, is developed in
[Principal Solutions of the Beltrami Equation](Quasiconformal/principal-solutions.hw.md).
The integer winding-number and local-degree layer used for global inversion
is developed in
[Planar Winding Numbers and Local Indices](Quasiconformal/planar-degree.hw.md).

The compact-support solution is now affinely normalized, extended over
infinity, and passed through varying-differential compactness on
the sphere. The resulting endpoint is the measurable Riemann mapping theorem:
for every measurable Beltrami differential on the Riemann sphere with
essential norm below one, there is a normalized quasiconformal sphere
homeomorphism fixing $0,1,\infty$ and realizing the differential in both the
finite and reciprocal coordinates. This final assembly is recorded in
[The Measurable Riemann Mapping Theorem](Quasiconformal/measurable-riemann-mapping.hw.md).

@include{lean:JJMath.Quasiconformal.normalizedRiemannSphere_beltramiDifferential_compactness}

The planar theorem needed by this assembly is now proved rather than hidden
behind assumptions. Local higher integrability gives the Lusin property and
the multiplicity area formula. A protected weighted-Jacobian measure proves
openness for light maps. Properness then combines this openness with finite
protected multiplicity to make every fiber finite, while local target
coverage makes every isolated local index strictly positive. The normalized
degree-one principal solution is consequently an orientation-preserving
homeomorphism.

@include{lean:JJMath.Quasiconformal.IsLocalW12On.boundedDistortion_derivative_memLpOn_compact_nearTwo}

@include{lean:JJMath.Quasiconformal.open_discrete_and_localIndex_pos_of_boundedDistortion_of_isProperMap}

The broader nonproper whole-plane theorem is now proved by analytic Stoilow
factorization. Solve the measurable coefficient of a bounded-distortion map
by the normalized sphere theorem, pass to its whole-plane finite chart, and
compose with the quasiconformal inverse. Equal coefficients cancel in the
weak differential, so the remaining factor is entire. The holomorphic
open-mapping and isolated-zero theorems then give openness and discrete
fibers, and the existing multiplicity argument gives positive local index.

@include{lean:JJMath.Quasiconformal.exists_stoilow_factorization_of_boundedDistortion}


The public whole-plane consequences are also available directly from the
quasiregular predicate.



Only the all-purpose topological Whyburn--Stoilow statement remains an
optional explicit leaf; neither analytic route uses it.
