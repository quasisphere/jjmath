# The measurable Riemann mapping theorem

Let $\mu:\mathbb C\to\mathbb C$ be measurable with
$|\mu|\le k<1$ almost everywhere. The compact-support construction first
produces an orientation-preserving principal plane homeomorphism. Its unique
complex-affine target normalization is

$$
  N_F(z)=\frac{F(z)-F(0)}{F(1)-F(0)}.
$$

This postcomposition fixes $0$ and $1$ without changing the Beltrami
coefficient or the distortion constant.

@include{lean:JJMath.Quasiconformal.exists_normalizedPrincipalHomeomorphismExtension_of_compactSupport}

Every normalized plane homeomorphism extends canonically over the point at
infinity. Its finite chart is exactly the original plane map.

@include{lean:JJMath.Quasiconformal.riemannSphereFiniteChartHomeomorph_planeHomeomorphExtension}

The reciprocal chart reduces to inversion before and after the plane map.
Away from the origin, the existing conformal-change laws preserve
$K$-quasiconformality. At the origin, the required extension is an
isolated-point removability statement: the distortion inequality and area
formula give finite energy, and shrinking smooth cutoffs remove the point from
the weak derivative identity.

@include{lean:JJMath.Quasiconformal.IsKQuasiconformalBetween.exists_isLocalW12On_univ_of_punctured_continuous}

The principal affine asymptotic becomes a nonzero complex tangent in the
reciprocal chart. Comparing a sufficiently small image circle with its
complex-linear tangent circle fills the orientation witness at the omitted
point.

@include{lean:JJMath.Quasiconformal.preservesPlanarOrientation_wholePlaneSubtype_of_punctured_of_tendsto_div}

@include{lean:JJMath.Quasiconformal.isKQuasiconformalRiemannSphere_planeHomeomorphExtension}

For a Beltrami differential on the sphere, write
$\mu_{\mathrm{fin}}$ and $\mu_\infty$ for its finite and reciprocal
coordinate representatives. Truncate the finite representative to

$$
  \mu_n=\mathbf 1_{B(0,n)}\mu_{\mathrm{fin}}.
$$

The normalized compact-support solutions all have the same constant
$K=(1+k)/(1-k)$. The coefficients $\mu_n$ converge pointwise to
$\mu_{\mathrm{fin}}$. Promote each truncation to a Beltrami differential on
the sphere. Affine convergence is equivalent to chartwise almost-everywhere
convergence, so normalized spherical compactness produces a subsequential
limit fixing $0,1,\infty$. It is
$K$-quasiconformal and realizes the original differential on the whole
sphere.

@include{lean:JJMath.BeltramiDifferential}

@include{lean:JJMath.Quasiconformal.normalizedRiemannSphere_beltramiDifferential_compactness}

@include{lean:JJMath.BeltramiDifferential.isBeltramiDifferentialOf_of_finite}


@include{lean:JJMath.Quasiconformal.exists_normalized_riemannSphere_homeomorph_of_beltrami}

The construction is fully assembled. On the proper principal-solution route,
the condenser argument gives lightness, the protected weighted-Jacobian
measure gives openness, protected multiplicity makes every fiber finite, and
local target coverage gives positive local index. Degree one then forces
bijectivity. The analytic and topological isolated-point arguments used by
the spherical extension are also proved.

@include{lean:JJMath.Quasiconformal.open_discrete_and_localIndex_pos_of_boundedDistortion_of_isProperMap}

Because the normalized sphere solution fixes infinity, its finite chart is
also a normalized quasiconformal homeomorphism of the whole plane. The
area-and-inverse theory additionally makes its weak Jacobian positive almost
everywhere. This is the form of the measurable Riemann mapping theorem used
to straighten the coefficient of a nonproper quasiregular map.

@include{lean:JJMath.Quasiconformal.exists_normalized_plane_homeomorph_of_beltrami}

Combining this plane solution with the inverse Sobolev chain rule and the
weak Cauchy--Riemann theorem yields Stoilow factorization and hence the
whole-plane open-and-discrete theorem.
