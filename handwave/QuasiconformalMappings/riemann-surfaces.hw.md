# Quasiregular Maps Between Riemann Surfaces

The planar bounded-distortion condition extends to Riemann surfaces by
passing to complex coordinates. For a map $f:X\to Y$, a source chart
$\phi_x$ and a target chart $\psi_y$ give the coordinate map

$$
  f_{x,y}(z)=\psi_y\bigl(f(\phi_x^{-1}(z))\bigr)
$$

on the maximal set where all three evaluations are valid:

$$
  U_{x,y}(f)=
  \{z\in\phi_x(X):f(\phi_x^{-1}(z))\in\operatorname{source}(\psi_y)\}.
$$

@include{lean:JJMath.Quasiconformal.riemannSurfaceChartMapSource}

@include{lean:JJMath.Quasiconformal.riemannSurfaceChartMap}

A map has chartwise $K$-bounded distortion when every such coordinate map
belongs locally to $W^{1,2}$ and satisfies

$$
  \lVert Df_{x,y}(z)\rVert_{\mathrm{op}}^2
    \le K\,\operatorname{Jac}f_{x,y}(z)
$$

almost everywhere on $U_{x,y}(f)$. A $K$-quasiregular map is additionally
continuous and strictly nonconstant.



For a homeomorphism $F:X\to Y$, the same coordinate expression is naturally
an open partial homeomorphism

$$
  \psi_y\circ F\circ\phi_x^{-1}.
$$

Its source is exactly $U_{x,y}(F)$, and its ambient representative agrees
there with the coordinate map above.

@include{lean:JJMath.Quasiconformal.riemannSurfaceChartRepresentation}

@include{lean:JJMath.Quasiconformal.riemannSurfaceChartRepresentation_source}


A homeomorphism is $K$-quasiconformal when $K\ge1$ and each coordinate
homeomorphism is planar $K$-quasiconformal.
This packages both the weak distortion inequality and orientation
preservation without choosing a distinguished global chart.

@include{lean:JJMath.Quasiconformal.IsKQuasiconformalBetweenRiemannSurfaces}

On a nontrivial range, a quasiconformal surface homeomorphism is
quasiregular. Inversion is intrinsic: exchanging the source and target
charts identifies every coordinate representation of $F^{-1}$ with the
inverse of the corresponding representation of $F$.




For the complex plane, all surface charts are the identity chart. Thus the
intrinsic condition is exactly the existing planar condition on the
universal domains.


For the Riemann sphere, the chart at a finite point is the affine chart and
the chart at infinity is the reciprocal chart. Consequently the intrinsic
condition is equivalent to checking the four pairs of these two standard
charts.


A scalar coefficient is not a coordinate-independent differential. For two
complex charts $z_i,z_j$, let $a_{ij}$ be the derivative of the coordinate
change from $z_i$ to $z_j$. The line bundle of $(p,q)$-differentials has
transition scalar

$$
  a_{ij}^{-p}\overline{a_{ij}}^{-q}.
$$

A $(p,q)$-differential is a section of this line bundle. This one
construction gives Beltrami differentials as the $(-1,1)$ case and quadratic
differentials as the $(2,0)$ case.

@include{lean:JJMath.PQDifferential}

@include{lean:JJMath.BeltramiDifferential}


Measurability and the essential norm of a Beltrami differential are imposed
on its scalar representative in every complex chart. The transition factor
has modulus one, so this is the coordinate-independent version of the usual
$L^\infty$ condition.

@include{lean:JJMath.BeltramiDifferential.IsAEStronglyMeasurable}

Almost-everywhere convergence of Beltrami differentials is likewise
chartwise: the scalar representatives converge almost everywhere in every
complex coordinate.

@include{lean:JJMath.BeltramiDifferential.AETendsto}

@include{lean:JJMath.BeltramiDifferential.HasEssentialNormLE}

On the Riemann sphere, write $\mu_{\mathrm{fin}}$ and $\mu_\infty$ for the
representatives of an intrinsic Beltrami differential in the affine and
reciprocal charts. The bundle transition law proves, rather than assumes,
that away from the reciprocal origin

$$
  \mu_\infty(w)
    =\mu_{\mathrm{fin}}(w^{-1})
      \frac{\overline{-w^{-2}}}{-w^{-2}}.
$$

The exceptional point is null, so the identity also holds almost everywhere.
Consequently, measurability and the essential norm on the whole sphere can be
checked in the affine chart alone. A planar coefficient can conversely be
promoted to an intrinsic spherical differential; its reciprocal coefficient
is exactly the inversion pullback.

@include{lean:JJMath.BeltramiDifferential.infinityCoefficient_eq_inversionPullback_of_ne_zero}

@include{lean:JJMath.BeltramiDifferential.isAEStronglyMeasurable_iff_finite}

@include{lean:JJMath.BeltramiDifferential.aeTendsto_iff_finite}

@include{lean:JJMath.BeltramiDifferential.hasEssentialNormLE_iff_finite}

@include{lean:JJMath.BeltramiDifferential.ofFinite}


A surface homeomorphism realizes a Beltrami differential when its
point-selected coordinate representative belongs locally to $W^{1,2}$ and
satisfies the weak Beltrami equation with the corresponding local
coefficient. For a normalized sphere homeomorphism, a finite-coordinate
equation automatically supplies this intrinsic realization: inversion gives
the equation at infinity, while all finite points use the common affine
chart.

@include{lean:JJMath.BeltramiDifferential.IsBeltramiDifferentialOf}

Intrinsic realization by a normalized sphere map can also be read back in
the affine chart: evaluating at $0$ supplies a whole-plane weak differential
and the equation with coefficient $\mu_{\mathrm{fin}}$.

@include{lean:JJMath.BeltramiDifferential.IsBeltramiDifferentialOf.exists_finite_weakDifferential}

@include{lean:JJMath.BeltramiDifferential.isBeltramiDifferentialOf_of_finite}

Normalized compactness can therefore be stated entirely with spherical
Beltrami differentials. Chartwise almost-everywhere convergence and a common
essential bound produce a normalized limit which realizes the limiting
differential and is quasiconformal.

@include{lean:JJMath.Quasiconformal.normalizedRiemannSphere_beltramiDifferential_compactness}

The spherical measurable Riemann mapping theorem applies this result to the
spherical differentials induced by finite-coordinate truncations. If the
original differential has essential norm at most $k<1$, the resulting
normalized homeomorphism realizes it and is
$\frac{1+k}{1-k}$-quasiconformal.

@include{lean:JJMath.Quasiconformal.exists_normalized_riemannSphere_homeomorph_of_beltrami}
