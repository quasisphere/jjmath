# Grönwall's Area Theorem and Koebe's One-Quarter Theorem

Let
\[
  G(z)=z+\frac{b}{z}+h\!\left(\frac1z\right)
\]
be analytic and injective outside the closed unit disk, where the constant and
linear terms of (h) vanish.  Grönwall's area theorem gives

\[
  |b|\leq 1.
\]

@include{lean:JJMath.ComplexAnalysis.gronwall_area_first_coefficient}

## The Area Estimate

On the circle of radius (s>1), differentiate (G(se^{it})) and divide by
the unit tangent.  The resulting periodic function has constant Fourier
coefficient (1) and second Fourier coefficient (-b/s^2).  Bessel's
inequality therefore gives the sharp lower bound

\[
  \int_{-\pi}^{\pi}|G'(se^{it})|^2\,dt
  \geq 2\pi\left(1+\frac{|b|^2}{s^4}\right).
\]

Integrating radially bounds from below the area of the image of an annulus.
For the opposite inequality, the omitted region is contained in the convex
hull of the outer boundary curve.  The boundary curve differs by a
quadratically small error from an ellipse, and the real determinant of the
ellipse map is (1-|b|^2/R^4).  Comparing the two bounds and letting the
outer radius tend to infinity leaves

\[
  |b|^2\leq r^4
\]

for every (r>1), hence (|b|\leq1).

The chain-level boundary-to-area equality is also a direct specialization of
Stokes' theorem.  The positive area estimate is expressed using the Jacobian
change-of-variables formula, while the following identity records the Stokes
interface that replaces an annular integral by its two oriented boundary
integrals.

@include{lean:JJMath.ComplexAnalysis.planar_annulus_stokes_identity}

## The Second Coefficient

For a normalized injective analytic map

\[
  f(z)=z+a_2z^2+\cdots
\]

on the unit disk, the quotient \(f(z)/z\) extends analytically across the
origin and never vanishes. Choose its holomorphic square root \(u\), normalized by

\[
  u(z)^2=\frac{f(z)}{z},\qquad u(0)=1,
\]

and set

\[
  g(z)=z\,u(z^2).
\]

Then \(g\) is odd and injective, and \(g(z)^2=f(z^2)\). Since

\[
  u(z)=1+\frac{a_2}{2}z+O(z^2),
\]

the reciprocal map on the exterior disk has expansion

\[
  G(\zeta)=\frac{1}{g(1/\zeta)}
  =\zeta-\frac{a_2}{2\zeta}+O(\zeta^{-3}).
\]

Grönwall's theorem bounds the modulus of the coefficient of
\(\zeta^{-1}\) by \(1\), and therefore yields the sharp estimate

\[
  |a_2|\leq2.
\]

@include{lean:JJMath.ComplexAnalysis.bieberbach_second_coefficient}

## The Omitted-Value Argument

Suppose a normalized injective map omits (a\neq0).  The Möbius transform

\[
  z\longmapsto \frac{a f(z)}{a-f(z)}
\]

is again normalized and injective.  Its second coefficient is
(a_2+1/a).  Applying the preceding estimate to both maps and using the
triangle inequality gives (|1/a|\leq4), hence (|a|\geq1/4).  Thus no
point of the open quarter disk is omitted.

@include{lean:JJMath.ComplexAnalysis.koebe_quarter_normalized}

After translating by (f(0)) and dividing by (f'(0)), the same statement
says that the image contains the disk centered at (f(0)) with radius
(|f'(0)|/4).

@include{lean:JJMath.ComplexAnalysis.koebe_quarter}
