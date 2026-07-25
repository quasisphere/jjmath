import JJMath.Quasiconformal.LinearAlgebra
import JJMath.Quasiconformal.LocalSobolev
import JJMath.Quasiconformal.ACL
import JJMath.Quasiconformal.ApproxDifferentiability
import JJMath.Quasiconformal.SquareBoundary
import JJMath.Quasiconformal.ConformalChange
import JJMath.Quasiconformal.Mobius
import JJMath.Quasiconformal.Basic
import JJMath.Quasiconformal.ChangeOfVariables
import JJMath.Quasiconformal.Capacity
import JJMath.Quasiconformal.Examples
import JJMath.Quasiconformal.CapacityGeometry
import JJMath.ComplexProjective.PQDifferential
import JJMath.Quasiconformal.Surface
import JJMath.Quasiconformal.RiemannSphere
import JJMath.Quasiconformal.RiemannSphereBeltrami
import JJMath.Quasiconformal.SphericalMetric
import JJMath.Quasiconformal.CapacitySeparation
import JJMath.Quasiconformal.Compactness
import JJMath.Quasiconformal.SphericalBeltramiCompactness
import JJMath.Quasiconformal.BeurlingKernel
import JJMath.Quasiconformal.BeurlingTruncation
import JJMath.Quasiconformal.BeurlingTransform
import JJMath.Quasiconformal.BeurlingApproximation
import JJMath.Quasiconformal.BeurlingRepresentation
import JJMath.Quasiconformal.BeurlingSeparated
import JJMath.Quasiconformal.BeurlingRoughRepresentation
import JJMath.Quasiconformal.BeurlingBadPart
import JJMath.Quasiconformal.BeurlingWeakType
import JJMath.Quasiconformal.BeurlingWeakExtension
import JJMath.Quasiconformal.BeurlingInterpolation
import JJMath.Quasiconformal.BeurlingLp
import JJMath.Quasiconformal.BeurlingDuality
import JJMath.Quasiconformal.BeurlingAboveTwo
import JJMath.Quasiconformal.BeurlingComplexInterpolation
import JJMath.Quasiconformal.BeltramiSolver
import JJMath.Quasiconformal.BeltramiLpSolver
import JJMath.Quasiconformal.CauchyTransform
import JJMath.Quasiconformal.CauchyLp
import JJMath.Quasiconformal.CauchyLpSobolev
import JJMath.Quasiconformal.SobolevBeurling
import JJMath.Quasiconformal.SobolevMorrey
import JJMath.Quasiconformal.WeakHolomorphic
import JJMath.Quasiconformal.PrincipalSolution
import JJMath.Quasiconformal.OpenDiscrete
import JJMath.Quasiconformal.PrincipalHomeomorphism
import JJMath.Quasiconformal.PrincipalNormalization
import JJMath.Quasiconformal.MeasurableRiemannMapping
import JJMath.Quasiconformal.Stoilow
import JJMath.Quasiconformal.PointRemovability

/-!
# Quasiconformal mappings

This umbrella module exports the planar real-linear distortion algebra, the
local $W^{1,2}$ and Beltrami interfaces, the topological orientation predicate,
the conformal and Möbius coordinate-change rules, the quantitative planar,
Riemann-surface, and Riemann-sphere definitions of quasiconformality,
intrinsic $(p,q)$-, Beltrami-, and quadratic-differential types, the
finite-distortion area and inverse interface, a compatible compact metric on the Riemann sphere,
normalized continuum-capacity separation, and basic complex-affine examples.
It also exports the Plancherel construction of the Beurling transform as an
isometry on planar $L^2$, all three Calderón--Zygmund conditions for its
physical kernel, absolutely convergent positive truncations on test
functions, the Fourier symbols of both Wirtinger derivatives,
the complete $L^2$ Neumann solver for the Beltrami equation, and the
test-function Cauchy fundamental solution together with the pointwise identity
$\partial_{\bar z}\mathcal Cg=g$, smoothness and far-field decay of
$\mathcal Cg$, the pointwise formula
$\partial_z\mathcal Cg=\mathcal C(\partial_zg)$, and the exact $L^2$ identity
$\mathcal S(\partial_{\bar z}g)=\partial_zg$ on test functions. The cutoff
argument at infinity is also complete, giving
$\partial_z\mathcal Cg=\mathcal Sg$ almost everywhere and the full local
$W^{1,2}$ differential of the Cauchy transform. The restricted weak $(1,1)$
estimate has also been extended by convergence in measure to a complex-linear
map from planar $L^1$ into measurable functions modulo null sets, compatible
with the original transform on $L^1\cap L^2$ and satisfying the same weak
bound with constant $40+16\pi$.
The real-interpolation core now also includes the measurable high/low
truncation of an $L^1$ input, the combined weak-$L^1$/strong-$L^2$
distribution estimate, the two Tonelli tail identities, and the resulting
strong $L^p$ moment and norm bounds for $1<p<2$ on integrable inputs. The
bounded transform has also been completed from finite-support simple
functions to a continuous complex-linear map on all planar $L^p$.
The complex-bilinear $L^2$ pairing has now also been developed far enough to
show that Fourier transform, inverse Fourier transform, the even Beurling
multiplier, and hence the $L^2$ Beurling transform have the required transpose
identities. Compatibility of the weak-$L^1$ extension with the Fourier
multiplier transfers this symmetry to every $L^1\cap L^2$ input pair.
Quantitative duality also transfers the completed estimate below two to the
conjugate exponent above two, first on finite-support simple functions and
then, by density, on the full planar $L^q$ space. On the common integrable
simple-function core, the exact $L^2$ pairing now has both this finite
above-two endpoint and its norm-one $L^2$ endpoint; bilinear complex
interpolation and quantitative duality give the corresponding strong
intermediate-exponent estimate. Density now gives the completed bounded
operator on all of $L^r$. Fixed endpoints $3/2$ and $3$ supply exponents
$2<r<3$ for which the $L^\infty$ multiplier--Beurling composition is a
strict contraction whenever the coefficient norm is less than one. Its
Neumann resolvent solves the $L^r$ Beltrami equation uniquely; simultaneous
simple approximation proves compatibility with the exact $L^2$ transform,
and compact support identifies the $L^r$ solution with the existing $L^2$
solution. The parameter choice is packaged for raw bounded measurable
coefficients supported in a disk. Smooth cutoff localization now extends this
near-$2$ argument to every continuous local $W^{1,2}$ Beltrami solution:
the rough Sobolev--Beurling identity, bounded compactly supported cutoff
error, and $L^2$ uniqueness prove that $Df$ belongs locally to some
$L^p$ with $2<p<3$. For disk-supported $L^p$ data with $p>2$,
the pointwise rough Cauchy integral is now proved absolutely convergent and
continuous by support-controlled smooth approximation and a uniform local
$L^q$ kernel estimate. It also satisfies the principal $O(|z|^{-1})$ decay
and tends to zero at infinity. Its weak Wirtinger derivatives are
$\partial_{\bar z}\mathcal C_ph=h$ and
$\partial_z\mathcal C_ph=\mathcal S_2h$. Consequently the compactly supported
Beltrami solver now produces a continuous local-$W^{1,2}$ principal map with
the prescribed weak equation and distortion inequality. The asymptotic
identity at infinity also makes this map proper and gives the standard
positive image-circle class about every target on a sufficiently large
circle.
-/
