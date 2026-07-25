# Plan for a quasiconformal mapping library

## Goal and recommended scope

Add a quasiconformal mapping library whose primary public definition is the
standard geometric one.  For open planar domains $\Omega,\Omega'\subseteq
\mathbb C$, a $K$-quasiconformal map is an orientation-preserving
homeomorphism

$$
f:\Omega\longrightarrow\Omega'
$$

which belongs to $W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb C)$ and satisfies

$$
\lVert Df(z)\rVert_{\mathrm{op}}^2\le K\,J_f(z)
\quad\text{for almost every }z\in\Omega,
\qquad K\ge 1.
$$

Here $J_f=\det_{\mathbb R}Df$.  The operator norm is essential: with the
Hilbert--Schmidt norm a conformal map satisfies $\lVert Df\rVert_{HS}^2=2J_f$,
so the normalization $K\ge1$ would be wrong.

The first major endpoint should be the measurable Riemann mapping theorem in
the following concrete form.

> If $\mu:\mathbb C\to\mathbb C$ is measurable and
> $\lVert\mu\rVert_\infty\le k<1$, there is an orientation-preserving
> homeomorphism $F:\widehat{\mathbb C}\to\widehat{\mathbb C}$ fixing
> $0,1,\infty$ whose finite-chart restriction is locally $W^{1,2}$ and
> satisfies $F_{\bar z}=\mu F_z$ almost everywhere.  It is
> $K$-quasiconformal for $K=(1+k)/(1-k)$.

The planar and Riemann-sphere APIs should be completed before general
Riemann-surface maps.  The latter are naturally chartwise, but building that
abstraction first would not remove any of the difficult analytic obligations.

## Implementation status (2026-07-23)

Milestone 1 is complete.  The new `JJMath.Quasiconformal`
umbrella exports:

- the real-linear Wirtinger decomposition;
- the exact real Jacobian and operator-norm formulas;
- the equivalence between Beltrami-ratio and metric-distortion bounds;
- exact Wirtinger composition formulas, conformal norm/Jacobian scaling on
  both sides, and the explicit continuous-linear inverse whenever the
  Jacobian is positive;
- the inverse of a positive-Jacobian real-linear map satisfies the same metric
  distortion inequality as the original map;
- the planar adjugate is continuous, has the same operator norm as the
  original real-linear map, satisfies both adjugate identities, and equals
  $J(L)L^\dagger$ under the finite-distortion inequality, including the
  zero-Jacobian branch;
- continuously differentiable maps have their classical differential as a
  weak differential, and real-affine maps are locally $W^{1,2}$ with their
  constant differential;
- continuous real-affine postcomposition and locally bi-Lipschitz
  precomposition preserve local $W^{1,2}$, with the full weak chain rule;
- inversion preserves planar null sets and local Sobolev regularity on
  $\mathbb C^\times$, with explicit $\partial_z$ and
  $\partial_{\bar z}$ transformation formulas;
- conformal source-coordinate changes transport the weak Beltrami equation
  by the cocycle $(\mu\circ T)\overline{T'}/T'$, preserve its essential norm
  bound, and preserve the metric distortion inequality;
- those coordinate-change laws are specialized to nonconstant
  complex-affine maps and inversion, while complex-linear target
  postcomposition preserves both the Beltrami equation and metric distortion;
- arbitrary projective Möbius representatives have a null-set-preserving
  finite fractional-linear formula, a locally bi-Lipschitz finite-chart
  equivalence, and full local Sobolev, Beltrami, essential-bound, and
  metric-distortion transport laws away from the pole;
- the pole-free finite Möbius equivalence preserves planar orientation and is
  $1$-quasiconformal;
- sphere homeomorphisms have a chartwise $K$-quasiconformal predicate using
  all finite/reciprocal source and target chart pairs, and the
  finite-to-finite projective action is identified with the fractional-linear
  formula on its exact source and target domains;
- reciprocal chart representations are reduced to finite representations of
  $A$, $AJ$, $JA$, or $JAJ$, proving that every projective Möbius sphere
  homeomorphism is $1$-quasiconformal in all four standard chart pairs;
- the planar local $W^{1,2}$ predicate, restriction and compact-exhaustion
  APIs, and almost-everywhere uniqueness of the weak differential;
- the weak Beltrami equation and essential coefficient bound;
- an honest topological orientation predicate witnessed by a closed disk in
  the domain and a normalized boundary-loop homotopy in
  $\mathbb C\setminus\{0\}$, together with radius independence and closure
  under composition;
- the requested geometric definition of a $K$-quasiconformal homeomorphism
  between open planar domains, together with independence from the
  weak-differential witness and locality under restriction to open source and
  target subdomains;
- the planar bounded-distortion hierarchy: an almost-everywhere analytic
  predicate, a continuous strictly nonconstant quasiregular predicate, and
  the quasiconformal specialization to orientation-preserving
  homeomorphisms; the existing whole-plane Stoilow and open/discrete
  theorems are exposed directly through the quasiregular predicate; and
- a complete end-to-end regression theorem: every nonconstant complex-affine
  whole-plane map $z\mapsto az+c$ is $1$-quasiconformal.

The harmonic-analysis branch needed above exponent two is now complete
through the solution-identification estimate. A reusable bilinear Riesz--Thorin theorem
has been proved on integrable simple functions, instantiated with the exact
$L^2$ Beurling pairing and a finite endpoint bound, and extended by density
to a bounded operator on all of $L^r$. With fixed endpoints $3/2$ and $3$,
the explicit choice
$$
  r_\theta^{-1}=\frac{1-\theta}{2}+\frac\theta3
$$
gives $2<r_\theta<3$, and continuity at $\theta=0$ gives
$\|\mu\|_\infty A_{3/2}^\theta<1$ for sufficiently small positive
$\theta$. The corresponding $L^r$ multiplier--Beurling operator has norm
strictly less than one, hence an invertible Neumann resolvent. The completed
$L^r$ transform agrees with the exact transform on $L^r\cap L^2$; compact
support then places the $L^r$ solution in $L^2$, where uniqueness identifies
it with the existing Hilbert-space solution. The parameter choice and
$L^r$ right-hand side are now also packaged for a raw bounded measurable
coefficient supported in a disk. The next analytic step is to build the rough
Cauchy potential.

The area-and-inverse foundation of Milestone 2 is now complete.
`ChangeOfVariables.lean` adds the standard
Lusin $N$ and $N^{-1}$ predicates, proves the classical differentiable area
formula and its null-set consequence, proves almost-everywhere nonnegativity
of the weak Jacobian from the quasiconformal distortion inequality, and
exposes the exact Sobolev area formula and inverse-quasiconformality theorem.
It now also proves the precise reduction from almost-everywhere Fréchet
differentiability and the Lusin $N$ property to the full area formula: a
measurable null exceptional set is removed, Mathlib's differentiable formula
is applied on the complement, and $N$ shows that the discarded image is null.
An audit of the available Sobolev and Jacobian foundations shows that this
should remain a strong-input convenience theorem rather than the primary
Sobolev proof route.  The primary route instead uses approximate
differentiability, countably many measurable pieces on which the map has its
weak differential as a derivative within the piece, and an independently
proved Lusin $N$ theorem.  This matches Mathlib's internal Jacobian
decomposition and avoids making ambient Fréchet differentiability an
unnecessarily strong intermediate target. `ChangeOfVariables.lean` now proves
the corresponding assembly theorem: an arbitrary countable measurable
within-differentiability cover, together with Lusin $N$, implies the full
weighted area formula.  The first ACL bridge is also now proved: a continuous
scalar weak Sobolev function on the product strip is absolutely continuous on
every compact subinterval of almost every vertical line, and its classical
line derivative is the corresponding weak directional derivative almost
everywhere.  This uses the repository's already complete fiberwise weak
derivative theorem and one-dimensional absolutely-continuous representative
theorem; continuity transfers the representative back to the original map.
Cutoff localization is now complete as well: a compactly supported Sobolev
localization has its product-rule weak differential on the entire ambient
space, and the strip theorem therefore applies to every protected vertical
segment in a compact subset of an open product-domain.  The real and imaginary
parts have also been recombined into a complex-valued ACL theorem with the
expected complex directional derivative.  The planar coordinate bridge is
now complete as well.  Weak differentials pull back exactly through any
volume-preserving continuous real-linear equivalence, by transporting test
functions and both integrals.  Specializing to $(x,y)\mapsto x+iy$ and to the
coordinate-swapped identification proves local ACL on protected horizontal
and vertical planar segments, with line derivatives $Df(1)$ and $Df(i)$,
respectively.  Thus coordinate ACL is no longer on the critical path; its
first geometric consumer is now complete as well.  Absolute continuity bounds
the diameter of each side image by the line integral of the corresponding
weak directional derivative, and the four intersecting side images assemble
into a rectangle-boundary diameter estimate.  A separate compact-set theorem
proves $|A|\leq\operatorname{diam}(\partial A)^2$ in the plane by applying the
product-coordinate volume estimate to real and imaginary extrema on the
frontier.  Consequently, for an ambient planar homeomorphism, the area of a
mapped closed rectangle is at most the square of the diameter of its mapped
boundary.  This avoids introducing Jordan-curve or sharp isoperimetric theory.
The abstract first-moment step of the Fubini selection is now proved too: a
nonnegative measurable product density admits horizontal and vertical fibers
satisfying any prescribed almost-everywhere good-line property and having
energy no larger than the corresponding transverse average.  Applying these
two selectors to four outer strips now produces an entire good rectangle
frame surrounding a prescribed inner rectangle.  This frame has now been
specialized to continuous local $W^{1,2}$ maps: its four selected lines are
ACL-good and their squared weak-differential energies satisfy the required
strip-average bounds.  Absolute continuity also automatically supplies
interval integrability of each almost-everywhere complex line derivative, so
the rectangle-boundary theorem no longer needs separate integrability
hypotheses.  A one-dimensional extended-valued Cauchy--Schwarz theorem now
turns the four selected line energies into an explicit mapped-boundary
diameter estimate using the operator norm of the weak differential.  The
rectangle area estimate has now been specialized from ambient
homeomorphisms to homeomorphisms between planar domains: the ambient
representative is continuous on the source, maps ambient-open source subsets
to ambient-open target subsets, and carries the frontier of a compact image
back to the source frontier.  The selected-frame line-energy estimate and the
four strip averages have also now been combined into the exact four-term
square-root bound.  On a concentric protected square, the four scale factors
cancel to give mapped-boundary diameter at most eight times the square root
of the doubled-square energy, and the domain-homeomorphism area estimate then
gives the scale-free bound
$|f(Q)|\leq64\int_{2Q}\lVert Df\rVert^2$.  Source translation preserves local
$W^{1,2}$ with the translated weak differential, so this estimate is proved
for arbitrary sufficiently small square centers rather than only centers in
the protected unit coordinates.  The compact-null covering argument is now
complete: absolute continuity of the product-coordinate energy measure, a
fine integer-grid cover, and a sixteen-color bounded-overlap estimate imply
that compact null sets have null images.  Measurability of ambient images and
inner regularity then upgrade this to the full Lusin $N$ property for local
$W^{1,2}$ homeomorphisms between open planar domains.
The density conversion is now complete, so every planar local $W^{1,2}$ map
is approximately differentiable almost everywhere with approximate
differential equal to its weak differential. The Lusin--Whitney theorem now
decomposes an approximately differentiable measurable map into countably
many measurable within-differentiability pieces. The Sobolev area formula is
therefore fully proved from this decomposition and the independent Lusin $N$
result. On the inverse
side, the total Wirtinger pseudoinverse, its reciprocal-Jacobian and distortion
identities, the null image of measurable zero-Jacobian source sets, and a
locally $L^2$ inverse differential candidate are now proved. The same
candidate satisfies the $K$-distortion inequality almost everywhere on the
target. The oriented area formula has also been upgraded to Bochner integrals.
The planar adjugate algebra, compact-support integrability,
change-of-variables transport, and the assembly identifying the candidate as
the inverse weak differential are all proved. The smooth core of the planar
Piola argument is now complete as well: Cartesian integration by parts,
divergence-freeness of the adjugate field by symmetry of mixed second
derivatives, the invariant smooth adjugate identity, and its cutoff-composition
form have all been formalized. The exact planar Sobolev Piola identity is now
proved: a fixed cutoff localizes all terms to one compact source set, the
Jacobian main term is passed along an almost-everywhere convergent subsequence,
the cutoff error vanishes, and the linear adjugate side converges in $L^2$.
The two scalar density sequences have now been recombined into smooth complex
maps converging in the full local $L^2$ graph norm, and the abstract $L^2$
pairing and Lipschitz-composition limit lemmas are proved. The compact
cutoff-adjugate multiplier estimate and the resulting localized decay of the
cutoff error are proved as well. Strong local $L^1$ convergence of the
Jacobians is now proved from graph-norm convergence, and an almost-everywhere
convergent subsequence plus dominated convergence passes the localized
Jacobian main term to its Sobolev limit. The fixed cutoff construction,
support localization, limit assembly, and removal of the cutoff are complete;
the linear adjugate side converges strongly by the same $L^2$ pairing
infrastructure. Symmetry of the topological orientation predicate under
inversion is now proved as well, so inverse quasiconformality and $N^{-1}$ are
fully assembled.

Both `lake build JJMath.Quasiconformal` and the full `lake build` succeed. Identity
orientation and closure of orientation preservation under composition are
proved.  The latter is established directly from compact normalized-loop
homotopies, without requiring a general winding-number or fundamental-group
library: shrink the first boundary into the second witness disk, transport its
positive class there, and rotate and rescale to the second positive boundary.
The local Sobolev, topological, conformal-change, and standard-chart sphere
slices are complete through projective Möbius maps. The independent Lusin $N$
input is complete. The scale-covariant planar $L^2$ Poincare estimate, local
$L^1$ consequences of local $W^{1,2}$ regularity, and localized Lebesgue-point
theorems are now also complete. In particular, the weak differential has
vanishing $L^2$ mean oscillation in operator norm almost everywhere; this is
obtained by applying Hilbert-valued mean-square differentiation to the two
coordinates $Df(1)$ and $Df(i)$ and then using an explicit norm comparison.
The complex-valued Poincare estimate and its application to
$f(y)-Df(x)(y-x)$ are complete as well: at almost every $x$ one can choose
constants $a_r$ for which the affine-remainder $L^2$ norm is $o(r^2)$.
The nested-ball comparison is now complete, as is the stronger local
mean-square route for identifying the centers. The dyadic telescoping step is
also complete and upgrades $a_r\to f(x)$ and
$\lVert a_r-a_{r/2}\rVert/r\to0$ to
$\lVert a_r-f(x)\rVert/r\to0$. Consequently the fixed-center affine
remainder has $L^2$ norm $o(r^2)$. A small-inner-ball split and the $L^2$
Chebyshev inequality now convert this into the standard density formulation,
and hence approximate differentiability with differential $Df$ holds almost
everywhere. Inverse symmetry of planar orientation, the planar Sobolev
adjugate/Piola identity, the area theorem, and the inverse theorem are complete.
The planar condenser-capacity distortion theorem is now complete, using both
forward and inverse Sobolev composition. The model-geometry layer now also
has complex-affine capacity invariance, concentric ring capacity, scale
invariance, reduction to the radius ratio $R/r$, and Sobolev bridges for
smooth and locally Lipschitz real competitors. The piecewise logarithmic
cutoff is now an admissible competitor; its differential and almost-everywhere
energy density are explicit, its polar energy is exactly
$2\pi/(\log R-\log r)$, and this proves the corresponding upper bound for
concentric ring capacity. The matching lower bound is now complete as well.
Endpoint-preserving radial ACL gives unit oscillation on almost every ray;
weighted Cauchy--Schwarz turns this into a radial energy bound; the exact
Haar-to-sphere polar decomposition supplies angular mass $2\pi$ and radial
measure $t\,dt$; and dilation invariance identifies the scaled unit-disk
integral with the original Dirichlet energy. Taking the infimum and comparing
with the logarithmic competitor proves the exact formula
$$
  \operatorname{cap}(r,R)=\frac{2\pi}{\log R-\log r}
  \qquad (0<r<R).
$$
The separation layer now contains the required planar Grötzsch--Loewner
estimate. For every $\delta>0$, a compact connected $E_0$ containing $0$ and
reaching modulus $\delta$, together with a closed connected unbounded $E_1$
containing $1$, has capacity bounded below by a positive constant depending
only on $\delta$. The proof is a direct circle-and-ray length--area argument;
a general curve-modulus library is not needed. Put

$$
  d=\min\{\delta/2,1/4\}.
$$

Polar averaging selects radii $a\in(d,2d)$ and $b\in(1,2)$. Connectedness
forces the two plates to meet their respective circles, and the angular ACL
estimate gives, for every direction $\theta$,

$$
  |u(a\theta)|,\ |1-u(b\theta)|
    \le \sqrt{4\pi E},
$$

Radial ACL and Fubini select a direction whose radial change satisfies

$$
  |u(b\theta)-u(a\theta)|
    \le \sqrt{E\log(2/d)/(2\pi)}.
$$

The triangle inequality therefore gives $1\le C(\delta)\sqrt E$, with

$$
  C(\delta)=4\sqrt{\pi}
    +\sqrt{\log(2/d)/(2\pi)},
$$

and hence $E\ge C(\delta)^{-2}$. Taking the capacity infimum completes the
uniform lower bound. This route avoids constructing circular means.

Capacity distortion, the ray comparison with the exact round ring, and
$\operatorname{cap}(e^{-n},1)=2\pi/n$ give uniform finite-chart moduli of
continuity for normalized $K$-quasiconformal sphere maps. Affine recentering
at a nonzero finite point $x$ uses $B_x(z)=x(1-z)$ in the source and
$B_{f(x)}^{-1}$ in the target; reciprocal control of the inverse family
supplies the uniform bound on $|f(x)|$ needed to undo the target
normalization. Together with reciprocal coordinates at $\infty$, this proves
equicontinuity on the entire sphere for the maps and inverses, hence uniform
equicontinuity by compactness. Arzelà--Ascoli now gives a common subsequence
whose maps and inverses converge uniformly to a normalized homeomorphism and
its inverse. The area formula and reciprocal finite-chart control now give a
uniform $L^2$ bound for the weak differentials on every fixed finite-chart
disk. Diagonal extraction on the integer disk exhaustion, compatibility of
the resulting $L^2$ classes, strong local $L^2$ convergence of the
finite-chart values, and closure of the distributional weak-derivative
identity are complete. The limit finite-chart homeomorphism is therefore in
$W^{1,2}_{\mathrm{loc}}$. For the prescribed-coefficient construction, the
locally stabilized compactness step is now complete: coefficients that agree
eventually with one measurable essentially bounded $\mu$ on every fixed disk
produce a limit satisfying
$\partial_{\bar z}f=\mu\,\partial_zf$ on the whole plane. When
$|\mu|\leq k<1$, the limit also satisfies the metric distortion inequality
with $K=(1+k)/(1-k)$. Topological orientation is preserved under compact-local
uniform homeomorphic limits. Inversion conjugation transfers both Sobolev
regularity and the Beltrami equation to reciprocal coordinates; a second
compactness extraction controls that chart without changing the spherical
limit. The two diagonal charts then imply the two mixed charts by restricting
to $\mathbb C^\times$ and composing with inversion. Thus almost-everywhere
convergence of uniformly bounded coefficients now gives a normalized
$((1+k)/(1-k))$-quasiconformal sphere limit in all four standard chart pairs.
The public compactness theorem now expresses this with intrinsic Beltrami
differentials and intrinsic Riemann-surface quasiconformality. Chartwise
almost-everywhere convergence is part of the differential API and, on the
sphere, is equivalent to convergence of the affine coefficients. The older
finite- and reciprocal-chart theorems remain the planar implementation
engine and no longer determine the public conclusion.
The principal-solution branch is now the largest missing part of the main
existence theorem. Its first Hilbert-space layer and its initial Cauchy
interface are complete:
`BeurlingTransform.lean` defines the multiplier
$m(0)=1$, $m(\xi)=\overline\xi/\xi$ for $\xi\ne0$, realizes pointwise
$L^\infty\times L^2\to L^2$ multiplication as a bounded linear map, and
conjugates this unit-modulus multiplier by Mathlib's unitary Fourier transform.
The resulting Beurling transform is an exact isometry on planar $L^2$.
`CauchyTransform.lean` proves local integrability of $(z-w)^{-1}$, proves
absolute integrability against every compactly supported smooth function,
defines the normalized Cauchy integral, and places test functions canonically
in planar $L^2$. The fundamental-solution argument is complete, the transform
is smooth, and $\partial_{\bar z}\mathcal Cg=g$ holds pointwise. Differentiation
through convolution now also gives
$\partial_z\mathcal Cg=\mathcal C(\partial_zg)$ pointwise, and the far-field
bound $\mathcal Cg(z)=O(|z|^{-1})$ is formalized. The two Schwartz
Fourier-symbol formulas and the exact test-function identity
$\mathcal S(\partial_{\bar z}\varphi)=\partial_z\varphi$ are proved, fixing the
sign and conjugation convention. The cutoff-at-infinity passage is now
complete as well: its antiholomorphic product-rule error has global $L^2$
norm $O(R^{-1})$, and local comparison on arbitrarily large cutoff disks
proves $\partial_z\mathcal Cg=\mathcal Sg$ almost everywhere. Consequently
the Cauchy transform has the claimed local $W^{1,2}$ differential.
`BeltramiSolver.lean` proves
$\lVert M_\mu\mathcal S\rVert_{2\to2}\leq\lVert\mu\rVert_\infty$, inverts
$I-M_\mu\mathcal S$ by its norm-convergent Neumann series, and proves existence
and uniqueness for $h-\mu\mathcal Sh=g$ in $L^2$. It also proves that the
roadmap's bounded coefficient supported almost everywhere in a disk belongs
to $L^2$, and hence obtains the particular equation
$h-\mu\mathcal Sh=\mu$.

## Executive assessment

The repository already has a substantial, fully proved Sobolev foundation.
The quasiconformal project should reuse it rather than introduce a second
notion of weak derivative. In particular, the implemented quasiconformal and
planar-orientation core has no `axiom` declarations. The Lusin--Whitney
decomposition, planar Sobolev adjugate/Piola identity, inverse symmetry of
planar orientation, Sobolev area formula, distributional inverse-differential
theorem, and public inverse-quasiconformality theorem are all proved. Ambient
Fréchet differentiability almost everywhere is retained only as a stronger
convenience hypothesis for an alternate area-formula theorem.

The measurable Riemann mapping theorem, including its compact-support input
and spherical extension, is fully assembled. The proper principal-solution
route proves openness, finite fibers, and positive local index by capacity,
weighted Jacobian measure, and protected multiplicity.

The nonproper whole-plane theorem is now complete as well, by a post-MRMT
Stoilow factorization. The normalized spherical solution is restricted to a
whole-plane quasiconformal homeomorphism; its weak Jacobian is proved strictly
positive almost everywhere by the area formula and the inverse Lusin
property. The inverse Sobolev chain rule and pointwise cancellation of equal
Beltrami coefficients make the residual factor weakly holomorphic, and the
Sobolev Weyl lemma makes it entire. The classical open-mapping and
isolated-zero theorems then transfer openness and discrete fibers through the
homeomorphism, while the existing local multiplicity theorem gives positive
local index. Thus the former nonproper theorem stub has been removed.

The largest remaining extensions of the library are:

1. **The domain-local quasiregular theorem and Stoilow factorization.** The
   proved theorem treats continuous nonconstant maps
   $\mathbb C\to\mathbb C$ that lie in $W^{1,2}_{\mathrm{loc}}$ and have
   bounded distortion; it is now available through
   `IsKQuasiregularOn K Set.univ f`. For a map defined only on an arbitrary
   open planar domain $\Omega$, extend its measurable coefficient by zero,
   solve the global equation, factor on $\Omega$, and formulate the
   holomorphic factor on the open set $\Phi(\Omega)$. This should reuse all
   analytic inputs, but still needs regional bookkeeping for the inverse
   chain rule and the weak Cauchy--Riemann conclusion.
2. **General nonlinear weak closure under normalized limits.** Rellich and weak
   Hilbert compactness theorems do not by themselves preserve the nonlinear
   finite-distortion inequality. General $K$-distortion closure would require
   distributional weak continuity of the planar Jacobian together with
   localized lower semicontinuity, or a closed capacity-distortion
   characterization. This is desirable for a coefficient-free compactness
   theorem, but it is no longer needed for the prescribed-coefficient route:
   varying bounded Beltrami equations now close under almost-everywhere
   coefficient convergence, including reciprocal coordinates and all four
   sphere charts.
3. **Tensor operations for intrinsic surface differentials.** The
   atlas-level line bundle of $(p,q)$-differentials is now constructed, with
   Beltrami differentials as the $(-1,1)$ case and quadratic differentials as
   the $(2,0)$ case. Chart coefficients, transition laws, measurability,
   essential norm bounds, chartwise almost-everywhere convergence, and the
   intrinsic realization predicate are in place. Spherical compactness is
   formulated using these intrinsic notions. What remains is a general
   pullback/composition API, chart independence theorems for weak equations
   beyond the chosen chart at each point, and analytic operations on
   quadratic differentials.

The all-purpose topological Whyburn--Stoilow theorem remains an optional stub,
but neither the proper principal-solution proof nor the analytic Stoilow route
uses it. There is no remaining theorem stub on the prescribed-coefficient
critical path. Items 1--3 can proceed independently.

## Current foundations to reuse

| Foundation | Current repository support | What is still missing for quasiconformal maps |
|---|---|---|
| Weak $W^{1,2}$ derivatives | [`Basic.lean`](JJMath/Analysis/Sobolev/Basic.lean) defines vector-valued Euclidean weak derivatives and local surface $W^{1,2}$ data. The new [`LocalSobolev.lean`](JJMath/Quasiconformal/LocalSobolev.lean) adds the planar local predicate, restriction, compact exhaustion, classical-to-weak differentiation, affine regularity, and uniqueness almost everywhere. [`ApproxDifferentiability.lean`](JJMath/Quasiconformal/ApproxDifferentiability.lean) proves approximate differentiability almost everywhere with approximate differential equal to the weak differential and supplies the countable Lusin--Whitney within-differentiability decomposition. | General finite-distortion composition rules needed for later weak-limit closure. |
| ACL and approximation | [`ACL.lean`](JJMath/Analysis/Sobolev/ACL.lean) proves weak fundamental-theorem identities for fixed translated segments and has local smooth graph approximation. [`Rellich.lean`](JJMath/Analysis/Sobolev/Rellich.lean) proves ACL for continuous scalar weak Sobolev functions on almost every first-coordinate line and localizes it by a compactly supported product-rule extension. [`Quasiconformal/ACL.lean`](JJMath/Quasiconformal/ACL.lean) recombines the real and imaginary statements, transports weak differentials through volume-preserving linear coordinates, and proves planar ACL on protected horizontal and vertical segments with derivatives $Df(1)$ and $Df(i)$. [`Quasiconformal/SquareBoundary.lean`](JJMath/Quasiconformal/SquareBoundary.lean) selects four good sides by Fubini and averaging, proves $|f(Q)|\leq64\int_{2Q}\lVert Df\rVert^2$, controls finite grid covers by sixteen-color bounded overlap, and establishes the compact-null image theorem. [`ChangeOfVariables.lean`](JJMath/Quasiconformal/ChangeOfVariables.lean) upgrades this by measurable-image inner regularity to the full Lusin $N$ property for local $W^{1,2}$ homeomorphisms between open planar domains. [`SobolevMorrey.lean`](JJMath/Quasiconformal/SobolevMorrey.lean) proves the same-ball Morrey area estimate and, via Besicovitch covering, full Lusin $N$ for continuous maps whose weak differential lies locally in some $L^p$, $p>2$; bounded distortion supplies this higher integrability. [`Pullback.lean`](JJMath/Analysis/Sobolev/Pullback.lean) gives exact translation and dilation laws for restricted $L^p$ norms, and [`Poincare.lean`](JJMath/Analysis/Sobolev/Poincare.lean) derives the scale-covariant complex $L^2$ Poincare inequality. [`ApproxDifferentiability.lean`](JJMath/Quasiconformal/ApproxDifferentiability.lean) proves the fixed-center affine remainder estimate, almost-everywhere approximate differentiability, and its Lusin--Whitney conversion into countably many measurable within-differentiability pieces. [`BallTrace.lean`](JJMath/Analysis/Sobolev/BallTrace.lean) contains the endpoint-preserving radial ACL machinery used in the exact ring-capacity proof. | Spherical separation. The radial trace results are not needed for the rectangle route. |
| Pullback and chain rules | [`Pullback.lean`](JJMath/Analysis/Sobolev/Pullback.lean) proves compact-local weak pullback under locally bi-Lipschitz maps and Rademacher-based chain rules. [`LocalSobolev.lean`](JJMath/Quasiconformal/LocalSobolev.lean) lifts this to complex-valued local $W^{1,2}$ maps, and [`ConformalChange.lean`](JJMath/Quasiconformal/ConformalChange.lean) handles inversion. [`Capacity.lean`](JJMath/Quasiconformal/Capacity.lean) proves both the continuous real-valued and complex-valued Sobolev outer chain rules when the inner map is quasiconformal; [`Stoilow.lean`](JJMath/Quasiconformal/Stoilow.lean) applies the latter to composition with the quasiconformal inverse. | Regional packaging for the domain-local Stoilow theorem and composition laws needed for coefficient-free weak-limit closure. |
| Compactness | [`Rellich.lean`](JJMath/Analysis/Sobolev/Rellich.lean) proves scalar and finite-dimensional local Rellich compactness. [`MazurLemma.lean`](JJMath/PotentialTheory/EnergyMethod/MazurLemma.lean) proves weak subsequence extraction in Hilbert spaces. [`Quasiconformal/Compactness.lean`](JJMath/Quasiconformal/Compactness.lean) proves simultaneous uniform convergence of normalized maps and inverses, diskwise weak-differential extraction and gluing, strong local $L^2$ convergence of finite-chart values, closure for fixed and almost-everywhere convergent bounded Beltrami coefficients, orientation preservation of the homeomorphic limit, reciprocal-chart transfer by inversion conjugation, the two-diagonal criterion for all four standard chart pairs, and spherical quasiconformality of the resulting limit with constant $(1+k)/(1-k)$. | General coefficient-free nonlinear closure of the $K$-distortion inequality remains optional; the prescribed-coefficient compactness interface is complete. |
| Arzelà--Ascoli | [`RadoSecondCountable.lean`](JJMath/Uniformization/RadoSecondCountable.lean) has locally uniform subsequence extraction from equicontinuity on compact exhaustions. [`Quasiconformal/Compactness.lean`](JJMath/Quasiconformal/Compactness.lean) applies it on the compact sphere and identifies the map and inverse limits. | Complete for the topological compactness step. |
| Jacobians | Mathlib's `MeasureTheory.Function.Jacobian` gives change of variables for injective maps differentiable within a measurable set and internally decomposes such sets into countably many `ApproximatesLinearOn` pieces. [`LinearAlgebra.lean`](JJMath/Quasiconformal/LinearAlgebra.lean) proves the exact determinant, operator-norm, sharp lower metric bound, total Wirtinger pseudoinverse, reciprocal-Jacobian, inverse-distortion, and planar-adjugate formulas. [`ChangeOfVariables.lean`](JJMath/Quasiconformal/ChangeOfVariables.lean) proves the classical and Sobolev scalar and Bochner area formulas, defines extended preimage multiplicity, decomposes positive- and negative-Jacobian differentiability sets into countably many injective sheets, proves both signed multiplicity area formulas, assembles the nonnegative formula over the almost-everywhere Lusin--Whitney cover, proves almost-everywhere measurability and real-valued integrability of Sobolev multiplicity, proves simultaneous compact-uniform and $W^{1,2}$ graph approximation, proves Lusin $N$, compact-local $L^2$ bounds plus target distortion for the inverse candidate, the planar Sobolev adjugate/Piola identity, the distributional inverse theorem, and strict positivity of the weak Jacobian almost everywhere for a quasiconformal homeomorphism. [`OpenDiscrete.lean`](JJMath/Quasiconformal/OpenDiscrete.lean) identifies smooth disk degree almost everywhere with signed multiplicity, proves the smooth and continuous-Sobolev distributional disk-degree formulas, proves that bounded-distortion multiplicity agrees almost everywhere with protected disk degree, deduces nonnegative boundary degree, and proves the protected pullback-energy inequality used by the condenser argument. | Complete for both the proper principal-solution route and the whole-plane Stoilow route. |
| Complex derivative algebra | [`Wirtinger.lean`](JJMath/Hyperbolic/Schwarzian/Wirtinger.lean) defines Fréchet-level $\partial_z$ and $\partial_{\bar z}$ values. The linear-algebra core defines the two components directly from a real continuous-linear map and proves decomposition, distortion, composition, conformal scaling, inverse formulas, and cancellation after inverse composition for two differentials with the same Beltrami coefficient. [`WeakHolomorphic.lean`](JJMath/Quasiconformal/WeakHolomorphic.lean) proves the Sobolev Weyl lemma: a continuous local $W^{1,2}$ map with $\partial_{\bar z}=0$ almost everywhere is holomorphic. [`Stoilow.lean`](JJMath/Quasiconformal/Stoilow.lean) combines these results with the inverse chain rule to prove the whole-plane Sobolev Stoilow factorization and the nonproper open-and-discrete theorem. [`ConformalChange.lean`](JJMath/Quasiconformal/ConformalChange.lean) proves the almost-everywhere Beltrami cocycle and metric invariance for conformal source changes, including affine maps and inversion. [`Mobius.lean`](JJMath/Quasiconformal/Mobius.lean) extends these laws to projective fractional-linear changes away from their poles. | Regional packaging for the domain-local factorization; the whole-plane route is complete. |
| Riemann surfaces, differentials, the sphere, and Möbius maps | [`RiemannSurface.lean`](JJMath/ComplexProjective/Prerequisites/RiemannSurface.lean) supplies the surface class. [`PQDifferential.lean`](JJMath/ComplexProjective/PQDifferential.lean) constructs the intrinsic line bundle of $(p,q)$-differentials and specializes it to Beltrami and quadratic differentials. [`Surface.lean`](JJMath/Quasiconformal/Surface.lean) defines coordinate sources and maps, chartwise bounded distortion and quasiregularity, intrinsic quasiconformality, and realization of a Beltrami differential by a surface homeomorphism. [`Mobius.lean`](JJMath/ProjectiveGeometry/Mobius.lean) and [`RiemannSphere.lean`](JJMath/ProjectiveGeometry/RiemannSphere.lean) provide the sphere geometry. [`RiemannSphereBeltrami.lean`](JJMath/Quasiconformal/RiemannSphereBeltrami.lean) proves the finite/reciprocal coordinate laws for the general intrinsic differential, and [`MeasurableRiemannMapping.lean`](JJMath/Quasiconformal/MeasurableRiemannMapping.lean) states the normalized theorem directly for a Beltrami differential on the whole sphere. | General pullback and composition laws, chart-independence of weak realization under arbitrary compatible coordinates, and analytic operations on quadratic differentials. |
| Uniformization | [`CompactH1Uniformization.lean`](JJMath/Uniformization/CompactH1Uniformization.lean) proves uniformization of simply connected Riemann surfaces. | It starts with a pre-existing smooth complex atlas.  It does not construct an integrable complex structure from a measurable Beltrami coefficient, so it cannot serve as the missing existence theorem without an equally hard isothermal-coordinate theorem. |
| Capacity | [`Analysis/Sobolev/Capacity.lean`](JJMath/Analysis/Sobolev/Capacity.lean) treats positive capacity at infinity for global zero-trace functions. [`Quasiconformal/Capacity.lean`](JJMath/Quasiconformal/Capacity.lean) defines planar condenser capacity, proves the quasiconformal covector-energy inequality, proves the continuous-Sobolev outer chain rule by bounded retracted approximation, and derives the two-sided $K$-distortion theorem. [`Quasiconformal/CapacityGeometry.lean`](JJMath/Quasiconformal/CapacityGeometry.lean) proves complex-affine invariance, the exact Haar polar decomposition in the plane, dilation invariance of Dirichlet energy, the exact formula $\operatorname{cap}(r,R)=2\pi/(\log R-\log r)$, globally smooth logarithmic cutoffs, their Sobolev postcomposition rule, and their $O(1/\log(R/r))$ energy bound. [`Quasiconformal/CapacitySeparation.lean`](JJMath/Quasiconformal/CapacitySeparation.lean) proves normalized continuum separation, its affine-invariant consequence that every compact nontrivial continuum has positive whole-plane capacity against every disjoint closed connected unbounded continuum, the capacity squeeze, affine recentering at arbitrary finite points, and uniform spherical equicontinuity of normalized maps and inverses. | Complete for normalized compactness and proper-map Reshetnyak lightness. |
| Holomorphic distortion | [`KoebeQuarter.lean`](JJMath/ComplexAnalysis/KoebeQuarter.lean) proves the Koebe quarter theorem and related area estimates. | These apply after a map is known to be holomorphic and do not replace quasiconformal modulus estimates. |

The rough-coefficient elliptic route is not presently shorter.  The Weyl and
potential-theory developments handle harmonic functions and smooth surface
metrics, not De Giorgi--Nash--Moser regularity or isothermal coordinates for
measurable uniformly elliptic coefficients.

## Public definitions and conventions

### Planar domains

Use `Homeomorph Ω Ω'`, where `Ω` and `Ω'` are subtypes of open subsets of
`ℂ`, as the public homeomorphism object.  An ambient extension
$\mathbb C\to\mathbb C$ may be used internally to feed the current weak
derivative predicate; prove immediately that the regional weak derivative is
independent of values outside $\Omega$.

Define a reusable predicate

```lean
def IsLocalW12On (Ω : Set ℂ) (f : ℂ → ℂ)
    (df : ℂ → ℂ →L[ℝ] ℂ) : Prop :=
  IsOpen Ω ∧
  JJMath.Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues Ω f df ∧
  ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
    MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict K) ∧
    MeasureTheory.MemLp df 2 (MeasureTheory.volume.restrict K)
```

The openness assumption can instead be a theorem parameter if that fits the
existing Sobolev style better.  It should not be replaced by global $L^2$
membership: the identity map of the plane must be locally Sobolev.

### Weak Wirtinger derivatives and Jacobian

For $L:\mathbb C\to_{\mathbb R}\mathbb C$, define

$$
L_z=\tfrac12\bigl(L(1)-iL(i)\bigr),\qquad
L_{\bar z}=\tfrac12\bigl(L(1)+iL(i)\bigr).
$$

Then prove, for all $L$,

$$
L(\xi)=L_z\xi+L_{\bar z}\bar\xi,
\quad
J(L)=|L_z|^2-|L_{\bar z}|^2,
\quad
\lVert L\rVert_{\mathrm{op}}=|L_z|+|L_{\bar z}|.
$$

The weak Beltrami equation should be the multiplication-free statement

$$
\partial_{\bar z}f=\mu\,\partial_z f
$$

almost everywhere.  Define the quotient
$\mu_f=\partial_{\bar z}f/\partial_z f$ only as a derived object, using zero on
the null/degenerate branch.  This avoids making the core PDE depend on division
by a possibly zero derivative.

### Orientation

Introduce a genuine topological, componentwise predicate for a homeomorphism
of oriented planar domains.  The recommended implementation is local degree
$+1$: on a sufficiently small disk about every point, the induced map on the
punctured disk sends the positive generator to the positive generator.  This
will probably require a small independent file on planar local degree or
winding number.

Prove later that a planar $W^{1,2}$ homeomorphism with $J_f\ge0$ almost
everywhere and $J_f\not\equiv0$ locally is topologically orientation
preserving.  Until that theorem exists, keep analytic nonnegative Jacobian and
topological orientation as separate hypotheses.

### Bounded distortion, quasiregularity, and quasiconformality

Keep the almost-everywhere analytic condition separate from the choice of a
pointwise representative:

```lean
def HasKBoundedDistortionOn
    (K : ℝ) (Ω : Set ℂ) (f : ℂ → ℂ) : Prop :=
  ∃ df : ℂ → ℂ →L[ℝ] ℂ,
    IsLocalW12On Ω f df ∧
    ∀ᵐ z ∂MeasureTheory.volume.restrict Ω,
      ‖df z‖ ^ 2 ≤ K * weakJacobian (df z)
```

This predicate deliberately does not assert continuity or $K\ge1$. It is
invariant under almost-everywhere changes of $f$, and weak-derivative
uniqueness makes it independent of the witness $df$.

The public planar quasiregular predicate selects the intended representative:

```lean
def IsKQuasiregularOn
    (K : ℝ) (Ω : Set ℂ) (f : ℂ → ℂ) : Prop :=
  1 ≤ K ∧
  ContinuousOn f Ω ∧
  (f '' Ω).Nontrivial ∧
  HasKBoundedDistortionOn K Ω f
```

The nonconstancy condition is strictly pointwise. This is appropriate because
continuity has already selected a representative; at the lower analytic
layer, any future nonconstancy hypothesis should instead be formulated modulo
almost-everywhere equality. Although finite-distortion theory supplies a
continuous representative for Euclidean-valued planar maps and for maps into
compact oriented surfaces, retaining continuity here avoids silently
replacing the actual Lean function and avoids target-valued representative
problems for noncompact planar domains.

Finally, the requested geometric quasiconformal definition specializes the
same analytic predicate to a homeomorphism. A thin domain-level wrapper keeps
the choice of a total ambient representative out of the public geometric API:

```lean
def HasKBoundedDistortionBetween
    (K : ℝ) {Ω Ω' : Set ℂ} (F : Ω ≃ₜ Ω') : Prop :=
  HasKBoundedDistortionOn K Ω (ambientMap F)

def IsKQuasiconformalBetween
    (K : ℝ) {Ω Ω' : Set ℂ} (F : Ω ≃ₜ Ω') : Prop :=
  1 ≤ K ∧
  IsOpen Ω' ∧
  PreservesPlanarOrientation F ∧
  HasKBoundedDistortionBetween K F
```

Every quasiconformal homeomorphism with nontrivial source is therefore
quasiregular. Introduce the unquantified predicates by existentially
quantifying $K$; the quantitative predicates remain primary.

The Beltrami interface is an equivalence theorem.  If
$\lVert\mu\rVert_\infty\le k<1$, set

$$
K(k)=\frac{1+k}{1-k}.
$$

Conversely, $K$-distortion gives
$k(K)=(K-1)/(K+1)$.  Include the $K=1$ corollary: an
orientation-preserving $1$-quasiconformal map is conformal.

### Sphere coefficient and normalization

The main theorem now accepts an intrinsic Beltrami differential on the whole
Riemann sphere. It is the $(-1,1)$ specialization of the general
$(p,q)$-differential line bundle. If $a_{ij}$ is the complex tangent
transition scalar, a coefficient changes by

$$
  a_{ij}\overline{a_{ij}}^{-1}.
$$

Thus the finite and reciprocal coordinate fields are derived views of one
section rather than unrelated input data. On their overlap they satisfy

$$
\mu_\infty(w)
  =\mu_{\mathrm{fin}}(w^{-1})
    \frac{\overline{-w^{-2}}}{-w^{-2}}.
$$

Measurability and the essential norm are defined chartwise for an arbitrary
surface and reduce on the sphere to the finite representative alone. The
conclusion of the spherical measurable Riemann mapping theorem uses the
intrinsic surface realization predicate, while the finite and reciprocal
weak equations appear only in its proof.

## Proposed module layout

```text
JJMath/Topology/PlanarDegree.lean
JJMath/Quasiconformal/LinearAlgebra.lean
JJMath/Quasiconformal/LocalSobolev.lean
JJMath/Quasiconformal/ConformalChange.lean
JJMath/Quasiconformal/Mobius.lean
JJMath/Quasiconformal/Basic.lean
JJMath/Quasiconformal/Examples.lean
JJMath/Quasiconformal/Beltrami.lean
JJMath/Quasiconformal/SquareBoundary.lean
JJMath/Quasiconformal/ChangeOfVariables.lean
JJMath/Quasiconformal/CondenserCapacity.lean
JJMath/Quasiconformal/Compactness.lean
JJMath/Quasiconformal/CauchyTransform.lean
JJMath/Quasiconformal/BeurlingTransform.lean
JJMath/Quasiconformal/SobolevBeurling.lean
JJMath/Quasiconformal/SobolevMorrey.lean
JJMath/Quasiconformal/PrincipalSolution.lean
JJMath/Quasiconformal/OpenDiscrete.lean
JJMath/Quasiconformal/RiemannSphere.lean
JJMath/Quasiconformal/MeasurableRiemannMapping.lean
JJMath/Quasiconformal/Surface.lean
JJMath/Quasiconformal.lean
handwave/quasiconformal.hw.md
```

The implemented core keeps planar orientation in
`JJMath/Topology/PlanarDegree.lean` and the initial Beltrami predicates in
`LocalSobolev.lean`; `ConformalChange.lean` contains the first sphere-chart
calculus, while `Mobius.lean` packages arbitrary finite projective changes and
`RiemannSphere.lean` defines chartwise sphere quasiconformality and proves the
projective Möbius regression theorem. Separate
`Orientation.lean` and `Beltrami.lean` files are not needed until those APIs
grow. `Examples.lean` is part of the umbrella and serves as an end-to-end
definition regression test.

Put the new declarations in `JJMath.Quasiconformal`; qualify the older
Sobolev results that currently live in `JJMath.Uniformization` rather than
extending that historical namespace further.

Keep `Surface.lean` out of the umbrella import until the planar and sphere
theorems are stable if its chart bookkeeping becomes expensive.

## Dependency spine

```text
real-linear Wirtinger algebra
        |
        +--> local W¹,² API --> planar quasiregular/quasiconformal definitions
        |                              |
        |                              +--> Sobolev area/inverse/chain rules
        |                                           |
        |                                           +--> condenser distortion
        |                                                        |
        |                                                        +--> normalized compactness
        |
        +--> Cauchy transform --> Beurling Lᵖ theory --> principal solutions
                                                                  |
normalized compactness + principal solutions + truncation --------+--> measurable Riemann mapping
                                                                        |
                                                                        +--> surface/chartwise API
```

The two difficult branches, compactness and principal solutions, can be
developed independently after the small core is in place.

## Hard-first implementation milestones

### Milestone 0: honest theorem skeleton and algebraic spike

Create the module tree, public definitions, and theorem stubs with `by sorry`.
Do not hide missing work in a package structure or conditional theorem.  Every
stub must have precise `%%handwave` metadata.

Prove the complete finite-dimensional linear algebra first:

- real-linear Wirtinger decomposition;
- determinant/Jacobian formula;
- operator norm formula;
- $|L_{\bar z}|\le k|L_z|$ if and only if
  $\lVert L\rVert^2\le K(k)J(L)$;
- behavior under complex-linear pre- and postcomposition;
- inverse formulas when $J(L)>0$.

This is a small but valuable compilation spike: it fixes norm conventions and
the exact algebraic shape of all later almost-everywhere statements.

### Milestone 1: local Sobolev and topological core

**Status: complete.**

Add:

- `IsLocalW12On` for complex-valued planar maps;
- restriction and compact-exhaustion characterizations;
- uniqueness of the weak differential almost everywhere;
- weak Wirtinger derivatives $\partial_z f$ and $\partial_{\bar z}f$;
- local Beltrami equation and essential coefficient bound;
- planar-domain homeomorphism ambient lift;
- topological orientation via local degree;
- canonical $K$-quasiconformal definition;
- the analytic bounded-distortion predicate and the continuous strictly
  nonconstant $K$-quasiregular predicate;
- invariance under conformal affine maps and reciprocal sphere-chart changes;
- projective finite Möbius coordinate-change laws and a chartwise sphere
  predicate;
- locality under chart restriction and the theorem that projective Möbius
  homeomorphisms are $1$-quasiconformal.

Do not yet attempt general Riemann-surface maps.  Test the API on affine maps
$z\mapsto az+b\bar z+c$, complex affine maps, conjugation, inversion away from
zero, and M\"obius maps.

### Milestone 2: attack normalized compactness before easy closure results

**Status: area, inverse, planar capacity distortion, exact model ring
capacity, continuum separation, and equicontinuity at the three normalization
points are complete.** The local Sobolev, Lusin $N$, approximate-differentiability,
Lusin--Whitney, area-formula, inverse-candidate, planar Piola,
inverse-orientation, inverse-distortion, continuous Sobolev pullback, and
two-sided planar capacity-distortion, polar assembly, and exact concentric
ring-capacity parts are all complete. The finite chart of a normalized sphere
homeomorphism is now a whole-plane homeomorphism fixing $0$ and $1$; the
positive ray is used as the outer plate; and the capacity squeeze proves a
uniform finite-chart modulus of continuity at $0$. Normalized continuum
separation and the reciprocal-coordinate arguments give the corresponding
control at $1$ and $\infty$, so this compactness interface is complete.

#### Lusin--Whitney construction

**Completed.** The proof uses measurable ambient representatives on a
full-measure density core, measurable dyadic density and affine defects,
simultaneous Egorov uniformization on bounded exhaustions at tolerances
$1/(k+1)$, and a countable measurable continuity cover of the differential.
For two nearby points in one uniform piece, a comparable dyadic radius and a
midpoint ball of relative volume $3/16$ leave a common point outside the two
affine-error sets and the density defect once each defect is below $1/16$.
Splitting the affine remainder through that point gives the derivative within
the piece. Pairing the exhaustion, Egorov, and continuity-cover indices then
produces the required countable measurable cover up to a null set.

This completes the repository-aligned route from local $W^{1,2}$ to
approximate differentiability, then to within-differentiability pieces, and
finally to Mathlib's Jacobian theorem. Ambient Fréchet differentiability almost
everywhere is neither asserted nor needed.

The area and inverse dependency chain is now:

1. Coordinate ACL — complete.  The scalar product-strip bridge, cutoff
   localization, complex reconstruction, volume-preserving real-linear
   coordinate transport, and the planar horizontal and vertical statements
   are all proved.  The line derivatives are exactly $Df(1)$ and $Df(i)$.
2. Prove Lusin $N$ for planar local $W^{1,2}$ homeomorphisms by a selected
   rectangle-boundary energy estimate — complete.  The
   complex fundamental theorem, endpoint and image-diameter inequalities,
   four-side ACL assembly, compact planar estimate
   $|A|\leq\operatorname{diam}(\partial A)^2$, and ambient-homeomorphism
   rectangle estimate are all proved.  This route needs neither the radial
   ball-trace theory nor a Jordan-curve/isoperimetric theorem.  The four
   strip-average bounds are now combined with the boundary estimate, and the
   geometric area estimate now applies directly to homeomorphisms between
   planar domains.  The concentric-square specialization and source-translation
   step are complete: for every sufficiently small square $Q$ whose doubled
   square lies in the source,
   $|f(Q)|\leq64\int_{2Q}\lVert Df\rVert^2$.  Absolute continuity of the
   product-coordinate energy measure, a fine finite integer-grid cover, and a
   modulo-four coloring in each coordinate bound the total doubled-square
   energy by sixteen times the energy of a chosen neighborhood.  This proves
   the compact-null theorem. Ambient-image measurability and inner regularity
   then give the full Lusin $N$ property for arbitrary null subsets of the
   open source domain.
3. Derive a scale-covariant local Poincare inequality — complete. Exact
   restricted $L^p$ transport under translation and dilation reduces every
   complex ball to the unit ball and gives a single finite constant in
   $\lVert u-a\rVert_2\leq Cr\lVert Du\rVert_2$. Local $W^{1,2}$ now implies
   local $L^1$ for both $u$ and $Du$, and localized Lebesgue differentiation
   gives their $L^1$ mean oscillation on centered balls almost everywhere.
   Mean-square differentiation of the coordinate pair $(Du(1),Du(i))$ and
   the inequality
   $\lVert L\rVert^2\leq2(\lVert L(1)\rVert^2+\lVert L(i)\rVert^2)$ now give
   the required $L^2$ operator-norm oscillation of $Du$. The complex-valued
   Poincare theorem is now proved and gives scale-dependent constants $a_r$
   with
   $\lVert u-Du(x)(\cdot-x)-a_r\rVert_{L^2(B(x,r))}=o(r^2)$.
   The explicit concentric-ball comparison is now proved. Local mean-square
   differentiation of $u$, together with the $O(r^2)$ norm of the affine
   term, identifies the centers by $a_r\to u(x)$; comparison at radii $r$
   and $r/2$ gives $\lVert a_r-a_{r/2}\rVert/r\to0$. Dyadic telescoping now
   upgrades these conclusions to $\lVert a_r-u(x)\rVert/r\to0$, and the
   triangle inequality gives the fixed-center $L^2$ remainder $o(r^2)$.
   A small-inner-ball split plus Chebyshev on the complementary annulus gives
   the relative-density condition in `HasApproxFDerivAt`, and local
   $W^{1,2}$ maps are approximately differentiable almost everywhere. The
   Lusin--Whitney theorem now decomposes almost all of the domain into
   countably many measurable pieces carrying `HasFDerivWithinAt`.
4. Sum Mathlib's differentiable area formula over those pieces. Lusin $N$
   removes the exceptional image. This assembly and the resulting Sobolev
   area formula are complete; ambient Fréchet differentiability is not
   required.
5. Define the candidate inverse weak differential by the total Wirtinger
   pseudoinverse of a measurable representative of $Df$, composed with
   $F^{-1}$ — complete. The area formula also proves directly that measurable
   zero-Jacobian source sets have null image.
6. Prove local $L^2$ bounds for that field by change of variables and the
   pointwise inverse-distortion theorem — complete. Transporting
   almost-everywhere properties through Lusin $N$ also proves the same
   $K$-distortion inequality for the candidate on the target. The oriented
   area formula is upgraded to Bochner integrals, and the candidate is
   identified as the inverse weak differential once the planar Sobolev Piola
   identity is supplied. The smooth half of that leaf is complete: the
   adjugate components are divergence-free by equality of mixed derivatives,
   and applying the resulting integration-by-parts theorem to
   $\chi(\varphi\circ T)$ gives the exact main term plus cutoff error for every
   smooth approximant $T$. The existing scalar graph-density theorem has now
   been applied to both real components and recombined into smooth planar maps
   $T_n$ with $T_n\to F$ and $DT_n\to Df$ in local $L^2$. The general bounded
   $L^2$ pairing estimate and the implication
   $\varphi(T_n)-\varphi(F)\to0$ in $L^2$ are also proved. The derivative of a
   fixed cutoff, adjugate evaluation, and the coordinate factor have now been
   packaged as a bounded compact multiplier; after splitting
   $DT_n=(DT_n-Df)+Df$, the localized cutoff-error integral is proved to tend
   to zero. Strong $L^2$ convergence of the differentials now gives strong
   $L^1$ convergence of their Jacobians. After extracting a subsequence on
   which $T_n\to F$ almost everywhere, dominated convergence passes the
   localized Jacobian main term to the limit. A cutoff equal to one, with zero
   differential, on $F^{-1}(\operatorname{supp}\varphi)$ now localizes the
   main, cutoff-error, and adjugate terms to one compact set. The smooth
   identity and uniqueness of limits prove the exact planar Sobolev Piola
   identity, and the cutoff is removed pointwise. Convergence of the linear
   adjugate side is proved for the full approximation sequence.
7. Separately prove that planar orientation preservation is inherited by the
   inverse — complete. The forward orientation witness is shrunk into a target
   disk, its normalized homotopy is lifted through the inverse, and the initial
   composite boundary is identified with the identity boundary. Inverse
   quasiconformality and $N^{-1}$ now follow.

In particular, do not infer inverse Sobolev regularity merely from an
almost-everywhere classical inverse derivative and an $L^2$ bound, and do not
claim that the forward area formula alone supplies $N^{-1}$.

This is the first deliberately hard vertical slice.  State the capstone first:

> Every sequence of $K$-quasiconformal self-homeomorphisms of the Riemann
> sphere fixing $0,1,\infty$ has a subsequence converging uniformly to a
> $K$-quasiconformal self-homeomorphism, and the inverse subsequence converges
> uniformly to its inverse.

Use condenser capacity rather than introducing a full theory of rectifiable
curve families.  After the area/inverse chain above, the required compactness
leaves are:

1. Define planar and spherical condenser capacity as an infimum of Dirichlet
   energies of local Sobolev competitors. **Planar definition complete;
   spherical globalization remains.** The planar capacity uses continuous
   real-valued local $W^{1,2}$ representatives with pointwise values $0$ and
   $1$ on the two plates and extended nonnegative Dirichlet energy, so an
   empty admissible family correctly has capacity $\infty$.
2. Prove density/truncation so that admissible competitors can be composed
   with quasiconformal maps. **Complete, including the continuous local
   Sobolev outer chain rule.** The differential of a smooth compactly supported outer
   function is globally Lipschitz.  Along a common smooth graph approximation
   $T_n\to F$, $DT_n\to DF$, the nonlinear derivative error splits into
   $(Du(T_n)-Du(F))[DF]$ and $Du(T_n)[DT_n-DF]$; both terms vanish as bounded
   $L^2$ pairings.  This proves
   $D(u\circ F)=(Du\circ F)\circ DF$ distributionally and gives the full
   local $W^{1,2}$ conclusion for smooth compactly supported $u$.
   Consequently a smooth compactly supported target condenser competitor
   pulls back to an actual source competitor, with its Dirichlet energy
   bounded by $K$ times the target energy.

   For a continuous scalar Sobolev function, compactness of a target
   neighborhood now supplies a bounded interval containing its values and a
   smooth compactly supported scalar retraction equal to the identity, with
   identity differential, on that interval.  From any smooth Sobolev graph
   approximation, a subsequence of the retracted approximants converges to the
   original function almost everywhere, while its actual chain-rule
   differentials converge to the weak differential strongly in $L^2$.  The
   proof splits the error into a graph-norm term and an almost-everywhere term
   dominated by the fixed weak differential.

   The local chain rule for a continuous real-valued
   $W^{1,2}_{\mathrm{loc}}$ outer function is now proved. For the
   support $K$ of a source test function, choose a compact target neighborhood
   of $F(K)$, apply the retracted approximation there, and multiply by a fixed
   target cutoff equal to one near $F(K)$. Each resulting outer function is
   smooth and compactly supported, so the completed smooth pullback theorem
   applies. Lusin $N^{-1}$ transports almost-everywhere value convergence to
   $K$, where boundedness gives dominated convergence. The quasiconformal
   covector-energy inequality transports the target $L^2$ differential error
   to the source. This proves
   $D(u\circ F)=(Du\circ F)\circ DF$ locally and gives the required local
   $L^2$ bounds without any unweighted $L^2$ composition theorem. It directly
   constructs the pullback of every continuous Sobolev condenser competitor.

   Global $[0,1]$ truncation is therefore not a prerequisite for the pullback
   theorem: continuity bounds the range on every compact neighborhood used by
   a test. A separate truncation lemma may still be useful for normalizing the
   variational class, but it is no longer on the critical dependency path.
3. Prove the quasiconformal energy pullback inequality and hence
   $K^{-1}\operatorname{cap}(E,D)\le
   \operatorname{cap}(fE,fD)\le K\operatorname{cap}(E,D)$.
   **Complete for the full continuous-Sobolev variational class:** for every
   target covector field $a$,
   $$
     \int_\Omega\lVert a(F(z))\circ DF(z)\rVert^2\,dz
       \le K\int_{\Omega'}\lVert a(y)\rVert^2\,dy.
   $$
   The same estimate constructs and controls the pullback of every continuous
   Sobolev admissible competitor. Taking infima proves one capacity inequality;
   applying it to the proved $K$-quasiconformal inverse gives the reverse
   inequality.
4. Compute the capacity of a round annulus explicitly. **Complete.**
   Complex-affine invariance reduces the model to the radius ratio. The
   logarithmic cutoff gives the upper bound. For the lower bound,
   endpoint-preserving radial ACL and weighted Cauchy--Schwarz give a
   measurable ray-energy estimate; the Haar polar decomposition has angular
   mass $2\pi$ and radial measure $t\,dt$; and planar Dirichlet energy is
   invariant under dilation. Hence every competitor has energy at least the
   logarithmic value, and
   $$
     \operatorname{cap}(r,R)=\frac{2\pi}{\log R-\log r}
     \qquad (0<r<R).
   $$
5. Prove the normalized continuum-separation lower bound. **Complete.**
   For each $\delta>0$ there is $c(\delta)>0$ such that
   $$
     c(\delta)\leq\operatorname{cap}_{\mathbb C}(E_0,E_1)
   $$
   whenever $E_0$ is compact and connected, contains $0$, and reaches
   modulus $\delta$, while $E_1$ is closed and connected, contains $1$, and
   is unbounded. The direct circle-and-ray proof selects two good circles and
   one good radial ray, then obtains $1\leq C(\delta)E^{1/2}$ for every
   admissible potential. Extended-real square-root cancellation and the
   variational infimum give the positive capacity bound.

   The downstream interface is complete. The finite chart is all of
   $\mathbb C$, the image of $[1,\infty)$ is a normalized outer continuum,
   the image of a closed disk is a normalized inner continuum, and capacity
   distortion gives
   $$
     c(\delta)\leq K\operatorname{cap}(r,1).
   $$
   Since $\operatorname{cap}(e^{-n},1)=2\pi/n$, this proves uniform
   finite-chart equicontinuity at $0$.
6. Globalize the chartwise estimate to equicontinuity on the sphere, then
   apply the same argument to normalized inverses. **Complete.** Reciprocal
   coordinates handle $\infty$. At the second normalized finite point, the
   involution $T(z)=1-z$ conjugates the estimate exactly to the already proved
   origin modulus; no second continuum-separation argument is used. At every
   other nonzero finite point $x$, the affine maps $B_x(z)=x(1-z)$ and
   $B_{f(x)}^{-1}$ reduce the centered condenser to the normalized origin
   condenser. Reciprocal control of inverse maps gives the required uniform
   bound on $|f(x)|$. The resulting family and its inverse family are
   equicontinuous everywhere and therefore uniformly equicontinuous on the
   compact sphere.
7. Feed that result into the existing Arzelà--Ascoli theorem in
   [`RadoSecondCountable.lean`](JJMath/Uniformization/RadoSecondCountable.lean).
   **Complete for the topological step.** A common subsequence of the maps and
   inverses converges uniformly; the two limits are inverse continuous maps,
   hence form a normalized sphere homeomorphism. No quasiconformality of the
   limit is asserted yet.
8. Derive uniform local Dirichlet-energy bounds. **Complete by a shorter
   finite-chart route.** For every measurable $E$ in a planar source,
   distortion and the oriented area formula give
   $$
     \int_E\lVert Df\rVert_{\mathrm{op}}^2
       \leq K\,|f(E)|.
   $$
   Reciprocal control of the inverse family places the image of every fixed
   source disk in one fixed target disk. Hence the chartwise weak
   differentials have a common finite $L^2$ bound on each fixed disk. An
   intrinsic spherical-energy formalization is unnecessary for compactness.
9. Use the existing weak Hilbert subsequence theorem to retain weak
   differentials on the exhaustion $\overline B(0,n)$. **Complete.**
   Evaluation of $Df_n$ at the real coordinate vectors $1$ and $i$ produces
   two complex-valued $L^2$ fields. One countable diagonal extraction gives
   weak limits on every integer disk, and bounded restriction maps show that
   these limits agree on nested disks. Spherical uniform convergence and the
   uniform finite-chart bound give strong local $L^2$ convergence of the map
   values. Passing the distributional test-function identities identifies
   each diskwise limit as the weak differential of the finite-chart limit;
   the compatible coordinate fields then glue to a whole-plane weak
   differential with locally finite $L^2$ norm. Local Rellich compactness is
   available but is not needed to identify the already-uniform limit.
10. Close the relevant analytic equation under this convergence. There are
    two distinct targets:

    - General nonlinear $K$-distortion closure requires distributional weak
      continuity of the two-dimensional Jacobian together with a localized
      lower-semicontinuity argument, or an equivalence with a closed
      capacity-distortion formulation. The pointwise inequality cannot be
      inferred directly from weak derivative convergence.
    - For the prescribed-coefficient construction, the shorter linear route
      is **complete**. Bounded multiplication by a measurable
      $\mu\in L^\infty$ is weakly continuous on $L^2$, diskwise eventual
      equality survives the normalized diagonal subsequence, and the disk
      conclusions globalize to $\mathbb C$. The bound $|\mu|\leq k<1$ then
      recovers the distortion inequality algebraically with
      $K=(1+k)/(1-k)$.

The prescribed-coefficient compactness route is complete. Planar orientation
is preserved by compact-local uniform homeomorphic limits. Inversion
conjugation supplies whole-plane reciprocal Sobolev data and the transformed
Beltrami equation; applying compactness to the conjugated sequence gives both
diagonal standard charts for the same spherical limit. The two mixed charts
are restrictions of the finite chart followed or preceded by conformal
inversion on $\mathbb C^\times$. Consequently an almost-everywhere convergent,
uniformly bounded coefficient sequence has a normalized quasiconformal sphere
limit in all four standard chart pairs. Stronger coefficient-free nonlinear
finite-distortion closure remains desirable but is not a prerequisite for
truncating a prescribed coefficient.

### Milestone 3: principal solutions for compactly supported coefficients

Develop the analytic construction on the plane.

The Fourier audit found a strong existing $L^2$ foundation in Mathlib:
`MeasureTheory.Lp.fourierTransformₗᵢ` is a unitary Fourier transform,
Plancherel and compatibility with Schwartz functions are proved, Schwartz
functions are dense in $L^2$, and directional derivatives have the expected
$2\pi i\langle\xi,v\rangle$ multiplier. Mathlib's generic multiplier on
Schwartz functions and tempered distributions is not the right definition
for the Beurling operator: its symbol is singular at the origin and does not
preserve the Schwartz class. The implemented route instead multiplies
directly by the measurable unit-modulus symbol in $L^2$ and conjugates by the
unitary Fourier transform. No existing theorem provides the required
$L^p$, $p>2$, singular-integral estimate.

1. **Complete.** The normalized Cauchy transform is defined on smooth
   compactly supported functions, its kernel is locally integrable, and its
   integrand is absolutely integrable. Smooth regularization of $1/z$,
   integration by parts, a normalized radial approximate identity, and
   dominated convergence prove
   $\partial_{\bar z}(1/(\pi z))=\delta_0$. Translation and differentiation
   through convolution then show that $\mathcal Cg$ is smooth and that
   $\partial_{\bar z}\mathcal Cg=g$ pointwise. The other component satisfies
   $\partial_z\mathcal Cg=\mathcal C(\partial_zg)$ pointwise, and
   $\mathcal Cg(z)=O(|z|^{-1})$ outside a disk containing the support. On the
   Fourier side the exact identity
   $\mathcal S(\partial_{\bar z}\varphi)=\partial_z\varphi$ is proved for every
   test function. Multiplication by ordinary smooth dilated cutoffs gives the
   exact formula
   $\partial_{\bar z}(\beta_R\mathcal Cg)-g
     =(\partial_{\bar z}\beta_R)\mathcal Cg$
   once the inner disk contains the support. The $O(|z|^{-1})$ far-field bound
   and uniform $O(R^{-1})$ cutoff-derivative bound make this error pointwise
   $O(R^{-2})$ on a disk of area $O(R^2)$, hence $O(R^{-1})$ in $L^2$.
   Beurling isometry and comparison on arbitrary fixed disks then prove
   $\partial_z\mathcal Cg=\mathcal Sg$ almost everywhere. The full local
   $W^{1,2}$ wrapper is assembled; logarithmic Sobolev cutoffs and a separate
   graph-density argument are unnecessary.
2. **Complete.** Define the Beurling transform $\mathcal S$ on planar $L^2$
   by the Fourier multiplier
   $m(0)=1$, $m(\xi)=\overline\xi/\xi$ for $\xi\ne0$, and prove its $L^2$
   isometry by Plancherel. The formulas
   $\mathcal F(\partial_zf)=\pi i\overline\xi\,\mathcal Ff$ and
   $\mathcal F(\partial_{\bar z}f)=\pi i\xi\,\mathcal Ff$ are also proved on
   Schwartz functions as convention regression tests.
3. **Complete in $L^2$.** Pointwise multiplication satisfies
   $\lVert M_\mu\rVert_{2\to2}\leq\lVert\mu\rVert_\infty$, so
   $I-M_\mu\mathcal S$ is inverted by a norm-convergent Neumann series when
   $\lVert\mu\rVert_\infty<1$. Every $g\in L^2$ has a unique solution of
   $h-\mu\mathcal Sh=g$. A bounded measurable coefficient vanishing almost
   everywhere outside a disk is proved to lie in $L^2$, giving the required
   particular equation $h-\mu\mathcal Sh=\mu$.
4. **Complete through a strict $L^r$ contraction above exponent two.** The
   Calderón--Zygmund decomposition, physical/Fourier
   identification, weak $(1,1)$ extension, high/low distribution estimate,
   layer cake, both Tonelli tail identities, and dense completion now give a
   bounded complex-linear Beurling transform on every $L^p(\mathbb C)$ with
   $1<p<2$. For the complex-bilinear pairing
   $B(f,g)=\int_{\mathbb C}fg$, Fourier transform and inverse Fourier transform
   are now proved self-transpose on $L^2$ by Schwartz density. Reflection
   satisfies $\mathcal F^{-1}=R\mathcal F$, the Beurling symbol is even, and
   its multiplier commutes with $R$; consequently
   $B(\mathcal Sf,g)=B(f,\mathcal Sg)$ on $L^2$. Compatibility transfers the
   same integral identity to $L^1\cap L^2$ inputs, including all finite-support
   simple functions.

   The quantitative $L^p$ duality theorem is now formalized in a reusable
   harmonic-analysis module. For $q\ge2$, it constructs
   $$N_q(z)=|z|^{q-2}\overline z,$$
   proves $zN_q(z)=|z|^q$ and $|N_q(z)|=|z|^{q-1}$, and restricts
   $N_q\circ h$ to the finite-measure sets
   $$E_n=S_n\cap\{|h|\le n\}.$$
   The resulting functions $g_n=\mathbf1_{E_n}N_q(h)$ are strongly
   measurable, lie in every finite $L^r$, and, for Hölder-conjugate $p,q$,
   satisfy
   $$h g_n=\mathbf1_{E_n}|h|^q,
     \qquad |g_n|^p=\mathbf1_{E_n}|h|^q,$$
   together with the exact formula
   $$\|g_n\|_p=\left(\int_{E_n}|h|^q\right)^{1/p}.$$

   Applying this theorem to the weak transform of a finite-support
   $F\in L^q$, bilinear symmetry moves the transform onto an arbitrary
   $L^p$ simple test function. Compatibility there with the completed
   lower-exponent transform, Hölder's inequality, and its bound $A_p$ give
   $$
     \left|\int (\mathcal SF)s\right|
       \leq A_p\|F\|_q\|s\|_p.
   $$
   Quantitative duality therefore yields
   $\mathcal SF\in L^q$ and $\|\mathcal SF\|_q\leq A_p\|F\|_q$.
   Linearity of the weak transform packages this construction as a bounded
   linear map on finite-support $L^q$ simple functions; dense extension now
   gives a continuous complex-linear Beurling transform on all planar
   $L^q$ with the same norm bound.

   Compatibility on the dense common core is now recorded: for every
   finite-support simple input, both the below-two and above-two completed
   transforms agree almost everywhere with the exact Fourier-multiplier
   $L^2$ transform. This is the compatibility actually needed for
   interpolation; proving equality of the completed operators on their full
   intersections with $L^2$ can be deferred unless a later API requires it.
   A reusable bilinear Riesz--Thorin theorem is now proved on the common
   finite-support simple core. Its analytic deformation starts from
   $$
     a(z)=\frac r{p_0}(1-z)+\frac r{p_1}z,
     \qquad
     w_z=\begin{cases}0,&w=0,\\(w/|w|)|w|^{a(z)},&w\ne0,
     \end{cases}
   $$
   the map $z\mapsto w_z$ is entire, its norm on the closed strip is
   $|w|^{\operatorname{Re}a(z)}$, and the reciprocal-exponent identity gives
   $w_\theta=w$. Applying this valuewise preserves integrable simple
   functions. Normalized $L^r$ simple functions have norm exactly one on
   both endpoint lines. Each deformation is expanded over its finitely many
   nonzero value fibers. Consequently every complex-bilinear pairing of two
   deformations is a finite double sum of entire scalar coefficients, is
   uniformly bounded on the closed strip, and satisfies Hadamard's
   three-lines estimate. Normalization and the zero-seminorm cases then give
   the full simple-core bound
   $$
     |B(f,g)|\leq A^{1-\theta}C^\theta\|f\|_r\|g\|_s.
   $$

   The Beurling-specific instantiation is complete. Integrable planar simple functions are
   included complex-linearly into $L^2$, and the common pairing is defined
   using the exact Fourier multiplier. It has the $L^2\times L^2$ endpoint
   with constant one and the $L^q\times L^{q'}$ endpoint supplied by the
   completed above-two transform. Interpolation followed by quantitative
   duality proves
   $$
     \|\mathcal Sf\|_r\leq A_p^\theta\|f\|_r
   $$
   for every integrable simple $f$, whenever
   $1/r=(1-\theta)/2+\theta/q$. This estimate has now been transferred to
   finite-support $L^r$ simple functions and extended by density to a bounded
   complex-linear operator on all planar $L^r$, with the same norm bound and
   exact compatibility on the simple $L^2$ core.

   Fixing $p=3/2$ and $q=3$, continuity of
   $\theta\mapsto kA_{3/2}^\theta$ at zero gives, for every $k<1$, a
   parameter $0<\theta<1$ such that $kA_{3/2}^\theta<1$. The exponent
   $$
     r_\theta=\left(\frac{1-\theta}{2}+\frac\theta3\right)^{-1}
   $$
   satisfies $2<r_\theta<3$. Pointwise multiplication by
   $\mu\in L^\infty$ is now implemented on every such $L^r$, and the
   composition satisfies
   $$
     \|M_\mu\mathcal S_{r_\theta}\|
       \leq\|\mu\|_\infty A_{3/2}^\theta<1.
   $$
5. **Complete at the operator level.** The corresponding $L^p$ Neumann
   solution exists uniquely. On $L^p\cap L^2$ the interpolated Beurling
   transform agrees almost everywhere with the exact $L^2$ transform.
   Compact support of $\mu$ lowers the product term to $L^2$, so the
   $L^p$ solution itself lies in $L^2$ and equals the unique Hilbert-space
   solution. The parameter choice and $L^p$ membership of a raw compactly
   supported coefficient are now packaged as well. The equation also now
   records explicitly that $h$ has the same disk support as $mu$.
6. **Analytic principal-solution construction complete.** For disk-supported
   $h\in L^p$, $p>2$, the conjugate exponent $q<2$ makes every compactly
   truncated Cauchy kernel an $L^q$ function. Hölder therefore makes
   $$
     \mathcal C_ph(z)=\frac1\pi\int_{\mathbb C}\frac{h(w)}{z-w}\,dw
   $$
   an honest integral at every point. Support-controlled smooth $L^p$
   approximation and a center-independent local $L^q$ kernel bound give
   local uniform convergence of smooth Cauchy transforms, hence continuity
   of $\mathcal C_ph$. The far-field estimate gives
   $\mathcal C_ph(z)\to0$ as $|z|\to\infty$. Common-support $L^p$
   approximation lowers to $L^2$ convergence, the Beurling isometry controls
   the holomorphic derivative, and compact-uniform convergence controls the
   potentials locally in $L^2$. Diskwise weak-derivative closure and
   exhaustion now prove
   $\partial_{\bar z}\mathcal C_ph=h$ and
   $\partial_z\mathcal C_ph=\mathcal S_2h$. Compatibility with the near-$2$
   transform converts the Neumann equation into
   $h=\mu(1+\mathcal S_2h)$. Thus $z+\mathcal C_ph(z)$ is continuous,
   belongs to $W^{1,2}_{\mathrm{loc}}$, satisfies the prescribed weak
   Beltrami equation and the $K=(1+k)/(1-k)$ distortion inequality almost
   everywhere, and is asymptotic to the identity at infinity. The latter
   implies $|f(z)|\to\infty$, so the principal map is proper.
7. **Beltrami reduction complete; the Reshetnyak core remains.** The exact
   planar Reshetnyak theorem is stated directly: a nonconstant continuous
   local $W^{1,2}$ map with $|Df|^2\le KJ_f$, $K\ge1$, is open, has discrete
   fibers, and has positive integer local indices. The first noncircular
   analytic reduction is now proved. The coefficient
   $$
     \mu=\begin{cases}
       0,&\partial_zf=0,\\
       \partial_{\bar z}f/\partial_zf,&\partial_zf\ne0
     \end{cases}
   $$
   is measurable up to a null set, satisfies
   $\partial_{\bar z}f=\mu\,\partial_zf$, and obeys
   $|\mu|\le(K-1)/(K+1)<1$ almost everywhere.
   The same pointwise reduction now also proves $J_f\ge0$ almost everywhere
   and $Df=0$ almost everywhere on the zero-Jacobian set.

   The remaining proof should not call the existing condenser-distortion
   theorem, because that theorem assumes a homeomorphism and would make the
   argument circular.

   The local higher-integrability route is complete. Smooth cutoff
   localization gives the whole-plane Sobolev--Beurling identity and the
   inhomogeneous equation
   $$
     h-\mu_\chi\mathcal S_2h=G_{\chi,f,\mu},
     \qquad h=\partial_{\bar z}(\chi f).
   $$
   Here $\mu_\chi$ is measurable, has the same essential bound as $\mu$,
   and is supported in a disk; the cutoff error is bounded, measurable,
   disk-supported, and hence belongs to every $L^p$. The near-$2$ resolvent
   solution is therefore available and also lies in $L^2$. Uniqueness of
   the $L^2$ solution identifies it with $h$, while compatibility of the
   $L^p$ and $L^2$ Beurling transforms gives both Wirtinger derivatives in
   $L^p$. Thus every compact $Q\subset\Omega$ admits some $2<p<3$ for which
   $Df\in L^p(Q)$.

   The remaining noncircular route is now:

   1. **Planar Morrey/Lusin layer complete.**
      `SobolevMorrey.lean` derives the scale-covariant $L^p$ Poincaré
      estimate, the dyadic Campanato convergence theorem, and the local
      Morrey estimate for every $p>2$. The original finite-grid argument
      remains available and proves compact-null preservation.

      For the full noninjective Lusin property, the sharper same-ball route
      avoids the enlarged-ball overlap problem. A radial geometric chain
      inside $\overline B(c,r)$ gives
      $$
        \operatorname{diam}f(\overline B(c,r))
          \leq C_p
            \|Df\|_{L^p(\overline B(c,r))}
            r^{1-2/p},
      $$
      using only the energy of that same ball. Consequently
      $$
        |f(\overline B(c,r))|
          \leq C_p^2
          \left(
            |\overline B(c,r)|
            +\int_{\overline B(c,r)}|Df|^p
          \right).
      $$
      Restricting the finite measure
      $|A|+\int_A|Df|^p$ to a compact ball, the Besicovitch covering theorem
      now covers any null subset by countably many admissible same-ball
      estimates with arbitrarily small total mass. This proves bounded
      null-set preservation directly, without injectivity or measurable
      selection. Closed-ball exhaustion upgrades it to the full
      `HasLusinNOn` property. Combining this with the completed local
      higher-integrability theorem proves Lusin $N$ for every continuous
      whole-plane map of bounded distortion;
   2. **The analytic multiplicity formula is complete; connect it to
      degree.**
      `ChangeOfVariables.lean` now defines
      $N(f,S,y)=\#(S\cap f^{-1}(y))$ with values in $[0,\infty]$.
      On a measurable set where the relative differential exists and has
      positive Jacobian, Mathlib's quantitative linear-approximation
      partition can be chosen with error below half the inverse norm. This
      gives countably many measurable injective sheets. Their indicator
      count is proved equal to the actual fiber cardinality, and summing the
      injective area formula gives
      $$
        \int_{\mathbb C}N(f,S,y)g(y)\,dy
          =\int_S J_f(x)g(f(x))\,dx.
      $$
      The formula now also holds when $J_f\geq0$: split off the
      zero-Jacobian locus and apply Mathlib's fixed-dimensional Sard lemma
      to show that its image is null.

      The countable assembly is now also complete. It replaces the
      Lusin--Whitney cover by disjoint differences, decomposes every
      positive-Jacobian part into injective sheets, pairs the two countable
      indices, and uses Lusin $N$ to remove the source-null remainder. A
      globally measurable weak-differential representative is clipped to
      the nonnegative-Jacobian branch and then identified with the original
      field off one measurable null set. Consequently every continuous
      whole-plane map of bounded distortion satisfies, for every measurable
      $S$,
      $$
        \int_{\mathbb C}N(f,S,y)g(y)\,dy
          =\int_S J_f(x)g(f(x))\,dx.
      $$

      The corresponding noninjective pullback-energy estimate is complete:
      for a measurable covector field $a$,
      $$
        \int_S\lVert a(f(x))\circ Df(x)\rVert^2\,dx
          \leq
        K\int_{\mathbb C}N(f,S,y)\lVert a(y)\rVert^2\,dy.
      $$
      An almost-everywhere bound $N(f,S,\cdot)\leq M<\infty$ therefore gives
      the condenser-ready estimate with constant $KM$.

      The regular-point sign layer is now complete. A real-linear map with
      positive Jacobian has the sharp lower bound
      $$
        (|\partial_zL|-|\partial_{\bar z}L|)|\xi|\leq|L\xi|,
      $$
      its affine boundary circles have index one, and a positive-Jacobian
      Fréchet regular point has a fiber-isolating circle of index one.
      Positive regular fibers are therefore discrete and locally finite.
      Combining this with the existing perforated-disk additivity theorem
      proves that an enclosing boundary circle has degree equal to the
      cardinality of any finite positive regular fiber.

      The disk-local regular-value count is now complete as well. For a
      smooth map and a positive regular target away from the outer boundary
      image, a localized finite family of isolating disks and smooth
      perforated-disk additivity prove that the boundary degree equals the
      number of preimages inside the disk, without assuming that the global
      fiber is finite or contained in the disk.

      A further audit rules out a tempting but invalid shortcut: arbitrary
      smooth approximation does not preserve $J\geq0$, so Sard alone only
      identifies the approximant's degree with a *signed* preimage count and
      cannot bound total multiplicity. The missing negative-orientation
      foundation is now complete: the negative unit circle has winding
      number $-1$, a negative-Jacobian regular point has local index $-1$,
      regular fibers of either sign are locally finite, and smooth
      perforated-disk additivity gives
      $$
        \operatorname{ind}(g|_{\partial B},y)
          =\sum_{x\in B\cap g^{-1}(y)}\operatorname{sgn}J_g(x)
      $$
      for every smooth regular value away from the boundary image. The
      negative-Jacobian locus now also has a countable measurable
      injective-sheet decomposition and its own multiplicity area formula
      with density $-J_g$. Sard's theorem therefore upgrades the preceding
      signed count to
      $$
        \deg(g,B,y)
          =\sum_{x\in B\cap g^{-1}(y)}\operatorname{sgn}J_g(x)
      $$
      for almost every target in any ball separated from
      $g(\partial B)$.

      The distributional-degree bridge is now complete. The extended-real
      positive- and negative-sheet identities have first been converted to
      ordinary real integrals. Integrating the almost-everywhere signed-count
      formula then gives the smooth identity. The standard localized
      mollifiers have been strengthened to converge simultaneously in the
      $W^{1,2}$ graph norm and uniformly on compact sets whenever the
      Sobolev map is continuous. Strong local $L^1$ convergence of the
      Jacobians and dominated convergence for the composed target test
      therefore pass the identity to continuous $W^{1,2}$ maps, while
      compact-uniform convergence preserves the protected boundary index.
      Thus, for target test functions supported away from the boundary
      image,
      $$
        \int_B J_f(x)\varphi(f(x))\,dx
          =
        \int_{\mathbb C}\deg(f,B,y)\varphi(y)\,dy.
      $$
      Comparing this distributional identity with the completed
      multiplicity area formula under $J_f\geq0$ is now complete:
      $N(f,B,y)=\deg(f,B,y)$ almost everywhere in every target ball
      separated from the boundary image. In particular, the multiplicity is
      integrable there and is bounded almost everywhere by the finite
      nonnegative boundary index. The anticipated separate good-radius
      boundary-null theorem is unnecessary: higher integrability already
      gives the full Lusin $N$ property, and every Euclidean circle is
      planar-null, so the image of every positive-radius circle is null.
      Compact separation plus positivity of target balls also upgrades the
      almost-everywhere comparison to the pointwise conclusion that every
      boundary index away from its boundary image is nonnegative. The
      condenser-facing pullback interface is now localized as well: if a
      measurable covector field is supported in such a protected target
      ball, its pullback energy over the source disk is at most $K$ times
      the finite disk index times its target energy. No multiplicity bound
      outside the field support is required;
   3. **Complete on the proper-map route.** A compact nontrivial fiber
      continuum has positive whole-plane capacity against a scaled positive
      source ray outside the proper inverse image of a fixed target disk.
      Globally smooth logarithmic target cutoffs compose with the Sobolev map,
      are constant on the two plates, and have weak differential supported
      in the protected source disk. The disk-degree pullback estimate bounds
      their energies by a fixed finite index times $O(1/n)$, contradicting
      positive capacity. Taking closures inside compact proper fibers proves
      that every connected subset of every fiber is a point. Arbitrary-domain
      local lightness remains useful, but the whole-plane nonproper theorem is
      now supplied instead by the completed analytic Stoilow route;
   4. **Complete on the proper principal-solution route.**
      The first local separation layer is proved: compact totally disconnected
      sets have arbitrarily small ambient neighborhoods whose boundaries miss
      the set, every light planar fiber has such neighborhoods locally, and
      passing to the component containing the base point preserves boundary
      avoidance while making the neighborhood connected and relatively
      compact. Directed intersections and compact clopen separation then
      produce a normal source domain $W$ and a protected radius $r>0$.

      The replacement for rough-domain Brouwer degree is now complete. The
      normal source domain supplies a smooth compactly supported cutoff
      $\chi$ with $\chi(x)=1$ and $D\chi=0$ over the protected closed target
      ball. The scalar Sobolev Piola identity gives
      $$
        \int_{\mathbb C}
          \chi(z)^2J_f(z)D\varphi(f(z))v\,dz=0.
      $$
      The source measure $\chi^2J_f\,dz$ is finite, its pushforward is
      absolutely continuous by the Sobolev area formula, and its
      Radon--Nikodym density belongs to $L^1$. A general distributional
      zero-gradient theorem, proved through the Euclidean Weyl lemma and
      Sobolev rigidity, makes that density constant on the target ball.
      Lightness implies strictly positive Jacobian mass on every source ball:
      otherwise $Df=0$ almost everywhere there and continuity makes $f$
      constant, contradicting lightness. This proves that the density
      constant is positive. If a point of the target ball were missing from
      the image of the compact cutoff support, a smaller target ball would
      have both zero pushforward mass and positive density. Thus the
      protected ball lies in the image, and every continuous light
      bounded-distortion map is open.

      The shorter analytic route to discreteness is also complete. Properness
      places a fiber and the inverse image of a protected target disk inside
      one source disk. The boundary of that disk is uniformly separated from
      the target, so its finite circle index equals source-disk multiplicity
      almost everywhere nearby. If the fiber contained arbitrarily many
      points, pairwise disjoint source neighborhoods and openness would force
      every sufficiently nearby target to have at least that many preimages,
      contradicting the finite almost-everywhere multiplicity. Thus proper
      fibers are finite and hence discrete.

      Finally, for any fiber-isolating disk, openness maps a smaller source
      disk onto a target neighborhood. Choose a target there where
      multiplicity equals the isolating circle index. Its multiplicity is
      nonzero, so that index, and therefore the local index, is strictly
      positive. The proper open/discrete theorem now uses only these proved
      analytic statements and does not call the general topological
      Whyburn--Stoilow theorem.

   Thus the prescribed-coefficient measurable Riemann mapping theorem has no
   remaining foundation gap. The whole-plane nonproper quasiregular theorem
   is now also proved by analytic Stoilow factorization. The all-purpose
   topological Whyburn--Stoilow statement remains a useful optional
   extension, but it lies on neither proof route.
8. **Degree and inversion assembly complete.**
   The exponential-cover construction supplies integer winding numbers,
   homotopy classification, concatenation additivity, circle indices,
   radius-independent local indices, and finite-fiber index sums. The finite
   geometric reduction is now complete: one simultaneously chooses pairwise
   disjoint isolating closed disks strictly inside the enclosing disk,
   removes their interiors, and smoothly approximates the original map on
   the resulting compact perforated disk by less than its positive distance
   to the target. Straight-line homotopy preserves every outer and inner
   circle index. Boundary additivity on the finite perforated disk is proved
   by multiplying $g-w$ by the coordinate vortices
   $\prod_i(q-c_i)^{-n_i}$. Product and integer-power laws make every inner
   boundary increment zero. Tietze extension fills those loops without
   introducing zeros, finite closed-cover gluing pastes the fillings across
   all holes, and radial contraction makes the corrected outer increment
   zero. Since every coordinate vortex has outer increment $2\pi i$, this
   gives $I_{\rm outer}(g-w)=\sum_i n_i$. The smooth approximation wrapper
   then yields the general continuous finite-fiber boundary formula.

   This route needs neither smoothness in its topological core,
   angular-form integration, nor a bespoke polygonal decomposition. Together
   with the remaining Reshetnyak interface, the asymptotic degree-one argument
   proves bijectivity, local index one, and preservation of the existing
   topological orientation predicate.
9. **Plane and sphere normalization assembled.** The compact-support analytic solution
   is now packaged as an orientation-preserving homeomorphism of
   $\mathbb C$, with its local $W^{1,2}$ differential, prescribed weak
   Beltrami equation, sharp $K(k)$ bound, and principal normalization. The
   complex-affine normalization sends the images of $0$ and $1$ back to
   $0$ and $1$. Its one-point extension is proved quasiconformal in the
   reciprocal chart: finite distorted area gives locally finite punctured
   $L^2$ energy, shrinking cutoffs remove the origin from the weak derivative
   identity, and the affine asymptotic gives a nonzero complex tangent which
   fills the topological orientation witness. Thus the normalized
   Riemann-sphere theorem for compactly supported coefficients is complete.

The compact-support principal-homeomorphism assembly is complete. Planar
Reshetnyak openness, finite fibers, and positive local index are proved on the
proper route; degree one at infinity then gives global inversion. The
finite perforated-disk boundary identity, analytic construction, spherical
extension, and orientation packaging are all formalized without a remaining
proof leaf.

### Milestone 4: measurable Riemann mapping theorem on the sphere

**Status: complete.**

Let $\mu_n=\mu\mathbf1_{\{|z|\le n\}}$.  Then:

1. **Complete.** Solve the compactly supported equation for each $\mu_n$;
2. **Complete.** Postcompose by the unique complex affine map sending
   $f_n(0),f_n(1),\infty$ to $0,1,\infty$;
3. **Complete.** Retain the same coefficient, orientation, and $K(k)$ bound
   under this normalization;
4. **Complete.** Extend each plane quasiconformal homeomorphism over infinity.
   In the reciprocal chart, pre- and postcomposition by inversion give the
   punctured quasiconformal map. The area formula bounds its $L^2$ energy on
   compact sets, shrinking smooth cutoffs remove the omitted origin from the
   distributional derivative identity, and the principal affine asymptotic
   supplies the nonzero tangent needed to preserve orientation at the filled
   point;
5. **Complete.** Apply normalized compactness
   simultaneously to $F_n$ and $F_n^{-1}$ and obtain a limiting sphere
   homeomorphism fixing $0,1,\infty$;
6. **Complete.** Extract weak local $L^2$ limits of the differential fields;
7. **Complete.** Pass to the equation
   $\partial_{\bar z}F_n=\mu_n\,\partial_zF_n$ using
   $\mu_n\to\mu$ almost everywhere, dominated convergence on test functions,
   and weak $L^2$ convergence of $DF_n$;
8. **Complete.** Conclude the distortion inequality, topological
   orientation, normalized spherical quasiconformality, and the prescribed
   Beltrami equation for the limit.

The varying-coefficient limit is a standalone reusable theorem. The
measurable Riemann mapping theorem is formally assembled from it and the
compact-support construction. Planar Reshetnyak openness/discreteness with
positive index, the perforated-disk boundary identity, and the spherical
isolated-point step are all fully proved.

After existence, prove normalized uniqueness.  If $F$ and $G$ have the same
coefficient, the composition $G\circ F^{-1}$ has vanishing Beltrami
coefficient, hence is a biholomorphic sphere automorphism.  The three fixed
points force it to be the identity.  This uses the quasiconformal inverse and
composition theorems from Milestone 2 and the existing affine classification
of automorphisms fixing infinity.

### Milestone 5: planar consequences

Add the standard working API:

- restriction to subdomains and locality;
- composition, inverse, and multiplicativity of maximal dilatation;
- conformal maps are $1$-quasiconformal;
- Beltrami coefficient of a composition and inverse;
- null-set preservation and change of variables;
- local higher integrability where it is already available from the
  principal-solution proof;
- normalized plane solutions and boundary behavior at infinity.

Avoid committing to a large boundary-extension theory until a concrete use
case requires prime ends or quasisymmetric boundary maps.

### Milestone 6: Riemann surfaces

**Status: in progress; the intrinsic differential and spherical MRMT
migration are complete.**

The new surface module mirrors the planar hierarchy. For an arbitrary map it
defines the maximal domain of each coordinate representation, chartwise
$K$-bounded distortion, and continuous strictly nonconstant
$K$-quasiregularity. For a homeomorphism it packages each coordinate
representation as an open partial homeomorphism and defines intrinsic
$K$-quasiconformality by the planar predicate on every chart pair.

The following pieces are complete:

- the coordinate-map and maximal-overlap-domain API;
- chartwise bounded distortion, quasiregularity, and their nonquantitative
  existential wrappers;
- coordinate partial homeomorphisms for surface homeomorphisms, including
  agreement of their ambient maps with the ordinary coordinate maps;
- the implication from intrinsic quasiconformality to quasiregularity on a
  nontrivial range;
- intrinsic closure under inverse with the same distortion constant;
- equivalence with the universal-domain planar predicate on $\mathbb C$;
- equivalence with the four finite/reciprocal standard-chart conditions on
  the Riemann sphere;
- the line bundle of $(p,q)$-differentials on an arbitrary complex
  one-manifold, including its chart transition law and coordinate
  representatives;
- Beltrami differentials as $(-1,1)$-differentials and quadratic
  differentials as $(2,0)$-differentials;
- chartwise measurability and essential norm bounds for intrinsic Beltrami
  differentials;
- realization of an intrinsic Beltrami differential by a surface
  homeomorphism through local weak equations;
- finite and reciprocal coordinate adapters on the sphere, with their
  compatibility derived from the bundle cocycle;
- an intrinsic quasiconformality and whole-sphere prescribed-coefficient
  conclusion in the normalized spherical measurable Riemann mapping theorem.

The next surface work should expose the locality hidden in the current
all-chart-pairs definition:

1. prove conformal transition maps are locally $1$-quasiconformal and that
   planar bounded distortion is invariant under their pre- and
   postcomposition;
2. prove it suffices to check one source/target chart pair near each point,
   and derive explicit invariance under replacing compatible holomorphic
   atlases;
3. add general pullback, tensor-product, conjugation, and composition
   operations for $(p,q)$-differentials, together with a useful analytic API
   for quadratic differentials;
4. prove intrinsic composition, with multiplication of maximal dilatations,
   once the corresponding planar Sobolev composition theorem is available;
5. formulate and prove prescribed-coefficient existence results on surfaces
   beyond the sphere once an appropriate global existence argument is in
   place.

Only after these are stable should the library consider maps between general
oriented two-dimensional real manifolds using chosen conformal structures.

## Explicit capstone theorem stubs

These are sketches of the intended Lean-facing statements.  Names and minor
type details may change after the Milestone 0 compilation spike, but the
mathematical content should not be weakened.

```lean
/--
%%handwave
name:
  Linear Beltrami bound and outer distortion
statement:
  Let $L:\mathbb C\to_{\mathbb R}\mathbb C$ be real linear and let
  $0\le k<1$. Then $|L_{\bar z}|\le k|L_z|$ if and only if
  $\|L\|_{\mathrm{op}}^2\le \frac{1+k}{1-k}\det_{\mathbb R}L$.
proof:
  Use $\|L\|_{\mathrm{op}}=|L_z|+|L_{\bar z}|$ and
  $\det_{\mathbb R}L=|L_z|^2-|L_{\bar z}|^2$, then factor both sides.
-/
theorem weakDBar_norm_le_iff_distortion
    (L : ℂ →L[ℝ] ℂ) {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1) :
    ‖weakDBar L‖ ≤ k * ‖weakDZ L‖ ↔
      ‖L‖ ^ 2 ≤ ((1 + k) / (1 - k)) * weakJacobian L := by
  sorry

/--
%%handwave
name:
  Compactness of normalized quasiconformal sphere maps
statement:
  Every sequence of orientation-preserving $K$-quasiconformal
  self-homeomorphisms of $\widehat{\mathbb C}$ fixing $0,1,\infty$ has a
  uniformly convergent subsequence whose limit is again an
  orientation-preserving $K$-quasiconformal self-homeomorphism fixing those
  three points; the corresponding inverses converge uniformly as well.
proof:
  Quasiconformal distortion of condenser capacity gives uniform
  equicontinuity of the maps and inverses. Apply Arzelà--Ascoli to both,
  identify the limits as inverse homeomorphisms, and use weak local Sobolev
  compactness to pass the distortion inequality to the limit.
-/
theorem normalized_quasiconformal_riemannSphere_compactness
    {K : ℝ} (hK : 1 ≤ K)
    (F : ℕ → RiemannSphere ≃ₜ RiemannSphere)
    (hqc : ∀ n, IsKQuasiconformalRiemannSphere K (F n))
    (hnorm : ∀ n, FixesZeroOneInfinity (F n)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ G : RiemannSphere ≃ₜ RiemannSphere,
        FixesZeroOneInfinity G ∧
        IsKQuasiconformalRiemannSphere K G ∧
        TendstoUniformly (fun n ↦ F (φ n)) G Filter.atTop ∧
        TendstoUniformly (fun n ↦ (F (φ n)).symm) G.symm Filter.atTop := by
  sorry

/--
%%handwave
name:
  Principal solution for a compactly supported Beltrami coefficient
statement:
  Let $\mu:\mathbb C\to\mathbb C$ be measurable, compactly supported, and
  satisfy $\|\mu\|_\infty\le k<1$. There is an orientation-preserving
  homeomorphism $f:\mathbb C\to\mathbb C$ with
  $f_{\bar z}=\mu f_z$ almost everywhere and $f(z)-z\to0$ as
  $z\to\infty$.
proof:
  Invert $I-M_\mu\mathcal S$ on a suitable $L^p$, $p>2$, set
  $f=z+\mathcal Ch$, and use quasiregular openness, discreteness, and degree
  one to obtain a homeomorphism.
-/
theorem exists_principalSolution_of_compactSupport
    (μ : ℂ → ℂ) {k : ℝ}
    (hμ : AEStronglyMeasurable μ MeasureTheory.volume)
    (hμsupp : ∃ R : ℝ, 0 ≤ R ∧
      ∀ᵐ z ∂MeasureTheory.volume, R ≤ ‖z‖ → μ z = 0)
    (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hbound : ∀ᵐ z ∂MeasureTheory.volume, ‖μ z‖ ≤ k) :
    ∃ f : ℂ ≃ₜ ℂ,
      HasBeltramiCoefficientOnPlane f μ ∧
      IsKQuasiconformalPlane ((1 + k) / (1 - k)) f ∧
      Filter.Tendsto (fun z ↦ f z - z) (cocompact ℂ) (𝓝 0) := by
  sorry

/--
%%handwave
name:
  Measurable Riemann mapping theorem on the sphere
statement:
  Let $\mu$ be a measurable Beltrami differential on the Riemann sphere with
  $\|\mu\|_\infty\le k<1$. There is an orientation-preserving
  $\frac{1+k}{1-k}$-quasiconformal homeomorphism of the Riemann sphere fixing
  $0,1,\infty$ whose Beltrami coefficient is $\mu$ on the whole sphere.
proof:
  Truncate the finite-coordinate representative to larger disks, solve the
  compactly supported equations, normalize the solutions, and promote the
  truncated coefficients to spherical Beltrami differentials. Intrinsic
  normalized compactness passes their chartwise almost-everywhere convergence
  to a quasiconformal limit realizing the original differential.
-/
theorem exists_normalized_riemannSphere_homeomorph_of_beltrami
    (μ : BeltramiDifferential RiemannSphere) {k : ℝ}
    (hμ : BeltramiDifferential.IsAEStronglyMeasurable μ)
    (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hbound : BeltramiDifferential.HasEssentialNormLE μ k) :
    ∃ F : RiemannSphere ≃ₜ RiemannSphere,
      ∃ _hFnorm : IsNormalizedRiemannSphereHomeomorph F,
        IsKQuasiconformalBetweenRiemannSurfaces ((1 + k) / (1 - k)) F ∧
        BeltramiDifferential.IsBeltramiDifferentialOf μ F := by
  sorry
```

Here `IsKQuasiconformalPlane` is the whole-plane specialization of the
domain predicate.  Using `AEStronglyMeasurable` makes the coefficient an
almost-everywhere object from the outset.

## Proof obligations that should not be hidden

The following tempting shortcuts would make the formal statements materially
weaker or nonstandard and should be avoided:

- Do not define orientation preservation as $J_f\ge0$ almost everywhere.
- Do not put the Beltrami equation into the definition of quasiconformality;
  prove it equivalent to the requested distortion inequality.
- Do not assume a prepackaged sequence of normalized solutions in the main
  theorem.  The compact-support principal-solution theorem must explicitly
  construct them.
- Do not assume equicontinuity or local uniform convergence as input to a
  “compactness” theorem.
- Do not use Mathlib's differentiable change-of-variables theorem directly on
  a Sobolev map without first proving the required differentiability/Lusin
  hypotheses or a Lipschitz decomposition.
- Do not model a sphere Beltrami coefficient as an unrelated scalar in both
  standard charts; enforce the reciprocal-chart cocycle law.
- Do not add axioms.  Analytic leaves that remain open should be theorem stubs
  with `by sorry` and precise Handwave metadata.

## Verification and documentation gates

For each milestone:

1. build the new leaf module before adding it to `JJMath/Quasiconformal.lean`;
2. run the Handwave validator and require `%%handwave` metadata on every new
   theorem, including support lemmas;
3. check that no new `axiom` declaration has appeared;
4. keep the principal theorem stubs visible in the dependency graph until
   their proofs are complete;
5. add affine, conformal, conjugation, and inverse examples as theorem-level
   regression tests;
6. only import `JJMath.Quasiconformal` from [`JJMath.lean`](JJMath.lean) after
   the umbrella module builds independently.

Create `handwave/quasiconformal.hw.md` once the algebraic and definition layer
is stable.  It should tell the mathematical story in the order

$$
\text{linear distortion}
\Longrightarrow \text{Sobolev quasiconformal maps}
\Longrightarrow \text{capacity distortion and compactness}
\Longrightarrow \text{principal solutions}
\Longrightarrow \text{measurable Riemann mapping}.
$$

## Current implementation target

Normalized prescribed-coefficient compactness is complete. The Fourier audit,
normalization choice, $L^2$ Beurling isometry, test-function Cauchy integral,
the two Schwartz Wirtinger-symbol formulas, and the complete $L^2$ Neumann
solver are also complete. The
Beurling symbol is $\overline\xi/\xi$ away from zero, consistently with the
Fourier symbols $\pi i\overline\xi$ for $\partial_z$ and $\pi i\xi$ for
$\partial_{\bar z}$; it is assigned the value $1$ at zero. The Cauchy kernel
is locally integrable, its convolution with a test function is an honest
Bochner integral at every point, and its distributional fundamental-solution
identity is proved by smooth regularization. The transform is smooth on test
functions, satisfies $\partial_{\bar z}\mathcal Cg=g$ and
$\partial_z\mathcal Cg=\mathcal C(\partial_zg)$ pointwise, and obeys the
far-field bound $\mathcal Cg(z)=O(|z|^{-1})$. The exact $L^2$ identity
$\mathcal S(\partial_{\bar z}\varphi)=\partial_z\varphi$ is also complete for
test functions. The cutoff error is $O(R^{-1})$ in global $L^2$, so local
comparison on expanding cutoff disks proves
$\partial_z\mathcal Cg=\mathcal Sg$ almost everywhere and completes the local
$W^{1,2}$ Cauchy-transform wrapper. The same weak identities are now proved
for compactly supported $L^p$ data above exponent two by fixed-support smooth
approximation, local uniform convergence of potentials, strong $L^2$
convergence of the two derivative components, and diskwise weak closure.
For every bounded
measurable coefficient which vanishes almost everywhere outside a disk and satisfies
$|\mu|\leq k<1$, there is now a unique $h\in L^2$ satisfying
$h-\mu\mathcal Sh=\mu$. The reusable harmonic-analysis branch is also
complete through a bounded transform on $L^r$, $2<r<3$, and a strict
contraction estimate for $M_\mu\mathcal S_r$. Combining these results now
constructs a continuous principal map $f(z)=z+\mathcal C_ph(z)$ satisfying
the prescribed weak Beltrami equation, the sharp algebraic distortion bound
$|Df|^2\leq(1+k)(1-k)^{-1}J_f$, and $f(z)-z\to0$ at infinity. It also proves
that this asymptotic normalization makes $f$ proper and that every target has
the standard positive image-circle class on a sufficiently large circle. The
remaining analytic target is the planar open/discrete theorem with positive
local index. The parallel topological degree target is complete: logarithmic
increments, vortex cancellation, finite hole filling, perforated-disk
boundary additivity, and the continuous finite-fiber formula are all proved.

1. **Complete.** The reusable harmonic-analysis layer under
   `JJMath.Analysis.Harmonic`, documented independently in
   `handwave/HarmonicAnalysis/singular-integrals.hw.md`. The kernel predicates, full-period Fourier
   cancellation, vector-valued polar annulus formula, all three physical
   Beurling-kernel inputs, abstract radial truncations, absolutely convergent
   positive Beurling truncations on $C_c^\infty(\mathbb C)$, and the
   off-support representation of the Fourier $L^2$ transform by the physical
   kernel are complete. The weak/strong operator-bound predicates are also
   available independently of the application. The unbounded polar formula,
   exact translated inverse-cube integral, and scale-independent integrated
   first-difference tail bound for a bad ball are complete as well. The
   product-space majorant, both Fubini directions, and mean-zero subtraction
   now give the full exterior $L^1$ tail estimate for each bad piece, with
   integrability recorded explicitly. Finite families have also been
   aggregated on the complement of all doubled support disks. The standard
   half-open planar dyadic grid is now defined with its floor-indexed unique
   square, measurable disjoint partition, exact area, controlled containing
   ball, parent/ancestor nesting, and laminar intersection theorem. The
   generic maximal-square selection and its specialization to the standard
   bad-average predicate are complete: integrability excludes sufficiently
   coarse bad squares, every bad square lies in a maximal one, the maximal
   family is countable and pairwise disjoint, its union is the full bad
   region, and every selected square satisfies
   $\alpha|Q|<\int_Q\|f\|\leq4\alpha|Q|$. Dyadic Lebesgue differentiation,
   the almost-everywhere high-value covering, and the total-area estimate
   $\alpha|\bigcup Q|\leq\|f\|_1$ are complete as well. The actual
   Calderón--Zygmund decomposition is now complete through the integrable
   pointwise bad sum, exact identity $f=g+b$, cancellation, total bad-piece
   $L^1$ bound, the essential bound $\|g\|\leq4\alpha$, and
   $\int\|g\|^2\leq4\alpha\|f\|_1$. Summable integrated norms now have a
   reusable pointwise-series integrability theorem. It upgrades the finite
   exterior aggregation to countable bad families, and the canonical
   corner-centered support disks for the maximal squares give
   $\alpha|\Omega^*|\leq16\pi\|f\|_1$ together with
   $\int_{(\Omega^*)^c}|\sum_QK*b_Q|\leq2\pi C\|f\|_1$. The good and total
   bad parts now have the required $L^2$ membership for $L^1\cap L^2$ input.
   The Beurling isometry gives
   $\|\mathcal Sg\|_2^2\leq4\alpha\|f\|_1$, its full Chebyshev superlevel
   estimate, and the exact $L^2$ identity
   $\mathcal Sf=\mathcal Sg+\mathcal Sb$. Support-controlled smooth density
   is also complete: a function supported in $\overline B(c,r)$ has test
   approximants supported in $\overline B(c,3r/2)$, leaving a strict gap to
   the exterior $|x-c|>2r$. The separated-disk physical-kernel estimate is
   now complete as well. The inverse-fourth-power tail is integrable with
   explicit bound $2\pi/a^2$; the separation inequality gives
   $|\mathcal Kh(x)|\leq16\pi^{-1}|x-c|^{-2}\|h\|_1$; and Hölder on the
   fixed support disk yields a quantitative exterior $L^2$ bound by the
   input $L^2$ energy. The rough off-support representation is complete as
   well: support-controlled test approximants converge on the Fourier side
   by the $L^2$ isometry and on the separated physical side by the new
   estimate; uniqueness of limits in measure proves
   $\mathcal Sh=\mathcal Kh$ almost everywhere outside the doubled support
   disk for every compactly supported $h\in L^2$. The countable passage is
   now complete too. A cofinal finite exhaustion of the maximal bad squares
   gives partial bad sums converging to the total bad part in $L^2$; on the
   common exterior, the corresponding physical kernels converge to their
   pointwise series in $L^1$. The finite rough formulas and uniqueness of
   convergence in measure therefore identify
   $\mathcal Sb=\sum_Q\mathcal Kb_Q$ almost everywhere on $(\Omega^*)^c$.
   The weak $(1,1)$ distribution argument is now complete for
   $L^1\cap L^2$ data. At level $\alpha=t$, the superlevel set is covered,
   modulo a null set, by the enlarged region, the $t/2$ good-part
   superlevel, and the exterior $t/2$ bad-part superlevel. Their constants
   are respectively $16\pi$, $16$, and $24$, giving
   $t|\{|\mathcal Sf|\geq t\}|\leq(40+16\pi)\|f\|_1$. The extension layer
   has now started. A reusable distribution lemma shows that a finite weak
   bound with vanishing right-hand side implies convergence in measure.
   Consequently, transforms of any $L^1$-Cauchy family in
   $L^1\cap L^2$ are Cauchy in measure globally, not merely on bounded
   disks. Every $L^1$ function now also has a canonical sequence of
   integrable simple approximants; each approximant lies in $L^2$, converges
   in $L^1$, and its transforms are globally Cauchy in measure.

   The completeness leaf is now complete as reusable analysis. Convergence
   in measure is stable under addition, negation, subtraction, fixed scalar
   multiplication, and passage to a dominated measure. A rapidly selected subsequence of a
   Cauchy-in-measure sequence converges almost everywhere by Borel--Cantelli;
   on a finite-measure space this identifies the limit in measure of the
   full sequence. Applied on every disk, this constructs a measurable
   canonical Beurling limit for every $L^1$ input. The limit is independent
   of the representative modulo almost-everywhere equality, so it defines a
   map from $L^1(\mathbb C)$ to measurable functions modulo null sets. For
   $L^1\cap L^2$ inputs, the simple approximants also converge in $L^2$;
   hence the new extension agrees almost everywhere with the original
   Fourier-multiplier transform. Comparing the three canonical approximation
   sequences for $f$, $g$, and $f+g$ proves additivity; the analogous scalar
   comparison proves complex homogeneity. Thus the extension is now a
   complex-linear map from $L^1(\mathbb C)$ to measurable functions modulo
   null sets.

   The distributional passage is also complete without loss. A reusable
   theorem passes weak distribution bounds through almost-everywhere limits
   when the controlling masses converge. Its proof uses eventual
   lower-threshold superlevel sets and lets the threshold ratio increase to
   one. Since the canonical simple approximants have convergent $L^1$
   masses, the extended Beurling transform satisfies
   $t|\{|\mathcal Sf|\geq t\}|\leq(40+16\pi)\|f\|_1$ for every finite
   positive $t$.

   The genuine linear weak-$(1,1)$ operator has now been combined with the
   exact $L^2$ isometry to obtain the strong moment estimate for
   $1<p<2$. The distribution function of a sum at level $t$ is bounded by
   the sum at level $t/2$, and distribution functions are invariant under
   almost-everywhere equality. For the split
   $f=f_{>u}+f_{\leq u}$, the low part is proved to lie in $L^2$ directly
   from $|f_{\leq u}|^2\leq u|f|$. Combining the inherited weak $(1,1)$
   estimate on $f_{>u}$ with compatibility and the exact $L^2$ isometry on
   $f_{\leq u}$ gives
   $$
     d_{\mathcal Sf}(t)
       \leq \frac{(40+16\pi)\int_{\{|f|>u\}}|f|}{t/2}
       +\frac{\int_{\{|f|\leq u\}}|f|^2}{(t/2)^2}.
   $$
   A reusable layer-cake theorem identifies
   $\int |g|^p$ with $p\int_0^\infty t^{p-1}d_g(t)\,dt$.
   The two Tonelli calculations with $u=t$ are now complete. They produce
   the factors $(p-1)^{-1}$ and $(2-p)^{-1}$ and give
   $$
     \|\mathcal Sf\|_p
       \leq
       \left[p\left(
         \frac{2(40+16\pi)}{p-1}+\frac4{2-p}
       \right)\right]^{1/p}\|f\|_p
   $$
   for every integrable input, with extended values allowed. In particular,
   the transform maps $L^1\cap L^p$ into $L^p$. The completion step below
   two is now complete as well. Finite-support $L^p$ simple functions are
   proved integrable and mapped complex-linearly through the weak-$L^1$
   transform into $L^p$. The preceding estimate gives a uniform bound on
   this dense subspace, and bounded linear extension produces
   $\mathcal S_p:L^p(\mathbb C)\to L^p(\mathbb C)$ with the same explicit
   constant. The extension is proved to agree with the construction on
   every simple function.

   The adjoint identity is now complete. The complex-bilinear $L^2$ pairing
   makes both Fourier transforms self-transpose; reflection relates the two
   Fourier conventions; and evenness of the Beurling symbol proves
   $\int(\mathcal Sf)g=\int f(\mathcal Sg)$. Compatibility carries this to
   all $L^1\cap L^2$ inputs. Quantitative duality, the finite above-$2$
   endpoint, the reusable simple-core Riesz--Thorin theorem, density
   completion, the explicit near-$2$ exponent, and the strict estimate
   $k\|\mathcal S_r\|_{r\to r}<1$ are now all complete;
2. **Analytic principal solution complete.** Set
   $f(z)=z+\mathcal Ch(z)$ using the identified $L^2\cap L^p$ solution. Its
   continuity, local Sobolev differential, weak equation, distortion bound,
   asymptotic identity, and properness are proved;
3. **Complete.** Properness and the logarithmic-condenser argument prove
   lightness. The protected-cutoff Jacobian measure route proves openness
   directly. Protected finite multiplicity plus openness makes every proper
   fiber finite, and local target coverage makes the index of every isolating
   disk strictly positive. The proper degree-one inversion argument then
   upgrades the principal solution to an orientation-preserving
   homeomorphism;
4. **Complete.** Normalize the compactly supported solutions, extend them
   quasiconformally over infinity by analytic and topological isolated-point
   removability, and feed their truncations into spherical compactness.

The full measurable-Riemann-mapping assembly is proved. On its proper
principal-solution route, the normal-domain construction, protected degree
cutoff, Sobolev scalar Piola identity, Radon--Nikodym rigidity and positivity,
target-ball coverage, analytic Reshetnyak lightness argument, finite-fiber
argument, positive local-index argument, degree-one inversion, spherical
extension, and normalized compactness limit are complete. The post-MRMT
Stoilow route is complete as well: strict positivity of the normalizing
Jacobian, the whole-plane finite-chart bridge, inverse Sobolev composition,
pointwise Beltrami cancellation, the continuous Sobolev
$\partial_{\bar z}$ Weyl lemma, the holomorphic open-mapping theorem, and
isolated zeros prove the nonproper whole-plane open-and-discrete theorem.
The domain-local version, the optional general Whyburn--Stoilow theorem, and
coefficient-free weak closure of finite distortion remain useful for the
broader quasiregular library but are not on the prescribed-coefficient
critical path.
