# Uniformization

The theorem proved here is the simply connected form of uniformization:
every simply connected Riemann surface is biholomorphic to the
Riemann sphere, the complex plane, or the unit disk. The proof first turns
simple connectedness into vanishing first real de Rham cohomology. The
noncompact case is then proved by Hubbard's normalized-exhaustion argument,
while the compact case is reduced to the noncompact theorem by deleting one
point.

## The three models

A biholomorphic equivalence is a homeomorphism whose forward and inverse maps
are holomorphic. We use existence of such an equivalence as the relation
between complex surfaces.

@include{lean:JJMath.Uniformization.Biholomorphic}

@include{lean:JJMath.Uniformization.BiholomorphicSurfaces}

The compact alternative uses the standard complex structure on the one-point
compactification of the plane.

@include{lean:JJMath.instRiemannSurfaceRiemannSphere}

The other two alternatives are the complex plane and the open unit disk.

## Simple connectedness and first cohomology

Let \(\omega\) be a closed real one-form on a simply connected Riemann
surface. The first step is a direct path-integral argument; no comparison with
singular cohomology is used.

For two smooth curves with the same endpoints and an endpoint-fixed homotopy
between them, cover the homotopy square by a finite rectangular grid such that
each rectangle maps into a neighborhood carrying a local primitive of
\(\omega\). Around each cell the four primitive differences cancel. Along
an edge shared by two cells, the two local primitives differ by a constant on
the relevant path component of their overlap, so the edge differences agree.
All interior edges cancel, and the two fixed vertical sides contribute zero.
Stokes' theorem on degenerate two-simplices supplies the subdivision identity
for the smooth horizontal boundary curves. Their integrals are therefore
equal.

@include{lean:JJMath.Uniformization.integrate_smoothCurveSegmentSimplex_eq_of_pathHomotopy}

Fixing a base point, define a function by integrating \(\omega\) along a
smooth path from the base point. Simple connectedness and the grid argument
make the value path-independent. Near any point, append a short path inside a
local primitive neighborhood. The resulting function is that local primitive
plus a constant, hence is smooth and has differential \(\omega\).

@include{lean:JJMath.Uniformization.simplyConnected_surface_closedOneForm_has_primitive}

Thus every closed real one-form is exact.

@include{lean:JJMath.Uniformization.simplyConnected_surface_deRhamH1_zero}

## A connected zero-cohomology exhaustion

Now let \(X\) be connected and noncompact with vanishing first real de Rham
cohomology. A connected noncompact Riemann surface first admits a smooth
relatively compact exhaustion.

@include{lean:JJMath.Uniformization.connected_noncompact_has_smoothRelativelyCompactExhaustion}

Choose a base point. For each exhaustion member, take the component containing
that point and fill all relatively compact complementary components. The
filled domains remain nested, relatively compact, and path connected. Every
remaining complementary component is exterior. Removing these exterior
components one at a time gives annular Mayer--Vietoris covers. The angular
period class supplied from the exterior side is nonzero, so exactness
preserves vanishing first cohomology at every removal. This produces a pointed
exhaustion by connected smooth domains with vanishing first cohomology. The
topology and construction are developed in more detail in
[the exhaustion argument](article:simply-connected-exhaustion).

@include{lean:JJMath.Uniformization.PointedH1ZeroSmoothRelativelyCompactExhaustion}

@include{lean:JJMath.Uniformization.smoothRelativelyCompactExhaustion_exists_pointedH1Zero_filling_of_ambientDeRhamH1Zero}

## Uniformizing one exhaustion member

Each member of the exhaustion is uniformized using a bounded-domain Green
potential.  Fix a smooth relatively compact domain \(\Omega\) and a pole
\(p\in\Omega\).  Delete a small coordinate disk of radius \(r\) around \(p\)
and solve the ordinary Dirichlet problem on the resulting annulus with
boundary values \(\log r\) on the inner circle and \(0\) on
\(\partial\Omega\).  Dividing by \(\log r<0\) gives a harmonic measure which
is \(1\) on the inner boundary, \(0\) on the outer boundary, and takes values
in \([0,1]\).

@include{lean:JJMath.Uniformization.annularPerronUnitHarmonicMeasure_mem_Icc}

For one fixed deleted disk, the strong maximum principle makes this harmonic
measure strictly less than \(1\) on every larger coordinate circle still
contained in \(\Omega\).  Compactness of the circle upgrades this to a uniform
bound \(a<1\).

@include{lean:JJMath.Uniformization.exists_annularPerronUnitHarmonicMeasure_outerCircle_bound}

Hubbard's barrier combines the logarithmic model \(A-\log|z|\) near the pole
with a suitable multiple of this fixed harmonic measure farther out.  Taking
the minimum in the intervening annulus and choosing the constants so that the
two pieces meet in the correct order gives a continuous superharmonic
function which vanishes on \(\partial\Omega\).

@include{lean:JJMath.Uniformization.hubbardAnnularPerronBarrier_properties}

A single shifted barrier dominates the negatives of all sufficiently late
annular solutions.  The maximum principle gives compact-local bounds away
from \(p\), and Harnack compactness gives a locally uniform harmonic limit.
The inner boundary normalization leaves the logarithmic singularity at
\(p\), while the outer barriers preserve the zero boundary value.

@include{lean:JJMath.Uniformization.annularPerron_approximationSystem_extracts_boundedNegativeGreenLimit}

The result is a negative Green potential on \(\Omega\), bounded above by
zero, with logarithmic zero at \(p\).

@include{lean:JJMath.Uniformization.BoundedNegativeGreenPotential}

@include{lean:JJMath.Uniformization.smoothBoundaryDomain_has_boundedNegativeGreenPotential_via_annularPerron}

Applying this construction to every exhaustion member chooses the bounded
Green potentials simultaneously.  Reversing their signs and regarding the
domains as open Riemann surfaces gives positive Green functions with compact
positive superlevel sets.

@include{lean:JJMath.Uniformization.smoothRelativelyCompactExhaustion_has_boundedNegativeGreenPotentials}

@include{lean:JJMath.Uniformization.PointedH1ZeroSmoothRelativelyCompactExhaustion.has_compactSuperlevelGreenFunctions}

To exponentiate the Green function, it is enough to construct a circle-valued
primitive of its conjugate differential. Near the pole, the residue
calculation separates this differential into a normalized angular generator
and an exact remainder. A compact coordinate vortex has the required winding
near the pole. Transporting its compensating zero to infinity through a
locally finite chain of coordinate charts produces a global smooth circle
phase on the punctured surface.

On a small punctured pole disk, explicit logarithm cuts and the de Rham
Mayer--Vietoris sequence identify the transported vortex class with the Green
angular class, up to orientation. Because the unpunctured domain has vanishing
first cohomology, restriction from the punctured domain to this punctured disk
is injective in degree one. The circle primitive therefore transfers to the
Green conjugate differential; the exact remainder only multiplies it by the
exponential of a smooth real-valued function.

@include{lean:JJMath.Uniformization.exists_puncturedAngularForm_greenConjugate_circlePrimitive_reduction}

The resulting phase multiplied by \(e^{-G}\) is locally an ordinary
holomorphic exponential. It extends across the pole by zero and has one
simple zero there and no other zeros.

@include{lean:JJMath.Uniformization.compactSuperlevelGreenFunction_planeMap_of_vortex}

Positivity places the map in the unit disk. Compact positive superlevels make
it proper, and the unique simple zero makes its degree one. A proper
degree-one holomorphic disk map is biholomorphic.

@include{lean:JJMath.Uniformization.compactSuperlevelGreenFunction_biholomorphic_unitDisc_of_deRhamH1Zero}

Consequently one can simultaneously choose bijective holomorphic maps from
all exhaustion members to the unit disk, carrying the common base point to
zero.

@include{lean:JJMath.Uniformization.PointedH1ZeroSmoothRelativelyCompactExhaustion.has_bijective_pointedDiskMaps}

## Normalized exhaustion maps

Record one disk equivalence for every exhaustion member, all sending the
common base point to zero.

@include{lean:JJMath.Uniformization.PointedDiskUniformization}

@include{lean:JJMath.Uniformization.PointedH1ZeroSmoothRelativelyCompactExhaustion.has_pointedDiskUniformization}

Fix the disk coordinate supplied by the first member and a nonzero tangent
vector at the base point. Divide each disk map by its derivative in that
coordinate. This gives an injective holomorphic map
\[
  \varphi_n:X_n\longrightarrow D_{r_n}
\]
with value zero and derivative one at the base point. For \(m\le n\), the
transition from \(D_{r_m}\) to \(D_{r_n}\) again fixes zero and has
derivative one. Schwarz's lemma gives \(r_m\le r_n\).

@include{lean:JJMath.Uniformization.PointedDiskUniformization.radius_mono}

### Compact-local bounds

If a compact set lies in one exhaustion member, compact containment in the
next member places its normalized image in a disk of relative radius
\(\rho<1\). The normalized univalent growth estimate gives
\[
  |f(z)|\le r\rho\exp\!\left(\frac{4\rho}{1-\rho}\right)
\]
for every later transition. This supplies a uniform bound on a neighborhood
of the compact set. The estimate ultimately comes from Grönwall's area
theorem; see [the Koebe estimate](article:koebe-quarter).

@include{lean:JJMath.Uniformization.univalent_disk_normalized_norm_le_exp_scaled}

The changing-domain form of Montel's theorem applies to maps that are
eventually holomorphic and bounded near every compact exhaustion member.

@include{lean:JJMath.Uniformization.eventualDomain_montel_of_eventually_boundedOn_exhaustion_neighborhoods}

It yields a subsequence of the normalized maps converging locally uniformly
on all of \(X\) to a holomorphic function.

@include{lean:JJMath.Uniformization.PointedDiskUniformization.exists_normalizedMap_limit}

The derivative-one normalization survives in the first disk coordinate, so
the limit is nonconstant. Every compact subset of \(X\) eventually lies in a
domain on which all approximating maps are injective. The changing-domain
Hurwitz argument therefore makes the limit injective.

@include{lean:JJMath.Uniformization.locallyUniformLimit_injective_of_eventuallyInjectiveOn_compacts}

@include{lean:JJMath.Uniformization.PointedDiskUniformization.normalizedMap_limit_injective}

### Unbounded conformal radii

Suppose the radii are unbounded. The scaled Koebe quarter theorem says that a
normalized univalent map on \(D_r\) covers \(D_{r/4}\).

@include{lean:JJMath.Uniformization.koebe_quarter_normalized_scaled}

Given \(w\in\mathbb C\), choose an earlier radius larger than
\(4|w|\). Then \(w\) lies in every sufficiently late image, and its
preimages remain in the compact closure of that one earlier exhaustion
member. Local uniform convergence puts \(w\) in the limiting image. Thus the
limit is a biholomorphic map onto the plane.

@include{lean:JJMath.Uniformization.PointedDiskUniformization.normalizedMap_limit_surjective_of_not_bddAbove_radius}

### Bounded conformal radii

Suppose instead that the radii have finite supremum \(R\). For a point
strictly inside \(D_R\), choose an earlier radius sufficiently close to
\(R\). After rescaling source and target to unit disks, every later
transition has derivative close to one. Schwarz and Borel--Carathéodory
estimates make such a transition uniformly close to the identity on a smaller
disk, and a quantitative open-mapping estimate puts the chosen point in its
image.

@include{lean:JJMath.Uniformization.normalized_diskSelfMap_mem_image_of_deriv_close}

Once again the preimages lie in the compact closure of one fixed member, so
local uniform convergence shows that the limiting image contains \(D_R\).

@include{lean:JJMath.Uniformization.PointedDiskUniformization.ball_csSup_radius_subset_range_normalizedMap_limit}

The approximating maps take values in disks of radii at most \(R\), hence
the limit lands in the closed disk of radius \(R\). It cannot attain the
boundary: a nonconstant holomorphic map is open, while every neighborhood of
a boundary point contains values of norm greater than \(R\). Thus its range
is exactly \(D_R\).

@include{lean:JJMath.Uniformization.PointedDiskUniformization.normalizedMap_limit_norm_lt_csSup_radius}

Rescaling \(D_R\) to the unit disk completes the bounded case. Combining
the two radius alternatives gives Hubbard's normal-family dichotomy.

@include{lean:JJMath.Uniformization.PointedDiskUniformization.biholomorphic_complexPlane_or_unitDisc}

Starting from the zero-cohomology exhaustion constructed above proves the
noncompact theorem.

@include{lean:JJMath.Uniformization.noncompact_deRhamH1Zero_biholomorphic_complexPlane_or_unitDisc}

## The compact zero-cohomology case

Let \(X\) be compact and connected with
\(H^1_{\mathrm{dR}}(X;\mathbb R)=0\), and fix \(p\in X\).  Cover \(X\) by
the punctured surface \(X\setminus\{p\}\) and a coordinate disk \(D\) around
\(p\).  Their intersection is an annulus, and Mayer--Vietoris contains
\[
  H^1_{\mathrm{dR}}(X)
  \longrightarrow
  H^1_{\mathrm{dR}}(X\setminus\{p\})\oplus H^1_{\mathrm{dR}}(D)
  \longrightarrow
  H^1_{\mathrm{dR}}(D\setminus\{p\})
  \xrightarrow{\partial}
  H^2_{\mathrm{dR}}(X).
\]

The connecting map \(\partial\) is nonzero.  Choose a positive area form
supported in a small coordinate disk on the punctured side of the cover.  Its
class on \(X\) is nonzero, since exactness would contradict Stokes' theorem
and positivity of its total integral.  The support may be placed in an
exterior component of the punctured surface, where mass transport gives a
global primitive; its restriction to \(D\) is exact by the Poincare lemma.
Mayer--Vietoris therefore places the nonzero compact-surface class in the
image of \(\partial\).  Since the first cohomology of an annulus is
one-dimensional, \(\partial\) is injective.

@include{lean:JJMath.Uniformization.compact_coordinatePuncture_mayerVietorisConnecting_injective}

Exactness, \(H^1_{\mathrm{dR}}(X)=0\), and
\(H^1_{\mathrm{dR}}(D)=0\) now force
\[
  H^1_{\mathrm{dR}}(X\setminus\{p\})=0.
\]

@include{lean:JJMath.Uniformization.compact_deRhamH1Zero_puncturedSurfaceOpen}

The punctured surface is connected and noncompact, so the theorem above
identifies it with the plane or the unit disk.  The disk alternative would
give a bounded holomorphic coordinate on \(X\setminus\{p\}\).  A bounded
holomorphic map on a once-punctured Riemann surface extends across the
puncture.

@include{lean:JJMath.Uniformization.bounded_punctured_holomorphicMap_extends}

The extension is holomorphic on compact \(X\), hence constant, contradicting
injectivity of the disk coordinate.

@include{lean:JJMath.Uniformization.compact_puncturedSurfaceOpen_not_biholomorphic_unitDisc}

Thus \(X\setminus\{p\}\) is biholomorphic to \(\mathbb C\).  The inverse plane
coordinate embeds \(\mathbb C\) in \(X\) with complement exactly \(\{p\}\).
Compactness identifies \(X\) with the one-point compactification of the plane,
and the complex charts make this identification biholomorphic.

@include{lean:JJMath.Uniformization.compact_biholomorphic_riemannSphere_of_punctured_complexPlane}

@include{lean:JJMath.Uniformization.compact_deRhamH1Zero_biholomorphic_riemannSphere}

## Uniformization of simply connected surfaces

Finally let \(X\) be simply connected. The fine-grid path-integral argument
gives \(H^1_{\mathrm{dR}}(X;\mathbb R)=0\). If \(X\) is compact, the
compact zero-cohomology theorem makes it biholomorphic to the Riemann sphere.
If it is noncompact, the normalized-exhaustion theorem makes it
biholomorphic to the complex plane or the unit disk. These are exactly the
three alternatives.

@include{lean:JJMath.Uniformization.simplyConnected_riemannSurface_uniformization}
