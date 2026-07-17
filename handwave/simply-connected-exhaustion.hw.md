# Exhaustions with Vanishing First Cohomology

Let \(X\) be a noncompact Riemann surface and fix \(p\in X\).  The goal is
to exhaust \(X\) by path-connected relatively compact smooth domains
containing \(p\), each with vanishing first real de Rham cohomology.  The
construction has two geometric steps: fill bounded complementary components,
then prove that this filling does not create first cohomology.

## Filling bounded holes

For a closed set \(K\subset X\), its bounded filling is

\[
  \widehat K=\operatorname{int}K\;\cup\!
  \bigcup_{\substack{V\text{ a component of }X\setminus K\\
                      \overline V\text{ compact}}}V.
\]

It fills precisely the complementary components which do not reach infinity.

@include{lean:JJMath.Uniformization.boundedFillingOfComplement}

Begin with a smooth relatively compact exhaustion and take, in each member,
the component containing \(p\).  Filling its bounded complementary components
preserves smoothness of the frontier, compact closure, path connectedness,
and the strong nesting of successive closures.  The filled components still
exhaust \(X\): any path from \(p\) to a prescribed point has compact image and
is eventually contained in the original exhaustion.

@include{lean:JJMath.Uniformization.smoothBoundaryDomain_exists_domain_with_boundedFilling_carrier}

## The period obstruction

Assume \(H^1_{\mathrm{dR}}(X;\mathbb R)=0\).  An exterior complementary
component cannot meet the domain along two different frontier components.
If it did, choose a smooth step across one component and extend its
differential by zero outside a small band.  A loop which crosses that band
once through the domain and returns through the exterior has period one,
contradicting exactness of every closed one-form.

@include{lean:JJMath.Uniformization.BoundaryComponentTransition.not_subsingleton_deRhamH1_of_two_frontier_components}

Thus each exterior component has connected frontier and hence a two-sided
annular collar.  On the collar, the angular closed one-form represents the
generator of first cohomology.  Extend it into the exterior component: after
cutoff, its failure to be closed is a compactly supported two-form, and a
locally finite transport to infinity supplies a primitive for that defect.

@include{lean:JJMath.Uniformization.IsExteriorComponent.exists_closed_exteriorAngularExtension}

Remove the finitely many exterior components one at a time.  At each stage,
the remaining region and the exterior component with its collar form a
Mayer--Vietoris cover whose intersection is an annulus.  The extended angular
form maps onto the annular generator, so exactness carries the vanishing of
\(H^1_{\mathrm{dR}}\) across the deletion.  After the last deletion one has
the bounded filling.

@include{lean:JJMath.Uniformization.SmoothBoundaryDomain.deRhamH1Zero_of_all_complementComponents_exterior}

Consequently ambient vanishing produces the desired pointed exhaustion.

@include{lean:JJMath.Uniformization.smoothRelativelyCompactExhaustion_exists_pointedH1Zero_filling_of_ambientDeRhamH1Zero}

The converse is also useful.  Normalize a primitive on every exhaustion
member by making it vanish at \(p\).  On connected overlaps two normalized
primitives have zero differential and agree at \(p\), so they glue to a
global primitive on \(X\).

@include{lean:JJMath.Uniformization.PointedH1ZeroSmoothRelativelyCompactExhaustion.ambientDeRhamH1Zero}

## Simple connectedness

If \(X\) is simply connected and \(\omega\) is closed, define

\[
  f(x)=\int_{p}^{x}\omega.
\]

This is independent of the chosen path.  Subdivide a homotopy between two
paths into a rectangular grid fine enough that every cell lies in a
neighborhood carrying a primitive of \(\omega\).  Contributions from common
edges cancel, leaving equality of the two boundary integrals.  Locally,
\(f\) differs by a constant from a smooth primitive, hence \(df=\omega\).

@include{lean:JJMath.Uniformization.simplyConnected_surface_closedOneForm_has_primitive}

Applying the bounded-filling construction gives the exhaustion required in
the uniformization argument.

@include{lean:JJMath.Uniformization.smoothRelativelyCompactExhaustion_exists_pointedH1Zero_filling}
