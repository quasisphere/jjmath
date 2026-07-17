# Radó's Second-Countability Theorem

Radó's theorem says that every Riemann surface is second countable. This is
not a purely topological fact: non-second-countable one-dimensional manifolds
exist. The complex structure rules out this pathology by providing enough
holomorphic functions to construct a countable basis.

For uniformization, the theorem supplies the countability needed for compact
exhaustions and diagonal normal-family arguments. The proof used here follows
the compact-or-Perron route in Will Rushworth's note
[Riemann surfaces are always second-countable](https://willierushrush.github.io/posts/2020/05/second-countability/).

## A Holomorphic Function Forces Countability

The first main step is a pullback-basis criterion. Suppose that a connected
Riemann surface \(X\) carries a nonconstant holomorphic function
\(f:X\to\mathbb C\). Start with a countable basis \(\mathcal B\) of the plane
and consider connected components of the sets \(f^{-1}(U)\), where
\(U\in\mathcal B\).

Only certain components need to be counted. Given \(x\in X\) and an open
neighborhood \(N\) of \(x\), choose a relatively compact coordinate disk
\(W\subseteq N\) whose frontier does not map to \(f(x)\). A sufficiently small
\(U\in\mathcal B\) containing \(f(x)\) then satisfies

\[
  f^{-1}(U)\cap\partial W=\varnothing.
\]

The component of \(f^{-1}(U)\) containing \(x\) cannot cross \(\partial W\),
so it lies in \(W\), is second countable, and refines \(N\). Call components
obtained this way *good sheets*. Thus good sheets form a basis of \(X\).

@include{lean:JJMath.Uniformization.nonconstant_holomorphicMap_goodPullbackSheets_local_refinement}

It remains to count them. For a fixed good sheet \(S\) and a fixed
\(U\in\mathcal B\), the components of \(f^{-1}(U)\) meeting \(S\) cut out
pairwise disjoint nonempty open subsets of the second-countable space \(S\).
There are only countably many such components. Taking the countable union over
\(\mathcal B\) shows that each good sheet meets only countably many others.

@include{lean:JJMath.Uniformization.goodPullbackSheet_meets_countably_many}

Starting from one good sheet and repeatedly adjoining all sheets that meet one
already chosen gives a countable family. Its union is both open and closed;
connectedness of \(X\) therefore makes it all of \(X\). Hence every good sheet
appears after finitely many adjacency steps, so the good-sheet basis is
countable.

@include{lean:JJMath.Uniformization.secondCountable_of_nonconstant_holomorphicMap_to_complex}

## The Compact Case

If \(X\) is compact, coordinate disks cover it, compactness gives a finite
subcover, and each disk is second countable. A finite open cover by
second-countable subspaces supplies a countable basis for \(X\).

@include{lean:JJMath.Uniformization.compact_riemannSurface_secondCountable}

## The Noncompact Case

Let \(X\) now be noncompact. Choose two disjoint closed coordinate disks
\(D_0,D_1\subset X\) such that

\[
  Y=X\setminus(D_0\cup D_1)
\]

is nonempty and connected. The three open pieces consisting of \(Y\) and
slightly enlarged versions of \(D_0\) and \(D_1\) cover \(X\).

@include{lean:JJMath.Uniformization.exists_radoTwoDiskCut}

### A Harmonic Separator

Prescribe boundary values \(0\) and \(1\) on the two boundary circles of
\(Y\). Perron's method produces a harmonic envelope \(h:Y\to\mathbb R\).
Exterior tangent disks at distinguished points of the two circles give
logarithmic barriers. These barriers force values of \(h\) arbitrarily close
to \(0\) near one circle and arbitrarily close to \(1\) near the other, so
\(h\) is nonconstant.

This is the only place where the full Perron construction enters the Radó
argument; its analytic details are developed in [Perron's method](article:perron).

@include{lean:JJMath.Uniformization.radoTwoDiskCut_has_harmonic_separator}

### From the Separator to a Holomorphic Function

Let \(\pi:\widetilde Y\to Y\) be the path-homotopy universal cover. The
pullback \(h\circ\pi\) is harmonic. Locally it is the real part of a
holomorphic function, and two such local functions differ on overlaps by an
imaginary constant. Since \(\widetilde Y\) is simply connected, these constants
have no periods, so the local harmonic conjugates glue to a holomorphic map
\(F:\widetilde Y\to\mathbb C\) satisfying

\[
  \operatorname{Re}F=h\circ\pi.
\]

@include{lean:JJMath.Uniformization.simplyConnected_harmonicOnSurface_has_holomorphic_real_part}

The endpoint projection \(\pi\) is surjective, so \(h\circ\pi\), and therefore
\(F\), is nonconstant.

@include{lean:JJMath.Uniformization.radoTwoDiskCut_universalCover_has_nonconstant_holomorphicMap_to_complex}

The pullback-basis criterion makes \(\widetilde Y\) second countable. Second
countability descends through the covering projection to \(Y\), and the finite
open cover by \(Y\) and the two coordinate disks then makes \(X\) second
countable.

@include{lean:JJMath.Uniformization.noncompact_riemannSurface_secondCountable_via_perron_universal_cover}

## Radó's Theorem

The compact case uses a finite coordinate cover. The noncompact case uses the
twice-cut Perron problem to construct a nonconstant holomorphic function on a
universal cover, then applies the pullback-basis criterion and descends the
result. Together they prove Radó's theorem.

@include{lean:JJMath.Uniformization.rado_secondCountableTopology_riemannSurface}

Consequently every Riemann surface admits a countable cover by coordinate
disks, the form used in later uniformization arguments.

@include{lean:JJMath.Uniformization.rado_countableCoordinateDiskCover}
