# Singular Cohomology

For a space \(X\) and a commutative coefficient ring \(R\), the singular
chain complex \(C_\bullet(X;R)\) is freely generated in degree \(n\) by
continuous maps \(\Delta^n\to X\).  Dualizing gives the cochain complex

\[
  C^n(X;R)=\operatorname{Hom}_R(C_n(X;R),R),
  \qquad (\delta\varphi)(c)=\varphi(\partial c),
\]

and its cohomology is \(H^n(X;R)\).  The harmless universe lift in the
coefficient module allows the same definition for spaces and coefficients
living in different universes.

@include{lean:JJMath.Cohomology.SingularChains}

@include{lean:JJMath.Cohomology.SingularCohomology}

@include{lean:JJMath.Cohomology.RealSingularCohomology}

## Functoriality and homotopy

A continuous map \(f:X\to Y\) pushes chains forward and therefore pulls
cochains back.  Passing to cohomology gives

\[
  f^*:H^n(Y;R)\longrightarrow H^n(X;R),
  \qquad (g\circ f)^*=f^*\circ g^*.
\]

@include{lean:JJMath.Cohomology.singularCohomologyMap}

@include{lean:JJMath.Cohomology.singularCohomologyMap_comp}

The prism operator associated with a homotopy gives a chain homotopy between
the two maps on singular chains.  Dualizing that homotopy and passing to
cohomology proves homotopy invariance.

@include{lean:JJMath.Cohomology.singularCohomologyMap_eq_of_homotopy}

## The singular-cochain sheaf resolution

To compare singular cohomology with sheaf cohomology, consider the
contravariant complex

\[
  U\longmapsto C^\bullet(U;\mathbb R)
\]

on the open subsets of \(X\), and sheafify it degree by degree.  Locally
constant real functions map to degree-zero singular cochains by assigning
the same number to every vertex.

@include{lean:JJMath.Cohomology.RealConstantAddSheaf}

@include{lean:JJMath.Cohomology.realSingularCochainSheafComplex}

On a locally contractible space this augmented complex is exact on stalks.
Indeed, near any point one may shrink to a neighborhood whose inclusion into
the original neighborhood is null-homotopic.  Positive-degree cocycles then
become coboundaries by homotopy invariance, while a degree-zero cocycle becomes
locally constant.  Exactness and monicity of morphisms of sheaves can be
checked stalkwise, so this gives the standard resolution of the constant real
sheaf.

@include{lean:JJMath.Cohomology.exists_sheafifiedOpenRealSingularCochainSheafAugmentation_with_resolution_properties}

## Why the resolution is acyclic

If \(V\subset U\), then \(C_n(V;\mathbb R)\to C_n(U;\mathbb R)\) is
injective: it is induced by an injection of the bases of singular simplices.
Because real vector spaces are injective modules, every real linear
functional on \(C_n(V;\mathbb R)\) extends to \(C_n(U;\mathbb R)\).  Thus
restriction of singular cochains is surjective.

@include{lean:JJMath.Cohomology.realSingularCochainOpenPresheafComplex_restriction_epi}

Surjective restriction maps survive sheafification, so the sheafified
singular-cochain sheaves are flasque.

@include{lean:JJMath.Cohomology.sheafification_preserves_flasque_addCommGrp_of_toSheafify_app_epi}

Flasque sheaves have no positive sheaf cohomology.  One embeds a flasque
sheaf into an injective sheaf, observes that the quotient remains flasque,
and uses the long exact sequence together with dimension shifting.

@include{lean:JJMath.Cohomology.sheafCohomology_subsingleton_of_flasque}

## Global sections and the comparison map

The whole space, regarded as its top open subset, has the same singular
cohomology as \(X\).  The sheafification units in each degree assemble to a
cochain map

\[
  C^\bullet(X;\mathbb R)
    \longrightarrow
  \Gamma\bigl(X,\mathcal C^\bullet_{\mathrm{sing}}\bigr).
\]

@include{lean:JJMath.Cohomology.realSingularCohomology_topOpen_linearEquiv}

@include{lean:JJMath.Cohomology.openSingularCochainTopToSheafifiedGlobalSections}

The kernel argument illustrates the one genuinely geometric point in the
comparison.  If a global sheafified cocycle is a boundary, local
representatives give ordinary local primitives.  In degree zero, local
vanishing of a locally constant cocycle immediately implies global
vanishing.

@include{lean:JJMath.Cohomology.openSingularCochainTop_homologyπ_zero_eq_zero_of_sheafified_boundary_subdivision}

In positive degree, a single global sheafified primitive produces compatible
ordinary local boundary representatives.

@include{lean:JJMath.Cohomology.openSingularCochainTopCycleLocallyBoundary_succ_of_sheafified_globalPrimitive}

Local exactness alone does not manufacture a global singular-cochain
primitive.  The remaining mathematical step is the classical subdivision
argument: repeatedly subdivide each singular simplex until its pieces lie in
members of the chosen cover, then use the compatibility inherited from the
single sheafified primitive to assemble the local primitives.  Keeping this
step conceptually separate prevents the categorical transport surrounding
sheafification from obscuring the geometric content of the comparison.

## Vanishing results used later

The contravariance established above gives a useful formal consequence.  If
\(A\) is a retract of \(X\), the identity on \(H^n(A;R)\) factors through
\(H^n(X;R)\).  Hence vanishing on \(X\) implies vanishing on \(A\).

@include{lean:JJMath.Cohomology.singularCohomology_isZero_of_retract}

Replacing a strict retraction by a homotopy inverse and using homotopy
invariance shows that vanishing singular cohomology is an invariant of
homotopy type.

@include{lean:JJMath.Cohomology.singularCohomology_isZero_iff_of_homotopyEquiv}

Finally, over \(\mathbb R\), taking linear duals is exact.  Therefore
vanishing of \(H_1(X;\mathbb R)\) implies vanishing of
\(H^1(X;\mathbb R)\), the form needed for simply connected surfaces.

@include{lean:JJMath.Cohomology.realSingularCohomology_one_isZero_of_realSingularHomology_one_isZero}
