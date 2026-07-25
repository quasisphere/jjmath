# Singular Cohomology

For a space $X$ and a commutative coefficient ring $R$, the singular
chain complex $C_\bullet(X;R)$ is freely generated in degree $n$ by
continuous maps $\Delta^n\to X$.  Dualizing gives the cochain complex

\[
  C^n(X;R)=\operatorname{Hom}_R(C_n(X;R),R),
  \qquad (\delta\varphi)(c)=\varphi(\partial c),
\]

and its cohomology is $H^n(X;R)$.  The harmless universe lift in the
coefficient module allows the same definition for spaces and coefficients
living in different universes.

@include{lean:JJMath.Cohomology.SingularChains}

@include{lean:JJMath.Cohomology.SingularCohomology}

@include{lean:JJMath.Cohomology.RealSingularCohomology}

## Functoriality and homotopy

A continuous map $f:X\to Y$ pushes chains forward and therefore pulls
cochains back.  Passing to cohomology gives

\[
  f^*:H^n(Y;R)\longrightarrow H^n(X;R),
  \qquad (g\circ f)^*=f^*\circ g^*.
\]



The prism operator associated with a homotopy gives a chain homotopy between
the two maps on singular chains.  Dualizing that homotopy and passing to
cohomology proves homotopy invariance.


## The singular-cochain sheaf resolution

To compare singular cohomology with sheaf cohomology, consider the
contravariant complex

\[
  U\longmapsto C^\bullet(U;\mathbb R)
\]

on the open subsets of $X$, and sheafify it degree by degree.  Locally
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

If $V\subset U$, then $C_n(V;\mathbb R)\to C_n(U;\mathbb R)$ is
injective: it is induced by an injection of the bases of singular simplices.
Because real vector spaces are injective modules, every real linear
functional on $C_n(V;\mathbb R)$ extends to $C_n(U;\mathbb R)$.  Thus
restriction of singular cochains is surjective.

@include{lean:JJMath.Cohomology.realSingularCochainOpenPresheafComplex_restriction_epi}

Surjective restriction maps do not survive sheafification merely from local
surjectivity of the sheafification unit.  For the spaces used in the de Rham
comparison, the missing global lifting is supplied by paracompactness of every
open subspace.  Starting from local cochain representatives of a sheafified
section, choose a locally finite shrinking with closures inside the original
representing opens.  For each singular simplex, use one shrunken open
containing its image to choose its value.  Near a fixed point, only finitely
many members of the shrinking remain relevant; local injectivity of
sheafification makes their representatives agree after one further finite
shrinking.  The resulting global cochain therefore represents the prescribed
sheafified section.

@include{lean:JJMath.Cohomology.exists_locallyFinite_open_shrinking}

@include{lean:JJMath.Cohomology.realSingularCochainOpenPresheafComplex_exists_global_cochain_of_chosen_local_simplex}

@include{lean:JJMath.Cohomology.realSingularCochain_toSheafify_app_surjective_of_paracompact}

Consequently the sheafification unit is sectionwise epimorphic and the
sheafified singular-cochain sheaves are flasque.

@include{lean:JJMath.Cohomology.sheafification_preserves_flasque_addCommGrp_of_toSheafify_app_epi}

@include{lean:JJMath.Cohomology.realSingularCochainSheafComplex_isFlasque_of_open_paracompact}

Flasque sheaves have no positive sheaf cohomology.  One embeds a flasque
sheaf into an injective sheaf, observes that the quotient remains flasque,
and uses the long exact sequence together with dimension shifting.

@include{lean:JJMath.Cohomology.sheafCohomology_subsingleton_of_flasque}

The exact augmented singular-cochain sheaf complex is therefore an acyclic
resolution of the constant real sheaf.  Its global-section cohomology computes
$H^n(X;\underline{\mathbb R})$, and the comparison can be chosen
simultaneously compatible with multiplication by every real scalar.

@include{lean:JJMath.Cohomology.realSingularCochainSheafGlobalSectionsCohomology_nonempty_addEquiv_realConstantSheafCohomology_of_open_paracompact}

@include{lean:JJMath.Cohomology.exists_realSingularCochainSheafGlobalSectionsCohomology_addEquiv_realConstantSheafCohomology_with_map_smul_of_open_paracompact}

## Global sections and the comparison map

The whole space, regarded as its top open subset, has the same singular
cohomology as $X$.  The sheafification units in each degree assemble to a
cochain map

\[
  C^\bullet(X;\mathbb R)
    \longrightarrow
  \Gamma\bigl(X,\mathcal C^\bullet_{\mathrm{sing}}\bigr).
\]

@include{lean:JJMath.Cohomology.realSingularCohomology_topOpen_linearEquiv}

@include{lean:JJMath.Cohomology.openSingularCochainTopToSheafifiedGlobalSections}

Barycentric subdivision writes each singular simplex as the alternating sum
of the simplices formed by flags of its faces.  It commutes with the boundary.
The homotopy to the identity is constructed by acyclic models: the singular
complex of each standard simplex contracts to degree zero, so the obstruction
cycle in each successive degree has a universal filler.  Pushing these
fillers along singular simplices gives natural prism operators
$T_n:C_n(X;\mathbb R)\to C_{n+1}(X;\mathbb R)$ with
$\partial T+T\partial=1-\operatorname{Sd}$.  This avoids choosing an explicit
geometric cone formula.

@include{lean:JJMath.Cohomology.barycentricSubdivision}

@include{lean:JJMath.Cohomology.barycentricSubdivisionDegree_comm}

@include{lean:JJMath.Cohomology.standardSimplexRealSingularChains_homotopyEquiv_singleZero}

@include{lean:JJMath.Cohomology.subdivisionPrismHomotopy}

For the mesh estimate, write every vertex of a barycentric child as

\[
  \frac1{n+1}e_{p(0)}+\frac n{n+1}r_k,
  \qquad r_k\in\Delta^n.
\]

The common first term cancels when two child vertices are subtracted, so one
subdivision contracts vertex diameter by at most $n/(n+1)$.  Iteration gives
geometric decay, and a Lebesgue number for the pullback of the cover to the
compact standard simplex then makes every sufficiently refined child
subordinate to one cover member.

@include{lean:stdSimplex.iteratedBarycentricAffineMap_range_diam_le}

@include{lean:stdSimplex.iteratedBarycentricAffineMaps_subordinate}

A singular chain has finite support.  Expressing it in the direct sum on
singular-simplex generators permits induction over that support: choose a
subdivision exponent for each generator and promote finitely many exponents
to one common exponent.  Thus every chain becomes cover-small after finitely
many subdivisions.

@include{lean:JJMath.Cohomology.singularChain_eventually_factors_small}

Surjectivity on homology follows by subdividing a cycle until it is small.
For injectivity, subdivide an ordinary bounding chain until it is small.
Since subdivision is homotopic to the identity both on ordinary and on
cover-small chains, inclusion is a quasi-isomorphism.  The chain groups are
free real modules, so the quasi-isomorphism is a chain-homotopy equivalence.

@include{lean:JJMath.Cohomology.smallRealSingularChainsInclusion_homotopyEquiv}

Consequently, an ordinary cocycle that vanishes locally vanishes globally,
and compatible local primitives can be assembled at the cohomology level.
The ordinary-to-sheafified cochain map is therefore a quasi-isomorphism.

@include{lean:JJMath.Cohomology.openSingularCochainTopToSheafifiedGlobalSections_homologyMap_bijective_of_subdivision}

Combining this quasi-isomorphism with the flasque resolution gives a
scalar-compatible equivalence between real singular cohomology and real
constant-sheaf cohomology.

@include{lean:JJMath.Cohomology.realSingularCohomology_nonempty_linearEquiv_realConstantSheafCohomology_of_open_paracompact}

## Vanishing results used later

The contravariance established above gives a useful formal consequence.  If
$A$ is a retract of $X$, the identity on $H^n(A;R)$ factors through
$H^n(X;R)$.  Hence vanishing on $X$ implies vanishing on $A$.


Replacing a strict retraction by a homotopy inverse and using homotopy
invariance shows that vanishing singular cohomology is an invariant of
homotopy type.


Finally, over $\mathbb R$, taking linear duals is exact.  Therefore
vanishing of $H_1(X;\mathbb R)$ implies vanishing of
$H^1(X;\mathbb R)$, the form needed for simply connected surfaces.
