# Roadmap for the de Rham comparison theorem

## Goal

For a finite-dimensional Hausdorff sigma-compact smooth manifold without
boundary, prove an $\mathbb R$-linear equivalence

$$
H_{\mathrm{dR}}^n(M;\mathbb R)
\simeq_{\mathbb R}
H_{\mathrm{sing}}^n(M;\mathbb R).
$$

The public endpoint is now present in
`JJMath/Manifold/DeRhamTheorem.lean`:

```lean
theorem deRhamCohomology_nonempty_linearEquiv_realSingularCohomology
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H) [Iℝ.Boundaryless]
    [IsManifold Iℝ ∞ M] [FiniteDimensional ℝ E]
    [T2Space M] [SigmaCompactSpace M]
    (n : ℕ) :
    Nonempty
      (DeRhamCohomology (I := Iℝ) (M := M) (A := ℝ) n ≃ₗ[ℝ]
        ↥(JJMath.Cohomology.RealSingularCohomology
          (TopCat.of M : TopCat) n))
```

It elaborates and builds.  Its axiom audit contains only `propext`,
`Classical.choice`, and `Quot.sound`: in particular, it has no dependency on
`sorryAx`.  The completed comparison contains no use of the Sella paper or its
localized-cochain construction.

## Proof architecture

Both theories are compared with sheaf cohomology of the constant real sheaf:

```text
de Rham cohomology
        |
        | exact fine resolution by smooth forms
        v
large-universe constant-sheaf cohomology
        |
        | coefficient-universe comparison
        v
ordinary constant-sheaf cohomology
        ^
        | exact flasque resolution by singular cochains
        |
real singular cohomology
```

The large coefficient universe is forced by the type of smooth forms.  The
implementation now crosses back to the ordinary universe by lifting the
sheafified singular-cochain resolution itself.  Exactness preserves the
resolution, mixed-universe flasque acyclicity applies to its terms, and the
natural isomorphism between lifted global sections and the lift of ordinary
global sections compares the two resulting cohomology groups.  This avoids
both an abstract Ext-invariance theorem and the Sella construction.

## Completed implementation

| Component | Main declarations |
| --- | --- |
| Differential forms and de Rham cohomology | `deRhamDifferential`, `DeRhamCohomology` |
| Convex and local Poincare lemmas | `deRham_poincareLemma_convex_open`, `deRham_local_poincareBasis_boundarylessModel` |
| Sheaves and the cochain complex of smooth forms | `smoothFormsAddPresheaf_isSheaf`, `smoothFormsAddSheafCochainComplex` |
| Exactness of the augmented de Rham sheaf complex | `realConstantAddSheaf_to_smoothFormsAddSheaf_exact`, `smoothFormsAddSheafCochainComplex_exactAt_succ_of_local_poincare` |
| Smooth-form sheaves are fine | `smoothFormsAddSheaf_isFine` |
| Fine sheaves are acyclic | `cohomology_subsingleton_of_isFine` |
| The constant sheaf embeds in smooth zero-forms | `realConstantAddSheafToSmoothFormsAddSheaf_mono` |
| Global smooth forms compute de Rham cohomology, with scalars | `exists_deRhamCohomology_addEquiv_smoothFormsAddSheafGlobalSectionsCohomology_with_map_smul` |
| General scalar-natural acyclic-resolution comparison | `exists_globalSections_homology_addEquiv_sheafCohomology_of_acyclic_resolution_with_family_map_core` |
| Singular cohomology, functoriality, and homotopy invariance | `RealSingularCohomology`, `singularCohomologyMap_eq_of_homotopy` |
| Exact sheafified singular-cochain resolution | `exists_sheafifiedOpenRealSingularCochainSheafAugmentation_with_resolution_properties` |
| Sectionwise surjectivity of singular-cochain sheafification | `realSingularCochain_toSheafify_app_surjective_of_paracompact` |
| Flasqueness and acyclicity of the singular resolution | `realSingularCochainSheafComplex_isFlasque_of_open_paracompact`, `sheafCohomology_subsingleton_of_flasque` |
| Mixed-universe flasque acyclicity | `sheafCohomology_subsingleton_of_flasque` with coefficient universe independent of the space universe |
| Global sheafified singular cochains compute constant-sheaf cohomology, with scalars | `exists_realSingularCochainSheafGlobalSectionsCohomology_addEquiv_realConstantSheafCohomology_with_map_smul_of_open_paracompact` |
| Direct universe comparison through the lifted singular resolution | `exists_liftedRealSingularCochainSheafGlobalSectionsCohomology_addEquiv_with_map_smul`, `exists_liftedRealSingularCochainGlobalSections_homology_iso_with_scalar` |
| Open subspaces of the manifolds in scope are paracompact | `smoothManifold_open_paracompactSpace` |
| Scalar-compatible comparison compositions | the three `exists_...with_smul` theorems in `DeRhamComparison/Final.lean` |
| Public de Rham–singular linear equivalence | `deRhamCohomology_nonempty_linearEquiv_realSingularCohomology` |

There are no remaining proof stubs in the dependency graph of the public
endpoint.

## Phase A: barycentric subdivision and small chains

The standard simplex and universal-prism infrastructure is in
`JJMath/Topology/SingularSubdivision.lean`; the mesh and small-chain argument
is in `JJMath/Topology/SmallSingularChains.lean`.

1. affine self-maps of the standard simplex;
2. initial-segment barycenters indexed by permutations;
3. the signed barycentric subdivision of a singular simplex;
4. its linear extension to each singular-chain degree;
5. the open-cover-small chain subcomplex and its inclusion.

Completed:

1. Expand the boundary of the permutation sum.
2. Pair internal face terms by the adjacent transposition that swaps the two
   vertices meeting at that face; their signs are opposite.
3. Identify the two unpaired outer faces with subdivisions of the
   corresponding faces of the original simplex.
4. Use this to prove `barycentricSubdivisionDegree_comm`.

Also completed:

1. Contract the singular complex of every standard simplex to a complex
   concentrated in degree zero and deduce that all positive cycles bound.
2. Use those fillings inductively, in the acyclic-models style, to construct
   universal prism operators in every degree.
3. Prove their naturality and assemble them into a chain homotopy
   $\partial T+T\partial=\mathrm{id}-\mathrm{Sd}$, without using an explicit
   cone formula or the Sella paper.

Also completed:

1. Decompose the vertices of every barycentric child around their common
   first vertex and prove the sharp mesh contraction
   $\operatorname{mesh}(\mathrm{Sd}\,\Delta^n)
   \le n/(n+1)\operatorname{mesh}(\Delta^n)$.
2. Iterate this estimate and combine it with a Lebesgue-number argument on
   the compact standard simplex to make every refined child subordinate to
   an arbitrary open cover.
3. Use the direct-sum description of singular chains to pass from individual
   simplices to a single common subdivision exponent for every finite chain.
4. Prove that the inclusion of cover-small chains is bijective on homology,
   hence a quasi-isomorphism.
5. Use projectivity of the free real chain groups to upgrade the
   quasi-isomorphism to
   `smallRealSingularChainsInclusion_homotopyEquiv`.

Acceptance gate:

```text
lake build JJMath.Topology.SmallSingularChains
```

succeeds with no `sorry` warning.

## Phase B: ordinary singular cohomology versus sheaf cohomology — completed

The surrounding sheaf theory is complete:

- the singular-cochain presheaf and its sheafification;
- exactness on locally contractible spaces;
- sectionwise surjectivity on spaces whose open subspaces are paracompact;
- flasqueness of every sheafified cochain term;
- scalar-compatible computation of constant-sheaf cohomology.

Phase A is used as follows:

1. A cocycle in the kernel of sheafification vanishes on all simplices small
   for some open cover.
2. Subdivide an arbitrary simplex until all pieces are small.
3. The subdivision homotopy and closedness identify the cocycle's value on the
   original simplex with its value on the subdivided chain, hence with zero.
4. For surjectivity on cohomology, lift a global sheafified cocycle to an
   ordinary cochain and use the same small-chain argument to correct its
   coboundary by a global primitive.
5. This proves
   `openSingularCochainTopToSheafifiedGlobalSections_homologyMap_bijective_of_subdivision`.

All later additive and linear singular comparisons follow from this theorem.

Acceptance gate:

```text
lake build JJMath.Topology.SingularCohomology
```

succeeds with no `sorry` warning.

## Phase C: fine sheaves are acyclic — completed

This phase deliberately avoids both Sella's construction and a separate
Čech-to-derived comparison theorem.  It uses the classical
discontinuous-sections resolution and dimension shifting:

1. For a sheaf $\mathcal F$, form the discontinuous-sections sheaf
   $\mathcal D(\mathcal F)$ whose sections are products of stalks.
2. Embed $\mathcal F$ monomorphically into $\mathcal D(\mathcal F)$ by taking
   germs, and let $\mathcal Q(\mathcal F)$ be the cokernel.
3. Prove $\mathcal D(\mathcal F)$ is flasque.
4. If $\mathcal F$ is fine, choose a locally finite shrinking and a
   subordinate partition of the identity.  Descend the partition
   endomorphisms to $\mathcal Q(\mathcal F)$ and control their germ supports
   by the closures of the shrinking.  This proves $\mathcal Q(\mathcal F)$ is
   fine.
5. Use the skyscraper adjunction and the filtered-colimit description of
   stalks to lift a quotient section locally.
6. Multiply those local lifts by the partition endomorphisms and take their
   locally finite sum.  The resulting discontinuous section is a global lift,
   so $\Gamma(\mathcal D(\mathcal F))\to\Gamma(\mathcal Q(\mathcal F))$ is
   surjective.
7. Apply flasque acyclicity and the long exact cohomology sequence.  The
   degree-one group vanishes by global surjectivity; higher degrees shift to
   the fine quotient and vanish inductively.

The theorem is universe-polymorphic in both the space and coefficients and is
then applied to `smoothFormsAddSheaf_isFine`.

Acceptance gate:

```text
lake build JJMath.Topology.FineSheafAcyclic
```

succeeds with no `sorry` warning.

## Phase D: the coefficient-universe gap — completed

### Completed: monicity of constants in smooth functions

This is now proved without a same-universe stalk shortcut.  The proof:

1. proves the presheaf map from constants to smooth zero-forms is locally
   injective;
2. applies each universe-lifted point fiber, where locally injective
   presheaf maps become injective;
3. uses that point fibers invert the sheafification unit;
4. invokes the conservative family of lifted points to reflect monomorphisms.

### Direct lifted-resolution comparison

The Ext-localization route has been removed from the dependency graph.  The
completed replacement:

1. proves flasque acyclicity with a coefficient universe independent of the
   space universe;
2. lifts the exact singular-cochain resolution objectwise;
3. proves its lifted terms remain flasque and hence acyclic;
4. applies the scalar-natural acyclic-resolution theorem in the large
   coefficient universe;
5. identifies global sections of the lifted complex with the lifted ordinary
   global-section complex;
6. commutes universe lift with homology and then removes `ULift`;
7. composes with the ordinary singular resolution comparison.

`DeRhamComparison/Final.lean` now builds without an explicit theorem stub, and
the route does not import or recreate Sella's localized-cochain construction.

## Phase E: final audit and documentation — completed

The comparison compositions and public theorem are implemented.  The final
checks are:

1. run a source scan for `sorry` in all comparison dependencies;
2. run an axiom audit on
   `JJMath.Manifold.deRhamCohomology_nonempty_linearEquiv_realSingularCohomology`;
3. require that the audit contain only the standard axioms already used by
   Mathlib and not `sorryAx`;
4. run the full build;
5. keep the Handwave articles synchronized with the final dependency graph.

Completed build checks:

```text
lake build JJMath.Topology.SmallSingularChains        # succeeds, no stubs
lake build JJMath.Topology.SingularCohomology          # succeeds, no stubs
lake build JJMath.Topology.FineSheafAcyclic            # succeeds, no stubs
lake build JJMath.Manifold.DeRhamComparison.Final      # succeeds, no stubs
lake build JJMath.Manifold.DeRhamTheorem               # succeeds, no stubs
```

The source scan finds no `sorry`, `admit`, or `axiom` declaration in the
comparison files.  The public theorem's axiom audit reports precisely
`propext`, `Classical.choice`, and `Quot.sound`.

## Later extensions

Once the linear comparison is `sorry`-free:

1. define integration of forms over smooth singular simplices;
2. prove Stokes' theorem and identify integration with the comparison;
3. prove naturality under smooth maps;
4. prove compatibility of wedge and cup products;
5. extend the statement to manifolds with boundary or corners after proving
   the corresponding local Poincare basis.
