import JJMath.Topology.SingularSubdivision
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Small singular chains compute singular homology

This file completes the barycentric-subdivision argument begun in
`JJMath.Topology.SingularSubdivision`.  It proves the mesh estimate, shows
that every finite singular chain becomes subordinate to a prescribed open
cover after finitely many subdivisions, and deduces that the inclusion of
cover-small chains is a chain-homotopy equivalence.

The proof uses the ordinary subdivision prism and elementary compactness.  It
does not use localized cochains or the Sella construction.
-/

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open Simplicial
open TopologicalSpace
open HomologicalComplex
open scoped DirectSum

namespace JJMath.Cohomology

noncomputable section

universe v

/--
%%handwave
name:
  Projection onto singular chains subordinate to a cover
statement:
  In degree $n$, send a singular simplex to itself when its image lies in one
  member of the cover and to zero otherwise, extending linearly to real
  singular chains.
-/
noncomputable def smallRealSingularChainsRetract
    (X : TopCat.{v}) {ι : Type v} (U : ι → Opens X) (n : ℕ) :
    (realSingularChains X).X n ⟶ (smallRealSingularChains X U).X n := by
  classical
  exact Sigma.desc fun σ =>
    if h : σ ∈ (openCoverSmallSingularSet X U).obj (op ⦋n⦌) then
      (openCoverSmallSingularSet X U : SSet.{v}).ιChainComplex
        (R := realSingularChainCoefficient) ⟨σ, h⟩
    else 0

/--
%%handwave
name:
  Projection retracts the inclusion of cover-small chains
statement:
  In every degree, including cover-small singular chains and then projecting
  back to the cover-small generators is the identity.
proof:
  Evaluate the composite on each cover-small simplex.  Its defining
  smallness witness selects the nonzero branch of the projection.
-/
theorem smallRealSingularChainsInclusion_retract
    (X : TopCat.{v}) {ι : Type v} (U : ι → Opens X) (n : ℕ) :
    (smallRealSingularChainsInclusion X U).f n ≫
      smallRealSingularChainsRetract X U n = 𝟙 _ := by
  classical
  apply SSet.chainComplex_hom_ext
  rintro ⟨σ, hσ⟩
  dsimp only [smallRealSingularChainsInclusion]
  rw [SSet.ι_chainComplexMap_f_assoc, Category.comp_id]
  change
    (TopCat.toSSet.obj X).ιChainComplex
        (R := realSingularChainCoefficient) σ ≫ smallRealSingularChainsRetract X U n =
      (openCoverSmallSingularSet X U : SSet.{v}).ιChainComplex
        (R := realSingularChainCoefficient) ⟨σ, hσ⟩
  dsimp only [smallRealSingularChainsRetract, SSet.ιChainComplex]
  refine (Sigma.ι_desc (fun σ =>
    if h : σ ∈ (openCoverSmallSingularSet X U).obj (op ⦋n⦌) then
      Sigma.ι (fun _ : (openCoverSmallSingularSet X U).obj (op ⦋n⦌) =>
        realSingularChainCoefficient) ⟨σ, h⟩
    else 0) σ).trans ?_
  rw [dif_pos hσ]
  rfl

/--
%%handwave
name:
  Degreewise injectivity of the cover-small chain inclusion
statement:
  In every degree, the homomorphism from cover-small real singular chains to
  all real singular chains is a monomorphism.
proof:
  The explicit projection onto cover-small generators is a retraction of the
  inclusion, so the inclusion is a split monomorphism.
-/
instance smallRealSingularChainsInclusion_component_mono
    (X : TopCat.{v}) {ι : Type v} (U : ι → Opens X) (n : ℕ) :
    Mono ((smallRealSingularChainsInclusion X U).f n) := by
  letI : IsSplitMono ((smallRealSingularChainsInclusion X U).f n) :=
    IsSplitMono.mk'
      { retraction := smallRealSingularChainsRetract X U n
        id := smallRealSingularChainsInclusion_retract X U n }
  infer_instance

/--
%%handwave
name:
  Barycentric child of a cover-small simplex
statement:
  If a singular $n$-simplex is contained in one member of an open cover, then
  its barycentric child indexed by any permutation is contained in that same
  cover member.
-/
noncomputable def smallBarycentricSubdivisionSimplex
    (X : TopCat.{v}) {ι : Type v} (U : ι → Opens X) (n : ℕ)
    (σ : (openCoverSmallSingularSet X U : SSet.{v}).obj (op ⦋n⦌))
    (p : Equiv.Perm (Fin (n + 1))) :
    (openCoverSmallSingularSet X U : SSet.{v}).obj (op ⦋n⦌) := by
  refine ⟨barycentricSubdivisionSingularSimplex X n σ.1 p, ?_⟩
  rcases σ.2 with ⟨i, hi⟩
  refine ⟨i, ?_⟩
  rintro y ⟨z, rfl⟩
  exact hi ⟨stdSimplex.barycentricSubdivisionMap p z, rfl⟩

/--
%%handwave
name:
  Barycentric subdivision on cover-small chains in one degree
statement:
  In degree $n$, cover-small barycentric subdivision is the signed sum of the
  $(n+1)!$ barycentric children of every cover-small singular simplex.
-/
noncomputable def smallBarycentricSubdivisionDegree
    (X : TopCat.{v}) {ι : Type v} (U : ι → Opens X) (n : ℕ) :
    (smallRealSingularChains X U).X n ⟶
      (smallRealSingularChains X U).X n := by
  classical
  exact Sigma.desc fun σ =>
    ∑ p : Equiv.Perm (Fin (n + 1)),
      ((Equiv.Perm.sign p : ℤˣ) : ℤ) •
        (openCoverSmallSingularSet X U : SSet.{v}).ιChainComplex
          (R := realSingularChainCoefficient)
          (smallBarycentricSubdivisionSimplex X U n σ p)

/--
%%handwave
name:
  Cover-small subdivision on a generator
statement:
  The subdivision of a cover-small singular $n$-simplex is its signed sum over
  all permutation-indexed barycentric children.
proof:
  Evaluate the linear extension defining subdivision on the chosen free
  generator.
-/
theorem smallBarycentricSubdivisionGenerator
    (X : TopCat.{v}) {ι : Type v} (U : ι → Opens X) (n : ℕ)
    (σ : (openCoverSmallSingularSet X U : SSet.{v}).obj (op ⦋n⦌)) :
    (openCoverSmallSingularSet X U : SSet.{v}).ιChainComplex
        (R := realSingularChainCoefficient) σ ≫
      smallBarycentricSubdivisionDegree X U n =
      ∑ p : Equiv.Perm (Fin (n + 1)),
        ((Equiv.Perm.sign p : ℤˣ) : ℤ) •
          (openCoverSmallSingularSet X U : SSet.{v}).ιChainComplex
            (R := realSingularChainCoefficient)
            (smallBarycentricSubdivisionSimplex X U n σ p) := by
  exact Sigma.ι_desc _ _

/--
%%handwave
name:
  Compatibility of small and ordinary subdivision
statement:
  Including a cover-small chain after barycentric subdivision gives the same
  ordinary chain as first including it and then subdividing.
proof:
  Check the equality on each free generator and identify every cover-small
  child with its underlying ordinary barycentric child.
-/
theorem smallBarycentricSubdivisionCompatibility
    (X : TopCat.{v}) {ι : Type v} (U : ι → Opens X) (n : ℕ) :
    smallBarycentricSubdivisionDegree X U n ≫
        (smallRealSingularChainsInclusion X U).f n =
      (smallRealSingularChainsInclusion X U).f n ≫
        barycentricSubdivisionDegree X n := by
  apply SSet.chainComplex_hom_ext
  rintro ⟨σ, hσ⟩
  simp only [← Category.assoc]
  rw [smallBarycentricSubdivisionGenerator]
  rw [Preadditive.sum_comp]
  simp_rw [Preadditive.zsmul_comp]
  dsimp only [smallRealSingularChainsInclusion]
  simp_rw [SSet.ι_chainComplexMap_f]
  change
    (∑ p : Equiv.Perm (Fin (n + 1)),
      ((Equiv.Perm.sign p : ℤˣ) : ℤ) •
        (TopCat.toSSet.obj X).ιChainComplex
          (R := realSingularChainCoefficient)
          (barycentricSubdivisionSingularSimplex X n σ p)) =
      (TopCat.toSSet.obj X).ιChainComplex
          (R := realSingularChainCoefficient) σ ≫
        barycentricSubdivisionDegree X n
  rw [singularSimplex_comp_barycentricSubdivisionDegree]

/--
%%handwave
name:
  Cover-small barycentric subdivision is a chain map
statement:
  On cover-small chains, barycentric subdivision commutes with the boundary
  from degree $n+1$ to degree $n$.
proof:
  Postcompose both sides with the monic inclusion into ordinary singular
  chains, use compatibility with ordinary subdivision, and apply the
  subdivision boundary formula there.
-/
theorem smallBarycentricSubdivisionDegree_comm
    (X : TopCat.{v}) {ι : Type v} (U : ι → Opens X) (n : ℕ) :
    smallBarycentricSubdivisionDegree X U (n + 1) ≫
        (smallRealSingularChains X U).d (n + 1) n =
      (smallRealSingularChains X U).d (n + 1) n ≫
        smallBarycentricSubdivisionDegree X U n := by
  apply (cancel_mono ((smallRealSingularChainsInclusion X U).f n)).1
  calc
    (smallBarycentricSubdivisionDegree X U (n + 1) ≫
          (smallRealSingularChains X U).d (n + 1) n) ≫
        (smallRealSingularChainsInclusion X U).f n =
      smallBarycentricSubdivisionDegree X U (n + 1) ≫
        ((smallRealSingularChains X U).d (n + 1) n ≫
          (smallRealSingularChainsInclusion X U).f n) :=
        Category.assoc _ _ _
    _ = smallBarycentricSubdivisionDegree X U (n + 1) ≫
        ((smallRealSingularChainsInclusion X U).f (n + 1) ≫
          (realSingularChains X).d (n + 1) n) := by
      rw [(smallRealSingularChainsInclusion X U).comm]
    _ = (smallBarycentricSubdivisionDegree X U (n + 1) ≫
          (smallRealSingularChainsInclusion X U).f (n + 1)) ≫
        (realSingularChains X).d (n + 1) n := by
      rw [Category.assoc]
    _ = ((smallRealSingularChainsInclusion X U).f (n + 1) ≫
          barycentricSubdivisionDegree X (n + 1)) ≫
        (realSingularChains X).d (n + 1) n := by
      rw [smallBarycentricSubdivisionCompatibility]
    _ = (smallRealSingularChainsInclusion X U).f (n + 1) ≫
        (barycentricSubdivisionDegree X (n + 1) ≫
          (realSingularChains X).d (n + 1) n) :=
      Category.assoc _ _ _
    _ = (smallRealSingularChainsInclusion X U).f (n + 1) ≫
        ((realSingularChains X).d (n + 1) n ≫
          barycentricSubdivisionDegree X n) := by
      rw [barycentricSubdivisionDegree_comm]
    _ = ((smallRealSingularChainsInclusion X U).f (n + 1) ≫
          (realSingularChains X).d (n + 1) n) ≫
        barycentricSubdivisionDegree X n := by
      rw [Category.assoc]
    _ = ((smallRealSingularChains X U).d (n + 1) n ≫
          (smallRealSingularChainsInclusion X U).f n) ≫
        barycentricSubdivisionDegree X n := by
      rw [(smallRealSingularChainsInclusion X U).comm]
    _ = (smallRealSingularChains X U).d (n + 1) n ≫
        ((smallRealSingularChainsInclusion X U).f n ≫
          barycentricSubdivisionDegree X n) :=
      Category.assoc _ _ _
    _ = (smallRealSingularChains X U).d (n + 1) n ≫
        (smallBarycentricSubdivisionDegree X U n ≫
          (smallRealSingularChainsInclusion X U).f n) := by
      rw [smallBarycentricSubdivisionCompatibility]
    _ = ((smallRealSingularChains X U).d (n + 1) n ≫
          smallBarycentricSubdivisionDegree X U n) ≫
        (smallRealSingularChainsInclusion X U).f n := by
      rw [Category.assoc]

/--
%%handwave
name:
  Barycentric subdivision of cover-small singular chains
statement:
  The degreewise cover-small subdivision operators assemble into an
  endomorphism of the cover-small real singular-chain complex.
-/
noncomputable def smallBarycentricSubdivision
    (X : TopCat.{v}) {ι : Type v} (U : ι → Opens X) :
    smallRealSingularChains X U ⟶ smallRealSingularChains X U :=
  ChainComplex.ofHom
    (smallBarycentricSubdivisionDegree X U)
    (smallBarycentricSubdivisionDegree_comm X U)

/--
%%handwave
name:
  Inclusion of a cover member into the ambient space
statement:
  For a member $U_i$ of an open cover of $X$, define the canonical continuous
  map $U_i\hookrightarrow X$.
-/
noncomputable def openSingularChainsInclusion
    (X : TopCat.{v}) {ι : Type v} (U : ι → Opens X) (i : ι) :
    (TopCat.of (U i) : TopCat.{v}) ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/--
%%handwave
name:
  Singular simplices in one cover member are cover-small
statement:
  The singular simplicial set of $U_i$ maps to the simplicial subset of
  singular simplices in $X$ contained in some member of the cover.
-/
noncomputable def openSingularChainsToSmall
    (X : TopCat.{v}) {ι : Type v} (U : ι → Opens X) (i : ι) :
    TopCat.toSSet.obj (TopCat.of (U i) : TopCat.{v}) ⟶
      (openCoverSmallSingularSet X U : SSet.{v}) where
  app n := ↾fun σ =>
    ⟨((TopCat.toSSet.map (openSingularChainsInclusion X U i)).app n) σ, by
      refine ⟨i, ?_⟩
      rintro y ⟨z, rfl⟩
      change
        (TopCat.toSSetObjEquiv X n
          (((TopCat.toSSet.map (openSingularChainsInclusion X U i)).app n) σ) z) ∈ U i
      change
        ((TopCat.toSSetObjEquiv (TopCat.of (U i) : TopCat.{v}) n σ) z).1 ∈ U i
      exact ((TopCat.toSSetObjEquiv
        (TopCat.of (U i) : TopCat.{v}) n σ) z).2⟩
  naturality _ _ f := by
    ext σ
    apply Subtype.ext
    rfl

/--
%%handwave
name:
  Factorization of a cover-member inclusion through small simplices
statement:
  The map from singular simplices of $U_i$ to singular simplices of $X$
  factors through the cover-small singular simplicial subset.
proof:
  Both composites send a simplex to its composite with the inclusion
  $U_i\hookrightarrow X$, so they agree degreewise.
-/
theorem openSingularChainsToSmall_comp_inclusion
    (X : TopCat.{v}) {ι : Type v} (U : ι → Opens X) (i : ι) :
    openSingularChainsToSmall X U i ≫ (openCoverSmallSingularSet X U).ι =
      TopCat.toSSet.map (openSingularChainsInclusion X U i) := by
  ext n σ
  rfl

/--
%%handwave
name:
  A cover member containing a small simplex
statement:
  For every cover-small singular simplex, choose an index $i$ whose open set
  $U_i$ contains the image of the simplex.
-/
noncomputable def smallCoverIndex
    (X : TopCat.{v}) {ι : Type v} (U : ι → Opens X) (n : ℕ)
    (σ : (openCoverSmallSingularSet X U : SSet.{v}).obj (op ⦋n⦌)) :
    ι :=
  Classical.choose σ.2

/--
%%handwave
name:
  Image containment for the chosen cover member
statement:
  The image of a cover-small singular simplex is contained in the open set
  selected for it.
proof:
  This is the defining property of the chosen witness of cover-smallness.
-/
theorem smallCoverIndex_range
    (X : TopCat.{v}) {ι : Type v} (U : ι → Opens X) (n : ℕ)
    (σ : (openCoverSmallSingularSet X U : SSet.{v}).obj (op ⦋n⦌)) :
    Set.range (TopCat.toSSetObjEquiv X _ σ.1) ⊆
      (U (smallCoverIndex X U n σ) : Set X) :=
  Classical.choose_spec σ.2

/--
%%handwave
name:
  Lift of a small simplex to its chosen cover member
statement:
  A cover-small singular simplex in $X$ canonically lifts to a singular
  simplex in the selected open set $U_i$ containing its image.
-/
noncomputable def smallSimplexLift
    (X : TopCat.{v}) {ι : Type v} (U : ι → Opens X) (n : ℕ)
    (σ : (openCoverSmallSingularSet X U : SSet.{v}).obj (op ⦋n⦌)) :
    TopCat.toSSet.obj
      (TopCat.of (U (smallCoverIndex X U n σ)) : TopCat.{v}) _⦋n⦌ :=
  (TopCat.toSSetObjEquiv
    (TopCat.of (U (smallCoverIndex X U n σ)) : TopCat.{v}) _).symm
    ⟨fun z =>
      ⟨TopCat.toSSetObjEquiv X _ σ.1 z,
        smallCoverIndex_range X U n σ ⟨z, rfl⟩⟩,
      Continuous.subtype_mk
        (TopCat.toSSetObjEquiv X _ σ.1).continuous _⟩

/--
%%handwave
name:
  The lifted small simplex maps to the original simplex
statement:
  Composing the lift of a cover-small simplex with $U_i\hookrightarrow X$
  recovers its underlying singular simplex in $X$.
proof:
  Apply the equivalence between singular simplices and continuous maps and
  check pointwise.
-/
theorem smallSimplexLift_map
    (X : TopCat.{v}) {ι : Type v} (U : ι → Opens X) (n : ℕ)
    (σ : (openCoverSmallSingularSet X U : SSet.{v}).obj (op ⦋n⦌)) :
    ((TopCat.toSSet.map
      (openSingularChainsInclusion X U (smallCoverIndex X U n σ))).app _)
        (smallSimplexLift X U n σ) = σ.1 := by
  apply (TopCat.toSSetObjEquiv X _).injective
  ext z
  rfl

/--
%%handwave
name:
  Chain-level compatibility for a cover-member inclusion
statement:
  Mapping singular chains of $U_i$ through cover-small chains and then into
  all chains of $X$ equals the usual chain map induced by $U_i\hookrightarrow
  X$.
proof:
  Check the equality on singular-simplex generators using the simplicial
  factorization through the cover-small subset.
-/
theorem openSingularChainsCompatibility
    (X : TopCat.{v}) {ι : Type v} (U : ι → Opens X) (i : ι)
    (n : ℕ) :
    (SSet.chainComplexMap (openSingularChainsToSmall X U i)
        realSingularChainCoefficient).f n ≫
        (smallRealSingularChainsInclusion X U).f n =
      (realSingularChainFunctor.map (openSingularChainsInclusion X U i)).f n := by
  change
    (SSet.chainComplexMap (openSingularChainsToSmall X U i)
        realSingularChainCoefficient).f n ≫
        (SSet.chainComplexMap (openCoverSmallSingularSet X U).ι
          realSingularChainCoefficient).f n =
      (SSet.chainComplexMap
        (TopCat.toSSet.map (openSingularChainsInclusion X U i))
        realSingularChainCoefficient).f n
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, SSet.ι_chainComplexMap_f]
  rw [SSet.ι_chainComplexMap_f]
  rw [SSet.ι_chainComplexMap_f]
  change
    (TopCat.toSSet.obj X).ιChainComplex
        (R := realSingularChainCoefficient)
        (((openSingularChainsToSmall X U i ≫
          (openCoverSmallSingularSet X U).ι).app _) σ) =
      (TopCat.toSSet.obj X).ιChainComplex
        (R := realSingularChainCoefficient)
        (((TopCat.toSSet.map (openSingularChainsInclusion X U i)).app _) σ)
  rw [openSingularChainsToSmall_comp_inclusion]

/--
%%handwave
name:
  The subdivision prism of a small generator remains small
statement:
  For a cover-small singular $n$-simplex, its universal subdivision-prism
  chain in degree $n+1$ factors through the cover-small chain group.
proof:
  Lift the simplex to a chosen cover member, apply naturality of the universal
  prism under $U_i\hookrightarrow X$, and then use the chain-level
  factorization through cover-small chains.
-/
theorem subdivisionPrismGenerator_factors_small
    (X : TopCat.{v}) {ι : Type v} (U : ι → Opens X) (n : ℕ)
    (σ : (openCoverSmallSingularSet X U : SSet.{v}).obj (op ⦋n⦌)) :
    (TopCat.toSSet.obj X).ιChainComplex
        (R := realSingularChainCoefficient) σ.1 ≫
        (subdivisionPrismDegree n).map X =
      ((TopCat.toSSet.obj
          (TopCat.of (U (smallCoverIndex X U n σ)) :
            TopCat.{v})).ιChainComplex
          (R := realSingularChainCoefficient)
          (smallSimplexLift X U n σ) ≫
        (subdivisionPrismDegree n).map
          (TopCat.of (U (smallCoverIndex X U n σ)) : TopCat.{v}) ≫
        (SSet.chainComplexMap
          (openSingularChainsToSmall X U (smallCoverIndex X U n σ))
          realSingularChainCoefficient).f (n + 1)) ≫
        (smallRealSingularChainsInclusion X U).f (n + 1) := by
  let O :=
    (TopCat.of (U (smallCoverIndex X U n σ)) : TopCat.{v})
  let f : O ⟶ X :=
    openSingularChainsInclusion X U (smallCoverIndex X U n σ)
  let τ := smallSimplexLift X U n σ
  have hgen :
      (TopCat.toSSet.obj O).ιChainComplex
          (R := realSingularChainCoefficient) τ ≫
          (realSingularChainFunctor.map f).f n =
        (TopCat.toSSet.obj X).ιChainComplex
          (R := realSingularChainCoefficient) σ.1 := by
    change
      (TopCat.toSSet.obj O).ιChainComplex
          (R := realSingularChainCoefficient) τ ≫
          (SSet.chainComplexMap (TopCat.toSSet.map f)
            realSingularChainCoefficient).f n =
        (TopCat.toSSet.obj X).ιChainComplex
          (R := realSingularChainCoefficient) σ.1
    rw [SSet.ι_chainComplexMap_f]
    change
      (TopCat.toSSet.obj X).ιChainComplex
          (R := realSingularChainCoefficient)
          (((TopCat.toSSet.map f).app _) τ) =
        (TopCat.toSSet.obj X).ιChainComplex
          (R := realSingularChainCoefficient) σ.1
    rw [smallSimplexLift_map]
  calc
    _ = ((TopCat.toSSet.obj O).ιChainComplex
          (R := realSingularChainCoefficient) τ ≫
        (realSingularChainFunctor.map f).f n) ≫
          (subdivisionPrismDegree n).map X := by
      rw [hgen]
      rfl
    _ = (TopCat.toSSet.obj O).ιChainComplex
          (R := realSingularChainCoefficient) τ ≫
        ((realSingularChainFunctor.map f).f n ≫
          (subdivisionPrismDegree n).map X) :=
      Category.assoc _ _ _
    _ = (TopCat.toSSet.obj O).ιChainComplex
          (R := realSingularChainCoefficient) τ ≫
        ((subdivisionPrismDegree n).map O ≫
          (realSingularChainFunctor.map f).f (n + 1)) := by
      rw [(subdivisionPrismDegree n).map_natural f]
      rfl
    _ = ((TopCat.toSSet.obj O).ιChainComplex
          (R := realSingularChainCoefficient) τ ≫
        (subdivisionPrismDegree n).map O) ≫
          (realSingularChainFunctor.map f).f (n + 1) := by
      rw [Category.assoc]
    _ = _ := by
      dsimp only [f, O, τ]
      rw [← openSingularChainsCompatibility]
      simp only [Category.assoc]
      rfl

/--
%%handwave
name:
  Subdivision prism on cover-small chains in one degree
statement:
  In degree $n$, define the cover-small prism by including into ordinary
  chains, applying the universal subdivision prism, and projecting back onto
  cover-small chains.
-/
noncomputable def smallSubdivisionPrismDegree
    (X : TopCat.{v}) {ι : Type v} (U : ι → Opens X) (n : ℕ) :
    (smallRealSingularChains X U).X n ⟶
      (smallRealSingularChains X U).X (n + 1) :=
  (smallRealSingularChainsInclusion X U).f n ≫
    (subdivisionPrismDegree n).map X ≫
      smallRealSingularChainsRetract X U (n + 1)

/--
%%handwave
name:
  Compatibility of the small and ordinary subdivision prisms
statement:
  Including the cover-small prism of a chain gives its ordinary subdivision
  prism.
proof:
  Check the identity on generators.  The ordinary prism of a small generator
  factors through small chains, on which the explicit projection is a
  retraction.
-/
theorem smallSubdivisionPrismCompatibility
    (X : TopCat.{v}) {ι : Type v} (U : ι → Opens X) (n : ℕ) :
    smallSubdivisionPrismDegree X U n ≫
        (smallRealSingularChainsInclusion X U).f (n + 1) =
      (smallRealSingularChainsInclusion X U).f n ≫
        (subdivisionPrismDegree n).map X := by
  apply SSet.chainComplex_hom_ext
  intro σ
  change
    ((openCoverSmallSingularSet X U : SSet.{v}).ιChainComplex
        (R := realSingularChainCoefficient) σ ≫
      (smallRealSingularChainsInclusion X U).f n ≫
      (subdivisionPrismDegree n).map X ≫
      smallRealSingularChainsRetract X U (n + 1)) ≫
        (smallRealSingularChainsInclusion X U).f (n + 1) =
      (openCoverSmallSingularSet X U : SSet.{v}).ιChainComplex
        (R := realSingularChainCoefficient) σ ≫
      ((smallRealSingularChainsInclusion X U).f n ≫
        (subdivisionPrismDegree n).map X)
  simp only [← Category.assoc]
  dsimp only [smallRealSingularChainsInclusion]
  rw [SSet.ι_chainComplexMap_f]
  change
    (((TopCat.toSSet.obj X).ιChainComplex
        (R := realSingularChainCoefficient) σ.1 ≫
      (subdivisionPrismDegree n).map X) ≫
      smallRealSingularChainsRetract X U (n + 1)) ≫
        (smallRealSingularChainsInclusion X U).f (n + 1) =
      (TopCat.toSSet.obj X).ιChainComplex
        (R := realSingularChainCoefficient) σ.1 ≫
      (subdivisionPrismDegree n).map X
  rw [subdivisionPrismGenerator_factors_small X U n σ]
  let g :=
    (TopCat.toSSet.obj
        (TopCat.of (U (smallCoverIndex X U n σ)) :
          TopCat.{v})).ιChainComplex
        (R := realSingularChainCoefficient)
        (smallSimplexLift X U n σ) ≫
      (subdivisionPrismDegree n).map
        (TopCat.of (U (smallCoverIndex X U n σ)) : TopCat.{v}) ≫
      (SSet.chainComplexMap
        (openSingularChainsToSmall X U (smallCoverIndex X U n σ))
        realSingularChainCoefficient).f (n + 1)
  change
    ((g ≫ (smallRealSingularChainsInclusion X U).f (n + 1)) ≫
      smallRealSingularChainsRetract X U (n + 1)) ≫
        (smallRealSingularChainsInclusion X U).f (n + 1) =
      g ≫ (smallRealSingularChainsInclusion X U).f (n + 1)
  rw [Category.assoc g]
  rw [smallRealSingularChainsInclusion_retract]
  rw [Category.comp_id]

/--
%%handwave
name:
  Compatibility of identity minus subdivision on small chains
statement:
  Inclusion intertwines identity minus cover-small subdivision with identity
  minus ordinary barycentric subdivision.
proof:
  Expand both differences and use compatibility of small and ordinary
  subdivision.
-/
theorem smallSubdivisionDifferenceCompatibility
    (X : TopCat.{v}) {ι : Type v} (U : ι → Opens X) (n : ℕ) :
    (𝟙 (smallRealSingularChains X U) - smallBarycentricSubdivision X U).f n ≫
        (smallRealSingularChainsInclusion X U).f n =
      (smallRealSingularChainsInclusion X U).f n ≫
        (𝟙 (realSingularChains X) - barycentricSubdivision X).f n := by
  rw [HomologicalComplex.sub_f_apply, HomologicalComplex.sub_f_apply,
    HomologicalComplex.id_f, HomologicalComplex.id_f,
    Preadditive.sub_comp, Preadditive.comp_sub,
    Category.id_comp, Category.comp_id]
  change
    (smallRealSingularChainsInclusion X U).f n -
        smallBarycentricSubdivisionDegree X U n ≫
          (smallRealSingularChainsInclusion X U).f n =
      (smallRealSingularChainsInclusion X U).f n -
        (smallRealSingularChainsInclusion X U).f n ≫
          barycentricSubdivisionDegree X n
  rw [smallBarycentricSubdivisionCompatibility]

/--
%%handwave
name:
  Small subdivision-prism identity in degree zero
statement:
  On cover-small zero-chains, $\mathrm{id}-\mathrm{Sd}$ equals the prism
  followed by the boundary from degree one.
proof:
  Postcompose with the monic inclusion, use the ordinary degree-zero prism
  identity, and commute inclusion past the prism and boundary.
-/
theorem smallSubdivisionPrismCommZero
    (X : TopCat.{v}) {ι : Type v} (U : ι → Opens X) :
    (𝟙 (smallRealSingularChains X U) - smallBarycentricSubdivision X U).f 0 =
      smallSubdivisionPrismDegree X U 0 ≫
        (smallRealSingularChains X U).d 1 0 := by
  apply (cancel_mono
    ((smallRealSingularChainsInclusion X U).f 0)).1
  calc
    (𝟙 (smallRealSingularChains X U) - smallBarycentricSubdivision X U).f 0 ≫
        (smallRealSingularChainsInclusion X U).f 0 =
      (smallRealSingularChainsInclusion X U).f 0 ≫
        (𝟙 (realSingularChains X) -
          barycentricSubdivision X).f 0 :=
      smallSubdivisionDifferenceCompatibility X U 0
    _ = (smallRealSingularChainsInclusion X U).f 0 ≫
        ((subdivisionPrismDegree 0).map X ≫
          (realSingularChains X).d 1 0) := by
      rw [subdivisionPrismDegree_comm_zero]
    _ = ((smallRealSingularChainsInclusion X U).f 0 ≫
          (subdivisionPrismDegree 0).map X) ≫
        (realSingularChains X).d 1 0 := by
      rw [Category.assoc]
    _ = (smallSubdivisionPrismDegree X U 0 ≫
          (smallRealSingularChainsInclusion X U).f 1) ≫
        (realSingularChains X).d 1 0 := by
      rw [smallSubdivisionPrismCompatibility]
    _ = smallSubdivisionPrismDegree X U 0 ≫
        ((smallRealSingularChainsInclusion X U).f 1 ≫
          (realSingularChains X).d 1 0) :=
      Category.assoc _ _ _
    _ = smallSubdivisionPrismDegree X U 0 ≫
        ((smallRealSingularChains X U).d 1 0 ≫
          (smallRealSingularChainsInclusion X U).f 0) := by
      rw [(smallRealSingularChainsInclusion X U).comm]
    _ = (smallSubdivisionPrismDegree X U 0 ≫
          (smallRealSingularChains X U).d 1 0) ≫
        (smallRealSingularChainsInclusion X U).f 0 := by
      rw [Category.assoc]

/--
%%handwave
name:
  Small subdivision-prism identity in positive degrees
statement:
  On cover-small chains in degree $n+1$,
  $\mathrm{id}-\mathrm{Sd}=\partial T+T\partial$.
proof:
  Postcompose with the monic inclusion and transport the ordinary subdivision
  prism identity through compatibility of inclusion with boundaries and
  prism operators.
-/
theorem smallSubdivisionPrismCommSucc
    (X : TopCat.{v}) {ι : Type v} (U : ι → Opens X) (n : ℕ) :
    (𝟙 (smallRealSingularChains X U) - smallBarycentricSubdivision X U).f (n + 1) =
      (smallRealSingularChains X U).d (n + 1) n ≫
          smallSubdivisionPrismDegree X U n +
        smallSubdivisionPrismDegree X U (n + 1) ≫
          (smallRealSingularChains X U).d (n + 2) (n + 1) := by
  apply (cancel_mono
    ((smallRealSingularChainsInclusion X U).f (n + 1))).1
  calc
    (𝟙 (smallRealSingularChains X U) -
          smallBarycentricSubdivision X U).f (n + 1) ≫
        (smallRealSingularChainsInclusion X U).f (n + 1) =
      (smallRealSingularChainsInclusion X U).f (n + 1) ≫
        (𝟙 (realSingularChains X) -
          barycentricSubdivision X).f (n + 1) :=
      smallSubdivisionDifferenceCompatibility X U (n + 1)
    _ = (smallRealSingularChainsInclusion X U).f (n + 1) ≫
        ((realSingularChains X).d (n + 1) n ≫
            (subdivisionPrismDegree n).map X +
          (subdivisionPrismDegree (n + 1)).map X ≫
            (realSingularChains X).d (n + 2) (n + 1)) := by
      rw [subdivisionPrismDegree_comm_succ]
    _ = ((smallRealSingularChainsInclusion X U).f (n + 1) ≫
            (realSingularChains X).d (n + 1) n) ≫
          (subdivisionPrismDegree n).map X +
        ((smallRealSingularChainsInclusion X U).f (n + 1) ≫
            (subdivisionPrismDegree (n + 1)).map X) ≫
          (realSingularChains X).d (n + 2) (n + 1) := by
      simp only [Preadditive.comp_add, Category.assoc]
    _ = (((smallRealSingularChains X U).d (n + 1) n ≫
            (smallRealSingularChainsInclusion X U).f n) ≫
          (subdivisionPrismDegree n).map X) +
        ((smallSubdivisionPrismDegree X U (n + 1) ≫
            (smallRealSingularChainsInclusion X U).f (n + 2)) ≫
          (realSingularChains X).d (n + 2) (n + 1)) := by
      rw [← (smallRealSingularChainsInclusion X U).comm,
        ← smallSubdivisionPrismCompatibility]
    _ = ((smallRealSingularChains X U).d (n + 1) n ≫
          ((smallRealSingularChainsInclusion X U).f n ≫
            (subdivisionPrismDegree n).map X)) +
        (smallSubdivisionPrismDegree X U (n + 1) ≫
          ((smallRealSingularChainsInclusion X U).f (n + 2) ≫
            (realSingularChains X).d (n + 2) (n + 1))) := by
      simp only [Category.assoc]
    _ = ((smallRealSingularChains X U).d (n + 1) n ≫
          (smallSubdivisionPrismDegree X U n ≫
            (smallRealSingularChainsInclusion X U).f (n + 1))) +
        (smallSubdivisionPrismDegree X U (n + 1) ≫
          ((smallRealSingularChains X U).d (n + 2) (n + 1) ≫
            (smallRealSingularChainsInclusion X U).f (n + 1))) := by
      rw [← smallSubdivisionPrismCompatibility,
        ← (smallRealSingularChainsInclusion X U).comm]
    _ = (((smallRealSingularChains X U).d (n + 1) n ≫
            smallSubdivisionPrismDegree X U n) ≫
          (smallRealSingularChainsInclusion X U).f (n + 1)) +
        ((smallSubdivisionPrismDegree X U (n + 1) ≫
            (smallRealSingularChains X U).d (n + 2) (n + 1)) ≫
          (smallRealSingularChainsInclusion X U).f (n + 1)) := by
      simp only [Category.assoc]
    _ = ((smallRealSingularChains X U).d (n + 1) n ≫
            smallSubdivisionPrismDegree X U n +
          smallSubdivisionPrismDegree X U (n + 1) ≫
            (smallRealSingularChains X U).d (n + 2) (n + 1)) ≫
        (smallRealSingularChainsInclusion X U).f (n + 1) := by
      rw [Preadditive.add_comp]

/--
%%handwave
name:
  Degree family for the cover-small subdivision homotopy
statement:
  Define the homotopy component from degree $i$ to degree $j$ to be the small
  prism operator when $j=i+1$, and zero otherwise.
-/
noncomputable def smallSubdivisionPrismHomotopyFamily
    (X : TopCat.{v}) {ι : Type v} (U : ι → Opens X)
    (i j : ℕ) :
    (smallRealSingularChains X U).X i ⟶
      (smallRealSingularChains X U).X j :=
  if h : i + 1 = j then by
    subst j
    exact smallSubdivisionPrismDegree X U i
  else 0

/--
%%handwave
name:
  Successor component of the cover-small homotopy family
statement:
  The component from degree $i$ to degree $i+1$ is the degree-$i$ small
  subdivision prism.
proof:
  Select the successor branch in the definition of the homotopy family.
-/
@[simp]
theorem smallSubdivisionPrismHomotopyFamily_succ
    (X : TopCat.{v}) {ι : Type v} (U : ι → Opens X)
    (i : ℕ) :
    smallSubdivisionPrismHomotopyFamily X U i (i + 1) =
      smallSubdivisionPrismDegree X U i := by
  simp [smallSubdivisionPrismHomotopyFamily]

/--
%%handwave
name:
  Vanishing of nonadjacent small homotopy components
statement:
  A component of the cover-small homotopy family is zero unless its target
  degree is the successor of its source degree.
proof:
  Split on the successor equality; the nonzero branch contradicts the
  assumed failure of the chain-complex adjacency relation.
-/
theorem smallSubdivisionPrismHomotopyFamily_zero
    (X : TopCat.{v}) {ι : Type v} (U : ι → Opens X)
    (i j : ℕ) (h : ¬(ComplexShape.down ℕ).Rel j i) :
    smallSubdivisionPrismHomotopyFamily X U i j = 0 := by
  rw [smallSubdivisionPrismHomotopyFamily]
  split_ifs with hij
  · subst j
    simp at h
  · rfl

/--
%%handwave
name:
  Small subdivision difference is null-homotopic
statement:
  On cover-small singular chains, $\mathrm{id}-\mathrm{Sd}$ is chain
  homotopic to zero.
-/
noncomputable def smallSubdivisionPrismSubZeroHomotopy
    (X : TopCat.{v}) {ι : Type v} (U : ι → Opens X) :
    Homotopy
      (𝟙 (smallRealSingularChains X U) - smallBarycentricSubdivision X U) 0 where
  hom := smallSubdivisionPrismHomotopyFamily X U
  zero := smallSubdivisionPrismHomotopyFamily_zero X U
  comm i := by
    rw [HomologicalComplex.zero_f_apply, add_zero]
    cases i with
    | zero =>
        rw [Homotopy.dNext_zero_chainComplex, zero_add,
          Homotopy.prevD_chainComplex,
          smallSubdivisionPrismHomotopyFamily_succ]
        exact smallSubdivisionPrismCommZero X U
    | succ n =>
        rw [Homotopy.dNext_succ_chainComplex,
          Homotopy.prevD_chainComplex,
          smallSubdivisionPrismHomotopyFamily_succ,
          smallSubdivisionPrismHomotopyFamily_succ]
        exact smallSubdivisionPrismCommSucc X U n

/--
%%handwave
name:
  Cover-small subdivision is homotopic to the identity
statement:
  Barycentric subdivision of cover-small singular chains is chain homotopic
  to the identity.
-/
noncomputable def smallSubdivisionPrismHomotopy
    (X : TopCat.{v}) {ι : Type v} (U : ι → Opens X) :
    Homotopy (𝟙 (smallRealSingularChains X U))
      (smallBarycentricSubdivision X U) :=
  Homotopy.equivSubZero.symm (smallSubdivisionPrismSubZeroHomotopy X U)

end
end JJMath.Cohomology

namespace stdSimplex

noncomputable section

/--
%%handwave
name:
  Barycentric mesh-contraction factor
statement:
  In dimension $n$, define the barycentric mesh-contraction factor to be
  $q_n=n/(n+1)$.
-/
noncomputable def barycentricContractionFactor (n : ℕ) : ℝ :=
  (n : ℝ) / (n + 1 : ℕ)

/--
%%handwave
name:
  Common vertex weight in the barycentric contraction
statement:
  In dimension $n$, define the common weight $a_n=1/(n+1)$.
-/
noncomputable def barycentricCommonWeight (n : ℕ) : ℝ :=
  ((n + 1 : ℕ) : ℝ)⁻¹

/--
%%handwave
name:
  Barycentric contraction weights sum to one
statement:
  For every $n$, the weights $a_n=1/(n+1)$ and $q_n=n/(n+1)$ satisfy
  $a_n+q_n=1$.
proof:
  Expand the definitions and simplify the elementary field identity.
-/
theorem barycentricWeights_add (n : ℕ) :
    barycentricCommonWeight n +
      barycentricContractionFactor n = 1 := by
  dsimp [barycentricCommonWeight,
    barycentricContractionFactor]
  field_simp
  norm_num [Nat.cast_add]
  ring

/--
%%handwave
name:
  Remainder after removing the common barycentric vertex
statement:
  For $n>0$, remove weight $1/(n+1)$ at the first permutation vertex from an
  initial barycenter and rescale by $n/(n+1)$; the resulting coordinates
  define a point of $\Delta^n$.
-/
noncomputable def permutationInitialBarycenterRemainder
    {n : ℕ} (hn : 0 < n)
    (p : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 1)) :
    stdSimplex ℝ (Fin (n + 1)) := by
  classical
  let a := barycentricCommonWeight n
  let q := barycentricContractionFactor n
  refine ⟨fun j =>
    (permutationInitialBarycenter p k j -
      if j = p 0 then a else 0) / q, ?_, ?_⟩
  · intro j
    apply div_nonneg
    · split_ifs with hj
      · subst j
        change
          0 ≤
            (if p.symm (p 0) ≤ k then
              (((k.val + 1 : ℕ) : ℝ)⁻¹) else 0) - a
        rw [if_pos (by simp)]
        dsimp only [a, barycentricCommonWeight]
        apply sub_nonneg.mpr
        apply (inv_le_inv₀ (by positivity) (by positivity)).2
        exact_mod_cast (Nat.succ_le_iff.mpr k.isLt)
      · apply sub_nonneg.mpr
        simpa only [hj, if_false] using
          stdSimplex.zero_le (permutationInitialBarycenter p k) j
    · dsimp only [q, barycentricContractionFactor]
      positivity
  · simp only [div_eq_mul_inv]
    rw [← Finset.sum_mul]
    rw [Finset.sum_sub_distrib]
    rw [stdSimplex.sum_eq_one]
    have hsum :
        (∑ j : Fin (n + 1),
          if j = p 0 then barycentricCommonWeight n else 0) =
          barycentricCommonWeight n := by
      simp
    rw [hsum]
    have hq :
        1 - barycentricCommonWeight n =
          q := by
      dsimp only [q]
      linarith [barycentricWeights_add n]
    rw [hq]
    exact mul_inv_cancel₀ (by
      dsimp only [q, barycentricContractionFactor]
      positivity)

/--
%%handwave
name:
  Decomposition of an initial permutation barycenter
statement:
  If $n>0$, an initial permutation barycenter $b_{p,k}$ decomposes as
  $b_{p,k}=a_n e_{p(0)}+q_n r_{p,k}$, where $r_{p,k}\in\Delta^n$.
proof:
  Compare every coordinate and simplify according to whether the coordinate
  is $p(0)$.
-/
theorem permutationInitialBarycenter_decompose
    {n : ℕ} (hn : 0 < n)
    (p : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 1)) :
    (permutationInitialBarycenter p k :
        Fin (n + 1) → ℝ) =
      barycentricCommonWeight n •
          (vertex (p 0) : Fin (n + 1) → ℝ) +
        barycentricContractionFactor n •
          (permutationInitialBarycenterRemainder hn p k :
            Fin (n + 1) → ℝ) := by
  funext j
  change
    permutationInitialBarycenter p k j =
      barycentricCommonWeight n *
          (vertex (p 0) : stdSimplex ℝ (Fin (n + 1))).1 j +
        barycentricContractionFactor n *
          (permutationInitialBarycenterRemainder hn p k).1 j
  dsimp only [vertex, permutationInitialBarycenterRemainder]
  simp only [Pi.single_apply]
  split_ifs <;>
    dsimp [barycentricContractionFactor,
      barycentricCommonWeight] <;>
    field_simp <;> ring

/--
%%handwave
name:
  Affine simplex map as a weighted sum
statement:
  For vertices $(v_i)$ and $x\in\Delta^I$, the underlying vector of the
  associated affine map is $\sum_i x_i v_i$.
proof:
  Expand the affine-map definition and compare coordinates.
-/
theorem affineMap_coe
    {I J : Type*} [Fintype I] [Fintype J]
    (v : I → stdSimplex ℝ J) (x : stdSimplex ℝ I) :
    (affineMap v x : J → ℝ) =
      ∑ i, x i • (v i : J → ℝ) := by
  funext j
  dsimp only [affineMap]
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  change (∑ i, x i * v i j) =
    ∑ i, x i * v i j
  rfl

/--
%%handwave
name:
  An affine simplex map lies in the convex hull of its vertices
statement:
  For every $x\in\Delta^I$, the point $A_v(x)$ lies in the convex hull of
  $\{v_i\mid i\in I\}$.
proof:
  Express $A_v(x)$ as a weighted sum whose coefficients are nonnegative and
  sum to one.
-/
theorem affineMap_mem_convexHull
    {I J : Type*} [Fintype I] [Fintype J]
    (v : I → stdSimplex ℝ J) (x : stdSimplex ℝ I) :
    (affineMap v x : J → ℝ) ∈
      convexHull ℝ (Set.range fun i => (v i : J → ℝ)) := by
  rw [affineMap_coe]
  rw [← Finset.univ.centerMass_eq_of_sum_1 _
    (by simpa using stdSimplex.sum_eq_one x)]
  exact Finset.univ.centerMass_mem_convexHull
    (fun i _ => stdSimplex.zero_le x i)
    (by simpa using stdSimplex.sum_eq_one x)
    (fun i _ => Set.mem_range_self i)

/--
%%handwave
name:
  The affine map determined by standard vertices is the identity
statement:
  The affine self-map of $\Delta^I$ determined by its standard vertices fixes
  every point.
proof:
  Compare coordinates and collapse the sum using the standard-vertex
  Kronecker delta.
-/
theorem affineMap_vertices
    {I : Type*} [Fintype I] [DecidableEq I]
    (x : stdSimplex ℝ I) :
    affineMap (vertex : I → stdSimplex ℝ I) x = x := by
  apply Subtype.ext
  funext j
  change
    (∑ i, x i *
      (Pi.single i (1 : ℝ) : I → ℝ) j) = x j
  simp [Pi.single_apply]

/--
%%handwave
name:
  Composition law for affine simplex maps
statement:
  If $v_i\in\Delta^J$ and $w_j\in\Delta^K$, then
  $A_w(A_v(x))=A_{i\mapsto A_w(v_i)}(x)$.
proof:
  Compare coordinates, expand both finite sums, and interchange their order.
-/
theorem affineMap_comp_affineMap
    {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    (v : J → stdSimplex ℝ K)
    (w : I → stdSimplex ℝ J)
    (x : stdSimplex ℝ I) :
    affineMap v (affineMap w x) =
      affineMap (fun i => affineMap v (w i)) x := by
  classical
  apply Subtype.ext
  funext k
  change
    (∑ j, (∑ i, x i * w i j) * v j k) =
      ∑ i, x i * ∑ j, w i j * v j k
  calc
    _ = ∑ j, ∑ i, (x i * w i j) * v j k := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul]
    _ = ∑ i, ∑ j, (x i * w i j) * v j k :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_assoc]

/--
%%handwave
name:
  Affine decomposition of barycentric child vertices
statement:
  For $n>0$, the affine image of every initial permutation barycenter is the
  convex combination, with weights $1/(n+1)$ and $n/(n+1)$, of the first
  image vertex and the image of the remainder point.
proof:
  Apply the affine map to the barycenter decomposition and distribute the
  finite weighted sum.
-/
theorem affineMap_permutationInitialBarycenter_decompose
    {n : ℕ} (hn : 0 < n)
    {J : Type*} [Fintype J]
    (v : Fin (n + 1) → stdSimplex ℝ J)
    (p : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 1)) :
    (affineMap v (permutationInitialBarycenter p k) : J → ℝ) =
      barycentricCommonWeight n • (v (p 0) : J → ℝ) +
        barycentricContractionFactor n •
          (affineMap v
            (permutationInitialBarycenterRemainder hn p k) :
              J → ℝ) := by
  classical
  rw [affineMap_coe, affineMap_coe]
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.add_apply]
  simp_rw [congrFun
    (permutationInitialBarycenter_decompose hn p k)]
  simp only [Pi.add_apply, Pi.smul_apply]
  simp_rw [smul_eq_mul, add_mul, mul_assoc]
  rw [Finset.sum_add_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  have hv :
      (∑ x : Fin (n + 1), (vertex (p 0)) x * v x j) =
        v (p 0) j := by
    change
      (∑ x : Fin (n + 1),
        (Pi.single (p 0) (1 : ℝ) :
          Fin (n + 1) → ℝ) x * v x j) =
        v (p 0) j
    simp [Pi.single_apply]
  rw [hv]

/--
%%handwave
name:
  Distance contraction between vertices of a barycentric child
statement:
  For $n>0$, any two vertices of one barycentric child under an affine map
  are at distance at most $n/(n+1)$ times the diameter of the original image
  vertices.
proof:
  Cancel the common affine term in their decompositions and bound the two
  remainder points by the diameter of the original convex hull.
-/
theorem affineMap_barycentric_vertices_dist_le
    {n : ℕ} (hn : 0 < n)
    {J : Type*} [Fintype J]
    (v : Fin (n + 1) → stdSimplex ℝ J)
    (p : Equiv.Perm (Fin (n + 1)))
    (k l : Fin (n + 1)) :
    dist
        (affineMap v (permutationInitialBarycenter p k))
        (affineMap v (permutationInitialBarycenter p l)) ≤
      barycentricContractionFactor n *
        Metric.diam
          (Set.range fun i => (v i : J → ℝ)) := by
  change
    dist
        (affineMap v (permutationInitialBarycenter p k) : J → ℝ)
        (affineMap v (permutationInitialBarycenter p l) : J → ℝ) ≤ _
  rw [affineMap_permutationInitialBarycenter_decompose hn,
    affineMap_permutationInitialBarycenter_decompose hn]
  rw [dist_add_left]
  rw [dist_smul₀]
  have hq :
      ‖barycentricContractionFactor n‖ =
        barycentricContractionFactor n := by
    rw [Real.norm_eq_abs, abs_of_nonneg]
    dsimp [barycentricContractionFactor]
    positivity
  rw [hq]
  apply mul_le_mul_of_nonneg_left
  · rw [← convexHull_diam]
    apply Metric.dist_le_diam_of_mem
    · rw [isBounded_convexHull]
      exact Set.finite_range _ |>.isBounded
    · exact affineMap_mem_convexHull _ _
    · exact affineMap_mem_convexHull _ _
  · dsimp [barycentricContractionFactor]
    positivity

/--
%%handwave
name:
  Vertices after one barycentric refinement
statement:
  Given vertices $v_i$ and a permutation $p$, define the refined vertices as
  the affine images of the initial barycenters indexed by $p$.
-/
noncomputable def barycentricRefinedVertices
    {n : ℕ}
    (v : Fin (n + 1) → stdSimplex ℝ (Fin (n + 1)))
    (p : Equiv.Perm (Fin (n + 1))) :
    Fin (n + 1) → stdSimplex ℝ (Fin (n + 1)) :=
  fun k => affineMap v (permutationInitialBarycenter p k)

/--
%%handwave
name:
  Diameter contraction under one barycentric refinement
statement:
  For $n>0$, the diameter of the vertices in any barycentric child is at most
  $n/(n+1)$ times the diameter of the parent vertices.
proof:
  Apply the pairwise child-vertex distance estimate and the definition of
  diameter.
-/
theorem barycentricRefinedVertices_diam_le
    {n : ℕ} (hn : 0 < n)
    (v : Fin (n + 1) → stdSimplex ℝ (Fin (n + 1)))
    (p : Equiv.Perm (Fin (n + 1))) :
    Metric.diam
        (Set.range fun i =>
          (barycentricRefinedVertices v p i :
            Fin (n + 1) → ℝ)) ≤
      barycentricContractionFactor n *
        Metric.diam
          (Set.range fun i => (v i : Fin (n + 1) → ℝ)) := by
  apply Metric.diam_le_of_forall_dist_le_of_nonempty
    (Set.range_nonempty _)
  rintro x ⟨k, rfl⟩ y ⟨l, rfl⟩
  exact affineMap_barycentric_vertices_dist_le hn v p k l

/--
%%handwave
name:
  Nonnegativity of the barycentric contraction factor
statement:
  For every $n$, $0\le n/(n+1)$.
proof:
  Both numerator and denominator are nonnegative.
-/
theorem barycentricContractionFactor_nonneg (n : ℕ) :
    0 ≤ barycentricContractionFactor n := by
  dsimp [barycentricContractionFactor]
  positivity

/--
%%handwave
name:
  Strict contraction of barycentric subdivision
statement:
  If $n>0$, then $n/(n+1)<1$.
proof:
  The denominator is positive and the numerator is strictly smaller than it.
-/
theorem barycentricContractionFactor_lt_one
    {n : ℕ} (hn : 0 < n) :
    barycentricContractionFactor n < 1 := by
  dsimp [barycentricContractionFactor]
  rw [div_lt_one]
  · exact_mod_cast Nat.lt_succ_self n
  · positivity

/--
%%handwave
name:
  Vertices after iterated barycentric refinement
statement:
  Starting from vertices $v_i$, recursively refine them along a list of
  permutation-indexed barycentric children.
-/
noncomputable def iteratedBarycentricVertices
    {n : ℕ} :
    List (Equiv.Perm (Fin (n + 1))) →
      Fin (n + 1) → stdSimplex ℝ (Fin (n + 1)) :=
  fun ps =>
    List.rec vertex
      (fun p _ v => barycentricRefinedVertices v p) ps

/--
%%handwave
name:
  Geometric decay of iterated barycentric vertex diameter
statement:
  In positive dimension, after $N$ barycentric refinements the vertex
  diameter is at most $(n/(n+1))^N$ times the original vertex diameter.
proof:
  Induct on the refinements and apply the one-step contraction at each
  successor.
-/
theorem iteratedBarycentricVertices_diam_le
    {n : ℕ} (hn : 0 < n)
    (ps : List (Equiv.Perm (Fin (n + 1)))) :
    Metric.diam
        (Set.range fun i =>
          (iteratedBarycentricVertices ps i :
            Fin (n + 1) → ℝ)) ≤
      barycentricContractionFactor n ^ ps.length *
        Metric.diam
          (Set.range fun i =>
            (vertex i : stdSimplex ℝ (Fin (n + 1))).1) := by
  induction ps with
  | nil =>
      simp [iteratedBarycentricVertices]
  | cons p ps ih =>
      calc
        _ ≤ barycentricContractionFactor n *
            Metric.diam
              (Set.range fun i =>
                (iteratedBarycentricVertices ps i :
                  Fin (n + 1) → ℝ)) :=
          barycentricRefinedVertices_diam_le hn _ _
        _ ≤ barycentricContractionFactor n *
            (barycentricContractionFactor n ^ ps.length *
              Metric.diam
                (Set.range fun i =>
                  (vertex i :
                    stdSimplex ℝ (Fin (n + 1))).1)) := by
          exact mul_le_mul_of_nonneg_left ih
            (barycentricContractionFactor_nonneg n)
        _ = barycentricContractionFactor n ^ (p :: ps).length *
            Metric.diam
              (Set.range fun i =>
                (vertex i :
                  stdSimplex ℝ (Fin (n + 1))).1) := by
          simp only [List.length_cons, pow_succ]
          ring

/--
%%handwave
name:
  Diameter of an affine simplex image is controlled by its vertices
statement:
  If the finite vertex set $(v_i)$ is bounded, then the diameter of the range
  of $A_v$ is at most the diameter of $\{v_i\}$.
proof:
  Both affine images lie in the convex hull of the vertices, which has the
  same diameter as the bounded vertex set.
-/
theorem affineMap_range_diam_le_vertices
    {I J : Type*} [Fintype I] [Fintype J]
    (v : I → stdSimplex ℝ J) :
    Metric.diam
        (Set.range fun x : stdSimplex ℝ I =>
          (affineMap v x : J → ℝ)) ≤
      Metric.diam (Set.range fun i => (v i : J → ℝ)) := by
  calc
    _ ≤ Metric.diam
        (convexHull ℝ (Set.range fun i => (v i : J → ℝ))) := by
      apply Metric.diam_mono
      · rintro _ ⟨x, rfl⟩
        exact affineMap_mem_convexHull v x
      · rw [isBounded_convexHull]
        exact Set.finite_range _ |>.isBounded
    _ = _ := convexHull_diam _

/--
%%handwave
name:
  Mesh estimate for an iterated barycentric child
statement:
  In positive dimension, the diameter of the affine image of an $N$-fold
  barycentric child is at most $(n/(n+1))^N$ times the initial vertex
  diameter.
proof:
  Control the affine image by its refined vertices and apply geometric decay
  of their diameter.
-/
theorem iteratedBarycentricAffineMap_range_diam_le
    {n : ℕ} (hn : 0 < n)
    (ps : List (Equiv.Perm (Fin (n + 1)))) :
    Metric.diam
        (Set.range fun x : stdSimplex ℝ (Fin (n + 1)) =>
          (affineMap (iteratedBarycentricVertices ps) x :
            Fin (n + 1) → ℝ)) ≤
      barycentricContractionFactor n ^ ps.length *
        Metric.diam
          (Set.range fun i =>
            (vertex i : stdSimplex ℝ (Fin (n + 1))).1) :=
  (affineMap_range_diam_le_vertices _).trans
    (iteratedBarycentricVertices_diam_le hn ps)

/--
%%handwave
name:
  A geometric power eventually beats a fixed scale
statement:
  If $0\le q<1$, $\varepsilon>0$, and $D\ge0$, then some $N$ satisfies
  $q^N D<\varepsilon$.
proof:
  Handle $D=0$ directly; otherwise use convergence of $q^N$ to zero and
  multiply the resulting bound by $D$.
-/
theorem exists_pow_mul_lt
    {q D δ : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1)
    (hD : 0 ≤ D) (hδ : 0 < δ) :
    ∃ N : ℕ, q ^ N * D < δ := by
  obtain ⟨N, hN⟩ :=
    exists_pow_lt_of_lt_one
      (div_pos hδ (by positivity : 0 < D + 1)) hq₁
  refine ⟨N, ?_⟩
  calc
    q ^ N * D ≤ q ^ N * (D + 1) := by
      exact mul_le_mul_of_nonneg_left
        (by linarith) (pow_nonneg hq₀ _)
    _ < (δ / (D + 1)) * (D + 1) := by
      exact mul_lt_mul_of_pos_right hN (by positivity)
    _ = δ := by
      field_simp

/--
%%handwave
name:
  Iterated barycentric affine images eventually have small diameter
statement:
  For $n>0$, fixed initial vertices, and $\varepsilon>0$, sufficiently many
  refinements make every barycentric child image have diameter less than
  $\varepsilon$.
proof:
  Choose the number of refinements by geometric decay and combine it with the
  iterated mesh estimate.
-/
theorem iteratedBarycentricAffineMap_eventually_small
    {n : ℕ} (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ ps : List (Equiv.Perm (Fin (n + 1))),
      ps.length = N →
      Metric.diam
          (Set.range fun x : stdSimplex ℝ (Fin (n + 1)) =>
            (affineMap (iteratedBarycentricVertices ps) x :
              Fin (n + 1) → ℝ)) < δ := by
  obtain ⟨N, hN⟩ := exists_pow_mul_lt
    (barycentricContractionFactor_nonneg n)
    (barycentricContractionFactor_lt_one hn)
    (show
      0 ≤ Metric.diam
        (Set.range fun i =>
          (vertex i : stdSimplex ℝ (Fin (n + 1))).1) from
      Metric.diam_nonneg)
    hδ
  refine ⟨N, fun ps hps => ?_⟩
  exact (iteratedBarycentricAffineMap_range_diam_le hn ps).trans_lt
    (by simpa [hps] using hN)

/--
%%handwave
name:
  Iterated barycentric subdivision is subordinate to an open cover
statement:
  Let $f:\Delta^n\to X$ be continuous and let $(U_i)$ cover $X$.  There is
  $N$ such that the image under $f$ of every $N$-fold barycentric child lies
  in one member of the cover.
proof:
  Pull the cover back to the compact standard simplex and use a Lebesgue
  number.  Apply the mesh estimate in positive dimension; in dimension zero
  the unique simplex is already small.
-/
theorem iteratedBarycentricAffineMaps_subordinate
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} (U : ι → Opens X) (hU : IsOpenCover U)
    {n : ℕ}
    (σ : C(stdSimplex ℝ (Fin (n + 1)), X)) :
    ∃ N : ℕ, ∀ ps : List (Equiv.Perm (Fin (n + 1))),
      ps.length = N →
      ∃ i : ι,
        Set.range (fun x =>
          σ (affineMap
            (iteratedBarycentricVertices ps) x)) ⊆
          (U i : Set X) := by
  by_cases hn : n = 0
  · subst n
    refine ⟨0, fun ps hps => ?_⟩
    have hps0 : ps = [] := List.length_eq_zero_iff.mp hps
    subst ps
    obtain ⟨i, hi⟩ := hU.exists_mem (σ (vertex 0))
    refine ⟨i, ?_⟩
    rintro _ ⟨x, rfl⟩
    change σ (affineMap vertex x) ∈ U i
    rw [affineMap_vertices]
    rw [Subsingleton.elim x (vertex 0)]
    exact hi
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    obtain ⟨δ, hδ, hball⟩ :=
      lebesgue_number_lemma_of_metric
        (s := Set.univ)
        (c := fun i => σ ⁻¹' (U i : Set X))
        isCompact_univ
        (fun i => (U i).isOpen.preimage σ.continuous)
        (by
          intro x _
          obtain ⟨i, hi⟩ := hU.exists_mem (σ x)
          exact Set.mem_iUnion.2 ⟨i, hi⟩)
    obtain ⟨N, hN⟩ :=
      iteratedBarycentricAffineMap_eventually_small hnpos hδ
    refine ⟨N, fun ps hps => ?_⟩
    let v := iteratedBarycentricVertices ps
    let c : stdSimplex ℝ (Fin (n + 1)) :=
      affineMap v (vertex 0)
    obtain ⟨i, hi⟩ := hball c (Set.mem_univ c)
    refine ⟨i, ?_⟩
    rintro _ ⟨x, rfl⟩
    apply hi
    rw [Metric.mem_ball]
    have hb :
        Bornology.IsBounded
          (Set.range fun y : stdSimplex ℝ (Fin (n + 1)) =>
            (affineMap v y : Fin (n + 1) → ℝ)) := by
      rw [← Set.image_univ]
      exact
        (isCompact_univ.image
          (continuous_subtype_val.comp
            (continuous_affineMap v))).isBounded
    exact
      (Metric.dist_le_diam_of_mem hb
        (Set.mem_range_self x)
        (Set.mem_range_self (vertex 0))).trans_lt
          (hN ps hps)

end

end stdSimplex

namespace JJMath.Cohomology

noncomputable section

universe w

/--
%%handwave
name:
  Singular simplex in an iterated barycentric child
statement:
  Starting from a singular $n$-simplex, recursively precompose with the
  barycentric child maps indexed by a list of permutations.
-/
noncomputable def iteratedBarycentricSingularSimplex
    (X : TopCat.{w}) (n : ℕ)
    (σ : TopCat.toSSet.obj X _⦋n⦌) :
    List (Equiv.Perm (Fin (n + 1))) →
      TopCat.toSSet.obj X _⦋n⦌ :=
  fun ps =>
    List.rec σ
      (fun p _ τ =>
        barycentricSubdivisionSingularSimplex X n τ p) ps

/--
%%handwave
name:
  Continuous map underlying an iterated singular child
statement:
  The continuous map underlying the singular simplex indexed by a list of
  barycentric refinements is the original simplex composed with the affine
  map determined by the corresponding iterated refined vertices.
proof:
  Induct on the list and use the composition law for affine simplex maps.
-/
theorem iteratedBarycentricSingularSimplex_toContinuousMap
    (X : TopCat.{w}) (n : ℕ)
    (σ : TopCat.toSSet.obj X _⦋n⦌)
    (ps : List (Equiv.Perm (Fin (n + 1)))) :
    TopCat.toSSetObjEquiv X _
        (iteratedBarycentricSingularSimplex X n σ ps) =
      (TopCat.toSSetObjEquiv X _ σ).comp
        ⟨stdSimplex.affineMap
          (stdSimplex.iteratedBarycentricVertices ps),
          stdSimplex.continuous_affineMap _⟩ := by
  induction ps with
  | nil =>
      apply ContinuousMap.ext
      intro x
      change
        TopCat.toSSetObjEquiv X _ σ x =
          TopCat.toSSetObjEquiv X _ σ
            (stdSimplex.affineMap stdSimplex.vertex x)
      rw [stdSimplex.affineMap_vertices]
  | cons p ps ih =>
      apply ContinuousMap.ext
      intro x
      change
        TopCat.toSSetObjEquiv X _
            (iteratedBarycentricSingularSimplex X n σ ps)
            (stdSimplex.barycentricSubdivisionMap p x) =
          TopCat.toSSetObjEquiv X _ σ
            (stdSimplex.affineMap
              (stdSimplex.barycentricRefinedVertices
                (stdSimplex.iteratedBarycentricVertices ps) p) x)
      rw [ih]
      change
        TopCat.toSSetObjEquiv X _ σ
            (stdSimplex.affineMap
              (stdSimplex.iteratedBarycentricVertices ps)
              (stdSimplex.affineMap
                (stdSimplex.permutationInitialBarycenter p) x)) =
          _
      rw [stdSimplex.affineMap_comp_affineMap]
      rfl

/--
%%handwave
name:
  Appending one barycentric refinement
statement:
  First taking the child indexed by $p$ and then following a refinement list
  gives the same singular simplex as appending $p$ to that list.
proof:
  Induct on the refinement list.
-/
theorem iteratedBarycentricSingularSimplex_append_singleton
    (X : TopCat.{w}) (n : ℕ)
    (σ : TopCat.toSSet.obj X _⦋n⦌)
    (p : Equiv.Perm (Fin (n + 1)))
    (ps : List (Equiv.Perm (Fin (n + 1)))) :
    iteratedBarycentricSingularSimplex X n
        (barycentricSubdivisionSingularSimplex X n σ p) ps =
      iteratedBarycentricSingularSimplex X n σ
        (ps ++ [p]) := by
  induction ps with
  | nil => rfl
  | cons q ps ih =>
      change
        barycentricSubdivisionSingularSimplex X n
            (iteratedBarycentricSingularSimplex X n
              (barycentricSubdivisionSingularSimplex X n σ p) ps) q =
          barycentricSubdivisionSingularSimplex X n
            (iteratedBarycentricSingularSimplex X n σ
              (ps ++ [p])) q
      rw [ih]

/--
%%handwave
name:
  Every sufficiently refined singular child is cover-small
statement:
  For a singular $n$-simplex and an open cover of $X$, there is $N$ such that
  every child indexed by a list of $N$ barycentric refinements has image in
  one cover member.
proof:
  Apply the subordination theorem to the continuous map underlying the
  simplex and identify each affine child with the corresponding singular
  child.
-/
theorem iteratedBarycentricSingularSimplex_eventually_small
    (X : TopCat.{w}) {ι : Type w} (U : ι → Opens X)
    (hU : IsOpenCover U) (n : ℕ)
    (σ : TopCat.toSSet.obj X _⦋n⦌) :
    ∃ N : ℕ, ∀ ps : List (Equiv.Perm (Fin (n + 1))),
      ps.length = N →
      iteratedBarycentricSingularSimplex X n σ ps ∈
        (openCoverSmallSingularSet X U).obj (op ⦋n⦌) := by
  obtain ⟨N, hN⟩ :=
    stdSimplex.iteratedBarycentricAffineMaps_subordinate
      U hU (TopCat.toSSetObjEquiv X _ σ)
  refine ⟨N, fun ps hps => ?_⟩
  obtain ⟨i, hi⟩ := hN ps hps
  refine ⟨i, ?_⟩
  rw [iteratedBarycentricSingularSimplex_toContinuousMap]
  exact hi

/--
%%handwave
name:
  Iterated barycentric subdivision on singular chains
statement:
  Define the $N$-fold barycentric subdivision endomorphism recursively, with
  zeroth iterate the identity.
-/
noncomputable def barycentricSubdivisionIterate
    (X : TopCat.{w}) :
    ℕ → (realSingularChains X ⟶ realSingularChains X) :=
  fun N =>
    Nat.rec (𝟙 _)
      (fun _ f => barycentricSubdivision X ≫ f) N

/--
%%handwave
name:
  Successor barycentric subdivision iterate
statement:
  The $(N+1)$st iterate is one barycentric subdivision followed by the
  $N$th iterate.
proof:
  This is the successor clause of the recursive definition.
-/
@[simp]
theorem barycentricSubdivisionIterate_succ
    (X : TopCat.{w}) (N : ℕ) :
    barycentricSubdivisionIterate X (N + 1) =
      barycentricSubdivision X ≫
        barycentricSubdivisionIterate X N :=
  rfl

/--
%%handwave
name:
  A uniformly small iterated subdivision factors through small chains
statement:
  If every $N$-fold barycentric child of a singular $n$-simplex is
  cover-small, then the chain obtained by applying the $N$th subdivision
  iterate to that generator factors through the cover-small chain group.
proof:
  Induct on $N$.  At a successor, factor every signed barycentric child by the
  induction hypothesis and sum the resulting factorizations.
-/
theorem singularSimplex_iteratedSubdivision_factors_small
    (X : TopCat.{w}) {ι : Type w} (U : ι → Opens X)
    (n N : ℕ)
    (σ : TopCat.toSSet.obj X _⦋n⦌)
    (hsmall :
      ∀ ps : List (Equiv.Perm (Fin (n + 1))),
        ps.length = N →
        iteratedBarycentricSingularSimplex X n σ ps ∈
          (openCoverSmallSingularSet X U).obj (op ⦋n⦌)) :
    ∃ g :
        realSingularChainCoefficient ⟶
          (smallRealSingularChains X U).X n,
      g ≫ (smallRealSingularChainsInclusion X U).f n =
        (TopCat.toSSet.obj X).ιChainComplex
            (R := realSingularChainCoefficient) σ ≫
          (barycentricSubdivisionIterate X N).f n := by
  induction N generalizing σ with
  | zero =>
      have hσ := hsmall [] rfl
      refine ⟨
        (openCoverSmallSingularSet X U : SSet.{w}).ιChainComplex
          (R := realSingularChainCoefficient) ⟨σ, hσ⟩, ?_⟩
      dsimp only [smallRealSingularChainsInclusion]
      rw [SSet.ι_chainComplexMap_f]
      change
        (TopCat.toSSet.obj X).ιChainComplex
            (R := realSingularChainCoefficient) σ =
          (TopCat.toSSet.obj X).ιChainComplex
              (R := realSingularChainCoefficient) σ ≫ 𝟙 _
      rw [Category.comp_id]
  | succ N ih =>
      have hfactor (p : Equiv.Perm (Fin (n + 1))) :
          ∃ g :
              realSingularChainCoefficient ⟶
                (smallRealSingularChains X U).X n,
            g ≫ (smallRealSingularChainsInclusion X U).f n =
              (TopCat.toSSet.obj X).ιChainComplex
                  (R := realSingularChainCoefficient)
                  (barycentricSubdivisionSingularSimplex X n σ p) ≫
                (barycentricSubdivisionIterate X N).f n := by
        apply ih
        intro ps hps
        rw [iteratedBarycentricSingularSimplex_append_singleton]
        apply hsmall
        simp [hps]
      choose g hg using hfactor
      refine ⟨
        ∑ p : Equiv.Perm (Fin (n + 1)),
          ((Equiv.Perm.sign p : ℤˣ) : ℤ) • g p, ?_⟩
      calc
        (∑ p : Equiv.Perm (Fin (n + 1)),
              ((Equiv.Perm.sign p : ℤˣ) : ℤ) • g p) ≫
            (smallRealSingularChainsInclusion X U).f n =
          ∑ p : Equiv.Perm (Fin (n + 1)),
            ((Equiv.Perm.sign p : ℤˣ) : ℤ) •
              (g p ≫
                (smallRealSingularChainsInclusion X U).f n) := by
          rw [Preadditive.sum_comp]
          simp_rw [Preadditive.zsmul_comp]
        _ = ∑ p : Equiv.Perm (Fin (n + 1)),
            ((Equiv.Perm.sign p : ℤˣ) : ℤ) •
              ((TopCat.toSSet.obj X).ιChainComplex
                  (R := realSingularChainCoefficient)
                  (barycentricSubdivisionSingularSimplex X n σ p) ≫
                (barycentricSubdivisionIterate X N).f n) := by
          apply Finset.sum_congr rfl
          intro p _
          rw [hg]
        _ = (∑ p : Equiv.Perm (Fin (n + 1)),
            ((Equiv.Perm.sign p : ℤˣ) : ℤ) •
              (TopCat.toSSet.obj X).ιChainComplex
                (R := realSingularChainCoefficient)
                (barycentricSubdivisionSingularSimplex X n σ p)) ≫
              (barycentricSubdivisionIterate X N).f n := by
          rw [Preadditive.sum_comp]
          simp_rw [Preadditive.zsmul_comp]
        _ = ((TopCat.toSSet.obj X).ιChainComplex
                (R := realSingularChainCoefficient) σ ≫
              barycentricSubdivisionDegree X n) ≫
            (barycentricSubdivisionIterate X N).f n := by
          rw [singularSimplex_comp_barycentricSubdivisionDegree]
        _ = (TopCat.toSSet.obj X).ιChainComplex
                (R := realSingularChainCoefficient) σ ≫
            (barycentricSubdivisionDegree X n ≫
              (barycentricSubdivisionIterate X N).f n) :=
          Category.assoc _ _ _
        _ = (TopCat.toSSet.obj X).ιChainComplex
                (R := realSingularChainCoefficient) σ ≫
            (barycentricSubdivisionIterate X (N + 1)).f n := by
          rfl

/--
%%handwave
name:
  Barycentric subdivision also commutes on the right with its iterates
statement:
  The $(N+1)$st subdivision iterate equals the $N$th iterate followed by one
  subdivision.
proof:
  Induct on $N$ and use associativity.
-/
theorem barycentricSubdivisionIterate_succ_eq_comp
    (X : TopCat.{w}) (N : ℕ) :
    barycentricSubdivisionIterate X (N + 1) =
      barycentricSubdivisionIterate X N ≫
        barycentricSubdivision X := by
  induction N with
  | zero => simp [barycentricSubdivisionIterate]
  | succ N ih =>
      calc
        barycentricSubdivisionIterate X (N + 1 + 1) =
            barycentricSubdivision X ≫
              barycentricSubdivisionIterate X (N + 1) :=
          rfl
        _ = barycentricSubdivision X ≫
            (barycentricSubdivisionIterate X N ≫
              barycentricSubdivision X) := by
          rw [ih]
        _ = (barycentricSubdivision X ≫
              barycentricSubdivisionIterate X N) ≫
            barycentricSubdivision X := by
          rw [Category.assoc]
        _ = barycentricSubdivisionIterate X (N + 1) ≫
            barycentricSubdivision X :=
          rfl

/--
%%handwave
name:
  Cover-small subdivision commutes with inclusion
statement:
  Subdividing in the cover-small complex and then including equals including
  first and applying ordinary barycentric subdivision.
proof:
  Extensionality reduces the chain-map equality to the degreewise
  compatibility already proved on generators.
-/
theorem smallBarycentricSubdivision_comp_inclusion
    (X : TopCat.{w}) {ι : Type w} (U : ι → Opens X) :
    smallBarycentricSubdivision X U ≫
        smallRealSingularChainsInclusion X U =
      smallRealSingularChainsInclusion X U ≫
        barycentricSubdivision X := by
  apply HomologicalComplex.Hom.ext
  funext n
  change
    smallBarycentricSubdivisionDegree X U n ≫
        (smallRealSingularChainsInclusion X U).f n =
      (smallRealSingularChainsInclusion X U).f n ≫
        barycentricSubdivisionDegree X n
  exact smallBarycentricSubdivisionCompatibility X U n

/--
%%handwave
name:
  Iterated subdivision on cover-small chains
statement:
  Define the $N$-fold barycentric subdivision endomorphism of cover-small
  chains recursively, with zeroth iterate the identity.
-/
noncomputable def smallBarycentricSubdivisionIterate
    (X : TopCat.{w}) {ι : Type w} (U : ι → Opens X) :
    ℕ →
      (smallRealSingularChains X U ⟶
        smallRealSingularChains X U) :=
  fun N =>
    Nat.rec (𝟙 _)
      (fun _ f => smallBarycentricSubdivision X U ≫ f) N

/--
%%handwave
name:
  Successor small subdivision iterate
statement:
  The $(N+1)$st cover-small iterate is one small subdivision followed by the
  $N$th iterate.
proof:
  This is the successor clause of the recursive definition.
-/
@[simp]
theorem smallBarycentricSubdivisionIterate_succ
    (X : TopCat.{w}) {ι : Type w} (U : ι → Opens X)
    (N : ℕ) :
    smallBarycentricSubdivisionIterate X U (N + 1) =
      smallBarycentricSubdivision X U ≫
        smallBarycentricSubdivisionIterate X U N :=
  rfl

/--
%%handwave
name:
  Iterated small subdivision commutes with inclusion
statement:
  For every $N$, inclusion intertwines the $N$th cover-small subdivision
  iterate with the $N$th ordinary subdivision iterate.
proof:
  Induct on $N$ using the one-step compatibility and associativity.
-/
theorem smallBarycentricSubdivisionIterate_comp_inclusion
    (X : TopCat.{w}) {ι : Type w} (U : ι → Opens X)
    (N : ℕ) :
    smallBarycentricSubdivisionIterate X U N ≫
        smallRealSingularChainsInclusion X U =
      smallRealSingularChainsInclusion X U ≫
        barycentricSubdivisionIterate X N := by
  induction N with
  | zero =>
      simp [smallBarycentricSubdivisionIterate,
        barycentricSubdivisionIterate]
  | succ N ih =>
      calc
        (smallBarycentricSubdivision X U ≫
              smallBarycentricSubdivisionIterate X U N) ≫
            smallRealSingularChainsInclusion X U =
          smallBarycentricSubdivision X U ≫
            (smallBarycentricSubdivisionIterate X U N ≫
              smallRealSingularChainsInclusion X U) :=
          Category.assoc _ _ _
        _ = smallBarycentricSubdivision X U ≫
            (smallRealSingularChainsInclusion X U ≫
              barycentricSubdivisionIterate X N) := by
          rw [ih]
        _ = (smallBarycentricSubdivision X U ≫
              smallRealSingularChainsInclusion X U) ≫
            barycentricSubdivisionIterate X N := by
          rw [Category.assoc]
        _ = (smallRealSingularChainsInclusion X U ≫
              barycentricSubdivision X) ≫
            barycentricSubdivisionIterate X N := by
          rw [smallBarycentricSubdivision_comp_inclusion]
        _ = smallRealSingularChainsInclusion X U ≫
            (barycentricSubdivision X ≫
              barycentricSubdivisionIterate X N) :=
          Category.assoc _ _ _

/--
%%handwave
name:
  Iterated subdivision acts trivially on singular homology
statement:
  Every iterate of barycentric subdivision induces the identity on real
  singular homology in every degree.
proof:
  Induct on the iterate and use that the subdivision prism makes one
  subdivision chain-homotopic to the identity.
-/
theorem barycentricSubdivisionIterate_homologyMap
    (X : TopCat.{w}) (N n : ℕ) :
    homologyMap (barycentricSubdivisionIterate X N) n =
      𝟙 _ := by
  induction N with
  | zero => simp [barycentricSubdivisionIterate]
  | succ N ih =>
      rw [barycentricSubdivisionIterate_succ,
        homologyMap_comp,
        ← (subdivisionPrismHomotopy X).homologyMap_eq,
        homologyMap_id, Category.id_comp, ih]

/--
%%handwave
name:
  Iterated small subdivision acts trivially on homology
statement:
  Every iterate of cover-small barycentric subdivision induces the identity
  on the homology of the cover-small chain complex.
proof:
  Induct on the iterate and use the restricted subdivision-prism homotopy.
-/
theorem smallBarycentricSubdivisionIterate_homologyMap
    (X : TopCat.{w}) {ι : Type w} (U : ι → Opens X)
    (N n : ℕ) :
    homologyMap
        (smallBarycentricSubdivisionIterate X U N) n =
      𝟙 _ := by
  induction N with
  | zero => simp [smallBarycentricSubdivisionIterate]
  | succ N ih =>
      rw [smallBarycentricSubdivisionIterate_succ,
        homologyMap_comp,
        ← (smallSubdivisionPrismHomotopy X U).homologyMap_eq,
        homologyMap_id, Category.id_comp, ih]

/--
%%handwave
name:
  Elementwise compatibility of small subdivision and inclusion
statement:
  For every cover-small chain $c$, including its subdivision equals
  subdividing its image in the ordinary singular-chain complex.
proof:
  Evaluate the degreewise compatibility of the two chain maps at $c$.
-/
theorem smallBarycentricSubdivision_apply_inclusion
    (X : TopCat.{w}) {ι : Type w} (U : ι → Opens X)
    (n : ℕ) (c : (smallRealSingularChains X U).X n) :
    (smallRealSingularChainsInclusion X U).f n
        ((smallBarycentricSubdivision X U).f n c) =
      (barycentricSubdivision X).f n
        ((smallRealSingularChainsInclusion X U).f n c) := by
  exact DFunLike.congr_fun
    (congrArg ModuleCat.Hom.hom
      (smallBarycentricSubdivisionCompatibility X U n)) c

/--
%%handwave
name:
  Promotion of a small factorization by one subdivision
statement:
  If the $N$th subdivision of a chain factors through cover-small chains,
  then so does its $(N+1)$st subdivision.
proof:
  Apply cover-small subdivision to the factor and use compatibility with
  inclusion.
-/
theorem iteratedSubdivision_factor_promote_one
    (X : TopCat.{w}) {ι : Type w} (U : ι → Opens X)
    (n N : ℕ) (c : (realSingularChains X).X n)
    (s : (smallRealSingularChains X U).X n)
    (h :
      (smallRealSingularChainsInclusion X U).f n s =
        (barycentricSubdivisionIterate X N).f n c) :
    ∃ s' : (smallRealSingularChains X U).X n,
      (smallRealSingularChainsInclusion X U).f n s' =
        (barycentricSubdivisionIterate X (N + 1)).f n c := by
  refine ⟨(smallBarycentricSubdivision X U).f n s, ?_⟩
  rw [smallBarycentricSubdivision_apply_inclusion, h,
    barycentricSubdivisionIterate_succ_eq_comp]
  rfl

/--
%%handwave
name:
  Promotion of a small factorization by finitely many subdivisions
statement:
  If the $N$th subdivision of a chain factors through cover-small chains,
  then the $(N+k)$th subdivision factors through cover-small chains for every
  $k$.
proof:
  Induct on $k$ using one-step promotion.
-/
theorem iteratedSubdivision_factor_promote
    (X : TopCat.{w}) {ι : Type w} (U : ι → Opens X)
    (n N : ℕ) (c : (realSingularChains X).X n)
    (s : (smallRealSingularChains X U).X n)
    (h :
      (smallRealSingularChainsInclusion X U).f n s =
        (barycentricSubdivisionIterate X N).f n c)
    (k : ℕ) :
    ∃ s' : (smallRealSingularChains X U).X n,
      (smallRealSingularChainsInclusion X U).f n s' =
        (barycentricSubdivisionIterate X (N + k)).f n c := by
  induction k with
  | zero =>
      exact ⟨s, by simpa using h⟩
  | succ k ih =>
      obtain ⟨s', hs'⟩ := ih
      simpa [Nat.add_assoc] using
        iteratedSubdivision_factor_promote_one
          X U n (N + k) c s' hs'

/--
%%handwave
name:
  Every singular-chain generator eventually factors through small chains
statement:
  For every scalar multiple of a singular $n$-simplex, some subdivision
  iterate lies in the image of the cover-small chain group.
proof:
  Choose an iterate for which every barycentric child is cover-small, factor
  the subdivided generator, and evaluate the factorization at the scalar.
-/
theorem singularGenerator_eventually_factors_small
    (X : TopCat.{w}) {ι : Type w} (U : ι → Opens X)
    (hU : IsOpenCover U) (n : ℕ)
    (σ : TopCat.toSSet.obj X _⦋n⦌)
    (r : realSingularChainCoefficient) :
    ∃ N : ℕ, ∃ s : (smallRealSingularChains X U).X n,
      (smallRealSingularChainsInclusion X U).f n s =
        (barycentricSubdivisionIterate X N).f n
          ((TopCat.toSSet.obj X).ιChainComplex
            (R := realSingularChainCoefficient) σ r) := by
  obtain ⟨N, hsmall⟩ :=
    iteratedBarycentricSingularSimplex_eventually_small
      X U hU n σ
  obtain ⟨g, hg⟩ :=
    singularSimplex_iteratedSubdivision_factors_small
      X U n N σ hsmall
  refine ⟨N, g r, ?_⟩
  exact DFunLike.congr_fun
    (congrArg ModuleCat.Hom.hom hg) r

/--
%%handwave
name:
  Every finite singular chain eventually becomes cover-small
statement:
  For every real singular $n$-chain $c$, there is $N$ such that
  $\mathrm{Sd}^N(c)$ lies in the image of the cover-small chain group.
proof:
  Express $c$ in the direct sum of its finitely many simplex coefficients.
  Induct over finite support, choose an iterate for each generator, and
  promote the two iterates to their common sum before adding their small
  factorizations.
-/
theorem singularChain_eventually_factors_small
    (X : TopCat.{w}) {ι : Type w} (U : ι → Opens X)
    (hU : IsOpenCover U) (n : ℕ)
    (c : (realSingularChains X).X n) :
    ∃ N : ℕ, ∃ s : (smallRealSingularChains X U).X n,
      (smallRealSingularChainsInclusion X U).f n s =
        (barycentricSubdivisionIterate X N).f n c := by
  classical
  let S := TopCat.toSSet.obj X _⦋n⦌
  let Z : S → ModuleCat.{w} ℝ :=
    fun _ => realSingularChainCoefficient
  let e := ModuleCat.coprodIsoDirectSum Z
  let d : (⨁ σ : S, Z σ) := e.hom c
  have hd :
      ∃ N : ℕ, ∃ s : (smallRealSingularChains X U).X n,
        (smallRealSingularChainsInclusion X U).f n s =
          (barycentricSubdivisionIterate X N).f n
            (e.inv d) := by
    induction d using DirectSum.induction_on with
    | zero =>
        refine ⟨0, 0, ?_⟩
        dsimp [barycentricSubdivisionIterate]
        simp
        rfl
    | of σ r =>
        have he :
            e.inv
                (DirectSum.lof ℝ S (fun i => (Z i : Type w)) σ r) =
              (TopCat.toSSet.obj X).ιChainComplex
                (R := realSingularChainCoefficient) σ r := by
          exact DFunLike.congr_fun
            (congrArg ModuleCat.Hom.hom
              (ModuleCat.lof_coprodIsoDirectSum_inv Z σ)) r
        change
          ∃ N : ℕ, ∃ s : (smallRealSingularChains X U).X n,
            (smallRealSingularChainsInclusion X U).f n s =
              (barycentricSubdivisionIterate X N).f n
                (e.inv
                  (DirectSum.lof ℝ S
                    (fun i => (Z i : Type w)) σ r))
        rw [he]
        exact singularGenerator_eventually_factors_small
          X U hU n σ r
    | add x y hx hy =>
        obtain ⟨Nx, sx, hsx⟩ := hx
        obtain ⟨Ny, sy, hsy⟩ := hy
        obtain ⟨sx', hsx'⟩ :=
          iteratedSubdivision_factor_promote
            X U n Nx (e.inv x) sx hsx Ny
        obtain ⟨sy', hsy'⟩ :=
          iteratedSubdivision_factor_promote
            X U n Ny (e.inv y) sy hsy Nx
        refine ⟨Nx + Ny, sx' + sy', ?_⟩
        rw [map_add, hsx']
        rw [show Ny + Nx = Nx + Ny by omega] at hsy'
        rw [hsy']
        symm
        rw [map_add]
        exact map_add
          ((barycentricSubdivisionIterate X (Nx + Ny)).f n).hom
          _ _
  obtain ⟨N, s, hs⟩ := hd
  refine ⟨N, s, ?_⟩
  simpa [d, e] using hs

/--
%%handwave
name:
  A zero homology class is represented by a boundary
statement:
  Let $K$ be a real chain complex.  If a cycle $z$ maps to zero in
  $H_n(K)$, then there is $b\in K_{n+1}$ with
  $\partial b=z$ after viewing $z$ in $K_n$.
proof:
  Transport the assertion through the concrete module-category description
  of homology as cycles modulo boundaries.  Membership in the boundary
  submodule supplies the required preimage.
-/
theorem exists_boundary_of_homologyπ_eq_zero
    (K : ChainComplex (ModuleCat.{w} ℝ) ℕ) (n : ℕ)
    (z : K.cycles n)
    (hz : K.homologyπ n z = 0) :
    ∃ b : K.X ((ComplexShape.down ℕ).prev n),
      K.d ((ComplexShape.down ℕ).prev n) n b =
        K.iCycles n z := by
  let S := K.sc n
  have hq :
      S.moduleCatLeftHomologyData.π
          (S.moduleCatCyclesIso.hom z) = 0 := by
    calc
      _ = S.moduleCatHomologyIso.hom
          (K.homologyπ n z) := by
        exact
          (ConcreteCategory.congr_hom
            S.π_moduleCatCyclesIso_hom z).symm
      _ = 0 := by
        rw [hz]
        exact S.moduleCatHomologyIso.hom.hom.map_zero
  change
    Submodule.Quotient.mk
      (S.moduleCatCyclesIso.hom z) = 0 at hq
  rw [Submodule.Quotient.mk_eq_zero] at hq
  obtain ⟨b, hb⟩ := hq
  refine ⟨b, ?_⟩
  have hbval := congrArg Subtype.val hb
  change
    K.d ((ComplexShape.down ℕ).prev n) n b =
      (S.moduleCatCyclesIso.hom z).1 at hbval
  calc
    _ = (S.moduleCatCyclesIso.hom z).1 := hbval
    _ = K.iCycles n z := by
      exact ConcreteCategory.congr_hom
        S.moduleCatCyclesIso_hom_i z

/--
%%handwave
name:
  A cycle represented by a boundary has zero homology class
statement:
  Let $K$ be a real chain complex.  If $z$ is a cycle and
  $\partial b=z$ in $K_n$, then the class of $z$ in $H_n(K)$ is zero.
proof:
  Under the concrete quotient of cycles by boundaries, the cycle lies in the
  boundary submodule with witness $b$, so its quotient class vanishes.
-/
theorem homologyπ_eq_zero_of_boundary
    (K : ChainComplex (ModuleCat ℝ) ℕ) (n : ℕ)
    (z : K.cycles n)
    (b : K.X ((ComplexShape.down ℕ).prev n))
    (hb :
      K.d ((ComplexShape.down ℕ).prev n) n b =
        K.iCycles n z) :
    K.homologyπ n z = 0 := by
  let S := K.sc n
  apply
    (ModuleCat.mono_iff_injective S.moduleCatHomologyIso.hom).1
      inferInstance
  calc
    S.moduleCatHomologyIso.hom (K.homologyπ n z) =
        S.moduleCatLeftHomologyData.π
          (S.moduleCatCyclesIso.hom z) := by
      exact ConcreteCategory.congr_hom S.π_moduleCatCyclesIso_hom z
    _ = 0 := by
      change Submodule.Quotient.mk
        (S.moduleCatCyclesIso.hom z) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      refine ⟨b, ?_⟩
      apply Subtype.ext
      change
        K.d ((ComplexShape.down ℕ).prev n) n b =
          (S.moduleCatCyclesIso.hom z).1
      calc
        _ = K.iCycles n z := hb
        _ = (S.moduleCatCyclesIso.hom z).1 := by
          exact (ConcreteCategory.congr_hom
            S.moduleCatCyclesIso_hom_i z).symm
    _ = S.moduleCatHomologyIso.hom 0 := by
      exact S.moduleCatHomologyIso.hom.hom.map_zero.symm

/--
%%handwave
name:
  Surjectivity of small-chain inclusion on homology
statement:
  For an open cover of $X$, every class in ordinary real singular homology is
  the image of a class represented by a cover-small cycle.
proof:
  Represent the class by a finite cycle and subdivide until the chain factors
  through cover-small chains.  Monicity of inclusion shows the factor is a
  cycle.  Naturality of the homology projection and triviality of subdivision
  on homology identify its image with the original class.
-/
theorem smallChainsInclusion_homologyMap_surjective
    (X : TopCat.{w}) {ι : Type w} (U : ι → Opens X)
    (hU : IsOpenCover U) (n : ℕ) :
    Function.Surjective
      (homologyMap (smallRealSingularChainsInclusion X U) n) := by
  intro y
  obtain ⟨z, hz⟩ :=
    (ModuleCat.epi_iff_surjective
      ((realSingularChains X).homologyπ n)).1
      inferInstance y
  let c : (realSingularChains X).X n :=
    (realSingularChains X).iCycles n z
  obtain ⟨N, s, hs⟩ :=
    singularChain_eventually_factors_small X U hU n c
  let m := (ComplexShape.down ℕ).next n
  have hc :
      (realSingularChains X).d n m c = 0 := by
    exact DFunLike.congr_fun
      (congrArg ModuleCat.Hom.hom
        ((realSingularChains X).iCycles_d n m)) z
  have hs_cycle :
      (smallRealSingularChains X U).d n m s = 0 := by
    apply (ModuleCat.mono_iff_injective
      ((smallRealSingularChainsInclusion X U).f m)).1
      inferInstance
    calc
      (smallRealSingularChainsInclusion X U).f m
          ((smallRealSingularChains X U).d n m s) =
        (realSingularChains X).d n m
          ((smallRealSingularChainsInclusion X U).f n s) := by
            exact (ConcreteCategory.congr_hom
              ((smallRealSingularChainsInclusion X U).comm n m) s).symm
      _ = (realSingularChains X).d n m
          ((barycentricSubdivisionIterate X N).f n c) := by
            rw [hs]
      _ = (barycentricSubdivisionIterate X N).f m
          ((realSingularChains X).d n m c) := by
            exact ConcreteCategory.congr_hom
              ((barycentricSubdivisionIterate X N).comm n m) c
      _ = 0 := by rw [hc, map_zero]
      _ = (smallRealSingularChainsInclusion X U).f m 0 := by
            rw [map_zero]
  let zs : (smallRealSingularChains X U).cycles n :=
    ((smallRealSingularChains X U).sc n).moduleCatCyclesIso.inv
      ⟨s, hs_cycle⟩
  have hzs :
      (smallRealSingularChains X U).iCycles n zs = s := by
    exact ConcreteCategory.congr_hom
      ((smallRealSingularChains X U).sc n).moduleCatCyclesIso_inv_iCycles
        ⟨s, hs_cycle⟩
  have hcycles :
      cyclesMap (smallRealSingularChainsInclusion X U) n zs =
        cyclesMap (barycentricSubdivisionIterate X N) n z := by
    apply (ModuleCat.mono_iff_injective
      ((realSingularChains X).iCycles n)).1 inferInstance
    calc
      (realSingularChains X).iCycles n
          (cyclesMap
            (smallRealSingularChainsInclusion X U) n zs) =
        (smallRealSingularChainsInclusion X U).f n
          ((smallRealSingularChains X U).iCycles n zs) := by
            exact ConcreteCategory.congr_hom
              (cyclesMap_i
                (smallRealSingularChainsInclusion X U) n) zs
      _ = (smallRealSingularChainsInclusion X U).f n s := by
            rw [hzs]
      _ = (barycentricSubdivisionIterate X N).f n c := hs
      _ = (barycentricSubdivisionIterate X N).f n
          ((realSingularChains X).iCycles n z) := rfl
      _ = (realSingularChains X).iCycles n
          (cyclesMap
            (barycentricSubdivisionIterate X N) n z) := by
            exact (ConcreteCategory.congr_hom
              (cyclesMap_i
                (barycentricSubdivisionIterate X N) n) z).symm
  refine ⟨(smallRealSingularChains X U).homologyπ n zs, ?_⟩
  calc
    homologyMap (smallRealSingularChainsInclusion X U) n
        ((smallRealSingularChains X U).homologyπ n zs) =
      (realSingularChains X).homologyπ n
        (cyclesMap
          (smallRealSingularChainsInclusion X U) n zs) := by
            exact ConcreteCategory.congr_hom
              (homologyπ_naturality
                (φ := smallRealSingularChainsInclusion X U) n) zs
    _ = (realSingularChains X).homologyπ n
        (cyclesMap
          (barycentricSubdivisionIterate X N) n z) := by
            rw [hcycles]
    _ = homologyMap (barycentricSubdivisionIterate X N) n
        ((realSingularChains X).homologyπ n z) := by
            exact (ConcreteCategory.congr_hom
              (homologyπ_naturality
                (φ := barycentricSubdivisionIterate X N) n) z).symm
    _ = (realSingularChains X).homologyπ n z := by
          rw [barycentricSubdivisionIterate_homologyMap]
          rfl
    _ = y := hz

/--
%%handwave
name:
  Kernel of small-chain inclusion on homology is zero
statement:
  For an open cover of $X$, a cover-small homology class whose image in
  ordinary singular homology is zero must itself be zero.
proof:
  Represent the class by a small cycle and choose an ordinary bounding chain.
  Subdivide that finite bounding chain until it is small.  Compatibility of
  subdivision with the boundary shows that it bounds the corresponding
  subdivided small cycle; subdivision acts as the identity on small-chain
  homology.
-/
theorem smallChainsInclusion_homologyMap_eq_zero
    (X : TopCat.{w}) {ι : Type w} (U : ι → Opens X)
    (hU : IsOpenCover U) (n : ℕ)
    (x : (smallRealSingularChains X U).homology n)
    (hx :
      homologyMap (smallRealSingularChainsInclusion X U) n x = 0) :
    x = 0 := by
  obtain ⟨z, hz⟩ :=
    (ModuleCat.epi_iff_surjective
      ((smallRealSingularChains X U).homologyπ n)).1
      inferInstance x
  have hfullzero :
      (realSingularChains X).homologyπ n
          (cyclesMap
            (smallRealSingularChainsInclusion X U) n z) = 0 := by
    calc
      _ = homologyMap (smallRealSingularChainsInclusion X U) n
          ((smallRealSingularChains X U).homologyπ n z) := by
            exact (ConcreteCategory.congr_hom
              (homologyπ_naturality
                (φ := smallRealSingularChainsInclusion X U) n) z).symm
      _ = homologyMap (smallRealSingularChainsInclusion X U) n x := by
            rw [hz]
      _ = 0 := hx
  obtain ⟨b, hb⟩ :=
    exists_boundary_of_homologyπ_eq_zero
      (realSingularChains X) n
      (cyclesMap (smallRealSingularChainsInclusion X U) n z)
      hfullzero
  let p := (ComplexShape.down ℕ).prev n
  obtain ⟨N, t, ht⟩ :=
    singularChain_eventually_factors_small X U hU p b
  have hboundary :
      (smallRealSingularChains X U).d p n t =
        (smallBarycentricSubdivisionIterate X U N).f n
          ((smallRealSingularChains X U).iCycles n z) := by
    apply (ModuleCat.mono_iff_injective
      ((smallRealSingularChainsInclusion X U).f n)).1
      inferInstance
    calc
      (smallRealSingularChainsInclusion X U).f n
          ((smallRealSingularChains X U).d p n t) =
        (realSingularChains X).d p n
          ((smallRealSingularChainsInclusion X U).f p t) := by
            exact (ConcreteCategory.congr_hom
              ((smallRealSingularChainsInclusion X U).comm p n) t).symm
      _ = (realSingularChains X).d p n
          ((barycentricSubdivisionIterate X N).f p b) := by
            rw [ht]
      _ = (barycentricSubdivisionIterate X N).f n
          ((realSingularChains X).d p n b) := by
            exact ConcreteCategory.congr_hom
              ((barycentricSubdivisionIterate X N).comm p n) b
      _ = (barycentricSubdivisionIterate X N).f n
          ((realSingularChains X).iCycles n
            (cyclesMap
              (smallRealSingularChainsInclusion X U) n z)) := by
            rw [hb]
      _ = (barycentricSubdivisionIterate X N).f n
          ((smallRealSingularChainsInclusion X U).f n
            ((smallRealSingularChains X U).iCycles n z)) := by
            exact congrArg
              (fun q => (barycentricSubdivisionIterate X N).f n q)
              (ConcreteCategory.congr_hom
                (cyclesMap_i
                  (smallRealSingularChainsInclusion X U) n) z)
      _ = (smallRealSingularChainsInclusion X U).f n
          ((smallBarycentricSubdivisionIterate X U N).f n
            ((smallRealSingularChains X U).iCycles n z)) := by
            have hcomp :=
              congrArg (fun φ => φ.f n)
                (smallBarycentricSubdivisionIterate_comp_inclusion X U N)
            exact (ConcreteCategory.congr_hom hcomp
              ((smallRealSingularChains X U).iCycles n z)).symm
  let zN : (smallRealSingularChains X U).cycles n :=
    cyclesMap
      (smallBarycentricSubdivisionIterate X U N) n z
  have hzNboundary :
      (smallRealSingularChains X U).d p n t =
        (smallRealSingularChains X U).iCycles n zN := by
    calc
      _ = (smallBarycentricSubdivisionIterate X U N).f n
          ((smallRealSingularChains X U).iCycles n z) := hboundary
      _ = (smallRealSingularChains X U).iCycles n zN := by
            exact (ConcreteCategory.congr_hom
              (cyclesMap_i
                (smallBarycentricSubdivisionIterate X U N) n) z).symm
  have hzNzero :
      (smallRealSingularChains X U).homologyπ n zN = 0 :=
    homologyπ_eq_zero_of_boundary
      (smallRealSingularChains X U) n zN t hzNboundary
  have hzπzero :
      (smallRealSingularChains X U).homologyπ n z = 0 := by
    have hiter :
        homologyMap
            (smallBarycentricSubdivisionIterate X U N) n
            ((smallRealSingularChains X U).homologyπ n z) = 0 := by
      calc
        _ = (smallRealSingularChains X U).homologyπ n
            (cyclesMap
              (smallBarycentricSubdivisionIterate X U N) n z) := by
                exact ConcreteCategory.congr_hom
                  (homologyπ_naturality
                    (φ :=
                      smallBarycentricSubdivisionIterate X U N) n) z
        _ = 0 := hzNzero
    rw [smallBarycentricSubdivisionIterate_homologyMap] at hiter
    exact hiter
  calc
    x = (smallRealSingularChains X U).homologyπ n z := hz.symm
    _ = 0 := hzπzero

/--
%%handwave
name:
  Injectivity of small-chain inclusion on homology
statement:
  For every open cover of $X$, inclusion of cover-small chains induces an
  injective map on real homology in every degree.
proof:
  Apply the zero-kernel result to the difference of two classes with equal
  images.
-/
theorem smallChainsInclusion_homologyMap_injective
    (X : TopCat.{w}) {ι : Type w} (U : ι → Opens X)
    (hU : IsOpenCover U) (n : ℕ) :
    Function.Injective
      (homologyMap (smallRealSingularChainsInclusion X U) n) := by
  intro x y hxy
  have hsub :
      homologyMap (smallRealSingularChainsInclusion X U) n (x - y) =
        0 := by
    rw [map_sub, hxy, sub_self]
  exact sub_eq_zero.mp
    (smallChainsInclusion_homologyMap_eq_zero X U hU n (x - y) hsub)

/--
%%handwave
name:
  Small-chain inclusion is an isomorphism on homology
statement:
  For every open cover of $X$, inclusion of cover-small real singular chains
  induces a bijection on homology in every degree.
proof:
  Combine injectivity and surjectivity of the induced homology map.
-/
theorem smallChainsInclusion_homologyMap_bijective
    (X : TopCat.{w}) {ι : Type w} (U : ι → Opens X)
    (hU : IsOpenCover U) (n : ℕ) :
    Function.Bijective
      (homologyMap (smallRealSingularChainsInclusion X U) n) :=
  ⟨smallChainsInclusion_homologyMap_injective X U hU n,
    smallChainsInclusion_homologyMap_surjective X U hU n⟩

/--
%%handwave
name:
  Small-chain inclusion is a quasi-isomorphism
statement:
  For every open cover of $X$, inclusion of cover-small real singular chains
  into all real singular chains is a quasi-isomorphism.
proof:
  In each degree, its induced homology map is bijective and hence an
  isomorphism of real modules.
-/
theorem smallRealSingularChainsInclusion_quasiIso
    (X : TopCat.{w}) {ι : Type w} (U : ι → Opens X)
    (hU : IsOpenCover U) :
    QuasiIso (smallRealSingularChainsInclusion X U) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap,
    ConcreteCategory.isIso_iff_bijective]
  exact smallChainsInclusion_homologyMap_bijective X U hU n

/--
%%handwave
name:
  Small singular chains compute singular homology
statement:
  For every open cover $(U_i)_{i\in\iota}$ of a topological space $X$,
  inclusion of the real singular chains generated by simplices subordinate
  to the cover into all real singular chains is a chain-homotopy equivalence.
proof:
  The mesh estimate and finite-support argument show that the inclusion is a
  quasi-isomorphism.  Both chain complexes are nonnegatively graded complexes
  of free, hence projective, real modules, so a quasi-isomorphism between them
  is a chain-homotopy equivalence.
-/
theorem smallRealSingularChainsInclusion_homotopyEquiv
    (X : TopCat.{w}) {ι : Type w} (U : ι → Opens X)
    (hU : IsOpenCover U) :
    ∃ e :
      HomotopyEquiv
        (smallRealSingularChains X U)
        (realSingularChains X),
      e.hom = smallRealSingularChainsInclusion X U := by
  apply
    (ChainComplex.quasiIso_iff_of_projective
      (smallRealSingularChainsInclusion X U)).1
  exact smallRealSingularChainsInclusion_quasiIso X U hU

end

end JJMath.Cohomology
