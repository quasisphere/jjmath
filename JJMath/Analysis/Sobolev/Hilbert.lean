import JJMath.Analysis.Sobolev.Bundle
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Group.Completeness
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Mathlib.Topology.VectorBundle.Constructions

/-!
# Hilbert structure for surface Sobolev spaces

This file records the Hilbert-space input for the representative-level
\(W^{1,2}\) spaces and their zero-trace subspace.
-/

namespace JJMath

open MeasureTheory
open scoped Manifold Topology ENNReal ContDiff Bundle

namespace Uniformization

noncomputable section

/--
The real cotangent fiber of a Riemann surface is the real Hilbert dual of
\(\mathbb C\).  Mathlib has the Riesz isometric equivalence with the strong
dual, but not an instance for this exact dual type, so we transport the inner
product across that equivalence here.
-/
noncomputable instance instComplexRealCotangentInnerProductSpace :
    InnerProductSpace ℝ (ℂ →L[ℝ] ℝ) where
  inner ξ η :=
    inner ℝ ((InnerProductSpace.toDual ℝ ℂ).symm ξ)
      ((InnerProductSpace.toDual ℝ ℂ).symm η)
  norm_sq_eq_re_inner ξ := by
    rw [← (InnerProductSpace.toDual ℝ ℂ).symm.norm_map ξ]
    exact norm_sq_eq_re_inner ((InnerProductSpace.toDual ℝ ℂ).symm ξ)
  conj_inner_symm ξ η := by
    change inner ℝ ((InnerProductSpace.toDual ℝ ℂ).symm η)
        ((InnerProductSpace.toDual ℝ ℂ).symm ξ) =
      inner ℝ ((InnerProductSpace.toDual ℝ ℂ).symm ξ)
        ((InnerProductSpace.toDual ℝ ℂ).symm η)
    exact real_inner_comm _ _
  add_left ξ η ζ := by
    simp [inner_add_left]
  smul_left ξ η r := by
    change inner ℝ ((InnerProductSpace.toDual ℝ ℂ).symm (r • ξ))
        ((InnerProductSpace.toDual ℝ ℂ).symm η) =
      r * inner ℝ ((InnerProductSpace.toDual ℝ ℂ).symm ξ)
        ((InnerProductSpace.toDual ℝ ℂ).symm η)
    have hmap :
        (InnerProductSpace.toDual ℝ ℂ).symm (r • ξ) =
          r • (InnerProductSpace.toDual ℝ ℂ).symm ξ := by
      simp
    rw [hmap]
    exact inner_smul_left ((InnerProductSpace.toDual ℝ ℂ).symm ξ)
      ((InnerProductSpace.toDual ℝ ℂ).symm η) r

/--
%%handwave
name:
  Riesz representatives evaluate cotangent fields
statement:
  Under the transported Hilbert structure on the cotangent fiber, pairing a
  cotangent vector with the Riesz representative of a tangent vector is the same
  as evaluating the cotangent vector on that tangent vector.
proof:
  This is the defining property of the Riesz isometry used to transport the
  inner product to the cotangent fiber.
-/
theorem cotangent_inner_toDual_eq_eval (ξ : ℂ →L[ℝ] ℝ) (v : ℂ) :
    inner ℝ ξ ((InnerProductSpace.toDual ℝ ℂ) v) = ξ v := by
  change inner ℝ ((InnerProductSpace.toDual ℝ ℂ).symm ξ)
      ((InnerProductSpace.toDual ℝ ℂ).symm ((InnerProductSpace.toDual ℝ ℂ) v)) = ξ v
  simp

/--
%%handwave
name:
  Riesz pairing with a scaled dual vector
statement:
  For a real-linear functional \(\xi\) on \(\mathbb C\), scalar \(a\), and vector \(v\), \(\langle\xi,a\,v^\flat\rangle=a\,\xi(v)\).
proof:
  Use the Riesz isometry, linearity in the second argument, and the defining identity between a functional and its dual vector.
-/
private theorem cotangent_inner_smul_toDual_eq_mul_eval
    (ξ : ℂ →L[ℝ] ℝ) (a : ℝ) (v : ℂ) :
    inner ℝ ξ (a • (InnerProductSpace.toDual ℝ ℂ) v) = a * ξ v := by
  calc
    inner ℝ ξ (a • (InnerProductSpace.toDual ℝ ℂ) v) =
        a * inner ℝ ξ ((InnerProductSpace.toDual ℝ ℂ) v) := by
          simpa using
            (real_inner_smul_right ξ ((InnerProductSpace.toDual ℝ ℂ) v) a)
    _ = a * ξ v := by
          rw [cotangent_inner_toDual_eq_eval]

/--
%%handwave
name:
  A type admits a real Hilbert structure
statement:
  A type admits a real Hilbert structure if it can be equipped with a real
  inner product norm and is complete for the associated metric.
-/
def AdmitsRealHilbertStructure (E : Type) : Prop :=
  ∃ (_ : NormedAddCommGroup E), ∃ (_ : InnerProductSpace ℝ E),
    ∃ (_ : CompleteSpace E), Nonempty (HilbertSpace ℝ E)

/--
%%handwave
name:
  \(L^2\) functions form a Hilbert space
statement:
  The space of square-integrable real-valued functions on a measured surface
  is a real Hilbert space.
proof:
  This is the standard \(L^2\) Hilbert-space structure.
-/
theorem surfaceL2Functions_admit_hilbert_structure
    {X : Type} [MeasurableSpace X] (μ : Measure X) :
    AdmitsRealHilbertStructure (Lp ℝ 2 μ) := by
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  exact ⟨HilbertSpace.mk⟩

/--
%%handwave
name:
  Hilbert-valued \(L^2\) functions form a Hilbert space
statement:
  The space of square-integrable maps from a measured space into a real
  Hilbert space is itself a real Hilbert space.
proof:
  This is the standard Hilbert-space structure on Hilbert-valued \(L^2\).
-/
theorem surfaceL2FunctionsWithValues_admit_hilbert_structure
    {X E : Type} [MeasurableSpace X] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (μ : Measure X) :
    AdmitsRealHilbertStructure (Lp E 2 μ) := by
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  exact ⟨HilbertSpace.mk⟩

/--
%%handwave
name:
  The zero section is square-integrable
statement:
  The zero section of a continuous Hilbert bundle is square-integrable.
proof:
  The zero total-space section is measurable, its fiberwise square norm is identically zero, and the zero function is integrable.
-/
theorem hilbertBundleSectionMemL2_zero
    {H X F : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold I 1 X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
    (G : HilbertBundleGeometry X F V)
    (hG_inner : ∀ (x : X) (v w : V x), G.fiberInner x v w = inner ℝ v w)
    (μ : Measure X) :
    HilbertBundleSectionMemL2 G μ (0 : HilbertBundleSectionOnSurface X V) := by
  refine ⟨?_, ?_⟩
  · change AEMeasurable (Bundle.zeroSection F V) μ
    exact (Bundle.contMDiff_zeroSection (𝕜 := ℝ)
      (IB := I) (F := F) (E := V) (n := 1)).continuous.aemeasurable
  · have hzero :
        (fun x : X ↦ G.fiberNormSq x ((0 : HilbertBundleSectionOnSurface X V) x)) =
          fun _ : X ↦ (0 : ℝ) := by
      funext x
      rw [G.fiberNormSq_eq_inner, hG_inner]
      simp
    rw [hzero]
    exact integrable_zero X ℝ μ

/--
%%handwave
name:
  Pair of two bundle sections
statement:
  Two sections of a vector bundle determine a section of the fiberwise product
  bundle by taking their ordered pair in each fiber.
-/
noncomputable def hilbertBundleSectionPairTotalSpace
    {X F : Type} {V : X → Type}
    (s t : HilbertBundleSectionOnSurface X V) :
    X → Bundle.TotalSpace (F × F) (V ×ᵇ V) :=
  fun x ↦ Bundle.TotalSpace.mk' (F × F) x (s x, t x)

/--
%%handwave
name:
  Fiberwise pairs of measurable sections are measurable
statement:
  If two sections of a Borel vector bundle are almost everywhere Borel
  measurable, then their fiberwise pair is almost everywhere Borel measurable
  as a section of the fiberwise product bundle.
proof:
  Combine the two almost-everywhere measurable total-space sections using the continuous fiberwise pairing map.
-/
theorem hilbertBundleSection_aemeasurable_pair
    {X F : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    [SecondCountableTopology (Bundle.TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, Module ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V]
    (μ : Measure X) {s t : HilbertBundleSectionOnSurface X V}
    (hs : AEMeasurable
      (HilbertBundleSectionOnSurface.toTotalSpace (F := F) s) μ)
    (ht : AEMeasurable
      (HilbertBundleSectionOnSurface.toTotalSpace (F := F) t) μ) :
    AEMeasurable (hilbertBundleSectionPairTotalSpace (F := F) s t) μ := by
  let diag :
      Bundle.TotalSpace (F × F) (V ×ᵇ V) →
        Bundle.TotalSpace F V × Bundle.TotalSpace F V :=
    fun p ↦
      ((Bundle.TotalSpace.mk' F p.1 p.2.1 : Bundle.TotalSpace F V),
        (Bundle.TotalSpace.mk' F p.1 p.2.2 : Bundle.TotalSpace F V))
  have hdiag_inj : Function.Injective diag := by
    intro p q hpq
    rcases p with ⟨x, v, w⟩
    rcases q with ⟨y, v', w'⟩
    simp [diag] at hpq ⊢
    rcases hpq with ⟨⟨hxy, hv⟩, ⟨_, hw⟩⟩
    subst y
    simpa using And.intro hv hw
  have hdiag_emb : Topology.IsEmbedding diag :=
    ⟨FiberBundle.Prod.isInducing_diag F V F V, hdiag_inj⟩
  have hdiag_range :
      MeasurableSet (Set.range diag) := by
    have hbase₁ : Measurable fun z : Bundle.TotalSpace F V × Bundle.TotalSpace F V ↦ z.1.1 :=
      (FiberBundle.continuous_proj F V).measurable.comp measurable_fst
    have hbase₂ : Measurable fun z : Bundle.TotalSpace F V × Bundle.TotalSpace F V ↦ z.2.1 :=
      (FiberBundle.continuous_proj F V).measurable.comp measurable_snd
    have hset :
        MeasurableSet
          {z : Bundle.TotalSpace F V × Bundle.TotalSpace F V | z.1.1 = z.2.1} :=
      measurableSet_eq_fun hbase₁ hbase₂
    convert hset using 1
    ext z
    constructor
    · rintro ⟨p, rfl⟩
      rfl
    · intro hz
      rcases z with ⟨p, q⟩
      cases p with
      | mk x v =>
        cases q with
        | mk y w =>
          dsimp at hz
          subst y
          exact ⟨Bundle.TotalSpace.mk' (F × F) x (v, w), rfl⟩
  have hdiag_meas : MeasurableEmbedding diag :=
    hdiag_emb.measurableEmbedding hdiag_range
  have hprod :
      AEMeasurable
        (fun x : X ↦
          (HilbertBundleSectionOnSurface.toTotalSpace (F := F) s x,
            HilbertBundleSectionOnSurface.toTotalSpace (F := F) t x)) μ :=
    hs.prodMk ht
  have hcomp :
      AEMeasurable (diag ∘ hilbertBundleSectionPairTotalSpace (F := F) s t) μ := by
    refine hprod.congr ?_
    filter_upwards [] with x
    rfl
  exact hdiag_meas.aemeasurable_comp_iff.1 hcomp

/--
%%handwave
name:
  Fiberwise addition is continuous
statement:
  The map from the fiberwise product bundle to the original vector bundle
  which sends a pair of vectors in the same fiber to their sum is continuous.
proof:
  In a local trivialization, the map is the ordinary addition map on the
  model normed vector space.
-/
theorem hilbertBundleSection_totalSpace_add_continuous
    {X F : Type} [TopologicalSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, Module ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V] :
    Continuous
      (fun p : Bundle.TotalSpace (F × F) (V ×ᵇ V) ↦
        (Bundle.TotalSpace.mk' F p.1 (p.2.1 + p.2.2) :
          Bundle.TotalSpace F V)) := by
  rw [continuous_iff_continuousAt]
  intro p
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨?_, ?_⟩
  · exact (FiberBundle.continuous_proj (F × F) (V ×ᵇ V)).continuousAt
  · set e := trivializationAt F V p.1
    set ep := (e.prod e :
      Bundle.Trivialization (F × F)
        (Bundle.TotalSpace.proj (F := F × F) (E := V ×ᵇ V)))
    have hpbase : p.1 ∈ e.baseSet := by
      simpa [e] using FiberBundle.mem_baseSet_trivializationAt' (F := F) (E := V) p.1
    have hpbase_prod : p.1 ∈ ep.baseSet := by
      simpa [ep] using And.intro hpbase hpbase
    have hcoord : ContinuousAt (fun q : Bundle.TotalSpace (F × F) (V ×ᵇ V) ↦ (ep q).2) p := by
      have hid : ContinuousAt
          (fun q : Bundle.TotalSpace (F × F) (V ×ᵇ V) ↦ q) p := continuousAt_id
      rw [FiberBundle.continuousAt_totalSpace] at hid
      simpa [ep] using hid.2
    refine (hcoord.fst.add hcoord.snd).congr_of_eventuallyEq ?_
    have hbase : ∀ᶠ q : Bundle.TotalSpace (F × F) (V ×ᵇ V) in 𝓝 p,
        q.1 ∈ e.baseSet :=
      (FiberBundle.continuous_proj (F × F) (V ×ᵇ V)).continuousAt
        (e.open_baseSet.mem_nhds hpbase)
    filter_upwards [hbase] with q hq
    simpa [ep] using (e.linear ℝ hq).map_add q.2.1 q.2.2

/--
%%handwave
name:
  Fiberwise sums of measurable sections are measurable
statement:
  In a continuous real vector bundle, the fiberwise sum of two almost
  everywhere Borel measurable sections is again almost everywhere Borel
  measurable.
proof:
  The fiberwise pair of the two sections is measurable as a section of the
  fiberwise product bundle, and fiberwise addition is a continuous map from
  that product bundle to the original bundle.
-/
theorem hilbertBundleSection_aemeasurable_add
    {X F : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    [SecondCountableTopology (Bundle.TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, Module ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V]
    (μ : Measure X) {s t : HilbertBundleSectionOnSurface X V}
    (hs : AEMeasurable
      (HilbertBundleSectionOnSurface.toTotalSpace (F := F) s) μ)
    (ht : AEMeasurable
      (HilbertBundleSectionOnSurface.toTotalSpace (F := F) t) μ) :
    AEMeasurable
      (HilbertBundleSectionOnSurface.toTotalSpace (F := F) (s + t)) μ := by
  have hpair : AEMeasurable (hilbertBundleSectionPairTotalSpace (F := F) s t) μ :=
    hilbertBundleSection_aemeasurable_pair (F := F) μ hs ht
  have hcomp :
      AEMeasurable
        ((fun p : Bundle.TotalSpace (F × F) (V ×ᵇ V) ↦
            (Bundle.TotalSpace.mk' F p.1 (p.2.1 + p.2.2) :
              Bundle.TotalSpace F V)) ∘
          hilbertBundleSectionPairTotalSpace (F := F) s t) μ :=
    hilbertBundleSection_totalSpace_add_continuous
      (X := X) (F := F) (V := V) |>.aemeasurable.comp_aemeasurable hpair
  simpa [Function.comp_def, hilbertBundleSectionPairTotalSpace,
    HilbertBundleSectionOnSurface.toTotalSpace] using hcomp

/--
%%handwave
name:
  Fiberwise negatives of measurable sections are measurable
statement:
  In a continuous real vector bundle, the fiberwise negative of an almost
  everywhere Borel measurable section is again almost everywhere Borel
  measurable.
proof:
  Compose the measurable total-space section with continuous fiberwise negation.
-/
theorem hilbertBundleSection_aemeasurable_neg
    {X F : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, Module ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V]
    (μ : Measure X) {s : HilbertBundleSectionOnSurface X V}
    (hs : AEMeasurable
      (HilbertBundleSectionOnSurface.toTotalSpace (F := F) s) μ) :
    AEMeasurable
      (HilbertBundleSectionOnSurface.toTotalSpace (F := F) (-s)) μ := by
  let negTotal : Bundle.TotalSpace F V → Bundle.TotalSpace F V :=
    fun p ↦ ⟨p.1, -p.2⟩
  have hneg_cont : Continuous negTotal := by
    rw [continuous_iff_continuousAt]
    intro p
    rw [FiberBundle.continuousAt_totalSpace]
    refine ⟨?_, ?_⟩
    · exact (FiberBundle.continuous_proj F V).continuousAt
    · set e := trivializationAt F V p.1
      have hpbase : p.1 ∈ e.baseSet := by
        simpa [e] using FiberBundle.mem_baseSet_trivializationAt' (F := F) (E := V) p.1
      have hcoord : ContinuousAt (fun q : Bundle.TotalSpace F V ↦ (e q).2) p := by
        have hid : ContinuousAt (fun q : Bundle.TotalSpace F V ↦ q) p := continuousAt_id
        rw [FiberBundle.continuousAt_totalSpace] at hid
        simpa [e] using hid.2
      refine hcoord.neg.congr_of_eventuallyEq ?_
      have hbase : ∀ᶠ q : Bundle.TotalSpace F V in 𝓝 p, q.1 ∈ e.baseSet :=
        (FiberBundle.continuous_proj F V).continuousAt (e.open_baseSet.mem_nhds hpbase)
      filter_upwards [hbase] with q hq
      simpa [negTotal] using (e.linear ℝ hq).map_neg q.2
  have hcomp :
      AEMeasurable
        (negTotal ∘ HilbertBundleSectionOnSurface.toTotalSpace (F := F) s) μ :=
    hneg_cont.aemeasurable.comp_aemeasurable hs
  simpa [negTotal, Function.comp_def, HilbertBundleSectionOnSurface.toTotalSpace] using hcomp

/--
%%handwave
name:
  Fiberwise scalar multiples of measurable sections are measurable
statement:
  In a continuous real vector bundle, multiplying an almost everywhere Borel
  measurable section by a fixed scalar again gives an almost everywhere Borel
  measurable section.
proof:
  Compose the section with continuous fiberwise multiplication by the fixed scalar.
-/
theorem hilbertBundleSection_aemeasurable_smul
    {X F : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, Module ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V]
    (μ : Measure X) (c : ℝ) {s : HilbertBundleSectionOnSurface X V}
    (hs : AEMeasurable
      (HilbertBundleSectionOnSurface.toTotalSpace (F := F) s) μ) :
    AEMeasurable
      (HilbertBundleSectionOnSurface.toTotalSpace (F := F) (c • s)) μ := by
  let smulTotal : Bundle.TotalSpace F V → Bundle.TotalSpace F V :=
    fun p ↦ ⟨p.1, c • p.2⟩
  have hsmul_cont : Continuous smulTotal := by
    rw [continuous_iff_continuousAt]
    intro p
    rw [FiberBundle.continuousAt_totalSpace]
    refine ⟨?_, ?_⟩
    · exact (FiberBundle.continuous_proj F V).continuousAt
    · set e := trivializationAt F V p.1
      have hpbase : p.1 ∈ e.baseSet := by
        simpa [e] using FiberBundle.mem_baseSet_trivializationAt' (F := F) (E := V) p.1
      have hcoord : ContinuousAt (fun q : Bundle.TotalSpace F V ↦ (e q).2) p := by
        have hid : ContinuousAt (fun q : Bundle.TotalSpace F V ↦ q) p := continuousAt_id
        rw [FiberBundle.continuousAt_totalSpace] at hid
        simpa [e] using hid.2
      refine
        (show ContinuousAt (fun q : Bundle.TotalSpace F V ↦ c • (e q).2) p from
          continuousAt_const.smul hcoord).congr_of_eventuallyEq ?_
      have hbase : ∀ᶠ q : Bundle.TotalSpace F V in 𝓝 p, q.1 ∈ e.baseSet :=
        (FiberBundle.continuous_proj F V).continuousAt (e.open_baseSet.mem_nhds hpbase)
      filter_upwards [hbase] with q hq
      simpa [smulTotal] using (e.linear ℝ hq).map_smul c q.2
  have hcomp :
      AEMeasurable
        (smulTotal ∘ HilbertBundleSectionOnSurface.toTotalSpace (F := F) s) μ :=
    hsmul_cont.aemeasurable.comp_aemeasurable hs
  simpa [smulTotal, Function.comp_def, HilbertBundleSectionOnSurface.toTotalSpace] using hcomp

/--
%%handwave
name:
  Fiberwise square norm is measurable along measurable sections
statement:
  In a continuous Hilbert bundle, the fiberwise squared norm of an almost
  everywhere Borel measurable section is almost everywhere Borel measurable.
proof:
  The bundle metric is continuous on the total space, hence its diagonal
  restricts to a Borel function along any almost everywhere Borel measurable
  section.
-/
theorem hilbertBundleSection_aemeasurable_normSq
    {H X F : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold I 1 X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
    (G : HilbertBundleGeometry X F V)
    (hG_inner : ∀ (x : X) (v w : V x), G.fiberInner x v w = inner ℝ v w)
    (μ : Measure X) {s : HilbertBundleSectionOnSurface X V}
    (hs : AEMeasurable
      (HilbertBundleSectionOnSurface.toTotalSpace (F := F) s) μ) :
    AEMeasurable (fun x : X ↦ G.fiberNormSq x (s x)) μ := by
  have hcont_inner :
      Continuous (fun p : Bundle.TotalSpace F V ↦ inner ℝ p.2 p.2) := by
    simpa using
      (Continuous.inner_bundle
        (M := Bundle.TotalSpace F V) (B := X) (F := F) (E := V)
        (b := fun p : Bundle.TotalSpace F V ↦ p.1)
        (v := fun p : Bundle.TotalSpace F V ↦ p.2)
        (w := fun p : Bundle.TotalSpace F V ↦ p.2)
        (by simpa using (continuous_id : Continuous (fun p : Bundle.TotalSpace F V ↦ p)))
        (by simpa using (continuous_id : Continuous (fun p : Bundle.TotalSpace F V ↦ p))))
  have hcomp :
      AEMeasurable
        ((fun p : Bundle.TotalSpace F V ↦ inner ℝ p.2 p.2) ∘
          HilbertBundleSectionOnSurface.toTotalSpace (F := F) s) μ :=
    hcont_inner.aemeasurable.comp_aemeasurable hs
  refine hcomp.congr ?_
  filter_upwards [] with x
  change inner ℝ (s x) (s x) = G.fiberNormSq x (s x)
  rw [G.fiberNormSq_eq_inner, hG_inner]

/--
%%handwave
name:
  Fiberwise inner products of measurable sections are measurable
statement:
  In a continuous Hilbert bundle, the pointwise inner product of two almost
  everywhere Borel measurable sections is almost everywhere Borel measurable.
proof:
  Pair the two measurable total-space sections and then apply the continuous fiberwise inner product.
-/
theorem hilbertBundleSection_aemeasurable_inner
    {X F : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    [SecondCountableTopology (Bundle.TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
    (μ : Measure X) {s t : HilbertBundleSectionOnSurface X V}
    (hs : AEMeasurable
      (HilbertBundleSectionOnSurface.toTotalSpace (F := F) s) μ)
    (ht : AEMeasurable
      (HilbertBundleSectionOnSurface.toTotalSpace (F := F) t) μ) :
    AEMeasurable (fun x : X ↦ inner ℝ (s x) (t x)) μ := by
  have hpair : AEMeasurable (hilbertBundleSectionPairTotalSpace (F := F) s t) μ :=
    hilbertBundleSection_aemeasurable_pair (F := F) μ hs ht
  let diag :
      Bundle.TotalSpace (F × F) (V ×ᵇ V) →
        Bundle.TotalSpace F V × Bundle.TotalSpace F V :=
    fun p ↦
      ((Bundle.TotalSpace.mk' F p.1 p.2.1 : Bundle.TotalSpace F V),
        (Bundle.TotalSpace.mk' F p.1 p.2.2 : Bundle.TotalSpace F V))
  have hdiag_inj : Function.Injective diag := by
    intro p q hpq
    rcases p with ⟨x, v, w⟩
    rcases q with ⟨y, v', w'⟩
    simp [diag] at hpq ⊢
    rcases hpq with ⟨⟨hxy, hv⟩, ⟨_, hw⟩⟩
    subst y
    simpa using And.intro hv hw
  have hdiag_emb : Topology.IsEmbedding diag :=
    ⟨FiberBundle.Prod.isInducing_diag F V F V, hdiag_inj⟩
  have hdiag_cont : Continuous diag := hdiag_emb.continuous
  have hleft :
      Continuous
        (fun p : Bundle.TotalSpace (F × F) (V ×ᵇ V) ↦
          (Bundle.TotalSpace.mk' F p.1 p.2.1 : Bundle.TotalSpace F V)) := by
    simpa [diag] using (continuous_fst.comp hdiag_cont)
  have hright :
      Continuous
        (fun p : Bundle.TotalSpace (F × F) (V ×ᵇ V) ↦
          (Bundle.TotalSpace.mk' F p.1 p.2.2 : Bundle.TotalSpace F V)) := by
    simpa [diag] using (continuous_snd.comp hdiag_cont)
  have hinner_cont :
      Continuous
        (fun p : Bundle.TotalSpace (F × F) (V ×ᵇ V) ↦
          inner ℝ p.2.1 p.2.2) := by
    simpa using
      (Continuous.inner_bundle
        (M := Bundle.TotalSpace (F × F) (V ×ᵇ V)) (B := X) (F := F) (E := V)
        (b := fun p : Bundle.TotalSpace (F × F) (V ×ᵇ V) ↦ p.1)
        (v := fun p : Bundle.TotalSpace (F × F) (V ×ᵇ V) ↦ p.2.1)
        (w := fun p : Bundle.TotalSpace (F × F) (V ×ᵇ V) ↦ p.2.2)
        hleft hright)
  have hcomp :
      AEMeasurable
        ((fun p : Bundle.TotalSpace (F × F) (V ×ᵇ V) ↦
            inner ℝ p.2.1 p.2.2) ∘
          hilbertBundleSectionPairTotalSpace (F := F) s t) μ :=
    hinner_cont.aemeasurable.comp_aemeasurable hpair
  simpa [Function.comp_def, hilbertBundleSectionPairTotalSpace] using hcomp

/--
%%handwave
name:
  Sums of square-integrable sections are square-integrable
statement:
  The pointwise sum of two square-integrable sections of a continuous Hilbert
  bundle is square-integrable.
proof:
  The sum section is measurable.  Its squared norm is bounded by twice the sum of the two squared norms, which is integrable.
-/
theorem hilbertBundleSectionMemL2_add
    {H X F : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    [SecondCountableTopology (Bundle.TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
    (G : HilbertBundleGeometry X F V)
    (hG_inner : ∀ (x : X) (v w : V x), G.fiberInner x v w = inner ℝ v w)
    (μ : Measure X) {s t : HilbertBundleSectionOnSurface X V}
    (hs : HilbertBundleSectionMemL2 G μ s)
    (ht : HilbertBundleSectionMemL2 G μ t) :
    HilbertBundleSectionMemL2 G μ (s + t) := by
  have hG_norm : ∀ (x : X) (v : V x), G.fiberNormSq x v = ‖v‖ ^ 2 := by
    intro x v
    rw [G.fiberNormSq_eq_inner, hG_inner]
    exact real_inner_self_eq_norm_sq v
  refine ⟨?_, ?_⟩
  · exact hilbertBundleSection_aemeasurable_add (F := F) μ hs.aemeasurable ht.aemeasurable
  · have hsm : AEMeasurable
        (HilbertBundleSectionOnSurface.toTotalSpace (F := F) (s + t)) μ :=
      hilbertBundleSection_aemeasurable_add (F := F) μ hs.aemeasurable ht.aemeasurable
    have hadd_meas :
        AEMeasurable (fun x : X ↦ G.fiberNormSq x ((s + t) x)) μ :=
      hilbertBundleSection_aemeasurable_normSq (I := I) (G := G) hG_inner μ hsm
    have hs_norm : Integrable (fun x : X ↦ ‖s x‖ ^ 2) μ := by
      refine hs.integrable_normSq.congr ?_
      filter_upwards [] with x
      rw [hG_norm]
    have ht_norm : Integrable (fun x : X ↦ ‖t x‖ ^ 2) μ := by
      refine ht.integrable_normSq.congr ?_
      filter_upwards [] with x
      rw [hG_norm]
    have hbound :
        Integrable (fun x : X ↦ 2 * ‖s x‖ ^ 2 + 2 * ‖t x‖ ^ 2) μ :=
      (hs_norm.const_mul (2 : ℝ)).add (ht_norm.const_mul (2 : ℝ))
    refine Integrable.mono' hbound hadd_meas.aestronglyMeasurable ?_
    filter_upwards [] with x
    rw [hG_norm, Real.norm_of_nonneg (sq_nonneg _)]
    calc
      ‖(s + t) x‖ ^ 2 = ‖s x + t x‖ ^ 2 := rfl
      _ ≤ (‖s x‖ + ‖t x‖) ^ 2 := by
        exact (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).2
          (norm_add_le _ _)
      _ ≤ 2 * (‖s x‖ ^ 2 + ‖t x‖ ^ 2) := by
        simpa using (add_sq_le (a := ‖s x‖) (b := ‖t x‖))
      _ = 2 * ‖s x‖ ^ 2 + 2 * ‖t x‖ ^ 2 := by ring

/--
%%handwave
name:
  Negatives of square-integrable sections are square-integrable
statement:
  The pointwise negative of a square-integrable section of a continuous
  Hilbert bundle is square-integrable.
proof:
  Negation preserves measurability and the fiberwise squared norm, hence preserves square-integrability.
-/
theorem hilbertBundleSectionMemL2_neg
    {H X F : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold I 1 X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
    (G : HilbertBundleGeometry X F V)
    (hG_inner : ∀ (x : X) (v : V x), G.fiberNormSq x v = ‖v‖ ^ 2)
    (μ : Measure X) {s : HilbertBundleSectionOnSurface X V}
    (hs : HilbertBundleSectionMemL2 G μ s) :
    HilbertBundleSectionMemL2 G μ (-s) := by
  refine ⟨?_, ?_⟩
  · exact hilbertBundleSection_aemeasurable_neg (F := F) μ hs.aemeasurable
  · refine hs.integrable_normSq.congr ?_
    filter_upwards [] with x
    rw [hG_inner x (s x), hG_inner x ((-s) x)]
    simp

/--
%%handwave
name:
  Scalar multiples of square-integrable sections are square-integrable
statement:
  Multiplying a square-integrable section of a continuous Hilbert bundle by a
  fixed real scalar gives another square-integrable section.
proof:
  Scalar multiplication preserves measurability and multiplies the fiberwise squared norm by the constant square of the scalar.
-/
theorem hilbertBundleSectionMemL2_smul
    {H X F : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold I 1 X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
    (G : HilbertBundleGeometry X F V)
    (hG_inner : ∀ (x : X) (v w : V x), G.fiberInner x v w = inner ℝ v w)
    (μ : Measure X) (c : ℝ) {s : HilbertBundleSectionOnSurface X V}
    (hs : HilbertBundleSectionMemL2 G μ s) :
    HilbertBundleSectionMemL2 G μ (c • s) := by
  have hG_norm : ∀ (x : X) (v : V x), G.fiberNormSq x v = ‖v‖ ^ 2 := by
    intro x v
    rw [G.fiberNormSq_eq_inner, hG_inner]
    exact real_inner_self_eq_norm_sq v
  refine ⟨?_, ?_⟩
  · exact hilbertBundleSection_aemeasurable_smul (F := F) μ c hs.aemeasurable
  · have hbound :
        Integrable (fun x : X ↦ c ^ 2 * G.fiberNormSq x (s x)) μ :=
      hs.integrable_normSq.const_mul (c ^ 2)
    refine hbound.congr ?_
    filter_upwards [] with x
    rw [hG_norm x ((c • s) x), hG_norm x (s x)]
    simp [Pi.smul_apply, norm_smul, Real.norm_eq_abs, sq]
    ring_nf
    rw [sq_abs]
    ring

/--
%%handwave
name:
  Natural multiples of square-integrable sections are square-integrable
statement:
  A natural multiple of a square-integrable section of a continuous Hilbert
  bundle is square-integrable.
proof:
  Regard multiplication by a natural number as fiberwise scalar multiplication and apply scalar stability.
-/
theorem hilbertBundleSectionMemL2_nsmul
    {H X F : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    [SecondCountableTopology (Bundle.TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
    (G : HilbertBundleGeometry X F V)
    (hG_inner : ∀ (x : X) (v w : V x), G.fiberInner x v w = inner ℝ v w)
    (μ : Measure X) (n : ℕ) {s : HilbertBundleSectionOnSurface X V}
    (hs : HilbertBundleSectionMemL2 G μ s) :
    HilbertBundleSectionMemL2 G μ (n • s) := by
  induction n with
  | zero =>
      simpa using hilbertBundleSectionMemL2_zero (I := I) (G := G) hG_inner μ
  | succ n ih =>
      simpa [Nat.succ_eq_add_one, succ_nsmul] using
        hilbertBundleSectionMemL2_add (I := I) (G := G) hG_inner μ ih hs

/--
%%handwave
name:
  Integer multiples of square-integrable sections are square-integrable
statement:
  An integer multiple of a square-integrable section of a continuous Hilbert
  bundle is square-integrable.
proof:
  Regard multiplication by an integer as fiberwise real scalar multiplication and apply scalar stability.
-/
theorem hilbertBundleSectionMemL2_zsmul
    {H X F : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    [SecondCountableTopology (Bundle.TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
    (G : HilbertBundleGeometry X F V)
    (hG_inner : ∀ (x : X) (v w : V x), G.fiberInner x v w = inner ℝ v w)
    (μ : Measure X) (n : ℤ) {s : HilbertBundleSectionOnSurface X V}
    (hs : HilbertBundleSectionMemL2 G μ s) :
    HilbertBundleSectionMemL2 G μ (n • s) := by
  have hG_norm : ∀ (x : X) (v : V x), G.fiberNormSq x v = ‖v‖ ^ 2 := by
    intro x v
    rw [G.fiberNormSq_eq_inner, hG_inner]
    exact real_inner_self_eq_norm_sq v
  cases n with
  | ofNat n =>
      simpa using hilbertBundleSectionMemL2_nsmul (I := I) (G := G) hG_inner μ n hs
  | negSucc n =>
      simpa using
        hilbertBundleSectionMemL2_neg (I := I) (G := G) hG_norm μ
          (hilbertBundleSectionMemL2_nsmul (I := I) (G := G) hG_inner μ (n + 1) hs)

/--
%%handwave
name:
  Additive group structure on \(L^2\)-sections of a Hilbert bundle
statement:
  The \(L^2\)-sections of a continuous Hilbert bundle form an additive
  commutative group under pointwise operations.
proof:
  Pointwise operations preserve square-integrability and almost-everywhere
  equality is compatible with these operations, so the additive group
  structure descends from representatives to equivalence classes.
-/
theorem l2HilbertBundle_admits_add_comm_group
    {H X F : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    [SecondCountableTopology (Bundle.TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
    (G : HilbertBundleGeometry X F V)
    (hG_inner : ∀ (x : X) (v w : V x), G.fiberInner x v w = inner ℝ v w)
    (μ : Measure X) :
    Nonempty (AddCommGroup (L2HilbertBundle G μ)) := by
  have hG_norm : ∀ (x : X) (v : V x), G.fiberNormSq x v = ‖v‖ ^ 2 := by
    intro x v
    rw [G.fiberNormSq_eq_inner, hG_inner]
    exact real_inner_self_eq_norm_sq v
  let Rep := SquareIntegrableHilbertBundleSection G μ
  let Q := L2HilbertBundle G μ
  letI : Zero Rep := {
    zero := ⟨0, hilbertBundleSectionMemL2_zero (I := I) (G := G) hG_inner μ⟩ }
  letI : Add Rep := {
    add := fun s t ↦
      ⟨s.toSection + t.toSection,
        hilbertBundleSectionMemL2_add (I := I) (G := G) hG_inner μ s.memL2 t.memL2⟩ }
  letI : Neg Rep := {
    neg := fun s ↦
      ⟨-s.toSection,
        hilbertBundleSectionMemL2_neg (I := I) (G := G) hG_norm μ s.memL2⟩ }
  letI : Sub Rep := {
    sub := fun s t ↦ s + -t }
  letI : SMul ℕ Rep := {
    smul := fun n s ↦
      ⟨n • s.toSection,
        hilbertBundleSectionMemL2_nsmul (I := I) (G := G) hG_inner μ n s.memL2⟩ }
  letI : SMul ℤ Rep := {
    smul := fun n s ↦
      ⟨n • s.toSection,
        hilbertBundleSectionMemL2_zsmul (I := I) (G := G) hG_inner μ n s.memL2⟩ }
  have coe_zero : (0 : Rep).toSection = 0 := rfl
  have coe_add : ∀ s t : Rep, (s + t).toSection = s.toSection + t.toSection := fun _ _ ↦ rfl
  have coe_neg : ∀ s : Rep, (-s).toSection = -s.toSection := fun _ ↦ rfl
  have coe_sub : ∀ s t : Rep, (s - t).toSection = s.toSection - t.toSection := by
    intro s t
    change (s + -t).toSection = s.toSection - t.toSection
    rw [coe_add, coe_neg]
    simp [sub_eq_add_neg]
  have coe_nsmul : ∀ (s : Rep) (n : ℕ), (n • s).toSection = n • s.toSection :=
    fun _ _ ↦ rfl
  have coe_zsmul : ∀ (s : Rep) (n : ℤ), (n • s).toSection = n • s.toSection :=
    fun _ _ ↦ rfl
  have toSection_injective : Function.Injective (fun s : Rep ↦ s.toSection) := by
    intro s t h
    exact SquareIntegrableHilbertBundleSection.ext (fun x ↦ congrFun h x)
  letI : AddCommGroup Rep :=
    Function.Injective.addCommGroup (fun s : Rep ↦ s.toSection)
      toSection_injective coe_zero coe_add coe_neg coe_sub coe_nsmul coe_zsmul
  have ae_add {s s' t t' : Rep}
      (hs : SquareIntegrableHilbertBundleSection.AeEq s s')
      (ht : SquareIntegrableHilbertBundleSection.AeEq t t') :
      SquareIntegrableHilbertBundleSection.AeEq (s + t) (s' + t') := by
    filter_upwards [hs, ht] with x hsx htx
    change s.toSection x + t.toSection x = s'.toSection x + t'.toSection x
    rw [hsx, htx]
  have ae_neg {s s' : Rep}
      (hs : SquareIntegrableHilbertBundleSection.AeEq s s') :
      SquareIntegrableHilbertBundleSection.AeEq (-s) (-s') := by
    filter_upwards [hs] with x hsx
    change -s.toSection x = -s'.toSection x
    rw [hsx]
  have ae_sub {s s' t t' : Rep}
      (hs : SquareIntegrableHilbertBundleSection.AeEq s s')
      (ht : SquareIntegrableHilbertBundleSection.AeEq t t') :
      SquareIntegrableHilbertBundleSection.AeEq (s - t) (s' - t') := by
    exact ae_add hs (ae_neg ht)
  have ae_nsmul {s s' : Rep} (n : ℕ)
      (hs : SquareIntegrableHilbertBundleSection.AeEq s s') :
      SquareIntegrableHilbertBundleSection.AeEq (n • s) (n • s') := by
    filter_upwards [hs] with x hsx
    change n • s.toSection x = n • s'.toSection x
    rw [hsx]
  have ae_zsmul {s s' : Rep} (n : ℤ)
      (hs : SquareIntegrableHilbertBundleSection.AeEq s s') :
      SquareIntegrableHilbertBundleSection.AeEq (n • s) (n • s') := by
    filter_upwards [hs] with x hsx
    change n • s.toSection x = n • s'.toSection x
    rw [hsx]
  letI : Zero (L2HilbertBundle G μ) := {
    zero := Quotient.mk (SquareIntegrableHilbertBundleSection.aeSetoid (G := G) (μ := μ)) 0 }
  letI : Add (L2HilbertBundle G μ) := {
    add := fun a b ↦
      Quotient.liftOn₂ a b
        (fun s t ↦ Quotient.mk
          (SquareIntegrableHilbertBundleSection.aeSetoid (G := G) (μ := μ)) (s + t))
        (by
          intro s t s' t' hs ht
          exact Quotient.sound (ae_add hs ht)) }
  letI : Neg (L2HilbertBundle G μ) := {
    neg := fun a ↦
      Quotient.liftOn a
        (fun s ↦ Quotient.mk
          (SquareIntegrableHilbertBundleSection.aeSetoid (G := G) (μ := μ)) (-s))
        (by
          intro s t hs
          exact Quotient.sound (ae_neg hs)) }
  letI : Sub (L2HilbertBundle G μ) := {
    sub := fun a b ↦ a + -b }
  letI : SMul ℕ (L2HilbertBundle G μ) := {
    smul := fun n a ↦
      Quotient.liftOn a
        (fun s ↦ Quotient.mk
          (SquareIntegrableHilbertBundleSection.aeSetoid (G := G) (μ := μ)) (n • s))
        (by
          intro s t hs
          exact Quotient.sound (ae_nsmul n hs)) }
  letI : SMul ℤ (L2HilbertBundle G μ) := {
    smul := fun n a ↦
      Quotient.liftOn a
        (fun s ↦ Quotient.mk
          (SquareIntegrableHilbertBundleSection.aeSetoid (G := G) (μ := μ)) (n • s))
        (by
          intro s t hs
          exact Quotient.sound (ae_zsmul n hs)) }
  have mk_surjective :
      Function.Surjective
        (fun s : Rep ↦
          (Quotient.mk (SquareIntegrableHilbertBundleSection.aeSetoid
            (G := G) (μ := μ)) s : L2HilbertBundle G μ)) :=
    Quotient.mk_surjective
  have mk_zero :
      (Quotient.mk (SquareIntegrableHilbertBundleSection.aeSetoid
          (G := G) (μ := μ)) (0 : Rep) : L2HilbertBundle G μ) =
        (0 : L2HilbertBundle G μ) :=
    rfl
  have mk_add : ∀ s t : Rep,
      (Quotient.mk (SquareIntegrableHilbertBundleSection.aeSetoid
          (G := G) (μ := μ)) (s + t) : L2HilbertBundle G μ) =
        (Quotient.mk (SquareIntegrableHilbertBundleSection.aeSetoid
          (G := G) (μ := μ)) s : L2HilbertBundle G μ) +
        (Quotient.mk (SquareIntegrableHilbertBundleSection.aeSetoid
          (G := G) (μ := μ)) t : L2HilbertBundle G μ) := by
    intro s t
    rfl
  have mk_neg : ∀ s : Rep,
      (Quotient.mk (SquareIntegrableHilbertBundleSection.aeSetoid
          (G := G) (μ := μ)) (-s) : L2HilbertBundle G μ) =
        -(Quotient.mk (SquareIntegrableHilbertBundleSection.aeSetoid
          (G := G) (μ := μ)) s : L2HilbertBundle G μ) := by
    intro s
    rfl
  have mk_sub : ∀ s t : Rep,
      (Quotient.mk (SquareIntegrableHilbertBundleSection.aeSetoid
          (G := G) (μ := μ)) (s - t) : L2HilbertBundle G μ) =
        (Quotient.mk (SquareIntegrableHilbertBundleSection.aeSetoid
          (G := G) (μ := μ)) s : L2HilbertBundle G μ) -
        (Quotient.mk (SquareIntegrableHilbertBundleSection.aeSetoid
          (G := G) (μ := μ)) t : L2HilbertBundle G μ) := by
    intro s t
    rfl
  have mk_nsmul : ∀ (s : Rep) (n : ℕ),
      (Quotient.mk (SquareIntegrableHilbertBundleSection.aeSetoid
          (G := G) (μ := μ)) (n • s) : L2HilbertBundle G μ) =
        n • (Quotient.mk (SquareIntegrableHilbertBundleSection.aeSetoid
          (G := G) (μ := μ)) s : L2HilbertBundle G μ) := by
    intro s n
    rfl
  have mk_zsmul : ∀ (s : Rep) (n : ℤ),
      (Quotient.mk (SquareIntegrableHilbertBundleSection.aeSetoid
          (G := G) (μ := μ)) (n • s) : L2HilbertBundle G μ) =
        n • (Quotient.mk (SquareIntegrableHilbertBundleSection.aeSetoid
          (G := G) (μ := μ)) s : L2HilbertBundle G μ) := by
    intro s n
    rfl
  exact ⟨Function.Surjective.addCommGroup
    (fun s : Rep ↦
      (Quotient.mk (SquareIntegrableHilbertBundleSection.aeSetoid
        (G := G) (μ := μ)) s : L2HilbertBundle G μ))
    mk_surjective mk_zero mk_add mk_neg mk_sub mk_nsmul mk_zsmul⟩

/--
%%handwave
name:
  Square \(L^2\)-norm of a bundle section
statement:
  The square \(L^2\)-norm of a square-integrable section is the integral over
  the base of the fiberwise square norm.
-/
noncomputable def squareIntegrableHilbertBundleSectionL2NormSq
    {X F : Type} [TopologicalSpace X] [MeasurableSpace X]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    (G : HilbertBundleGeometry X F V) (μ : Measure X)
    (s : SquareIntegrableHilbertBundleSection G μ) : ℝ :=
  ∫ x, G.fiberNormSq x (s.toSection x) ∂μ

/--
%%handwave
name:
  \(L^2\)-norm of a bundle section
statement:
  The \(L^2\)-norm of a square-integrable section is the square root of its
  integrated fiberwise square norm.
-/
noncomputable def squareIntegrableHilbertBundleSectionL2Norm
    {X F : Type} [TopologicalSpace X] [MeasurableSpace X]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    (G : HilbertBundleGeometry X F V) (μ : Measure X)
    (s : SquareIntegrableHilbertBundleSection G μ) : ℝ :=
  Real.sqrt (squareIntegrableHilbertBundleSectionL2NormSq G μ s)

/--
%%handwave
name:
  The \(L^2\)-norm depends only on the almost-everywhere class
statement:
  Almost-everywhere equal square-integrable sections have the same
  \(L^2\)-norm.
proof:
  Almost-everywhere equality makes the two fiberwise squared norms equal almost everywhere, so their integrals and square roots coincide.
-/
theorem squareIntegrableHilbertBundleSectionL2Norm_congr_ae
    {X F : Type} [TopologicalSpace X] [MeasurableSpace X]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    (G : HilbertBundleGeometry X F V) (μ : Measure X)
    {s t : SquareIntegrableHilbertBundleSection G μ}
    (hst : SquareIntegrableHilbertBundleSection.AeEq s t) :
    squareIntegrableHilbertBundleSectionL2Norm G μ s =
      squareIntegrableHilbertBundleSectionL2Norm G μ t := by
  apply congrArg Real.sqrt
  unfold squareIntegrableHilbertBundleSectionL2NormSq
  exact integral_congr_ae (hst.mono fun x hx ↦ by
    exact congrArg (fun v ↦ G.fiberNormSq x v) hx)

/--
%%handwave
name:
  The zero section has zero \(L^2\)-norm
statement:
  The \(L^2\)-norm of the zero section of a Hilbert bundle is zero.
proof:
  The fiber norm of the zero section is zero everywhere, so its squared norm integral and square root vanish.
-/
theorem squareIntegrableHilbertBundleSectionL2Norm_zero
    {H X F : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold I 1 X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
    (G : HilbertBundleGeometry X F V)
    (hG_inner : ∀ (x : X) (v w : V x), G.fiberInner x v w = inner ℝ v w)
    (μ : Measure X) :
    squareIntegrableHilbertBundleSectionL2Norm G μ
      ⟨0, hilbertBundleSectionMemL2_zero (I := I) (G := G) hG_inner μ⟩ = 0 := by
  unfold squareIntegrableHilbertBundleSectionL2Norm
  unfold squareIntegrableHilbertBundleSectionL2NormSq
  have hzero :
      (fun x : X ↦ G.fiberNormSq x ((0 : HilbertBundleSectionOnSurface X V) x)) =
        fun _ : X ↦ (0 : ℝ) := by
    funext x
    rw [G.fiberNormSq_eq_inner, hG_inner]
    simp
  rw [hzero]
  simp

/--
%%handwave
name:
  Negation preserves the \(L^2\)-norm
statement:
  The \(L^2\)-norm of the negative of a square-integrable section is the same
  as the \(L^2\)-norm of the section.
proof:
  Fiberwise negation preserves the norm, hence it leaves the integrated square norm unchanged.
-/
theorem squareIntegrableHilbertBundleSectionL2Norm_neg
    {H X F : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold I 1 X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
    (G : HilbertBundleGeometry X F V)
    (hG_norm : ∀ (x : X) (v : V x), G.fiberNormSq x v = ‖v‖ ^ 2)
    (μ : Measure X) (s : SquareIntegrableHilbertBundleSection G μ) :
    squareIntegrableHilbertBundleSectionL2Norm G μ
      ⟨-s.toSection, hilbertBundleSectionMemL2_neg (I := I) (G := G) hG_norm μ s.memL2⟩ =
      squareIntegrableHilbertBundleSectionL2Norm G μ s := by
  apply congrArg Real.sqrt
  unfold squareIntegrableHilbertBundleSectionL2NormSq
  refine integral_congr_ae ?_
  filter_upwards [] with x
  rw [hG_norm x ((-s.toSection) x), hG_norm x (s.toSection x)]
  simp

/--
%%handwave
name:
  Scalar homogeneity of the \(L^2\)-norm
statement:
  The \(L^2\)-norm of a scalar multiple of a square-integrable Hilbert-bundle
  section is the absolute value of the scalar times the \(L^2\)-norm of the
  section.
proof:
  Pull the constant scalar square out of the integral and use that the square root of the scalar square is its absolute value.
-/
theorem squareIntegrableHilbertBundleSectionL2Norm_smul
    {H X F : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold I 1 X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
    (G : HilbertBundleGeometry X F V)
    (hG_inner : ∀ (x : X) (v w : V x), G.fiberInner x v w = inner ℝ v w)
    (μ : Measure X) (c : ℝ) (s : SquareIntegrableHilbertBundleSection G μ) :
    squareIntegrableHilbertBundleSectionL2Norm G μ
      ⟨c • s.toSection, hilbertBundleSectionMemL2_smul (I := I) (G := G) hG_inner μ c s.memL2⟩ =
      ‖c‖ * squareIntegrableHilbertBundleSectionL2Norm G μ s := by
  have hG_norm : ∀ (x : X) (v : V x), G.fiberNormSq x v = ‖v‖ ^ 2 := by
    intro x v
    rw [G.fiberNormSq_eq_inner, hG_inner]
    exact real_inner_self_eq_norm_sq v
  have hnonneg :
      0 ≤ ∫ x, G.fiberNormSq x (s.toSection x) ∂μ := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [] with x
    rw [hG_norm x (s.toSection x)]
    exact sq_nonneg _
  have hscale :
      ∫ x, G.fiberNormSq x ((c • s.toSection) x) ∂μ =
        c ^ 2 * ∫ x, G.fiberNormSq x (s.toSection x) ∂μ := by
    calc
      ∫ x, G.fiberNormSq x ((c • s.toSection) x) ∂μ =
          ∫ x, c ^ 2 * G.fiberNormSq x (s.toSection x) ∂μ := by
            refine integral_congr_ae ?_
            filter_upwards [] with x
            rw [hG_norm x ((c • s.toSection) x), hG_norm x (s.toSection x)]
            simp [Pi.smul_apply, norm_smul, Real.norm_eq_abs, sq]
            ring_nf
            rw [sq_abs]
            ring
      _ = c ^ 2 * ∫ x, G.fiberNormSq x (s.toSection x) ∂μ := by
            exact integral_const_mul (c ^ 2) (fun x ↦ G.fiberNormSq x (s.toSection x))
  unfold squareIntegrableHilbertBundleSectionL2Norm
  unfold squareIntegrableHilbertBundleSectionL2NormSq
  rw [hscale, Real.sqrt_mul (sq_nonneg c),
    Real.sqrt_sq_eq_abs, Real.norm_eq_abs]

/--
%%handwave
name:
  Bundle \(L^2\)-norm as a scalar \(L^2\)-norm
statement:
  The \(L^2\)-norm of a square-integrable Hilbert-bundle section is the scalar
  \(L^2\)-norm of its pointwise fiber norm.
proof:
  Rewrite the fiberwise square norm as the square of the ordinary norm and compare the defining integral formulas for the two real norms.
-/
theorem squareIntegrableHilbertBundleSectionL2Norm_eq_lpNorm_norm
    {H X F : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold I 1 X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
    (G : HilbertBundleGeometry X F V)
    (hG_inner : ∀ (x : X) (v w : V x), G.fiberInner x v w = inner ℝ v w)
    (μ : Measure X) (s : SquareIntegrableHilbertBundleSection G μ) :
    squareIntegrableHilbertBundleSectionL2Norm G μ s =
      lpNorm (fun x : X ↦ ‖s.toSection x‖) 2 μ := by
  have hG_norm : ∀ (x : X) (v : V x), G.fiberNormSq x v = ‖v‖ ^ 2 := by
    intro x v
    rw [G.fiberNormSq_eq_inner, hG_inner]
    exact real_inner_self_eq_norm_sq v
  have hnorm_ae :
      (fun x : X ↦ √(G.fiberNormSq x (s.toSection x))) =ᵐ[μ]
        fun x : X ↦ ‖s.toSection x‖ := by
    filter_upwards [] with x
    rw [hG_norm x (s.toSection x), Real.sqrt_sq (norm_nonneg _)]
  have hnorm_aestr :
      AEStronglyMeasurable (fun x : X ↦ ‖s.toSection x‖) μ := by
    have hsqrt_aestr :
        AEStronglyMeasurable (fun x : X ↦ √(G.fiberNormSq x (s.toSection x))) μ :=
      (s.memL2.integrable_normSq.aestronglyMeasurable.aemeasurable.sqrt).aestronglyMeasurable
    exact (aestronglyMeasurable_congr hnorm_ae).1 hsqrt_aestr
  unfold squareIntegrableHilbertBundleSectionL2Norm
  unfold squareIntegrableHilbertBundleSectionL2NormSq
  rw [lpNorm_eq_integral_norm_rpow_toReal (p := (2 : ℝ≥0∞))
    (by norm_num) (by norm_num) hnorm_aestr]
  have hint_eq :
      ∫ x, G.fiberNormSq x (s.toSection x) ∂μ =
        ∫ x, ‖(‖s.toSection x‖ : ℝ)‖ ^ (2 : ℝ≥0∞).toReal ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [] with x
    rw [hG_norm x (s.toSection x)]
    simp
  rw [hint_eq, Real.sqrt_eq_rpow]
  norm_num

/--
%%handwave
name:
  Pointwise norms of square-integrable sections are square-integrable
statement:
  The pointwise fiber norm of a square-integrable Hilbert-bundle section is a
  scalar \(L^2\)-function.
proof:
  Strong measurability follows from the measurable bundle section and continuity of the norm; integrability of its square is precisely the bundle square-integrability assumption.
-/
theorem squareIntegrableHilbertBundleSection_norm_memLp
    {H X F : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold I 1 X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
    (G : HilbertBundleGeometry X F V)
    (hG_inner : ∀ (x : X) (v w : V x), G.fiberInner x v w = inner ℝ v w)
    (μ : Measure X) (s : SquareIntegrableHilbertBundleSection G μ) :
    MemLp (fun x : X ↦ ‖s.toSection x‖) 2 μ := by
  have hG_norm : ∀ (x : X) (v : V x), G.fiberNormSq x v = ‖v‖ ^ 2 := by
    intro x v
    rw [G.fiberNormSq_eq_inner, hG_inner]
    exact real_inner_self_eq_norm_sq v
  have hnorm_ae :
      (fun x : X ↦ √(G.fiberNormSq x (s.toSection x))) =ᵐ[μ]
        fun x : X ↦ ‖s.toSection x‖ := by
    filter_upwards [] with x
    rw [hG_norm x (s.toSection x), Real.sqrt_sq (norm_nonneg _)]
  have hnorm_aestr :
      AEStronglyMeasurable (fun x : X ↦ ‖s.toSection x‖) μ := by
    have hsqrt_aestr :
        AEStronglyMeasurable
          (fun x : X ↦ √(G.fiberNormSq x (s.toSection x))) μ :=
      (s.memL2.integrable_normSq.aestronglyMeasurable.aemeasurable.sqrt).aestronglyMeasurable
    exact (aestronglyMeasurable_congr hnorm_ae).1 hsqrt_aestr
  have hnorm_sq_int :
      Integrable (fun x : X ↦ ‖s.toSection x‖ ^ 2) μ := by
    refine s.memL2.integrable_normSq.congr ?_
    filter_upwards [] with x
    rw [hG_norm x (s.toSection x)]
  exact (memLp_two_iff_integrable_sq hnorm_aestr).2 hnorm_sq_int

/--
%%handwave
name:
  Fiberwise inner products of \(L^2\)-sections are integrable
statement:
  The pointwise inner product of two square-integrable Hilbert-bundle sections
  is integrable.
proof:
  Its absolute value is bounded by the product of the two pointwise norms, and
  the product of two scalar \(L^2\)-functions is integrable by Hölder's
  inequality.
-/
theorem squareIntegrableHilbertBundleSection_inner_integrable
    {H X F : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    [SecondCountableTopology (Bundle.TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
    (G : HilbertBundleGeometry X F V)
    (hG_inner : ∀ (x : X) (v w : V x), G.fiberInner x v w = inner ℝ v w)
    (μ : Measure X) (s t : SquareIntegrableHilbertBundleSection G μ) :
    Integrable (fun x : X ↦ inner ℝ (s.toSection x) (t.toSection x)) μ := by
  have hinner_meas :
      AEMeasurable (fun x : X ↦ inner ℝ (s.toSection x) (t.toSection x)) μ :=
    hilbertBundleSection_aemeasurable_inner (F := F) μ
      s.memL2.aemeasurable t.memL2.aemeasurable
  have hs_norm : MemLp (fun x : X ↦ ‖s.toSection x‖) 2 μ :=
    squareIntegrableHilbertBundleSection_norm_memLp (I := I) (G := G) hG_inner μ s
  have ht_norm : MemLp (fun x : X ↦ ‖t.toSection x‖) 2 μ :=
    squareIntegrableHilbertBundleSection_norm_memLp (I := I) (G := G) hG_inner μ t
  haveI : ENNReal.HolderTriple (2 : ℝ≥0∞) (2 : ℝ≥0∞) 1 := by
    rw [ENNReal.holderTriple_iff]
    simpa using ENNReal.inv_two_add_inv_two
  have hprod :
      Integrable
        ((fun x : X ↦ ‖s.toSection x‖) *
          (fun x : X ↦ ‖t.toSection x‖)) μ :=
    hs_norm.integrable_mul ht_norm
  refine Integrable.mono' hprod hinner_meas.aestronglyMeasurable ?_
  filter_upwards [] with x
  change ‖inner ℝ (s.toSection x) (t.toSection x)‖ ≤
    ‖s.toSection x‖ * ‖t.toSection x‖
  exact norm_inner_le_norm _ _

/--
%%handwave
name:
  Triangle inequality for the \(L^2\)-norm of bundle sections
statement:
  The \(L^2\)-norm of the pointwise sum of two square-integrable Hilbert-bundle
  sections is bounded above by the sum of their \(L^2\)-norms.
proof:
  This is the Minkowski inequality for Hilbert-valued \(L^2\)-sections, applied
  fiberwise using the Hilbert norm and then integrated over the base.
-/
theorem squareIntegrableHilbertBundleSectionL2Norm_add_le
    {H X F : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    [SecondCountableTopology (Bundle.TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
    (G : HilbertBundleGeometry X F V)
    (hG_inner : ∀ (x : X) (v w : V x), G.fiberInner x v w = inner ℝ v w)
    (μ : Measure X) (s t : SquareIntegrableHilbertBundleSection G μ) :
    squareIntegrableHilbertBundleSectionL2Norm G μ
      ⟨s.toSection + t.toSection,
        hilbertBundleSectionMemL2_add (I := I) (G := G) hG_inner μ s.memL2 t.memL2⟩ ≤
      squareIntegrableHilbertBundleSectionL2Norm G μ s +
        squareIntegrableHilbertBundleSectionL2Norm G μ t := by
  have hG_norm : ∀ (x : X) (v : V x), G.fiberNormSq x v = ‖v‖ ^ 2 := by
    intro x v
    rw [G.fiberNormSq_eq_inner, hG_inner]
    exact real_inner_self_eq_norm_sq v
  have norm_memLp (r : SquareIntegrableHilbertBundleSection G μ) :
      MemLp (fun x : X ↦ ‖r.toSection x‖) 2 μ := by
    have hnorm_ae :
        (fun x : X ↦ √(G.fiberNormSq x (r.toSection x))) =ᵐ[μ]
          fun x : X ↦ ‖r.toSection x‖ := by
      filter_upwards [] with x
      rw [hG_norm x (r.toSection x), Real.sqrt_sq (norm_nonneg _)]
    have hnorm_aestr :
        AEStronglyMeasurable (fun x : X ↦ ‖r.toSection x‖) μ := by
      have hsqrt_aestr :
          AEStronglyMeasurable
            (fun x : X ↦ √(G.fiberNormSq x (r.toSection x))) μ :=
        (r.memL2.integrable_normSq.aestronglyMeasurable.aemeasurable.sqrt).aestronglyMeasurable
      exact (aestronglyMeasurable_congr hnorm_ae).1 hsqrt_aestr
    have hnorm_sq_int :
        Integrable (fun x : X ↦ ‖r.toSection x‖ ^ 2) μ := by
      refine r.memL2.integrable_normSq.congr ?_
      filter_upwards [] with x
      rw [hG_norm x (r.toSection x)]
    exact (memLp_two_iff_integrable_sq hnorm_aestr).2 hnorm_sq_int
  let u : SquareIntegrableHilbertBundleSection G μ :=
    ⟨s.toSection + t.toSection,
      hilbertBundleSectionMemL2_add (I := I) (G := G) hG_inner μ s.memL2 t.memL2⟩
  have hs_norm_memLp : MemLp (fun x : X ↦ ‖s.toSection x‖) 2 μ :=
    norm_memLp s
  have ht_norm_memLp : MemLp (fun x : X ↦ ‖t.toSection x‖) 2 μ :=
    norm_memLp t
  have hsum_norm_memLp :
      MemLp (fun x : X ↦ ‖s.toSection x‖ + ‖t.toSection x‖) 2 μ := by
    simpa [Pi.add_apply] using hs_norm_memLp.add ht_norm_memLp
  have hpointwise :
      ∀ x : X, ‖(fun y : X ↦ ‖u.toSection y‖) x‖ ≤
        (fun y : X ↦ ‖s.toSection y‖ + ‖t.toSection y‖) x := by
    intro x
    rw [Real.norm_of_nonneg (norm_nonneg (u.toSection x))]
    change ‖s.toSection x + t.toSection x‖ ≤ ‖s.toSection x‖ + ‖t.toSection x‖
    exact norm_add_le _ _
  calc
    squareIntegrableHilbertBundleSectionL2Norm G μ u =
        lpNorm (fun x : X ↦ ‖u.toSection x‖) 2 μ := by
          exact squareIntegrableHilbertBundleSectionL2Norm_eq_lpNorm_norm
            (I := I) (G := G) hG_inner μ u
    _ ≤ lpNorm (fun x : X ↦ ‖s.toSection x‖ + ‖t.toSection x‖) 2 μ := by
          exact lpNorm_mono_real (p := (2 : ℝ≥0∞)) (μ := μ)
            (f := fun x : X ↦ ‖u.toSection x‖)
            (g := fun x : X ↦ ‖s.toSection x‖ + ‖t.toSection x‖)
            hsum_norm_memLp hpointwise
    _ ≤ lpNorm (fun x : X ↦ ‖s.toSection x‖) 2 μ +
        lpNorm (fun x : X ↦ ‖t.toSection x‖) 2 μ := by
          simpa [Pi.add_apply] using
            lpNorm_add_le (p := (2 : ℝ≥0∞)) (μ := μ)
              (f := fun x : X ↦ ‖s.toSection x‖)
              (g := fun x : X ↦ ‖t.toSection x‖)
              hs_norm_memLp (by norm_num)
    _ = squareIntegrableHilbertBundleSectionL2Norm G μ s +
        squareIntegrableHilbertBundleSectionL2Norm G μ t := by
          rw [← squareIntegrableHilbertBundleSectionL2Norm_eq_lpNorm_norm
            (I := I) (G := G) hG_inner μ s,
            ← squareIntegrableHilbertBundleSectionL2Norm_eq_lpNorm_norm
            (I := I) (G := G) hG_inner μ t]

/--
%%handwave
name:
  Zero \(L^2\)-norm detects the zero almost-everywhere class
statement:
  A square-integrable Hilbert-bundle section has zero \(L^2\)-norm if and only
  if it vanishes almost everywhere.
proof:
  The fiberwise square norm is nonnegative, so an integral equal to zero forces
  the square norm to vanish almost everywhere.  Since each fiber norm is
  positive definite, the section itself vanishes almost everywhere.  The
  converse follows by replacing the section by the zero section under the
  integral.
-/
theorem squareIntegrableHilbertBundleSectionL2Norm_eq_zero_iff_ae_zero
    {H X F : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold I 1 X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
    (G : HilbertBundleGeometry X F V)
    (hG_inner : ∀ (x : X) (v w : V x), G.fiberInner x v w = inner ℝ v w)
    (μ : Measure X) (s : SquareIntegrableHilbertBundleSection G μ) :
    squareIntegrableHilbertBundleSectionL2Norm G μ s = 0 ↔
      SquareIntegrableHilbertBundleSection.AeEq s
        ⟨0, hilbertBundleSectionMemL2_zero (I := I) (G := G) hG_inner μ⟩ := by
  have hG_norm : ∀ (x : X) (v : V x), G.fiberNormSq x v = ‖v‖ ^ 2 := by
    intro x v
    rw [G.fiberNormSq_eq_inner, hG_inner]
    exact real_inner_self_eq_norm_sq v
  constructor
  · intro hnorm
    have hnonneg :
        0 ≤ᵐ[μ] fun x : X ↦ G.fiberNormSq x (s.toSection x) := by
      filter_upwards [] with x
      rw [hG_norm x (s.toSection x)]
      exact sq_nonneg _
    have hintegral_zero :
        ∫ x, G.fiberNormSq x (s.toSection x) ∂μ = 0 := by
      have hintegral_nonneg :
          0 ≤ ∫ x, G.fiberNormSq x (s.toSection x) ∂μ :=
        integral_nonneg_of_ae hnonneg
      unfold squareIntegrableHilbertBundleSectionL2Norm at hnorm
      exact (Real.sqrt_eq_zero hintegral_nonneg).1 hnorm
    have hsq_zero :
        (fun x : X ↦ G.fiberNormSq x (s.toSection x)) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae hnonneg s.memL2.integrable_normSq).1
        hintegral_zero
    filter_upwards [hsq_zero] with x hx
    rw [hG_norm x (s.toSection x)] at hx
    exact norm_eq_zero.1 (sq_eq_zero_iff.1 hx)
  · intro hzero
    exact (squareIntegrableHilbertBundleSectionL2Norm_congr_ae (G := G) μ hzero).trans
      (squareIntegrableHilbertBundleSectionL2Norm_zero (I := I) (G := G) hG_inner μ)

/--
%%handwave
name:
  Normed additive structure on \(L^2\)-sections of a Hilbert bundle
statement:
  Pointwise addition and scalar multiplication of representatives descend to
  \(L^2\)-sections modulo almost-everywhere equality, and the integrated
  square norm gives the resulting quotient a normed additive group structure.
proof:
  Addition, negation, and scalar multiplication are defined on
  representatives pointwise.  The continuous vector-bundle operations preserve
  almost-everywhere Borel measurability, and the Hilbert norm inequalities
  preserve square-integrability.  Almost-everywhere equality is a congruence
  for these operations, so they descend to the quotient.
-/
@[reducible]
noncomputable def l2HilbertBundleNormedAddCommGroup
    {H X F : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    [SecondCountableTopology (Bundle.TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
    (G : HilbertBundleGeometry X F V)
    (hG_inner : ∀ (x : X) (v w : V x), G.fiberInner x v w = inner ℝ v w)
    (μ : Measure X) :
    NormedAddCommGroup (L2HilbertBundle G μ) := by
  have hG_norm : ∀ (x : X) (v : V x), G.fiberNormSq x v = ‖v‖ ^ 2 := by
    intro x v
    rw [G.fiberNormSq_eq_inner, hG_inner]
    exact real_inner_self_eq_norm_sq v
  let Rep := SquareIntegrableHilbertBundleSection G μ
  let Q := L2HilbertBundle G μ
  letI : Zero Rep := {
    zero := ⟨0, hilbertBundleSectionMemL2_zero (I := I) (G := G) hG_inner μ⟩ }
  letI : Add Rep := {
    add := fun s t ↦
      ⟨s.toSection + t.toSection,
        hilbertBundleSectionMemL2_add (I := I) (G := G) hG_inner μ s.memL2 t.memL2⟩ }
  letI : Neg Rep := {
    neg := fun s ↦
      ⟨-s.toSection,
        hilbertBundleSectionMemL2_neg (I := I) (G := G) hG_norm μ s.memL2⟩ }
  letI : Sub Rep := {
    sub := fun s t ↦ s + -t }
  letI : SMul ℕ Rep := {
    smul := fun n s ↦
      ⟨n • s.toSection,
        hilbertBundleSectionMemL2_nsmul (I := I) (G := G) hG_inner μ n s.memL2⟩ }
  letI : SMul ℤ Rep := {
    smul := fun n s ↦
      ⟨n • s.toSection,
        hilbertBundleSectionMemL2_zsmul (I := I) (G := G) hG_inner μ n s.memL2⟩ }
  have coe_zero : (0 : Rep).toSection = 0 := rfl
  have coe_add : ∀ s t : Rep, (s + t).toSection = s.toSection + t.toSection := fun _ _ ↦ rfl
  have coe_neg : ∀ s : Rep, (-s).toSection = -s.toSection := fun _ ↦ rfl
  have coe_sub : ∀ s t : Rep, (s - t).toSection = s.toSection - t.toSection := by
    intro s t
    change (s + -t).toSection = s.toSection - t.toSection
    rw [coe_add, coe_neg]
    simp [sub_eq_add_neg]
  have coe_nsmul : ∀ (s : Rep) (n : ℕ), (n • s).toSection = n • s.toSection :=
    fun _ _ ↦ rfl
  have coe_zsmul : ∀ (s : Rep) (n : ℤ), (n • s).toSection = n • s.toSection :=
    fun _ _ ↦ rfl
  have toSection_injective : Function.Injective (fun s : Rep ↦ s.toSection) := by
    intro s t h
    exact SquareIntegrableHilbertBundleSection.ext (fun x ↦ congrFun h x)
  letI : AddCommGroup Rep :=
    Function.Injective.addCommGroup (fun s : Rep ↦ s.toSection)
      toSection_injective coe_zero coe_add coe_neg coe_sub coe_nsmul coe_zsmul
  have ae_add {s s' t t' : Rep}
      (hs : SquareIntegrableHilbertBundleSection.AeEq s s')
      (ht : SquareIntegrableHilbertBundleSection.AeEq t t') :
      SquareIntegrableHilbertBundleSection.AeEq (s + t) (s' + t') := by
    filter_upwards [hs, ht] with x hsx htx
    change s.toSection x + t.toSection x = s'.toSection x + t'.toSection x
    rw [hsx, htx]
  have ae_neg {s s' : Rep}
      (hs : SquareIntegrableHilbertBundleSection.AeEq s s') :
      SquareIntegrableHilbertBundleSection.AeEq (-s) (-s') := by
    filter_upwards [hs] with x hsx
    change -s.toSection x = -s'.toSection x
    rw [hsx]
  have ae_sub {s s' t t' : Rep}
      (hs : SquareIntegrableHilbertBundleSection.AeEq s s')
      (ht : SquareIntegrableHilbertBundleSection.AeEq t t') :
      SquareIntegrableHilbertBundleSection.AeEq (s - t) (s' - t') := by
    exact ae_add hs (ae_neg ht)
  have ae_nsmul {s s' : Rep} (n : ℕ)
      (hs : SquareIntegrableHilbertBundleSection.AeEq s s') :
      SquareIntegrableHilbertBundleSection.AeEq (n • s) (n • s') := by
    filter_upwards [hs] with x hsx
    change n • s.toSection x = n • s'.toSection x
    rw [hsx]
  have ae_zsmul {s s' : Rep} (n : ℤ)
      (hs : SquareIntegrableHilbertBundleSection.AeEq s s') :
      SquareIntegrableHilbertBundleSection.AeEq (n • s) (n • s') := by
    filter_upwards [hs] with x hsx
    change n • s.toSection x = n • s'.toSection x
    rw [hsx]
  letI : Zero Q := {
    zero := Quotient.mk (SquareIntegrableHilbertBundleSection.aeSetoid (G := G) (μ := μ)) 0 }
  letI : Add Q := {
    add := fun a b ↦
      Quotient.liftOn₂ a b
        (fun s t ↦ Quotient.mk
          (SquareIntegrableHilbertBundleSection.aeSetoid (G := G) (μ := μ)) (s + t))
        (by
          intro s t s' t' hs ht
          exact Quotient.sound (ae_add hs ht)) }
  letI : Neg Q := {
    neg := fun a ↦
      Quotient.liftOn a
        (fun s ↦ Quotient.mk
          (SquareIntegrableHilbertBundleSection.aeSetoid (G := G) (μ := μ)) (-s))
        (by
          intro s t hs
          exact Quotient.sound (ae_neg hs)) }
  letI : Sub Q := {
    sub := fun a b ↦ a + -b }
  letI : SMul ℕ Q := {
    smul := fun n a ↦
      Quotient.liftOn a
        (fun s ↦ Quotient.mk
          (SquareIntegrableHilbertBundleSection.aeSetoid (G := G) (μ := μ)) (n • s))
        (by
          intro s t hs
          exact Quotient.sound (ae_nsmul n hs)) }
  letI : SMul ℤ Q := {
    smul := fun n a ↦
      Quotient.liftOn a
        (fun s ↦ Quotient.mk
          (SquareIntegrableHilbertBundleSection.aeSetoid (G := G) (μ := μ)) (n • s))
        (by
          intro s t hs
          exact Quotient.sound (ae_zsmul n hs)) }
  have mk_surjective :
      Function.Surjective
        (fun s : Rep ↦
          (Quotient.mk (SquareIntegrableHilbertBundleSection.aeSetoid
            (G := G) (μ := μ)) s : Q)) :=
    Quotient.mk_surjective
  have mk_zero :
      (Quotient.mk (SquareIntegrableHilbertBundleSection.aeSetoid
          (G := G) (μ := μ)) (0 : Rep) : Q) =
        (0 : Q) :=
    rfl
  have mk_add : ∀ s t : Rep,
      (Quotient.mk (SquareIntegrableHilbertBundleSection.aeSetoid
          (G := G) (μ := μ)) (s + t) : Q) =
        (Quotient.mk (SquareIntegrableHilbertBundleSection.aeSetoid
          (G := G) (μ := μ)) s : Q) +
        (Quotient.mk (SquareIntegrableHilbertBundleSection.aeSetoid
          (G := G) (μ := μ)) t : Q) := by
    intro s t
    rfl
  have mk_neg : ∀ s : Rep,
      (Quotient.mk (SquareIntegrableHilbertBundleSection.aeSetoid
          (G := G) (μ := μ)) (-s) : Q) =
        -(Quotient.mk (SquareIntegrableHilbertBundleSection.aeSetoid
          (G := G) (μ := μ)) s : Q) := by
    intro s
    rfl
  have mk_sub : ∀ s t : Rep,
      (Quotient.mk (SquareIntegrableHilbertBundleSection.aeSetoid
          (G := G) (μ := μ)) (s - t) : Q) =
        (Quotient.mk (SquareIntegrableHilbertBundleSection.aeSetoid
          (G := G) (μ := μ)) s : Q) -
        (Quotient.mk (SquareIntegrableHilbertBundleSection.aeSetoid
          (G := G) (μ := μ)) t : Q) := by
    intro s t
    rfl
  have mk_nsmul : ∀ (s : Rep) (n : ℕ),
      (Quotient.mk (SquareIntegrableHilbertBundleSection.aeSetoid
          (G := G) (μ := μ)) (n • s) : Q) =
        n • (Quotient.mk (SquareIntegrableHilbertBundleSection.aeSetoid
          (G := G) (μ := μ)) s : Q) := by
    intro s n
    rfl
  have mk_zsmul : ∀ (s : Rep) (n : ℤ),
      (Quotient.mk (SquareIntegrableHilbertBundleSection.aeSetoid
          (G := G) (μ := μ)) (n • s) : Q) =
        n • (Quotient.mk (SquareIntegrableHilbertBundleSection.aeSetoid
          (G := G) (μ := μ)) s : Q) := by
    intro s n
    rfl
  letI : AddCommGroup Q :=
    Function.Surjective.addCommGroup
      (fun s : Rep ↦
        (Quotient.mk (SquareIntegrableHilbertBundleSection.aeSetoid
          (G := G) (μ := μ)) s : Q))
      mk_surjective mk_zero mk_add mk_neg mk_sub mk_nsmul mk_zsmul
  let normQ : Q → ℝ :=
    Quotient.lift
      (fun s : Rep ↦ squareIntegrableHilbertBundleSectionL2Norm G μ s)
      (by
        intro s t hst
        exact squareIntegrableHilbertBundleSectionL2Norm_congr_ae (G := G) μ hst)
  let l2Norm : AddGroupNorm Q := {
    toFun := normQ
    map_zero' := by
      change normQ (0 : Q) = 0
      change squareIntegrableHilbertBundleSectionL2Norm G μ (0 : Rep) = 0
      exact squareIntegrableHilbertBundleSectionL2Norm_zero (I := I) (G := G) hG_inner μ
    add_le' := by
      intro u v
      refine Quotient.inductionOn₂ u v ?_
      intro s t
      change squareIntegrableHilbertBundleSectionL2Norm G μ (s + t : Rep) ≤
        squareIntegrableHilbertBundleSectionL2Norm G μ s +
          squareIntegrableHilbertBundleSectionL2Norm G μ t
      exact squareIntegrableHilbertBundleSectionL2Norm_add_le (I := I) (G := G) hG_inner μ s t
    neg' := by
      intro u
      refine Quotient.inductionOn u ?_
      intro s
      change squareIntegrableHilbertBundleSectionL2Norm G μ (-s : Rep) =
        squareIntegrableHilbertBundleSectionL2Norm G μ s
      exact squareIntegrableHilbertBundleSectionL2Norm_neg (I := I) (G := G) hG_norm μ s
    eq_zero_of_map_eq_zero' := by
      intro u
      refine Quotient.inductionOn u ?_
      intro s hs
      change squareIntegrableHilbertBundleSectionL2Norm G μ s = 0 at hs
      change (Quotient.mk (SquareIntegrableHilbertBundleSection.aeSetoid
          (G := G) (μ := μ)) s : Q) =
        Quotient.mk (SquareIntegrableHilbertBundleSection.aeSetoid
          (G := G) (μ := μ)) (0 : Rep)
      exact Quotient.sound
        ((squareIntegrableHilbertBundleSectionL2Norm_eq_zero_iff_ae_zero
          (I := I) (G := G) hG_inner μ s).1 hs) }
  exact AddGroupNorm.toNormedAddCommGroup l2Norm
/--
%%handwave
name:
  Normed additive group structure on \(L^2\)-sections
statement:
  Let \(V\to X\) be a continuous real Hilbert vector bundle, let \(G\) be a
  bundle geometry whose fiberwise inner product is the given inner product on
  every fiber, and let \(\mu\) be a measure on \(X\).  Then the space
  \(L^2(X,V;\mu)\) of square-integrable measurable sections modulo almost
  everywhere equality admits a normed additive commutative group structure.
proof:
  The norm of an equivalence class is the square root of the integral of the
  fiberwise squared norm of any representative.  The previously constructed
  normed-group structure supplies this norm and is independent of the chosen
  representative.
-/
theorem l2HilbertBundle_admits_normed_add_comm_group
    {H X F : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    [SecondCountableTopology (Bundle.TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
    (G : HilbertBundleGeometry X F V)
    (hG_inner : ∀ (x : X) (v w : V x), G.fiberInner x v w = inner ℝ v w)
    (μ : Measure X) :
    Nonempty (NormedAddCommGroup (L2HilbertBundle G μ)) := by
  exact ⟨l2HilbertBundleNormedAddCommGroup (I := I) (G := G) hG_inner μ⟩

/--
%%handwave
name:
  Inner product on \(L^2\)-sections of a Hilbert bundle
statement:
  The fiberwise inner product integrates to an inner product on the normed
  group of \(L^2\)-sections of a continuous Hilbert bundle.
proof:
  For representatives \(s,t\), define
  \(\langle s,t\rangle=\int_X\langle s(x),t(x)\rangle_x\,d\mu(x)\).
  The Cauchy-Schwarz inequality gives integrability, and changing either
  representative on a null set does not change the integral.  The inner
  product identities follow from the corresponding fiberwise identities.
-/
@[reducible]
noncomputable def l2HilbertBundleInnerProductSpace
    {H X F : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    [SecondCountableTopology (Bundle.TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
    (G : HilbertBundleGeometry X F V) (μ : Measure X)
    (hG_inner : ∀ (x : X) (v w : V x), G.fiberInner x v w = inner ℝ v w) :
    letI : NormedAddCommGroup (L2HilbertBundle G μ) :=
      l2HilbertBundleNormedAddCommGroup (I := I) (G := G) hG_inner μ
    InnerProductSpace ℝ (L2HilbertBundle G μ) := by
  have hG_norm : ∀ (x : X) (v : V x), G.fiberNormSq x v = ‖v‖ ^ 2 := by
    intro x v
    rw [G.fiberNormSq_eq_inner, hG_inner]
    exact real_inner_self_eq_norm_sq v
  let Rep := SquareIntegrableHilbertBundleSection G μ
  let Q := L2HilbertBundle G μ
  letI : Zero Rep := {
    zero := ⟨0, hilbertBundleSectionMemL2_zero (I := I) (G := G) hG_inner μ⟩ }
  letI : Add Rep := {
    add := fun s t ↦
      ⟨s.toSection + t.toSection,
        hilbertBundleSectionMemL2_add (I := I) (G := G) hG_inner μ s.memL2 t.memL2⟩ }
  letI : Neg Rep := {
    neg := fun s ↦
      ⟨-s.toSection,
        hilbertBundleSectionMemL2_neg (I := I) (G := G) hG_norm μ s.memL2⟩ }
  letI : Sub Rep := {
    sub := fun s t ↦ s + -t }
  letI : SMul ℕ Rep := {
    smul := fun n s ↦
      ⟨n • s.toSection,
        hilbertBundleSectionMemL2_nsmul (I := I) (G := G) hG_inner μ n s.memL2⟩ }
  letI : SMul ℤ Rep := {
    smul := fun n s ↦
      ⟨n • s.toSection,
        hilbertBundleSectionMemL2_zsmul (I := I) (G := G) hG_inner μ n s.memL2⟩ }
  letI : SMul ℝ Rep := {
    smul := fun c s ↦
      ⟨c • s.toSection,
        hilbertBundleSectionMemL2_smul (I := I) (G := G) hG_inner μ c s.memL2⟩ }
  have coe_zero : (0 : Rep).toSection = 0 := rfl
  have coe_add : ∀ s t : Rep, (s + t).toSection = s.toSection + t.toSection := fun _ _ ↦ rfl
  have coe_neg : ∀ s : Rep, (-s).toSection = -s.toSection := fun _ ↦ rfl
  have coe_sub : ∀ s t : Rep, (s - t).toSection = s.toSection - t.toSection := by
    intro s t
    change (s + -t).toSection = s.toSection - t.toSection
    rw [coe_add, coe_neg]
    simp [sub_eq_add_neg]
  have coe_nsmul : ∀ (s : Rep) (n : ℕ), (n • s).toSection = n • s.toSection :=
    fun _ _ ↦ rfl
  have coe_zsmul : ∀ (s : Rep) (n : ℤ), (n • s).toSection = n • s.toSection :=
    fun _ _ ↦ rfl
  have coe_smul : ∀ (c : ℝ) (s : Rep), (c • s).toSection = c • s.toSection :=
    fun _ _ ↦ rfl
  have toSection_injective : Function.Injective (fun s : Rep ↦ s.toSection) := by
    intro s t h
    exact SquareIntegrableHilbertBundleSection.ext (fun x ↦ congrFun h x)
  letI : AddCommGroup Rep :=
    Function.Injective.addCommGroup (fun s : Rep ↦ s.toSection)
      toSection_injective coe_zero coe_add coe_neg coe_sub coe_nsmul coe_zsmul
  let toSectionAddHom : Rep →+ HilbertBundleSectionOnSurface X V := {
    toFun := fun s ↦ s.toSection
    map_zero' := coe_zero
    map_add' := coe_add }
  letI : Module ℝ Rep :=
    Function.Injective.module ℝ toSectionAddHom toSection_injective coe_smul
  have ae_add {s s' t t' : Rep}
      (hs : SquareIntegrableHilbertBundleSection.AeEq s s')
      (ht : SquareIntegrableHilbertBundleSection.AeEq t t') :
      SquareIntegrableHilbertBundleSection.AeEq (s + t) (s' + t') := by
    filter_upwards [hs, ht] with x hsx htx
    change s.toSection x + t.toSection x = s'.toSection x + t'.toSection x
    rw [hsx, htx]
  have ae_neg {s s' : Rep}
      (hs : SquareIntegrableHilbertBundleSection.AeEq s s') :
      SquareIntegrableHilbertBundleSection.AeEq (-s) (-s') := by
    filter_upwards [hs] with x hsx
    change -s.toSection x = -s'.toSection x
    rw [hsx]
  have ae_sub {s s' t t' : Rep}
      (hs : SquareIntegrableHilbertBundleSection.AeEq s s')
      (ht : SquareIntegrableHilbertBundleSection.AeEq t t') :
      SquareIntegrableHilbertBundleSection.AeEq (s - t) (s' - t') := by
    exact ae_add hs (ae_neg ht)
  have ae_nsmul {s s' : Rep} (n : ℕ)
      (hs : SquareIntegrableHilbertBundleSection.AeEq s s') :
      SquareIntegrableHilbertBundleSection.AeEq (n • s) (n • s') := by
    filter_upwards [hs] with x hsx
    change n • s.toSection x = n • s'.toSection x
    rw [hsx]
  have ae_zsmul {s s' : Rep} (n : ℤ)
      (hs : SquareIntegrableHilbertBundleSection.AeEq s s') :
      SquareIntegrableHilbertBundleSection.AeEq (n • s) (n • s') := by
    filter_upwards [hs] with x hsx
    change n • s.toSection x = n • s'.toSection x
    rw [hsx]
  have ae_smul {s s' : Rep} (c : ℝ)
      (hs : SquareIntegrableHilbertBundleSection.AeEq s s') :
      SquareIntegrableHilbertBundleSection.AeEq (c • s) (c • s') := by
    filter_upwards [hs] with x hsx
    change c • s.toSection x = c • s'.toSection x
    rw [hsx]
  letI : Zero Q := {
    zero := Quotient.mk (SquareIntegrableHilbertBundleSection.aeSetoid (G := G) (μ := μ)) 0 }
  letI : Add Q := {
    add := fun a b ↦
      Quotient.liftOn₂ a b
        (fun s t ↦ Quotient.mk
          (SquareIntegrableHilbertBundleSection.aeSetoid (G := G) (μ := μ)) (s + t))
        (by
          intro s t s' t' hs ht
          exact Quotient.sound (ae_add hs ht)) }
  letI : Neg Q := {
    neg := fun a ↦
      Quotient.liftOn a
        (fun s ↦ Quotient.mk
          (SquareIntegrableHilbertBundleSection.aeSetoid (G := G) (μ := μ)) (-s))
        (by
          intro s t hs
          exact Quotient.sound (ae_neg hs)) }
  letI : Sub Q := {
    sub := fun a b ↦ a + -b }
  letI : SMul ℕ Q := {
    smul := fun n a ↦
      Quotient.liftOn a
        (fun s ↦ Quotient.mk
          (SquareIntegrableHilbertBundleSection.aeSetoid (G := G) (μ := μ)) (n • s))
        (by
          intro s t hs
          exact Quotient.sound (ae_nsmul n hs)) }
  letI : SMul ℤ Q := {
    smul := fun n a ↦
      Quotient.liftOn a
        (fun s ↦ Quotient.mk
          (SquareIntegrableHilbertBundleSection.aeSetoid (G := G) (μ := μ)) (n • s))
        (by
          intro s t hs
          exact Quotient.sound (ae_zsmul n hs)) }
  letI : SMul ℝ Q := {
    smul := fun c a ↦
      Quotient.liftOn a
        (fun s ↦ Quotient.mk
          (SquareIntegrableHilbertBundleSection.aeSetoid (G := G) (μ := μ)) (c • s))
        (by
          intro s t hs
          exact Quotient.sound (ae_smul c hs)) }
  have mk_surjective :
      Function.Surjective
        (fun s : Rep ↦
          (Quotient.mk (SquareIntegrableHilbertBundleSection.aeSetoid
            (G := G) (μ := μ)) s : Q)) :=
    Quotient.mk_surjective
  have mk_zero :
      (Quotient.mk (SquareIntegrableHilbertBundleSection.aeSetoid
          (G := G) (μ := μ)) (0 : Rep) : Q) =
        (0 : Q) :=
    rfl
  have mk_add : ∀ s t : Rep,
      (Quotient.mk (SquareIntegrableHilbertBundleSection.aeSetoid
          (G := G) (μ := μ)) (s + t) : Q) =
        (Quotient.mk (SquareIntegrableHilbertBundleSection.aeSetoid
          (G := G) (μ := μ)) s : Q) +
        (Quotient.mk (SquareIntegrableHilbertBundleSection.aeSetoid
          (G := G) (μ := μ)) t : Q) := by
    intro s t
    rfl
  have mk_neg : ∀ s : Rep,
      (Quotient.mk (SquareIntegrableHilbertBundleSection.aeSetoid
          (G := G) (μ := μ)) (-s) : Q) =
        -(Quotient.mk (SquareIntegrableHilbertBundleSection.aeSetoid
          (G := G) (μ := μ)) s : Q) := by
    intro s
    rfl
  have mk_sub : ∀ s t : Rep,
      (Quotient.mk (SquareIntegrableHilbertBundleSection.aeSetoid
          (G := G) (μ := μ)) (s - t) : Q) =
        (Quotient.mk (SquareIntegrableHilbertBundleSection.aeSetoid
          (G := G) (μ := μ)) s : Q) -
        (Quotient.mk (SquareIntegrableHilbertBundleSection.aeSetoid
          (G := G) (μ := μ)) t : Q) := by
    intro s t
    rfl
  have mk_nsmul : ∀ (s : Rep) (n : ℕ),
      (Quotient.mk (SquareIntegrableHilbertBundleSection.aeSetoid
          (G := G) (μ := μ)) (n • s) : Q) =
        n • (Quotient.mk (SquareIntegrableHilbertBundleSection.aeSetoid
          (G := G) (μ := μ)) s : Q) := by
    intro s n
    rfl
  have mk_zsmul : ∀ (s : Rep) (n : ℤ),
      (Quotient.mk (SquareIntegrableHilbertBundleSection.aeSetoid
          (G := G) (μ := μ)) (n • s) : Q) =
        n • (Quotient.mk (SquareIntegrableHilbertBundleSection.aeSetoid
          (G := G) (μ := μ)) s : Q) := by
    intro s n
    rfl
  have mk_smul : ∀ (s : Rep) (c : ℝ),
      (Quotient.mk (SquareIntegrableHilbertBundleSection.aeSetoid
          (G := G) (μ := μ)) (c • s) : Q) =
        c • (Quotient.mk (SquareIntegrableHilbertBundleSection.aeSetoid
          (G := G) (μ := μ)) s : Q) := by
    intro s c
    rfl
  letI : AddCommGroup Q :=
    Function.Surjective.addCommGroup
      (fun s : Rep ↦
        (Quotient.mk (SquareIntegrableHilbertBundleSection.aeSetoid
          (G := G) (μ := μ)) s : Q))
      mk_surjective mk_zero mk_add mk_neg mk_sub mk_nsmul mk_zsmul
  let mkAddHom : Rep →+ Q := {
    toFun := fun s ↦
      (Quotient.mk (SquareIntegrableHilbertBundleSection.aeSetoid
        (G := G) (μ := μ)) s : Q)
    map_zero' := mk_zero
    map_add' := mk_add }
  letI : Module ℝ Q :=
    Function.Surjective.module ℝ mkAddHom mk_surjective (fun c s ↦ mk_smul s c)
  let normQ : Q → ℝ :=
    Quotient.lift
      (fun s : Rep ↦ squareIntegrableHilbertBundleSectionL2Norm G μ s)
      (by
        intro s t hst
        exact squareIntegrableHilbertBundleSectionL2Norm_congr_ae (G := G) μ hst)
  let l2Norm : AddGroupNorm Q := {
    toFun := normQ
    map_zero' := by
      change normQ (0 : Q) = 0
      change squareIntegrableHilbertBundleSectionL2Norm G μ (0 : Rep) = 0
      exact squareIntegrableHilbertBundleSectionL2Norm_zero (I := I) (G := G) hG_inner μ
    add_le' := by
      intro u v
      refine Quotient.inductionOn₂ u v ?_
      intro s t
      change squareIntegrableHilbertBundleSectionL2Norm G μ (s + t : Rep) ≤
        squareIntegrableHilbertBundleSectionL2Norm G μ s +
          squareIntegrableHilbertBundleSectionL2Norm G μ t
      exact squareIntegrableHilbertBundleSectionL2Norm_add_le (I := I) (G := G) hG_inner μ s t
    neg' := by
      intro u
      refine Quotient.inductionOn u ?_
      intro s
      change squareIntegrableHilbertBundleSectionL2Norm G μ (-s : Rep) =
        squareIntegrableHilbertBundleSectionL2Norm G μ s
      exact squareIntegrableHilbertBundleSectionL2Norm_neg (I := I) (G := G) hG_norm μ s
    eq_zero_of_map_eq_zero' := by
      intro u
      refine Quotient.inductionOn u ?_
      intro s hs
      change squareIntegrableHilbertBundleSectionL2Norm G μ s = 0 at hs
      change (Quotient.mk (SquareIntegrableHilbertBundleSection.aeSetoid
          (G := G) (μ := μ)) s : Q) =
        Quotient.mk (SquareIntegrableHilbertBundleSection.aeSetoid
          (G := G) (μ := μ)) (0 : Rep)
      exact Quotient.sound
        ((squareIntegrableHilbertBundleSectionL2Norm_eq_zero_iff_ae_zero
          (I := I) (G := G) hG_inner μ s).1 hs) }
  letI : NormedAddCommGroup Q :=
    l2HilbertBundleNormedAddCommGroup (I := I) (G := G) hG_inner μ
  letI : NormedSpace ℝ Q := {
    norm_smul_le := by
      intro c u
      refine Quotient.inductionOn u ?_
      intro s
      change squareIntegrableHilbertBundleSectionL2Norm G μ (c • s : Rep) ≤
        ‖c‖ * squareIntegrableHilbertBundleSectionL2Norm G μ s
      exact (squareIntegrableHilbertBundleSectionL2Norm_smul (I := I) (G := G)
        hG_inner μ c s).le }
  let innerRep : Rep → Rep → ℝ :=
    fun s t ↦ ∫ x, inner ℝ (s.toSection x) (t.toSection x) ∂μ
  let innerQ : Q → Q → ℝ :=
    Quotient.lift₂ innerRep
      (by
        intro s t s' t' hs ht
        apply integral_congr_ae
        filter_upwards [hs, ht] with x hsx htx
        simp [hsx, htx])
  exact {
    inner := innerQ
    norm_sq_eq_re_inner := by
      intro u
      refine Quotient.inductionOn u ?_
      intro s
      change squareIntegrableHilbertBundleSectionL2Norm G μ s ^ 2 =
        ∫ x, inner ℝ (s.toSection x) (s.toSection x) ∂μ
      have hnonneg :
          0 ≤ ∫ x, G.fiberNormSq x (s.toSection x) ∂μ := by
        refine integral_nonneg_of_ae ?_
        filter_upwards [] with x
        rw [hG_norm x (s.toSection x)]
        exact sq_nonneg _
      unfold squareIntegrableHilbertBundleSectionL2Norm
      unfold squareIntegrableHilbertBundleSectionL2NormSq
      rw [Real.sq_sqrt hnonneg]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [G.fiberNormSq_eq_inner, hG_inner]
    conj_inner_symm := by
      intro u v
      refine Quotient.inductionOn₂ u v ?_
      intro s t
      change innerRep t s = innerRep s t
      apply integral_congr_ae
      filter_upwards [] with x
      exact real_inner_comm _ _
    add_left := by
      intro u v w
      refine Quotient.inductionOn₃ u v w ?_
      intro s t r
      change innerRep (s + t) r = innerRep s r + innerRep t r
      have hs_int : Integrable (fun x : X ↦ inner ℝ (s.toSection x) (r.toSection x)) μ :=
        squareIntegrableHilbertBundleSection_inner_integrable (I := I) (G := G) hG_inner μ s r
      have ht_int : Integrable (fun x : X ↦ inner ℝ (t.toSection x) (r.toSection x)) μ :=
        squareIntegrableHilbertBundleSection_inner_integrable (I := I) (G := G) hG_inner μ t r
      calc
        ∫ x, inner ℝ ((s + t : Rep).toSection x) (r.toSection x) ∂μ =
            ∫ x, (inner ℝ (s.toSection x) (r.toSection x) +
              inner ℝ (t.toSection x) (r.toSection x)) ∂μ := by
              apply integral_congr_ae
              filter_upwards [] with x
              change inner ℝ (s.toSection x + t.toSection x) (r.toSection x) =
                inner ℝ (s.toSection x) (r.toSection x) +
                  inner ℝ (t.toSection x) (r.toSection x)
              exact inner_add_left _ _ _
        _ = ∫ x, inner ℝ (s.toSection x) (r.toSection x) ∂μ +
            ∫ x, inner ℝ (t.toSection x) (r.toSection x) ∂μ := by
              exact integral_add hs_int ht_int
    smul_left := by
      intro u v c
      refine Quotient.inductionOn₂ u v ?_
      intro s t
      change innerRep (c • s) t = c * innerRep s t
      calc
        ∫ x, inner ℝ ((c • s : Rep).toSection x) (t.toSection x) ∂μ =
            ∫ x, c * inner ℝ (s.toSection x) (t.toSection x) ∂μ := by
              apply integral_congr_ae
              filter_upwards [] with x
              change inner ℝ (c • s.toSection x) (t.toSection x) =
                c * inner ℝ (s.toSection x) (t.toSection x)
              exact real_inner_smul_left _ _ c
        _ = c * ∫ x, inner ℝ (s.toSection x) (t.toSection x) ∂μ := by
              exact integral_const_mul c (fun x ↦ inner ℝ (s.toSection x) (t.toSection x)) }
/--
%%handwave
name:
  Inner-product structure on \(L^2\)-sections
statement:
  Let \(V\to X\) be a continuous real Hilbert vector bundle, let \(G\) be a
  bundle geometry satisfying
  \(\langle v,w\rangle_{G,x}=\langle v,w\rangle_x\) for every \(x\in X\) and
  \(v,w\in V_x\), and let \(\mu\) be a measure on \(X\).  There is a normed
  additive commutative group structure on \(L^2(X,V;\mu)\) for which this
  space admits the inner product
  \[\langle [s],[t]\rangle_{L^2}=\int_X\langle s(x),t(x)\rangle_x\,d\mu(x).\]
proof:
  Equip the quotient with the norm obtained from the fiberwise \(L^2\)-norm,
  then use the integrated fiberwise pairing.  Its value is unchanged by
  replacing either section on a null set, and the resulting norm is the
  chosen \(L^2\)-norm.
-/
theorem l2HilbertBundle_admits_inner_product_space
    {H X F : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    [SecondCountableTopology (Bundle.TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
    (G : HilbertBundleGeometry X F V) (μ : Measure X)
    (hG_inner : ∀ (x : X) (v w : V x), G.fiberInner x v w = inner ℝ v w) :
    ∃ (_ : NormedAddCommGroup (L2HilbertBundle G μ)),
      Nonempty (InnerProductSpace ℝ (L2HilbertBundle G μ)) := by
  let instNormed : NormedAddCommGroup (L2HilbertBundle G μ) :=
    l2HilbertBundleNormedAddCommGroup (I := I) (G := G) hG_inner μ
  letI : NormedAddCommGroup (L2HilbertBundle G μ) := instNormed
  exact ⟨instNormed,
    ⟨l2HilbertBundleInnerProductSpace (I := I) (G := G) (μ := μ) hG_inner⟩⟩

/--
%%handwave
name:
  Absolutely summable representative series are Cauchy in \(L^2\)
statement:
  If the \(L^2\)-norms of a sequence of square-integrable bundle sections are
  summable, then the sequence of \(L^2\)-classes of finite partial sums is
  Cauchy.
proof:
  The quotient norm of the class of a representative is its representative
  \(L^2\)-norm.  Hence the hypotheses say that the norms of the terms in the
  quotient normed group are summable.  The standard normed-group comparison
  criterion then gives Cauchy convergence of finite sums, and restricting from
  arbitrary finite subsets to the increasing initial segments gives the usual
  partial sums.
-/
private theorem l2HilbertBundle_representative_summable_series_partial_sums_cauchy
    {H X F : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    [SecondCountableTopology (Bundle.TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
    (G : HilbertBundleGeometry X F V) (μ : Measure X)
    (hG_inner : ∀ (x : X) (v w : V x), G.fiberInner x v w = inner ℝ v w) :
    letI : NormedAddCommGroup (L2HilbertBundle G μ) :=
      l2HilbertBundleNormedAddCommGroup (I := I) (G := G) hG_inner μ
    ∀ s : ℕ → SquareIntegrableHilbertBundleSection G μ,
      Summable (fun n ↦ squareIntegrableHilbertBundleSectionL2Norm G μ (s n)) →
        CauchySeq
          (fun n : ℕ ↦ ∑ i ∈ Finset.range n, L2HilbertBundle.mk (s i)) := by
  letI : NormedAddCommGroup (L2HilbertBundle G μ) :=
    l2HilbertBundleNormedAddCommGroup (I := I) (G := G) hG_inner μ
  intro s hs
  have hs_norm :
      Summable
        (fun n : ℕ ↦ ‖(L2HilbertBundle.mk (s n) : L2HilbertBundle G μ)‖) := by
    have hnorm :
        (fun n : ℕ ↦ ‖(L2HilbertBundle.mk (s n) : L2HilbertBundle G μ)‖) =
          fun n : ℕ ↦ squareIntegrableHilbertBundleSectionL2Norm G μ (s n) := by
      funext n
      rfl
    simpa [hnorm] using hs
  have hfin :
      CauchySeq
        (fun I : Finset ℕ ↦
          ∑ i ∈ I, (L2HilbertBundle.mk (s i) : L2HilbertBundle G μ)) :=
    cauchySeq_finset_of_summable_norm hs_norm
  simpa [Function.comp_def] using hfin.comp_tendsto Filter.tendsto_finset_range

/--
%%handwave
name:
  Finite sums of square-integrable sections are square-integrable
statement:
  A finite fiberwise sum of square-integrable Hilbert-bundle sections is again
  square-integrable.
proof:
  Induct on the finite set.  The empty sum is the zero section, and the
  induction step uses closure of square-integrable sections under fiberwise
  addition.
-/
private theorem hilbertBundleSectionMemL2_finset_sum
    {H X F ι : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    [SecondCountableTopology (Bundle.TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
    (G : HilbertBundleGeometry X F V)
    (hG_inner : ∀ (x : X) (v w : V x), G.fiberInner x v w = inner ℝ v w)
    (μ : Measure X) (s : ι → SquareIntegrableHilbertBundleSection G μ)
    (J : Finset ι) :
    HilbertBundleSectionMemL2 G μ
      (fun x : X ↦ ∑ i ∈ J, (s i).toSection x) := by
  classical
  refine Finset.induction_on J ?_ ?_
  · simpa using hilbertBundleSectionMemL2_zero (I := I) (G := G) hG_inner μ
  · intro a K haK hK
    have h_add :
        HilbertBundleSectionMemL2 G μ
          ((s a).toSection + fun x : X ↦ ∑ i ∈ K, (s i).toSection x) :=
      hilbertBundleSectionMemL2_add (I := I) (G := G) hG_inner μ (s a).memL2 hK
    refine h_add.congr_ae ?_
    filter_upwards [] with x
    simp [Finset.sum_insert, haK]

/--
%%handwave
name:
  Finite sums as square-integrable representatives
statement:
  The finite fiberwise sum of square-integrable sections defines a
  square-integrable representative.
-/
private noncomputable def squareIntegrableHilbertBundleSectionFinsetSum
    {H X F ι : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    [SecondCountableTopology (Bundle.TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
    (G : HilbertBundleGeometry X F V)
    (hG_inner : ∀ (x : X) (v w : V x), G.fiberInner x v w = inner ℝ v w)
    (μ : Measure X) (s : ι → SquareIntegrableHilbertBundleSection G μ)
    (J : Finset ι) :
    SquareIntegrableHilbertBundleSection G μ :=
  ⟨fun x : X ↦ ∑ i ∈ J, (s i).toSection x,
    hilbertBundleSectionMemL2_finset_sum (I := I) (G := G) hG_inner μ s J⟩

/--
%%handwave
name:
  Finite representative sums descend to finite quotient sums
statement:
  The \(L^2\)-class of a finite fiberwise sum of representatives is the finite
  sum of the corresponding \(L^2\)-classes.
proof:
  Induct on the finite set.  The empty-sum case is the zero representative,
  and the induction step is the definition of addition on the almost-everywhere
  quotient.
-/
private theorem l2HilbertBundle_mk_finset_sum
    {H X F ι : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    [SecondCountableTopology (Bundle.TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
    (G : HilbertBundleGeometry X F V) (μ : Measure X)
    (hG_inner : ∀ (x : X) (v w : V x), G.fiberInner x v w = inner ℝ v w) :
    letI : NormedAddCommGroup (L2HilbertBundle G μ) :=
      l2HilbertBundleNormedAddCommGroup (I := I) (G := G) hG_inner μ
    ∀ (s : ι → SquareIntegrableHilbertBundleSection G μ) (J : Finset ι),
      L2HilbertBundle.mk
          (squareIntegrableHilbertBundleSectionFinsetSum
            (I := I) (G := G) hG_inner μ s J) =
        ∑ i ∈ J, L2HilbertBundle.mk (s i) := by
  classical
  letI : NormedAddCommGroup (L2HilbertBundle G μ) :=
    l2HilbertBundleNormedAddCommGroup (I := I) (G := G) hG_inner μ
  intro s J
  refine Finset.induction_on J ?_ ?_
  · rfl
  · intro a K haK hK
    rw [Finset.sum_insert haK, ← hK]
    apply L2HilbertBundle.sound
    filter_upwards [] with x
    change (∑ i ∈ insert a K, (s i).toSection x) =
      (s a).toSection x + ∑ i ∈ K, (s i).toSection x
    simp [Finset.sum_insert, haK]

/--
%%handwave
name:
  The zero representative defines the zero bundle \(L^2\) class
statement:
  In the Hilbert structure on square-integrable bundle sections, the class of the pointwise zero section is the zero vector.
proof:
  Unfold the quotient operations; the two representatives agree pointwise.
-/
theorem l2HilbertBundle_mk_zero
    {H X F : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    [SecondCountableTopology (Bundle.TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
    (G : HilbertBundleGeometry X F V) (μ : Measure X)
    (hG_inner : ∀ (x : X) (v w : V x), G.fiberInner x v w = inner ℝ v w) :
    letI : NormedAddCommGroup (L2HilbertBundle G μ) :=
      l2HilbertBundleNormedAddCommGroup (I := I) (G := G) hG_inner μ
    L2HilbertBundle.mk
        (⟨0, hilbertBundleSectionMemL2_zero (I := I) (G := G) hG_inner μ⟩ :
          SquareIntegrableHilbertBundleSection G μ) =
      0 := by
  letI : NormedAddCommGroup (L2HilbertBundle G μ) :=
    l2HilbertBundleNormedAddCommGroup (I := I) (G := G) hG_inner μ
  rfl

noncomputable def squareIntegrableHilbertBundleSectionAdd
    {H X F : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    [SecondCountableTopology (Bundle.TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
    (G : HilbertBundleGeometry X F V)
    (hG_inner : ∀ (x : X) (v w : V x), G.fiberInner x v w = inner ℝ v w)
    (μ : Measure X) (s t : SquareIntegrableHilbertBundleSection G μ) :
    SquareIntegrableHilbertBundleSection G μ :=
  ⟨s.toSection + t.toSection,
    hilbertBundleSectionMemL2_add (I := I) (G := G) hG_inner μ s.memL2 t.memL2⟩

/--
%%handwave
name:
  Addition of bundle \(L^2\) representatives
statement:
  For square-integrable bundle sections (s,t), the class of (s+t) equals the sum of their classes.
proof:
  Addition on the quotient is induced by pointwise fiberwise addition, so the representatives coincide.
-/
theorem l2HilbertBundle_mk_add
    {H X F : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    [SecondCountableTopology (Bundle.TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
    (G : HilbertBundleGeometry X F V) (μ : Measure X)
    (hG_inner : ∀ (x : X) (v w : V x), G.fiberInner x v w = inner ℝ v w)
    (s t : SquareIntegrableHilbertBundleSection G μ) :
    letI : NormedAddCommGroup (L2HilbertBundle G μ) :=
      l2HilbertBundleNormedAddCommGroup (I := I) (G := G) hG_inner μ
    L2HilbertBundle.mk
        (squareIntegrableHilbertBundleSectionAdd (I := I) (G := G) hG_inner μ s t) =
      L2HilbertBundle.mk s + L2HilbertBundle.mk t := by
  letI : NormedAddCommGroup (L2HilbertBundle G μ) :=
    l2HilbertBundleNormedAddCommGroup (I := I) (G := G) hG_inner μ
  rfl

noncomputable def squareIntegrableHilbertBundleSectionSmul
    {H X F : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    [SecondCountableTopology (Bundle.TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
    (G : HilbertBundleGeometry X F V)
    (hG_inner : ∀ (x : X) (v w : V x), G.fiberInner x v w = inner ℝ v w)
    (μ : Measure X) (c : ℝ) (s : SquareIntegrableHilbertBundleSection G μ) :
    SquareIntegrableHilbertBundleSection G μ :=
  ⟨c • s.toSection,
    hilbertBundleSectionMemL2_smul (I := I) (G := G) hG_inner μ c s.memL2⟩

/--
%%handwave
name:
  Scalar multiplication of bundle \(L^2\) representatives
statement:
  For \(c\in\mathbb R\), the class of the section \(cs\) is \(c\) times the class of \(s\).
proof:
  Scalar multiplication on the quotient is induced by pointwise scalar multiplication.
-/
theorem l2HilbertBundle_mk_smul
    {H X F : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    [SecondCountableTopology (Bundle.TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
    (G : HilbertBundleGeometry X F V) (μ : Measure X)
    (hG_inner : ∀ (x : X) (v w : V x), G.fiberInner x v w = inner ℝ v w)
    (c : ℝ) (s : SquareIntegrableHilbertBundleSection G μ) :
    letI : NormedAddCommGroup (L2HilbertBundle G μ) :=
      l2HilbertBundleNormedAddCommGroup (I := I) (G := G) hG_inner μ
    letI : InnerProductSpace ℝ (L2HilbertBundle G μ) :=
      l2HilbertBundleInnerProductSpace (I := I) (G := G) (μ := μ) hG_inner
    L2HilbertBundle.mk
        (squareIntegrableHilbertBundleSectionSmul (I := I) (G := G) hG_inner μ c s) =
      c • L2HilbertBundle.mk s := by
  letI : NormedAddCommGroup (L2HilbertBundle G μ) :=
    l2HilbertBundleNormedAddCommGroup (I := I) (G := G) hG_inner μ
  letI : InnerProductSpace ℝ (L2HilbertBundle G μ) :=
    l2HilbertBundleInnerProductSpace (I := I) (G := G) (μ := μ) hG_inner
  rfl

private noncomputable def squareIntegrableHilbertBundleSectionSub
    {H X F : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    [SecondCountableTopology (Bundle.TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
    (G : HilbertBundleGeometry X F V)
    (hG_inner : ∀ (x : X) (v w : V x), G.fiberInner x v w = inner ℝ v w)
    (μ : Measure X) (s t : SquareIntegrableHilbertBundleSection G μ) :
    SquareIntegrableHilbertBundleSection G μ := by
  have hG_norm : ∀ (x : X) (v : V x), G.fiberNormSq x v = ‖v‖ ^ 2 := by
    intro x v
    rw [G.fiberNormSq_eq_inner, hG_inner]
    exact real_inner_self_eq_norm_sq v
  exact
    ⟨s.toSection + -t.toSection,
      hilbertBundleSectionMemL2_add (I := I) (G := G) hG_inner μ s.memL2
        (hilbertBundleSectionMemL2_neg (I := I) (G := G) hG_norm μ t.memL2)⟩

/--
%%handwave
name:
  Subtraction of bundle \(L^2\) representatives
statement:
  The class of the pointwise difference (s-t) equals the difference of the two bundle \(L^2\) classes.
proof:
  Rewrite subtraction as addition of the negative and use the representative formulas for addition and scalar multiplication.
-/
private theorem l2HilbertBundle_mk_sub
    {H X F : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    [SecondCountableTopology (Bundle.TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
    (G : HilbertBundleGeometry X F V) (μ : Measure X)
    (hG_inner : ∀ (x : X) (v w : V x), G.fiberInner x v w = inner ℝ v w)
    (s t : SquareIntegrableHilbertBundleSection G μ) :
    letI : NormedAddCommGroup (L2HilbertBundle G μ) :=
      l2HilbertBundleNormedAddCommGroup (I := I) (G := G) hG_inner μ
    L2HilbertBundle.mk
        (squareIntegrableHilbertBundleSectionSub (I := I) (G := G) hG_inner μ s t) =
      L2HilbertBundle.mk s - L2HilbertBundle.mk t := by
  letI : NormedAddCommGroup (L2HilbertBundle G μ) :=
    l2HilbertBundleNormedAddCommGroup (I := I) (G := G) hG_inner μ
  rfl

/--
%%handwave
name:
  Norm of a represented bundle \(L^2\) section
statement:
  The norm of the class represented by \(s\) equals \(\big(\int \|s(x)\|_x^2\,d\mu\big)^{1/2}\).
proof:
  The quotient Hilbert norm is defined by the integrated fiberwise inner product; evaluating it on the diagonal gives the stated \(L^2\) norm.
-/
theorem l2HilbertBundle_norm_mk_eq_l2Norm
    {H X F : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    [SecondCountableTopology (Bundle.TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
    (G : HilbertBundleGeometry X F V) (μ : Measure X)
    (hG_inner : ∀ (x : X) (v w : V x), G.fiberInner x v w = inner ℝ v w)
    (s : SquareIntegrableHilbertBundleSection G μ) :
    letI : NormedAddCommGroup (L2HilbertBundle G μ) :=
      l2HilbertBundleNormedAddCommGroup (I := I) (G := G) hG_inner μ
    ‖L2HilbertBundle.mk s‖ =
      squareIntegrableHilbertBundleSectionL2Norm G μ s := by
  letI : NormedAddCommGroup (L2HilbertBundle G μ) :=
    l2HilbertBundleNormedAddCommGroup (I := I) (G := G) hG_inner μ
  rfl

/--
%%handwave
name:
  Extended norm of the pointwise fiber norm
statement:
  For a square-integrable bundle section \(s\), the extended \(L^2\)-norm of \(x\mapsto\|s(x)\|_x\) is the finite extended-real image of its real \(L^2\)-norm.
proof:
  Square both quantities, identify both with the integral of the fiberwise square norm, and use nonnegativity to take square roots.
-/
private theorem squareIntegrableHilbertBundleSection_eLpNorm_norm_eq_ofReal_l2Norm
    {H X F : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold I 1 X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
    (G : HilbertBundleGeometry X F V)
    (hG_inner : ∀ (x : X) (v w : V x), G.fiberInner x v w = inner ℝ v w)
    (μ : Measure X) (s : SquareIntegrableHilbertBundleSection G μ) :
    eLpNorm (fun x : X ↦ ‖s.toSection x‖) 2 μ =
      ENNReal.ofReal (squareIntegrableHilbertBundleSectionL2Norm G μ s) := by
  have hs_memLp :
      MemLp (fun x : X ↦ ‖s.toSection x‖) 2 μ :=
    squareIntegrableHilbertBundleSection_norm_memLp (I := I) (G := G) hG_inner μ s
  rw [← MeasureTheory.ofReal_lpNorm hs_memLp]
  congr 1
  exact (squareIntegrableHilbertBundleSectionL2Norm_eq_lpNorm_norm
            (I := I) (G := G) hG_inner μ s).symm

/--
%%handwave
name:
  Pointwise sum of an absolutely summable series of sections
statement:
  The pointwise sum of a series of bundle sections is defined by summing in
  each fiber where the series of fiber norms is summable, and by the zero
  vector elsewhere.
-/
private noncomputable def hilbertBundleSectionSeriesLimit
    {H X F : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold I 1 X]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, CompleteSpace (V x)]
    (G : HilbertBundleGeometry X F V) (μ : Measure X)
    (s : ℕ → SquareIntegrableHilbertBundleSection G μ) :
    HilbertBundleSectionOnSurface X V := by
  classical
  exact fun x ↦
    if hx : Summable fun n : ℕ ↦ ‖(s n).toSection x‖ then
      ∑' n : ℕ, (s n).toSection x
    else
      0

/--
%%handwave
name:
  Pointwise convergence of fiberwise partial sums
statement:
  On the set where the series of fiber norms is summable, the finite fiberwise
  partial sums converge to the pointwise series-limit section.
proof:
  At such a point, absolute convergence of the fiber series gives summability
  in the complete fiber.  The standard theorem identifying the sum of a
  summable series with the limit of its finite partial sums gives the result.
-/
private theorem hilbertBundleSectionSeriesLimit_tendsto_ae
    {H X F : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    [SecondCountableTopology (Bundle.TotalSpace F V)]
    [TopologicalSpace.PseudoMetrizableSpace (Bundle.TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [∀ x, CompleteSpace (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
    (G : HilbertBundleGeometry X F V)
    (hG_inner : ∀ (x : X) (v w : V x), G.fiberInner x v w = inner ℝ v w)
    (μ : Measure X) (s : ℕ → SquareIntegrableHilbertBundleSection G μ)
    (hpoint : ∀ᵐ x ∂μ, Summable fun n : ℕ ↦ ‖(s n).toSection x‖) :
    ∀ᵐ x ∂μ,
      Filter.Tendsto
        (fun n : ℕ ↦
          (squareIntegrableHilbertBundleSectionFinsetSum
            (I := I) (G := G) hG_inner μ s (Finset.range n)).toSection x)
        Filter.atTop
        (𝓝 (hilbertBundleSectionSeriesLimit (I := I) (G := G) μ s x)) := by
  filter_upwards [hpoint] with x hx
  have hx_vec : Summable fun n : ℕ ↦ (s n).toSection x :=
    hx.of_norm
  have hx_sum :
      Filter.Tendsto
        (fun n : ℕ ↦ ∑ i ∈ Finset.range n, (s i).toSection x)
        Filter.atTop
        (𝓝 (∑' n : ℕ, (s n).toSection x)) :=
    hx_vec.hasSum.tendsto_sum_nat
  simpa [squareIntegrableHilbertBundleSectionFinsetSum,
    hilbertBundleSectionSeriesLimit, hx] using hx_sum

/--
%%handwave
name:
  Pointwise summability of fiber norms
statement:
  If the \(L^2\)-norms of a sequence of square-integrable sections are
  summable, then the pointwise series of fiber norms is summable almost
  everywhere.
proof:
  The scalar pointwise norms are \(L^2\)-functions.  Minkowski's inequality
  bounds the \(L^2\)-norms of their finite partial sums by the corresponding
  finite sums of the \(L^2\)-norms, hence uniformly by the full numerical
  series.  Fatou's lemma applied to the nonnegative squared partial sums gives
  a finite \(L^2\)-bound for the extended pointwise sum, so that sum is finite
  almost everywhere.  Finiteness of the extended nonnegative sum is equivalent
  to summability of the real nonnegative fiber norms.
-/
private theorem l2HilbertBundle_pointwise_norm_series_summable_ae
    {H X F : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    [SecondCountableTopology (Bundle.TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
    (G : HilbertBundleGeometry X F V) (μ : Measure X)
    (hG_inner : ∀ (x : X) (v w : V x), G.fiberInner x v w = inner ℝ v w)
    (s : ℕ → SquareIntegrableHilbertBundleSection G μ)
    (hs : Summable (fun n ↦ squareIntegrableHilbertBundleSectionL2Norm G μ (s n))) :
    ∀ᵐ x ∂μ, Summable fun n : ℕ ↦ ‖(s n).toSection x‖ := by
  let f : ℕ → X → ℝ := fun n x ↦ ‖(s n).toSection x‖
  have hf_memLp : ∀ n : ℕ, MemLp (f n) (2 : ℝ≥0∞) μ := by
    intro n
    simpa [f] using
      squareIntegrableHilbertBundleSection_norm_memLp
      (I := I) (G := G) hG_inner μ (s n)
  let C : ℝ≥0∞ :=
    ∑' n : ℕ, ENNReal.ofReal (squareIntegrableHilbertBundleSectionL2Norm G μ (s n))
  have hnorm_nonneg :
      ∀ n : ℕ, 0 ≤ squareIntegrableHilbertBundleSectionL2Norm G μ (s n) := by
    intro n
    exact Real.sqrt_nonneg _
  have hC_ne_top : C ≠ (∞ : ℝ≥0∞) := by
    have hC_eq :
        C = ENNReal.ofReal
          (∑' n : ℕ, squareIntegrableHilbertBundleSectionL2Norm G μ (s n)) := by
      dsimp [C]
      rw [ENNReal.ofReal_tsum_of_nonneg hnorm_nonneg hs]
    rw [hC_eq]
    exact ENNReal.ofReal_ne_top
  have heLp_f :
      ∀ n : ℕ, eLpNorm (f n) (2 : ℝ≥0∞) μ =
        ENNReal.ofReal (squareIntegrableHilbertBundleSectionL2Norm G μ (s n)) := by
    intro n
    rw [← MeasureTheory.ofReal_lpNorm (hf_memLp n)]
    congr 1
    exact (squareIntegrableHilbertBundleSectionL2Norm_eq_lpNorm_norm
            (I := I) (G := G) hG_inner μ (s n)).symm
  have h_partial_bound :
      ∀ N : ℕ,
        eLpNorm (∑ i ∈ Finset.range N, f i) (2 : ℝ≥0∞) μ ≤ C := by
    intro N
    calc
      eLpNorm (∑ i ∈ Finset.range N, f i) (2 : ℝ≥0∞) μ
          ≤ ∑ i ∈ Finset.range N, eLpNorm (f i) (2 : ℝ≥0∞) μ := by
            exact eLpNorm_sum_le
              (s := Finset.range N)
              (f := f) (p := (2 : ℝ≥0∞)) (μ := μ)
              (fun i _ ↦ (hf_memLp i).aestronglyMeasurable)
              (by norm_num)
      _ = ∑ i ∈ Finset.range N,
          ENNReal.ofReal (squareIntegrableHilbertBundleSectionL2Norm G μ (s i)) := by
            exact Finset.sum_congr rfl fun i _ ↦ heLp_f i
      _ ≤ C := by
            exact ENNReal.sum_le_tsum (Finset.range N)
  have h_integral_partial :
      ∀ N : ℕ,
        ∫⁻ x, (∑ i ∈ Finset.range N, ‖(s i).toSection x‖ₑ) ^ (2 : ℝ) ∂μ ≤
          C ^ (2 : ℝ) := by
    intro N
    have h_e := h_partial_bound N
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := (2 : ℝ≥0∞))
      (by norm_num) (by norm_num)] at h_e
    norm_num at h_e
    have h_pow :
        (∫⁻ x, ‖(∑ i ∈ Finset.range N, f i) x‖ₑ ^ (2 : ℝ) ∂μ) ≤
          C ^ (2 : ℝ) := by
      let A : ℝ≥0∞ :=
        ∫⁻ x, ‖(∑ i ∈ Finset.range N, f i) x‖ₑ ^ (2 : ℝ) ∂μ
      have h_e' : A ^ ((2 : ℝ)⁻¹) ≤ C := by
        dsimp [A]
        simpa [one_div] using h_e
      simpa [A, inv_inv] using
        (ENNReal.le_rpow_inv_iff
          (x := A) (y := C) (z := (2 : ℝ)⁻¹)
          (by norm_num : 0 < (2 : ℝ)⁻¹)).2 h_e'
    calc
      ∫⁻ x, (∑ i ∈ Finset.range N, ‖(s i).toSection x‖ₑ) ^ (2 : ℝ) ∂μ =
          ∫⁻ x, ‖(∑ i ∈ Finset.range N, f i) x‖ₑ ^ (2 : ℝ) ∂μ := by
            apply lintegral_congr
            intro x
            congr 1
            have hfun :
                ((∑ i ∈ Finset.range N, f i) x) =
                  ∑ i ∈ Finset.range N, ‖(s i).toSection x‖ := by
              simp [f]
            rw [hfun]
            change (∑ i ∈ Finset.range N, ‖(s i).toSection x‖ₑ) =
              ‖(∑ i ∈ Finset.range N, ‖(s i).toSection x‖)‖ₑ
            have hsum_nonneg :
                0 ≤ ∑ i ∈ Finset.range N, ‖(s i).toSection x‖ := by
              exact Finset.sum_nonneg fun i _ ↦ norm_nonneg _
            rw [Real.enorm_of_nonneg hsum_nonneg]
            rw [ENNReal.ofReal_sum_of_nonneg]
            · simp
            · intro i _
              exact norm_nonneg ((s i).toSection x)
      _ ≤ C ^ (2 : ℝ) := h_pow
  have h_liminf_integral :
      ∫⁻ x, Filter.liminf
          (fun N : ℕ ↦ (∑ i ∈ Finset.range N, ‖(s i).toSection x‖ₑ) ^ (2 : ℝ))
          Filter.atTop ∂μ ≤
        C ^ (2 : ℝ) := by
    refine (lintegral_liminf_le' ?_).trans ?_
    · intro N
      simpa [f] using
        (Finset.aemeasurable_fun_sum (Finset.range N)
          fun i _ ↦ (hf_memLp i).aestronglyMeasurable.enorm).pow_const (2 : ℝ)
    · refine Filter.liminf_le_of_frequently_le' ?_
      exact (Filter.Eventually.of_forall h_integral_partial).frequently
  have h_liminf_eq :
      (fun x : X ↦ Filter.liminf
          (fun N : ℕ ↦ (∑ i ∈ Finset.range N, ‖(s i).toSection x‖ₑ) ^ (2 : ℝ))
          Filter.atTop) =
        fun x : X ↦ (∑' i : ℕ, ‖(s i).toSection x‖ₑ) ^ (2 : ℝ) := by
    funext x
    have h_tsum :
        (∑' i : ℕ, ‖(s i).toSection x‖ₑ) =
          Filter.liminf
            (fun N : ℕ ↦ ∑ i ∈ Finset.range N, ‖(s i).toSection x‖ₑ)
            Filter.atTop := by
      rw [ENNReal.tsum_eq_liminf_sum_nat]
    rw [h_tsum]
    have h_rpow_mono := ENNReal.strictMono_rpow_of_pos (by norm_num : 0 < (2 : ℝ))
    have h_rpow_surj := (ENNReal.rpow_left_bijective (by norm_num : (2 : ℝ) ≠ 0)).2
    refine ((h_rpow_mono.orderIsoOfSurjective _ h_rpow_surj).liminf_apply ?_ ?_ ?_ ?_).symm
    all_goals isBoundedDefault
  have h_integral_tsum :
      ∫⁻ x, (∑' i : ℕ, ‖(s i).toSection x‖ₑ) ^ (2 : ℝ) ∂μ < (∞ : ℝ≥0∞) := by
    rw [← h_liminf_eq]
    exact lt_of_le_of_lt h_liminf_integral
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num : 0 ≤ (2 : ℝ)) hC_ne_top)
  have h_tsum_lt_top :
      ∀ᵐ x ∂μ, (∑' i : ℕ, ‖(s i).toSection x‖ₑ) < (∞ : ℝ≥0∞) := by
    have h_pow_ae :
        ∀ᵐ x ∂μ, ((∑' i : ℕ, ‖(s i).toSection x‖ₑ) ^ (2 : ℝ)) < (∞ : ℝ≥0∞) := by
      exact ae_lt_top'
        (by
          simpa [f] using
            ((AEMeasurable.tsum fun i ↦
              (hf_memLp i).aestronglyMeasurable.enorm).pow_const (2 : ℝ)))
        h_integral_tsum.ne
    refine h_pow_ae.mono fun x hx ↦ ?_
    rwa [← ENNReal.lt_rpow_inv_iff (by norm_num : 0 < (2 : ℝ)),
      ENNReal.top_rpow_of_pos (by norm_num : 0 < (2 : ℝ)⁻¹)] at hx
  refine h_tsum_lt_top.mono fun x hx ↦ ?_
  have hx_nn :
      Summable fun n : ℕ ↦ ‖(s n).toSection x‖₊ :=
    ENNReal.tsum_coe_ne_top_iff_summable.1 ?_
  · exact NNReal.summable_coe.2 hx_nn
  · simpa using hx.ne

/--
%%handwave
name:
  Fiberwise convergence gives total-space convergence
statement:
  If the finite fiberwise partial sums of a sequence of sections converge
  almost everywhere to a section in each fiber, then the associated total-space
  section maps converge almost everywhere in the bundle total space.
proof:
  For a fixed base point, the inclusion of the fiber into the total space is
  continuous in a vector bundle.  Composing the fiberwise convergence with this
  continuous map gives convergence in the total space.
-/
private theorem hilbertBundleSectionSeriesLimit_totalSpace_tendsto_ae
    {H X F : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    [SecondCountableTopology (Bundle.TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
    (G : HilbertBundleGeometry X F V)
    (hG_inner : ∀ (x : X) (v w : V x), G.fiberInner x v w = inner ℝ v w)
    (μ : Measure X) (s : ℕ → SquareIntegrableHilbertBundleSection G μ)
    (tSection : HilbertBundleSectionOnSurface X V)
    (hpoint_tendsto :
      ∀ᵐ x ∂μ,
        Filter.Tendsto
          (fun n : ℕ ↦
            (squareIntegrableHilbertBundleSectionFinsetSum
            (I := I) (G := G) hG_inner μ s (Finset.range n)).toSection x)
          Filter.atTop (𝓝 (tSection x))) :
    ∀ᵐ x ∂μ,
      Filter.Tendsto
        (fun n : ℕ ↦
          HilbertBundleSectionOnSurface.toTotalSpace (F := F)
            (squareIntegrableHilbertBundleSectionFinsetSum
            (I := I) (G := G) hG_inner μ s (Finset.range n)).toSection x)
        Filter.atTop
        (𝓝 (HilbertBundleSectionOnSurface.toTotalSpace (F := F) tSection x)) := by
  filter_upwards [hpoint_tendsto] with x hx
  change Filter.Tendsto
    (fun n : ℕ ↦ Bundle.TotalSpace.mk' F x
      ((squareIntegrableHilbertBundleSectionFinsetSum
            (I := I) (G := G) hG_inner μ s (Finset.range n)).toSection x))
    Filter.atTop
    (𝓝 (Bundle.TotalSpace.mk' F x (tSection x)))
  exact ((FiberBundle.totalSpaceMk_isInducing F V x).continuous.tendsto _).comp hx

/--
%%handwave
name:
  Uniform \(L^2\)-bound for representative partial sums
statement:
  If the \(L^2\)-norms of a sequence of square-integrable sections are
  summable, then the \(L^2\)-norms of all finite representative partial sums
  are bounded by a finite extended real constant.
proof:
  The class of a finite representative sum is the finite sum of the
  corresponding \(L^2\)-classes.  The norm of this finite sum is bounded by the
  finite sum of the term norms, and these finite sums are bounded by the full
  summable numerical series.
-/
private theorem l2HilbertBundle_partial_sum_norm_eLpNorm_bounded
    {H X F : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    [SecondCountableTopology (Bundle.TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
    (G : HilbertBundleGeometry X F V) (μ : Measure X)
    (hG_inner : ∀ (x : X) (v w : V x), G.fiberInner x v w = inner ℝ v w)
    (s : ℕ → SquareIntegrableHilbertBundleSection G μ)
    (hs : Summable (fun n ↦ squareIntegrableHilbertBundleSectionL2Norm G μ (s n))) :
    letI : NormedAddCommGroup (L2HilbertBundle G μ) :=
      l2HilbertBundleNormedAddCommGroup (I := I) (G := G) hG_inner μ
    ∃ C : ℝ≥0∞, C ≠ (∞ : ℝ≥0∞) ∧
      ∀ n : ℕ,
        eLpNorm
          (fun x : X ↦
            ‖(squareIntegrableHilbertBundleSectionFinsetSum
            (I := I) (G := G) hG_inner μ s (Finset.range n)).toSection x‖)
          2 μ ≤ C := by
  letI : NormedAddCommGroup (L2HilbertBundle G μ) :=
    l2HilbertBundleNormedAddCommGroup (I := I) (G := G) hG_inner μ
  let C : ℝ≥0∞ :=
    ∑' n : ℕ, ENNReal.ofReal (squareIntegrableHilbertBundleSectionL2Norm G μ (s n))
  have hnorm_nonneg :
      ∀ n : ℕ, 0 ≤ squareIntegrableHilbertBundleSectionL2Norm G μ (s n) := by
    intro n
    exact Real.sqrt_nonneg _
  have hC_ne_top : C ≠ (∞ : ℝ≥0∞) := by
    have hC_eq :
        C = ENNReal.ofReal
          (∑' n : ℕ, squareIntegrableHilbertBundleSectionL2Norm G μ (s n)) := by
      dsimp [C]
      rw [ENNReal.ofReal_tsum_of_nonneg hnorm_nonneg hs]
    rw [hC_eq]
    exact ENNReal.ofReal_ne_top
  refine ⟨C, hC_ne_top, ?_⟩
  intro n
  let p : SquareIntegrableHilbertBundleSection G μ :=
    squareIntegrableHilbertBundleSectionFinsetSum
            (I := I) (G := G) hG_inner μ s (Finset.range n)
  have hp_memLp :
      MemLp (fun x : X ↦ ‖p.toSection x‖) 2 μ :=
    squareIntegrableHilbertBundleSection_norm_memLp (I := I) (G := G) hG_inner μ p
  have hp_eLp :
      eLpNorm (fun x : X ↦ ‖p.toSection x‖) 2 μ =
        ENNReal.ofReal (squareIntegrableHilbertBundleSectionL2Norm G μ p) := by
    rw [← MeasureTheory.ofReal_lpNorm hp_memLp]
    congr 1
    exact (squareIntegrableHilbertBundleSectionL2Norm_eq_lpNorm_norm
            (I := I) (G := G) hG_inner μ p).symm
  have hp_norm_bound :
      squareIntegrableHilbertBundleSectionL2Norm G μ p ≤
        ∑ i ∈ Finset.range n, squareIntegrableHilbertBundleSectionL2Norm G μ (s i) := by
    calc
      squareIntegrableHilbertBundleSectionL2Norm G μ p =
          ‖(L2HilbertBundle.mk p : L2HilbertBundle G μ)‖ := rfl
      _ = ‖∑ i ∈ Finset.range n, L2HilbertBundle.mk (s i)‖ := by
            rw [l2HilbertBundle_mk_finset_sum
      (I := I) (G := G) (μ := μ) hG_inner s (Finset.range n)]
      _ ≤ ∑ i ∈ Finset.range n, ‖(L2HilbertBundle.mk (s i) : L2HilbertBundle G μ)‖ := by
            exact norm_sum_le _ _
      _ = ∑ i ∈ Finset.range n, squareIntegrableHilbertBundleSectionL2Norm G μ (s i) := by
            rfl
  calc
    eLpNorm
        (fun x : X ↦
          ‖(squareIntegrableHilbertBundleSectionFinsetSum
            (I := I) (G := G) hG_inner μ s (Finset.range n)).toSection x‖)
        2 μ =
        ENNReal.ofReal (squareIntegrableHilbertBundleSectionL2Norm G μ p) := by
          simpa [p] using hp_eLp
    _ ≤ ENNReal.ofReal
          (∑ i ∈ Finset.range n, squareIntegrableHilbertBundleSectionL2Norm G μ (s i)) := by
          exact ENNReal.ofReal_le_ofReal hp_norm_bound
    _ = ∑ i ∈ Finset.range n,
          ENNReal.ofReal (squareIntegrableHilbertBundleSectionL2Norm G μ (s i)) := by
          rw [ENNReal.ofReal_sum_of_nonneg]
          intro i _
          exact hnorm_nonneg i
    _ ≤ C := by
          exact ENNReal.sum_le_tsum (Finset.range n)

/--
%%handwave
name:
  Absolutely summable representative series have \(L^2\)-tail limits
statement:
  If the \(L^2\)-norms of a sequence of square-integrable bundle sections are
  summable, then there is a square-integrable limit section such that the
  \(L^2\)-norms of the tails of the finite partial sums tend to zero.
proof:
  The preceding Cauchy estimate gives uniform \(L^2\)-control of the tails.
  From the summability of the scalar norms, the pointwise series of fiber
  norms is finite almost everywhere.  On that full-measure set the partial
  sums are Cauchy in each fiber, hence converge by fiber completeness.  The
  resulting section is measurable as an almost-everywhere limit of measurable
  partial sums, and Fatou's lemma together with the tail estimates gives
  square-integrability and convergence of the \(L^2\)-tail norms to zero.
-/
private theorem l2HilbertBundle_representative_summable_series_tail_norm_tendsto
    {H X F : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    [SecondCountableTopology (Bundle.TotalSpace F V)]
    [TopologicalSpace.PseudoMetrizableSpace (Bundle.TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [∀ x, CompleteSpace (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
    (G : HilbertBundleGeometry X F V) (μ : Measure X)
    (hG_inner : ∀ (x : X) (v w : V x), G.fiberInner x v w = inner ℝ v w) :
    letI : NormedAddCommGroup (L2HilbertBundle G μ) :=
      l2HilbertBundleNormedAddCommGroup (I := I) (G := G) hG_inner μ
    ∀ s : ℕ → SquareIntegrableHilbertBundleSection G μ,
      Summable (fun n ↦ squareIntegrableHilbertBundleSectionL2Norm G μ (s n)) →
        ∃ t : SquareIntegrableHilbertBundleSection G μ,
          Filter.Tendsto
            (fun n : ℕ ↦
              ‖(∑ i ∈ Finset.range n, L2HilbertBundle.mk (s i)) -
                L2HilbertBundle.mk t‖)
            Filter.atTop (𝓝 0) := by
  letI : NormedAddCommGroup (L2HilbertBundle G μ) :=
    l2HilbertBundleNormedAddCommGroup (I := I) (G := G) hG_inner μ
  intro s hs
  have h_cauchy :
      CauchySeq
        (fun n : ℕ ↦ ∑ i ∈ Finset.range n, L2HilbertBundle.mk (s i)) :=
    l2HilbertBundle_representative_summable_series_partial_sums_cauchy
      (I := I) (G := G) (μ := μ) hG_inner s hs
  have hpoint :
      ∀ᵐ x ∂μ, Summable fun n : ℕ ↦ ‖(s n).toSection x‖ := by
    exact l2HilbertBundle_pointwise_norm_series_summable_ae
      (I := I) (G := G) (μ := μ) hG_inner s hs
  let tSection : HilbertBundleSectionOnSurface X V :=
    hilbertBundleSectionSeriesLimit (I := I) (G := G) μ s
  have hpoint_tendsto :
      ∀ᵐ x ∂μ,
        Filter.Tendsto
          (fun n : ℕ ↦
            (squareIntegrableHilbertBundleSectionFinsetSum
            (I := I) (G := G) hG_inner μ s (Finset.range n)).toSection x)
          Filter.atTop (𝓝 (tSection x)) := by
    simpa [tSection] using
      hilbertBundleSectionSeriesLimit_tendsto_ae
      (I := I) (G := G) hG_inner μ s hpoint
  have htotal_tendsto :
      ∀ᵐ x ∂μ,
        Filter.Tendsto
          (fun n : ℕ ↦
            HilbertBundleSectionOnSurface.toTotalSpace (F := F)
              (squareIntegrableHilbertBundleSectionFinsetSum
            (I := I) (G := G) hG_inner μ s (Finset.range n)).toSection x)
          Filter.atTop
          (𝓝 (HilbertBundleSectionOnSurface.toTotalSpace (F := F) tSection x)) :=
    hilbertBundleSectionSeriesLimit_totalSpace_tendsto_ae
      (I := I) (G := G) hG_inner μ s tSection hpoint_tendsto
  have ht_aemeasurable :
      AEMeasurable
        (HilbertBundleSectionOnSurface.toTotalSpace (F := F) tSection) μ := by
    refine aemeasurable_of_tendsto_metrizable_ae Filter.atTop ?_ htotal_tendsto
    intro n
    exact (squareIntegrableHilbertBundleSectionFinsetSum
            (I := I) (G := G) hG_inner μ s (Finset.range n)).memL2.aemeasurable
  rcases l2HilbertBundle_partial_sum_norm_eLpNorm_bounded
      (I := I) (G := G) (μ := μ) hG_inner s hs with ⟨C, hC_ne_top, hC_bound⟩
  have hnorm_tendsto :
      ∀ᵐ x ∂μ,
        Filter.Tendsto
          (fun n : ℕ ↦
            ‖(squareIntegrableHilbertBundleSectionFinsetSum
            (I := I) (G := G) hG_inner μ s (Finset.range n)).toSection x‖)
          Filter.atTop (𝓝 ‖tSection x‖) := by
    filter_upwards [hpoint_tendsto] with x hx
    exact tendsto_norm.comp hx
  have ht_norm_eLp_bound :
      eLpNorm (fun x : X ↦ ‖tSection x‖) 2 μ ≤ C := by
    exact MeasureTheory.Lp.eLpNorm_le_of_ae_tendsto
      (u := Filter.atTop)
      (bound := Filter.Eventually.of_forall hC_bound)
      (fun n ↦
        (squareIntegrableHilbertBundleSection_norm_memLp
      (I := I) (G := G) hG_inner μ
          (squareIntegrableHilbertBundleSectionFinsetSum
            (I := I) (G := G) hG_inner μ s (Finset.range n))).aestronglyMeasurable)
      hnorm_tendsto
  have hG_norm : ∀ (x : X) (v : V x), G.fiberNormSq x v = ‖v‖ ^ 2 := by
    intro x v
    rw [G.fiberNormSq_eq_inner, hG_inner]
    exact real_inner_self_eq_norm_sq v
  have ht_normSq_aemeas :
      AEMeasurable (fun x : X ↦ G.fiberNormSq x (tSection x)) μ :=
    hilbertBundleSection_aemeasurable_normSq (I := I) (G := G) hG_inner μ ht_aemeasurable
  have ht_norm_ae :
      (fun x : X ↦ √(G.fiberNormSq x (tSection x))) =ᵐ[μ]
        fun x : X ↦ ‖tSection x‖ := by
    filter_upwards [] with x
    rw [hG_norm x (tSection x), Real.sqrt_sq (norm_nonneg _)]
  have ht_norm_aestrongly :
      AEStronglyMeasurable (fun x : X ↦ ‖tSection x‖) μ := by
    have hsqrt_aestr :
        AEStronglyMeasurable (fun x : X ↦ √(G.fiberNormSq x (tSection x))) μ :=
      ht_normSq_aemeas.sqrt.aestronglyMeasurable
    exact (aestronglyMeasurable_congr ht_norm_ae).1 hsqrt_aestr
  have ht_norm_memLp :
      MemLp (fun x : X ↦ ‖tSection x‖) 2 μ := by
    refine ⟨ht_norm_aestrongly, ?_⟩
    exact lt_of_le_of_lt ht_norm_eLp_bound (lt_top_iff_ne_top.2 hC_ne_top)
  have ht_integrable_norm_sq :
      Integrable (fun x : X ↦ ‖tSection x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq ht_norm_aestrongly).1 ht_norm_memLp
  have ht_memL2 : HilbertBundleSectionMemL2 G μ tSection := by
    refine ⟨ht_aemeasurable, ?_⟩
    refine ht_integrable_norm_sq.congr ?_
    filter_upwards [] with x
    rw [hG_norm x (tSection x)]
  have hmk_partial :
      ∀ n : ℕ,
        L2HilbertBundle.mk
            (squareIntegrableHilbertBundleSectionFinsetSum
            (I := I) (G := G) hG_inner μ s (Finset.range n)) =
          ∑ i ∈ Finset.range n, L2HilbertBundle.mk (s i) := by
    intro n
    exact l2HilbertBundle_mk_finset_sum
      (I := I) (G := G) (μ := μ) hG_inner s (Finset.range n)
  have htail :
      ∃ ht : HilbertBundleSectionMemL2 G μ tSection,
        Filter.Tendsto
          (fun n : ℕ ↦
            ‖(∑ i ∈ Finset.range n, L2HilbertBundle.mk (s i)) -
              L2HilbertBundle.mk
                ({ toSection := tSection, memL2 := ht } :
                  SquareIntegrableHilbertBundleSection G μ)‖)
          Filter.atTop (𝓝 0) := by
    refine ⟨ht_memL2, ?_⟩
    let t : SquareIntegrableHilbertBundleSection G μ :=
      { toSection := tSection, memL2 := ht_memL2 }
    change
      Filter.Tendsto
        (fun n : ℕ ↦
          ‖(∑ i ∈ Finset.range n, L2HilbertBundle.mk (s i)) -
            L2HilbertBundle.mk t‖)
        Filter.atTop (𝓝 0)
    let P : ℕ → SquareIntegrableHilbertBundleSection G μ := fun n ↦
      squareIntegrableHilbertBundleSectionFinsetSum
            (I := I) (G := G) hG_inner μ s (Finset.range n)
    let q : ℕ → L2HilbertBundle G μ := fun n ↦
      ∑ i ∈ Finset.range n, L2HilbertBundle.mk (s i)
    let diff : ℕ → ℕ → SquareIntegrableHilbertBundleSection G μ := fun n m ↦
      squareIntegrableHilbertBundleSectionSub (I := I) (G := G) hG_inner μ (P n) (P m)
    let diffT : ℕ → SquareIntegrableHilbertBundleSection G μ := fun n ↦
      squareIntegrableHilbertBundleSectionSub (I := I) (G := G) hG_inner μ (P n) t
    have hP_mk : ∀ n : ℕ, L2HilbertBundle.mk (P n) = q n := by
      intro n
      simpa [P, q] using hmk_partial n
    have hdiff_mk :
        ∀ n m : ℕ, L2HilbertBundle.mk (diff n m) = q n - q m := by
      intro n m
      calc
        L2HilbertBundle.mk (diff n m) =
            L2HilbertBundle.mk (P n) - L2HilbertBundle.mk (P m) := by
              simpa [diff] using
                l2HilbertBundle_mk_sub
                  (I := I) (G := G) (μ := μ) hG_inner (P n) (P m)
        _ = q n - q m := by rw [hP_mk n, hP_mk m]
    have hdiffT_mk :
        ∀ n : ℕ, L2HilbertBundle.mk (diffT n) = q n - L2HilbertBundle.mk t := by
      intro n
      calc
        L2HilbertBundle.mk (diffT n) =
            L2HilbertBundle.mk (P n) - L2HilbertBundle.mk t := by
              simpa [diffT] using
                l2HilbertBundle_mk_sub
                  (I := I) (G := G) (μ := μ) hG_inner (P n) t
        _ = q n - L2HilbertBundle.mk t := by rw [hP_mk n]
    have hq_cauchy : CauchySeq q := by
      simpa [q] using h_cauchy
    rcases cauchySeq_iff_le_tendsto_0.1 hq_cauchy with
      ⟨b, hb_nonneg, hb_bound, hb_tendsto⟩
    have hlimit_eLp_bound :
        ∀ n N : ℕ, N ≤ n →
          eLpNorm (fun x : X ↦ ‖(diffT n).toSection x‖) (2 : ℝ≥0∞) μ ≤
            ENNReal.ofReal (b N) := by
      intro n N hNn
      have hbound_eventual :
          ∀ᶠ m in Filter.atTop,
            eLpNorm (fun x : X ↦ ‖(diff n m).toSection x‖) (2 : ℝ≥0∞) μ ≤
              ENNReal.ofReal (b N) := by
        filter_upwards [Filter.eventually_ge_atTop N] with m hmN
        have hq_norm : ‖q n - q m‖ ≤ b N := by
          simpa [dist_eq_norm] using hb_bound n m N hNn hmN
        have hdiff_norm : ‖L2HilbertBundle.mk (diff n m)‖ ≤ b N := by
          calc
            ‖L2HilbertBundle.mk (diff n m)‖ = ‖q n - q m‖ := by
              rw [hdiff_mk n m]
            _ ≤ b N := hq_norm
        calc
          eLpNorm (fun x : X ↦ ‖(diff n m).toSection x‖) (2 : ℝ≥0∞) μ =
              ENNReal.ofReal
                (squareIntegrableHilbertBundleSectionL2Norm G μ (diff n m)) := by
                exact squareIntegrableHilbertBundleSection_eLpNorm_norm_eq_ofReal_l2Norm
                  (I := I) (G := G) hG_inner μ (diff n m)
          _ = ENNReal.ofReal ‖L2HilbertBundle.mk (diff n m)‖ := rfl
          _ ≤ ENNReal.ofReal (b N) := ENNReal.ofReal_le_ofReal hdiff_norm
      have hdiff_tendsto :
          ∀ᵐ x ∂μ,
            Filter.Tendsto
              (fun m : ℕ ↦ ‖(diff n m).toSection x‖)
              Filter.atTop (𝓝 ‖(diffT n).toSection x‖) := by
        filter_upwards [hpoint_tendsto] with x hx
        have hxP :
            Filter.Tendsto (fun m : ℕ ↦ (P m).toSection x)
              Filter.atTop (𝓝 (tSection x)) := by
          simpa [P] using hx
        have hxdiff :
            Filter.Tendsto
              (fun m : ℕ ↦ (P n).toSection x + -((P m).toSection x))
              Filter.atTop (𝓝 ((P n).toSection x + -(tSection x))) :=
          tendsto_const_nhds.add hxP.neg
        simpa [diff, diffT, squareIntegrableHilbertBundleSectionSub, t]
          using hxdiff.norm
      exact MeasureTheory.Lp.eLpNorm_le_of_ae_tendsto
        (u := Filter.atTop)
        (bound := hbound_eventual)
        (fun m ↦
          (squareIntegrableHilbertBundleSection_norm_memLp
      (I := I) (G := G) hG_inner μ (diff n m)).aestronglyMeasurable)
        hdiff_tendsto
    have htail_bound :
        ∀ n N : ℕ, N ≤ n → ‖q n - L2HilbertBundle.mk t‖ ≤ b N := by
      intro n N hNn
      have hnorm_eq :
          squareIntegrableHilbertBundleSectionL2Norm G μ (diffT n) =
            ‖q n - L2HilbertBundle.mk t‖ := by
        calc
          squareIntegrableHilbertBundleSectionL2Norm G μ (diffT n) =
              ‖L2HilbertBundle.mk (diffT n)‖ := rfl
          _ = ‖q n - L2HilbertBundle.mk t‖ := by rw [hdiffT_mk n]
      have hnorm_enn :
          ENNReal.ofReal ‖q n - L2HilbertBundle.mk t‖ ≤ ENNReal.ofReal (b N) := by
        calc
          ENNReal.ofReal ‖q n - L2HilbertBundle.mk t‖ =
              eLpNorm (fun x : X ↦ ‖(diffT n).toSection x‖) (2 : ℝ≥0∞) μ := by
                rw [← hnorm_eq]
                exact
                  (squareIntegrableHilbertBundleSection_eLpNorm_norm_eq_ofReal_l2Norm
                    (I := I) (G := G) hG_inner μ (diffT n)).symm
          _ ≤ ENNReal.ofReal (b N) := hlimit_eLp_bound n N hNn
      exact (ENNReal.ofReal_le_ofReal_iff (hb_nonneg N)).1 hnorm_enn
    have htend_q :
        Filter.Tendsto
          (fun n : ℕ ↦ ‖q n - L2HilbertBundle.mk t‖)
          Filter.atTop (𝓝 0) :=
      squeeze_zero
        (fun n : ℕ ↦ norm_nonneg (q n - L2HilbertBundle.mk t))
        (fun n : ℕ ↦ htail_bound n n le_rfl) hb_tendsto
    simpa [q] using htend_q
  rcases htail with ⟨ht_mem, ht_tendsto⟩
  exact ⟨⟨tSection, ht_mem⟩, ht_tendsto⟩

/--
%%handwave
name:
  Absolutely summable series of representatives have \(L^2\)-limits
statement:
  For a continuous Hilbert bundle with complete fibers, any series of
  square-integrable representatives whose \(L^2\)-norms are summable has a
  limit in the quotient \(L^2\)-space.
proof:
  The summability of the \(L^2\)-norms implies that the pointwise series of
  fiber norms is finite almost everywhere.  Since the fibers are complete, the
  pointwise series converges almost everywhere in the corresponding fiber.  The
  limit section is measurable as an almost-everywhere limit of measurable
  partial sums and is square-integrable by the usual Fatou and tail estimates.
  These tail estimates give convergence of the partial sums in \(L^2\).
-/
private theorem l2HilbertBundle_representative_summable_series_tendsto
    {H X F : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    [SecondCountableTopology (Bundle.TotalSpace F V)]
    [TopologicalSpace.PseudoMetrizableSpace (Bundle.TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [∀ x, CompleteSpace (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
    (G : HilbertBundleGeometry X F V) (μ : Measure X)
    (hG_inner : ∀ (x : X) (v w : V x), G.fiberInner x v w = inner ℝ v w) :
    letI : NormedAddCommGroup (L2HilbertBundle G μ) :=
      l2HilbertBundleNormedAddCommGroup (I := I) (G := G) hG_inner μ
    ∀ s : ℕ → SquareIntegrableHilbertBundleSection G μ,
      Summable (fun n ↦ squareIntegrableHilbertBundleSectionL2Norm G μ (s n)) →
        ∃ a : L2HilbertBundle G μ,
          Filter.Tendsto
            (fun n : ℕ ↦ ∑ i ∈ Finset.range n, L2HilbertBundle.mk (s i))
            Filter.atTop (𝓝 a) := by
  letI : NormedAddCommGroup (L2HilbertBundle G μ) :=
    l2HilbertBundleNormedAddCommGroup (I := I) (G := G) hG_inner μ
  intro s hs
  rcases l2HilbertBundle_representative_summable_series_tail_norm_tendsto
      (I := I) (G := G) (μ := μ) hG_inner s hs with ⟨t, ht⟩
  exact ⟨L2HilbertBundle.mk t, tendsto_iff_norm_sub_tendsto_zero.2 ht⟩

/--
%%handwave
name:
  Absolutely summable series of \(L^2\)-sections converge
statement:
  In the canonical \(L^2\)-norm on square-integrable sections of a continuous
  Hilbert bundle with complete fibers, every series whose \(L^2\)-norms are
  summable has an \(L^2\)-limit.
proof:
  Choose a representative of each \(L^2\)-class and apply the representative
  series convergence theorem.  Since the quotient norm is the representative
  \(L^2\)-norm, the summability hypothesis transfers to the chosen
  representatives, and their partial sums represent the original partial sums.
-/
private theorem l2HilbertBundle_summable_series_tendsto
    {H X F : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    [SecondCountableTopology (Bundle.TotalSpace F V)]
    [TopologicalSpace.PseudoMetrizableSpace (Bundle.TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [∀ x, CompleteSpace (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
    (G : HilbertBundleGeometry X F V) (μ : Measure X)
    (hG_inner : ∀ (x : X) (v w : V x), G.fiberInner x v w = inner ℝ v w) :
    letI : NormedAddCommGroup (L2HilbertBundle G μ) :=
      l2HilbertBundleNormedAddCommGroup (I := I) (G := G) hG_inner μ
    ∀ u : ℕ → L2HilbertBundle G μ,
      Summable (fun n ↦ ‖u n‖) →
        ∃ a : L2HilbertBundle G μ,
          Filter.Tendsto (fun n : ℕ ↦ ∑ i ∈ Finset.range n, u i) Filter.atTop (𝓝 a) := by
  letI : NormedAddCommGroup (L2HilbertBundle G μ) :=
    l2HilbertBundleNormedAddCommGroup (I := I) (G := G) hG_inner μ
  intro u hu
  let s : ℕ → SquareIntegrableHilbertBundleSection G μ := fun n ↦ Quotient.out (u n)
  have hs_mk : ∀ n : ℕ, L2HilbertBundle.mk (s n) = u n := by
    intro n
    exact Quotient.out_eq (u n)
  have hs_norm :
      (fun n : ℕ ↦ squareIntegrableHilbertBundleSectionL2Norm G μ (s n)) =
        fun n : ℕ ↦ ‖u n‖ := by
    funext n
    rw [← hs_mk n]
    rfl
  have hs_sum :
      Summable (fun n : ℕ ↦ squareIntegrableHilbertBundleSectionL2Norm G μ (s n)) := by
    simpa [hs_norm] using hu
  rcases l2HilbertBundle_representative_summable_series_tendsto
      (I := I) (G := G) (μ := μ) hG_inner s hs_sum with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  convert ha using 1
  ext n
  exact Finset.sum_congr rfl (fun i _ ↦ (hs_mk i).symm)

/--
%%handwave
name:
  Completeness of \(L^2\)-sections as the analytic core
statement:
  For a continuous Hilbert bundle with complete fibers, the canonical
  \(L^2\)-norm on square-integrable sections is complete.
proof:
  Apply the standard completeness criterion for normed additive groups:
  completeness follows once every absolutely summable series converges.
-/
theorem l2HilbertBundle_completeSpace_core
    {H X F : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    [SecondCountableTopology (Bundle.TotalSpace F V)]
    [TopologicalSpace.PseudoMetrizableSpace (Bundle.TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [∀ x, CompleteSpace (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
    (G : HilbertBundleGeometry X F V) (μ : Measure X)
    (hG_inner : ∀ (x : X) (v w : V x), G.fiberInner x v w = inner ℝ v w) :
    letI : NormedAddCommGroup (L2HilbertBundle G μ) :=
      l2HilbertBundleNormedAddCommGroup (I := I) (G := G) hG_inner μ
    CompleteSpace (L2HilbertBundle G μ) := by
  letI : NormedAddCommGroup (L2HilbertBundle G μ) :=
    l2HilbertBundleNormedAddCommGroup (I := I) (G := G) hG_inner μ
  exact NormedAddCommGroup.completeSpace_of_summable_imp_tendsto
    (l2HilbertBundle_summable_series_tendsto
      (G := G) (μ := μ) (hG_inner := hG_inner))

/--
%%handwave
name:
  Completeness of \(L^2\)-sections of a Hilbert bundle with complete fibers
statement:
  If the fibers of a continuous Hilbert bundle are complete, then the
  canonical normed space of \(L^2\)-sections is complete.
proof:
  A Cauchy sequence of \(L^2\)-classes is locally represented in bundle
  trivializations by Cauchy sequences of Hilbert-valued \(L^2\) functions.
  Completeness of the model Hilbert space gives local limits; compatibility
  of transition maps glues these limits to a measurable square-integrable
  section representing the global limit.
-/
theorem l2HilbertBundle_completeSpace_of_complete_fibers
    {H X F : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    [SecondCountableTopology (Bundle.TotalSpace F V)]
    [TopologicalSpace.PseudoMetrizableSpace (Bundle.TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [∀ x, CompleteSpace (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
    (G : HilbertBundleGeometry X F V) (μ : Measure X)
    (hG_inner : ∀ (x : X) (v w : V x), G.fiberInner x v w = inner ℝ v w) :
    ∃ (_ : NormedAddCommGroup (L2HilbertBundle G μ)),
      ∃ (_ : InnerProductSpace ℝ (L2HilbertBundle G μ)),
        Nonempty (CompleteSpace (L2HilbertBundle G μ)) := by
  let instNormed : NormedAddCommGroup (L2HilbertBundle G μ) :=
    l2HilbertBundleNormedAddCommGroup (I := I) (G := G) hG_inner μ
  letI : NormedAddCommGroup (L2HilbertBundle G μ) := instNormed
  let instInner : InnerProductSpace ℝ (L2HilbertBundle G μ) :=
    l2HilbertBundleInnerProductSpace (I := I) (G := G) (μ := μ) hG_inner
  letI : InnerProductSpace ℝ (L2HilbertBundle G μ) := instInner
  let instComplete : CompleteSpace (L2HilbertBundle G μ) :=
    l2HilbertBundle_completeSpace_core (I := I) (G := G) (μ := μ) hG_inner
  exact ⟨instNormed, instInner, ⟨instComplete⟩⟩

/--
%%handwave
name:
  \(L^2\)-sections of a Hilbert bundle admit a complete structure
statement:
  If the fibers of a continuous Hilbert bundle are complete, then the space
  of square-integrable sections admits its canonical normed inner-product
  structure and is complete for the associated metric.
proof:
  The norm and inner product are the canonical \(L^2\) ones, and completeness
  is the standard completeness theorem for square-integrable sections of a
  measurable field of complete Hilbert spaces.
-/
theorem l2HilbertBundle_admits_complete_space
    {H X F : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    [SecondCountableTopology (Bundle.TotalSpace F V)]
    [TopologicalSpace.PseudoMetrizableSpace (Bundle.TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [∀ x, CompleteSpace (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
    (G : HilbertBundleGeometry X F V) (μ : Measure X)
    (hG_inner : ∀ (x : X) (v w : V x), G.fiberInner x v w = inner ℝ v w) :
    ∃ (_ : NormedAddCommGroup (L2HilbertBundle G μ)),
      ∃ (_ : InnerProductSpace ℝ (L2HilbertBundle G μ)),
        Nonempty (CompleteSpace (L2HilbertBundle G μ)) := by
  exact l2HilbertBundle_completeSpace_of_complete_fibers
      (I := I) (G := G) (μ := μ) hG_inner

/--
%%handwave
name:
  \(L^2\)-sections of a Hilbert bundle form a Hilbert space
statement:
  For a continuous real Hilbert vector bundle over a measured surface, the
  space of square-integrable sections modulo almost-everywhere equality is a
  real Hilbert space.
proof:
  The inner product is obtained by integrating the fiberwise inner product.
  Completeness follows from the usual \(L^2\) completeness theorem for
  measurable fields of Hilbert spaces, using the continuous local
  trivializations of the bundle.
-/
theorem l2HilbertBundle_admits_hilbert_structure
    {H X F : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    [SecondCountableTopology (Bundle.TotalSpace F V)]
    [TopologicalSpace.PseudoMetrizableSpace (Bundle.TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [∀ x, CompleteSpace (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]
    (G : HilbertBundleGeometry X F V)
    (hG_inner : ∀ (x : X) (v w : V x), G.fiberInner x v w = inner ℝ v w)
    (μ : Measure X) :
    AdmitsRealHilbertStructure (L2HilbertBundle G μ) := by
  rcases l2HilbertBundle_admits_complete_space
      (I := I) (G := G) (μ := μ) hG_inner with
    ⟨instNormed, instInner, ⟨instComplete⟩⟩
  letI : NormedAddCommGroup (L2HilbertBundle G μ) := instNormed
  letI : InnerProductSpace ℝ (L2HilbertBundle G μ) := instInner
  letI : CompleteSpace (L2HilbertBundle G μ) := instComplete
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  exact ⟨HilbertSpace.mk⟩

/--
%%handwave
name:
  \(L^2\)-sections of a trivial Hilbert bundle form a Hilbert space
statement:
  The square-integrable sections of the trivial bundle with fiber a real
  Hilbert space form a real Hilbert space.
proof:
  This is the standard Hilbert-space theorem for Hilbert-valued
  square-integrable functions, transported through the trivial-bundle
  identification.
-/
theorem surfaceValueL2Sections_admit_hilbert_structure
    {X E : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X]
    [IsManifold SurfaceRealModel 1 X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology (Bundle.TotalSpace E (Bundle.Trivial X E))]
    [TopologicalSpace.PseudoMetrizableSpace (Bundle.TotalSpace E (Bundle.Trivial X E))]
    (μ : Measure X) :
    AdmitsRealHilbertStructure (SurfaceValueL2Section (X := X) (E := E) μ) := by
  exact l2HilbertBundle_admits_hilbert_structure
    (I := SurfaceRealModel) (G := trivialHilbertBundleGeometryOnSurface X E)
    (μ := μ) (by intro x v w; rfl)

/--
%%handwave
name:
  \(L^2\)-sections of a trivial Hilbert bundle over a manifold form a
  Hilbert space
statement:
  On a finite-dimensional smooth manifold, the square-integrable sections of
  the trivial bundle with fiber a complete real Hilbert space form a real
  Hilbert space.
proof:
  This is the standard Hilbert-space theorem for Hilbert-valued
  square-integrable functions, transported through the trivial-bundle
  identification.
-/
theorem manifoldValueL2Sections_admit_hilbert_structure
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology (Bundle.TotalSpace E (Bundle.Trivial X E))]
    [TopologicalSpace.PseudoMetrizableSpace (Bundle.TotalSpace E (Bundle.Trivial X E))]
    (μ : Measure X) :
    AdmitsRealHilbertStructure (ValueL2Section (X := X) (E := E) μ) := by
  exact l2HilbertBundle_admits_hilbert_structure
    (I := I) (G := trivialHilbertBundleGeometry X E)
    (μ := μ) (by intro x v w; rfl)

/--
%%handwave
name:
  Canonical normed group structure on Hilbert-valued \(L^2\)-sections
statement:
  The quotient of square-integrable sections of the trivial Hilbert bundle is
  equipped with the norm induced by the representative \(L^2\)-norm.
-/
@[reducible] noncomputable def valueL2SectionNormedAddCommGroup
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology (Bundle.TotalSpace E (Bundle.Trivial X E))]
    (μ : Measure X) :
    NormedAddCommGroup (ValueL2Section (X := X) (E := E) μ) :=
  l2HilbertBundleNormedAddCommGroup
    (I := I) (G := trivialHilbertBundleGeometry X E)
    (fun _ _ _ ↦ rfl) μ

/--
%%handwave
name:
  Distance between represented value sections
statement:
  For two square-integrable Hilbert-valued maps (w_1,w_2), the extended distance between their \(L^2\) classes is \(\operatorname{ofReal}|w_1-w_2|_{L^2}\).
proof:
  Express distance as the norm of the difference class and use the representative and norm formulas.
-/
private theorem valueL2Section_edist_mk_eq_ofReal_l2Norm_sub
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology (Bundle.TotalSpace E (Bundle.Trivial X E))]
    (μ : Measure X)
    (w₁ w₂ : SquareIntegrableValueSection (X := X) (E := E) μ) :
    letI : NormedAddCommGroup (ValueL2Section (X := X) (E := E) μ) :=
      valueL2SectionNormedAddCommGroup (I := I) (X := X) (E := E) μ
    edist
        (Quotient.mk
          (SquareIntegrableValueSection.aeSetoid
            (X := X) (E := E) (μ := μ)) w₁ :
          ValueL2Section (X := X) (E := E) μ)
        (Quotient.mk
          (SquareIntegrableValueSection.aeSetoid
            (X := X) (E := E) (μ := μ)) w₂ :
          ValueL2Section (X := X) (E := E) μ) =
      ENNReal.ofReal
        (squareIntegrableHilbertBundleSectionL2Norm
          (trivialHilbertBundleGeometry X E) μ
          (squareIntegrableHilbertBundleSectionSub
            (I := I) (G := trivialHilbertBundleGeometry X E)
            (fun _ _ _ ↦ rfl) μ w₁ w₂)) := by
  letI : NormedAddCommGroup (ValueL2Section (X := X) (E := E) μ) :=
    valueL2SectionNormedAddCommGroup (I := I) (X := X) (E := E) μ
  rw [edist_eq_enorm_sub]
  rw [← l2HilbertBundle_mk_sub
    (I := I) (G := trivialHilbertBundleGeometry X E)
    (μ := μ) (fun _ _ _ ↦ rfl) w₁ w₂]
  rw [← ofReal_norm]
  rfl

/--
%%handwave
name:
  \(L^2\)-convergence of value representatives gives quotient convergence
statement:
  If square-integrable trivial-bundle representatives \(u_i\) satisfy
  \(\|u_i-u\|_{L^2}\to0\), then their classes converge to the class of \(u\)
  in the intrinsic \(L^2\)-section space.
proof:
  The quotient distance between two representatives is exactly the
  \(L^2\)-norm of their pointwise difference.  Rewriting convergence to the
  limiting class in terms of this distance gives the result.
-/
theorem valueL2Section_tendsto_of_eLpNorm_sub_tendsto_zero
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology (Bundle.TotalSpace E (Bundle.Trivial X E))]
    (μ : Measure X) :
    letI : NormedAddCommGroup (ValueL2Section (X := X) (E := E) μ) :=
      valueL2SectionNormedAddCommGroup (I := I) (X := X) (E := E) μ
    ∀ {ι : Type} {l : Filter ι} [l.NeBot]
      {u : ι → SquareIntegrableValueSection (X := X) (E := E) μ}
      {uLim : SquareIntegrableValueSection (X := X) (E := E) μ},
      Filter.Tendsto
        (fun i ↦ eLpNorm
          (fun x : X ↦ (u i).toFunction x - uLim.toFunction x) 2 μ)
        l (𝓝 0) →
      Filter.Tendsto
        (fun i ↦
          (Quotient.mk
            (SquareIntegrableValueSection.aeSetoid
              (X := X) (E := E) (μ := μ)) (u i) :
            ValueL2Section (X := X) (E := E) μ))
        l
        (𝓝
          (Quotient.mk
            (SquareIntegrableValueSection.aeSetoid
              (X := X) (E := E) (μ := μ)) uLim :
            ValueL2Section (X := X) (E := E) μ)) := by
  letI : NormedAddCommGroup (ValueL2Section (X := X) (E := E) μ) :=
    valueL2SectionNormedAddCommGroup (I := I) (X := X) (E := E) μ
  intro ι l hne u uLim hconv
  rw [tendsto_iff_edist_tendsto_0]
  refine hconv.congr' ?_
  filter_upwards [] with i
  let wdiff : SquareIntegrableValueSection (X := X) (E := E) μ :=
    squareIntegrableHilbertBundleSectionSub
      (I := I) (G := trivialHilbertBundleGeometry X E)
      (fun _ _ _ ↦ rfl) μ (u i) uLim
  have hwdiff_fun :
      wdiff.toFunction =
        fun x : X ↦ (u i).toFunction x - uLim.toFunction x := by
    funext x
    simp [wdiff, squareIntegrableHilbertBundleSectionSub,
      SquareIntegrableValueSection.toFunction, sub_eq_add_neg]
  have hwdiff_eLp :
      eLpNorm (fun x : X ↦ (u i).toFunction x - uLim.toFunction x) 2 μ =
        ENNReal.ofReal
          (squareIntegrableHilbertBundleSectionL2Norm
            (trivialHilbertBundleGeometry X E) μ wdiff) := by
    rw [← hwdiff_fun]
    rw [← eLpNorm_norm wdiff.toFunction]
    simpa [SquareIntegrableValueSection.toFunction] using
      squareIntegrableHilbertBundleSection_eLpNorm_norm_eq_ofReal_l2Norm
        (I := I) (G := trivialHilbertBundleGeometry X E)
        (fun _ _ _ ↦ rfl) μ wdiff
  rw [hwdiff_eLp]
  exact
    (valueL2Section_edist_mk_eq_ofReal_l2Norm_sub
      (I := I) (X := X) (E := E) μ (u i) uLim).symm

/--
%%handwave
name:
  Hilbert structure on \(L^2\) differential sections
statement:
  A continuous Hilbert metric on the differential bundle induces a real Hilbert-space structure on its \(L^2\)-sections.
proof:
  Apply the Hilbert-space construction for \(L^2\)-sections of a continuous Hilbert bundle to the metric-induced fiber inner products.
-/
theorem manifoldDifferentialL2Sections_admit_hilbert_structure_of_metric
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := I) X E)]
    [TopologicalSpace.PseudoMetrizableSpace (ManifoldDifferentialTotalSpace (I := I) X E)]
    (metric : Bundle.ContinuousRiemannianMetric (H →L[ℝ] E)
      (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E)))
    (μ : Measure X) :
    AdmitsRealHilbertStructure
      (L2HilbertBundle
        (manifoldDifferentialHilbertBundleGeometryOfMetric
          (I := I) (X := X) (E := E) metric) μ) := by
  letI : Bundle.RiemannianBundle
      (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E)) :=
    ⟨metric.toRiemannianMetric⟩
  letI (x : X) :
      TopologicalSpace (ManifoldDifferentialBundleFiber
        (I := I) (X := X) (E := E) x) :=
    inferInstance
  letI (x : X) :
      AddCommGroup (ManifoldDifferentialBundleFiber
        (I := I) (X := X) (E := E) x) :=
    inferInstance
  letI (x : X) :
      Module ℝ (ManifoldDifferentialBundleFiber
        (I := I) (X := X) (E := E) x) :=
    inferInstance
  letI (x : X) :
      IsTopologicalAddGroup (ManifoldDifferentialBundleFiber
        (I := I) (X := X) (E := E) x) :=
    inferInstance
  letI (x : X) :
      ContinuousConstSMul ℝ (ManifoldDifferentialBundleFiber
        (I := I) (X := X) (E := E) x) :=
    inferInstance
  letI (x : X) :
      NormedAddCommGroup (ManifoldDifferentialBundleFiber
        (I := I) (X := X) (E := E) x) :=
    manifoldDifferentialHilbertSchmidtNormedAddCommGroup
      (I := I) (X := X) (E := E) metric x
  letI (x : X) :
      InnerProductSpace ℝ (ManifoldDifferentialBundleFiber
        (I := I) (X := X) (E := E) x) :=
    manifoldDifferentialHilbertSchmidtInnerProductSpace
      (I := I) (X := X) (E := E) metric x
  let V := ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E)
  let G := manifoldDifferentialHilbertBundleGeometryOfMetric
    (I := I) (X := X) (E := E) metric
  exact @l2HilbertBundle_admits_hilbert_structure
    H X (H →L[ℝ] E)
    inferInstance inferInstance
    I inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance
    V inferInstance inferInstance inferInstance
    (fun x ↦ manifoldDifferentialHilbertSchmidtNormedAddCommGroup
      (I := I) (X := X) (E := E) metric x)
    (fun x ↦ manifoldDifferentialHilbertSchmidtInnerProductSpace
      (I := I) (X := X) (E := E) metric x)
    (fun x ↦ by
      let U0 : UniformSpace (V x) :=
        ContinuousLinearMap.uniformSpace
          (𝕜₁ := ℝ) (𝕜₂ := ℝ) (σ := RingHom.id ℝ)
          (E := TangentSpace I x) (F := E)
      have hU : PseudoMetricSpace.toUniformSpace = U0 := by
        apply UniformSpace.ext
        rw [@uniformity_eq_comap_nhds_zero (V x)
          PseudoMetricSpace.toUniformSpace inferInstance inferInstance]
        letI : UniformSpace (V x) := U0
        rw [@uniformity_eq_comap_nhds_zero (V x)
          U0 inferInstance inferInstance]
      change @CompleteSpace (V x) PseudoMetricSpace.toUniformSpace
      rw [hU]
      change CompleteSpace (H →L[ℝ] E)
      infer_instance)
    inferInstance inferInstance inferInstance
    G
    (by
      intro x A B
      rfl)
    μ

/--
%%handwave
name:
  Intrinsic \(L^2\) differential sections over a manifold form a Hilbert space
statement:
  For a finite-dimensional smooth Riemannian manifold and a complete real
  Hilbert target, the \(L^2\)-sections of \(T^\ast X\otimes E\), equipped with
  the Hilbert-Schmidt inner product, form a real Hilbert space.
proof:
  The Hilbert-Schmidt metric makes the differential bundle a continuous
  Hilbert bundle with complete fibers.  The general Hilbert-space theorem for
  square-integrable sections then applies.
-/
theorem manifoldDifferentialL2Sections_admit_hilbert_structure
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := I) X E)]
    [TopologicalSpace.PseudoMetrizableSpace (ManifoldDifferentialTotalSpace (I := I) X E)]
    (g : SmoothRiemannianMetricOnManifold I X) (μ : Measure X) :
    AdmitsRealHilbertStructure
      (ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ) := by
  let metric :=
    manifoldDifferentialHilbertSchmidtContinuousRiemannianMetric
      (I := I) (X := X) (E := E) g
  simpa [ManifoldDifferentialL2Section, manifoldDifferentialHilbertBundleGeometry]
    using
      manifoldDifferentialL2Sections_admit_hilbert_structure_of_metric
        (I := I) (X := X) (E := E) metric μ

/--
%%handwave
name:
  Canonical normed group structure on differential \(L^2\)-sections
statement:
  The quotient of square-integrable sections of \(T^\ast X\otimes E\) is
  equipped with the norm induced by the fiberwise Hilbert--Schmidt
  representative \(L^2\)-norm.
-/
@[reducible] noncomputable def manifoldDifferentialL2SectionNormedAddCommGroup
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := I) X E)]
    [TopologicalSpace.PseudoMetrizableSpace (ManifoldDifferentialTotalSpace (I := I) X E)]
    (g : SmoothRiemannianMetricOnManifold I X) (μ : Measure X) :
    NormedAddCommGroup
      (ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ) := by
  let metric :=
    manifoldDifferentialHilbertSchmidtContinuousRiemannianMetric
      (I := I) (X := X) (E := E) g
  letI : Bundle.RiemannianBundle
      (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E)) :=
    ⟨metric.toRiemannianMetric⟩
  letI (x : X) :
      NormedAddCommGroup (ManifoldDifferentialBundleFiber
        (I := I) (X := X) (E := E) x) :=
    manifoldDifferentialHilbertSchmidtNormedAddCommGroup
      (I := I) (X := X) (E := E) metric x
  letI (x : X) :
      InnerProductSpace ℝ (ManifoldDifferentialBundleFiber
        (I := I) (X := X) (E := E) x) :=
    manifoldDifferentialHilbertSchmidtInnerProductSpace
      (I := I) (X := X) (E := E) metric x
  exact l2HilbertBundleNormedAddCommGroup
    (I := I)
    (G := manifoldDifferentialHilbertBundleGeometry (I := I) (X := X) (E := E) g)
    (by intro x A B; rfl) μ

private noncomputable def squareIntegrableManifoldDifferentialFieldSub
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := I) X E)]
    [TopologicalSpace.PseudoMetrizableSpace (ManifoldDifferentialTotalSpace (I := I) X E)]
    (g : SmoothRiemannianMetricOnManifold I X) (μ : Measure X)
    (w₁ w₂ : SquareIntegrableManifoldDifferentialField
      (I := I) (X := X) (E := E) g μ) :
    SquareIntegrableManifoldDifferentialField (I := I) (X := X) (E := E) g μ := by
  let metric :=
    manifoldDifferentialHilbertSchmidtContinuousRiemannianMetric
      (I := I) (X := X) (E := E) g
  letI : Bundle.RiemannianBundle
      (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E)) :=
    ⟨metric.toRiemannianMetric⟩
  letI (x : X) :
      NormedAddCommGroup (ManifoldDifferentialBundleFiber
        (I := I) (X := X) (E := E) x) :=
    manifoldDifferentialHilbertSchmidtNormedAddCommGroup
      (I := I) (X := X) (E := E) metric x
  letI (x : X) :
      InnerProductSpace ℝ (ManifoldDifferentialBundleFiber
        (I := I) (X := X) (E := E) x) :=
    manifoldDifferentialHilbertSchmidtInnerProductSpace
      (I := I) (X := X) (E := E) metric x
  exact squareIntegrableHilbertBundleSectionSub
    (I := I)
    (G := manifoldDifferentialHilbertBundleGeometry (I := I) (X := X) (E := E) g)
    (fun _ _ _ ↦ rfl) μ w₁ w₂

/--
%%handwave
name:
  Distance between represented differential sections
statement:
  For square-integrable differential fields (A,B), the extended distance between their \(L^2\) classes is the finite extended-real image of the \(L^2\)-norm of (A-B).
proof:
  Use the general distance formula for represented Hilbert-bundle sections with the metric Hilbert--Schmidt fiber norm.
-/
private theorem manifoldDifferentialL2Section_edist_mk_eq_ofReal_l2Norm_sub
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := I) X E)]
    [TopologicalSpace.PseudoMetrizableSpace (ManifoldDifferentialTotalSpace (I := I) X E)]
    (g : SmoothRiemannianMetricOnManifold I X) (μ : Measure X)
    (w₁ w₂ : SquareIntegrableManifoldDifferentialField
      (I := I) (X := X) (E := E) g μ) :
    letI : NormedAddCommGroup
        (ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ) :=
      manifoldDifferentialL2SectionNormedAddCommGroup (I := I) (X := X) (E := E) g μ
    edist
        (Quotient.mk
          (SquareIntegrableManifoldDifferentialField.aeSetoid
            (I := I) (X := X) (E := E) (g := g) (μ := μ)) w₁ :
          ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ)
        (Quotient.mk
          (SquareIntegrableManifoldDifferentialField.aeSetoid
            (I := I) (X := X) (E := E) (g := g) (μ := μ)) w₂ :
          ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ) =
      ENNReal.ofReal
        (squareIntegrableHilbertBundleSectionL2Norm
          (manifoldDifferentialHilbertBundleGeometry (I := I) (X := X) (E := E) g) μ
          (squareIntegrableManifoldDifferentialFieldSub
            (I := I) (X := X) (E := E) g μ w₁ w₂)) := by
  let metric :=
    manifoldDifferentialHilbertSchmidtContinuousRiemannianMetric
      (I := I) (X := X) (E := E) g
  letI : Bundle.RiemannianBundle
      (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E)) :=
    ⟨metric.toRiemannianMetric⟩
  letI (x : X) :
      NormedAddCommGroup (ManifoldDifferentialBundleFiber
        (I := I) (X := X) (E := E) x) :=
    manifoldDifferentialHilbertSchmidtNormedAddCommGroup
      (I := I) (X := X) (E := E) metric x
  letI (x : X) :
      InnerProductSpace ℝ (ManifoldDifferentialBundleFiber
        (I := I) (X := X) (E := E) x) :=
    manifoldDifferentialHilbertSchmidtInnerProductSpace
      (I := I) (X := X) (E := E) metric x
  letI : NormedAddCommGroup
      (ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ) :=
    manifoldDifferentialL2SectionNormedAddCommGroup (I := I) (X := X) (E := E) g μ
  rw [edist_eq_enorm_sub]
  rw [← l2HilbertBundle_mk_sub
    (I := I)
    (G := manifoldDifferentialHilbertBundleGeometry (I := I) (X := X) (E := E) g)
    (μ := μ) (fun _ _ _ ↦ rfl) w₁ w₂]
  rw [← ofReal_norm]
  rw [l2HilbertBundle_norm_mk_eq_l2Norm
    (I := I)
    (G := manifoldDifferentialHilbertBundleGeometry (I := I) (X := X) (E := E) g)
    (μ := μ) (fun _ _ _ ↦ rfl)]
  simp [squareIntegrableManifoldDifferentialFieldSub]

/--
%%handwave
name:
  Vanishing differential \(L^2\)-norm gives quotient convergence to zero
statement:
  If square-integrable differential representatives have intrinsic squared
  \(L^2\)-norms tending to zero, then their classes converge to zero in the
  intrinsic differential \(L^2\)-section space.
proof:
  The quotient norm of a representative is its intrinsic \(L^2\)-norm, and
  this norm is the square root of the squared norm.  Continuity of the square
  root transfers convergence of the squared norms to convergence of norms.
-/
theorem manifoldDifferentialL2Section_tendsto_zero_of_l2NormSq_tendsto_zero
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := I) X E)]
    [TopologicalSpace.PseudoMetrizableSpace (ManifoldDifferentialTotalSpace (I := I) X E)]
    (g : SmoothRiemannianMetricOnManifold I X) (μ : Measure X) :
    letI : NormedAddCommGroup
        (ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ) :=
      manifoldDifferentialL2SectionNormedAddCommGroup (I := I) (X := X) (E := E) g μ
    ∀ {ι : Type} {l : Filter ι} [l.NeBot]
      {du : ι → SquareIntegrableManifoldDifferentialField
        (I := I) (X := X) (E := E) g μ},
      Filter.Tendsto
        (fun i ↦
          squareIntegrableHilbertBundleSectionL2NormSq
            (manifoldDifferentialHilbertBundleGeometry
              (I := I) (X := X) (E := E) g) μ (du i))
        l (𝓝 0) →
      Filter.Tendsto
        (fun i ↦
          (Quotient.mk
            (SquareIntegrableManifoldDifferentialField.aeSetoid
              (I := I) (X := X) (E := E) (g := g) (μ := μ)) (du i) :
            ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ))
        l
        (𝓝 (0 :
          ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ)) := by
  let metric :=
    manifoldDifferentialHilbertSchmidtContinuousRiemannianMetric
      (I := I) (X := X) (E := E) g
  letI : Bundle.RiemannianBundle
      (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E)) :=
    ⟨metric.toRiemannianMetric⟩
  letI (x : X) :
      NormedAddCommGroup (ManifoldDifferentialBundleFiber
        (I := I) (X := X) (E := E) x) :=
    manifoldDifferentialHilbertSchmidtNormedAddCommGroup
      (I := I) (X := X) (E := E) metric x
  letI (x : X) :
      InnerProductSpace ℝ (ManifoldDifferentialBundleFiber
        (I := I) (X := X) (E := E) x) :=
    manifoldDifferentialHilbertSchmidtInnerProductSpace
      (I := I) (X := X) (E := E) metric x
  letI : NormedAddCommGroup
      (ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ) :=
    manifoldDifferentialL2SectionNormedAddCommGroup (I := I) (X := X) (E := E) g μ
  intro ι l hne du hsq
  have hnorm :
      Filter.Tendsto
        (fun i ↦
          squareIntegrableHilbertBundleSectionL2Norm
            (manifoldDifferentialHilbertBundleGeometry
              (I := I) (X := X) (E := E) g) μ (du i))
        l (𝓝 0) := by
    simpa [squareIntegrableHilbertBundleSectionL2Norm] using
      (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  refine hnorm.congr' ?_
  filter_upwards [] with i
  rw [sub_zero]
  exact
    l2HilbertBundle_norm_mk_eq_l2Norm
      (I := I)
      (G := manifoldDifferentialHilbertBundleGeometry
        (I := I) (X := X) (E := E) g)
      (μ := μ) (fun _ _ _ ↦ rfl) (du i)

/--
%%handwave
name:
  Intrinsic first-order \(L^2\) model on a manifold
statement:
  The ambient intrinsic first-order model for Hilbert-valued Sobolev maps on a
  Riemannian manifold is the \(L^2\)-product of the value bundle and the
  differential bundle \(T^\ast X\otimes E\).
-/
abbrev SobolevH1OnManifoldWithValuesIntrinsicAmbientModel {H X E : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold I 1 X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : SmoothRiemannianMetricOnManifold I X) (μ : Measure X) : Type _ :=
  WithLp 2
    (ValueL2Section (X := X) (E := E) μ ×
      ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ)

/--
%%handwave
name:
  Intrinsic first-order \(L^2\) model on a manifold is Hilbert
statement:
  The intrinsic first-order square-sum product \(L^2(X;E)\times
  L^2(T^\ast X\otimes E)\) on a finite-dimensional Riemannian manifold is a
  real Hilbert space.
proof:
  Both factors are Hilbert spaces, and products of Hilbert spaces are Hilbert
  spaces.
-/
theorem manifoldH1WithValuesIntrinsicAmbientModel_admits_hilbert_structure
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology (Bundle.TotalSpace E (Bundle.Trivial X E))]
    [TopologicalSpace.PseudoMetrizableSpace (Bundle.TotalSpace E (Bundle.Trivial X E))]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := I) X E)]
    [TopologicalSpace.PseudoMetrizableSpace (ManifoldDifferentialTotalSpace (I := I) X E)]
    (g : SmoothRiemannianMetricOnManifold I X) (μ : Measure X) :
    AdmitsRealHilbertStructure
      (SobolevH1OnManifoldWithValuesIntrinsicAmbientModel
        (I := I) (X := X) (E := E) g μ) := by
  rcases manifoldValueL2Sections_admit_hilbert_structure
      (I := I) (X := X) (E := E) μ with
    ⟨valueNormed, valueInner, valueComplete, _⟩
  rcases manifoldDifferentialL2Sections_admit_hilbert_structure
      (I := I) (X := X) (E := E) g μ with
    ⟨diffNormed, diffInner, diffComplete, _⟩
  letI : NormedAddCommGroup (ValueL2Section (X := X) (E := E) μ) := valueNormed
  letI : InnerProductSpace ℝ (ValueL2Section (X := X) (E := E) μ) := valueInner
  letI : CompleteSpace (ValueL2Section (X := X) (E := E) μ) := valueComplete
  letI :
      NormedAddCommGroup
        (ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ) :=
    diffNormed
  letI :
      InnerProductSpace ℝ
        (ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ) :=
    diffInner
  letI : CompleteSpace
      (ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ) :=
    diffComplete
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  exact ⟨HilbertSpace.mk⟩

/--
%%handwave
name:
  Intrinsic Hilbert-valued weak-derivative graph on a manifold
statement:
  The intrinsic weak-derivative graph consists of an \(L^2\)-class map and an
  \(L^2\)-class section of \(T^\ast X\otimes E\) which admit representatives
  satisfying the chartwise weak-derivative identities.
-/
def WeakDerivativeIntrinsicGraphOnManifoldWithValues {H X E : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H]
    [MeasurableSpace X] [BorelSpace X] [IsManifold I 1 X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : SmoothRiemannianMetricOnManifold I X) (μ : Measure X)
    (p : SobolevH1OnManifoldWithValuesIntrinsicAmbientModel
      (I := I) (X := X) (E := E) g μ) : Prop :=
  ∃ u : SquareIntegrableValueSection (X := X) (E := E) μ,
  ∃ du : SquareIntegrableManifoldDifferentialField
      (I := I) (X := X) (E := E) g μ,
    Quotient.mk
        (SquareIntegrableValueSection.aeSetoid
          (X := X) (E := E) (μ := μ)) u = (WithLp.ofLp p).1 ∧
      Quotient.mk
          (SquareIntegrableManifoldDifferentialField.aeSetoid
            (I := I) (X := X) (E := E) (g := g) (μ := μ)) du = (WithLp.ofLp p).2 ∧
        IsWeakDerivativeOnManifoldBundle
          (I := I) μ u.toFunction du.toField

/--
%%handwave
name:
  Intrinsic manifold graph Hilbert model
statement:
  The intrinsic graph model of \(W^{1,2}(X;E)\) is the weak-derivative graph
  inside the product of \(L^2(X;E)\) and \(L^2(T^\ast X\otimes E)\).
-/
def SobolevH1OnManifoldWithValuesIntrinsicGraphHilbertModel {H X E : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H]
    [MeasurableSpace X] [BorelSpace X] [IsManifold I 1 X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : SmoothRiemannianMetricOnManifold I X) (μ : Measure X) : Type _ :=
  {p : SobolevH1OnManifoldWithValuesIntrinsicAmbientModel
      (I := I) (X := X) (E := E) g μ //
    WeakDerivativeIntrinsicGraphOnManifoldWithValues g μ p}

/--
%%handwave
name:
  Smooth compactly supported Hilbert-valued manifold map
statement:
  A smooth compactly supported map from a finite-dimensional manifold to a
  real normed vector space is a smooth map whose topological support is
  compact.
-/
structure SmoothCompactlySupportedManifoldMap {H X E : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I : ModelWithCorners ℝ H H) [TopologicalSpace X] [ChartedSpace H X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] where
  /-- The underlying map. -/
  toFun : X → E
  /-- The map is smooth. -/
  smooth : ContMDiff I 𝓘(ℝ, E) ∞ toFun
  /-- The topological support is compact. -/
  compact_support : IsCompact (tsupport toFun)

namespace SmoothCompactlySupportedManifoldMap

instance {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] :
    CoeFun (SmoothCompactlySupportedManifoldMap (X := X) (E := E) I)
      (fun _ ↦ X → E) where
  coe f := f.toFun

/--
%%handwave
name:
  Classical differential field of a smooth map
statement:
  A smooth compactly supported map determines a classical differential field,
  assigning to each point the differential from the tangent space to the
  target Hilbert space.
-/
noncomputable def differential {H X E : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : SmoothCompactlySupportedManifoldMap (X := X) (E := E) I) :
    ManifoldDifferentialField I X E :=
  fun x ↦
    (mfderiv I 𝓘(ℝ, E) f.toFun x :
      TangentSpace I x →L[ℝ] E)

end SmoothCompactlySupportedManifoldMap

/--
%%handwave
name:
  Smooth compactly supported maps as Sobolev graph elements
statement:
  A point of the graph model is represented by a smooth compactly supported
  map if its value component is the \(L^2\)-class of that map and its
  differential component is the \(L^2\)-class of the classical differential
  field.
-/
def IsSmoothCompactlySupportedManifoldSobolevGraphElement {H X E : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H]
    [MeasurableSpace X] [BorelSpace X] [IsManifold I 1 X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : SmoothRiemannianMetricOnManifold I X) (μ : Measure X)
    (p : SobolevH1OnManifoldWithValuesIntrinsicGraphHilbertModel
      (I := I) (X := X) (E := E) g μ) : Prop :=
  ∃ f : SmoothCompactlySupportedManifoldMap (X := X) (E := E) I,
  ∃ hf_mem :
      HilbertBundleSectionMemL2 (trivialHilbertBundleGeometry X E) μ f.toFun,
  ∃ hdf_mem :
      ManifoldDifferentialFieldMemHilbertSchmidtL2
        (I := I) g μ f.differential,
    (Quotient.mk
        (SquareIntegrableValueSection.aeSetoid
          (X := X) (E := E) (μ := μ))
        ({ toSection := f.toFun, memL2 := hf_mem } :
          SquareIntegrableValueSection (X := X) (E := E) μ) :
      ValueL2Section (X := X) (E := E) μ) =
        (WithLp.ofLp p.1).1 ∧
      (Quotient.mk
          (SquareIntegrableManifoldDifferentialField.aeSetoid
            (I := I) (X := X) (E := E) (g := g) (μ := μ))
          ({ toSection := f.differential, memL2 := hdf_mem } :
            SquareIntegrableManifoldDifferentialField
              (I := I) (X := X) (E := E) g μ) :
        ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ) =
          (WithLp.ofLp p.1).2

/--
%%handwave
name:
  Smooth compactly supported Sobolev graph elements
statement:
  The compactly supported smooth graph elements are the elements of the
  Sobolev graph represented by smooth compactly supported maps with their
  classical differentials.
-/
def smoothCompactlySupportedManifoldSobolevGraphElements {H X E : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H]
    [MeasurableSpace X] [BorelSpace X] [IsManifold I 1 X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : SmoothRiemannianMetricOnManifold I X) (μ : Measure X) :
    Set (SobolevH1OnManifoldWithValuesIntrinsicGraphHilbertModel
      (I := I) (X := X) (E := E) g μ) :=
  {p | IsSmoothCompactlySupportedManifoldSobolevGraphElement g μ p}

/--
%%handwave
name:
  Zero-trace Sobolev space on a manifold
statement:
  The zero-trace first-order Sobolev space is the closed linear subspace
  generated by smooth compactly supported maps in the graph Hilbert space.
-/
def SobolevH1ZeroOnManifoldWithValuesIntrinsicClosedSubmodule {H X E : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H]
    [MeasurableSpace X] [BorelSpace X] [IsManifold I 1 X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : SmoothRiemannianMetricOnManifold I X) (μ : Measure X)
    [AddCommMonoid
      (SobolevH1OnManifoldWithValuesIntrinsicGraphHilbertModel
        (I := I) (X := X) (E := E) g μ)]
    [Module ℝ
      (SobolevH1OnManifoldWithValuesIntrinsicGraphHilbertModel
        (I := I) (X := X) (E := E) g μ)]
    [TopologicalSpace
      (SobolevH1OnManifoldWithValuesIntrinsicGraphHilbertModel
        (I := I) (X := X) (E := E) g μ)]
    [ContinuousAdd
      (SobolevH1OnManifoldWithValuesIntrinsicGraphHilbertModel
        (I := I) (X := X) (E := E) g μ)]
    [ContinuousConstSMul ℝ
      (SobolevH1OnManifoldWithValuesIntrinsicGraphHilbertModel
        (I := I) (X := X) (E := E) g μ)] :
    ClosedSubmodule ℝ
      (SobolevH1OnManifoldWithValuesIntrinsicGraphHilbertModel
        (I := I) (X := X) (E := E) g μ) :=
  (Submodule.span ℝ
    (smoothCompactlySupportedManifoldSobolevGraphElements
      (I := I) (X := X) (E := E) g μ)).closure

/--
%%handwave
name:
  Zero-trace Sobolev Hilbert model on a manifold
statement:
  The zero-trace Sobolev Hilbert model is the closed subspace generated by
  compactly supported smooth maps inside \(W^{1,2}\).
-/
abbrev SobolevH1ZeroOnManifoldWithValuesIntrinsicHilbertModel {H X E : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H]
    [MeasurableSpace X] [BorelSpace X] [IsManifold I 1 X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : SmoothRiemannianMetricOnManifold I X) (μ : Measure X)
    [AddCommMonoid
      (SobolevH1OnManifoldWithValuesIntrinsicGraphHilbertModel
        (I := I) (X := X) (E := E) g μ)]
    [Module ℝ
      (SobolevH1OnManifoldWithValuesIntrinsicGraphHilbertModel
        (I := I) (X := X) (E := E) g μ)]
    [TopologicalSpace
      (SobolevH1OnManifoldWithValuesIntrinsicGraphHilbertModel
        (I := I) (X := X) (E := E) g μ)]
    [ContinuousAdd
      (SobolevH1OnManifoldWithValuesIntrinsicGraphHilbertModel
        (I := I) (X := X) (E := E) g μ)]
    [ContinuousConstSMul ℝ
      (SobolevH1OnManifoldWithValuesIntrinsicGraphHilbertModel
        (I := I) (X := X) (E := E) g μ)] : Type _ :=
  (SobolevH1ZeroOnManifoldWithValuesIntrinsicClosedSubmodule
    (I := I) (X := X) (E := E) g μ :
    Submodule ℝ
      (SobolevH1OnManifoldWithValuesIntrinsicGraphHilbertModel
        (I := I) (X := X) (E := E) g μ))

/--
%%handwave
name:
  Zero-trace Sobolev space is closed
statement:
  The zero-trace Sobolev space is a closed linear subspace of the graph
  Hilbert space \(W^{1,2}\).
proof:
  It is defined as the topological closure of the linear span of compactly
  supported smooth graph elements.  The topological closure of a submodule is
  closed.
-/
theorem sobolevH1ZeroOnManifoldWithValuesIntrinsic_isClosed {H X E : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H]
    [MeasurableSpace X] [BorelSpace X] [IsManifold I 1 X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : SmoothRiemannianMetricOnManifold I X) (μ : Measure X)
    [AddCommMonoid
      (SobolevH1OnManifoldWithValuesIntrinsicGraphHilbertModel
        (I := I) (X := X) (E := E) g μ)]
    [Module ℝ
      (SobolevH1OnManifoldWithValuesIntrinsicGraphHilbertModel
        (I := I) (X := X) (E := E) g μ)]
    [TopologicalSpace
      (SobolevH1OnManifoldWithValuesIntrinsicGraphHilbertModel
        (I := I) (X := X) (E := E) g μ)]
    [ContinuousAdd
      (SobolevH1OnManifoldWithValuesIntrinsicGraphHilbertModel
        (I := I) (X := X) (E := E) g μ)]
    [ContinuousConstSMul ℝ
      (SobolevH1OnManifoldWithValuesIntrinsicGraphHilbertModel
        (I := I) (X := X) (E := E) g μ)] :
    IsClosed
      (SobolevH1ZeroOnManifoldWithValuesIntrinsicClosedSubmodule
        (I := I) (X := X) (E := E) g μ :
        Set (SobolevH1OnManifoldWithValuesIntrinsicGraphHilbertModel
          (I := I) (X := X) (E := E) g μ)) := by
  exact ClosedSubmodule.isClosed _

/--
%%handwave
name:
  Zero-trace intrinsic Sobolev space is Hilbert
statement:
  If the intrinsic graph model of \(W^{1,2}\) is a Hilbert space, then the
  zero-trace space generated by compactly supported smooth maps is a Hilbert
  space with the induced structure.
proof:
  The zero-trace space is a closed submodule of the graph Hilbert space.  A
  closed linear subspace of a Hilbert space is complete, and the inherited
  inner product makes it a Hilbert space.
-/
theorem sobolevH1ZeroOnManifoldWithValuesIntrinsic_admits_hilbert_structure
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H]
    [MeasurableSpace X] [BorelSpace X] [IsManifold I 1 X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : SmoothRiemannianMetricOnManifold I X) (μ : Measure X)
    [NormedAddCommGroup
      (SobolevH1OnManifoldWithValuesIntrinsicGraphHilbertModel
        (I := I) (X := X) (E := E) g μ)]
    [InnerProductSpace ℝ
      (SobolevH1OnManifoldWithValuesIntrinsicGraphHilbertModel
        (I := I) (X := X) (E := E) g μ)]
    [CompleteSpace
      (SobolevH1OnManifoldWithValuesIntrinsicGraphHilbertModel
        (I := I) (X := X) (E := E) g μ)]
    [ContinuousAdd
      (SobolevH1OnManifoldWithValuesIntrinsicGraphHilbertModel
        (I := I) (X := X) (E := E) g μ)]
    [ContinuousConstSMul ℝ
      (SobolevH1OnManifoldWithValuesIntrinsicGraphHilbertModel
        (I := I) (X := X) (E := E) g μ)] :
    AdmitsRealHilbertStructure
      (SobolevH1ZeroOnManifoldWithValuesIntrinsicHilbertModel
        (I := I) (X := X) (E := E) g μ) := by
  let Gclosed :=
    SobolevH1ZeroOnManifoldWithValuesIntrinsicClosedSubmodule
      (I := I) (X := X) (E := E) g μ
  let G : Submodule ℝ
      (SobolevH1OnManifoldWithValuesIntrinsicGraphHilbertModel
        (I := I) (X := X) (E := E) g μ) :=
    Gclosed
  have hG_closed : IsClosed
      (G : Set
        (SobolevH1OnManifoldWithValuesIntrinsicGraphHilbertModel
          (I := I) (X := X) (E := E) g μ)) := by
    simpa [G, Gclosed] using
      sobolevH1ZeroOnManifoldWithValuesIntrinsic_isClosed
        (I := I) (X := X) (E := E) g μ
  have hG_complete : CompleteSpace G := by
    change CompleteSpace
      (G : Set
        (SobolevH1OnManifoldWithValuesIntrinsicGraphHilbertModel
          (I := I) (X := X) (E := E) g μ))
    exact hG_closed.isComplete.completeSpace_coe
  haveI : CompleteSpace G := hG_complete
  change AdmitsRealHilbertStructure G
  refine ⟨inferInstance, inferInstance, hG_complete, ?_⟩
  exact ⟨@HilbertSpace.mk ℝ G _ _ _ hG_complete⟩

/--
%%handwave
name:
  Vector-valued weak derivative of zero on a manifold
statement:
  The zero differential field is the weak derivative of the zero map.
proof:
  Both sides of every coordinate integration-by-parts identity are zero, and the zero integrands are integrable.
-/
theorem isWeakDerivativeOnManifoldBundle_zero
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H] [MeasurableSpace X] [IsManifold I 1 X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X) :
    IsWeakDerivativeOnManifoldBundle (I := I) μ (0 : X → E)
      (0 : ManifoldDifferentialField I X E) := by
  intro e _he φ v
  constructor
  · simp
  · constructor
    · simp [ManifoldDifferentialField.evalChart]
    · simp [ManifoldDifferentialField.evalChart]

/--
%%handwave
name:
  Vector-valued weak derivatives add on a manifold
statement:
  The sum of two vector-valued weak derivatives is the weak derivative of the
  sum of the corresponding maps.
proof:
  Add the two integration-by-parts identities and use linearity of the
  Bochner integral.
-/
theorem IsWeakDerivativeOnManifoldBundle.add
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H] [MeasurableSpace X] [IsManifold I 1 X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure X} {u₁ u₂ : X → E}
    {du₁ du₂ : ManifoldDifferentialField I X E}
    (hu₁ : IsWeakDerivativeOnManifoldBundle (I := I) μ u₁ du₁)
    (hu₂ : IsWeakDerivativeOnManifoldBundle (I := I) μ u₂ du₂) :
    IsWeakDerivativeOnManifoldBundle (I := I) μ (u₁ + u₂) (du₁ + du₂) := by
  intro e he φ v
  rcases hu₁ e he φ v with ⟨hu₁_int, hdu₁_int, h₁_eq⟩
  rcases hu₂ e he φ v with ⟨hu₂_int, hdu₂_int, h₂_eq⟩
  let Ω : Set H := manifoldChartRegion e (Set.univ : Set X)
  let μΩ := MeasureTheory.volume.restrict Ω
  let lhs₁ : H → E :=
    fun z ↦ (fderiv ℝ (φ : H → ℝ) z v) • u₁ (e.symm z)
  let lhs₂ : H → E :=
    fun z ↦ (fderiv ℝ (φ : H → ℝ) z v) • u₂ (e.symm z)
  let rhs₁ : H → E :=
    fun z ↦ φ z • ManifoldDifferentialField.evalChart du₁ e z v
  let rhs₂ : H → E :=
    fun z ↦ φ z • ManifoldDifferentialField.evalChart du₂ e z v
  have hrhs_add :
      (fun z ↦ rhs₁ z + rhs₂ z) =
        fun z ↦
          φ z • ManifoldDifferentialField.evalChart (du₁ + du₂) e z v := by
    ext z
    simp [rhs₁, rhs₂, ManifoldDifferentialField.evalChart, smul_add]
  have h₁_eq' : ∫ z, lhs₁ z ∂μΩ = -∫ z, rhs₁ z ∂μΩ := by
    simpa [Ω, μΩ, lhs₁, rhs₁] using h₁_eq
  have h₂_eq' : ∫ z, lhs₂ z ∂μΩ = -∫ z, rhs₂ z ∂μΩ := by
    simpa [Ω, μΩ, lhs₂, rhs₂] using h₂_eq
  constructor
  · convert hu₁_int.add hu₂_int using 1
    ext z
    simp [smul_add]
  · constructor
    · convert hdu₁_int.add hdu₂_int using 1
      ext z
      simp [ManifoldDifferentialField.evalChart, smul_add]
    · calc
        ∫ z in Ω,
            (fderiv ℝ (φ : H → ℝ) z v) • (u₁ + u₂) (e.symm z)
              ∂MeasureTheory.volume
            = ∫ z, lhs₁ z + lhs₂ z ∂μΩ := by
                congr 1
                ext z
                simp [lhs₁, lhs₂, smul_add]
        _ = ∫ z, lhs₁ z ∂μΩ + ∫ z, lhs₂ z ∂μΩ :=
              integral_add hu₁_int hu₂_int
        _ = -∫ z, rhs₁ z ∂μΩ + -∫ z, rhs₂ z ∂μΩ := by
              rw [h₁_eq', h₂_eq']
        _ = -(∫ z, rhs₁ z ∂μΩ + ∫ z, rhs₂ z ∂μΩ) := by
              rw [neg_add]
        _ = -∫ z, rhs₁ z + rhs₂ z ∂μΩ := by
              rw [integral_add hdu₁_int hdu₂_int]
        _ = -∫ z in Ω,
            φ z • ManifoldDifferentialField.evalChart (du₁ + du₂) e z v
              ∂MeasureTheory.volume := by
                rw [show μΩ = MeasureTheory.volume.restrict Ω from rfl, hrhs_add]

/--
%%handwave
name:
  Vector-valued weak derivatives scale on a manifold
statement:
  Multiplying a vector-valued map and its weak derivative by the same real
  scalar preserves the weak-derivative identity.
proof:
  Pull the scalar through both Bochner integrals.
-/
theorem IsWeakDerivativeOnManifoldBundle.const_smul
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H] [MeasurableSpace X] [IsManifold I 1 X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure X} (c : ℝ) {u : X → E}
    {du : ManifoldDifferentialField I X E}
    (hu : IsWeakDerivativeOnManifoldBundle (I := I) μ u du) :
    IsWeakDerivativeOnManifoldBundle (I := I) μ (c • u) (c • du) := by
  intro e he φ v
  rcases hu e he φ v with ⟨hu_int, hdu_int, h_eq⟩
  let Ω : Set H := manifoldChartRegion e (Set.univ : Set X)
  let μΩ := MeasureTheory.volume.restrict Ω
  let lhs : H → E :=
    fun z ↦ (fderiv ℝ (φ : H → ℝ) z v) • u (e.symm z)
  let rhs : H → E :=
    fun z ↦ φ z • ManifoldDifferentialField.evalChart du e z v
  have hrhs_smul :
      (fun z ↦ c • rhs z) =
        fun z ↦
          φ z • ManifoldDifferentialField.evalChart (c • du) e z v := by
    ext z
    simp [rhs, ManifoldDifferentialField.evalChart, smul_smul, mul_comm]
  have h_eq' : ∫ z, lhs z ∂μΩ = -∫ z, rhs z ∂μΩ := by
    simpa [Ω, μΩ, lhs, rhs] using h_eq
  constructor
  · convert Integrable.smul c hu_int using 1
    ext z
    simp [smul_smul, mul_comm]
  · constructor
    · convert Integrable.smul c hdu_int using 1
      ext z
      simp [ManifoldDifferentialField.evalChart, smul_smul, mul_comm]
    · calc
        ∫ z in Ω,
            (fderiv ℝ (φ : H → ℝ) z v) • (c • u) (e.symm z)
              ∂MeasureTheory.volume
            = ∫ z, c • lhs z ∂μΩ := by
                congr 1
                ext z
                simp [lhs, smul_smul, mul_comm]
        _ = c • ∫ z, lhs z ∂μΩ := integral_smul c lhs
        _ = c • (-∫ z, rhs z ∂μΩ) := by rw [h_eq']
        _ = -(c • ∫ z, rhs z ∂μΩ) := by simp
        _ = -∫ z, c • rhs z ∂μΩ := by rw [integral_smul c rhs]
        _ = -∫ z in Ω,
            φ z • ManifoldDifferentialField.evalChart (c • du) e z v
              ∂MeasureTheory.volume := by
                rw [show μΩ = MeasureTheory.volume.restrict Ω from rfl, hrhs_smul]

/--
%%handwave
name:
  Local \(L^2\) control on a finite support gives chart integrability
statement:
  If a function is square-integrable on a finite-measure set \(K\), is
  supported in \(K\), and \(K\) lies in a chart region \(\Omega\), then it is
  integrable over \(\Omega\).
proof:
  On the finite-measure set \(K\), \(L^2\) embeds into \(L^1\).  Since the
  function vanishes outside \(K\), integrability over \(K\) is equivalent to
  integrability over the larger region \(\Omega\).
-/
private theorem integrableOn_region_of_memLp_two_restrict_support
    {α E : Type} [MeasurableSpace α]
    [NormedAddCommGroup E]
    {ν : Measure α} {Ω K : Set α} {F : α → E}
    (hF : MemLp F 2 (ν.restrict K))
    (hK_finite : ν K ≠ (∞ : ℝ≥0∞))
    (hF_support : Function.support F ⊆ K)
    (hKΩ : K ⊆ Ω) :
    Integrable F (ν.restrict Ω) := by
  have hK_lt_top : ν K < (∞ : ℝ≥0∞) := lt_top_iff_ne_top.2 hK_finite
  letI : IsFiniteMeasure (ν.restrict K) :=
    ⟨by simpa [Measure.restrict_apply_univ] using hK_lt_top⟩
  have hF_int_K : Integrable F (ν.restrict K) :=
    hF.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hF_int_on_K :
      IntegrableOn F K (ν.restrict Ω) := by
    change Integrable F ((ν.restrict Ω).restrict K)
    rw [Measure.restrict_restrict_of_subset hKΩ]
    exact hF_int_K
  exact (integrableOn_iff_integrable_of_support_subset
    (μ := ν.restrict Ω) hF_support).1 hF_int_on_K

/--
%%handwave
name:
  Compact coordinate supports have finite Lebesgue measure
statement:
  Let a smooth positive measure be written in a coordinate chart as a positive
  smooth density with respect to Lebesgue measure.  Any compact subset of the
  chart region has finite Lebesgue measure.
proof:
  The coordinate density is continuous and strictly positive on the compact
  set, hence bounded below by a positive constant.  The smooth positive
  measure is finite on the compact preimage in the manifold, so the
  density-weighted Lebesgue measure of the compact set is finite.  The lower
  bound for the density then implies finite Lebesgue measure.
-/
theorem smoothPositiveMeasureOnManifold_chart_volume_finite_of_compact
    {H X : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (_hμ : SmoothPositiveMeasureOnManifold (I := I) μ) :
    ∀ (e : OpenPartialHomeomorph X H) (_he : e ∈ atlas H X)
      (K : Set H),
      K ⊆ manifoldChartRegion e (Set.univ : Set X) →
      IsCompact K →
      MeasureTheory.volume K ≠ (∞ : ℝ≥0∞) := by
  intro e he K hK_region hK_compact
  classical
  rcases _hμ.chart_density e he with ⟨ρ, hρ_smooth, hρ_pos, hmap⟩
  let ν : Measure H := MeasureTheory.volume.restrict e.target
  have hK_target : K ⊆ e.target := fun z hz ↦ (hK_region hz).1
  have hK_meas : MeasurableSet K := hK_compact.measurableSet
  rcases K.eq_empty_or_nonempty with rfl | hK_nonempty
  · simp
  have hρ_cont_K : ContinuousOn ρ K :=
    hρ_smooth.continuousOn.mono hK_target
  rcases hK_compact.exists_sInf_image_eq_and_le hK_nonempty hρ_cont_K with
    ⟨z₀, hz₀K, _hz₀_inf, hz₀_min⟩
  let c : ℝ := ρ z₀
  have hc_pos : 0 < c := hρ_pos z₀ (hK_target hz₀K)
  have hc_ne_zero : ENNReal.ofReal c ≠ 0 := by
    simp [ENNReal.ofReal_eq_zero, not_le.mpr hc_pos]
  have hρ_lower : ∀ z ∈ K, ENNReal.ofReal c ≤ ENNReal.ofReal (ρ z) := by
    intro z hz
    exact ENNReal.ofReal_le_ofReal (hz₀_min z hz)
  have hpreimage_subset :
      e ⁻¹' K ≤ᵐ[μ.restrict e.source] e.symm '' K := by
    filter_upwards [ae_restrict_mem e.open_source.measurableSet] with x hx_source hxK
    exact ⟨e x, hxK, e.left_inv hx_source⟩
  have he_aemeas : AEMeasurable e (μ.restrict e.source) :=
    e.continuousOn.aemeasurable e.open_source.measurableSet
  have hmap_finite :
      Measure.map e (μ.restrict e.source) K < (∞ : ℝ≥0∞) := by
    rw [Measure.map_apply_of_aemeasurable he_aemeas hK_meas]
    refine lt_of_le_of_lt (measure_mono_ae hpreimage_subset) ?_
    exact (Measure.restrict_apply_le e.source (e.symm '' K)).trans_lt
      (lt_top_iff_ne_top.2
        (_hμ.finite_on_compact (e.symm '' K)
          (hK_compact.image_of_continuousOn
            (e.continuousOn_symm.mono hK_target))))
  have hweighted_finite :
      ν.withDensity (fun z : H ↦ ENNReal.ofReal (ρ z)) K < (∞ : ℝ≥0∞) := by
    rw [← hmap]
    exact hmap_finite
  have hconst_le_weight :
      ENNReal.ofReal c * ν K ≤
        ν.withDensity (fun z : H ↦ ENNReal.ofReal (ρ z)) K := by
    rw [withDensity_apply _ hK_meas]
    have hmono :
        (∫⁻ _ in K, ENNReal.ofReal c ∂ν) ≤
          ∫⁻ z in K, ENNReal.ofReal (ρ z) ∂ν :=
      setLIntegral_mono' hK_meas hρ_lower
    simpa [lintegral_const, Measure.restrict_apply_univ, mul_comm] using hmono
  have hmul_finite :
      ENNReal.ofReal c * ν K < (∞ : ℝ≥0∞) :=
    lt_of_le_of_lt hconst_le_weight hweighted_finite
  have hνK_finite : ν K < (∞ : ℝ≥0∞) :=
    ENNReal.lt_top_of_mul_ne_top_right hmul_finite.ne hc_ne_zero
  have hνK_eq : ν K = MeasureTheory.volume K :=
    Measure.restrict_eq_self MeasureTheory.volume hK_target
  exact (lt_top_iff_ne_top.1 (by simpa [ν, hνK_eq] using hνK_finite))

/--
%%handwave
name:
  Strong measurability of a square-integrable value representative
statement:
  A square-integrable section of a trivial Hilbert bundle is almost everywhere strongly measurable as an ordinary Hilbert-valued function.
proof:
  Compose the almost-everywhere strongly measurable total-space section with the continuous projection to the trivial fiber.
-/
private theorem squareIntegrableValueSection_aestronglyMeasurable
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [IsManifold I 1 X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology (Bundle.TotalSpace E (Bundle.Trivial X E))]
    [TopologicalSpace.PseudoMetrizableSpace (Bundle.TotalSpace E (Bundle.Trivial X E))]
    (μ : Measure X) (w : SquareIntegrableValueSection (X := X) (E := E) μ) :
    AEStronglyMeasurable w.toFunction μ := by
  have htotal : AEStronglyMeasurable
      (HilbertBundleSectionOnSurface.toTotalSpace (F := E) w.toSection) μ :=
    w.memL2.aemeasurable.aestronglyMeasurable
  have hsnd : Continuous (Bundle.TotalSpace.trivialSnd X E) := by
    simpa [Bundle.TotalSpace.trivialSnd, Bundle.Trivial.homeomorphProd,
      Bundle.TotalSpace.toProd] using
      (continuous_snd.comp (Bundle.Trivial.homeomorphProd X E).continuous)
  exact hsnd.comp_aestronglyMeasurable htotal

/--
%%handwave
name:
  A square-integrable value representative belongs to \(L^2\)
statement:
  Every square-integrable section of a trivial Hilbert bundle belongs to the ordinary Bochner space \(L^2(\mu;E)\).
proof:
  Combine strong measurability with finiteness of the \(L^2\)-norm of its pointwise norm.
-/
private theorem squareIntegrableValueSection_memLp
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [IsManifold I 1 X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology (Bundle.TotalSpace E (Bundle.Trivial X E))]
    [TopologicalSpace.PseudoMetrizableSpace (Bundle.TotalSpace E (Bundle.Trivial X E))]
    (μ : Measure X) (w : SquareIntegrableValueSection (X := X) (E := E) μ) :
    MemLp w.toFunction 2 μ := by
  have hw_aestr :
      AEStronglyMeasurable w.toFunction μ :=
    squareIntegrableValueSection_aestronglyMeasurable (I := I) μ w
  have hnorm : MemLp (fun x : X ↦ ‖w.toFunction x‖) 2 μ := by
    simpa [SquareIntegrableValueSection.toFunction] using
      squareIntegrableHilbertBundleSection_norm_memLp
        (I := I) (G := trivialHilbertBundleGeometry X E)
        (fun _ _ _ ↦ rfl) μ w
  exact (memLp_norm_iff hw_aestr).1 hnorm

/--
%%handwave
name:
  Square-integrable value representatives are \(L^2\)
statement:
  A square-integrable representative of a trivial Hilbert bundle section is
  an \(L^2\) map with respect to the underlying measure.
proof:
  Apply the preceding result that a square-integrable trivial-bundle representative is strongly measurable and has finite scalar norm.
-/
theorem SquareIntegrableValueSection.memLp
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [IsManifold I 1 X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology (Bundle.TotalSpace E (Bundle.Trivial X E))]
    [TopologicalSpace.PseudoMetrizableSpace (Bundle.TotalSpace E (Bundle.Trivial X E))]
    (μ : Measure X) (w : SquareIntegrableValueSection (X := X) (E := E) μ) :
    MemLp w.toFunction 2 μ :=
  squareIntegrableValueSection_memLp (I := I) μ w

/--
%%handwave
name:
  Removing a density bounded below
statement:
  Let \(K\) be measurable and suppose \(0<c\le\delta\) almost everywhere on \(K\), with \(c<\infty\).  If \(f\in L^p((\delta\,d\nu)|_K)\), then \(f\in L^p(\nu|_K)\).
proof:
  The density bound gives \(\nu|_K\le c^{-1}(\delta\,d\nu)|_K\); monotonicity of \(L^p\)-membership under a bounded measure comparison proves the claim.
-/
private theorem memLp_of_withDensity_lower_bound_on_restrict
    {α E : Type} [MeasurableSpace α] [TopologicalSpace E] [ContinuousENorm E]
    {ν : Measure α} {δ : α → ℝ≥0∞} {K : Set α} {c : ℝ≥0∞}
    (hK : MeasurableSet K) (hc0 : c ≠ 0) (hctop : c ≠ (⊤ : ℝ≥0∞))
    (hδ : ∀ᵐ x ∂ν.restrict K, c ≤ δ x)
    {f : α → E} {p : ℝ≥0∞}
    (hf : MemLp f p ((ν.withDensity δ).restrict K)) :
    MemLp f p (ν.restrict K) := by
  have hweighted_eq : (ν.withDensity δ).restrict K = (ν.restrict K).withDensity δ :=
    restrict_withDensity hK δ
  have hconst_le : c • ν.restrict K ≤ (ν.withDensity δ).restrict K := by
    rw [hweighted_eq, ← withDensity_const (μ := ν.restrict K) c]
    exact withDensity_mono hδ
  have hmeasure_le : ν.restrict K ≤ c⁻¹ • ((ν.withDensity δ).restrict K) := by
    calc
      ν.restrict K = (1 : ℝ≥0∞) • ν.restrict K := by simp
      _ = (c⁻¹ * c) • ν.restrict K := by
            rw [ENNReal.inv_mul_cancel hc0 hctop]
      _ = c⁻¹ • (c • ν.restrict K) := by rw [smul_smul]
      _ ≤ c⁻¹ • ((ν.withDensity δ).restrict K) := by
            apply Measure.le_iff.2
            intro s hs
            rw [Measure.smul_apply, Measure.smul_apply]
            exact mul_le_mul_right (Measure.le_iff.1 hconst_le s hs) _

  exact hf.of_measure_le_smul (by simpa [ENNReal.inv_ne_top] using hc0) hmeasure_le

/--
%%handwave
name:
  \(L^2\)-norm comparison under a density lower bound
statement:
  If \(0<c\le\delta\) almost everywhere on a measurable \(K\), then
  \[
    \|f\|_{L^2(\nu|_K)}\le c^{-1/2}\|f\|_{L^2((\delta\,d\nu)|_K)}.
  \]
proof:
  Use the measure inequality \(\nu|_K\le c^{-1}(\delta\,d\nu)|_K\) and the scaling formula for the extended \(L^2\)-norm.
-/
private theorem eLpNorm_two_of_withDensity_lower_bound_on_restrict_le
    {α E : Type} [MeasurableSpace α] [TopologicalSpace E] [ContinuousENorm E]
    {ν : Measure α} {δ : α → ℝ≥0∞} {K : Set α} {c : ℝ≥0∞}
    (hK : MeasurableSet K) (hc0 : c ≠ 0) (hctop : c ≠ (⊤ : ℝ≥0∞))
    (hδ : ∀ᵐ x ∂ν.restrict K, c ≤ δ x)
    (f : α → E) :
    eLpNorm f 2 (ν.restrict K) ≤
      c⁻¹ ^ ((1 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal *
        eLpNorm f 2 ((ν.withDensity δ).restrict K) := by
  have hweighted_eq : (ν.withDensity δ).restrict K = (ν.restrict K).withDensity δ :=
    restrict_withDensity hK δ
  have hconst_le : c • ν.restrict K ≤ (ν.withDensity δ).restrict K := by
    rw [hweighted_eq, ← withDensity_const (μ := ν.restrict K) c]
    exact withDensity_mono hδ
  have hmeasure_le : ν.restrict K ≤ c⁻¹ • ((ν.withDensity δ).restrict K) := by
    calc
      ν.restrict K = (1 : ℝ≥0∞) • ν.restrict K := by simp
      _ = (c⁻¹ * c) • ν.restrict K := by
            rw [ENNReal.inv_mul_cancel hc0 hctop]
      _ = c⁻¹ • (c • ν.restrict K) := by rw [smul_smul]
      _ ≤ c⁻¹ • ((ν.withDensity δ).restrict K) := by
            apply Measure.le_iff.2
            intro s hs
            rw [Measure.smul_apply, Measure.smul_apply]
            exact mul_le_mul_right (Measure.le_iff.1 hconst_le s hs) _
  calc
    eLpNorm f 2 (ν.restrict K) ≤
        eLpNorm f 2 (c⁻¹ • ((ν.withDensity δ).restrict K)) :=
      eLpNorm_mono_measure f hmeasure_le
    _ = c⁻¹ ^ ((1 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal *
        eLpNorm f 2 ((ν.withDensity δ).restrict K) := by
          rw [eLpNorm_smul_measure_of_ne_zero]
          · rfl
          · exact ENNReal.inv_ne_zero.2 hctop

/--
%%handwave
name:
  Almost-everywhere equality for a smooth positive chart measure
statement:
  In a chart for a smooth positive measure, two coordinate functions agree almost everywhere for the pushed-forward surface measure exactly when they agree almost everywhere for Lebesgue measure on the chart target.
proof:
  The chart measure is a positive smooth density times Lebesgue measure, and a strictly positive density has exactly the same null sets.
-/
private theorem smoothPositiveMeasureOnManifold_chart_ae_eq
    {H X β : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (hμ : SmoothPositiveMeasureOnManifold (I := I) μ)
    (e : OpenPartialHomeomorph X H) (he : e ∈ atlas H X) {f g : H → β} :
    f =ᵐ[Measure.map e (μ.restrict e.source)] g ↔
      f =ᵐ[MeasureTheory.volume.restrict e.target] g := by
  obtain ⟨ρ, hρ_smooth, hρ_pos, hmap⟩ := hμ.chart_density e he
  rw [hmap]
  have hρ_aemeas :
      AEMeasurable (fun z : H ↦ ENNReal.ofReal (ρ z))
        (MeasureTheory.volume.restrict e.target) := by
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      (hρ_smooth.continuousOn.aemeasurable e.open_target.measurableSet)
  have hρ_ne_zero :
      ∀ᵐ z ∂MeasureTheory.volume.restrict e.target,
        ENNReal.ofReal (ρ z) ≠ 0 := by
    exact ae_restrict_of_forall_mem e.open_target.measurableSet fun z hz ↦
      ne_of_gt (ENNReal.ofReal_pos.mpr (hρ_pos z hz))
  exact withDensity_ae_eq hρ_aemeas hρ_ne_zero

/--
%%handwave
name:
  Almost-everywhere measurability of an inverse chart
statement:
  For a smooth positive manifold measure, the inverse chart is almost everywhere measurable with respect to the chart pushforward measure.
proof:
  The inverse chart is measurable for restricted Lebesgue measure, and the chart pushforward is absolutely continuous with respect to that measure.
-/
private theorem smoothPositiveMeasureOnManifold_chart_symm_aemeasurable
    {H X : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (hμ : SmoothPositiveMeasureOnManifold (I := I) μ)
    (e : OpenPartialHomeomorph X H) (he : e ∈ atlas H X) :
    AEMeasurable e.symm (Measure.map e (μ.restrict e.source)) := by
  rcases hμ.chart_density e he with ⟨_ρ, _hρ_smooth, _hρ_pos, hmap⟩
  have hsymm_vol :
      AEMeasurable e.symm (MeasureTheory.volume.restrict e.target) :=
    openPartialHomeomorph_symm_aemeasurable_restrict_target e MeasureTheory.volume
  have h_ac :
      Measure.map e (μ.restrict e.source) ≪
        MeasureTheory.volume.restrict e.target := by
    rw [hmap]
    exact withDensity_absolutelyContinuous _ _
  exact hsymm_vol.mono_ac h_ac

/--
%%handwave
name:
  Pushing a chart measure back through the inverse chart
statement:
  For a chart (e), pushing (e_ast\(mu|_{\mathrm{source}}\)) forward by (e^{-1}) recovers \(mu|_{\mathrm{source}}\).
proof:
  Compose the two almost-everywhere measurable maps and use the chart left-inverse identity on the source.
-/
private theorem smoothPositiveMeasureOnManifold_chart_map_symm_map
    {H X : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (hμ : SmoothPositiveMeasureOnManifold (I := I) μ)
    (e : OpenPartialHomeomorph X H) (he : e ∈ atlas H X) :
    Measure.map e.symm (Measure.map e (μ.restrict e.source)) =
      μ.restrict e.source := by
  have he_aemeas : AEMeasurable e (μ.restrict e.source) :=
    openPartialHomeomorph_aemeasurable_restrict_source e μ
  have hsymm_aemeas :
      AEMeasurable e.symm (Measure.map e (μ.restrict e.source)) :=
    smoothPositiveMeasureOnManifold_chart_symm_aemeasurable μ hμ e he
  have hmap :
      Measure.map e.symm (Measure.map e (μ.restrict e.source)) =
        Measure.map (fun x : X ↦ e.symm (e x)) (μ.restrict e.source) := by
    simpa [Function.comp_def] using
      (AEMeasurable.map_map_of_aemeasurable hsymm_aemeas he_aemeas)
  have hleft :
      (fun x : X ↦ e.symm (e x)) =ᵐ[μ.restrict e.source] fun x ↦ x :=
    ae_restrict_of_forall_mem e.open_source.measurableSet fun x hx ↦
      e.left_inv hx
  calc
    Measure.map e.symm (Measure.map e (μ.restrict e.source))
        = Measure.map (fun x : X ↦ e.symm (e x)) (μ.restrict e.source) := hmap
    _ = Measure.map (fun x : X ↦ x) (μ.restrict e.source) :=
        Measure.map_congr hleft
    _ = μ.restrict e.source := by rw [Measure.map_id']

/--
%%handwave
name:
  Pulling almost-everywhere equality through an inverse chart
statement:
  If (f=g) almost everywhere on the manifold, then \(f\circ e^{-1}=g\circ e^{-1}\) almost everywhere for Lebesgue measure on the chart target.
proof:
  Restrict the original equality to the chart source, pull it through the inverse chart, and replace the chart measure by its equivalent positive-density Lebesgue measure.
-/
private theorem smoothPositiveMeasureOnManifold_chart_comp_symm_ae_eq
    {H X β : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (hμ : SmoothPositiveMeasureOnManifold (I := I) μ)
    (e : OpenPartialHomeomorph X H) (he : e ∈ atlas H X)
    {f g : X → β} (hfg : f =ᵐ[μ] g) :
    (fun z : H ↦ f (e.symm z)) =ᵐ[MeasureTheory.volume.restrict e.target]
      fun z ↦ g (e.symm z) := by
  have hfg_source : f =ᵐ[μ.restrict e.source] g :=
    ae_restrict_of_ae hfg
  have hsymm_aemeas :
      AEMeasurable e.symm (Measure.map e (μ.restrict e.source)) :=
    smoothPositiveMeasureOnManifold_chart_symm_aemeasurable μ hμ e he
  have hmap_symm :
      Measure.map e.symm (Measure.map e (μ.restrict e.source)) =
        μ.restrict e.source :=
    smoothPositiveMeasureOnManifold_chart_map_symm_map μ hμ e he
  have hmap_eq :
      (fun z : H ↦ f (e.symm z)) =ᵐ[Measure.map e (μ.restrict e.source)]
        fun z ↦ g (e.symm z) := by
    have hpull :
        f =ᵐ[Measure.map e.symm (Measure.map e (μ.restrict e.source))] g := by
      simpa [hmap_symm] using hfg_source
    exact ae_of_ae_map hsymm_aemeas hpull
  exact
    (smoothPositiveMeasureOnManifold_chart_ae_eq μ hμ e he).1 hmap_eq

/--
%%handwave
name:
  Lebesgue measure is dominated by a smooth positive chart measure
statement:
  On a chart target, restricted Lebesgue measure is absolutely continuous with respect to the pushforward of a smooth positive manifold measure.
proof:
  The pushforward has a smooth strictly positive density relative to Lebesgue measure, so every set null for it is Lebesgue-null.
-/
private theorem smoothPositiveMeasureOnManifold_chart_volume_ac_map
    {H X : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (hμ : SmoothPositiveMeasureOnManifold (I := I) μ)
    (e : OpenPartialHomeomorph X H) (he : e ∈ atlas H X) :
    MeasureTheory.volume.restrict e.target ≪
      Measure.map e (μ.restrict e.source) := by
  obtain ⟨ρ, hρ_smooth, hρ_pos, hmap⟩ := hμ.chart_density e he
  rw [hmap]
  have hρ_aemeas :
      AEMeasurable (fun z : H ↦ ENNReal.ofReal (ρ z))
        (MeasureTheory.volume.restrict e.target) := by
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      (hρ_smooth.continuousOn.aemeasurable e.open_target.measurableSet)
  have hρ_ne_zero :
      ∀ᵐ z ∂MeasureTheory.volume.restrict e.target,
        ENNReal.ofReal (ρ z) ≠ 0 := by
    exact ae_restrict_of_forall_mem e.open_target.measurableSet fun z hz ↦
      ne_of_gt (ENNReal.ofReal_pos.mpr (hρ_pos z hz))
  exact withDensity_absolutelyContinuous' hρ_aemeas hρ_ne_zero

/--
%%handwave
name:
  Strong measurability of a chart pullback
statement:
  If (f) is almost everywhere strongly measurable on the manifold and (K) lies in a chart target, then \(f\circ e^{-1}\) is almost everywhere strongly measurable for Lebesgue measure restricted to (K).
proof:
  Pull strong measurability through the inverse chart for the chart measure, transfer it by absolute continuity to Lebesgue measure, and restrict to (K).
-/
private theorem smoothPositiveMeasureOnManifold_chartPullback_aestronglyMeasurable
    {H X β : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace β]
    (μ : Measure X) (hμ : SmoothPositiveMeasureOnManifold (I := I) μ)
    (e : OpenPartialHomeomorph X H) (he : e ∈ atlas H X)
    (K : Set H) (hK : K ⊆ e.target) {f : X → β}
    (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun z : H ↦ f (e.symm z))
      (MeasureTheory.volume.restrict K) := by
  let ν : Measure H := Measure.map e (μ.restrict e.source)
  have hf_source : AEStronglyMeasurable f (μ.restrict e.source) := hf.restrict
  have hsymm : AEMeasurable e.symm ν := by
    simpa [ν] using
      smoothPositiveMeasureOnManifold_chart_symm_aemeasurable μ hμ e he
  have hmap_symm : Measure.map e.symm ν = μ.restrict e.source := by
    simpa [ν] using
      smoothPositiveMeasureOnManifold_chart_map_symm_map μ hμ e he
  have hpull_ν : AEStronglyMeasurable (fun z : H ↦ f (e.symm z)) ν := by
    have hf_map : AEStronglyMeasurable f (Measure.map e.symm ν) := by
      simpa [hmap_symm] using hf_source
    simpa [Function.comp_def] using hf_map.comp_aemeasurable hsymm
  have hvol_ac : MeasureTheory.volume.restrict e.target ≪ ν := by
    simpa [ν] using
      smoothPositiveMeasureOnManifold_chart_volume_ac_map μ hμ e he
  have hpull_target :
      AEStronglyMeasurable (fun z : H ↦ f (e.symm z))
        (MeasureTheory.volume.restrict e.target) :=
    MeasureTheory.AEStronglyMeasurable.mono_ac hvol_ac hpull_ν
  exact hpull_target.mono_measure (Measure.restrict_mono hK le_rfl)

/--
%%handwave
name:
  Local \(L^2\) integrability of chart pullbacks
statement:
  If (f\in L^2(mu)) and (K) is compactly contained in a chart region, then (f\circ e^{-1}in L^2(K,dx)).
proof:
  The smooth positive chart density has a positive minimum on (K); remove that density using the resulting lower bound and the chart change-of-variables formula.
-/
private theorem smoothPositiveMeasureOnManifold_chartPullback_memLp_two_restrict_compact
    {H X F : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold I 1 X]
    [TopologicalSpace F] [ContinuousENorm F]
    (μ : Measure X) (hμ : SmoothPositiveMeasureOnManifold (I := I) μ)
    (e : OpenPartialHomeomorph X H) (he : e ∈ atlas H X)
    (K : Set H) (hK_region : K ⊆ manifoldChartRegion e (Set.univ : Set X))
    (hK_compact : IsCompact K) {f : X → F} (hf : MemLp f 2 μ) :
    MemLp (fun z : H ↦ f (e.symm z)) 2 (MeasureTheory.volume.restrict K) := by
  classical
  rcases hμ.chart_density e he with ⟨ρ, hρ_smooth, hρ_pos, hmap⟩
  let ν : Measure H := MeasureTheory.volume.restrict e.target
  let δ : H → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (ρ z)
  have hK_target : K ⊆ e.target := by
    intro z hz
    exact (hK_region hz).1
  have hK_meas : MeasurableSet K := hK_compact.measurableSet
  rcases K.eq_empty_or_nonempty with hK_empty | hK_nonempty
  · have hzero : MeasureTheory.volume.restrict K = 0 := by
      simp [hK_empty]
    rw [hzero]
    exact memLp_measure_zero
  have hρ_cont_K : ContinuousOn ρ K :=
    hρ_smooth.continuousOn.mono hK_target
  rcases hK_compact.exists_sInf_image_eq_and_le hK_nonempty hρ_cont_K with
    ⟨z₀, hz₀K, _hz₀_inf, hz₀_min⟩
  let c : ℝ≥0∞ := ENNReal.ofReal (ρ z₀)
  have hc_pos : 0 < ρ z₀ := hρ_pos z₀ (hK_target hz₀K)
  have hc0 : c ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hc_pos)
  have hctop : c ≠ (⊤ : ℝ≥0∞) := by
    simp [c]
  have hδ_lower : ∀ᵐ z ∂ν.restrict K, c ≤ δ z := by
    filter_upwards [ae_restrict_mem hK_meas] with z hzK
    exact ENNReal.ofReal_le_ofReal (hz₀_min z hzK)
  let μs : Measure X := μ.restrict e.source
  let Fpull : H → F := fun z ↦ f (e.symm z)
  have he_aemeas : AEMeasurable e μs := by
    simpa [μs] using openPartialHomeomorph_aemeasurable_restrict_source e μ
  have hsymm_aemeas : AEMeasurable e.symm (Measure.map e μs) := by
    simpa [μs] using
      smoothPositiveMeasureOnManifold_chart_symm_aemeasurable μ hμ e he
  have hmap_symm :
      Measure.map e.symm (Measure.map e μs) = μs := by
    simpa [μs] using
      smoothPositiveMeasureOnManifold_chart_map_symm_map μ hμ e he
  have hf_source : MemLp f 2 μs := by
    simpa [μs] using hf.restrict e.source
  have hf_aestr_source : AEStronglyMeasurable f μs := by
    simpa [μs] using hf.aestronglyMeasurable.mono_measure Measure.restrict_le_self
  have hf_aestr_map_symm :
      AEStronglyMeasurable f (Measure.map e.symm (Measure.map e μs)) := by
    simpa [hmap_symm] using hf_aestr_source
  have hFpull_aestr :
      AEStronglyMeasurable Fpull (Measure.map e μs) := by
    simpa [Fpull, Function.comp_def] using
      hf_aestr_map_symm.comp_aemeasurable hsymm_aemeas
  have hcomp_eq :
      (fun x : X ↦ Fpull (e x)) =ᵐ[μs] f := by
    filter_upwards [show ∀ᵐ x ∂μs, x ∈ e.source from by
      simpa [μs] using
        (ae_restrict_mem e.open_source.measurableSet :
          ∀ᵐ x ∂μ.restrict e.source, x ∈ e.source)] with x hx_source
    simp [Fpull, e.left_inv hx_source]
  have hcomp_mem : MemLp (fun x : X ↦ Fpull (e x)) 2 μs :=
    (memLp_congr_ae hcomp_eq).2 hf_source
  have hF_map : MemLp Fpull 2 (Measure.map e μs) :=
    (memLp_map_measure_iff hFpull_aestr he_aemeas).2 hcomp_mem
  have hF_weighted : MemLp Fpull 2 (ν.withDensity δ) := by
    simpa [ν, δ, μs, hmap] using hF_map
  have hF_weighted_K : MemLp Fpull 2 ((ν.withDensity δ).restrict K) :=
    hF_weighted.restrict K
  have hF_νK : MemLp Fpull 2 (ν.restrict K) :=
    memLp_of_withDensity_lower_bound_on_restrict
      (ν := ν) (δ := δ) (K := K) (c := c)
      hK_meas hc0 hctop hδ_lower hF_weighted_K
  simpa [Fpull, ν, Measure.restrict_restrict_of_subset hK_target] using hF_νK

/--
%%handwave
name:
  Uniform local chart pullback estimate
statement:
  For a compact \(K\) in a chart region there is \(C<\infty\) such that
  \[
    \|f\circ e^{-1}\|_{L^2(K,dx)}\le C\|f\|_{L^2\(\mu\)}
  \]
  for every almost everywhere strongly measurable \(f\).
proof:
  Take the positive minimum of the smooth chart density on (K), apply the density norm comparison, and use change of variables plus restriction monotonicity.
-/
private theorem smoothPositiveMeasureOnManifold_chartPullback_eLpNorm_two_restrict_compact_le
    {H X F : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold I 1 X]
    [TopologicalSpace F] [ContinuousENorm F]
    (μ : Measure X) (hμ : SmoothPositiveMeasureOnManifold (I := I) μ)
    (e : OpenPartialHomeomorph X H) (he : e ∈ atlas H X)
    (K : Set H) (hK_region : K ⊆ manifoldChartRegion e (Set.univ : Set X))
    (hK_compact : IsCompact K) :
    ∃ C : NNReal,
      ∀ f : X → F, AEStronglyMeasurable f μ →
        eLpNorm (fun z : H ↦ f (e.symm z)) 2
            (MeasureTheory.volume.restrict K) ≤
          (C : ℝ≥0∞) * eLpNorm f 2 μ := by
  classical
  rcases hμ.chart_density e he with ⟨ρ, hρ_smooth, hρ_pos, hmap⟩
  let ν : Measure H := MeasureTheory.volume.restrict e.target
  let δ : H → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (ρ z)
  have hK_target : K ⊆ e.target := by
    intro z hz
    exact (hK_region hz).1
  have hK_meas : MeasurableSet K := hK_compact.measurableSet
  rcases K.eq_empty_or_nonempty with hK_empty | hK_nonempty
  · refine ⟨0, ?_⟩
    intro f hf
    have hzero : MeasureTheory.volume.restrict K = 0 := by
      simp [hK_empty]
    simp [hzero]
  have hρ_cont_K : ContinuousOn ρ K :=
    hρ_smooth.continuousOn.mono hK_target
  rcases hK_compact.exists_sInf_image_eq_and_le hK_nonempty hρ_cont_K with
    ⟨z₀, hz₀K, _hz₀_inf, hz₀_min⟩
  let c : ℝ≥0∞ := ENNReal.ofReal (ρ z₀)
  let q : ℝ := ((1 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal
  let Cₑ : ℝ≥0∞ := c⁻¹ ^ q
  have hc_pos : 0 < ρ z₀ := hρ_pos z₀ (hK_target hz₀K)
  have hc0 : c ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hc_pos)
  have hctop : c ≠ (⊤ : ℝ≥0∞) := by
    simp [c]
  have hδ_lower : ∀ᵐ z ∂ν.restrict K, c ≤ δ z := by
    filter_upwards [ae_restrict_mem hK_meas] with z hzK
    exact ENNReal.ofReal_le_ofReal (hz₀_min z hzK)
  have hq_nonneg : 0 ≤ q := by
    norm_num [q]
  have hCₑ_ne_top : Cₑ ≠ (⊤ : ℝ≥0∞) := by
    exact (ENNReal.rpow_lt_top_of_nonneg hq_nonneg
      (by simpa using (ENNReal.inv_ne_top.2 hc0))).ne
  refine ⟨Cₑ.toNNReal, ?_⟩
  intro f hf_aestr
  let μs : Measure X := μ.restrict e.source
  let Fpull : H → F := fun z ↦ f (e.symm z)
  have he_aemeas : AEMeasurable e μs := by
    simpa [μs] using openPartialHomeomorph_aemeasurable_restrict_source e μ
  have hsymm_aemeas : AEMeasurable e.symm (Measure.map e μs) := by
    simpa [μs] using
      smoothPositiveMeasureOnManifold_chart_symm_aemeasurable μ hμ e he
  have hmap_symm :
      Measure.map e.symm (Measure.map e μs) = μs := by
    simpa [μs] using
      smoothPositiveMeasureOnManifold_chart_map_symm_map μ hμ e he
  have hf_aestr_source : AEStronglyMeasurable f μs := by
    simpa [μs] using hf_aestr.mono_measure Measure.restrict_le_self
  have hf_aestr_map_symm :
      AEStronglyMeasurable f (Measure.map e.symm (Measure.map e μs)) := by
    simpa [hmap_symm] using hf_aestr_source
  have hFpull_aestr :
      AEStronglyMeasurable Fpull (Measure.map e μs) := by
    simpa [Fpull, Function.comp_def] using
      hf_aestr_map_symm.comp_aemeasurable hsymm_aemeas
  have hweighted_full :
      eLpNorm Fpull 2 (ν.withDensity δ) = eLpNorm f 2 μs := by
    calc
      eLpNorm Fpull 2 (ν.withDensity δ)
          = eLpNorm Fpull 2 (Measure.map e μs) := by
              simp [ν, δ, μs, hmap]
      _ = eLpNorm (fun x : X ↦ Fpull (e x)) 2 μs := by
              exact eLpNorm_map_measure hFpull_aestr he_aemeas
      _ = eLpNorm f 2 μs := by
              apply eLpNorm_congr_ae
              filter_upwards [show ∀ᵐ x ∂μs, x ∈ e.source from by
                simpa [μs] using
                  (ae_restrict_mem e.open_source.measurableSet :
                    ∀ᵐ x ∂μ.restrict e.source, x ∈ e.source)] with x hx_source
              simp [Fpull, e.left_inv hx_source]
  have hrestrict_le :
      eLpNorm Fpull 2 ((ν.withDensity δ).restrict K) ≤
        eLpNorm Fpull 2 (ν.withDensity δ) :=
    eLpNorm_mono_measure Fpull Measure.restrict_le_self
  have hsource_le :
      eLpNorm f 2 μs ≤ eLpNorm f 2 μ :=
    eLpNorm_mono_measure f Measure.restrict_le_self
  have hνK_eq : ν.restrict K = MeasureTheory.volume.restrict K := by
    simpa [ν] using Measure.restrict_restrict_of_subset (μ := MeasureTheory.volume) hK_target
  have hcompare :
      eLpNorm Fpull 2 (ν.restrict K) ≤
        Cₑ * eLpNorm Fpull 2 ((ν.withDensity δ).restrict K) := by
    simpa [Cₑ, q] using
      eLpNorm_two_of_withDensity_lower_bound_on_restrict_le
        (ν := ν) (δ := δ) (K := K) (c := c)
        hK_meas hc0 hctop hδ_lower Fpull
  calc
    eLpNorm (fun z : H ↦ f (e.symm z)) 2
        (MeasureTheory.volume.restrict K)
        = eLpNorm Fpull 2 (ν.restrict K) := by
            simp [Fpull, hνK_eq]
    _ ≤ Cₑ * eLpNorm Fpull 2 ((ν.withDensity δ).restrict K) := hcompare
    _ ≤ Cₑ * eLpNorm Fpull 2 (ν.withDensity δ) :=
        mul_le_mul_right hrestrict_le Cₑ
    _ = Cₑ * eLpNorm f 2 μs := by
        rw [hweighted_full]
    _ ≤ Cₑ * eLpNorm f 2 μ :=
        mul_le_mul_right hsource_le Cₑ
    _ = (Cₑ.toNNReal : ℝ≥0∞) * eLpNorm f 2 μ := by
        rw [ENNReal.coe_toNNReal hCₑ_ne_top]

/--
%%handwave
name:
  Value multipliers are locally square-integrable in coordinates
statement:
  In a coordinate chart, a bounded compactly supported scalar multiplier times
  a square-integrable value-section representative is square-integrable on the
  multiplier support with respect to Lebesgue measure.
proof:
  On the compact support, the smooth positive coordinate density is bounded
  above and below.  Thus square-integrability for the intrinsic measure is
  equivalent to square-integrability of the pulled-back representative with
  respect to coordinate Lebesgue measure.  Multiplication by a bounded scalar
  preserves \(L^2\).
-/
theorem manifoldValueCompactlySupportedMultiplier_memLp_two_on_support
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [IsManifold I 1 X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology (Bundle.TotalSpace E (Bundle.Trivial X E))]
    [TopologicalSpace.PseudoMetrizableSpace (Bundle.TotalSpace E (Bundle.Trivial X E))]
    (μ : Measure X) (_hμ : SmoothPositiveMeasureOnManifold (I := I) μ) :
    ∀ (e : OpenPartialHomeomorph X H) (_he : e ∈ atlas H X)
      (a : H → ℝ),
      Continuous a →
      (∃ C : NNReal, ∀ z : H, ‖a z‖ ≤ C) →
      tsupport a ⊆ manifoldChartRegion e (Set.univ : Set X) →
      IsCompact (tsupport a) →
      ∀ w : SquareIntegrableValueSection (X := X) (E := E) μ,
        MemLp
          (fun z ↦ a z • w.toFunction (e.symm z))
          2
          (MeasureTheory.volume.restrict (tsupport a)) := by
  intro e he a ha_cont ha_bound ha_support ha_compact w
  classical
  rcases _hμ.chart_density e he with ⟨ρ, hρ_smooth, hρ_pos, hmap⟩
  let K : Set H := tsupport a
  let F : H → E := fun z ↦ a z • w.toFunction (e.symm z)
  let ν : Measure H := MeasureTheory.volume.restrict e.target
  let δ : H → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (ρ z)
  have hK_target : K ⊆ e.target := by
    intro z hz
    exact (ha_support hz).1
  have hK_meas : MeasurableSet K := ha_compact.measurableSet
  rcases K.eq_empty_or_nonempty with hK_empty | hK_nonempty
  · have hzero : MeasureTheory.volume.restrict K = 0 := by
      simp [K, hK_empty]
    rw [hzero]
    exact memLp_measure_zero
  have hρ_cont_K : ContinuousOn ρ K :=
    hρ_smooth.continuousOn.mono hK_target
  rcases ha_compact.exists_sInf_image_eq_and_le hK_nonempty hρ_cont_K with
    ⟨z₀, hz₀K, _hz₀_inf, hz₀_min⟩
  let c : ℝ≥0∞ := ENNReal.ofReal (ρ z₀)
  have hc_pos : 0 < ρ z₀ := hρ_pos z₀ (hK_target hz₀K)
  have hc0 : c ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hc_pos)
  have hctop : c ≠ (⊤ : ℝ≥0∞) := by
    simp [c]
  have hδ_lower : ∀ᵐ z ∂ν.restrict K, c ≤ δ z := by
    filter_upwards [ae_restrict_mem hK_meas] with z hzK
    exact ENNReal.ofReal_le_ofReal (hz₀_min z hzK)

  let μs : Measure X := μ.restrict e.source
  have he_aemeas : AEMeasurable e μs := by
    simpa [μs] using openPartialHomeomorph_aemeasurable_restrict_source e μ
  have hsymm_aemeas : AEMeasurable e.symm (Measure.map e μs) := by
    simpa [μs] using
      smoothPositiveMeasureOnManifold_chart_symm_aemeasurable μ _hμ e he
  have hmap_symm :
      Measure.map e.symm (Measure.map e μs) = μs := by
    simpa [μs] using
      smoothPositiveMeasureOnManifold_chart_map_symm_map μ _hμ e he

  have hw_mem : MemLp w.toFunction 2 μ :=
    squareIntegrableValueSection_memLp (I := I) μ w
  have hw_source : MemLp w.toFunction 2 μs := by
    simpa [μs] using hw_mem.restrict e.source
  have hb_aemeas : AEMeasurable (fun x : X ↦ a (e x)) μs :=
    ha_cont.aemeasurable.comp_aemeasurable he_aemeas
  have hb_aestr : AEStronglyMeasurable (fun x : X ↦ a (e x)) μs :=
    hb_aemeas.aestronglyMeasurable
  rcases ha_bound with ⟨C, hC⟩
  have hb_bound : ∀ᵐ x ∂μs, ‖a (e x)‖ ≤ (C : ℝ) :=
    Filter.Eventually.of_forall fun x ↦ hC (e x)
  have hb_top : MemLp (fun x : X ↦ a (e x)) ∞ μs :=
    memLp_top_of_bound hb_aestr (C : ℝ) hb_bound
  have hsource_prod :
      MemLp (fun x : X ↦ a (e x) • w.toFunction x) 2 μs := by
    simpa [Pi.smul_apply] using
      (hw_source.smul (p := ∞) (q := 2) (r := 2) hb_top)

  have hw_aestr_source :
      AEStronglyMeasurable w.toFunction μs := by
    simpa [μs] using
      (squareIntegrableValueSection_aestronglyMeasurable (I := I) μ w).mono_measure
        Measure.restrict_le_self
  have hw_aestr_map_symm :
      AEStronglyMeasurable w.toFunction
        (Measure.map e.symm (Measure.map e μs)) := by
    simpa [hmap_symm] using hw_aestr_source
  have hw_symm_aestr :
      AEStronglyMeasurable (fun z : H ↦ w.toFunction (e.symm z))
        (Measure.map e μs) := by
    simpa [Function.comp_def] using
      hw_aestr_map_symm.comp_aemeasurable hsymm_aemeas
  have ha_aestr_map : AEStronglyMeasurable a (Measure.map e μs) :=
    ha_cont.aestronglyMeasurable
  have hF_aestr : AEStronglyMeasurable F (Measure.map e μs) := by
    simpa [F] using ha_aestr_map.smul hw_symm_aestr
  have hcomp_eq :
      (fun x : X ↦ F (e x)) =ᵐ[μs]
        fun x : X ↦ a (e x) • w.toFunction x := by
    filter_upwards [show ∀ᵐ x ∂μs, x ∈ e.source from by
      simpa [μs] using
        (ae_restrict_mem e.open_source.measurableSet :
          ∀ᵐ x ∂μ.restrict e.source, x ∈ e.source)] with x hx_source
    simp [F, e.left_inv hx_source]
  have hcomp_mem : MemLp (fun x : X ↦ F (e x)) 2 μs :=
    (memLp_congr_ae hcomp_eq).2 hsource_prod
  have hF_map : MemLp F 2 (Measure.map e μs) :=
    (memLp_map_measure_iff hF_aestr he_aemeas).2 hcomp_mem
  have hF_weighted : MemLp F 2 (ν.withDensity δ) := by
    simpa [ν, δ, μs, hmap] using hF_map
  have hF_weighted_K : MemLp F 2 ((ν.withDensity δ).restrict K) :=
    hF_weighted.restrict K
  have hF_νK : MemLp F 2 (ν.restrict K) :=
    memLp_of_withDensity_lower_bound_on_restrict
      (ν := ν) (δ := δ) (K := K) (c := c)
      hK_meas hc0 hctop hδ_lower hF_weighted_K
  simpa [F, K, ν, Measure.restrict_restrict_of_subset hK_target] using hF_νK

/--
%%handwave
name:
  Local chart estimate for Hilbert-valued manifold functions
statement:
  A Hilbert-valued \(L^2\) function obeys a uniform \(L^2\) pullback bound on every compact subset of a chart region.
proof:
  Apply the general smooth-positive-measure chart estimate to the canonical strongly measurable representative of the \(L^2\) function.
-/
private theorem manifoldValueChartPullback_eLpNorm_two_restrict_compact_le
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [IsManifold I 1 X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology (Bundle.TotalSpace E (Bundle.Trivial X E))]
    [TopologicalSpace.PseudoMetrizableSpace (Bundle.TotalSpace E (Bundle.Trivial X E))]
    (μ : Measure X) (_hμ : SmoothPositiveMeasureOnManifold (I := I) μ)
    (e : OpenPartialHomeomorph X H) (he : e ∈ atlas H X)
    (K : Set H) (hK_region : K ⊆ manifoldChartRegion e (Set.univ : Set X))
    (hK_compact : IsCompact K) :
    ∃ C : NNReal,
      ∀ w : SquareIntegrableValueSection (X := X) (E := E) μ,
        eLpNorm (fun z : H ↦ w.toFunction (e.symm z)) 2
            (MeasureTheory.volume.restrict K) ≤
          (C : ℝ≥0∞) * eLpNorm w.toFunction 2 μ := by
  classical
  rcases _hμ.chart_density e he with ⟨ρ, hρ_smooth, hρ_pos, hmap⟩
  let ν : Measure H := MeasureTheory.volume.restrict e.target
  let δ : H → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (ρ z)
  have hK_target : K ⊆ e.target := by
    intro z hz
    exact (hK_region hz).1
  have hK_meas : MeasurableSet K := hK_compact.measurableSet
  rcases K.eq_empty_or_nonempty with hK_empty | hK_nonempty
  · refine ⟨0, ?_⟩
    intro w
    have hzero : MeasureTheory.volume.restrict K = 0 := by
      simp [hK_empty]
    simp [hzero]
  have hρ_cont_K : ContinuousOn ρ K :=
    hρ_smooth.continuousOn.mono hK_target
  rcases hK_compact.exists_sInf_image_eq_and_le hK_nonempty hρ_cont_K with
    ⟨z₀, hz₀K, _hz₀_inf, hz₀_min⟩
  let c : ℝ≥0∞ := ENNReal.ofReal (ρ z₀)
  let q : ℝ := ((1 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal
  let Cₑ : ℝ≥0∞ := c⁻¹ ^ q
  have hc_pos : 0 < ρ z₀ := hρ_pos z₀ (hK_target hz₀K)
  have hc0 : c ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hc_pos)
  have hctop : c ≠ (⊤ : ℝ≥0∞) := by
    simp [c]
  have hδ_lower : ∀ᵐ z ∂ν.restrict K, c ≤ δ z := by
    filter_upwards [ae_restrict_mem hK_meas] with z hzK
    exact ENNReal.ofReal_le_ofReal (hz₀_min z hzK)
  have hq_nonneg : 0 ≤ q := by
    norm_num [q]
  have hCₑ_ne_top : Cₑ ≠ (⊤ : ℝ≥0∞) := by
    exact (ENNReal.rpow_lt_top_of_nonneg hq_nonneg
      (by simpa using (ENNReal.inv_ne_top.2 hc0))).ne
  refine ⟨Cₑ.toNNReal, ?_⟩
  intro w
  let μs : Measure X := μ.restrict e.source
  let f : H → E := fun z ↦ w.toFunction (e.symm z)
  have he_aemeas : AEMeasurable e μs := by
    simpa [μs] using openPartialHomeomorph_aemeasurable_restrict_source e μ
  have hsymm_aemeas : AEMeasurable e.symm (Measure.map e μs) := by
    simpa [μs] using
      smoothPositiveMeasureOnManifold_chart_symm_aemeasurable μ _hμ e he
  have hmap_symm :
      Measure.map e.symm (Measure.map e μs) = μs := by
    simpa [μs] using
      smoothPositiveMeasureOnManifold_chart_map_symm_map μ _hμ e he
  have hw_aestr_source :
      AEStronglyMeasurable w.toFunction μs := by
    simpa [μs] using
      (squareIntegrableValueSection_aestronglyMeasurable (I := I) μ w).mono_measure
        Measure.restrict_le_self
  have hw_aestr_map_symm :
      AEStronglyMeasurable w.toFunction
        (Measure.map e.symm (Measure.map e μs)) := by
    simpa [hmap_symm] using hw_aestr_source
  have hf_map_aestr :
      AEStronglyMeasurable f (Measure.map e μs) := by
    simpa [f, Function.comp_def] using
      hw_aestr_map_symm.comp_aemeasurable hsymm_aemeas
  have hweighted_full :
      eLpNorm f 2 (ν.withDensity δ) = eLpNorm w.toFunction 2 μs := by
    calc
      eLpNorm f 2 (ν.withDensity δ)
          = eLpNorm f 2 (Measure.map e μs) := by
              simp [ν, δ, μs, hmap]
      _ = eLpNorm (fun x : X ↦ f (e x)) 2 μs := by
              exact eLpNorm_map_measure hf_map_aestr he_aemeas
      _ = eLpNorm w.toFunction 2 μs := by
              apply eLpNorm_congr_ae
              filter_upwards [show ∀ᵐ x ∂μs, x ∈ e.source from by
                simpa [μs] using
                  (ae_restrict_mem e.open_source.measurableSet :
                    ∀ᵐ x ∂μ.restrict e.source, x ∈ e.source)] with x hx_source
              simp [f, e.left_inv hx_source]
  have hrestrict_le :
      eLpNorm f 2 ((ν.withDensity δ).restrict K) ≤
        eLpNorm f 2 (ν.withDensity δ) :=
    eLpNorm_mono_measure f Measure.restrict_le_self
  have hsource_le :
      eLpNorm w.toFunction 2 μs ≤ eLpNorm w.toFunction 2 μ :=
    eLpNorm_mono_measure w.toFunction Measure.restrict_le_self
  have hνK_eq : ν.restrict K = MeasureTheory.volume.restrict K := by
    simpa [ν] using Measure.restrict_restrict_of_subset (μ := MeasureTheory.volume) hK_target
  have hcompare :
      eLpNorm f 2 (ν.restrict K) ≤
        Cₑ * eLpNorm f 2 ((ν.withDensity δ).restrict K) := by
    simpa [Cₑ, q] using
      eLpNorm_two_of_withDensity_lower_bound_on_restrict_le
        (ν := ν) (δ := δ) (K := K) (c := c)
        hK_meas hc0 hctop hδ_lower f
  calc
    eLpNorm (fun z : H ↦ w.toFunction (e.symm z)) 2
        (MeasureTheory.volume.restrict K)
        = eLpNorm f 2 (ν.restrict K) := by
            simp [f, hνK_eq]
    _ ≤ Cₑ * eLpNorm f 2 ((ν.withDensity δ).restrict K) := hcompare
    _ ≤ Cₑ * eLpNorm f 2 (ν.withDensity δ) :=
        mul_le_mul_right hrestrict_le Cₑ
    _ = Cₑ * eLpNorm w.toFunction 2 μs := by
        rw [hweighted_full]
    _ ≤ Cₑ * eLpNorm w.toFunction 2 μ :=
        mul_le_mul_right hsource_le Cₑ
    _ = (Cₑ.toNNReal : ℝ≥0∞) * eLpNorm w.toFunction 2 μ := by
        rw [ENNReal.coe_toNNReal hCₑ_ne_top]

/--
%%handwave
name:
  Bounded compactly supported coordinate multipliers give integrable value
  pairings
statement:
  In a coordinate chart, multiplying a square-integrable value-section
  representative by a bounded continuous scalar multiplier with compact
  support inside the coordinate region gives a Bochner integrable function.
proof:
  On the compact support, the smooth positive coordinate density is bounded
  above and below, so the pulled-back representative is locally \(L^2\) with
  respect to Lebesgue measure.  The multiplier is bounded and supported on a
  finite-measure compact set.  Cauchy--Schwarz gives \(L^1\)-integrability.
-/
theorem manifoldValueCompactlySupportedMultiplier_integrable
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [IsManifold I 1 X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology (Bundle.TotalSpace E (Bundle.Trivial X E))]
    [TopologicalSpace.PseudoMetrizableSpace (Bundle.TotalSpace E (Bundle.Trivial X E))]
    (μ : Measure X) (_hμ : SmoothPositiveMeasureOnManifold (I := I) μ) :
    ∀ (e : OpenPartialHomeomorph X H) (_he : e ∈ atlas H X)
      (a : H → ℝ),
      Continuous a →
      (∃ C : NNReal, ∀ z : H, ‖a z‖ ≤ C) →
      tsupport a ⊆ manifoldChartRegion e (Set.univ : Set X) →
      IsCompact (tsupport a) →
      ∀ w : SquareIntegrableValueSection (X := X) (E := E) μ,
        Integrable
          (fun z ↦ a z • w.toFunction (e.symm z))
          (MeasureTheory.volume.restrict
            (manifoldChartRegion e (Set.univ : Set X))) := by
  intro e he a ha_cont ha_bound ha_support ha_compact w
  let Ω : Set H := manifoldChartRegion e (Set.univ : Set X)
  let F : H → E := fun z ↦ a z • w.toFunction (e.symm z)
  have hF_memLp :
      MemLp F 2 (MeasureTheory.volume.restrict (tsupport a)) := by
    simpa [F] using
      manifoldValueCompactlySupportedMultiplier_memLp_two_on_support
        (I := I) (X := X) (E := E) μ _hμ e he a
        ha_cont ha_bound ha_support ha_compact w
  have hK_finite :
      MeasureTheory.volume (tsupport a) ≠ (∞ : ℝ≥0∞) :=
    smoothPositiveMeasureOnManifold_chart_volume_finite_of_compact
      (I := I) (X := X) μ _hμ e he (tsupport a)
      (by simpa [Ω] using ha_support) ha_compact
  have hF_support : Function.support F ⊆ tsupport a := by
    intro z hz
    by_contra hz_support
    have ha_zero : a z = 0 := image_eq_zero_of_notMem_tsupport hz_support
    exact hz (by simp [F, ha_zero])
  exact integrableOn_region_of_memLp_two_restrict_support
    (ν := MeasureTheory.volume) (Ω := Ω) (K := tsupport a)
    hF_memLp hK_finite hF_support (by simpa [Ω] using ha_support)

/--
%%handwave
name:
  Almost-everywhere congruence for compactly supported multiplier integrals
statement:
  Replacing an \(L^2\) manifold function by an almost-everywhere equal representative does not change its chart integral after multiplication by a fixed compactly supported coordinate factor.
proof:
  Pull the equality into the chart, multiply it pointwise by the fixed factor, and use congruence of the Bochner integral.
-/
private theorem manifoldValueCompactlySupportedMultiplier_integral_congr_ae
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [IsManifold I 1 X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology (Bundle.TotalSpace E (Bundle.Trivial X E))]
    [TopologicalSpace.PseudoMetrizableSpace (Bundle.TotalSpace E (Bundle.Trivial X E))]
    (μ : Measure X) (hμ : SmoothPositiveMeasureOnManifold (I := I) μ)
    (e : OpenPartialHomeomorph X H) (he : e ∈ atlas H X)
    (a : H → ℝ)
    {w₁ w₂ : SquareIntegrableValueSection (X := X) (E := E) μ}
    (hw : w₁.toFunction =ᵐ[μ] w₂.toFunction) :
    (∫ z in manifoldChartRegion e (Set.univ : Set X),
        a z • w₁.toFunction (e.symm z) ∂MeasureTheory.volume) =
      ∫ z in manifoldChartRegion e (Set.univ : Set X),
        a z • w₂.toFunction (e.symm z) ∂MeasureTheory.volume := by
  have hcoord :
      (fun z : H ↦ w₁.toFunction (e.symm z)) =ᵐ[MeasureTheory.volume.restrict e.target]
        fun z ↦ w₂.toFunction (e.symm z) :=
    smoothPositiveMeasureOnManifold_chart_comp_symm_ae_eq μ hμ e he hw
  refine integral_congr_ae ?_
  simpa [manifoldChartRegion] using hcoord.mono fun z hz ↦ by simp [hz]

/--
%%handwave
name:
  Bounded compactly supported coordinate multipliers give Lipschitz value
  pairings
statement:
  In a coordinate chart, integration against a bounded continuous scalar
  multiplier with compact support inside the coordinate region is Lipschitz in
  the intrinsic \(L^2\)-distance of value-section representatives.
proof:
  Apply the preceding integrability estimate to differences.  The local
  comparison of the smooth positive measure with coordinate Lebesgue measure
  and the boundedness of the multiplier reduce the estimate to the
  Cauchy--Schwarz inequality on its compact support.
-/
theorem manifoldValueCompactlySupportedMultiplier_integral_lipschitz_estimate
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [IsManifold I 1 X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology (Bundle.TotalSpace E (Bundle.Trivial X E))]
    [TopologicalSpace.PseudoMetrizableSpace (Bundle.TotalSpace E (Bundle.Trivial X E))]
    (μ : Measure X) (_hμ : SmoothPositiveMeasureOnManifold (I := I) μ) :
    letI : NormedAddCommGroup (ValueL2Section (X := X) (E := E) μ) :=
      valueL2SectionNormedAddCommGroup (I := I) (X := X) (E := E) μ
    ∀ (e : OpenPartialHomeomorph X H) (_he : e ∈ atlas H X)
      (a : H → ℝ),
      Continuous a →
      (∃ C : NNReal, ∀ z : H, ‖a z‖ ≤ C) →
      tsupport a ⊆ manifoldChartRegion e (Set.univ : Set X) →
      IsCompact (tsupport a) →
      ∃ K : NNReal,
        ∀ w₁ w₂ : SquareIntegrableValueSection (X := X) (E := E) μ,
          edist
            (∫ z in manifoldChartRegion e (Set.univ : Set X),
              a z • w₁.toFunction (e.symm z)
              ∂MeasureTheory.volume)
            (∫ z in manifoldChartRegion e (Set.univ : Set X),
              a z • w₂.toFunction (e.symm z)
              ∂MeasureTheory.volume) ≤
            K *
              edist
                (Quotient.mk
                  (SquareIntegrableValueSection.aeSetoid
                    (X := X) (E := E) (μ := μ)) w₁ :
                  ValueL2Section (X := X) (E := E) μ)
                (Quotient.mk
                  (SquareIntegrableValueSection.aeSetoid
                    (X := X) (E := E) (μ := μ)) w₂ :
                  ValueL2Section (X := X) (E := E) μ) := by
  classical
  letI : NormedAddCommGroup (ValueL2Section (X := X) (E := E) μ) :=
    valueL2SectionNormedAddCommGroup (I := I) (X := X) (E := E) μ
  intro e he a ha_cont ha_bound ha_support ha_compact
  rcases ha_bound with ⟨Ca, hCa⟩
  let Ω : Set H := manifoldChartRegion e (Set.univ : Set X)
  let K : Set H := tsupport a
  let q : ℝ := ((1 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal
  let Mpow : ℝ≥0∞ := MeasureTheory.volume K ^ q
  rcases manifoldValueChartPullback_eLpNorm_two_restrict_compact_le
      (I := I) (X := X) (E := E) μ _hμ e he K
      (by simpa [K, Ω] using ha_support) ha_compact with
    ⟨Cchart, hCchart⟩
  let B : ℝ≥0∞ := Mpow * (Ca : ℝ≥0∞) * (Cchart : ℝ≥0∞)
  have hK_finite : MeasureTheory.volume K ≠ (∞ : ℝ≥0∞) :=
    smoothPositiveMeasureOnManifold_chart_volume_finite_of_compact
      (I := I) (X := X) μ _hμ e he K
      (by simpa [K, Ω] using ha_support) ha_compact
  have hq_nonneg : 0 ≤ q := by
    norm_num [q]
  have hMpow_ne_top : Mpow ≠ (∞ : ℝ≥0∞) := by
    exact (ENNReal.rpow_lt_top_of_nonneg hq_nonneg
      (by simpa [Mpow, K] using hK_finite)).ne
  have hB_ne_top : B ≠ (∞ : ℝ≥0∞) := by
    dsimp [B]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top hMpow_ne_top ENNReal.coe_ne_top)
      ENNReal.coe_ne_top
  refine ⟨B.toNNReal, ?_⟩
  intro w₁ w₂
  let μΩ : Measure H := MeasureTheory.volume.restrict Ω
  let wdiff : SquareIntegrableValueSection (X := X) (E := E) μ :=
    squareIntegrableHilbertBundleSectionSub
      (I := I) (G := trivialHilbertBundleGeometry X E)
      (fun _ _ _ ↦ rfl) μ w₁ w₂
  let F₁ : H → E := fun z ↦ a z • w₁.toFunction (e.symm z)
  let F₂ : H → E := fun z ↦ a z • w₂.toFunction (e.symm z)
  let f : H → E := fun z ↦ wdiff.toFunction (e.symm z)
  let Fdiff : H → E := fun z ↦ a z • f z
  let u₁ : ValueL2Section (X := X) (E := E) μ :=
    Quotient.mk
      (SquareIntegrableValueSection.aeSetoid
        (X := X) (E := E) (μ := μ)) w₁
  let u₂ : ValueL2Section (X := X) (E := E) μ :=
    Quotient.mk
      (SquareIntegrableValueSection.aeSetoid
        (X := X) (E := E) (μ := μ)) w₂
  have hF₁_int : Integrable F₁ μΩ := by
    simpa [F₁, μΩ, Ω] using
      manifoldValueCompactlySupportedMultiplier_integrable
        (I := I) (X := X) (E := E) μ _hμ e he a
        ha_cont ⟨Ca, hCa⟩ (by simpa [K, Ω] using ha_support)
        ha_compact w₁
  have hF₂_int : Integrable F₂ μΩ := by
    simpa [F₂, μΩ, Ω] using
      manifoldValueCompactlySupportedMultiplier_integrable
        (I := I) (X := X) (E := E) μ _hμ e he a
        ha_cont ⟨Ca, hCa⟩ (by simpa [K, Ω] using ha_support)
        ha_compact w₂
  have hFdiff_memLp2 : MemLp Fdiff 2 (MeasureTheory.volume.restrict K) := by
    simpa [Fdiff, f, K] using
      manifoldValueCompactlySupportedMultiplier_memLp_two_on_support
        (I := I) (X := X) (E := E) μ _hμ e he a
        ha_cont ⟨Ca, hCa⟩ (by simpa [K, Ω] using ha_support)
        ha_compact wdiff
  have hsub_ae : (fun z : H ↦ F₁ z - F₂ z) =ᵐ[μΩ] Fdiff := by
    filter_upwards [] with z
    simp [F₁, F₂, Fdiff, f, wdiff,
      squareIntegrableHilbertBundleSectionSub, SquareIntegrableValueSection.toFunction,
      Pi.add_apply, Pi.neg_apply, sub_eq_add_neg]
  have hintegral_sub :
      (∫ z, F₁ z ∂μΩ) - (∫ z, F₂ z ∂μΩ) =
        ∫ z, Fdiff z ∂μΩ := by
    rw [← integral_sub hF₁_int hF₂_int]
    exact integral_congr_ae hsub_ae
  have hFdiff_support : Function.support Fdiff ⊆ K := by
    intro z hz
    by_contra hzK
    have ha_zero : a z = 0 := image_eq_zero_of_notMem_tsupport (by simpa [K] using hzK)
    exact hz (by simp [Fdiff, ha_zero])
  have hrestrict_eq :
      eLpNorm Fdiff 1 μΩ = eLpNorm Fdiff 1 (MeasureTheory.volume.restrict K) := by
    rw [← eLpNorm_restrict_eq_of_support_subset
      (μ := μΩ) (s := K) (p := (1 : ℝ≥0∞)) hFdiff_support]
    rw [Measure.restrict_restrict_of_subset]
    exact by
      simpa [μΩ, Ω, K] using ha_support
  have hL1L2 :
      eLpNorm Fdiff 1 (MeasureTheory.volume.restrict K) ≤
        eLpNorm Fdiff 2 (MeasureTheory.volume.restrict K) * Mpow := by
    have h :=
      eLpNorm_le_eLpNorm_mul_rpow_measure_univ
        (μ := MeasureTheory.volume.restrict K) (f := Fdiff)
        (p := (1 : ℝ≥0∞)) (q := (2 : ℝ≥0∞))
        (by norm_num) hFdiff_memLp2.1
    have h' :
        eLpNorm Fdiff 1 (MeasureTheory.volume.restrict K) ≤
          eLpNorm Fdiff 2 (MeasureTheory.volume.restrict K) *
            MeasureTheory.volume K ^
              (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) := by
      simpa [Measure.restrict_apply_univ] using h
    have hq_eq :
        (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) = q := by
      norm_num [q]
    have hq_eq' : (1 : ℝ) - (2 : ℝ)⁻¹ = q := by
      norm_num [q]
    simpa [Mpow, hq_eq, hq_eq'] using h'
  have hmul2 :
      eLpNorm Fdiff 2 (MeasureTheory.volume.restrict K) ≤
        (Ca : ℝ≥0∞) * eLpNorm f 2 (MeasureTheory.volume.restrict K) := by
    have hnorm_ae :
        ∀ᵐ z ∂MeasureTheory.volume.restrict K,
          ‖Fdiff z‖ ≤ ‖(Ca : ℝ) • f z‖ := by
      filter_upwards [] with z
      calc
        ‖Fdiff z‖ = ‖a z • f z‖ := rfl
        _ = ‖a z‖ * ‖f z‖ := norm_smul (a z) (f z)
        _ ≤ (Ca : ℝ) * ‖f z‖ :=
            mul_le_mul_of_nonneg_right (hCa z) (norm_nonneg _)
        _ = ‖(Ca : ℝ) • f z‖ := by
            rw [norm_smul, Real.norm_of_nonneg (NNReal.coe_nonneg Ca)]
    calc
      eLpNorm Fdiff 2 (MeasureTheory.volume.restrict K)
          ≤ eLpNorm (fun z : H ↦ (Ca : ℝ) • f z) 2
              (MeasureTheory.volume.restrict K) :=
            eLpNorm_mono_ae hnorm_ae
      _ = (Ca : ℝ≥0∞) * eLpNorm f 2 (MeasureTheory.volume.restrict K) := by
            simpa [Real.norm_of_nonneg (NNReal.coe_nonneg Ca)] using
              eLpNorm_const_smul (μ := MeasureTheory.volume.restrict K)
                (p := (2 : ℝ≥0∞)) (c := (Ca : ℝ)) (f := f)
  have hchart :
      eLpNorm f 2 (MeasureTheory.volume.restrict K) ≤
        (Cchart : ℝ≥0∞) * eLpNorm wdiff.toFunction 2 μ := by
    simpa [f] using hCchart wdiff
  have hwdiff_eLp :
      eLpNorm wdiff.toFunction 2 μ =
        ENNReal.ofReal
          (squareIntegrableHilbertBundleSectionL2Norm
            (trivialHilbertBundleGeometry X E) μ wdiff) := by
    rw [← eLpNorm_norm wdiff.toFunction]
    simpa [SquareIntegrableValueSection.toFunction] using
      squareIntegrableHilbertBundleSection_eLpNorm_norm_eq_ofReal_l2Norm
        (I := I) (G := trivialHilbertBundleGeometry X E)
        (fun _ _ _ ↦ rfl) μ wdiff
  have hdist_eq :
      eLpNorm wdiff.toFunction 2 μ = edist u₁ u₂ := by
    rw [hwdiff_eLp]
    exact (valueL2Section_edist_mk_eq_ofReal_l2Norm_sub
      (I := I) (X := X) (E := E) μ w₁ w₂).symm
  have hmain :
      edist (∫ z, F₁ z ∂μΩ) (∫ z, F₂ z ∂μΩ) ≤
        B * edist u₁ u₂ := by
    calc
      edist (∫ z, F₁ z ∂μΩ) (∫ z, F₂ z ∂μΩ)
          = ‖(∫ z, F₁ z ∂μΩ) - (∫ z, F₂ z ∂μΩ)‖ₑ := by
              rw [edist_eq_enorm_sub]
      _ = ‖∫ z, Fdiff z ∂μΩ‖ₑ := by rw [hintegral_sub]
      _ ≤ ∫⁻ z, ‖Fdiff z‖ₑ ∂μΩ :=
          enorm_integral_le_lintegral_enorm Fdiff
      _ = eLpNorm Fdiff 1 μΩ := by
          rw [eLpNorm_one_eq_lintegral_enorm]
      _ = eLpNorm Fdiff 1 (MeasureTheory.volume.restrict K) := hrestrict_eq
      _ ≤ eLpNorm Fdiff 2 (MeasureTheory.volume.restrict K) * Mpow := hL1L2
      _ ≤ ((Ca : ℝ≥0∞) * eLpNorm f 2 (MeasureTheory.volume.restrict K)) * Mpow :=
          mul_le_mul_left hmul2 Mpow
      _ ≤ ((Ca : ℝ≥0∞) * ((Cchart : ℝ≥0∞) * eLpNorm wdiff.toFunction 2 μ)) * Mpow :=
          mul_le_mul_left
            (mul_le_mul_right hchart (Ca : ℝ≥0∞)) Mpow
      _ = B * eLpNorm wdiff.toFunction 2 μ := by
          dsimp [B, Mpow]
          ac_rfl
      _ = B * edist u₁ u₂ := by rw [hdist_eq]
  change edist (∫ z, F₁ z ∂μΩ) (∫ z, F₂ z ∂μΩ) ≤
    (B.toNNReal : ℝ≥0∞) * edist u₁ u₂
  calc
    edist (∫ z, F₁ z ∂μΩ) (∫ z, F₂ z ∂μΩ) ≤
        B * edist u₁ u₂ := hmain
    _ = (B.toNNReal : ℝ≥0∞) * edist u₁ u₂ := by
        rw [ENNReal.coe_toNNReal hB_ne_top]

/--
%%handwave
name:
  Coordinate value test integrands are integrable
statement:
  Fix a coordinate chart, a compactly supported coordinate test function, and
  a tangent direction.  Multiplying an \(L^2\)-value-section representative by
  the directional derivative of the test function gives a Bochner integrable
  function on the coordinate region.
proof:
  The derivative of the test is bounded and supported in a compact subset of
  the coordinate region.  The smooth positive coordinate density is locally
  comparable with Lebesgue measure on this compact set, so the representative
  is locally \(L^2\) in coordinates.  Cauchy--Schwarz then gives
  \(L^1\)-integrability.
-/
theorem manifoldValueCoordinateTestPairing_integrable
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [IsManifold I 1 X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology (Bundle.TotalSpace E (Bundle.Trivial X E))]
    [TopologicalSpace.PseudoMetrizableSpace (Bundle.TotalSpace E (Bundle.Trivial X E))]
    (μ : Measure X) (_hμ : SmoothPositiveMeasureOnManifold (I := I) μ) :
    ∀ (e : OpenPartialHomeomorph X H) (_he : e ∈ atlas H X)
      (φ : SmoothCompactlySupportedManifoldCoordinateFunction
        (manifoldChartRegion e (Set.univ : Set X)))
      (v : H) (w : SquareIntegrableValueSection (X := X) (E := E) μ),
      Integrable
        (fun z ↦ (fderiv ℝ (φ : H → ℝ) z v) • w.toFunction (e.symm z))
        (MeasureTheory.volume.restrict
          (manifoldChartRegion e (Set.univ : Set X))) := by
  intro e he φ v w
  let a : H → ℝ := fun z ↦ fderiv ℝ (φ : H → ℝ) z v
  have ha_cont : Continuous a :=
    (φ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have ha_bound : ∃ C : NNReal, ∀ z : H, ‖a z‖ ≤ C := by
    simpa [a] using
      (SmoothCompactlySupportedManifoldCoordinateFunction.exists_derivative_bound
        φ v)
  have ha_support : tsupport a ⊆ manifoldChartRegion e (Set.univ : Set X) := by
    have hderiv_support :
        tsupport a ⊆ tsupport (φ : H → ℝ) := by
      simpa [a] using
        (tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := (φ : H → ℝ)) v)
    exact hderiv_support.trans φ.support_subset
  have ha_compact : IsCompact (tsupport a) := by
    have hderiv_support :
        tsupport a ⊆ tsupport (φ : H → ℝ) := by
      simpa [a] using
        (tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := (φ : H → ℝ)) v)
    exact φ.compact_support.of_isClosed_subset (isClosed_tsupport a) hderiv_support
  exact manifoldValueCompactlySupportedMultiplier_integrable
    (I := I) (X := X) (E := E) μ _hμ e he a
    ha_cont ha_bound ha_support ha_compact w

/--
%%handwave
name:
  Coordinate value test integrals satisfy a Lipschitz estimate
statement:
  Fix a coordinate chart, a compactly supported coordinate test function, and
  a tangent direction.  The coordinate value test integral is Lipschitz in the
  intrinsic \(L^2\)-distance of square-integrable representatives.
proof:
  Apply the integrability estimate to differences.  The bounded test
  derivative and local comparison between coordinate Lebesgue measure and the
  smooth positive measure reduce the bound to Cauchy--Schwarz on the compact
  support of the derivative.
-/
theorem manifoldValueCoordinateTestPairing_integral_lipschitz_estimate
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [IsManifold I 1 X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology (Bundle.TotalSpace E (Bundle.Trivial X E))]
    [TopologicalSpace.PseudoMetrizableSpace (Bundle.TotalSpace E (Bundle.Trivial X E))]
    (μ : Measure X) (_hμ : SmoothPositiveMeasureOnManifold (I := I) μ) :
    letI : NormedAddCommGroup (ValueL2Section (X := X) (E := E) μ) :=
      valueL2SectionNormedAddCommGroup (I := I) (X := X) (E := E) μ
    ∀ (e : OpenPartialHomeomorph X H) (_he : e ∈ atlas H X)
      (φ : SmoothCompactlySupportedManifoldCoordinateFunction
        (manifoldChartRegion e (Set.univ : Set X)))
      (v : H),
      ∃ K : NNReal,
        ∀ w₁ w₂ : SquareIntegrableValueSection (X := X) (E := E) μ,
          edist
            (∫ z in manifoldChartRegion e (Set.univ : Set X),
              (fderiv ℝ (φ : H → ℝ) z v) • w₁.toFunction (e.symm z)
              ∂MeasureTheory.volume)
            (∫ z in manifoldChartRegion e (Set.univ : Set X),
              (fderiv ℝ (φ : H → ℝ) z v) • w₂.toFunction (e.symm z)
              ∂MeasureTheory.volume) ≤
            K *
              edist
                (Quotient.mk
                  (SquareIntegrableValueSection.aeSetoid
                    (X := X) (E := E) (μ := μ)) w₁ :
                  ValueL2Section (X := X) (E := E) μ)
                (Quotient.mk
                  (SquareIntegrableValueSection.aeSetoid
                    (X := X) (E := E) (μ := μ)) w₂ :
                  ValueL2Section (X := X) (E := E) μ) := by
  letI : NormedAddCommGroup (ValueL2Section (X := X) (E := E) μ) :=
    valueL2SectionNormedAddCommGroup (I := I) (X := X) (E := E) μ
  intro e he φ v
  let a : H → ℝ := fun z ↦ fderiv ℝ (φ : H → ℝ) z v
  have ha_cont : Continuous a :=
    (φ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have ha_bound : ∃ C : NNReal, ∀ z : H, ‖a z‖ ≤ C := by
    simpa [a] using
      (SmoothCompactlySupportedManifoldCoordinateFunction.exists_derivative_bound
        φ v)
  have ha_support : tsupport a ⊆ manifoldChartRegion e (Set.univ : Set X) := by
    have hderiv_support :
        tsupport a ⊆ tsupport (φ : H → ℝ) := by
      simpa [a] using
        (tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := (φ : H → ℝ)) v)
    exact hderiv_support.trans φ.support_subset
  have ha_compact : IsCompact (tsupport a) := by
    have hderiv_support :
        tsupport a ⊆ tsupport (φ : H → ℝ) := by
      simpa [a] using
        (tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := (φ : H → ℝ)) v)
    exact φ.compact_support.of_isClosed_subset (isClosed_tsupport a) hderiv_support
  rcases manifoldValueCompactlySupportedMultiplier_integral_lipschitz_estimate
      (I := I) (X := X) (E := E) μ _hμ e he a
      ha_cont ha_bound ha_support ha_compact with
    ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro w₁ w₂
  simpa [a] using hK w₁ w₂

/--
%%handwave
name:
  Coordinate value test pairings have Lipschitz \(L^2\)-section representers
statement:
  Fix a coordinate chart, a compactly supported coordinate test function, and
  a tangent direction.  The coordinate integral obtained by pairing a
  value-section representative with the derivative of the test function
  descends to a Lipschitz map from the intrinsic \(L^2\)-section space to the
  target Hilbert space.
proof:
  The coordinate density is smooth and strictly positive, so on the compact
  support of the test derivative it is bounded above and below.  The coordinate
  integral is therefore bounded by Cauchy--Schwarz by a fixed constant times
  the intrinsic \(L^2\)-norm of the section.  The same estimate applied to
  differences gives the Lipschitz bound and proves independence of the
  representative.
-/
theorem manifoldValueCoordinateTestPairing_has_lipschitz_l2_representer
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [IsManifold I 1 X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology (Bundle.TotalSpace E (Bundle.Trivial X E))]
    [TopologicalSpace.PseudoMetrizableSpace (Bundle.TotalSpace E (Bundle.Trivial X E))]
    (μ : Measure X) (_hμ : SmoothPositiveMeasureOnManifold (I := I) μ) :
    letI : NormedAddCommGroup (ValueL2Section (X := X) (E := E) μ) :=
      valueL2SectionNormedAddCommGroup (I := I) (X := X) (E := E) μ
    ∀ (e : OpenPartialHomeomorph X H) (_he : e ∈ atlas H X)
      (φ : SmoothCompactlySupportedManifoldCoordinateFunction
        (manifoldChartRegion e (Set.univ : Set X)))
      (v : H),
      ∃ K : NNReal, ∃ T : ValueL2Section (X := X) (E := E) μ → E,
        LipschitzWith K T ∧
          ∀ w : SquareIntegrableValueSection (X := X) (E := E) μ,
            Integrable
              (fun z ↦ (fderiv ℝ (φ : H → ℝ) z v) • w.toFunction (e.symm z))
              (MeasureTheory.volume.restrict
                (manifoldChartRegion e (Set.univ : Set X))) ∧
            (∫ z in manifoldChartRegion e (Set.univ : Set X),
                (fderiv ℝ (φ : H → ℝ) z v) • w.toFunction (e.symm z)
                ∂MeasureTheory.volume) =
              T
                (Quotient.mk
                  (SquareIntegrableValueSection.aeSetoid
                    (X := X) (E := E) (μ := μ)) w) := by
  letI : NormedAddCommGroup (ValueL2Section (X := X) (E := E) μ) :=
    valueL2SectionNormedAddCommGroup (I := I) (X := X) (E := E) μ
  intro e he φ v
  rcases manifoldValueCoordinateTestPairing_integral_lipschitz_estimate
      (I := I) (X := X) (E := E) μ _hμ e he φ v with
    ⟨K, hK⟩
  let F : SquareIntegrableValueSection (X := X) (E := E) μ → E :=
    fun w ↦
      ∫ z in manifoldChartRegion e (Set.univ : Set X),
        (fderiv ℝ (φ : H → ℝ) z v) • w.toFunction (e.symm z)
        ∂MeasureTheory.volume
  have hF_congr :
      ∀ w₁ w₂ : SquareIntegrableValueSection (X := X) (E := E) μ,
        SquareIntegrableHilbertBundleSection.AeEq w₁ w₂ → F w₁ = F w₂ := by
    intro w₁ w₂ h12
    have hclasses :
        (Quotient.mk
          (SquareIntegrableValueSection.aeSetoid
            (X := X) (E := E) (μ := μ)) w₁ :
          ValueL2Section (X := X) (E := E) μ) =
          Quotient.mk
            (SquareIntegrableValueSection.aeSetoid
              (X := X) (E := E) (μ := μ)) w₂ :=
      Quotient.sound h12
    have hdist_zero : edist (F w₁) (F w₂) = 0 := by
      have hle : edist (F w₁) (F w₂) ≤
          K *
            edist
              (Quotient.mk
                (SquareIntegrableValueSection.aeSetoid
                  (X := X) (E := E) (μ := μ)) w₁ :
                ValueL2Section (X := X) (E := E) μ)
              (Quotient.mk
                (SquareIntegrableValueSection.aeSetoid
                  (X := X) (E := E) (μ := μ)) w₂ :
                ValueL2Section (X := X) (E := E) μ) := by
        simpa [F] using hK w₁ w₂
      rw [hclasses, edist_self, mul_zero] at hle
      exact le_antisymm hle zero_le
    exact eq_of_edist_eq_zero hdist_zero
  let T : ValueL2Section (X := X) (E := E) μ → E :=
    Quotient.lift F (by
      intro w₁ w₂ h
      exact hF_congr w₁ w₂ h)
  refine ⟨K, T, ?_, ?_⟩
  · intro q r
    refine Quotient.inductionOn₂ q r ?_
    intro w₁ w₂
    simpa [T, F] using hK w₁ w₂
  · intro w
    exact ⟨manifoldValueCoordinateTestPairing_integrable
      (I := I) (X := X) (E := E) μ _hμ e he φ v w, by simp [T, F]⟩

/--
%%handwave
name:
  Coordinate value test pairings are continuous for \(L^2\)-section limits
statement:
  Fix a coordinate chart, a compactly supported coordinate test function, and
  a tangent direction.  If value representatives converge in the intrinsic
  \(L^2\)-section quotient, then the coordinate integral obtained by pairing
  the representative with the derivative of the test function converges to the
  corresponding limiting coordinate integral.  The limiting coordinate
  integrand is integrable.
proof:
  The compactly supported derivative of the test function defines a bounded
  multiplier on the chart support.  The smooth positive density of the measure
  identifies the coordinate integral with a continuous \(L^2\)-pairing against
  a fixed square-integrable value section.  Continuity of this pairing gives
  the stated convergence and integrability.
-/
theorem manifoldValueCoordinateTestPairing_tendsto_of_tendsto_l2_sections
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [IsManifold I 1 X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology (Bundle.TotalSpace E (Bundle.Trivial X E))]
    [TopologicalSpace.PseudoMetrizableSpace (Bundle.TotalSpace E (Bundle.Trivial X E))]
    (μ : Measure X) (_hμ : SmoothPositiveMeasureOnManifold (I := I) μ) :
    letI : NormedAddCommGroup (ValueL2Section (X := X) (E := E) μ) :=
      valueL2SectionNormedAddCommGroup (I := I) (X := X) (E := E) μ
    ∀ {ι : Type} {l : Filter ι} [l.NeBot]
      {u : ι → SquareIntegrableValueSection (X := X) (E := E) μ}
      {uLim : SquareIntegrableValueSection (X := X) (E := E) μ}
      {uLimClass : ValueL2Section (X := X) (E := E) μ},
      (Quotient.mk
        (SquareIntegrableValueSection.aeSetoid
          (X := X) (E := E) (μ := μ)) uLim :
        ValueL2Section (X := X) (E := E) μ) = uLimClass →
      Filter.Tendsto
        (fun i ↦
          (Quotient.mk
            (SquareIntegrableValueSection.aeSetoid
              (X := X) (E := E) (μ := μ)) (u i) :
            ValueL2Section (X := X) (E := E) μ))
        l
        (𝓝 uLimClass) →
      ∀ (e : OpenPartialHomeomorph X H) (_he : e ∈ atlas H X)
        (φ : SmoothCompactlySupportedManifoldCoordinateFunction
          (manifoldChartRegion e (Set.univ : Set X)))
        (v : H),
        Integrable
            (fun z ↦ (fderiv ℝ (φ : H → ℝ) z v) • uLim.toFunction (e.symm z))
            (MeasureTheory.volume.restrict
              (manifoldChartRegion e (Set.univ : Set X))) ∧
          Filter.Tendsto
            (fun i ↦
              ∫ z in manifoldChartRegion e (Set.univ : Set X),
                (fderiv ℝ (φ : H → ℝ) z v) • (u i).toFunction (e.symm z)
                ∂MeasureTheory.volume)
            l
            (𝓝 (∫ z in manifoldChartRegion e (Set.univ : Set X),
                (fderiv ℝ (φ : H → ℝ) z v) • uLim.toFunction (e.symm z)
                ∂MeasureTheory.volume)) := by
  letI : NormedAddCommGroup (ValueL2Section (X := X) (E := E) μ) :=
    valueL2SectionNormedAddCommGroup (I := I) (X := X) (E := E) μ
  intro ι l hne u uLim uLimClass huLim_eq hu_tendsto e he φ v
  rcases manifoldValueCoordinateTestPairing_has_lipschitz_l2_representer
      (I := I) (X := X) (E := E) μ _hμ e he φ v with
    ⟨_K, T, hT_lipschitz, hT⟩
  rcases hT uLim with ⟨huLim_int, huLim_integral_eq⟩
  have hT_tendsto :
      Filter.Tendsto
        (fun i ↦
          T
            (Quotient.mk
              (SquareIntegrableValueSection.aeSetoid
                (X := X) (E := E) (μ := μ)) (u i) :
              ValueL2Section (X := X) (E := E) μ))
        l
        (𝓝 (T uLimClass)) :=
    hT_lipschitz.continuous.tendsto uLimClass |>.comp hu_tendsto
  have hseq_eq :
      (fun i ↦
          T
            (Quotient.mk
              (SquareIntegrableValueSection.aeSetoid
                (X := X) (E := E) (μ := μ)) (u i) :
              ValueL2Section (X := X) (E := E) μ)) =ᶠ[l]
        fun i ↦
          ∫ z in manifoldChartRegion e (Set.univ : Set X),
            (fderiv ℝ (φ : H → ℝ) z v) • (u i).toFunction (e.symm z)
            ∂MeasureTheory.volume :=
    Filter.Eventually.of_forall fun i ↦ (hT (u i)).2.symm
  have hlim_eq :
      T uLimClass =
        ∫ z in manifoldChartRegion e (Set.univ : Set X),
          (fderiv ℝ (φ : H → ℝ) z v) • uLim.toFunction (e.symm z)
          ∂MeasureTheory.volume := by
    rw [← huLim_eq]
    exact huLim_integral_eq.symm
  exact ⟨huLim_int, by
    have h_integrals_tendsto :=
      Filter.Tendsto.congr' hseq_eq hT_tendsto
    simpa [hlim_eq] using h_integrals_tendsto⟩

/--
%%handwave
name:
  Fiber evaluation is controlled by the Hilbert--Schmidt norm
statement:
  At a fixed point of the manifold, evaluating a vector-valued differential
  on a fixed tangent vector is bounded by a constant times the
  Hilbert--Schmidt fiber norm.
proof:
  The Hilbert--Schmidt metric gives the differential fiber the same topology
  as the usual continuous-linear-map fiber topology.  Evaluation at a fixed
  tangent vector is therefore a continuous linear map on this Hilbert fiber,
  and the operator-norm estimate gives the desired bound.
-/
theorem manifoldDifferentialFiberEvaluation_norm_le
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold I 1 X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : SmoothRiemannianMetricOnManifold I X) (x : X)
    (ξ : TangentSpace I x) :
    ∃ C : NNReal,
      ∀ A : ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E) x,
        ‖A ξ‖ ≤
          (C : ℝ) *
            Real.sqrt
              ((manifoldDifferentialHilbertBundleGeometry
                (I := I) (X := X) (E := E) g).fiberNormSq x A) := by
  classical
  let metric :=
    manifoldDifferentialHilbertSchmidtContinuousRiemannianMetric
      (I := I) (X := X) (E := E) g
  let G :=
    manifoldDifferentialHilbertBundleGeometry
      (I := I) (X := X) (E := E) g
  letI : NormedAddCommGroup (TangentSpace I x) := by
    change NormedAddCommGroup H
    infer_instance
  letI : NormedSpace ℝ (TangentSpace I x) := by
    change NormedSpace ℝ H
    infer_instance
  letI : T2Space (TangentSpace I x) := by
    change T2Space H
    infer_instance
  letI : NormedAddCommGroup (Bundle.Trivial X E x) :=
    inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (Bundle.Trivial X E x) :=
    inferInstanceAs (NormedSpace ℝ E)
  letI : T2Space (Bundle.Trivial X E x) :=
    inferInstanceAs (T2Space E)
  let evalCLM :
      (TangentSpace I x →L[ℝ] Bundle.Trivial X E x) →L[ℝ]
          Bundle.Trivial X E x :=
    ContinuousLinearMap.apply ℝ (Bundle.Trivial X E x) ξ
  let S : Set (TangentSpace I x →L[ℝ] Bundle.Trivial X E x) :=
    {A | metric.inner x A A < 1}
  have hS : Bornology.IsVonNBounded ℝ S := by
    simpa [S, metric] using
      manifoldDifferentialHilbertSchmidtInnerCLMAt_isVonNBounded
        (I := I) (X := X) (E := E) g x
  have hImg : Bornology.IsVonNBounded ℝ (evalCLM '' S) :=
    Bornology.IsVonNBounded.image hS evalCLM
  rcases (NormedSpace.isVonNBounded_iff'
      (𝕜 := ℝ) (E := Bundle.Trivial X E x)).1 hImg with
    ⟨R, hR⟩
  have hEval_bound :
      ∀ B ∈ S, ‖B ξ‖ ≤ R := by
    intro B hB
    have hmem : evalCLM B ∈ evalCLM '' S := ⟨B, hB, rfl⟩
    simpa [evalCLM] using hR (evalCLM B) hmem
  have hzero_mem : (0 : TangentSpace I x →L[ℝ] Bundle.Trivial X E x) ∈ S := by
    simp [S]
  have hR_nonneg : 0 ≤ R := by
    have h := hEval_bound 0 hzero_mem
    simpa using h
  refine ⟨⟨2 * R, by nlinarith⟩, ?_⟩
  intro A
  by_cases hA : A = 0
  · subst A
    simpa using
      mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hR_nonneg)
        (Real.sqrt_nonneg _)
  · have hnormsq_pos : 0 < G.fiberNormSq x A := by
      change 0 < metric.inner x A A
      exact metric.pos x A hA
    have hnormsq_nonneg : 0 ≤ G.fiberNormSq x A := hnormsq_pos.le
    let s : ℝ := Real.sqrt (G.fiberNormSq x A)
    have hs_pos : 0 < s := Real.sqrt_pos.2 hnormsq_pos
    have hs_ne : s ≠ 0 := ne_of_gt hs_pos
    let c : ℝ := (2 * s)⁻¹
    have hc_pos : 0 < c := by
      dsimp [c]
      positivity
    have hmetric_eq : metric.inner x A A = s ^ 2 := by
      change G.fiberNormSq x A = s ^ 2
      exact (Real.sq_sqrt hnormsq_nonneg).symm
    have hscale_mem : (c • A) ∈ S := by
      dsimp [S]
      calc
        metric.inner x (c • A) (c • A)
            = c * c * metric.inner x A A := by
              simp [mul_assoc]
        _ = c * c * s ^ 2 := by rw [hmetric_eq]
        _ = (1 / 2 : ℝ) ^ 2 := by
              dsimp [c]
              field_simp [hs_ne]
        _ < 1 := by norm_num
    have hscaled_bound := hEval_bound (c • A) hscale_mem
    have hscaled_norm : ‖(c • A) ξ‖ = c * ‖A ξ‖ := by
      rw [ContinuousLinearMap.smul_apply, norm_smul, Real.norm_eq_abs,
        abs_of_pos hc_pos]
    rw [hscaled_norm] at hscaled_bound
    have hmain : ‖A ξ‖ ≤ (2 * R) * s := by
      have hdiv : ‖A ξ‖ ≤ R / c := by
        rw [le_div_iff₀ hc_pos]
        rwa [mul_comm]
      have hdiv_eq : R / c = (2 * R) * s := by
        dsimp [c]
        field_simp [hs_ne]
      simpa [hdiv_eq] using hdiv
    change ‖A ξ‖ ≤ (2 * R) * Real.sqrt (G.fiberNormSq x A)
    simpa [s] using hmain

/--
%%handwave
name:
  Hom-bundle coordinates preserve differential evaluation
statement:
  If a differential fiber is written in a local Hom-bundle trivialization and
  a tangent vector is written in the corresponding tangent-bundle
  trivialization, evaluating in local coordinates agrees with evaluating the
  original differential on the original tangent vector.
proof:
  The Hom-bundle trivialization is induced by the tangent-bundle
  trivialization on the source and the trivial target-bundle trivialization on
  the target.  Therefore applying the transported Hom map to the transported
  tangent vector cancels the two inverse coordinate maps.
-/
theorem manifoldDifferentialBundle_trivialization_eval_eq
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold I 1 X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x₀ y : X)
    (hy : y ∈
      (trivializationAt (H →L[ℝ] E)
        (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E)) x₀).baseSet)
    (A : ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E) y)
    (ξ : TangentSpace I y) :
    (((trivializationAt (H →L[ℝ] E)
        (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E)) x₀
        ).continuousLinearMapAt ℝ y) A)
      (((trivializationAt H (TangentSpace I : X → Type) x₀
        ).continuousLinearMapAt ℝ y) ξ) =
      A ξ := by
  let eT := trivializationAt H (TangentSpace I : X → Type) x₀
  let eE := trivializationAt E (Bundle.Trivial X E) x₀
  let eD := trivializationAt (H →L[ℝ] E)
    (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E)) x₀
  have hyTE : y ∈ eT.baseSet ∩ eE.baseSet := by
    simpa [eT, eE, eD, ManifoldDifferentialBundleFiber,
      hom_trivializationAt_baseSet] using hy
  have hyT : y ∈ eT.baseSet := hyTE.1
  have hyD : y ∈ (eT.continuousLinearMap (RingHom.id ℝ) eE).baseSet := by
    simpa [Bundle.Trivialization.baseSet_continuousLinearMap] using hyTE
  change
    ((eT.continuousLinearMap (RingHom.id ℝ) eE).continuousLinearMapAt ℝ y A)
      (eT.continuousLinearMapAt ℝ y ξ) = A ξ
  rw [Bundle.Trivialization.continuousLinearMapAt_apply]
  rw [Bundle.Trivialization.coe_linearMapAt_of_mem _ hyD]
  change
    eE.continuousLinearMapAt ℝ y
      (A (eT.symmL ℝ y (eT.continuousLinearMapAt ℝ y ξ))) = A ξ
  rw [Bundle.Trivialization.symmL_continuousLinearMapAt eT hyT ξ]
  simp [eE]

/--
%%handwave
name:
  Continuity of a coordinate tangent vector in the bundle
statement:
  For a fixed model vector \(u\), the total-space vector \(z\mapsto(e^{-1}(z),D(e^{-1})(z)u)\) is continuous on the chart target.
proof:
  This is the defining continuity of the tangent-bundle chart trivialization applied to the constant coordinate vector (u).
-/
private theorem manifoldChartCoordinateVector_continuousOn_id {H X : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [TopologicalSpace X] [ChartedSpace H X]
    [FiniteDimensional ℝ H] [IsManifold (𝓘(ℝ, H)) 1 X]
    (e : OpenPartialHomeomorph X H) (_he : e ∈ atlas H X) (u : H) :
    ContinuousOn
      (fun z : H ↦ (Bundle.TotalSpace.mk' H (e.symm z)
        (manifoldChartTangentVector (I := 𝓘(ℝ, H)) e z u) :
          TangentBundle (𝓘(ℝ, H)) X)) e.target := by
  let I : ModelWithCorners ℝ H H := 𝓘(ℝ, H)
  have hsymm : ContMDiffOn I I 1 e.symm e.target :=
    contMDiffOn_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := I) (n := 1) _he)
  have hbaseVec : ContMDiffOn I I.tangent ∞
      (fun z : H ↦ (⟨z, u⟩ : TangentBundle I H)) e.target := by
    change ContMDiffOn I I.tangent ∞
        ((tangentBundleModelSpaceHomeomorph I).symm ∘
          fun z : H ↦ ((z, u) : ModelProd H H)) e.target
    refine (contMDiff_tangentBundleModelSpaceHomeomorph_symm
      (I := I)).contMDiffOn.comp (t := Set.univ) ?_ ?_
    · rw [← modelWithCornersSelf_prod]
      apply ContDiffOn.contMDiffOn
      fun_prop
    · intro z hz
      simp
  have htangent : ContinuousOn
      (tangentMapWithin I I e.symm e.target)
      (Bundle.TotalSpace.proj ⁻¹' e.target) := by
    exact hsymm.continuousOn_tangentMapWithin (n := 1) (by norm_num)
      e.open_target.uniqueMDiffOn
  have hcomp : ContinuousOn
      ((tangentMapWithin I I e.symm e.target) ∘
        (fun z : H ↦ (⟨z, u⟩ : TangentBundle I H))) e.target := by
    exact htangent.comp hbaseVec.continuousOn
      (fun z hz => by simpa using hz)
  refine hcomp.congr ?_
  intro z hz
  have hmd : MDifferentiableWithinAt I I e.symm e.target z :=
    mdifferentiableOn_atlas_symm (I := I) _he z hz
  simp [tangentMapWithin, manifoldChartTangentVector, mfderivWithin,
    writtenInExtChartAt, I, hmd]
  rfl

/--
%%handwave
name:
  Coordinate tangent vectors are locally bounded in tangent coordinates
statement:
  Near any coordinate point in a chart, a fixed coordinate tangent vector,
  transported to a fixed tangent-bundle trivialization, has bounded model
  norm.
proof:
  In the tangent trivialization centered at the base point, the transported
  coordinate tangent vector is the derivative of the coordinate transition
  from the given chart to the centered chart.  The transition is \(C^1\), so
  this derivative varies continuously and is locally bounded.
-/
theorem manifoldChartTangentVector_in_trivialization_locally_bounded
    {H X : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [IsManifold I 1 X] [IsIdentityManifoldModel H I] [FiniteDimensional ℝ H]
    (e : OpenPartialHomeomorph X H) (_he : e ∈ atlas H X) (v : H) :
    ∀ z₀ ∈ manifoldChartRegion e (Set.univ : Set X),
      ∃ U ∈ 𝓝 z₀, ∃ C : NNReal,
        ∀ z ∈ U,
          ‖((trivializationAt H (TangentSpace I : X → Type) (e.symm z₀)
              ).continuousLinearMapAt ℝ (e.symm z))
            (manifoldChartTangentVector (I := I) e z v)‖ ≤ (C : ℝ) := by
  classical
  have hI : I = 𝓘(ℝ, H) :=
    IsIdentityManifoldModel.eq_identity (H := H) (I := I)
  subst I
  intro z₀ hz₀
  rcases hz₀ with ⟨hz₀_target, _hz₀_univ⟩
  let x₀ : X := e.symm z₀
  let eT := trivializationAt H (TangentSpace (𝓘(ℝ, H)) : X → Type) x₀
  let F : H → TangentBundle (𝓘(ℝ, H)) X := fun z ↦
    (Bundle.TotalSpace.mk' H (e.symm z)
      (manifoldChartTangentVector (I := 𝓘(ℝ, H)) e z v) :
      TangentBundle (𝓘(ℝ, H)) X)
  let f : H → H := fun z ↦ (eT (F z)).2
  have hF_contOn : ContinuousOn F e.target := by
    simpa [F] using
      manifoldChartCoordinateVector_continuousOn_id (X := X) e _he v
  have hF_contAt : ContinuousAt F z₀ :=
    hF_contOn.continuousAt (e.open_target.mem_nhds hz₀_target)
  have hx₀T : x₀ ∈ eT.baseSet := by
    exact FiberBundle.mem_baseSet_trivializationAt' x₀
  have hFz₀_source : F z₀ ∈ eT.source := by
    rw [eT.mem_source]
    simpa [F, x₀] using hx₀T
  have heT_contAt : ContinuousAt eT (F z₀) :=
    eT.continuousOn.continuousAt (eT.open_source.mem_nhds hFz₀_source)
  have hf_contAt : ContinuousAt f z₀ := by
    exact continuous_snd.continuousAt.comp (heT_contAt.comp hF_contAt)
  have hbase_event :
      ∀ᶠ z in 𝓝 z₀, e.symm z ∈ eT.baseSet := by
    exact (e.symm.continuousAt hz₀_target).preimage_mem_nhds
      (eT.open_baseSet.mem_nhds hx₀T)
  have hnorm_event :
      ∀ᶠ z in 𝓝 z₀, ‖f z‖ < ‖f z₀‖ + 1 := by
    exact hf_contAt.norm.preimage_mem_nhds
      (Iio_mem_nhds (by linarith [norm_nonneg (f z₀)]))
  let U : Set H :=
    {z : H | e.symm z ∈ eT.baseSet} ∩
      {z : H | ‖f z‖ < ‖f z₀‖ + 1}
  have hU : U ∈ 𝓝 z₀ := Filter.inter_mem hbase_event hnorm_event
  refine ⟨U, hU, ⟨‖f z₀‖ + 1, by positivity⟩, ?_⟩
  intro z hz
  have hzbase : e.symm z ∈ eT.baseSet := hz.1
  have hzbound : ‖f z‖ < ‖f z₀‖ + 1 := hz.2
  have hlin :
      eT.continuousLinearMapAt ℝ (e.symm z)
        (manifoldChartTangentVector (I := 𝓘(ℝ, H)) e z v) = f z := by
    rw [Bundle.Trivialization.continuousLinearMapAt_apply]
    rw [Bundle.Trivialization.coe_linearMapAt_of_mem _ hzbase]
  rw [hlin]
  exact le_of_lt hzbound

/--
%%handwave
name:
  Coordinate evaluation is locally bounded
statement:
  Around each point in a coordinate chart, evaluation of a vector-valued
  differential on a fixed coordinate tangent direction is bounded by a local
  constant times the Hilbert--Schmidt fiber norm.
proof:
  In local bundle coordinates, the differential fiber norm is locally
  equivalent to the model Hilbert--Schmidt norm, and the coordinate tangent
  vector has locally bounded model coordinates.  Model evaluation is a
  continuous bilinear map, so these two local bounds give the estimate.
-/
theorem manifoldDifferentialCoordinateEvaluation_locally_pointwise_norm_le
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [IsManifold I 1 X] [IsIdentityManifoldModel H I]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := I) X E)]
    [TopologicalSpace.PseudoMetrizableSpace (ManifoldDifferentialTotalSpace (I := I) X E)]
    (g : SmoothRiemannianMetricOnManifold I X)
    (e : OpenPartialHomeomorph X H) (_he : e ∈ atlas H X) (v : H) :
    ∀ z₀ ∈ manifoldChartRegion e (Set.univ : Set X),
      ∃ U ∈ 𝓝 z₀, ∃ C : NNReal,
        ∀ z ∈ U,
          ∀ A : ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E) (e.symm z),
            ‖A (manifoldChartTangentVector (I := I) e z v)‖ ≤
              (C : ℝ) *
                Real.sqrt
                  ((manifoldDifferentialHilbertBundleGeometry
                    (I := I) (X := X) (E := E) g).fiberNormSq (e.symm z) A) := by
  classical
  intro z₀ hz₀
  rcases hz₀ with ⟨hz₀_target, _hz₀_univ⟩
  let x₀ : X := e.symm z₀
  let G :=
    manifoldDifferentialHilbertBundleGeometry
      (I := I) (X := X) (E := E) g
  let metric :=
    manifoldDifferentialHilbertSchmidtContinuousRiemannianMetric
      (I := I) (X := X) (E := E) g
  letI : Bundle.RiemannianBundle
      (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E)) :=
    ⟨metric.toRiemannianMetric⟩
  letI (x : X) :
      NormedAddCommGroup (ManifoldDifferentialBundleFiber
        (I := I) (X := X) (E := E) x) :=
    manifoldDifferentialHilbertSchmidtNormedAddCommGroup
      (I := I) (X := X) (E := E) metric x
  letI (x : X) :
      InnerProductSpace ℝ (ManifoldDifferentialBundleFiber
        (I := I) (X := X) (E := E) x) :=
    manifoldDifferentialHilbertSchmidtInnerProductSpace
      (I := I) (X := X) (E := E) metric x
  have hG_inner :
      ∀ (x : X)
        (A B : ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E) x),
        G.fiberInner x A B = inner ℝ A B := by
    intro x A B
    rfl
  have hsqrt_eq :
      ∀ (x : X)
        (A : ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E) x),
        Real.sqrt (G.fiberNormSq x A) = ‖A‖ := by
    intro x A
    have hnormsq : G.fiberNormSq x A = ‖A‖ ^ 2 := by
      rw [G.fiberNormSq_eq_inner, hG_inner]
      exact real_inner_self_eq_norm_sq A
    rw [hnormsq, Real.sqrt_sq (norm_nonneg _)]
  let eD :=
    trivializationAt (H →L[ℝ] E)
      (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E)) x₀
  let eT := trivializationAt H (TangentSpace I : X → Type) x₀
  rcases eventually_norm_trivializationAt_lt
      (F := H →L[ℝ] E)
      (E := ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E)) x₀ with
    ⟨CD, hCD_pos, hD_event⟩
  have hx₀D : x₀ ∈ eD.baseSet := by
    exact FiberBundle.mem_baseSet_trivializationAt' x₀
  have hD_event_z :
      ∀ᶠ z in 𝓝 z₀, ‖eD.continuousLinearMapAt ℝ (e.symm z)‖ < CD := by
    exact (e.symm.continuousAt hz₀_target).eventually hD_event
  have hD_base_z :
      ∀ᶠ z in 𝓝 z₀, e.symm z ∈ eD.baseSet := by
    exact (e.symm.continuousAt hz₀_target).eventually
      (eD.open_baseSet.mem_nhds hx₀D)
  rcases manifoldChartTangentVector_in_trivialization_locally_bounded
      (I := I) (X := X) e _he v z₀ ⟨hz₀_target, trivial⟩ with
    ⟨UT, hUT, CT, hCT⟩
  let U : Set H :=
    {z : H | ‖eD.continuousLinearMapAt ℝ (e.symm z)‖ < CD} ∩
      {z : H | e.symm z ∈ eD.baseSet} ∩ UT
  have hU : U ∈ 𝓝 z₀ := by
    exact Filter.inter_mem (Filter.inter_mem hD_event_z hD_base_z) hUT
  refine ⟨U, hU, ⟨CD * (CT : ℝ), mul_nonneg hCD_pos.le CT.2⟩, ?_⟩
  intro z hz A
  have hDlt : ‖eD.continuousLinearMapAt ℝ (e.symm z)‖ < CD := hz.1.1
  have hyD : e.symm z ∈ eD.baseSet := hz.1.2
  have hTbound :
      ‖(eT.continuousLinearMapAt ℝ (e.symm z))
          (manifoldChartTangentVector (I := I) e z v)‖ ≤ (CT : ℝ) := by
    simpa [eT, x₀] using hCT z hz.2
  let ξ : TangentSpace I (e.symm z) :=
    manifoldChartTangentVector (I := I) e z v
  let D :
      ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E) (e.symm z) →L[ℝ]
        (H →L[ℝ] E) :=
    eD.continuousLinearMapAt ℝ (e.symm z)
  let η : H := eT.continuousLinearMapAt ℝ (e.symm z) ξ
  have heval :
      (D A) η = A ξ := by
    simpa [D, η, ξ, eD, eT, x₀] using
      manifoldDifferentialBundle_trivialization_eval_eq
        (I := I) (X := X) (E := E) x₀ (e.symm z) hyD A ξ
  have hmain : ‖A ξ‖ ≤ (CD * (CT : ℝ)) * ‖A‖ := by
    calc
      ‖A ξ‖ = ‖(D A) η‖ := by rw [heval]
      _ ≤ ‖D A‖ * ‖η‖ := (D A).le_opNorm η
      _ ≤ (‖D‖ * ‖A‖) * ‖η‖ := by
        gcongr
        exact D.le_opNorm A
      _ ≤ (CD * ‖A‖) * ‖η‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hDlt.le (norm_nonneg A))
          (norm_nonneg η)
      _ ≤ (CD * ‖A‖) * (CT : ℝ) := by
        exact mul_le_mul_of_nonneg_left hTbound
          (mul_nonneg hCD_pos.le (norm_nonneg A))
      _ = (CD * (CT : ℝ)) * ‖A‖ := by ring
  change ‖A ξ‖ ≤ (CD * (CT : ℝ)) * Real.sqrt (G.fiberNormSq (e.symm z) A)
  simpa [hsqrt_eq] using hmain

/--
%%handwave
name:
  Compact coordinate evaluation is pointwise controlled
statement:
  On a compact coordinate support, evaluation of a vector-valued differential
  on a fixed coordinate tangent direction is bounded pointwise by a uniform
  constant times the Hilbert--Schmidt fiber norm.
proof:
  Fiberwise, evaluation on a tangent vector is bounded by the
  Hilbert--Schmidt norm times the length of that tangent vector.  In a fixed
  chart, the coordinate tangent vector and the Riemannian metric vary
  continuously, so this length is bounded on compact subsets of the chart.
-/
theorem manifoldDifferentialCompactEvaluation_pointwise_norm_le
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [IsManifold I 1 X] [IsIdentityManifoldModel H I]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := I) X E)]
    [TopologicalSpace.PseudoMetrizableSpace (ManifoldDifferentialTotalSpace (I := I) X E)]
    (g : SmoothRiemannianMetricOnManifold I X) :
    ∀ (e : OpenPartialHomeomorph X H) (_he : e ∈ atlas H X)
      (K : Set H) (v : H),
      K ⊆ manifoldChartRegion e (Set.univ : Set X) →
      IsCompact K →
      ∃ C : NNReal,
        ∀ z ∈ K,
          ∀ A : ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E) (e.symm z),
            ‖A (manifoldChartTangentVector (I := I) e z v)‖ ≤
              (C : ℝ) *
                Real.sqrt
                  ((manifoldDifferentialHilbertBundleGeometry
                    (I := I) (X := X) (E := E) g).fiberNormSq (e.symm z) A) := by
  classical
  intro e he K v hK_region hK_compact
  have hlocal :
      ∀ z ∈ K,
        ∃ U ∈ 𝓝 z, ∃ C : NNReal,
          ∀ z' ∈ U,
            ∀ A : ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E) (e.symm z'),
              ‖A (manifoldChartTangentVector (I := I) e z' v)‖ ≤
                (C : ℝ) *
                  Real.sqrt
                    ((manifoldDifferentialHilbertBundleGeometry
                      (I := I) (X := X) (E := E) g).fiberNormSq (e.symm z') A) := by
    intro z hz
    exact manifoldDifferentialCoordinateEvaluation_locally_pointwise_norm_le
      (I := I) (X := X) (E := E) g e he v z (hK_region hz)
  choose U hU C hC using hlocal
  rcases hK_compact.elim_nhds_subcover' U hU with ⟨t, hcover⟩
  let Cmax : NNReal := t.sup fun z : K ↦ C z z.2
  refine ⟨Cmax, ?_⟩
  intro z hz A
  rcases Set.mem_iUnion.mp (hcover hz) with ⟨z₀, hz₀⟩
  rcases Set.mem_iUnion.mp hz₀ with ⟨hz₀t, hzU⟩
  have hpoint := hC z₀ z₀.2 z hzU A
  have hC_le : C z₀ z₀.2 ≤ Cmax := by
    exact Finset.le_sup (s := t) (f := fun z : K ↦ C z z.2) hz₀t
  have hC_le_real : ((C z₀ z₀.2 : NNReal) : ℝ) ≤ (Cmax : ℝ) := by
    exact_mod_cast hC_le
  exact hpoint.trans
    (mul_le_mul_of_nonneg_right hC_le_real (Real.sqrt_nonneg _))

/--
%%handwave
name:
  Compact coordinate evaluation is measurable
statement:
  The coordinate evaluation of a square-integrable differential section on a
  fixed chart direction is strongly measurable on every compact coordinate
  support.
proof:
  In local bundle coordinates, the section is measurable, the coordinate
  tangent vector is a measurable tangent-bundle section, and evaluation in the
  Hom bundle is continuous.
-/
theorem manifoldDifferentialCompactEvaluation_aestronglyMeasurable
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [IsManifold I 1 X] [IsIdentityManifoldModel H I]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := I) X E)]
    [TopologicalSpace.PseudoMetrizableSpace (ManifoldDifferentialTotalSpace (I := I) X E)]
    (g : SmoothRiemannianMetricOnManifold I X) (μ : Measure X)
    (_hμ : SmoothPositiveMeasureOnManifold (I := I) μ) :
    ∀ (e : OpenPartialHomeomorph X H) (_he : e ∈ atlas H X)
      (K : Set H) (v : H),
      K ⊆ manifoldChartRegion e (Set.univ : Set X) →
      IsCompact K →
      ∀ w : SquareIntegrableManifoldDifferentialField
        (I := I) (X := X) (E := E) g μ,
        AEStronglyMeasurable
          (fun z ↦ ManifoldDifferentialField.evalChart w.toField e z v)
          (MeasureTheory.volume.restrict K) := by
  classical
  have hI : I = 𝓘(ℝ, H) := IsIdentityManifoldModel.eq_identity (H := H) (I := I)
  subst I
  intro e he K v hK_region hK_compact w
  let totalPull : H → ManifoldDifferentialTotalSpace (I := 𝓘(ℝ, H)) X E :=
    fun z ↦ HilbertBundleSectionOnSurface.toTotalSpace
      (F := H →L[ℝ] E) w.toSection (e.symm z)
  have hK_target : K ⊆ e.target := fun z hz ↦ (hK_region hz).1
  have htotal_K :
      AEStronglyMeasurable totalPull (MeasureTheory.volume.restrict K) := by
    have htotal_μ :
        AEStronglyMeasurable
          (HilbertBundleSectionOnSurface.toTotalSpace
            (F := H →L[ℝ] E) w.toSection) μ :=
      w.memL2.aemeasurable.aestronglyMeasurable
    simpa [totalPull] using
      smoothPositiveMeasureOnManifold_chartPullback_aestronglyMeasurable
        (I := 𝓘(ℝ, H)) μ _hμ e he K hK_target htotal_μ
  have hlocal :
      ∀ z₀ : K,
        ∃ U ∈ 𝓝 ((z₀ : K) : H), MeasurableSet U ∧
          AEStronglyMeasurable
            (fun z ↦ ManifoldDifferentialField.evalChart w.toField e z v)
            (MeasureTheory.volume.restrict (K ∩ U)) := by
    intro z₀
    let x₀ : X := e.symm ((z₀ : K) : H)
    let eD := trivializationAt (H →L[ℝ] E)
      (ManifoldDifferentialBundleFiber (I := 𝓘(ℝ, H)) (X := X) (E := E)) x₀
    let eT := trivializationAt H (TangentSpace (𝓘(ℝ, H)) : X → Type) x₀
    let U : Set H := e.target ∩ e.symm ⁻¹' (eD.baseSet ∩ eT.baseSet)
    have hz₀_target : ((z₀ : K) : H) ∈ e.target := hK_target z₀.2
    have hx₀D : x₀ ∈ eD.baseSet := by
      exact FiberBundle.mem_baseSet_trivializationAt' x₀
    have hx₀T : x₀ ∈ eT.baseSet := by
      exact FiberBundle.mem_baseSet_trivializationAt' x₀
    have hz₀U : ((z₀ : K) : H) ∈ U := by
      exact ⟨hz₀_target, by simpa [x₀] using And.intro hx₀D hx₀T⟩
    have hU_open : IsOpen U := by
      simpa [U] using
        e.isOpen_inter_preimage_symm (eD.open_baseSet.inter eT.open_baseSet)
    have hU_meas : MeasurableSet U := hU_open.measurableSet
    let S : Set H := K ∩ U
    have hS_meas : MeasurableSet S := hK_compact.measurableSet.inter hU_meas
    have htotal_S : AEStronglyMeasurable totalPull (MeasureTheory.volume.restrict S) :=
      htotal_K.mono_set (by intro z hz; exact hz.1)
    have hdefault_source : totalPull ((z₀ : K) : H) ∈ eD.source := by
      rw [eD.mem_source]
      simpa [totalPull, x₀] using hx₀D
    let defaultD : eD.source := ⟨totalPull ((z₀ : K) : H), hdefault_source⟩
    let totalDSubtype : H → eD.source := fun z ↦
      if hz : z ∈ S then
        ⟨totalPull z, by
          rw [eD.mem_source]
          simpa [totalPull] using hz.2.2.1⟩
      else defaultD
    have hval_eq :
        (fun z : H ↦
          ((totalDSubtype z : eD.source) :
            ManifoldDifferentialTotalSpace (I := 𝓘(ℝ, H)) X E)) =ᵐ[
              MeasureTheory.volume.restrict S] totalPull := by
      filter_upwards [ae_restrict_mem hS_meas] with z hzS
      simp [totalDSubtype, hzS]
    have hval_aestr :
        AEStronglyMeasurable
          (fun z : H ↦
            ((totalDSubtype z : eD.source) :
              ManifoldDifferentialTotalSpace (I := 𝓘(ℝ, H)) X E))
          (MeasureTheory.volume.restrict S) :=
      htotal_S.congr hval_eq.symm
    have hsub_aestr :
        AEStronglyMeasurable totalDSubtype (MeasureTheory.volume.restrict S) := by
      have hsubtype :
          Topology.IsEmbedding
            (fun p : eD.source ↦
              ((p : eD.source) :
                ManifoldDifferentialTotalSpace (I := 𝓘(ℝ, H)) X E)) :=
        Topology.IsEmbedding.subtypeVal
      exact hsubtype.aestronglyMeasurable_comp_iff.1 hval_aestr
    let coordD : eD.source → H →L[ℝ] E := fun p ↦
      (eD ((p : eD.source) :
        ManifoldDifferentialTotalSpace (I := 𝓘(ℝ, H)) X E)).2
    have hcoordD_cont : Continuous coordD := by
      have heD_restrict :
          Continuous
            (eD.source.restrict
              (fun p : ManifoldDifferentialTotalSpace (I := 𝓘(ℝ, H)) X E ↦
                eD p)) :=
        eD.continuousOn.restrict
      exact continuous_snd.comp heD_restrict
    let dcoord : H → H →L[ℝ] E := fun z ↦
      eD.continuousLinearMapAt ℝ (e.symm z) (w.toSection (e.symm z))
    have hD_raw :
        AEStronglyMeasurable
          (fun z : H ↦ coordD (totalDSubtype z))
          (MeasureTheory.volume.restrict S) :=
      hcoordD_cont.comp_aestronglyMeasurable hsub_aestr
    have hDcoord :
        AEStronglyMeasurable dcoord (MeasureTheory.volume.restrict S) := by
      refine hD_raw.congr ?_
      filter_upwards [ae_restrict_mem hS_meas] with z hzS
      have hzD : e.symm z ∈ eD.baseSet := hzS.2.2.1
      simp only [coordD, totalDSubtype, dcoord, totalPull, dif_pos hzS]
      change
        (eD (Bundle.TotalSpace.mk' (H →L[ℝ] E) (e.symm z)
          (w.toSection (e.symm z)))).2 =
          eD.continuousLinearMapAt ℝ (e.symm z) (w.toSection (e.symm z))
      rw [Bundle.Trivialization.continuousLinearMapAt_apply]
      rw [Bundle.Trivialization.coe_linearMapAt_of_mem _ hzD]
    let ξ : (z : H) → TangentSpace (𝓘(ℝ, H)) (e.symm z) := fun z ↦
      manifoldChartTangentVector (I := 𝓘(ℝ, H)) e z v
    let F : H → TangentBundle (𝓘(ℝ, H)) X := fun z ↦
      (Bundle.TotalSpace.mk' H (e.symm z) (ξ z) :
        TangentBundle (𝓘(ℝ, H)) X)
    let tcoord : H → H := fun z ↦
      eT.continuousLinearMapAt ℝ (e.symm z) (ξ z)
    have hF_contOn : ContinuousOn F e.target := by
      simpa [F, ξ] using
        manifoldChartCoordinateVector_continuousOn_id (X := X) e he v
    have heT_coord_contOn :
        ContinuousOn
          (fun q : TangentBundle (𝓘(ℝ, H)) X ↦ (eT q).2)
          eT.source := by
      exact continuous_snd.continuousOn.comp eT.continuousOn
        (fun q hq ↦ Set.mem_univ _)
    have hF_maps : Set.MapsTo F U eT.source := by
      intro z hz
      rw [eT.mem_source]
      simpa [F, ξ] using hz.2.2
    have hT_raw_contOn :
        ContinuousOn (fun z : H ↦ (eT (F z)).2) U :=
      heT_coord_contOn.comp (hF_contOn.mono (by intro z hz; exact hz.1)) hF_maps
    have hT_contOn : ContinuousOn tcoord U := by
      refine hT_raw_contOn.congr ?_
      intro z hz
      have hzT : e.symm z ∈ eT.baseSet := hz.2.2
      change
        eT.continuousLinearMapAt ℝ (e.symm z) (ξ z) =
          (eT (Bundle.TotalSpace.mk' H (e.symm z) (ξ z))).2
      rw [Bundle.Trivialization.continuousLinearMapAt_apply]
      rw [Bundle.Trivialization.coe_linearMapAt_of_mem _ hzT]
    have hTcoord :
        AEStronglyMeasurable tcoord (MeasureTheory.volume.restrict S) := by
      exact (hT_contOn.mono (by intro z hz; exact hz.2)).aestronglyMeasurable hS_meas
    let L : (H →L[ℝ] E) →L[ℝ] H →L[ℝ] E :=
      ContinuousLinearMap.flip
        (ContinuousLinearMap.apply ℝ E :
          H →L[ℝ] (H →L[ℝ] E) →L[ℝ] E)
    have happly :
        AEStronglyMeasurable
          (fun z : H ↦ dcoord z (tcoord z))
          (MeasureTheory.volume.restrict S) := by
      simpa [L] using
        (ContinuousLinearMap.aestronglyMeasurable_comp₂ L hDcoord hTcoord)
    have heval_eq :
        (fun z : H ↦ dcoord z (tcoord z)) =ᵐ[
          MeasureTheory.volume.restrict S]
          fun z ↦ ManifoldDifferentialField.evalChart w.toField e z v := by
      filter_upwards [ae_restrict_mem hS_meas] with z hzS
      have hzD : e.symm z ∈ eD.baseSet := hzS.2.2.1
      simpa [dcoord, tcoord, ξ, ManifoldDifferentialField.evalChart,
        SquareIntegrableManifoldDifferentialField.toField] using
        manifoldDifferentialBundle_trivialization_eval_eq
          (I := 𝓘(ℝ, H)) (X := X) (E := E) x₀ (e.symm z) hzD
          (w.toSection (e.symm z))
          (manifoldChartTangentVector (I := 𝓘(ℝ, H)) e z v)
    refine ⟨U, hU_open.mem_nhds hz₀U, hU_meas, ?_⟩
    exact happly.congr heval_eq
  choose U hU_nhds _hU_meas hU_eval using hlocal
  rcases hK_compact.elim_nhds_subcover'
      (fun z hz ↦ U ⟨z, hz⟩)
      (fun z hz ↦ hU_nhds ⟨z, hz⟩) with
    ⟨t, hcover⟩
  let coverSet : Set H :=
    ⋃ z₀ : {z : K // z ∈ t}, K ∩ U z₀.1
  have hK_eq : K = coverSet := by
    ext z
    constructor
    · intro hzK
      rcases Set.mem_iUnion.mp (hcover hzK) with ⟨z₀, hz₀⟩
      rcases Set.mem_iUnion.mp hz₀ with ⟨hz₀t, hzU⟩
      exact Set.mem_iUnion.mpr ⟨⟨z₀, hz₀t⟩, ⟨hzK, hzU⟩⟩
    · intro hz
      rcases Set.mem_iUnion.mp hz with ⟨z₀, hzS⟩
      exact hzS.1
  rw [hK_eq]
  rw [aestronglyMeasurable_iUnion_iff]
  intro z₀
  exact hU_eval z₀.1

/--
%%handwave
name:
  Compact coordinate evaluation is controlled by the Hilbert--Schmidt norm
statement:
  On a compact coordinate support, evaluating a differential section on a
  fixed chart tangent direction is a bounded map from intrinsic
  \(L^2\)-differential sections to coordinate \(L^2\)-functions.
proof:
  The chart density of the smooth positive measure is bounded below on the
  compact support.  The chart tangent vector has bounded length there, and
  evaluation on a tangent vector is bounded by the Hilbert--Schmidt norm
  times this length.  The coordinate \(L^2\) bound follows from the density
  comparison.
-/
theorem manifoldDifferentialCompactEvaluation_eLpNorm_two_on_support_le
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [IsManifold I 1 X] [IsIdentityManifoldModel H I]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := I) X E)]
    [TopologicalSpace.PseudoMetrizableSpace (ManifoldDifferentialTotalSpace (I := I) X E)]
    (g : SmoothRiemannianMetricOnManifold I X) (μ : Measure X)
    (_hμ : SmoothPositiveMeasureOnManifold (I := I) μ) :
    ∀ (e : OpenPartialHomeomorph X H) (_he : e ∈ atlas H X)
      (K : Set H) (v : H),
      K ⊆ manifoldChartRegion e (Set.univ : Set X) →
      IsCompact K →
      ∃ C : NNReal,
        ∀ w : SquareIntegrableManifoldDifferentialField
          (I := I) (X := X) (E := E) g μ,
          MemLp
            (fun z ↦ ManifoldDifferentialField.evalChart w.toField e z v)
            2
            (MeasureTheory.volume.restrict K) ∧
          eLpNorm
            (fun z ↦ ManifoldDifferentialField.evalChart w.toField e z v)
            2
            (MeasureTheory.volume.restrict K) ≤
            (C : ℝ≥0∞) *
              ENNReal.ofReal
                (squareIntegrableHilbertBundleSectionL2Norm
                  (manifoldDifferentialHilbertBundleGeometry
                    (I := I) (X := X) (E := E) g) μ w) := by
  classical
  intro e he K v hK_region hK_compact
  rcases manifoldDifferentialCompactEvaluation_pointwise_norm_le
      (I := I) (X := X) (E := E) g e he K v hK_region hK_compact with
    ⟨Ceval, hCeval⟩
  rcases smoothPositiveMeasureOnManifold_chartPullback_eLpNorm_two_restrict_compact_le
      (I := I) (X := X) (F := ℝ) μ _hμ e he K hK_region hK_compact with
    ⟨Cchart, hCchart⟩
  refine ⟨Ceval * Cchart, ?_⟩
  intro w
  let G :=
    manifoldDifferentialHilbertBundleGeometry
      (I := I) (X := X) (E := E) g
  let metric :=
    manifoldDifferentialHilbertSchmidtContinuousRiemannianMetric
      (I := I) (X := X) (E := E) g
  letI : Bundle.RiemannianBundle
      (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E)) :=
    ⟨metric.toRiemannianMetric⟩
  letI (x : X) :
      NormedAddCommGroup (ManifoldDifferentialBundleFiber
        (I := I) (X := X) (E := E) x) :=
    manifoldDifferentialHilbertSchmidtNormedAddCommGroup
      (I := I) (X := X) (E := E) metric x
  letI (x : X) :
      InnerProductSpace ℝ (ManifoldDifferentialBundleFiber
        (I := I) (X := X) (E := E) x) :=
    manifoldDifferentialHilbertSchmidtInnerProductSpace
      (I := I) (X := X) (E := E) metric x
  let fNorm : X → ℝ := fun x ↦ ‖w.toSection x‖
  let fPull : H → ℝ := fun z ↦ fNorm (e.symm z)
  let fEval : H → E := fun z ↦
    ManifoldDifferentialField.evalChart w.toField e z v
  have hG_inner :
      ∀ (x : X)
        (A B : ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E) x),
        G.fiberInner x A B = inner ℝ A B := by
    intro x A B
    rfl
  have hG_norm :
      ∀ (x : X)
        (A : ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E) x),
        G.fiberNormSq x A = ‖A‖ ^ 2 := by
    intro x A
    rw [G.fiberNormSq_eq_inner, hG_inner]
    exact real_inner_self_eq_norm_sq A
  have hsqrt_eq :
      ∀ (x : X)
        (A : ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E) x),
        Real.sqrt (G.fiberNormSq x A) = ‖A‖ := by
    intro x A
    rw [hG_norm x A, Real.sqrt_sq (norm_nonneg _)]
  have hf_memLp : MemLp fNorm 2 μ := by
    simpa [fNorm, G] using
      squareIntegrableHilbertBundleSection_norm_memLp
        (I := I) (G := G) hG_inner μ w
  have hfPull_memLp : MemLp fPull 2 (MeasureTheory.volume.restrict K) := by
    simpa [fPull, fNorm] using
      smoothPositiveMeasureOnManifold_chartPullback_memLp_two_restrict_compact
        (I := I) (X := X) (F := ℝ) μ _hμ e he K hK_region hK_compact hf_memLp
  have hfPull_bound :
      eLpNorm fPull 2 (MeasureTheory.volume.restrict K) ≤
        (Cchart : ℝ≥0∞) *
          eLpNorm fNorm 2 μ := by
    simpa [fPull] using hCchart fNorm hf_memLp.aestronglyMeasurable
  have hfNorm_l2 :
      eLpNorm fNorm 2 μ =
        ENNReal.ofReal
          (squareIntegrableHilbertBundleSectionL2Norm G μ w) := by
    simpa [fNorm, G] using
      squareIntegrableHilbertBundleSection_eLpNorm_norm_eq_ofReal_l2Norm
        (I := I) (G := G) hG_inner μ w
  have hfEval_aestr : AEStronglyMeasurable fEval (MeasureTheory.volume.restrict K) := by
    simpa [fEval] using
      manifoldDifferentialCompactEvaluation_aestronglyMeasurable
        (I := I) (X := X) (E := E) g μ _hμ e he K v hK_region hK_compact w
  have hpoint :
      ∀ᵐ z ∂MeasureTheory.volume.restrict K,
        ‖fEval z‖ ≤ (Ceval : ℝ) * ‖fPull z‖ := by
    filter_upwards [ae_restrict_mem hK_compact.measurableSet] with z hzK
    have h :=
      hCeval z hzK
        (w.toSection (e.symm z) :
          ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E) (e.symm z))
    calc
      ‖fEval z‖ ≤
          (Ceval : ℝ) *
            Real.sqrt
              (G.fiberNormSq (e.symm z)
                (w.toSection (e.symm z) :
                  ManifoldDifferentialBundleFiber
                    (I := I) (X := X) (E := E) (e.symm z))) := by
            simpa [fEval, G, ManifoldDifferentialField.evalChart,
              SquareIntegrableManifoldDifferentialField.toField] using h
      _ = (Ceval : ℝ) * ‖fPull z‖ := by
            rw [hsqrt_eq]
            simp [fPull, fNorm]
  have hfEval_memLp : MemLp fEval 2 (MeasureTheory.volume.restrict K) :=
    MemLp.of_le_mul hfPull_memLp hfEval_aestr hpoint
  have hEval_bound :
      eLpNorm fEval 2 (MeasureTheory.volume.restrict K) ≤
        ENNReal.ofReal (Ceval : ℝ) *
          eLpNorm fPull 2 (MeasureTheory.volume.restrict K) :=
    eLpNorm_le_mul_eLpNorm_of_ae_le_mul hpoint 2
  refine ⟨by simpa [fEval] using hfEval_memLp, ?_⟩
  calc
    eLpNorm
        (fun z ↦ ManifoldDifferentialField.evalChart w.toField e z v)
        2
        (MeasureTheory.volume.restrict K)
        = eLpNorm fEval 2 (MeasureTheory.volume.restrict K) := rfl
    _ ≤ ENNReal.ofReal (Ceval : ℝ) *
          eLpNorm fPull 2 (MeasureTheory.volume.restrict K) := hEval_bound
    _ ≤ ENNReal.ofReal (Ceval : ℝ) *
          ((Cchart : ℝ≥0∞) * eLpNorm fNorm 2 μ) :=
        mul_le_mul_right hfPull_bound (ENNReal.ofReal (Ceval : ℝ))
    _ = ENNReal.ofReal (Ceval : ℝ) *
          ((Cchart : ℝ≥0∞) *
            ENNReal.ofReal
              (squareIntegrableHilbertBundleSectionL2Norm G μ w)) := by
        rw [hfNorm_l2]
    _ = ((Ceval * Cchart : NNReal) : ℝ≥0∞) *
          ENNReal.ofReal
            (squareIntegrableHilbertBundleSectionL2Norm G μ w) := by
        simp [mul_assoc]

/--
%%handwave
name:
  Compactly supported differential multipliers have a local \(L^2\) bound
statement:
  On a compact subset of a coordinate chart, evaluating a square-integrable
  differential representative on a fixed coordinate tangent direction and
  multiplying by a bounded scalar test gives an \(L^2\)-function.  Its
  coordinate \(L^2\)-norm is bounded by a constant, depending only on the chart,
  compact support, tangent direction, multiplier, metric, and measure, times
  the intrinsic Hilbert--Schmidt \(L^2\)-norm of the representative.
proof:
  This is the local coordinate form of the compact Hilbert--Schmidt evaluation
  estimate.
-/
theorem manifoldDifferentialCompactlySupportedMultiplier_eLpNorm_two_on_support_le
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [IsManifold I 1 X] [IsIdentityManifoldModel H I]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := I) X E)]
    [TopologicalSpace.PseudoMetrizableSpace (ManifoldDifferentialTotalSpace (I := I) X E)]
    (g : SmoothRiemannianMetricOnManifold I X) (μ : Measure X)
    (_hμ : SmoothPositiveMeasureOnManifold (I := I) μ) :
    ∀ (e : OpenPartialHomeomorph X H) (_he : e ∈ atlas H X)
      (a : H → ℝ) (v : H),
      Continuous a →
      (∃ C : NNReal, ∀ z : H, ‖a z‖ ≤ C) →
      tsupport a ⊆ manifoldChartRegion e (Set.univ : Set X) →
      IsCompact (tsupport a) →
      ∃ C : NNReal,
        ∀ w : SquareIntegrableManifoldDifferentialField
          (I := I) (X := X) (E := E) g μ,
          MemLp
            (fun z ↦ a z • ManifoldDifferentialField.evalChart w.toField e z v)
            2
            (MeasureTheory.volume.restrict (tsupport a)) ∧
          eLpNorm
            (fun z ↦ a z • ManifoldDifferentialField.evalChart w.toField e z v)
            2
            (MeasureTheory.volume.restrict (tsupport a)) ≤
            (C : ℝ≥0∞) *
              ENNReal.ofReal
                (squareIntegrableHilbertBundleSectionL2Norm
                  (manifoldDifferentialHilbertBundleGeometry
                    (I := I) (X := X) (E := E) g) μ w) := by
  intro e he a v ha_cont ha_bound ha_support ha_compact
  rcases ha_bound with ⟨Ca, hCa⟩
  rcases manifoldDifferentialCompactEvaluation_eLpNorm_two_on_support_le
      (I := I) (X := X) (E := E) g μ _hμ e he (tsupport a) v
      ha_support ha_compact with
    ⟨Ceval, hCeval⟩
  refine ⟨Ca * Ceval, ?_⟩
  intro w
  let ν : Measure H := MeasureTheory.volume.restrict (tsupport a)
  let f : H → E := fun z ↦
    a z • ManifoldDifferentialField.evalChart w.toField e z v
  let gEval : H → E := fun z ↦
    ManifoldDifferentialField.evalChart w.toField e z v
  rcases hCeval w with ⟨hg_memLp, hg_bound⟩
  have ha_aestr : AEStronglyMeasurable a ν :=
    ha_cont.aestronglyMeasurable
  have hf_aestr : AEStronglyMeasurable f ν := by
    exact ha_aestr.smul hg_memLp.aestronglyMeasurable
  have hpoint : ∀ᵐ z ∂ν, ‖f z‖ ≤ (Ca : ℝ) * ‖gEval z‖ := by
    filter_upwards [] with z
    calc
      ‖f z‖ = ‖a z‖ * ‖gEval z‖ := by
        simp [f, gEval, norm_smul]
      _ ≤ (Ca : ℝ) * ‖gEval z‖ :=
        mul_le_mul_of_nonneg_right (hCa z) (norm_nonneg _)
  have hf_memLp : MemLp f 2 ν :=
    MemLp.of_le_mul hg_memLp hf_aestr hpoint
  have hnorm_bound :
      eLpNorm f 2 ν ≤ ENNReal.ofReal (Ca : ℝ) * eLpNorm gEval 2 ν :=
    eLpNorm_le_mul_eLpNorm_of_ae_le_mul hpoint 2
  refine ⟨by simpa [f, ν] using hf_memLp, ?_⟩
  calc
    eLpNorm
        (fun z ↦ a z • ManifoldDifferentialField.evalChart w.toField e z v)
        2
        (MeasureTheory.volume.restrict (tsupport a))
        = eLpNorm f 2 ν := rfl
    _ ≤ ENNReal.ofReal (Ca : ℝ) * eLpNorm gEval 2 ν := hnorm_bound
    _ ≤ ENNReal.ofReal (Ca : ℝ) *
        ((Ceval : ℝ≥0∞) *
          ENNReal.ofReal
            (squareIntegrableHilbertBundleSectionL2Norm
              (manifoldDifferentialHilbertBundleGeometry
                (I := I) (X := X) (E := E) g) μ w)) :=
      mul_le_mul_right hg_bound (ENNReal.ofReal (Ca : ℝ))
    _ = ((Ca * Ceval : NNReal) : ℝ≥0∞) *
        ENNReal.ofReal
          (squareIntegrableHilbertBundleSectionL2Norm
            (manifoldDifferentialHilbertBundleGeometry
              (I := I) (X := X) (E := E) g) μ w) := by
      simp [mul_assoc]

/--
%%handwave
name:
  Differential multipliers are locally square-integrable in coordinates
statement:
  In a coordinate chart, a bounded compactly supported scalar multiplier times
  a square-integrable differential-field representative, evaluated on a fixed
  coordinate tangent direction, is square-integrable on the multiplier support
  with respect to Lebesgue measure.
proof:
  On the compact support, the chart tangent vector has uniformly bounded
  Hilbert--Schmidt evaluation norm, and the smooth positive coordinate density
  is bounded above and below.  Hence intrinsic \(L^2\)-control of the
  differential field gives coordinate \(L^2\)-control of the evaluated field.
  Multiplication by a bounded scalar preserves \(L^2\).
-/
theorem manifoldDifferentialCompactlySupportedMultiplier_memLp_two_on_support
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [IsManifold I 1 X] [IsIdentityManifoldModel H I]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := I) X E)]
    [TopologicalSpace.PseudoMetrizableSpace (ManifoldDifferentialTotalSpace (I := I) X E)]
    (g : SmoothRiemannianMetricOnManifold I X) (μ : Measure X)
    (_hμ : SmoothPositiveMeasureOnManifold (I := I) μ) :
    ∀ (e : OpenPartialHomeomorph X H) (_he : e ∈ atlas H X)
      (a : H → ℝ) (v : H),
      Continuous a →
      (∃ C : NNReal, ∀ z : H, ‖a z‖ ≤ C) →
      tsupport a ⊆ manifoldChartRegion e (Set.univ : Set X) →
      IsCompact (tsupport a) →
      ∀ w : SquareIntegrableManifoldDifferentialField
        (I := I) (X := X) (E := E) g μ,
        MemLp
          (fun z ↦ a z • ManifoldDifferentialField.evalChart w.toField e z v)
          2
          (MeasureTheory.volume.restrict (tsupport a)) := by
  intro e he a v ha_cont ha_bound ha_support ha_compact w
  rcases manifoldDifferentialCompactlySupportedMultiplier_eLpNorm_two_on_support_le
      (I := I) (X := X) (E := E) g μ _hμ e he a v
      ha_cont ha_bound ha_support ha_compact with
    ⟨C, hC⟩
  exact (hC w).1

/--
%%handwave
name:
  Bounded compactly supported coordinate multipliers give integrable
  differential pairings
statement:
  In a coordinate chart, multiplying a square-integrable differential-field
  representative, evaluated on a fixed coordinate tangent direction, by a
  bounded continuous scalar multiplier with compact support inside the
  coordinate region gives a Bochner integrable function.
proof:
  On the compact support, evaluation on the fixed chart tangent direction is
  uniformly bounded by the Hilbert--Schmidt fiber norm, and the coordinate
  density is comparable with the smooth positive measure.  The multiplier is
  bounded and supported on a finite-measure compact set.  Cauchy--Schwarz
  gives \(L^1\)-integrability.
-/
theorem manifoldDifferentialCompactlySupportedMultiplier_integrable
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [IsManifold I 1 X] [IsIdentityManifoldModel H I]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := I) X E)]
    [TopologicalSpace.PseudoMetrizableSpace (ManifoldDifferentialTotalSpace (I := I) X E)]
    (g : SmoothRiemannianMetricOnManifold I X) (μ : Measure X)
    (_hμ : SmoothPositiveMeasureOnManifold (I := I) μ) :
    ∀ (e : OpenPartialHomeomorph X H) (_he : e ∈ atlas H X)
      (a : H → ℝ) (v : H),
      Continuous a →
      (∃ C : NNReal, ∀ z : H, ‖a z‖ ≤ C) →
      tsupport a ⊆ manifoldChartRegion e (Set.univ : Set X) →
      IsCompact (tsupport a) →
      ∀ w : SquareIntegrableManifoldDifferentialField
        (I := I) (X := X) (E := E) g μ,
        Integrable
          (fun z ↦ a z • ManifoldDifferentialField.evalChart w.toField e z v)
          (MeasureTheory.volume.restrict
            (manifoldChartRegion e (Set.univ : Set X))) := by
  intro e he a v ha_cont ha_bound ha_support ha_compact w
  let Ω : Set H := manifoldChartRegion e (Set.univ : Set X)
  let F : H → E :=
    fun z ↦ a z • ManifoldDifferentialField.evalChart w.toField e z v
  have hF_memLp :
      MemLp F 2 (MeasureTheory.volume.restrict (tsupport a)) := by
    simpa [F] using
      manifoldDifferentialCompactlySupportedMultiplier_memLp_two_on_support
        (I := I) (X := X) (E := E) g μ _hμ e he a v
        ha_cont ha_bound ha_support ha_compact w
  have hK_finite :
      MeasureTheory.volume (tsupport a) ≠ (∞ : ℝ≥0∞) :=
    smoothPositiveMeasureOnManifold_chart_volume_finite_of_compact
      (I := I) (X := X) μ _hμ e he (tsupport a)
      (by simpa [Ω] using ha_support) ha_compact
  have hF_support : Function.support F ⊆ tsupport a := by
    intro z hz
    by_contra hz_support
    have ha_zero : a z = 0 := image_eq_zero_of_notMem_tsupport hz_support
    exact hz (by simp [F, ha_zero])
  exact integrableOn_region_of_memLp_two_restrict_support
    (ν := MeasureTheory.volume) (Ω := Ω) (K := tsupport a)
    hF_memLp hK_finite hF_support (by simpa [Ω] using ha_support)

/--
%%handwave
name:
  Bounded compactly supported coordinate multipliers give Lipschitz
  differential pairings
statement:
  In a coordinate chart, integrating a square-integrable differential-field
  representative evaluated on a fixed tangent direction against a bounded
  continuous compactly supported scalar multiplier is Lipschitz in the
  intrinsic differential \(L^2\)-distance.
proof:
  Apply the preceding integrability estimate to differences.  The uniform
  Hilbert--Schmidt bound for evaluation on the fixed direction, the local
  comparison between the smooth positive measure and coordinate Lebesgue
  measure, and the boundedness of the multiplier reduce the estimate to
  Cauchy--Schwarz on its compact support.
-/
theorem manifoldDifferentialCompactlySupportedMultiplier_integral_lipschitz_estimate
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [IsManifold I 1 X] [IsIdentityManifoldModel H I]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := I) X E)]
    [TopologicalSpace.PseudoMetrizableSpace (ManifoldDifferentialTotalSpace (I := I) X E)]
    (g : SmoothRiemannianMetricOnManifold I X) (μ : Measure X)
    (_hμ : SmoothPositiveMeasureOnManifold (I := I) μ) :
    letI : NormedAddCommGroup
        (ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ) :=
      manifoldDifferentialL2SectionNormedAddCommGroup (I := I) (X := X) (E := E) g μ
    ∀ (e : OpenPartialHomeomorph X H) (_he : e ∈ atlas H X)
      (a : H → ℝ) (v : H),
      Continuous a →
      (∃ C : NNReal, ∀ z : H, ‖a z‖ ≤ C) →
      tsupport a ⊆ manifoldChartRegion e (Set.univ : Set X) →
      IsCompact (tsupport a) →
      ∃ K : NNReal,
        ∀ w₁ w₂ : SquareIntegrableManifoldDifferentialField
            (I := I) (X := X) (E := E) g μ,
          edist
            (∫ z in manifoldChartRegion e (Set.univ : Set X),
              a z • ManifoldDifferentialField.evalChart w₁.toField e z v
              ∂MeasureTheory.volume)
            (∫ z in manifoldChartRegion e (Set.univ : Set X),
              a z • ManifoldDifferentialField.evalChart w₂.toField e z v
              ∂MeasureTheory.volume) ≤
            K *
              edist
                (Quotient.mk
                  (SquareIntegrableManifoldDifferentialField.aeSetoid
                    (I := I) (X := X) (E := E) (g := g) (μ := μ)) w₁ :
                  ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ)
                (Quotient.mk
                  (SquareIntegrableManifoldDifferentialField.aeSetoid
                    (I := I) (X := X) (E := E) (g := g) (μ := μ)) w₂ :
                  ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ) := by
  classical
  letI : NormedAddCommGroup
      (ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ) :=
    manifoldDifferentialL2SectionNormedAddCommGroup (I := I) (X := X) (E := E) g μ
  intro e he a v ha_cont ha_bound ha_support ha_compact
  let Ω : Set H := manifoldChartRegion e (Set.univ : Set X)
  let K : Set H := tsupport a
  let q : ℝ := ((1 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal
  let Mpow : ℝ≥0∞ := MeasureTheory.volume K ^ q
  rcases manifoldDifferentialCompactlySupportedMultiplier_eLpNorm_two_on_support_le
      (I := I) (X := X) (E := E) g μ _hμ e he a v
      ha_cont ha_bound (by simpa [K, Ω] using ha_support) ha_compact with
    ⟨Cdiff, hCdiff⟩
  let B : ℝ≥0∞ := Mpow * (Cdiff : ℝ≥0∞)
  have hK_finite : MeasureTheory.volume K ≠ (∞ : ℝ≥0∞) :=
    smoothPositiveMeasureOnManifold_chart_volume_finite_of_compact
      (I := I) (X := X) μ _hμ e he K
      (by simpa [K, Ω] using ha_support) ha_compact
  have hq_nonneg : 0 ≤ q := by
    norm_num [q]
  have hMpow_ne_top : Mpow ≠ (∞ : ℝ≥0∞) := by
    exact (ENNReal.rpow_lt_top_of_nonneg hq_nonneg
      (by simpa [Mpow, K] using hK_finite)).ne
  have hB_ne_top : B ≠ (∞ : ℝ≥0∞) := by
    dsimp [B]
    exact ENNReal.mul_ne_top hMpow_ne_top ENNReal.coe_ne_top
  refine ⟨B.toNNReal, ?_⟩
  intro w₁ w₂
  let μΩ : Measure H := MeasureTheory.volume.restrict Ω
  let wdiff : SquareIntegrableManifoldDifferentialField
      (I := I) (X := X) (E := E) g μ :=
    squareIntegrableManifoldDifferentialFieldSub
      (I := I) (X := X) (E := E) g μ w₁ w₂
  let F₁ : H → E :=
    fun z ↦ a z • ManifoldDifferentialField.evalChart w₁.toField e z v
  let F₂ : H → E :=
    fun z ↦ a z • ManifoldDifferentialField.evalChart w₂.toField e z v
  let Fdiff : H → E :=
    fun z ↦ a z • ManifoldDifferentialField.evalChart wdiff.toField e z v
  let u₁ : ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ :=
    Quotient.mk
      (SquareIntegrableManifoldDifferentialField.aeSetoid
        (I := I) (X := X) (E := E) (g := g) (μ := μ)) w₁
  let u₂ : ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ :=
    Quotient.mk
      (SquareIntegrableManifoldDifferentialField.aeSetoid
        (I := I) (X := X) (E := E) (g := g) (μ := μ)) w₂
  have hF₁_int : Integrable F₁ μΩ := by
    simpa [F₁, μΩ, Ω] using
      manifoldDifferentialCompactlySupportedMultiplier_integrable
        (I := I) (X := X) (E := E) g μ _hμ e he a v
        ha_cont ha_bound (by simpa [K, Ω] using ha_support)
        ha_compact w₁
  have hF₂_int : Integrable F₂ μΩ := by
    simpa [F₂, μΩ, Ω] using
      manifoldDifferentialCompactlySupportedMultiplier_integrable
        (I := I) (X := X) (E := E) g μ _hμ e he a v
        ha_cont ha_bound (by simpa [K, Ω] using ha_support)
        ha_compact w₂
  have hdiff_bound := hCdiff wdiff
  have hFdiff_memLp2 : MemLp Fdiff 2 (MeasureTheory.volume.restrict K) := by
    simpa [Fdiff, K] using hdiff_bound.1
  have hFdiff2_le :
      eLpNorm Fdiff 2 (MeasureTheory.volume.restrict K) ≤
        (Cdiff : ℝ≥0∞) *
          ENNReal.ofReal
            (squareIntegrableHilbertBundleSectionL2Norm
              (manifoldDifferentialHilbertBundleGeometry
                (I := I) (X := X) (E := E) g) μ wdiff) := by
    simpa [Fdiff, K] using hdiff_bound.2
  have hsub_ae : (fun z : H ↦ F₁ z - F₂ z) =ᵐ[μΩ] Fdiff := by
    filter_upwards [] with z
    simp [F₁, F₂, Fdiff, wdiff, squareIntegrableManifoldDifferentialFieldSub,
      squareIntegrableHilbertBundleSectionSub,
      SquareIntegrableManifoldDifferentialField.toField,
      ManifoldDifferentialField.evalChart, Pi.add_apply, Pi.neg_apply,
      sub_eq_add_neg]
  have hintegral_sub :
      (∫ z, F₁ z ∂μΩ) - (∫ z, F₂ z ∂μΩ) =
        ∫ z, Fdiff z ∂μΩ := by
    rw [← integral_sub hF₁_int hF₂_int]
    exact integral_congr_ae hsub_ae
  have hFdiff_support : Function.support Fdiff ⊆ K := by
    intro z hz
    by_contra hzK
    have ha_zero : a z = 0 := image_eq_zero_of_notMem_tsupport (by simpa [K] using hzK)
    exact hz (by simp [Fdiff, ha_zero])
  have hrestrict_eq :
      eLpNorm Fdiff 1 μΩ = eLpNorm Fdiff 1 (MeasureTheory.volume.restrict K) := by
    rw [← eLpNorm_restrict_eq_of_support_subset
      (μ := μΩ) (s := K) (p := (1 : ℝ≥0∞)) hFdiff_support]
    rw [Measure.restrict_restrict_of_subset]
    exact by
      simpa [μΩ, Ω, K] using ha_support
  have hL1L2 :
      eLpNorm Fdiff 1 (MeasureTheory.volume.restrict K) ≤
        eLpNorm Fdiff 2 (MeasureTheory.volume.restrict K) * Mpow := by
    have h :=
      eLpNorm_le_eLpNorm_mul_rpow_measure_univ
        (μ := MeasureTheory.volume.restrict K) (f := Fdiff)
        (p := (1 : ℝ≥0∞)) (q := (2 : ℝ≥0∞))
        (by norm_num) hFdiff_memLp2.1
    have h' :
        eLpNorm Fdiff 1 (MeasureTheory.volume.restrict K) ≤
          eLpNorm Fdiff 2 (MeasureTheory.volume.restrict K) *
            MeasureTheory.volume K ^
              (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) := by
      simpa [Measure.restrict_apply_univ] using h
    have hq_eq :
        (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) = q := by
      norm_num [q]
    have hq_eq' : (1 : ℝ) - (2 : ℝ)⁻¹ = q := by
      norm_num [q]
    simpa [Mpow, hq_eq, hq_eq'] using h'
  have hdist_eq :
      ENNReal.ofReal
          (squareIntegrableHilbertBundleSectionL2Norm
            (manifoldDifferentialHilbertBundleGeometry
              (I := I) (X := X) (E := E) g) μ wdiff) =
        edist u₁ u₂ := by
    simpa [wdiff, u₁, u₂] using
      (manifoldDifferentialL2Section_edist_mk_eq_ofReal_l2Norm_sub
        (I := I) (X := X) (E := E) g μ w₁ w₂).symm
  have hmain :
      edist (∫ z, F₁ z ∂μΩ) (∫ z, F₂ z ∂μΩ) ≤
        B * edist u₁ u₂ := by
    calc
      edist (∫ z, F₁ z ∂μΩ) (∫ z, F₂ z ∂μΩ)
          = ‖(∫ z, F₁ z ∂μΩ) - (∫ z, F₂ z ∂μΩ)‖ₑ := by
              rw [edist_eq_enorm_sub]
      _ = ‖∫ z, Fdiff z ∂μΩ‖ₑ := by rw [hintegral_sub]
      _ ≤ ∫⁻ z, ‖Fdiff z‖ₑ ∂μΩ :=
          enorm_integral_le_lintegral_enorm Fdiff
      _ = eLpNorm Fdiff 1 μΩ := by
          rw [eLpNorm_one_eq_lintegral_enorm]
      _ = eLpNorm Fdiff 1 (MeasureTheory.volume.restrict K) := hrestrict_eq
      _ ≤ eLpNorm Fdiff 2 (MeasureTheory.volume.restrict K) * Mpow := hL1L2
      _ ≤ ((Cdiff : ℝ≥0∞) *
            ENNReal.ofReal
              (squareIntegrableHilbertBundleSectionL2Norm
                (manifoldDifferentialHilbertBundleGeometry
                  (I := I) (X := X) (E := E) g) μ wdiff)) * Mpow :=
          mul_le_mul_left hFdiff2_le Mpow
      _ = B *
            ENNReal.ofReal
              (squareIntegrableHilbertBundleSectionL2Norm
                (manifoldDifferentialHilbertBundleGeometry
                  (I := I) (X := X) (E := E) g) μ wdiff) := by
          dsimp [B, Mpow]
          ac_rfl
      _ = B * edist u₁ u₂ := by rw [hdist_eq]
  change edist (∫ z, F₁ z ∂μΩ) (∫ z, F₂ z ∂μΩ) ≤
    (B.toNNReal : ℝ≥0∞) * edist u₁ u₂
  calc
    edist (∫ z, F₁ z ∂μΩ) (∫ z, F₂ z ∂μΩ) ≤
        B * edist u₁ u₂ := hmain
    _ = (B.toNNReal : ℝ≥0∞) * edist u₁ u₂ := by
        rw [ENNReal.coe_toNNReal hB_ne_top]

/--
%%handwave
name:
  Coordinate differential test integrands are integrable
statement:
  Fix a coordinate chart, a compactly supported coordinate test function, and
  a tangent direction.  Multiplying a square-integrable differential-field
  representative, evaluated on that tangent direction, by the test function
  gives a Bochner integrable function on the coordinate region.
proof:
  The test function is bounded and compactly supported.  On its compact
  support, evaluation on the fixed chart tangent direction is bounded by the
  Hilbert--Schmidt fiber norm with a uniform local constant, and the coordinate
  density is comparable with the smooth positive measure.  Cauchy--Schwarz
  gives integrability.
-/
theorem manifoldDifferentialCoordinateTestPairing_integrable
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [IsManifold I 1 X] [IsIdentityManifoldModel H I]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := I) X E)]
    [TopologicalSpace.PseudoMetrizableSpace (ManifoldDifferentialTotalSpace (I := I) X E)]
    (g : SmoothRiemannianMetricOnManifold I X) (μ : Measure X)
    (_hμ : SmoothPositiveMeasureOnManifold (I := I) μ) :
    ∀ (e : OpenPartialHomeomorph X H) (_he : e ∈ atlas H X)
      (φ : SmoothCompactlySupportedManifoldCoordinateFunction
        (manifoldChartRegion e (Set.univ : Set X)))
      (v : H)
      (w : SquareIntegrableManifoldDifferentialField
        (I := I) (X := X) (E := E) g μ),
      Integrable
        (fun z ↦ φ z • ManifoldDifferentialField.evalChart w.toField e z v)
        (MeasureTheory.volume.restrict
          (manifoldChartRegion e (Set.univ : Set X))) := by
  intro e he φ v w
  have hφ_cont : Continuous (φ : H → ℝ) := φ.smooth.continuous
  have hφ_bound : ∃ C : NNReal, ∀ z : H, ‖(φ : H → ℝ) z‖ ≤ C :=
    SmoothCompactlySupportedManifoldCoordinateFunction.exists_bound φ
  exact manifoldDifferentialCompactlySupportedMultiplier_integrable
    (I := I) (X := X) (E := E) g μ _hμ e he (φ : H → ℝ) v
    hφ_cont hφ_bound φ.support_subset φ.compact_support w

/--
%%handwave
name:
  Coordinate differential test integrals satisfy a Lipschitz estimate
statement:
  Fix a coordinate chart, a compactly supported coordinate test function, and
  a tangent direction.  The coordinate differential test integral is Lipschitz
  in the intrinsic differential \(L^2\)-distance of square-integrable
  representatives.
proof:
  Apply the integrability estimate to differences.  The bounded test function,
  the local Hilbert--Schmidt bound for evaluation on the fixed direction, and
  the local comparison of smooth positive measure with coordinate Lebesgue
  measure reduce the estimate to Cauchy--Schwarz.
-/
theorem manifoldDifferentialCoordinateTestPairing_integral_lipschitz_estimate
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [IsManifold I 1 X] [IsIdentityManifoldModel H I]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := I) X E)]
    [TopologicalSpace.PseudoMetrizableSpace (ManifoldDifferentialTotalSpace (I := I) X E)]
    (g : SmoothRiemannianMetricOnManifold I X) (μ : Measure X)
    (_hμ : SmoothPositiveMeasureOnManifold (I := I) μ) :
    letI : NormedAddCommGroup
        (ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ) :=
      manifoldDifferentialL2SectionNormedAddCommGroup (I := I) (X := X) (E := E) g μ
    ∀ (e : OpenPartialHomeomorph X H) (_he : e ∈ atlas H X)
      (φ : SmoothCompactlySupportedManifoldCoordinateFunction
        (manifoldChartRegion e (Set.univ : Set X)))
      (v : H),
      ∃ K : NNReal,
        ∀ w₁ w₂ : SquareIntegrableManifoldDifferentialField
            (I := I) (X := X) (E := E) g μ,
          edist
            (∫ z in manifoldChartRegion e (Set.univ : Set X),
              φ z • ManifoldDifferentialField.evalChart w₁.toField e z v
              ∂MeasureTheory.volume)
            (∫ z in manifoldChartRegion e (Set.univ : Set X),
              φ z • ManifoldDifferentialField.evalChart w₂.toField e z v
              ∂MeasureTheory.volume) ≤
            K *
              edist
                (Quotient.mk
                  (SquareIntegrableManifoldDifferentialField.aeSetoid
                    (I := I) (X := X) (E := E) (g := g) (μ := μ)) w₁ :
                  ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ)
                (Quotient.mk
                  (SquareIntegrableManifoldDifferentialField.aeSetoid
                    (I := I) (X := X) (E := E) (g := g) (μ := μ)) w₂ :
                  ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ) := by
  letI : NormedAddCommGroup
      (ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ) :=
    manifoldDifferentialL2SectionNormedAddCommGroup (I := I) (X := X) (E := E) g μ
  intro e he φ v
  have hφ_cont : Continuous (φ : H → ℝ) := φ.smooth.continuous
  have hφ_bound : ∃ C : NNReal, ∀ z : H, ‖(φ : H → ℝ) z‖ ≤ C :=
    SmoothCompactlySupportedManifoldCoordinateFunction.exists_bound φ
  rcases manifoldDifferentialCompactlySupportedMultiplier_integral_lipschitz_estimate
      (I := I) (X := X) (E := E) g μ _hμ e he (φ : H → ℝ) v
      hφ_cont hφ_bound φ.support_subset φ.compact_support with
    ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro w₁ w₂
  simpa using hK w₁ w₂

/--
%%handwave
name:
  Coordinate differential test pairings have Lipschitz \(L^2\)-section
  representers
statement:
  Fix a coordinate chart, a compactly supported coordinate test function, and
  a tangent direction.  The coordinate integral obtained by evaluating a
  differential representative on the chart tangent direction and multiplying
  by the test function descends to a Lipschitz map from the intrinsic
  differential \(L^2\)-section space to the target Hilbert space.
proof:
  On the compact support of the test function, the smooth positive density and
  the Hilbert--Schmidt metric are uniformly comparable with their coordinate
  expressions.  Evaluating a cotangent-valued section on the fixed chart
  tangent direction and multiplying by the bounded test function is therefore
  bounded by a constant times the Hilbert--Schmidt norm.  Cauchy--Schwarz gives
  the Lipschitz estimate on the quotient and representative independence.
-/
theorem manifoldDifferentialCoordinateTestPairing_has_lipschitz_l2_representer
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [IsManifold I 1 X] [IsIdentityManifoldModel H I]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := I) X E)]
    [TopologicalSpace.PseudoMetrizableSpace (ManifoldDifferentialTotalSpace (I := I) X E)]
    (g : SmoothRiemannianMetricOnManifold I X) (μ : Measure X)
    (_hμ : SmoothPositiveMeasureOnManifold (I := I) μ) :
    letI : NormedAddCommGroup
        (ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ) :=
      manifoldDifferentialL2SectionNormedAddCommGroup (I := I) (X := X) (E := E) g μ
    ∀ (e : OpenPartialHomeomorph X H) (_he : e ∈ atlas H X)
      (φ : SmoothCompactlySupportedManifoldCoordinateFunction
        (manifoldChartRegion e (Set.univ : Set X)))
      (v : H),
      ∃ K : NNReal,
      ∃ T : ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ → E,
        LipschitzWith K T ∧
          ∀ w : SquareIntegrableManifoldDifferentialField
              (I := I) (X := X) (E := E) g μ,
            Integrable
              (fun z ↦ φ z • ManifoldDifferentialField.evalChart w.toField e z v)
              (MeasureTheory.volume.restrict
                (manifoldChartRegion e (Set.univ : Set X))) ∧
            (∫ z in manifoldChartRegion e (Set.univ : Set X),
                φ z • ManifoldDifferentialField.evalChart w.toField e z v
                ∂MeasureTheory.volume) =
              T
                (Quotient.mk
                  (SquareIntegrableManifoldDifferentialField.aeSetoid
                    (I := I) (X := X) (E := E) (g := g) (μ := μ)) w) := by
  letI : NormedAddCommGroup
      (ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ) :=
    manifoldDifferentialL2SectionNormedAddCommGroup (I := I) (X := X) (E := E) g μ
  intro e he φ v
  rcases manifoldDifferentialCoordinateTestPairing_integral_lipschitz_estimate
      (I := I) (X := X) (E := E) g μ _hμ e he φ v with
    ⟨K, hK⟩
  let F :
      SquareIntegrableManifoldDifferentialField
        (I := I) (X := X) (E := E) g μ → E :=
    fun w ↦
      ∫ z in manifoldChartRegion e (Set.univ : Set X),
        φ z • ManifoldDifferentialField.evalChart w.toField e z v
        ∂MeasureTheory.volume
  have hF_congr :
      ∀ w₁ w₂ : SquareIntegrableManifoldDifferentialField
          (I := I) (X := X) (E := E) g μ,
        SquareIntegrableHilbertBundleSection.AeEq w₁ w₂ → F w₁ = F w₂ := by
    intro w₁ w₂ h12
    have hclasses :
        (Quotient.mk
          (SquareIntegrableManifoldDifferentialField.aeSetoid
            (I := I) (X := X) (E := E) (g := g) (μ := μ)) w₁ :
          ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ) =
          Quotient.mk
            (SquareIntegrableManifoldDifferentialField.aeSetoid
              (I := I) (X := X) (E := E) (g := g) (μ := μ)) w₂ :=
      Quotient.sound h12
    have hdist_zero : edist (F w₁) (F w₂) = 0 := by
      have hle : edist (F w₁) (F w₂) ≤
          K *
            edist
              (Quotient.mk
                (SquareIntegrableManifoldDifferentialField.aeSetoid
                  (I := I) (X := X) (E := E) (g := g) (μ := μ)) w₁ :
                ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ)
              (Quotient.mk
                (SquareIntegrableManifoldDifferentialField.aeSetoid
                  (I := I) (X := X) (E := E) (g := g) (μ := μ)) w₂ :
                ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ) := by
        simpa [F] using hK w₁ w₂
      rw [hclasses, edist_self, mul_zero] at hle
      exact le_antisymm hle zero_le
    exact eq_of_edist_eq_zero hdist_zero
  let T : ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ → E :=
    Quotient.lift F (by
      intro w₁ w₂ h
      exact hF_congr w₁ w₂ h)
  refine ⟨K, T, ?_, ?_⟩
  · intro q r
    refine Quotient.inductionOn₂ q r ?_
    intro w₁ w₂
    simpa [T, F] using hK w₁ w₂
  · intro w
    exact ⟨manifoldDifferentialCoordinateTestPairing_integrable
      (I := I) (X := X) (E := E) g μ _hμ e he φ v w, by simp [T, F]⟩

/--
%%handwave
name:
  Coordinate differential test pairings are continuous for \(L^2\)-section limits
statement:
  Fix a coordinate chart, a compactly supported coordinate test function, and
  a tangent direction.  If differential representatives converge in the
  intrinsic \(L^2\)-section quotient, then the coordinate integral obtained by
  evaluating the differential on the chart tangent direction and multiplying
  by the test function converges to the corresponding limiting coordinate
  integral.  The limiting coordinate integrand is integrable.
proof:
  The compactly supported test function and the chart tangent direction define
  a bounded test section of the differential Hilbert bundle over the chart
  support.  The smooth positive density of the measure identifies the
  coordinate integral with a continuous \(L^2\)-pairing against this fixed
  square-integrable differential test section.  Continuity of the pairing gives
  the stated convergence and integrability.
-/
theorem manifoldDifferentialCoordinateTestPairing_tendsto_of_tendsto_l2_sections
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [IsManifold I 1 X] [IsIdentityManifoldModel H I]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := I) X E)]
    [TopologicalSpace.PseudoMetrizableSpace (ManifoldDifferentialTotalSpace (I := I) X E)]
    (g : SmoothRiemannianMetricOnManifold I X) (μ : Measure X)
    (_hμ : SmoothPositiveMeasureOnManifold (I := I) μ) :
    letI : NormedAddCommGroup
        (ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ) :=
      manifoldDifferentialL2SectionNormedAddCommGroup (I := I) (X := X) (E := E) g μ
    ∀ {ι : Type} {l : Filter ι} [l.NeBot]
      {du : ι → SquareIntegrableManifoldDifferentialField
        (I := I) (X := X) (E := E) g μ}
      {duLim : SquareIntegrableManifoldDifferentialField
        (I := I) (X := X) (E := E) g μ}
      {duLimClass :
        ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ},
      (Quotient.mk
        (SquareIntegrableManifoldDifferentialField.aeSetoid
          (I := I) (X := X) (E := E) (g := g) (μ := μ)) duLim :
        ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ) =
        duLimClass →
      Filter.Tendsto
        (fun i ↦
          (Quotient.mk
            (SquareIntegrableManifoldDifferentialField.aeSetoid
              (I := I) (X := X) (E := E) (g := g) (μ := μ)) (du i) :
            ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ))
        l
        (𝓝 duLimClass) →
      ∀ (e : OpenPartialHomeomorph X H) (_he : e ∈ atlas H X)
        (φ : SmoothCompactlySupportedManifoldCoordinateFunction
          (manifoldChartRegion e (Set.univ : Set X)))
        (v : H),
        Integrable
            (fun z ↦
              φ z • ManifoldDifferentialField.evalChart duLim.toField e z v)
            (MeasureTheory.volume.restrict
              (manifoldChartRegion e (Set.univ : Set X))) ∧
          Filter.Tendsto
            (fun i ↦
              ∫ z in manifoldChartRegion e (Set.univ : Set X),
                φ z • ManifoldDifferentialField.evalChart (du i).toField e z v
                ∂MeasureTheory.volume)
            l
            (𝓝 (∫ z in manifoldChartRegion e (Set.univ : Set X),
                φ z • ManifoldDifferentialField.evalChart duLim.toField e z v
                ∂MeasureTheory.volume)) := by
  letI : NormedAddCommGroup
      (ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ) :=
    manifoldDifferentialL2SectionNormedAddCommGroup (I := I) (X := X) (E := E) g μ
  intro ι l hne du duLim duLimClass hduLim_eq hdu_tendsto e he φ v
  rcases manifoldDifferentialCoordinateTestPairing_has_lipschitz_l2_representer
      (I := I) (X := X) (E := E) g μ _hμ e he φ v with
    ⟨_K, T, hT_lipschitz, hT⟩
  rcases hT duLim with ⟨hduLim_int, hduLim_integral_eq⟩
  have hT_tendsto :
      Filter.Tendsto
        (fun i ↦
          T
            (Quotient.mk
              (SquareIntegrableManifoldDifferentialField.aeSetoid
                (I := I) (X := X) (E := E) (g := g) (μ := μ)) (du i) :
              ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ))
        l
        (𝓝 (T duLimClass)) :=
    hT_lipschitz.continuous.tendsto duLimClass |>.comp hdu_tendsto
  have hseq_eq :
      (fun i ↦
          T
            (Quotient.mk
              (SquareIntegrableManifoldDifferentialField.aeSetoid
                (I := I) (X := X) (E := E) (g := g) (μ := μ)) (du i) :
              ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ)) =ᶠ[l]
        fun i ↦
          ∫ z in manifoldChartRegion e (Set.univ : Set X),
            φ z • ManifoldDifferentialField.evalChart (du i).toField e z v
            ∂MeasureTheory.volume :=
    Filter.Eventually.of_forall fun i ↦ (hT (du i)).2.symm
  have hlim_eq :
      T duLimClass =
        ∫ z in manifoldChartRegion e (Set.univ : Set X),
          φ z • ManifoldDifferentialField.evalChart duLim.toField e z v
          ∂MeasureTheory.volume := by
    rw [← hduLim_eq]
    exact hduLim_integral_eq.symm
  exact ⟨hduLim_int, by
    have h_integrals_tendsto :=
      Filter.Tendsto.congr' hseq_eq hT_tendsto
    simpa [hlim_eq] using h_integrals_tendsto⟩

/--
%%handwave
name:
  Coordinate weak-derivative identities pass to \(L^2\) limits
statement:
  Fix one coordinate chart, one compactly supported coordinate test function,
  and one tangent direction.  If square-integrable value representatives and
  differential representatives converge in their \(L^2\)-section quotient
  norms and eventually satisfy the weak-derivative identity, then the limiting
  representatives satisfy this fixed coordinate integration-by-parts identity.
proof:
  The compactly supported test gives bounded multiplier sections in the value
  and differential \(L^2\)-section spaces.  The smooth positive density of the
  measure identifies the coordinate Lebesgue integrals with continuous
  \(L^2\)-pairings over the manifold on the compact support.  Therefore both
  integrals in the identity converge separately, and the equality passes to
  the limit.
-/
theorem manifoldWeakDerivative_coordinateTest_identity_of_tendsto_l2_sections
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [IsManifold I 1 X] [IsIdentityManifoldModel H I]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology (Bundle.TotalSpace E (Bundle.Trivial X E))]
    [TopologicalSpace.PseudoMetrizableSpace (Bundle.TotalSpace E (Bundle.Trivial X E))]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := I) X E)]
    [TopologicalSpace.PseudoMetrizableSpace (ManifoldDifferentialTotalSpace (I := I) X E)]
    (g : SmoothRiemannianMetricOnManifold I X) (μ : Measure X)
    (hμ : SmoothPositiveMeasureOnManifold (I := I) μ) :
    letI : NormedAddCommGroup (ValueL2Section (X := X) (E := E) μ) :=
      valueL2SectionNormedAddCommGroup (I := I) (X := X) (E := E) μ
    letI : NormedAddCommGroup
        (ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ) :=
      manifoldDifferentialL2SectionNormedAddCommGroup (I := I) (X := X) (E := E) g μ
    ∀ {ι : Type} {l : Filter ι} [l.NeBot]
      {u : ι → SquareIntegrableValueSection (X := X) (E := E) μ}
      {du : ι → SquareIntegrableManifoldDifferentialField
        (I := I) (X := X) (E := E) g μ}
      {uLim : SquareIntegrableValueSection (X := X) (E := E) μ}
      {duLim : SquareIntegrableManifoldDifferentialField
        (I := I) (X := X) (E := E) g μ}
      {uLimClass : ValueL2Section (X := X) (E := E) μ}
      {duLimClass :
        ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ},
      (∀ᶠ i in l,
        IsWeakDerivativeOnManifoldBundle
          (I := I) μ (u i).toFunction (du i).toField) →
      (Quotient.mk
        (SquareIntegrableValueSection.aeSetoid
          (X := X) (E := E) (μ := μ)) uLim :
        ValueL2Section (X := X) (E := E) μ) = uLimClass →
      (Quotient.mk
        (SquareIntegrableManifoldDifferentialField.aeSetoid
          (I := I) (X := X) (E := E) (g := g) (μ := μ)) duLim :
        ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ) =
        duLimClass →
      Filter.Tendsto
        (fun i ↦
          (Quotient.mk
            (SquareIntegrableValueSection.aeSetoid
              (X := X) (E := E) (μ := μ)) (u i) :
            ValueL2Section (X := X) (E := E) μ))
        l
        (𝓝 uLimClass) →
      Filter.Tendsto
        (fun i ↦
          (Quotient.mk
            (SquareIntegrableManifoldDifferentialField.aeSetoid
              (I := I) (X := X) (E := E) (g := g) (μ := μ)) (du i) :
            ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ))
        l
        (𝓝 duLimClass) →
      ∀ (e : OpenPartialHomeomorph X H) (_he : e ∈ atlas H X)
        (φ : SmoothCompactlySupportedManifoldCoordinateFunction
          (manifoldChartRegion e (Set.univ : Set X)))
        (v : H),
        Integrable
            (fun z ↦ (fderiv ℝ (φ : H → ℝ) z v) • uLim.toFunction (e.symm z))
            (MeasureTheory.volume.restrict
              (manifoldChartRegion e (Set.univ : Set X))) ∧
          Integrable
            (fun z ↦
              φ z • ManifoldDifferentialField.evalChart duLim.toField e z v)
            (MeasureTheory.volume.restrict
              (manifoldChartRegion e (Set.univ : Set X))) ∧
            ∫ z in manifoldChartRegion e (Set.univ : Set X),
                (fderiv ℝ (φ : H → ℝ) z v) • uLim.toFunction (e.symm z)
                ∂MeasureTheory.volume =
              -∫ z in manifoldChartRegion e (Set.univ : Set X),
                φ z • ManifoldDifferentialField.evalChart duLim.toField e z v
                ∂MeasureTheory.volume := by
  intro ι l hne u du uLim duLim uLimClass duLimClass hweak
    huLim_eq hduLim_eq hu_tendsto hdu_tendsto e he φ v
  let Ω : Set H := manifoldChartRegion e (Set.univ : Set X)
  let L : ι → E :=
    fun i ↦
      ∫ z in Ω,
        (fderiv ℝ (φ : H → ℝ) z v) • (u i).toFunction (e.symm z)
        ∂MeasureTheory.volume
  let R : ι → E :=
    fun i ↦
      ∫ z in Ω,
        φ z • ManifoldDifferentialField.evalChart (du i).toField e z v
        ∂MeasureTheory.volume
  let Llim : E :=
    ∫ z in Ω,
      (fderiv ℝ (φ : H → ℝ) z v) • uLim.toFunction (e.symm z)
      ∂MeasureTheory.volume
  let Rlim : E :=
    ∫ z in Ω,
      φ z • ManifoldDifferentialField.evalChart duLim.toField e z v
      ∂MeasureTheory.volume
  rcases manifoldValueCoordinateTestPairing_tendsto_of_tendsto_l2_sections
      (I := I) (X := X) (E := E) μ hμ
      huLim_eq hu_tendsto e he φ v with
    ⟨huLim_int, hL_tendsto⟩
  rcases manifoldDifferentialCoordinateTestPairing_tendsto_of_tendsto_l2_sections
      (I := I) (X := X) (E := E) g μ hμ
      hduLim_eq hdu_tendsto e he φ v with
    ⟨hduLim_int, hR_tendsto⟩
  have hweak_eq_eventually : ∀ᶠ i in l, L i = -R i := by
    filter_upwards [hweak] with i hi
    simpa [L, R, Ω] using (hi e he φ v).2.2
  have hnegR_tendsto_to_Llim :
      Filter.Tendsto (fun i ↦ -R i) l (𝓝 Llim) := by
    exact Filter.Tendsto.congr' hweak_eq_eventually
      (by simpa [L, Llim, Ω] using hL_tendsto)
  have hnegR_tendsto_to_neg_Rlim :
      Filter.Tendsto (fun i ↦ -R i) l (𝓝 (-Rlim)) := by
    have hR_tendsto' : Filter.Tendsto R l (𝓝 Rlim) := by
      simpa [R, Rlim, Ω] using hR_tendsto
    exact hR_tendsto'.neg
  have hlim_eq : Llim = -Rlim :=
    tendsto_nhds_unique hnegR_tendsto_to_Llim hnegR_tendsto_to_neg_Rlim
  exact ⟨huLim_int, hduLim_int, by simpa [Llim, Rlim, Ω] using hlim_eq⟩

/--
%%handwave
name:
  Weak derivatives pass to limits of square-integrable representatives
statement:
  If square-integrable value representatives and square-integrable
  differential representatives converge in their \(L^2\)-section quotient
  norms, and the differential representatives are eventually weak
  derivatives of the value representatives, then the limiting representative
  satisfies the weak-derivative identities.
proof:
  Fix a compactly supported coordinate test.  The smooth positive density
  hypothesis represents the associated coordinate pairing as a continuous
  \(L^2\)-pairing against a compactly supported square-integrable test
  section.  The two sides of the integration-by-parts identity therefore
  converge separately, and the identity passes to the limit.
-/
theorem isWeakDerivativeOnManifoldBundle_of_tendsto_l2_sections
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [IsManifold I 1 X] [IsIdentityManifoldModel H I]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology (Bundle.TotalSpace E (Bundle.Trivial X E))]
    [TopologicalSpace.PseudoMetrizableSpace (Bundle.TotalSpace E (Bundle.Trivial X E))]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := I) X E)]
    [TopologicalSpace.PseudoMetrizableSpace (ManifoldDifferentialTotalSpace (I := I) X E)]
    (g : SmoothRiemannianMetricOnManifold I X) (μ : Measure X)
    (_hμ : SmoothPositiveMeasureOnManifold (I := I) μ) :
    letI : NormedAddCommGroup (ValueL2Section (X := X) (E := E) μ) :=
      valueL2SectionNormedAddCommGroup (I := I) (X := X) (E := E) μ
    letI : NormedAddCommGroup
        (ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ) :=
      manifoldDifferentialL2SectionNormedAddCommGroup (I := I) (X := X) (E := E) g μ
    ∀ {ι : Type} {l : Filter ι} [l.NeBot]
      {u : ι → SquareIntegrableValueSection (X := X) (E := E) μ}
      {du : ι → SquareIntegrableManifoldDifferentialField
        (I := I) (X := X) (E := E) g μ}
      {uLim : SquareIntegrableValueSection (X := X) (E := E) μ}
      {duLim : SquareIntegrableManifoldDifferentialField
        (I := I) (X := X) (E := E) g μ}
      {uLimClass : ValueL2Section (X := X) (E := E) μ}
      {duLimClass :
        ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ},
      (∀ᶠ i in l,
        IsWeakDerivativeOnManifoldBundle
          (I := I) μ (u i).toFunction (du i).toField) →
      (Quotient.mk
        (SquareIntegrableValueSection.aeSetoid
          (X := X) (E := E) (μ := μ)) uLim :
        ValueL2Section (X := X) (E := E) μ) = uLimClass →
      (Quotient.mk
        (SquareIntegrableManifoldDifferentialField.aeSetoid
          (I := I) (X := X) (E := E) (g := g) (μ := μ)) duLim :
        ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ) =
        duLimClass →
      Filter.Tendsto
        (fun i ↦
          (Quotient.mk
            (SquareIntegrableValueSection.aeSetoid
              (X := X) (E := E) (μ := μ)) (u i) :
            ValueL2Section (X := X) (E := E) μ))
        l
        (𝓝 uLimClass) →
      Filter.Tendsto
        (fun i ↦
          (Quotient.mk
            (SquareIntegrableManifoldDifferentialField.aeSetoid
              (I := I) (X := X) (E := E) (g := g) (μ := μ)) (du i) :
            ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ))
        l
        (𝓝 duLimClass) →
      IsWeakDerivativeOnManifoldBundle
        (I := I) μ uLim.toFunction duLim.toField := by
  intro ι l hne u du uLim duLim uLimClass duLimClass hweak
    huLim_eq hduLim_eq hu_tendsto hdu_tendsto e he φ v
  exact
    manifoldWeakDerivative_coordinateTest_identity_of_tendsto_l2_sections
      (I := I) (X := X) (E := E) g μ _hμ
      hweak huLim_eq hduLim_eq hu_tendsto hdu_tendsto e he φ v

/--
%%handwave
name:
  The intrinsic weak-derivative graph is sequentially closed under \(L^2\)
  convergence
statement:
  If a net of pairs \((u_i,\alpha_i)\) in the first-order \(L^2\) product
  converges to \((u,\alpha)\), and eventually each \(\alpha_i\) is the weak
  differential of \(u_i\), then \(\alpha\) is the weak differential of \(u\).
proof:
  For each compactly supported coordinate test, represent the test pairing as
  a continuous functional on the appropriate \(L^2\)-section space.  The
  distributional identities for the approximating pairs then pass to the
  limit by continuity of the \(L^2\) pairings.
-/
theorem weakDerivativeIntrinsicGraphOnManifoldWithValues_mem_of_tendsto
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [IsManifold I 1 X] [IsIdentityManifoldModel H I]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology (Bundle.TotalSpace E (Bundle.Trivial X E))]
    [TopologicalSpace.PseudoMetrizableSpace (Bundle.TotalSpace E (Bundle.Trivial X E))]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := I) X E)]
    [TopologicalSpace.PseudoMetrizableSpace (ManifoldDifferentialTotalSpace (I := I) X E)]
    (g : SmoothRiemannianMetricOnManifold I X) (μ : Measure X)
    (_hμ : SmoothPositiveMeasureOnManifold (I := I) μ) :
    letI : NormedAddCommGroup (ValueL2Section (X := X) (E := E) μ) :=
      valueL2SectionNormedAddCommGroup (I := I) (X := X) (E := E) μ
    letI : NormedAddCommGroup
        (ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ) :=
      manifoldDifferentialL2SectionNormedAddCommGroup (I := I) (X := X) (E := E) g μ
    ∀ {ι : Type} {l : Filter ι} [l.NeBot]
      {p : ι → SobolevH1OnManifoldWithValuesIntrinsicAmbientModel
        (I := I) (X := X) (E := E) g μ}
      {q : SobolevH1OnManifoldWithValuesIntrinsicAmbientModel
        (I := I) (X := X) (E := E) g μ},
      (∀ᶠ i in l, WeakDerivativeIntrinsicGraphOnManifoldWithValues g μ (p i)) →
      Filter.Tendsto p l (𝓝 q) →
      WeakDerivativeIntrinsicGraphOnManifoldWithValues g μ q := by
  letI : NormedAddCommGroup (ValueL2Section (X := X) (E := E) μ) :=
    valueL2SectionNormedAddCommGroup (I := I) (X := X) (E := E) μ
  letI : NormedAddCommGroup
      (ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ) :=
    manifoldDifferentialL2SectionNormedAddCommGroup (I := I) (X := X) (E := E) g μ
  classical
  intro ι l hne p q hp_graph hp_tendsto
  let uLim : SquareIntegrableValueSection (X := X) (E := E) μ :=
    Quotient.out ((WithLp.ofLp q).1 :
      ValueL2Section (X := X) (E := E) μ)
  let duLim : SquareIntegrableManifoldDifferentialField
      (I := I) (X := X) (E := E) g μ :=
    Quotient.out ((WithLp.ofLp q).2 :
      ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ)
  let uRep : ι → SquareIntegrableValueSection (X := X) (E := E) μ := fun i ↦
    if h : WeakDerivativeIntrinsicGraphOnManifoldWithValues g μ (p i) then
      Classical.choose h
    else
      uLim
  let duRep : ι → SquareIntegrableManifoldDifferentialField
      (I := I) (X := X) (E := E) g μ := fun i ↦
    if h : WeakDerivativeIntrinsicGraphOnManifoldWithValues g μ (p i) then
      Classical.choose (Classical.choose_spec h)
    else
      duLim
  have hweak :
      ∀ᶠ i in l,
        IsWeakDerivativeOnManifoldBundle
          (I := I) μ (uRep i).toFunction (duRep i).toField := by
    filter_upwards [hp_graph] with i hi
    dsimp [uRep, duRep]
    rw [dif_pos hi, dif_pos hi]
    exact (Classical.choose_spec (Classical.choose_spec hi)).2.2
  have hp_ofLp :
      Filter.Tendsto
        (fun i ↦ WithLp.ofLp (p i))
        l
        (𝓝 (WithLp.ofLp q :
          ValueL2Section (X := X) (E := E) μ ×
            ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ)) := by
    exact
      ((WithLp.prod_continuous_ofLp (p := 2)
        (α := ValueL2Section (X := X) (E := E) μ)
        (β := ManifoldDifferentialL2Section
          (I := I) (X := X) (E := E) g μ)).tendsto q).comp hp_tendsto
  have hp_fst :
      Filter.Tendsto
        (fun i ↦ (WithLp.ofLp (p i)).1)
        l
        (𝓝 (WithLp.ofLp q).1) :=
    hp_ofLp.fst_nhds
  have hp_snd :
      Filter.Tendsto
        (fun i ↦ (WithLp.ofLp (p i)).2)
        l
        (𝓝 (WithLp.ofLp q).2) :=
    hp_ofLp.snd_nhds
  have hu_eq_eventually :
      ∀ᶠ i in l,
        (Quotient.mk
          (SquareIntegrableValueSection.aeSetoid
            (X := X) (E := E) (μ := μ)) (uRep i) :
          ValueL2Section (X := X) (E := E) μ) =
          (WithLp.ofLp (p i)).1 := by
    filter_upwards [hp_graph] with i hi
    dsimp [uRep]
    rw [dif_pos hi]
    exact (Classical.choose_spec (Classical.choose_spec hi)).1
  have hdu_eq_eventually :
      ∀ᶠ i in l,
        (Quotient.mk
          (SquareIntegrableManifoldDifferentialField.aeSetoid
            (I := I) (X := X) (E := E) (g := g) (μ := μ)) (duRep i) :
          ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ) =
          (WithLp.ofLp (p i)).2 := by
    filter_upwards [hp_graph] with i hi
    dsimp [duRep]
    rw [dif_pos hi]
    exact (Classical.choose_spec (Classical.choose_spec hi)).2.1
  have huLim_eq :
      (Quotient.mk
        (SquareIntegrableValueSection.aeSetoid
          (X := X) (E := E) (μ := μ)) uLim :
        ValueL2Section (X := X) (E := E) μ) =
        (WithLp.ofLp q).1 := by
    simp [uLim]
  have hduLim_eq :
      (Quotient.mk
        (SquareIntegrableManifoldDifferentialField.aeSetoid
          (I := I) (X := X) (E := E) (g := g) (μ := μ)) duLim :
        ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ) =
        (WithLp.ofLp q).2 := by
    simp [duLim]
  have hu_tendsto :
      Filter.Tendsto
        (fun i ↦
          (Quotient.mk
            (SquareIntegrableValueSection.aeSetoid
              (X := X) (E := E) (μ := μ)) (uRep i) :
            ValueL2Section (X := X) (E := E) μ))
        l
        (𝓝 ((WithLp.ofLp q).1 :
          ValueL2Section (X := X) (E := E) μ)) := by
    refine Filter.Tendsto.congr' ?_ hp_fst
    exact hu_eq_eventually.mono fun _ hi ↦ hi.symm
  have hdu_tendsto :
      Filter.Tendsto
        (fun i ↦
          (Quotient.mk
            (SquareIntegrableManifoldDifferentialField.aeSetoid
              (I := I) (X := X) (E := E) (g := g) (μ := μ)) (duRep i) :
            ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ))
        l
        (𝓝 ((WithLp.ofLp q).2 :
          ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ)) := by
    refine Filter.Tendsto.congr' ?_ hp_snd
    exact hdu_eq_eventually.mono fun _ hi ↦ hi.symm
  have hlim_weak :
      IsWeakDerivativeOnManifoldBundle
        (I := I) μ uLim.toFunction duLim.toField :=
    isWeakDerivativeOnManifoldBundle_of_tendsto_l2_sections
      (I := I) (X := X) (E := E) g μ _hμ
      hweak huLim_eq hduLim_eq hu_tendsto hdu_tendsto
  exact ⟨uLim, duLim, huLim_eq, hduLim_eq, hlim_weak⟩

/--
%%handwave
name:
  Intrinsic weak-derivative graph on a manifold is closed
statement:
  If the measure has smooth positive coordinate densities, then the
  weak-derivative graph is closed in the first-order \(L^2\) Hilbert product.
proof:
  The proof is the usual closedness of distributional derivatives.  From
  convergence in the two \(L^2\) factors, pass to the limit in every compactly
  supported coordinate test identity using Cauchy--Schwarz on compact chart
  supports and the local equivalence between the manifold measure and
  Lebesgue measure.  The limiting representatives therefore satisfy the same
  integration-by-parts identities.
-/
theorem weakDerivativeIntrinsicGraphOnManifoldWithValues_isClosed_of_smoothPositiveMeasure
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [IsManifold I 1 X] [IsIdentityManifoldModel H I]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology (Bundle.TotalSpace E (Bundle.Trivial X E))]
    [TopologicalSpace.PseudoMetrizableSpace (Bundle.TotalSpace E (Bundle.Trivial X E))]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := I) X E)]
    [TopologicalSpace.PseudoMetrizableSpace (ManifoldDifferentialTotalSpace (I := I) X E)]
    (g : SmoothRiemannianMetricOnManifold I X) (μ : Measure X)
    (_hμ : SmoothPositiveMeasureOnManifold (I := I) μ) :
    letI : NormedAddCommGroup (ValueL2Section (X := X) (E := E) μ) :=
      valueL2SectionNormedAddCommGroup (I := I) (X := X) (E := E) μ
    letI : NormedAddCommGroup
        (ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ) :=
      manifoldDifferentialL2SectionNormedAddCommGroup (I := I) (X := X) (E := E) g μ
    IsClosed
      {p : SobolevH1OnManifoldWithValuesIntrinsicAmbientModel
          (I := I) (X := X) (E := E) g μ |
        WeakDerivativeIntrinsicGraphOnManifoldWithValues g μ p} := by
  letI : NormedAddCommGroup (ValueL2Section (X := X) (E := E) μ) :=
    valueL2SectionNormedAddCommGroup (I := I) (X := X) (E := E) μ
  letI : NormedAddCommGroup
      (ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ) :=
    manifoldDifferentialL2SectionNormedAddCommGroup (I := I) (X := X) (E := E) g μ
  refine isClosed_iff_forall_filter.2 ?_
  intro q F hF_ne hF_graph hF_lim
  haveI : F.NeBot := hF_ne
  have hgraph_eventually :
      ∀ᶠ y in F, WeakDerivativeIntrinsicGraphOnManifoldWithValues g μ y :=
    hF_graph (by simp)
  have hid_tendsto :
      Filter.Tendsto
        (fun y : SobolevH1OnManifoldWithValuesIntrinsicAmbientModel
            (I := I) (X := X) (E := E) g μ ↦ y) F (𝓝 q) := by
    simpa using hF_lim
  exact
    weakDerivativeIntrinsicGraphOnManifoldWithValues_mem_of_tendsto
      (I := I) (X := X) (E := E) g μ _hμ
      hgraph_eventually hid_tendsto

/--
%%handwave
name:
  Intrinsic weak-derivative graph for the Riemannian volume is closed
statement:
  On a finite-dimensional smooth Riemannian manifold, the weak-derivative
  graph is closed in the first-order \(L^2\) Hilbert product formed using the
  Riemannian volume measure.
proof:
  The Riemannian volume has smooth strictly positive coordinate densities.
  Apply the closedness theorem for smooth positive measures.
-/
theorem weakDerivativeIntrinsicGraphOnManifoldWithValues_isClosed
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H] [OpensMeasurableSpace H]
    [Measure.IsAddHaarMeasure (MeasureTheory.volume : Measure H)]
    [IsLocallyFiniteMeasure (MeasureTheory.volume : Measure H)]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [SecondCountableTopology X] [T2Space X] [IsManifold (𝓘(ℝ, H)) 1 X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology (Bundle.TotalSpace E (Bundle.Trivial X E))]
    [TopologicalSpace.PseudoMetrizableSpace (Bundle.TotalSpace E (Bundle.Trivial X E))]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := 𝓘(ℝ, H)) X E)]
    [TopologicalSpace.PseudoMetrizableSpace
      (ManifoldDifferentialTotalSpace (I := 𝓘(ℝ, H)) X E)]
    (g : SmoothRiemannianMetricOnManifold (𝓘(ℝ, H)) X) :
    let μ := SmoothRiemannianMetricOnManifold.volume g
    letI : NormedAddCommGroup (ValueL2Section (X := X) (E := E) μ) :=
      valueL2SectionNormedAddCommGroup
        (I := 𝓘(ℝ, H)) (X := X) (E := E) μ
    letI : NormedAddCommGroup
        (ManifoldDifferentialL2Section
          (I := 𝓘(ℝ, H)) (X := X) (E := E) g μ) :=
      manifoldDifferentialL2SectionNormedAddCommGroup
        (I := 𝓘(ℝ, H)) (X := X) (E := E) g μ
    IsClosed
      {p : SobolevH1OnManifoldWithValuesIntrinsicAmbientModel
          (I := 𝓘(ℝ, H)) (X := X) (E := E) g μ |
        WeakDerivativeIntrinsicGraphOnManifoldWithValues g μ p} := by
  let μ := SmoothRiemannianMetricOnManifold.volume g
  have hμ : SmoothPositiveMeasureOnManifold (I := 𝓘(ℝ, H)) μ :=
    SmoothRiemannianMetricOnManifold.volume_smooth_positive g
  exact
    weakDerivativeIntrinsicGraphOnManifoldWithValues_isClosed_of_smoothPositiveMeasure
      (I := 𝓘(ℝ, H)) (X := X) (E := E) g μ hμ

/--
%%handwave
name:
  Intrinsic graph model for a smooth positive measure is Hilbert
statement:
  For maps from a finite-dimensional smooth Riemannian manifold into a
  complete real Hilbert space, the intrinsic weak-derivative graph formed
  with any smooth positive measure is a real Hilbert space with the graph
  inner product inherited from the first-order \(L^2\) product.
proof:
  The value and differential \(L^2\)-section spaces are Hilbert spaces, hence
  so is their square-sum product.  The weak-derivative graph is a real linear
  subspace by linearity of the distributional identity, and it is closed by
  the closed-graph theorem for weak derivatives with smooth positive measure.
  A closed subspace of a Hilbert space is Hilbert.
-/
theorem sobolevH1OnManifoldWithValuesIntrinsicGraph_admits_hilbert_structure_of_smoothPositiveMeasure
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [IsManifold I 1 X] [IsIdentityManifoldModel H I]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology (Bundle.TotalSpace E (Bundle.Trivial X E))]
    [TopologicalSpace.PseudoMetrizableSpace (Bundle.TotalSpace E (Bundle.Trivial X E))]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := I) X E)]
    [TopologicalSpace.PseudoMetrizableSpace
      (ManifoldDifferentialTotalSpace (I := I) X E)]
    (g : SmoothRiemannianMetricOnManifold I X) (μ : Measure X)
    (hμ : SmoothPositiveMeasureOnManifold (I := I) μ) :
    AdmitsRealHilbertStructure
      (SobolevH1OnManifoldWithValuesIntrinsicGraphHilbertModel
        (I := I) (X := X) (E := E) g μ) := by
  classical
  let metric :=
    manifoldDifferentialHilbertSchmidtContinuousRiemannianMetric
      (I := I) (X := X) (E := E) g
  letI : Bundle.RiemannianBundle
      (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E)) :=
    ⟨metric.toRiemannianMetric⟩
  letI (x : X) :
      NormedAddCommGroup
        (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E) x) :=
    manifoldDifferentialHilbertSchmidtNormedAddCommGroup
      (I := I) (X := X) (E := E) metric x
  letI (x : X) :
      InnerProductSpace ℝ
        (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E) x) :=
    manifoldDifferentialHilbertSchmidtInnerProductSpace
      (I := I) (X := X) (E := E) metric x
  let Vd := ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E)
  let diffFiberComplete :
      ∀ x : X,
        CompleteSpace (Vd x) :=
    fun _ ↦ by
      change CompleteSpace (H →L[ℝ] E)
      infer_instance
  let diffFiberCompletePseudo :
      ∀ x : X, @CompleteSpace (Vd x) PseudoMetricSpace.toUniformSpace :=
    fun x ↦ by
      let U0 : UniformSpace (Vd x) :=
        ContinuousLinearMap.uniformSpace
          (𝕜₁ := ℝ) (𝕜₂ := ℝ) (σ := RingHom.id ℝ)
          (E := TangentSpace I x) (F := E)
      have hU : PseudoMetricSpace.toUniformSpace = U0 := by
        apply UniformSpace.ext
        rw [@uniformity_eq_comap_nhds_zero (Vd x)
          PseudoMetricSpace.toUniformSpace inferInstance inferInstance]
        letI : UniformSpace (Vd x) := U0
        rw [@uniformity_eq_comap_nhds_zero (Vd x)
          U0 inferInstance inferInstance]
      change @CompleteSpace (Vd x) PseudoMetricSpace.toUniformSpace
      rw [hU]
      change CompleteSpace (H →L[ℝ] E)
      infer_instance
  haveI :
      ∀ x : X,
        CompleteSpace (Vd x) :=
    diffFiberComplete
  let valueG := trivialHilbertBundleGeometry X E
  let diffG := manifoldDifferentialHilbertBundleGeometry (I := I) (X := X) (E := E) g
  letI : NormedAddCommGroup (ValueL2Section (X := X) (E := E) μ) :=
    valueL2SectionNormedAddCommGroup (I := I) (X := X) (E := E) μ
  letI : InnerProductSpace ℝ (ValueL2Section (X := X) (E := E) μ) :=
    l2HilbertBundleInnerProductSpace (I := I) (G := valueG) (μ := μ)
      (fun _ _ _ ↦ rfl)
  letI : CompleteSpace (ValueL2Section (X := X) (E := E) μ) :=
    l2HilbertBundle_completeSpace_core (I := I) (G := valueG) (μ := μ)
      (fun _ _ _ ↦ rfl)
  letI :
      NormedAddCommGroup
        (ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ) :=
    manifoldDifferentialL2SectionNormedAddCommGroup
      (I := I) (X := X) (E := E) g μ
  letI :
      InnerProductSpace ℝ
        (ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ) :=
    l2HilbertBundleInnerProductSpace (I := I) (G := diffG) (μ := μ)
      (fun _ _ _ ↦ rfl)
  letI : CompleteSpace
      (ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ) :=
    by
      exact @l2HilbertBundle_completeSpace_core
        H X (H →L[ℝ] E)
        inferInstance inferInstance
        I inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
        inferInstance inferInstance inferInstance
        Vd inferInstance inferInstance inferInstance
        (fun x ↦ manifoldDifferentialHilbertSchmidtNormedAddCommGroup
          (I := I) (X := X) (E := E) metric x)
        (fun x ↦ manifoldDifferentialHilbertSchmidtInnerProductSpace
          (I := I) (X := X) (E := E) metric x)
        diffFiberCompletePseudo
        inferInstance inferInstance inferInstance
        diffG μ (by intro x A B; rfl)
  let Ambient :=
    SobolevH1OnManifoldWithValuesIntrinsicAmbientModel
      (I := I) (X := X) (E := E) g μ
  let G : Submodule ℝ Ambient := {
    carrier := {p : Ambient | WeakDerivativeIntrinsicGraphOnManifoldWithValues g μ p}
    zero_mem' := by
      let u0 : SquareIntegrableValueSection (X := X) (E := E) μ :=
        ⟨0, hilbertBundleSectionMemL2_zero
          (I := I) (G := valueG) (fun _ _ _ ↦ rfl) μ⟩
      let du0 :
          SquareIntegrableManifoldDifferentialField
            (I := I) (X := X) (E := E) g μ :=
        ⟨0, hilbertBundleSectionMemL2_zero
          (I := I) (G := diffG) (fun _ _ _ ↦ rfl) μ⟩
      refine ⟨u0, du0, ?_, ?_, ?_⟩
      · have h :=
          l2HilbertBundle_mk_zero
            (I := I) (G := valueG) (μ := μ) (fun _ _ _ ↦ rfl)
        simpa [u0, valueG, Ambient] using h
      · have h :=
          l2HilbertBundle_mk_zero
            (I := I) (G := diffG) (μ := μ) (fun _ _ _ ↦ rfl)
        simpa [du0, diffG, Ambient] using h
      · simpa [u0, du0, SquareIntegrableValueSection.toFunction,
          SquareIntegrableManifoldDifferentialField.toField] using
          (isWeakDerivativeOnManifoldBundle_zero (I := I) (X := X) (E := E) μ)
    add_mem' := by
      intro p q hp hq
      rcases hp with ⟨u₁, du₁, hu₁, hdu₁, hweak₁⟩
      rcases hq with ⟨u₂, du₂, hu₂, hdu₂, hweak₂⟩
      let uAdd : SquareIntegrableValueSection (X := X) (E := E) μ :=
        squareIntegrableHilbertBundleSectionAdd
          (I := I) (G := valueG) (fun _ _ _ ↦ rfl) μ u₁ u₂
      let duAdd :
          SquareIntegrableManifoldDifferentialField
            (I := I) (X := X) (E := E) g μ :=
        squareIntegrableHilbertBundleSectionAdd
          (I := I) (G := diffG) (fun _ _ _ ↦ rfl) μ du₁ du₂
      refine ⟨uAdd, duAdd, ?_, ?_, ?_⟩
      · have h :=
          l2HilbertBundle_mk_add
            (I := I) (G := valueG) (μ := μ) (fun _ _ _ ↦ rfl) u₁ u₂
        calc
          (Quotient.mk
              (SquareIntegrableValueSection.aeSetoid
                (X := X) (E := E) (μ := μ)) uAdd :
              ValueL2Section (X := X) (E := E) μ) =
              (Quotient.mk
                (SquareIntegrableValueSection.aeSetoid
                  (X := X) (E := E) (μ := μ)) u₁ :
                ValueL2Section (X := X) (E := E) μ) +
                Quotient.mk
                  (SquareIntegrableValueSection.aeSetoid
                    (X := X) (E := E) (μ := μ)) u₂ := by
            simpa [uAdd, valueG] using h
          _ = (WithLp.ofLp (p + q)).1 := by
            rw [hu₁, hu₂]
            simp [Ambient]
      · have h :=
          l2HilbertBundle_mk_add
            (I := I) (G := diffG) (μ := μ) (fun _ _ _ ↦ rfl) du₁ du₂
        calc
          (Quotient.mk
              (SquareIntegrableManifoldDifferentialField.aeSetoid
                (I := I) (X := X) (E := E) (g := g) (μ := μ)) duAdd :
              ManifoldDifferentialL2Section
                (I := I) (X := X) (E := E) g μ) =
              (Quotient.mk
                (SquareIntegrableManifoldDifferentialField.aeSetoid
                  (I := I) (X := X) (E := E) (g := g) (μ := μ)) du₁ :
                ManifoldDifferentialL2Section
                  (I := I) (X := X) (E := E) g μ) +
                Quotient.mk
                  (SquareIntegrableManifoldDifferentialField.aeSetoid
                    (I := I) (X := X) (E := E) (g := g) (μ := μ)) du₂ := by
            simpa [duAdd, diffG] using h
          _ = (WithLp.ofLp (p + q)).2 := by
            rw [hdu₁, hdu₂]
            simp [Ambient]
      · simpa [uAdd, duAdd, SquareIntegrableValueSection.toFunction,
          SquareIntegrableManifoldDifferentialField.toField,
          squareIntegrableHilbertBundleSectionAdd] using hweak₁.add hweak₂
    smul_mem' := by
      intro c p hp
      rcases hp with ⟨u, du, hu, hdu, hweak⟩
      let uSmul : SquareIntegrableValueSection (X := X) (E := E) μ :=
        squareIntegrableHilbertBundleSectionSmul
          (I := I) (G := valueG) (fun _ _ _ ↦ rfl) μ c u
      let duSmul :
          SquareIntegrableManifoldDifferentialField
            (I := I) (X := X) (E := E) g μ :=
        squareIntegrableHilbertBundleSectionSmul
          (I := I) (G := diffG) (fun _ _ _ ↦ rfl) μ c du
      refine ⟨uSmul, duSmul, ?_, ?_, ?_⟩
      · have h :=
          l2HilbertBundle_mk_smul
            (I := I) (G := valueG) (μ := μ) (fun _ _ _ ↦ rfl) c u
        calc
          (Quotient.mk
              (SquareIntegrableValueSection.aeSetoid
                (X := X) (E := E) (μ := μ)) uSmul :
              ValueL2Section (X := X) (E := E) μ) =
              c •
                (Quotient.mk
                  (SquareIntegrableValueSection.aeSetoid
                    (X := X) (E := E) (μ := μ)) u :
                  ValueL2Section (X := X) (E := E) μ) := by
            simpa [uSmul, valueG] using h
          _ = (WithLp.ofLp (c • p)).1 := by
            rw [hu]
            simp [Ambient]
      · have h :=
          l2HilbertBundle_mk_smul
            (I := I) (G := diffG) (μ := μ) (fun _ _ _ ↦ rfl) c du
        calc
          (Quotient.mk
              (SquareIntegrableManifoldDifferentialField.aeSetoid
                (I := I) (X := X) (E := E) (g := g) (μ := μ)) duSmul :
              ManifoldDifferentialL2Section
                (I := I) (X := X) (E := E) g μ) =
              c •
                (Quotient.mk
                  (SquareIntegrableManifoldDifferentialField.aeSetoid
                    (I := I) (X := X) (E := E) (g := g) (μ := μ)) du :
                  ManifoldDifferentialL2Section
                    (I := I) (X := X) (E := E) g μ) := by
            simpa [duSmul, diffG] using h
          _ = (WithLp.ofLp (c • p)).2 := by
            rw [hdu]
            simp [Ambient]
      · simpa [uSmul, duSmul, SquareIntegrableValueSection.toFunction,
          SquareIntegrableManifoldDifferentialField.toField,
          squareIntegrableHilbertBundleSectionSmul] using hweak.const_smul c
  }
  have hG_closed : IsClosed (G : Set Ambient) := by
    simpa [G, Ambient] using
      weakDerivativeIntrinsicGraphOnManifoldWithValues_isClosed_of_smoothPositiveMeasure
        (I := I) (X := X) (E := E) g μ hμ
  have hG_complete : CompleteSpace G := by
    change CompleteSpace (G : Set Ambient)
    exact hG_closed.isComplete.completeSpace_coe
  haveI : CompleteSpace G := hG_complete
  change AdmitsRealHilbertStructure G
  refine ⟨inferInstance, inferInstance, hG_complete, ?_⟩
  exact ⟨@HilbertSpace.mk ℝ G _ _ _ hG_complete⟩

/--
%%handwave
name:
  Intrinsic graph model on a Riemannian manifold is Hilbert
statement:
  For maps from a finite-dimensional smooth Riemannian manifold into a
  complete real Hilbert space, the intrinsic weak-derivative graph formed
  with the Riemannian volume measure is a real Hilbert space.
proof:
  The Riemannian volume has smooth positive coordinate densities.  Apply the
  Hilbert-space theorem for the intrinsic graph with a smooth positive
  measure.
-/
theorem sobolevH1OnRiemannianManifoldWithValuesIntrinsicGraph_admits_hilbert_structure
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H] [OpensMeasurableSpace H]
    [Measure.IsAddHaarMeasure (MeasureTheory.volume : Measure H)]
    [IsLocallyFiniteMeasure (MeasureTheory.volume : Measure H)]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [SecondCountableTopology X] [T2Space X] [IsManifold (𝓘(ℝ, H)) 1 X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology (Bundle.TotalSpace E (Bundle.Trivial X E))]
    [TopologicalSpace.PseudoMetrizableSpace (Bundle.TotalSpace E (Bundle.Trivial X E))]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := 𝓘(ℝ, H)) X E)]
    [TopologicalSpace.PseudoMetrizableSpace
      (ManifoldDifferentialTotalSpace (I := 𝓘(ℝ, H)) X E)]
    (g : SmoothRiemannianMetricOnManifold (𝓘(ℝ, H)) X) :
    let μ := SmoothRiemannianMetricOnManifold.volume g
    AdmitsRealHilbertStructure
      (SobolevH1OnManifoldWithValuesIntrinsicGraphHilbertModel
        (I := 𝓘(ℝ, H)) (X := X) (E := E) g μ) := by
  let μ := SmoothRiemannianMetricOnManifold.volume g
  have hμ : SmoothPositiveMeasureOnManifold (I := 𝓘(ℝ, H)) μ :=
    SmoothRiemannianMetricOnManifold.volume_smooth_positive g
  simpa [μ] using
    sobolevH1OnManifoldWithValuesIntrinsicGraph_admits_hilbert_structure_of_smoothPositiveMeasure
      (I := 𝓘(ℝ, H)) (X := X) (E := E) g μ hμ

/--
%%handwave
name:
  Coordinate Hilbert-Schmidt differential fiber
statement:
  For Hilbert-valued surface maps, a first derivative in a coordinate chart is
  recorded by its two real coordinate components, equipped with the square-sum
  Hilbert norm.
-/
abbrev SurfaceDifferentialCoordinateHilbertFiber (E : Type)
    [NormedAddCommGroup E] : Type :=
  WithLp 2 (E × E)

namespace SurfaceDifferentialCoordinateHilbertFiber

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/--
%%handwave
name:
  Coordinate differential as a real-linear map
statement:
  A pair of coordinate derivative components determines the corresponding
  real-linear map on the coordinate tangent plane.
-/
noncomputable def toLinearMap
    (D : SurfaceDifferentialCoordinateHilbertFiber E) : ℂ →L[ℝ] E :=
  Complex.reCLM.smulRight (WithLp.ofLp D).1 +
    Complex.imCLM.smulRight (WithLp.ofLp D).2

/--
%%handwave
name:
  Coordinate differential as a continuous linear construction
statement:
  Forming the real-linear coordinate differential from its two coordinate
  components depends continuously and linearly on the component pair.
-/
noncomputable def toLinearMapCLM :
    SurfaceDifferentialCoordinateHilbertFiber E →L[ℝ] (ℂ →L[ℝ] E) :=
  (ContinuousLinearMap.smulRightL ℝ ℂ E Complex.reCLM).comp
      (WithLp.fstL (p := (2 : ℝ≥0∞)) ℝ E E) +
    (ContinuousLinearMap.smulRightL ℝ ℂ E Complex.imCLM).comp
      (WithLp.sndL (p := (2 : ℝ≥0∞)) ℝ E E)

/--
%%handwave
name:
  Evaluation of the continuous map from coordinate pairs to linear maps
statement:
  The continuous linear realization of a coordinate differential pair \(Din E\times E\) has the same value as its underlying real-linear map.
proof:
  The continuous linear map is defined by packaging that underlying pointwise construction.
-/
@[simp]
theorem toLinearMapCLM_apply
    (D : SurfaceDifferentialCoordinateHilbertFiber E) :
    toLinearMapCLM D = toLinearMap D := by
  ext z
  simp [toLinearMapCLM, toLinearMap]

/--
%%handwave
name:
  Scalar projection of a coordinate differential
statement:
  Applying a continuous linear functional on the target to a vector-valued
  coordinate differential gives a scalar coordinate cotangent field, and this
  operation is continuous and linear in the differential.
-/
noncomputable def dualProjectionCLM (Λ : E →L[ℝ] ℝ) :
    SurfaceDifferentialCoordinateHilbertFiber E →L[ℝ] (ℂ →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ ℂ E ℝ Λ).comp toLinearMapCLM

/--
%%handwave
name:
  Dual projection of a coordinate differential
statement:
  For a functional \(\Lambda:E\to\mathbb R\), projecting a coordinate differential (D) gives the composite \(\Lambda\circ D\).
proof:
  Expand the continuous linear projection: it applies \(\Lambda\) to both coordinate components, which is precisely composition.
-/
@[simp]
theorem dualProjectionCLM_apply
    (Λ : E →L[ℝ] ℝ) (D : SurfaceDifferentialCoordinateHilbertFiber E) :
    dualProjectionCLM Λ D = Λ.comp (toLinearMap D) := by
  simp [dualProjectionCLM]

/--
%%handwave
name:
  Linear map represented by two coordinate components
statement:
  If \(D=(D_1,D_2)\), then for \(z\in\mathbb C\),
  \[
    D(z)=\operatorname{Re}(z)D_1+\operatorname{Im}(z)D_2.
  \]
proof:
  Expand the real basis decomposition (z=\operatorname{Re}(z)\cdot1+\operatorname{Im}(z)\cdot i).
-/
@[simp]
theorem toLinearMap_apply
    (D : SurfaceDifferentialCoordinateHilbertFiber E) (z : ℂ) :
    toLinearMap D z =
      z.re • (WithLp.ofLp D).1 + z.im • (WithLp.ofLp D).2 := by
  simp [toLinearMap]

/--
%%handwave
name:
  The zero coordinate pair represents the zero differential
statement:
  The coordinate pair \((0,0)\) represents the zero real-linear map \(\mathbb C\to E\).
proof:
  Evaluate on an arbitrary complex vector and simplify both coordinate terms.
-/
@[simp]
theorem toLinearMap_zero :
    toLinearMap (0 : SurfaceDifferentialCoordinateHilbertFiber E) = 0 := by
  ext z
  simp [toLinearMap]

/--
%%handwave
name:
  Addition of coordinate differential pairs
statement:
  The linear map represented by (D+F) is the sum of the maps represented by (D) and (F).
proof:
  Evaluate at (z), expand both coordinate components, and distribute addition.
-/
@[simp]
theorem toLinearMap_add
    (D F : SurfaceDifferentialCoordinateHilbertFiber E) :
    toLinearMap (D + F) = toLinearMap D + toLinearMap F := by
  ext z
  simp [toLinearMap, add_assoc, add_left_comm]

/--
%%handwave
name:
  Scalar multiplication of coordinate differential pairs
statement:
  The map represented by (cD) is (c) times the map represented by (D).
proof:
  Evaluate at (z) and distribute the scalar through the two coordinate components.
-/
@[simp]
theorem toLinearMap_smul
    (c : ℝ) (D : SurfaceDifferentialCoordinateHilbertFiber E) :
    toLinearMap (c • D) = c • toLinearMap D := by
  ext z
  simp [toLinearMap, smul_add, smul_smul, mul_comm]

/--
%%handwave
name:
  Coordinate components of a real-linear differential
statement:
  A real-linear map on the coordinate tangent plane determines its two
  coordinate derivative components by evaluation on the coordinate axes.
-/
noncomputable def ofLinearMap (A : ℂ →L[ℝ] E) :
    SurfaceDifferentialCoordinateHilbertFiber E :=
  WithLp.toLp 2 (A 1, A Complex.I)

end SurfaceDifferentialCoordinateHilbertFiber

/--
%%handwave
name:
  Coordinate differential fibers are Hilbert spaces
statement:
  If the target is a real Hilbert space, then the coordinate derivative fiber
  with square-sum norm is a real Hilbert space.
proof:
  Products of real Hilbert spaces are real Hilbert spaces, and the square-sum
  norm is the standard product Hilbert norm.
-/
theorem surfaceDifferentialCoordinateHilbertFiber_admits_hilbert_structure
    (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] :
    AdmitsRealHilbertStructure (SurfaceDifferentialCoordinateHilbertFiber E) := by
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  exact ⟨HilbertSpace.mk⟩

/--
%%handwave
name:
  \(L^2\) coordinate differential fields form a Hilbert space
statement:
  Square-integrable coordinate differential fields with values in a real
  Hilbert space form a real Hilbert space.
proof:
  This is the Hilbert-valued \(L^2\) construction applied to the coordinate
  derivative fiber.
-/
theorem surfaceDifferentialCoordinateFieldL2_admits_hilbert_structure
    {X E : Type} [MeasurableSpace X] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (μ : Measure X) :
    AdmitsRealHilbertStructure
      (Lp (SurfaceDifferentialCoordinateHilbertFiber E) 2 μ) := by
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  exact ⟨HilbertSpace.mk⟩

/--
%%handwave
name:
  \(L^2\) cotangent fields form a Hilbert space
statement:
  The space of square-integrable cotangent fields on a measured surface is a
  real Hilbert space.
proof:
  This is the \(L^2\) Hilbert-space structure with target the Hilbert space of
  continuous real-linear functionals on the real Hilbert space \(\mathbb C\).
-/
theorem surfaceCotangentFieldL2_admits_hilbert_structure
    {X : Type} [MeasurableSpace X] (μ : Measure X) :
    AdmitsRealHilbertStructure (Lp (ℂ →L[ℝ] ℝ) 2 μ) := by
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  exact ⟨HilbertSpace.mk⟩

/--
%%handwave
name:
  Ambient first-order \(L^2\) Hilbert model
statement:
  The ambient first-order \(L^2\) Hilbert model is the \(L^2\)-class product
  of functions and cotangent fields, equipped with the square-sum
  norm.
-/
abbrev SobolevH1OnSurfaceAmbientHilbertModel {X : Type} [MeasurableSpace X]
    (μ : Measure X) : Type _ :=
  WithLp 2 (Lp ℝ 2 μ × Lp (ℂ →L[ℝ] ℝ) 2 μ)

/--
%%handwave
name:
  Hilbert-valued ambient first-order \(L^2\) model
statement:
  For maps into a real Hilbert space, the ambient first-order \(L^2\) model is
  the square-sum product of the \(L^2\) space of values and the \(L^2\) space
  of coordinate differential components.
-/
abbrev SobolevH1OnSurfaceWithValuesAmbientHilbertModel
    {X E : Type} [MeasurableSpace X] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (μ : Measure X) : Type _ :=
  WithLp 2
    (Lp E 2 μ × Lp (SurfaceDifferentialCoordinateHilbertFiber E) 2 μ)

/--
%%handwave
name:
  \(L^2\) class has an \(L^2\) weak gradient
statement:
  An \(L^2\)-class function has an \(L^2\) weak gradient if it admits a
  square-integrable cotangent field satisfying the weak-gradient
  integration-by-parts identity.
-/
def HasWeakGradientInL2OnSurface {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (u : Lp ℝ 2 μ) : Prop :=
  ∃ u₀ : X → ℝ, ∃ du : X → ℂ →L[ℝ] ℝ,
    ∃ _hu_mem : MemLp u₀ 2 μ, ∃ _hdu_mem : MemLp du 2 μ,
      (fun x ↦ u x) =ᵐ[μ] u₀ ∧ IsWeakGradientOnSurface μ u₀ du

/--
%%handwave
name:
  Dual-tested vector-valued weak derivative
statement:
  A vector-valued coordinate differential is a weak derivative if every
  continuous linear functional on the target turns it into the scalar weak
  gradient of the corresponding scalar projection of the map.
-/
def IsWeakDerivativeOnSurfaceWithValuesByDual {X E : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X) (u : X → E)
    (du : X → SurfaceDifferentialCoordinateHilbertFiber E) : Prop :=
  ∀ Λ : E →L[ℝ] ℝ,
    IsWeakGradientOnSurface μ (fun x ↦ Λ (u x))
      (fun x ↦ SurfaceDifferentialCoordinateHilbertFiber.dualProjectionCLM Λ (du x))

/--
%%handwave
name:
  \(L^2\) class has an \(L^2\) vector-valued weak derivative
statement:
  A Banach-valued \(L^2\)-class has an \(L^2\) weak derivative if it admits a
  square-integrable representative and square-integrable coordinate
  differential components whose scalar projections satisfy the scalar weak
  gradient identities for every continuous linear functional on the target.
-/
def HasWeakDerivativeInL2OnSurfaceWithValues {X E : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [IsManifold SurfaceRealModel 1 X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X) (u : Lp E 2 μ) : Prop :=
  ∃ u₀ : X → E,
  ∃ du : X → SurfaceDifferentialCoordinateHilbertFiber E,
    ∃ _hu_mem : MemLp u₀ 2 μ, ∃ _hdu_mem : MemLp du 2 μ,
      (fun x ↦ u x) =ᵐ[μ] u₀ ∧
        IsWeakDerivativeOnSurfaceWithValuesByDual μ u₀ du

/--
%%handwave
name:
  Intrinsic dual-tested vector-valued weak derivative
statement:
  A section of \(T^\ast X\otimes E\) is the weak derivative of a map
  \(u:X\to E\) if every continuous linear functional on \(E\) turns it into
  the scalar weak gradient of the corresponding scalar projection of \(u\).
-/
def IsWeakDerivativeOnSurfaceWithValuesIntrinsicByDual {X E : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [IsManifold SurfaceRealModel 1 X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X) (u : X → E)
    (du : SurfaceDifferentialField X E) : Prop :=
  ∀ Λ : E →L[ℝ] ℝ,
    IsWeakGradientOnSurfaceBundle μ (fun x ↦ Λ (u x))
      (fun x ↦ Λ.comp (du x))

/--
%%handwave
name:
  Intrinsic \(L^2\) class has a vector-valued weak derivative
statement:
  A Hilbert-valued \(L^2\)-class has an intrinsic \(L^2\) weak derivative
  when it has an \(L^2\) representative and a square-integrable section of
  \(T^\ast X\otimes E\) satisfying the dual-tested weak-derivative identities.
-/
def HasIntrinsicWeakDerivativeInL2OnSurfaceWithValues {X E : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [IsManifold SurfaceRealModel 1 X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : SmoothRiemannianMetricOnSurface X) (μ : Measure X)
    (u : SurfaceValueL2Section (X := X) (E := E) μ) : Prop :=
  ∃ u₀ : SquareIntegrableSurfaceValueSection (X := X) (E := E) μ,
  ∃ du : SquareIntegrableSurfaceDifferentialField (X := X) (E := E) g μ,
    Quotient.mk
        (SquareIntegrableSurfaceValueSection.aeSetoid
          (X := X) (E := E) (μ := μ)) u₀ = u ∧
      IsWeakDerivativeOnSurfaceWithValuesIntrinsicByDual μ u₀.toFunction du.toField

/--
%%handwave
name:
  Intrinsic Hilbert-valued first-order \(L^2\) model
statement:
  The intrinsic first-order \(L^2\) model is the square-sum product of
  Hilbert-valued \(L^2\) maps and \(L^2\)-sections of the differential bundle
  \(T^\ast X\otimes E\).
-/
abbrev SobolevH1OnSurfaceWithValuesIntrinsicAmbientModel {X E : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [IsManifold SurfaceRealModel 1 X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : SmoothRiemannianMetricOnSurface X) (μ : Measure X) : Type _ :=
  WithLp 2
    (SurfaceValueL2Section (X := X) (E := E) μ ×
      SurfaceDifferentialL2Section (X := X) (E := E) g μ)

/--
%%handwave
name:
  Intrinsic Hilbert-valued weak-derivative graph
statement:
  The intrinsic weak-derivative graph consists of an \(L^2\)-class map and an
  \(L^2\)-class section of \(T^\ast X\otimes E\) that admit representatives
  satisfying the chartwise vector-valued weak-derivative identities.
-/
def WeakDerivativeIntrinsicGraphOnSurfaceWithValues {X E : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [IsManifold SurfaceRealModel 1 X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : SmoothRiemannianMetricOnSurface X) (μ : Measure X)
    (p : SobolevH1OnSurfaceWithValuesIntrinsicAmbientModel
      (X := X) (E := E) g μ) : Prop :=
  WeakDerivativeIntrinsicGraphOnManifoldWithValues
    (I := SurfaceRealModel) (X := X) (E := E) g.toManifoldMetric μ p

/--
%%handwave
name:
  Intrinsic graph Hilbert model
statement:
  The intrinsic graph model of \(W^{1,2}(X;E)\) is the weak-derivative graph
  inside the product of \(L^2(X;E)\) and \(L^2(T^\ast X\otimes E)\).
-/
def SobolevH1OnSurfaceWithValuesIntrinsicGraphHilbertModel {X E : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [IsManifold SurfaceRealModel 1 X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : SmoothRiemannianMetricOnSurface X) (μ : Measure X) : Type _ :=
  {p : SobolevH1OnSurfaceWithValuesIntrinsicAmbientModel
      (X := X) (E := E) g μ //
    WeakDerivativeIntrinsicGraphOnSurfaceWithValues g μ p}

/--
%%handwave
name:
  Intrinsic separated Hilbert-valued \(W^{1,2}\) model
statement:
  The intrinsic separated Sobolev model consists of Hilbert-valued
  \(L^2\)-classes which admit an intrinsic \(L^2\) weak derivative.
-/
def SobolevH1OnSurfaceWithValuesIntrinsicHilbertModel {X E : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [IsManifold SurfaceRealModel 1 X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : SmoothRiemannianMetricOnSurface X) (μ : Measure X) : Type _ :=
  {u : SurfaceValueL2Section (X := X) (E := E) μ //
    HasIntrinsicWeakDerivativeInL2OnSurfaceWithValues g μ u}

/--
%%handwave
name:
  Intrinsic \(L^2\) differential sections form a Hilbert space
statement:
  For a smooth Riemannian surface and a real Hilbert target, the
  \(L^2\)-sections of \(T^\ast X\otimes E\), with the metric
  Hilbert-Schmidt inner product, form a real Hilbert space.
proof:
  This is the standard Hilbert-space theorem for square-integrable sections
  of a finite-rank Hilbert bundle tensored with a fixed Hilbert space.
-/
theorem surfaceDifferentialL2Sections_admit_hilbert_structure
    {X E : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X]
    [IsManifold SurfaceRealModel ∞ X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X E)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X E)]
    (g : SmoothRiemannianMetricOnSurface X) (μ : Measure X) :
    AdmitsRealHilbertStructure
      (SurfaceDifferentialL2Section (X := X) (E := E) g μ) := by
  exact manifoldDifferentialL2Sections_admit_hilbert_structure
    (I := SurfaceRealModel) (X := X) (E := E) g.toManifoldMetric μ

/-- Sum of square-integrable surface differential representatives. -/
noncomputable def squareIntegrableSurfaceDifferentialFieldAdd
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    (g : SmoothRiemannianMetricOnSurface X) (μ : Measure X)
    (du dv : SquareIntegrableSurfaceDifferentialField
      (X := X) (E := ℝ) g μ) :
    SquareIntegrableSurfaceDifferentialField (X := X) (E := ℝ) g μ := by
  let metric :=
    manifoldDifferentialHilbertSchmidtContinuousRiemannianMetric
      (I := SurfaceRealModel) (X := X) (E := ℝ) g.toManifoldMetric
  letI : Bundle.RiemannianBundle
      (ManifoldDifferentialBundleFiber
        (I := SurfaceRealModel) (X := X) (E := ℝ)) :=
    ⟨metric.toRiemannianMetric⟩
  letI (x : X) :
      NormedAddCommGroup
        (ManifoldDifferentialBundleFiber
          (I := SurfaceRealModel) (X := X) (E := ℝ) x) :=
    manifoldDifferentialHilbertSchmidtNormedAddCommGroup
      (I := SurfaceRealModel) (X := X) (E := ℝ) metric x
  letI (x : X) :
      InnerProductSpace ℝ
        (ManifoldDifferentialBundleFiber
          (I := SurfaceRealModel) (X := X) (E := ℝ) x) :=
    manifoldDifferentialHilbertSchmidtInnerProductSpace
      (I := SurfaceRealModel) (X := X) (E := ℝ) metric x
  exact
    squareIntegrableHilbertBundleSectionAdd
      (I := SurfaceRealModel)
      (G := manifoldDifferentialHilbertBundleGeometry
        (I := SurfaceRealModel) (X := X) (E := ℝ) g.toManifoldMetric)
      (fun _ _ _ ↦ rfl) μ du dv

/-- Scalar multiple of a square-integrable surface differential representative. -/
noncomputable def squareIntegrableSurfaceDifferentialFieldSmul
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    (g : SmoothRiemannianMetricOnSurface X) (μ : Measure X) (c : ℝ)
    (du : SquareIntegrableSurfaceDifferentialField
      (X := X) (E := ℝ) g μ) :
    SquareIntegrableSurfaceDifferentialField (X := X) (E := ℝ) g μ := by
  let metric :=
    manifoldDifferentialHilbertSchmidtContinuousRiemannianMetric
      (I := SurfaceRealModel) (X := X) (E := ℝ) g.toManifoldMetric
  letI : Bundle.RiemannianBundle
      (ManifoldDifferentialBundleFiber
        (I := SurfaceRealModel) (X := X) (E := ℝ)) :=
    ⟨metric.toRiemannianMetric⟩
  letI (x : X) :
      NormedAddCommGroup
        (ManifoldDifferentialBundleFiber
          (I := SurfaceRealModel) (X := X) (E := ℝ) x) :=
    manifoldDifferentialHilbertSchmidtNormedAddCommGroup
      (I := SurfaceRealModel) (X := X) (E := ℝ) metric x
  letI (x : X) :
      InnerProductSpace ℝ
        (ManifoldDifferentialBundleFiber
          (I := SurfaceRealModel) (X := X) (E := ℝ) x) :=
    manifoldDifferentialHilbertSchmidtInnerProductSpace
      (I := SurfaceRealModel) (X := X) (E := ℝ) metric x
  exact
    squareIntegrableHilbertBundleSectionSmul
      (I := SurfaceRealModel)
      (G := manifoldDifferentialHilbertBundleGeometry
        (I := SurfaceRealModel) (X := X) (E := ℝ) g.toManifoldMetric)
      (fun _ _ _ ↦ rfl) μ c du

/--
%%handwave
name:
  Intrinsic first-order \(L^2\) model is Hilbert
statement:
  The intrinsic first-order square-sum product \(L^2(X;E)\times
  L^2(T^\ast X\otimes E)\) is a real Hilbert space.
proof:
  Both factors are Hilbert spaces, and products of Hilbert spaces are Hilbert
  spaces.
-/
theorem surfaceH1WithValuesIntrinsicAmbientModel_admits_hilbert_structure
    {X E : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X]
    [IsManifold SurfaceRealModel ∞ X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology (Bundle.TotalSpace E (Bundle.Trivial X E))]
    [TopologicalSpace.PseudoMetrizableSpace (Bundle.TotalSpace E (Bundle.Trivial X E))]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X E)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X E)]
    (g : SmoothRiemannianMetricOnSurface X) (μ : Measure X) :
    AdmitsRealHilbertStructure
      (SobolevH1OnSurfaceWithValuesIntrinsicAmbientModel
        (X := X) (E := E) g μ) := by
  rcases surfaceValueL2Sections_admit_hilbert_structure
      (X := X) (E := E) μ with
    ⟨valueNormed, valueInner, valueComplete, _⟩
  rcases surfaceDifferentialL2Sections_admit_hilbert_structure
      (X := X) (E := E) g μ with
    ⟨diffNormed, diffInner, diffComplete, _⟩
  letI : NormedAddCommGroup (SurfaceValueL2Section (X := X) (E := E) μ) := valueNormed
  letI : InnerProductSpace ℝ (SurfaceValueL2Section (X := X) (E := E) μ) := valueInner
  letI : CompleteSpace (SurfaceValueL2Section (X := X) (E := E) μ) := valueComplete
  letI :
      NormedAddCommGroup (SurfaceDifferentialL2Section (X := X) (E := E) g μ) :=
    diffNormed
  letI :
      InnerProductSpace ℝ (SurfaceDifferentialL2Section (X := X) (E := E) g μ) :=
    diffInner
  letI : CompleteSpace (SurfaceDifferentialL2Section (X := X) (E := E) g μ) :=
    diffComplete
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  exact ⟨HilbertSpace.mk⟩

/--
%%handwave
name:
  Intrinsic Hilbert-valued graph model is Hilbert
statement:
  For maps from a smooth Riemannian surface into a real Hilbert space, the
  intrinsic weak-derivative graph is a real Hilbert space with the graph
  inner product inherited from the first-order \(L^2\) product.
proof:
  The intrinsic weak derivative is a closed linear operator into the
  \(L^2\)-sections of \(T^\ast X\otimes E\).  Its graph is therefore a closed
  real linear subspace of the intrinsic first-order Hilbert product.
-/
theorem sobolevH1OnRiemannianSurfaceWithValuesIntrinsicGraph_admits_hilbert_structure
    {X E : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [SecondCountableTopology X] [T2Space X]
    [IsManifold SurfaceRealModel ∞ X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology (Bundle.TotalSpace E (Bundle.Trivial X E))]
    [TopologicalSpace.PseudoMetrizableSpace (Bundle.TotalSpace E (Bundle.Trivial X E))]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X E)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X E)]
    (g : SmoothRiemannianMetricOnSurface X) :
    AdmitsRealHilbertStructure
      (SobolevH1OnSurfaceWithValuesIntrinsicGraphHilbertModel
        (X := X) (E := E) g
        (SmoothRiemannianMetricOnManifold.volume g.toManifoldMetric)) := by
  simpa [WeakDerivativeIntrinsicGraphOnSurfaceWithValues, SurfaceRealModel]
    using
      sobolevH1OnRiemannianManifoldWithValuesIntrinsicGraph_admits_hilbert_structure
        (H := ℂ) (X := X) (E := E) g.toManifoldMetric

/--
%%handwave
name:
  Intrinsic surface graph model for a smooth area measure is Hilbert
statement:
  For maps from a smooth Riemannian surface into a complete real Hilbert
  space, the intrinsic weak-derivative graph formed with any smooth positive
  area measure is a real Hilbert space.
proof:
  A smooth positive area measure is a smooth positive measure for the real
  surface manifold model.  Apply the manifold intrinsic graph Hilbert theorem.
-/
theorem sobolevH1OnSurfaceWithValuesIntrinsicGraph_admits_hilbert_structure_of_smoothPositiveArea
    {X E : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X]
    [IsManifold SurfaceRealModel ∞ X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology (Bundle.TotalSpace E (Bundle.Trivial X E))]
    [TopologicalSpace.PseudoMetrizableSpace (Bundle.TotalSpace E (Bundle.Trivial X E))]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X E)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X E)]
    (g : SmoothRiemannianMetricOnSurface X) (μ : Measure X)
    (hμ : SmoothPositiveAreaMeasureOnSurface X μ) :
    AdmitsRealHilbertStructure
      (SobolevH1OnSurfaceWithValuesIntrinsicGraphHilbertModel
        (X := X) (E := E) g μ) := by
  letI : IsManifold SurfaceRealModel 1 X := inferInstance
  let hμ' : SmoothPositiveMeasureOnManifold (I := SurfaceRealModel) μ :=
    { finite_on_compact := hμ.finite_on_compact
      chart_density := hμ.chart_density }
  simpa [WeakDerivativeIntrinsicGraphOnSurfaceWithValues, SurfaceRealModel]
    using
      sobolevH1OnManifoldWithValuesIntrinsicGraph_admits_hilbert_structure_of_smoothPositiveMeasure
        (I := SurfaceRealModel) (X := X) (E := E) g.toManifoldMetric μ hμ'

/--
%%handwave
name:
  Difference of weak gradients has zero coordinate pairings
statement:
  If two cotangent fields are weak gradients of the same function, then in
  every coordinate chart the difference of their coordinate components has
  zero pairing with every smooth compactly supported coordinate test.
proof:
  Apply the two integration-by-parts identities to the same test function and
  subtract.  The left-hand sides agree because the underlying function is the
  same, so the integrals of the two cotangent fields against the test agree.
-/
theorem weakGradient_difference_coordinate_pairings_zero {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) {u : X → ℝ} {du dv : X → ℂ →L[ℝ] ℝ}
    (hdu : IsWeakGradientOnSurface μ u du)
    (hdv : IsWeakGradientOnSurface μ u dv) :
    ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
      (φ : SmoothCompactlySupportedCoordinateFunction
        (surfaceChartRegion e (Set.univ : Set X))) (v : ℂ),
      Integrable
        (fun z ↦
          (du (e.symm z) - dv (e.symm z))
            (surfaceChartTangentMap e z v) * φ z)
        (MeasureTheory.volume.restrict
          (surfaceChartRegion e (Set.univ : Set X))) ∧
        ∫ z in surfaceChartRegion e (Set.univ : Set X),
            (du (e.symm z) - dv (e.symm z))
              (surfaceChartTangentMap e z v) * φ z ∂MeasureTheory.volume = 0 := by
  intro e he φ v
  rcases hdu e he φ v with ⟨_hu_int, hdu_int, hdu_eq⟩
  rcases hdv e he φ v with ⟨_hu_int', hdv_int, hdv_eq⟩
  let μe := MeasureTheory.volume.restrict
    (surfaceChartRegion e (Set.univ : Set X))
  let fdu : ℂ → ℝ :=
    fun z ↦ du (e.symm z) (surfaceChartTangentMap e z v) * φ z
  let fdv : ℂ → ℝ :=
    fun z ↦ dv (e.symm z) (surfaceChartTangentMap e z v) * φ z
  have hsub_int : Integrable (fun z ↦ fdu z - fdv z) μe :=
    hdu_int.sub hdv_int
  have hpair_eq : ∫ z, fdu z ∂μe = ∫ z, fdv z ∂μe := by
    have hneg :
        -(∫ z, fdu z ∂μe) = -(∫ z, fdv z ∂μe) := by
      simpa [μe, fdu, fdv] using hdu_eq.symm.trans hdv_eq
    exact neg_injective hneg
  constructor
  · convert hsub_int using 1
    ext z
    simp [fdu, fdv, sub_mul]
  · calc
      ∫ z in surfaceChartRegion e (Set.univ : Set X),
          (du (e.symm z) - dv (e.symm z))
            (surfaceChartTangentMap e z v) * φ z ∂MeasureTheory.volume
          = ∫ z, fdu z - fdv z ∂μe := by
              congr 1
              ext z
              simp [fdu, fdv, sub_mul]
      _ = ∫ z, fdu z ∂μe - ∫ z, fdv z ∂μe := integral_sub hdu_int hdv_int
      _ = 0 := sub_eq_zero.mpr hpair_eq

/--
%%handwave
name:
  Zero distributional pairings force a coordinate function to vanish
statement:
  On an open coordinate region, a real-valued function whose product with
  every smooth compactly supported test is integrable and whose test pairings
  all vanish is zero almost everywhere.
proof:
  First obtain local integrability.  On every compact subset of the region,
  choose a smooth bump function which is identically one on the compact set
  and whose closed support stays inside the region; the assumed integrability
  of the product with this bump gives integrability of the original function
  on the compact set.  Then apply the standard fundamental lemma of
  distributions for locally integrable functions tested against compactly
  supported smooth functions.
-/
theorem coordinateFunction_eq_zero_ae_of_zero_distribution_pairings
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {f : ℂ → ℝ}
    (hpair :
      ∀ φ : SmoothCompactlySupportedCoordinateFunction Ω,
        Integrable (fun z ↦ f z * φ z) (MeasureTheory.volume.restrict Ω) ∧
          ∫ z in Ω, f z * φ z ∂MeasureTheory.volume = 0) :
    ∀ᵐ z ∂MeasureTheory.volume.restrict Ω, f z = 0 := by
  have hf_loc : LocallyIntegrableOn f Ω MeasureTheory.volume := by
    rw [locallyIntegrableOn_iff hΩ.isLocallyClosed]
    intro K hKΩ hK_comp
    obtain ⟨δ, hδ_pos, hδΩ⟩ :=
      hK_comp.exists_cthickening_subset_open hΩ hKΩ
    obtain ⟨ψ, hψ_smooth, _hψ_range, hψ_support, hψ_one⟩ :=
      exists_contMDiff_support_eq_eq_one_iff
        (I := 𝓘(ℝ, ℂ)) (n := ⊤)
        (Metric.isOpen_thickening) hK_comp.isClosed
        (Metric.self_subset_thickening hδ_pos K)
    have hψ_tsupport_subset_cthickening :
        tsupport ψ ⊆ Metric.cthickening δ K := by
      rw [tsupport, hψ_support]
      exact Metric.closure_thickening_subset_cthickening δ K
    let φ : SmoothCompactlySupportedCoordinateFunction Ω :=
      { toFun := ψ
        smooth := hψ_smooth.contDiff
        support_subset := hψ_tsupport_subset_cthickening.trans hδΩ
        compact_support := by
          exact IsCompact.of_isClosed_subset (hK_comp.cthickening)
            (isClosed_tsupport ψ) hψ_tsupport_subset_cthickening }
    have hprod_int : Integrable (fun z ↦ f z * φ z)
        (MeasureTheory.volume.restrict Ω) :=
      (hpair φ).1
    have hprod_int_K : Integrable (fun z ↦ f z * φ z)
        (MeasureTheory.volume.restrict K) := by
      have hres := hprod_int.restrict (s := K)
      simpa [Measure.restrict_restrict_of_subset hKΩ] using hres
    have hprod_eq_f : (fun z ↦ f z * φ z) =ᵐ[MeasureTheory.volume.restrict K] f := by
      exact ae_restrict_of_forall_mem hK_comp.measurableSet fun z hzK ↦ by
        have hψ_eq_one : ψ z = 1 := (hψ_one z).1 hzK
        simp [φ, hψ_eq_one]
    exact hprod_int_K.congr hprod_eq_f
  have hzero_vol :
      ∀ᵐ z ∂MeasureTheory.volume, z ∈ Ω → f z = 0 := by
    refine hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero hf_loc ?_
    intro g hg_smooth hg_compact hg_support
    let φ : SmoothCompactlySupportedCoordinateFunction Ω :=
      { toFun := g
        smooth := hg_smooth
        support_subset := hg_support
        compact_support := hg_compact }
    have hset : ∫ z in Ω, f z * φ z ∂MeasureTheory.volume = 0 :=
      (hpair φ).2
    have hfull :
        ∫ z in Ω, g z * f z ∂MeasureTheory.volume =
          ∫ z, g z * f z ∂MeasureTheory.volume := by
      exact setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := Ω) (μ := MeasureTheory.volume)
        (f := fun z ↦ g z * f z)
        fun z hzΩ ↦ by
          have hz_tsupport : z ∉ tsupport g := fun hz ↦ hzΩ (hg_support hz)
          simp [image_eq_zero_of_notMem_tsupport hz_tsupport]
    calc
      ∫ z, g z • f z ∂MeasureTheory.volume
          = ∫ z, g z * f z ∂MeasureTheory.volume := by simp
      _ = ∫ z in Ω, g z * f z ∂MeasureTheory.volume := hfull.symm
      _ = ∫ z in Ω, f z * φ z ∂MeasureTheory.volume := by
            congr 1
            ext z
            simp [φ, mul_comm]
      _ = 0 := hset
  exact (ae_restrict_iff' hΩ.measurableSet).2 hzero_vol

/--
%%handwave
name:
  Zero coordinate distributional pairings force zero cotangent field
statement:
  For a smooth positive area measure, an \(L^2\) cotangent field whose
  coordinate components pair to zero with every smooth compactly supported
  coordinate test is zero almost everywhere.
proof:
  In each coordinate chart, the fundamental lemma of distributions says that
  an \(L^1_{\mathrm{loc}}\) function with zero pairing against all smooth
  compactly supported tests vanishes Lebesgue-a.e.  Apply this to the two
  coordinate components of the cotangent field.  The chart tangent map is an
  isomorphism on the coordinate image, so the cotangent field vanishes in the
  chart.  Since the smooth area measure is locally a positive smooth density
  times Lebesgue measure, these coordinate almost-everywhere statements give
  vanishing almost everywhere on the surface.
-/
theorem cotangentField_eq_zero_ae_of_zero_coordinate_distribution_pairings {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [IsManifold SurfaceRealModel ∞ X]
    (μ : Measure X) {w : X → ℂ →L[ℝ] ℝ}
    (hμ : SmoothPositiveAreaMeasureOnSurface X μ)
    (_hw_mem : MemLp w 2 μ)
    (hpair :
      ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
        (φ : SmoothCompactlySupportedCoordinateFunction
          (surfaceChartRegion e (Set.univ : Set X))) (v : ℂ),
        Integrable
          (fun z ↦ w (e.symm z) (surfaceChartTangentMap e z v) * φ z)
          (MeasureTheory.volume.restrict
            (surfaceChartRegion e (Set.univ : Set X))) ∧
          ∫ z in surfaceChartRegion e (Set.univ : Set X),
              w (e.symm z) (surfaceChartTangentMap e z v) * φ z
                ∂MeasureTheory.volume = 0) :
    w =ᵐ[μ] 0 := by
  have hchart_zero :
      ∀ (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X),
        ∀ᵐ x ∂μ.restrict e.source, w x = 0 := by
    intro e he
    let Ω : Set ℂ := surfaceChartRegion e (Set.univ : Set X)
    have hΩ_eq : Ω = e.target := by
      ext z
      simp [Ω, surfaceChartRegion]
    have hΩ_open : IsOpen Ω := by
      simpa [hΩ_eq] using e.open_target
    have hcoord :
        ∀ v : ℂ, ∀ᵐ z ∂MeasureTheory.volume.restrict Ω,
          w (e.symm z) (surfaceChartTangentMap e z v) = 0 := by
      intro v
      exact coordinateFunction_eq_zero_ae_of_zero_distribution_pairings
        hΩ_open
        (f := fun z ↦ w (e.symm z) (surfaceChartTangentMap e z v))
        (by
          intro φ
          simpa [Ω] using hpair e he φ v)
    have hcoord_zero :
        ∀ᵐ z ∂MeasureTheory.volume.restrict Ω, w (e.symm z) = 0 := by
      filter_upwards [hcoord (1 : ℂ), hcoord Complex.I,
        ae_restrict_mem hΩ_open.measurableSet] with z h₁ hI hzΩ
      have hz_target : z ∈ e.target := by
        simpa [hΩ_eq] using hzΩ
      let A : ℂ →L[ℝ] ℂ := surfaceChartTangentMap e z
      let ξ : ℂ →L[ℝ] ℝ := w (e.symm z)
      have hA : A.IsInvertible := by
        simpa [A] using
          surfaceChartTangentMap_isInvertible_of_isManifold X e he z hz_target
      have h₁' : ξ (A (1 : ℂ)) = 0 := by
        simpa [A, ξ] using h₁
      have hI' : ξ (A Complex.I) = 0 := by
        simpa [A, ξ] using hI
      ext u
      rcases ContinuousLinearMap.IsInvertible.surjective hA u with ⟨a, rfl⟩
      have ha :
          a = (a.re : ℝ) • (1 : ℂ) + (a.im : ℝ) • Complex.I := by
        simpa [smul_eq_mul, mul_comm] using (Complex.re_add_im a).symm
      have hA_decomp :
          A a = (a.re : ℝ) • A (1 : ℂ) + (a.im : ℝ) • A Complex.I := by
        conv_lhs => rw [ha]
        rw [map_add, map_smul, map_smul]
      change ξ (A a) = 0
      calc
        ξ (A a)
            = ξ ((a.re : ℝ) • A (1 : ℂ) + (a.im : ℝ) • A Complex.I) := by
                rw [hA_decomp]
        _ = (a.re : ℝ) • ξ (A (1 : ℂ)) + (a.im : ℝ) • ξ (A Complex.I) := by
                rw [map_add, map_smul, map_smul]
        _ = 0 := by
                simp [h₁', hI']
    obtain ⟨ρ, _hρ_smooth, _hρ_pos, hmap⟩ := hμ.chart_density e he
    have hcoord_target :
        ∀ᵐ z ∂MeasureTheory.volume.restrict e.target, w (e.symm z) = 0 := by
      simpa [hΩ_eq] using hcoord_zero
    have hmap_zero :
        ∀ᵐ z ∂Measure.map e (μ.restrict e.source), w (e.symm z) = 0 := by
      rw [hmap]
      exact (withDensity_absolutelyContinuous _ _).ae_le hcoord_target
    have he_aemeas : AEMeasurable e (μ.restrict e.source) :=
      openPartialHomeomorph_aemeasurable_restrict_source e μ
    have hpull :
        ∀ᵐ x ∂μ.restrict e.source, w (e.symm (e x)) = 0 :=
      ae_of_ae_map he_aemeas hmap_zero
    filter_upwards [hpull, ae_restrict_mem e.open_source.measurableSet] with x hx hx_source
    simpa [e.left_inv hx_source] using hx
  obtain ⟨S, hS_countable, hS_cover⟩ :=
    exists_countable_chartAt_source_cover X
  have hcover_restrict :
      ∀ᵐ y ∂μ.restrict (⋃ x ∈ S, (chartAt ℂ x).source), w y = 0 := by
    refine (ae_restrict_biUnion_iff
      (μ := μ) (s := fun x : X ↦ (chartAt ℂ x).source)
      hS_countable (fun y ↦ w y = 0)).2 ?_
    intro x _hxS
    exact hchart_zero (chartAt ℂ x) (chart_mem_atlas ℂ x)
  have hcover_univ :
      ∀ᵐ y ∂μ.restrict (Set.univ : Set X), w y = 0 := by
    simpa [hS_cover] using hcover_restrict
  simpa using hcover_univ

/--
%%handwave
name:
  Weak gradients are unique for smooth area measures
statement:
  For a smooth positive area measure, if two square-integrable cotangent
  fields are weak gradients of the same function, then they agree almost
  everywhere.
proof:
  Test the difference of the two weak-gradient identities against compactly
  supported smooth functions.  The resulting distribution has zero pairing
  with all tests, so the difference field vanishes as an \(L^2\) cotangent
  field in each coordinate chart.  The smooth positive area measure is
  mutually absolutely continuous with Lebesgue measure in coordinates, so the
  coordinate almost-everywhere equality glues to the surface.
-/
theorem weakGradient_unique_ae_on_smooth_positive_area_surface {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [IsManifold SurfaceRealModel ∞ X]
    (μ : Measure X) {u : X → ℝ} {du dv : X → ℂ →L[ℝ] ℝ}
    (hμ : SmoothPositiveAreaMeasureOnSurface X μ)
    (hdu_mem : MemLp du 2 μ) (hdv_mem : MemLp dv 2 μ)
    (hdu : IsWeakGradientOnSurface μ u du)
    (hdv : IsWeakGradientOnSurface μ u dv) :
    du =ᵐ[μ] dv := by
  have hdiff_mem : MemLp (fun x ↦ du x - dv x) 2 μ :=
    hdu_mem.sub hdv_mem
  have hdiff_pair :=
    weakGradient_difference_coordinate_pairings_zero μ hdu hdv
  have hdiff_zero :
      (fun x ↦ du x - dv x) =ᵐ[μ] 0 :=
    cotangentField_eq_zero_ae_of_zero_coordinate_distribution_pairings
      μ hμ hdiff_mem hdiff_pair
  filter_upwards [hdiff_zero] with x hx
  exact sub_eq_zero.mp hx

/--
%%handwave
name:
  Weak gradients are unique
statement:
  For the smooth area measures used in the surface Sobolev theory, if two
  square-integrable cotangent fields are weak gradients of the same function,
  then they agree almost everywhere.
proof:
  This is the smooth-area weak-gradient uniqueness theorem.
-/
theorem weakGradient_unique_ae_on_surface {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [IsManifold SurfaceRealModel ∞ X]
    (μ : Measure X) {u : X → ℝ} {du dv : X → ℂ →L[ℝ] ℝ}
    (hμ : SmoothPositiveAreaMeasureOnSurface X μ)
    (hdu_mem : MemLp du 2 μ) (hdv_mem : MemLp dv 2 μ)
    (hdu : IsWeakGradientOnSurface μ u du)
    (hdv : IsWeakGradientOnSurface μ u dv) :
    du =ᵐ[μ] dv :=
  weakGradient_unique_ae_on_smooth_positive_area_surface
    μ hμ hdu_mem hdv_mem hdu hdv

/--
%%handwave
name:
  Zero has zero weak gradient
statement:
  The zero cotangent field is the weak gradient of the zero function.
proof:
  Both sides of every integration-by-parts identity are integrals of the zero
  function.
-/
theorem isWeakGradientOnSurface_zero {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) :
    IsWeakGradientOnSurface μ (0 : X → ℝ) (0 : X → ℂ →L[ℝ] ℝ) := by
  intro e _he φ v
  let Ω : Set ℂ := surfaceChartRegion e (Set.univ : Set X)
  constructor
  · simp
  · constructor
    · simp
    · simp

/--
%%handwave
name:
  Weak gradients add
statement:
  The sum of two weak gradients is the weak gradient of the sum of the
  functions.
proof:
  Add the two integration-by-parts identities and use linearity of the
  integral.
-/
theorem IsWeakGradientOnSurface.add {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} {u₁ u₂ : X → ℝ}
    {du₁ du₂ : X → ℂ →L[ℝ] ℝ}
    (hu₁ : IsWeakGradientOnSurface μ u₁ du₁)
    (hu₂ : IsWeakGradientOnSurface μ u₂ du₂) :
    IsWeakGradientOnSurface μ (u₁ + u₂) (du₁ + du₂) := by
  intro e he φ v
  rcases hu₁ e he φ v with ⟨hu₁_int, hdu₁_int, h₁_eq⟩
  rcases hu₂ e he φ v with ⟨hu₂_int, hdu₂_int, h₂_eq⟩
  let Ω : Set ℂ := surfaceChartRegion e (Set.univ : Set X)
  let μΩ := MeasureTheory.volume.restrict Ω
  let lhs₁ : ℂ → ℝ :=
    fun z ↦ u₁ (e.symm z) * fderiv ℝ (φ : ℂ → ℝ) z v
  let lhs₂ : ℂ → ℝ :=
    fun z ↦ u₂ (e.symm z) * fderiv ℝ (φ : ℂ → ℝ) z v
  let rhs₁ : ℂ → ℝ :=
    fun z ↦ du₁ (e.symm z) (surfaceChartTangentMap e z v) * φ z
  let rhs₂ : ℂ → ℝ :=
    fun z ↦ du₂ (e.symm z) (surfaceChartTangentMap e z v) * φ z
  have hrhs_add :
      (fun z ↦ rhs₁ z + rhs₂ z) =
        fun z ↦
          (du₁ + du₂) (e.symm z) (surfaceChartTangentMap e z v) * φ z := by
    ext z
    simp [rhs₁, rhs₂, add_mul]
  have h₁_eq' : ∫ z, lhs₁ z ∂μΩ = -∫ z, rhs₁ z ∂μΩ := by
    simpa [Ω, μΩ, lhs₁, rhs₁] using h₁_eq
  have h₂_eq' : ∫ z, lhs₂ z ∂μΩ = -∫ z, rhs₂ z ∂μΩ := by
    simpa [Ω, μΩ, lhs₂, rhs₂] using h₂_eq
  constructor
  · convert hu₁_int.add hu₂_int using 1
    ext z
    simp [add_mul]
  · constructor
    · convert hdu₁_int.add hdu₂_int using 1
      ext z
      simp [add_mul]
    · calc
        ∫ z in Ω,
            (u₁ + u₂) (e.symm z) *
              fderiv ℝ (φ : ℂ → ℝ) z v ∂MeasureTheory.volume
            = ∫ z, lhs₁ z + lhs₂ z ∂μΩ := by
                congr 1
                ext z
                simp [lhs₁, lhs₂, add_mul]
        _ = ∫ z, lhs₁ z ∂μΩ + ∫ z, lhs₂ z ∂μΩ :=
              integral_add hu₁_int hu₂_int
        _ = -∫ z, rhs₁ z ∂μΩ + -∫ z, rhs₂ z ∂μΩ := by
              rw [h₁_eq', h₂_eq']
        _ = -(∫ z, rhs₁ z ∂μΩ + ∫ z, rhs₂ z ∂μΩ) := by ring
        _ = -∫ z, rhs₁ z + rhs₂ z ∂μΩ := by
              rw [integral_add hdu₁_int hdu₂_int]
        _ = -∫ z in Ω,
            (du₁ + du₂) (e.symm z) (surfaceChartTangentMap e z v) *
              φ z ∂MeasureTheory.volume := by
                rw [show μΩ = MeasureTheory.volume.restrict Ω from rfl, hrhs_add]

/--
%%handwave
name:
  Weak gradients scale
statement:
  Multiplying a function and its weak gradient by the same real scalar
  preserves the weak-gradient identity.
proof:
  Pull the scalar through both integrals in the integration-by-parts identity.
-/
theorem IsWeakGradientOnSurface.const_smul {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} (c : ℝ) {u : X → ℝ} {du : X → ℂ →L[ℝ] ℝ}
    (hu : IsWeakGradientOnSurface μ u du) :
    IsWeakGradientOnSurface μ (c • u) (c • du) := by
  intro e he φ v
  rcases hu e he φ v with ⟨hu_int, hdu_int, h_eq⟩
  let Ω : Set ℂ := surfaceChartRegion e (Set.univ : Set X)
  let μΩ := MeasureTheory.volume.restrict Ω
  let lhs : ℂ → ℝ :=
    fun z ↦ u (e.symm z) * fderiv ℝ (φ : ℂ → ℝ) z v
  let rhs : ℂ → ℝ :=
    fun z ↦ du (e.symm z) (surfaceChartTangentMap e z v) * φ z
  have hrhs_smul :
      (fun z ↦ c * rhs z) =
        fun z ↦
          (c • du) (e.symm z) (surfaceChartTangentMap e z v) * φ z := by
    ext z
    simp [rhs, mul_assoc]
  have h_eq' : ∫ z, lhs z ∂μΩ = -∫ z, rhs z ∂μΩ := by
    simpa [Ω, μΩ, lhs, rhs] using h_eq
  constructor
  · convert hu_int.const_mul c using 1
    ext z
    simp [mul_assoc]
  · constructor
    · convert hdu_int.const_mul c using 1
      ext z
      simp [mul_assoc]
    · calc
        ∫ z in Ω,
            (c • u) (e.symm z) * fderiv ℝ (φ : ℂ → ℝ) z v
              ∂MeasureTheory.volume
            = ∫ z, c * lhs z ∂μΩ := by
                congr 1
                ext z
                simp [lhs, mul_assoc]
        _ = c * ∫ z, lhs z ∂μΩ := integral_const_mul c lhs
        _ = c * (-∫ z, rhs z ∂μΩ) := by rw [h_eq']
        _ = -(c * ∫ z, rhs z ∂μΩ) := by ring
        _ = -∫ z, c * rhs z ∂μΩ := by rw [integral_const_mul c rhs]
        _ = -∫ z in Ω,
            (c • du) (e.symm z) (surfaceChartTangentMap e z v) * φ z
              ∂MeasureTheory.volume := by
                rw [show μΩ = MeasureTheory.volume.restrict Ω from rfl, hrhs_smul]

/--
%%handwave
name:
  Smooth functions are continuous on their surface domain
statement:
  A function smooth on a surface region (U) is continuous on (U).
proof:
  In every chart its coordinate representative is smooth and hence continuous; the local chart descriptions cover (U).
-/
theorem isSmoothOnSurface_continuousOn
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {U : Set X} {u : X → ℝ}
    (hu : IsSmoothOnSurface U u) :
    ContinuousOn u U := by
  intro x hx
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ x
  have he : e ∈ atlas ℂ X := chart_mem_atlas ℂ x
  have hcoord_cont : ContinuousOn (fun z : ℂ ↦ u (e.symm z))
      (e.target ∩ e.symm ⁻¹' U) :=
    (hu e he).continuousOn
  have hlocal : ContinuousOn u (U ∩ e.source) := by
    have hsubset : U ∩ e.source ⊆ e.source := by
      intro y hy
      exact hy.2
    rw [e.symm.continuousOn_iff_continuousOn_comp_right (f := u)
      (s := U ∩ e.source) hsubset]
    exact hcoord_cont.mono (by
      intro z hz
      exact ⟨hz.1, hz.2.1⟩)
  have hxlocal : x ∈ U ∩ e.source := ⟨hx, mem_chart_source ℂ x⟩
  have hlocal_at : ContinuousWithinAt u (U ∩ e.source) x :=
    hlocal.continuousWithinAt hxlocal
  have hsource_nhds : e.source ∈ 𝓝 x := chart_source_mem_nhds ℂ x
  exact (continuousWithinAt_inter hsource_nhds).1 hlocal_at

/--
%%handwave
name:
  A globally smooth surface function is continuous
statement:
  If a function is smooth on the whole surface, then it is continuous.
proof:
  Its restriction is continuous on the universal set, which is equivalent to ordinary continuity.
-/
theorem isSmoothOnSurface_univ_continuous
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {u : X → ℝ} (hu : IsSmoothOnSurface (Set.univ : Set X) u) :
    Continuous u := by
  rw [← continuousOn_univ]
  exact isSmoothOnSurface_continuousOn hu

/-- Smooth compactly supported surface tests are closed under addition. -/
def SmoothCompactlySupportedGlobalSurfaceFunction.add
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (F G : SmoothCompactlySupportedGlobalSurfaceFunction X) :
    SmoothCompactlySupportedGlobalSurfaceFunction X where
  toFun := F.toFun + G.toFun
  gradient := F.gradient + G.gradient
  smooth := by
    intro e he
    exact (F.smooth e he).add (G.smooth e he)
  gradient_eq := by
    intro e he z hz v
    have hFdiff :
        DifferentiableAt ℝ (fun w : ℂ ↦ F.toFun (e.symm w)) z :=
      surfaceFunctionChartRepresentative_differentiableAt e he F.toFun F.smooth z hz
    have hGdiff :
        DifferentiableAt ℝ (fun w : ℂ ↦ G.toFun (e.symm w)) z :=
      surfaceFunctionChartRepresentative_differentiableAt e he G.toFun G.smooth z hz
    calc
      (F.gradient + G.gradient) (e.symm z) (surfaceChartTangentMap e z v)
          = F.gradient (e.symm z) (surfaceChartTangentMap e z v) +
              G.gradient (e.symm z) (surfaceChartTangentMap e z v) := by
              simp
      _ = fderiv ℝ (fun w : ℂ ↦ F.toFun (e.symm w)) z v +
            fderiv ℝ (fun w : ℂ ↦ G.toFun (e.symm w)) z v := by
              rw [F.gradient_eq e he z hz v, G.gradient_eq e he z hz v]
      _ = (fderiv ℝ (fun w : ℂ ↦ F.toFun (e.symm w)) z +
            fderiv ℝ (fun w : ℂ ↦ G.toFun (e.symm w)) z) v := by
              simp
      _ = fderiv ℝ
            ((fun w : ℂ ↦ F.toFun (e.symm w)) +
              fun w : ℂ ↦ G.toFun (e.symm w)) z v := by
              symm
              rw [fderiv_add hFdiff hGdiff]
      _ = fderiv ℝ
            (fun w : ℂ ↦ (F.toFun + G.toFun) (e.symm w)) z v := by
              rfl
  compact_support := by
    have hF : HasCompactSupport F.toFun := by
      simpa [HasCompactSupportOnSurface, HasCompactSupport] using F.compact_support
    have hG : HasCompactSupport G.toFun := by
      simpa [HasCompactSupportOnSurface, HasCompactSupport] using G.compact_support
    simpa [HasCompactSupportOnSurface, HasCompactSupport] using hF.add hG

/-- Smooth compactly supported surface tests are closed under negation. -/
def SmoothCompactlySupportedGlobalSurfaceFunction.neg
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (F : SmoothCompactlySupportedGlobalSurfaceFunction X) :
    SmoothCompactlySupportedGlobalSurfaceFunction X where
  toFun := -F.toFun
  gradient := -F.gradient
  smooth := by
    intro e he
    exact (F.smooth e he).neg
  gradient_eq := by
    intro e he z hz v
    calc
      (-F.gradient) (e.symm z) (surfaceChartTangentMap e z v)
          = -F.gradient (e.symm z) (surfaceChartTangentMap e z v) := by
              simp
      _ = -fderiv ℝ (fun w : ℂ ↦ F.toFun (e.symm w)) z v := by
              rw [F.gradient_eq e he z hz v]
      _ = (-fderiv ℝ (fun w : ℂ ↦ F.toFun (e.symm w)) z) v := by
              simp
      _ = fderiv ℝ (-(fun w : ℂ ↦ F.toFun (e.symm w))) z v := by
              symm
              rw [fderiv_neg]
      _ = fderiv ℝ (fun w : ℂ ↦ (-F.toFun) (e.symm w)) z v := by
              rfl
  compact_support := by
    have hF : HasCompactSupport F.toFun := by
      simpa [HasCompactSupportOnSurface, HasCompactSupport] using F.compact_support
    simpa [HasCompactSupportOnSurface, HasCompactSupport] using hF.neg

/-- Smooth compactly supported surface tests are closed under subtraction. -/
def SmoothCompactlySupportedGlobalSurfaceFunction.sub
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (F G : SmoothCompactlySupportedGlobalSurfaceFunction X) :
    SmoothCompactlySupportedGlobalSurfaceFunction X :=
  SmoothCompactlySupportedGlobalSurfaceFunction.add F
    (SmoothCompactlySupportedGlobalSurfaceFunction.neg G)

/--
%%handwave
name:
  Vector-valued weak derivative of zero
statement:
  The zero differential field is the weak derivative of the zero map.
proof:
  Specialize the zero weak-derivative identity on manifolds to the surface model.
-/
theorem isWeakDerivativeOnSurfaceBundle_zero {X E : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [IsManifold SurfaceRealModel 1 X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X) :
    IsWeakDerivativeOnSurfaceBundle μ (0 : X → E)
      (0 : SurfaceDifferentialField X E) := by
  intro e _he φ v
  constructor
  · simp
  · constructor
    · simp [SurfaceDifferentialField.evalChart]
    · simp [SurfaceDifferentialField.evalChart]

/--
%%handwave
name:
  Vector-valued weak derivatives add
statement:
  The sum of two vector-valued weak derivatives is the weak derivative of the
  sum of the corresponding maps.
proof:
  Add the two integration-by-parts identities and use linearity of the
  Bochner integral.
-/
theorem IsWeakDerivativeOnSurfaceBundle.add {X E : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [IsManifold SurfaceRealModel 1 X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure X} {u₁ u₂ : X → E}
    {du₁ du₂ : SurfaceDifferentialField X E}
    (hu₁ : IsWeakDerivativeOnSurfaceBundle μ u₁ du₁)
    (hu₂ : IsWeakDerivativeOnSurfaceBundle μ u₂ du₂) :
    IsWeakDerivativeOnSurfaceBundle μ (u₁ + u₂) (du₁ + du₂) := by
  intro e he φ v
  rcases hu₁ e he φ v with ⟨hu₁_int, hdu₁_int, h₁_eq⟩
  rcases hu₂ e he φ v with ⟨hu₂_int, hdu₂_int, h₂_eq⟩
  let Ω : Set ℂ := surfaceChartRegion e (Set.univ : Set X)
  let μΩ := MeasureTheory.volume.restrict Ω
  let lhs₁ : ℂ → E :=
    fun z ↦ (fderiv ℝ (φ : ℂ → ℝ) z v) • u₁ (e.symm z)
  let lhs₂ : ℂ → E :=
    fun z ↦ (fderiv ℝ (φ : ℂ → ℝ) z v) • u₂ (e.symm z)
  let rhs₁ : ℂ → E :=
    fun z ↦ φ z • SurfaceDifferentialField.evalChart du₁ e z v
  let rhs₂ : ℂ → E :=
    fun z ↦ φ z • SurfaceDifferentialField.evalChart du₂ e z v
  have hrhs_add :
      (fun z ↦ rhs₁ z + rhs₂ z) =
        fun z ↦
          φ z • SurfaceDifferentialField.evalChart (du₁ + du₂) e z v := by
    ext z
    simp [rhs₁, rhs₂, SurfaceDifferentialField.evalChart, smul_add]
  have h₁_eq' : ∫ z, lhs₁ z ∂μΩ = -∫ z, rhs₁ z ∂μΩ := by
    simpa [Ω, μΩ, lhs₁, rhs₁] using h₁_eq
  have h₂_eq' : ∫ z, lhs₂ z ∂μΩ = -∫ z, rhs₂ z ∂μΩ := by
    simpa [Ω, μΩ, lhs₂, rhs₂] using h₂_eq
  constructor
  · convert hu₁_int.add hu₂_int using 1
    ext z
    simp [smul_add]
  · constructor
    · convert hdu₁_int.add hdu₂_int using 1
      ext z
      simp [SurfaceDifferentialField.evalChart, smul_add]
    · calc
        ∫ z in Ω,
            (fderiv ℝ (φ : ℂ → ℝ) z v) • (u₁ + u₂) (e.symm z)
              ∂MeasureTheory.volume
            = ∫ z, lhs₁ z + lhs₂ z ∂μΩ := by
                congr 1
                ext z
                simp [lhs₁, lhs₂, smul_add]
        _ = ∫ z, lhs₁ z ∂μΩ + ∫ z, lhs₂ z ∂μΩ :=
              integral_add hu₁_int hu₂_int
        _ = -∫ z, rhs₁ z ∂μΩ + -∫ z, rhs₂ z ∂μΩ := by
              rw [h₁_eq', h₂_eq']
        _ = -(∫ z, rhs₁ z ∂μΩ + ∫ z, rhs₂ z ∂μΩ) := by
              rw [neg_add]
        _ = -∫ z, rhs₁ z + rhs₂ z ∂μΩ := by
              rw [integral_add hdu₁_int hdu₂_int]
        _ = -∫ z in Ω,
            φ z • SurfaceDifferentialField.evalChart (du₁ + du₂) e z v
              ∂MeasureTheory.volume := by
                rw [show μΩ = MeasureTheory.volume.restrict Ω from rfl, hrhs_add]

/--
%%handwave
name:
  Vector-valued weak derivatives scale
statement:
  Multiplying a vector-valued map and its weak derivative by the same real
  scalar preserves the weak-derivative identity.
proof:
  Pull the scalar through both Bochner integrals.
-/
theorem IsWeakDerivativeOnSurfaceBundle.const_smul {X E : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [IsManifold SurfaceRealModel 1 X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure X} (c : ℝ) {u : X → E}
    {du : SurfaceDifferentialField X E}
    (hu : IsWeakDerivativeOnSurfaceBundle μ u du) :
    IsWeakDerivativeOnSurfaceBundle μ (c • u) (c • du) := by
  intro e he φ v
  rcases hu e he φ v with ⟨hu_int, hdu_int, h_eq⟩
  let Ω : Set ℂ := surfaceChartRegion e (Set.univ : Set X)
  let μΩ := MeasureTheory.volume.restrict Ω
  let lhs : ℂ → E :=
    fun z ↦ (fderiv ℝ (φ : ℂ → ℝ) z v) • u (e.symm z)
  let rhs : ℂ → E :=
    fun z ↦ φ z • SurfaceDifferentialField.evalChart du e z v
  have hrhs_smul :
      (fun z ↦ c • rhs z) =
        fun z ↦
          φ z • SurfaceDifferentialField.evalChart (c • du) e z v := by
    ext z
    simp [rhs, SurfaceDifferentialField.evalChart, smul_smul, mul_comm]
  have h_eq' : ∫ z, lhs z ∂μΩ = -∫ z, rhs z ∂μΩ := by
    simpa [Ω, μΩ, lhs, rhs] using h_eq
  constructor
  · convert Integrable.smul c hu_int using 1
    ext z
    simp [smul_smul, mul_comm]
  · constructor
    · convert Integrable.smul c hdu_int using 1
      ext z
      simp [SurfaceDifferentialField.evalChart, smul_smul, mul_comm]
    · calc
        ∫ z in Ω,
            (fderiv ℝ (φ : ℂ → ℝ) z v) • (c • u) (e.symm z)
              ∂MeasureTheory.volume
            = ∫ z, c • lhs z ∂μΩ := by
                congr 1
                ext z
                simp [lhs, smul_smul, mul_comm]
        _ = c • ∫ z, lhs z ∂μΩ := integral_smul c lhs
        _ = c • (-∫ z, rhs z ∂μΩ) := by rw [h_eq']
        _ = -(c • ∫ z, rhs z ∂μΩ) := by simp
        _ = -∫ z, c • rhs z ∂μΩ := by rw [integral_smul c rhs]
        _ = -∫ z in Ω,
            φ z • SurfaceDifferentialField.evalChart (c • du) e z v
              ∂MeasureTheory.volume := by
                rw [show μΩ = MeasureTheory.volume.restrict Ω from rfl, hrhs_smul]

/--
%%handwave
name:
  Dual-tested vector-valued weak derivative of zero
statement:
  The zero coordinate differential is the dual-tested weak derivative of the
  zero map.
proof:
  Every continuous linear functional sends the zero value and zero differential to the scalar zero weak-gradient pair.
-/
theorem isWeakDerivativeOnSurfaceWithValuesByDual_zero {X E : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X) :
    IsWeakDerivativeOnSurfaceWithValuesByDual μ (0 : X → E)
      (0 : X → SurfaceDifferentialCoordinateHilbertFiber E) := by
  intro Λ
  simpa using (isWeakGradientOnSurface_zero (X := X) μ)

/--
%%handwave
name:
  Dual-tested vector-valued weak derivatives add
statement:
  The sum of two dual-tested weak derivatives is the dual-tested weak
  derivative of the sum of the maps.
proof:
  After applying any target functional, linearity turns the sum into the sum of the two scalar weak-gradient pairs; add their identities.
-/
theorem IsWeakDerivativeOnSurfaceWithValuesByDual.add {X E : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure X} {u₁ u₂ : X → E}
    {du₁ du₂ : X → SurfaceDifferentialCoordinateHilbertFiber E}
    (hu₁ : IsWeakDerivativeOnSurfaceWithValuesByDual μ u₁ du₁)
    (hu₂ : IsWeakDerivativeOnSurfaceWithValuesByDual μ u₂ du₂) :
    IsWeakDerivativeOnSurfaceWithValuesByDual μ (u₁ + u₂) (du₁ + du₂) := by
  intro Λ
  simpa [Pi.add_apply, map_add, SurfaceDifferentialCoordinateHilbertFiber.toLinearMap_add]
    using (hu₁ Λ).add (hu₂ Λ)

/--
%%handwave
name:
  Dual-tested vector-valued weak derivatives scale
statement:
  Multiplying a vector-valued map and its weak derivative by the same real
  scalar preserves the dual-tested weak-derivative identity.
proof:
  After scalar projection, pull the constant through the functional and scale the scalar weak-gradient identity.
-/
theorem IsWeakDerivativeOnSurfaceWithValuesByDual.const_smul {X E : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure X} (c : ℝ) {u : X → E}
    {du : X → SurfaceDifferentialCoordinateHilbertFiber E}
    (hu : IsWeakDerivativeOnSurfaceWithValuesByDual μ u du) :
    IsWeakDerivativeOnSurfaceWithValuesByDual μ (c • u) (c • du) := by
  intro Λ
  simpa [Pi.smul_apply, map_smul, SurfaceDifferentialCoordinateHilbertFiber.toLinearMap_smul]
    using (hu Λ).const_smul c

/--
%%handwave
name:
  Weak-gradient graph
statement:
  The weak-gradient graph consists of \(L^2\) function classes paired with
  \(L^2\) cotangent-field classes which represent their weak gradients.
-/
def WeakGradientGraphOnSurface {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (p : Lp ℝ 2 μ × Lp (ℂ →L[ℝ] ℝ) 2 μ) : Prop :=
  ∃ u : X → ℝ, ∃ du : X → ℂ →L[ℝ] ℝ,
    (fun x ↦ p.1 x) =ᵐ[μ] u ∧ (fun x ↦ p.2 x) =ᵐ[μ] du ∧
      IsWeakGradientOnSurface μ u du

/--
%%handwave
name:
  The zero pair belongs to the weak-gradient graph
statement:
  The zero \(L^2\) function together with the zero cotangent field satisfies the surface weak-gradient identity.
proof:
  Choose zero representatives; both test integrals vanish.
-/
theorem weakGradientGraphOnSurface_zero {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) :
    WeakGradientGraphOnSurface μ
      (0 : Lp ℝ 2 μ × Lp (ℂ →L[ℝ] ℝ) 2 μ) := by
  refine ⟨(0 : X → ℝ), (0 : X → ℂ →L[ℝ] ℝ), ?_, ?_, ?_⟩
  · simpa using
      (Lp.coeFn_zero ℝ 2 μ :
        ((0 : Lp ℝ 2 μ) : X → ℝ) =ᵐ[μ] 0)
  · simpa using
      (Lp.coeFn_zero (ℂ →L[ℝ] ℝ) 2 μ :
        ((0 : Lp (ℂ →L[ℝ] ℝ) 2 μ) : X → ℂ →L[ℝ] ℝ) =ᵐ[μ]
          (0 : X → ℂ →L[ℝ] ℝ))
  · exact isWeakGradientOnSurface_zero μ

/--
%%handwave
name:
  The weak-gradient graph is closed under addition
statement:
  If \((u,du)\) and \((v,dv)\) are weak-gradient pairs, then \((u+v,du+dv)\) is a weak-gradient pair.
proof:
  Add the two distributional integration-by-parts identities and use linearity of the integrals.
-/
theorem weakGradientGraphOnSurface_add {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} {p q : Lp ℝ 2 μ × Lp (ℂ →L[ℝ] ℝ) 2 μ}
    (hp : WeakGradientGraphOnSurface μ p)
    (hq : WeakGradientGraphOnSurface μ q) :
    WeakGradientGraphOnSurface μ (p + q) := by
  rcases hp with ⟨u, du, hp_u, hp_du, hweak⟩
  rcases hq with ⟨v, dv, hq_u, hq_du, hweak'⟩
  refine ⟨u + v, du + dv, ?_, ?_, ?_⟩
  · have hcoe :
        (fun x ↦ (p + q).1 x) =ᵐ[μ] fun x ↦ p.1 x + q.1 x := by
      simpa using (Lp.coeFn_add p.1 q.1)
    exact hcoe.trans (hp_u.add hq_u)
  · have hcoe :
        (fun x ↦ (p + q).2 x) =ᵐ[μ] fun x ↦ p.2 x + q.2 x := by
      simpa using (Lp.coeFn_add p.2 q.2)
    exact hcoe.trans (hp_du.add hq_du)
  · exact hweak.add hweak'

set_option synthInstance.maxHeartbeats 200000 in
/--
%%handwave
name:
  The weak-gradient graph is closed under real scaling
statement:
  If \((u,du)\) is a weak-gradient pair and \(c\in\mathbb R\), then \((cu,c\,du)\) is also a weak-gradient pair.
proof:
  Multiply the distributional identity by (c) and use linearity of integration.
-/
theorem weakGradientGraphOnSurface_const_smul {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} (c : ℝ)
    {p : Lp ℝ 2 μ × Lp (ℂ →L[ℝ] ℝ) 2 μ}
    (hp : WeakGradientGraphOnSurface μ p) :
    WeakGradientGraphOnSurface μ (c • p) := by
  rcases hp with ⟨u, du, hp_u, hp_du, hweak⟩
  refine ⟨c • u, c • du, ?_, ?_, ?_⟩
  · have hcoe :
        (fun x ↦ (c • p).1 x) =ᵐ[μ] fun x ↦ c • p.1 x := by
      simpa using (Lp.coeFn_smul c p.1)
    filter_upwards [hcoe, hp_u] with x hx hx'
    rw [hx, hx']
    rfl
  · have hcoe :
        (fun x ↦ (c • p).2 x) =ᵐ[μ] fun x ↦ c • p.2 x := by
      simpa using (Lp.coeFn_smul c p.2)
    filter_upwards [hcoe, hp_du] with x hx hx'
    rw [hx, hx']
    rfl
  · exact hweak.const_smul c

/--
%%handwave
name:
  Hilbert-valued weak-derivative graph
statement:
  The Hilbert-valued weak-derivative graph consists of \(L^2\) function
  classes paired with \(L^2\) coordinate differential classes which represent
  their weak derivatives.
-/
def WeakDerivativeGraphOnSurfaceWithValues {X E : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [IsManifold SurfaceRealModel 1 X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X)
    (p : Lp E 2 μ × Lp (SurfaceDifferentialCoordinateHilbertFiber E) 2 μ) :
    Prop :=
  ∃ u : X → E, ∃ du : X → SurfaceDifferentialCoordinateHilbertFiber E,
    (fun x ↦ p.1 x) =ᵐ[μ] u ∧ (fun x ↦ p.2 x) =ᵐ[μ] du ∧
      IsWeakDerivativeOnSurfaceWithValuesByDual μ u du

/--
%%handwave
name:
  The zero pair belongs to the vector-valued weak-derivative graph
statement:
  The zero Hilbert-valued \(L^2\) function and zero coordinate differential form a weak-derivative pair.
proof:
  Every scalar dual projection is the zero weak-gradient pair.
-/
theorem weakDerivativeGraphOnSurfaceWithValues_zero {X E : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [IsManifold SurfaceRealModel 1 X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X) :
    WeakDerivativeGraphOnSurfaceWithValues μ
      (0 : Lp E 2 μ ×
        Lp (SurfaceDifferentialCoordinateHilbertFiber E) 2 μ) := by
  refine ⟨(0 : X → E), (0 : X → SurfaceDifferentialCoordinateHilbertFiber E),
    ?_, ?_, ?_⟩
  · simpa using
      (Lp.coeFn_zero E 2 μ :
        ((0 : Lp E 2 μ) : X → E) =ᵐ[μ] 0)
  · simpa using
      (Lp.coeFn_zero (SurfaceDifferentialCoordinateHilbertFiber E) 2 μ :
        ((0 : Lp (SurfaceDifferentialCoordinateHilbertFiber E) 2 μ) :
            X → SurfaceDifferentialCoordinateHilbertFiber E) =ᵐ[μ]
          (0 : X → SurfaceDifferentialCoordinateHilbertFiber E))
  · exact isWeakDerivativeOnSurfaceWithValuesByDual_zero (X := X) (E := E) μ

/--
%%handwave
name:
  The vector-valued weak-derivative graph is closed under addition
statement:
  The sum of two Hilbert-valued weak-derivative pairs is again a weak-derivative pair.
proof:
  For every continuous linear functional on the target, add the corresponding scalar weak-gradient identities.
-/
theorem weakDerivativeGraphOnSurfaceWithValues_add {X E : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [IsManifold SurfaceRealModel 1 X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure X}
    {p q : Lp E 2 μ × Lp (SurfaceDifferentialCoordinateHilbertFiber E) 2 μ}
    (hp : WeakDerivativeGraphOnSurfaceWithValues μ p)
    (hq : WeakDerivativeGraphOnSurfaceWithValues μ q) :
    WeakDerivativeGraphOnSurfaceWithValues μ (p + q) := by
  rcases hp with ⟨u, du, hp_u, hp_du, hweak⟩
  rcases hq with ⟨v, dv, hq_u, hq_du, hweak'⟩
  refine ⟨u + v, du + dv, ?_, ?_, ?_⟩
  · have hcoe :
        (fun x ↦ (p + q).1 x) =ᵐ[μ] fun x ↦ p.1 x + q.1 x := by
      simpa using (Lp.coeFn_add p.1 q.1)
    exact hcoe.trans (hp_u.add hq_u)
  · have hcoe :
        (fun x ↦ (p + q).2 x) =ᵐ[μ] fun x ↦ p.2 x + q.2 x := by
      simpa using (Lp.coeFn_add p.2 q.2)
    exact hcoe.trans (hp_du.add hq_du)
  · exact hweak.add hweak'

/--
%%handwave
name:
  The vector-valued weak-derivative graph is closed under real scaling
statement:
  A real scalar multiple of a Hilbert-valued weak-derivative pair remains in the graph.
proof:
  Apply each target functional and scale the resulting scalar weak-gradient identity.
-/
theorem weakDerivativeGraphOnSurfaceWithValues_const_smul {X E : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [IsManifold SurfaceRealModel 1 X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure X} (c : ℝ)
    {p : Lp E 2 μ × Lp (SurfaceDifferentialCoordinateHilbertFiber E) 2 μ}
    (hp : WeakDerivativeGraphOnSurfaceWithValues μ p) :
    WeakDerivativeGraphOnSurfaceWithValues μ (c • p) := by
  rcases hp with ⟨u, du, hp_u, hp_du, hweak⟩
  refine ⟨c • u, c • du, ?_, ?_, ?_⟩
  · have hcoe :
        (fun x ↦ (c • p).1 x) =ᵐ[μ] fun x ↦ c • p.1 x := by
      simpa using (Lp.coeFn_smul c p.1)
    filter_upwards [hcoe, hp_u] with x hx hx'
    rw [hx, hx']
    rfl
  · have hcoe :
        (fun x ↦ (c • p).2 x) =ᵐ[μ] fun x ↦ c • p.2 x := by
      simpa using (Lp.coeFn_smul c p.2)
    filter_upwards [hcoe, hp_du] with x hx hx'
    rw [hx, hx']
    rfl
  · exact hweak.const_smul c

/--
%%handwave
name:
  Chart density preserves almost-everywhere equality
statement:
  In a chart for a smooth positive area measure, the pushed-forward area
  measure and Lebesgue measure on the chart target have the same null sets.
  Consequently they define the same almost-everywhere equality relation.
proof:
  The pushed-forward measure is Lebesgue measure restricted to the chart target
  with a smooth strictly positive density.  A strictly positive density is
  nonzero almost everywhere, so the weighted and unweighted measures are
  mutually absolutely continuous.
-/
theorem smoothPositiveAreaMeasureOnSurface_chart_ae_eq {X β : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (hμ : SmoothPositiveAreaMeasureOnSurface X μ)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    {f g : ℂ → β} :
    f =ᵐ[Measure.map e (μ.restrict e.source)] g ↔
      f =ᵐ[MeasureTheory.volume.restrict e.target] g := by
  obtain ⟨ρ, hρ_smooth, hρ_pos, hmap⟩ := hμ.chart_density e he
  rw [hmap]
  have hρ_aemeas :
      AEMeasurable (fun z : ℂ ↦ ENNReal.ofReal (ρ z))
        (MeasureTheory.volume.restrict e.target) := by
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      (hρ_smooth.continuousOn.aemeasurable e.open_target.measurableSet)
  have hρ_ne_zero :
      ∀ᵐ z ∂MeasureTheory.volume.restrict e.target,
        ENNReal.ofReal (ρ z) ≠ 0 := by
    exact ae_restrict_of_forall_mem e.open_target.measurableSet fun z hz ↦
      ne_of_gt (ENNReal.ofReal_pos.mpr (hρ_pos z hz))
  exact withDensity_ae_eq hρ_aemeas hρ_ne_zero

/--
%%handwave
name:
  Almost-everywhere measurability of inverse surface charts
statement:
  For a smooth positive area measure, an inverse surface chart is almost everywhere measurable for the chart pushforward measure.
proof:
  This is the manifold inverse-chart measurability result specialized to the surface model.
-/
theorem smoothPositiveAreaMeasureOnSurface_chart_symm_aemeasurable {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (hμ : SmoothPositiveAreaMeasureOnSurface X μ)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X) :
    AEMeasurable e.symm (Measure.map e (μ.restrict e.source)) := by
  obtain ⟨ρ, _hρ_smooth, _hρ_pos, hmap⟩ := hμ.chart_density e he
  have hsymm_vol :
      AEMeasurable e.symm (MeasureTheory.volume.restrict e.target) :=
    openPartialHomeomorph_symm_aemeasurable_restrict_target e MeasureTheory.volume
  have h_ac :
      Measure.map e (μ.restrict e.source) ≪
        MeasureTheory.volume.restrict e.target := by
    rw [hmap]
    exact withDensity_absolutelyContinuous _ _
  exact hsymm_vol.mono_ac h_ac

/--
%%handwave
name:
  A surface chart measure is inverted by its inverse chart
statement:
  Pushing the restricted surface measure into coordinates and then back through the inverse chart recovers the original restricted measure.
proof:
  Specialize the manifold chart pushforward--pullback identity to \(\mathbb C\).
-/
theorem smoothPositiveAreaMeasureOnSurface_chart_map_symm_map {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (hμ : SmoothPositiveAreaMeasureOnSurface X μ)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X) :
    Measure.map e.symm (Measure.map e (μ.restrict e.source)) =
      μ.restrict e.source := by
  have he_aemeas : AEMeasurable e (μ.restrict e.source) :=
    openPartialHomeomorph_aemeasurable_restrict_source e μ
  have hsymm_aemeas :
      AEMeasurable e.symm (Measure.map e (μ.restrict e.source)) :=
    smoothPositiveAreaMeasureOnSurface_chart_symm_aemeasurable μ hμ e he
  have hmap :
      Measure.map e.symm (Measure.map e (μ.restrict e.source)) =
        Measure.map (fun x : X ↦ e.symm (e x)) (μ.restrict e.source) := by
    simpa [Function.comp_def] using
      (AEMeasurable.map_map_of_aemeasurable hsymm_aemeas he_aemeas)
  have hleft :
      (fun x : X ↦ e.symm (e x)) =ᵐ[μ.restrict e.source] fun x ↦ x :=
    ae_restrict_of_forall_mem e.open_source.measurableSet fun x hx ↦
      e.left_inv hx
  calc
    Measure.map e.symm (Measure.map e (μ.restrict e.source))
        = Measure.map (fun x : X ↦ e.symm (e x)) (μ.restrict e.source) := hmap
    _ = Measure.map (fun x : X ↦ x) (μ.restrict e.source) :=
        Measure.map_congr hleft
    _ = μ.restrict e.source := by rw [Measure.map_id']

/--
%%handwave
name:
  Almost-everywhere equality pulls back to surface coordinates
statement:
  If (f=g) almost everywhere on a surface, then \(f\circ e^{-1}=g\circ e^{-1}\) for Lebesgue-almost every point of the chart target.
proof:
  Use the smooth positive chart density and the manifold pullback result in the surface model.
-/
theorem smoothPositiveAreaMeasureOnSurface_chart_comp_symm_ae_eq {X β : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (hμ : SmoothPositiveAreaMeasureOnSurface X μ)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    {f g : X → β} (hfg : f =ᵐ[μ] g) :
    (fun z : ℂ ↦ f (e.symm z)) =ᵐ[MeasureTheory.volume.restrict e.target]
      fun z ↦ g (e.symm z) := by
  have hfg_source : f =ᵐ[μ.restrict e.source] g :=
    ae_restrict_of_ae hfg
  have hsymm_aemeas :
      AEMeasurable e.symm (Measure.map e (μ.restrict e.source)) :=
    smoothPositiveAreaMeasureOnSurface_chart_symm_aemeasurable μ hμ e he
  have hmap_symm :
      Measure.map e.symm (Measure.map e (μ.restrict e.source)) =
        μ.restrict e.source :=
    smoothPositiveAreaMeasureOnSurface_chart_map_symm_map μ hμ e he
  have hcomp_map :
      (fun z : ℂ ↦ f (e.symm z)) =ᵐ[Measure.map e (μ.restrict e.source)]
        fun z ↦ g (e.symm z) := by
    have h_ac :
        Measure.map e.symm (Measure.map e (μ.restrict e.source)) ≪
          μ.restrict e.source := by
      rw [hmap_symm]
    simpa [Function.comp_def] using
      (ae_eq_comp' hsymm_aemeas hfg_source h_ac)
  exact (smoothPositiveAreaMeasureOnSurface_chart_ae_eq μ hμ e he).1 hcomp_map

/--
%%handwave
name:
  Weak-gradient identities do not depend on representatives
statement:
  For a smooth positive area measure, changing the function and cotangent field
  on a null set does not change the weak-gradient identity.
proof:
  The weak-gradient identity is tested in coordinate patches against compactly
  supported smooth functions.  The coordinate expression of a smooth positive
  area measure is mutually absolutely continuous with Lebesgue measure, so
  null changes for the area measure give null changes in every coordinate
  integral.  Replacing both representatives therefore leaves each tested
  distributional identity unchanged.
-/
theorem IsWeakGradientOnSurface.congr_ae {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [IsManifold SurfaceRealModel ∞ X]
    (μ : Measure X) (hμ : SmoothPositiveAreaMeasureOnSurface X μ)
    {u u' : X → ℝ} {du du' : X → ℂ →L[ℝ] ℝ}
    (hu : u =ᵐ[μ] u') (hdu : du =ᵐ[μ] du')
    (hweak : IsWeakGradientOnSurface μ u du) :
    IsWeakGradientOnSurface μ u' du' := by
  intro e he φ v
  rcases hweak e he φ v with ⟨hu_int, hdu_int, h_eq⟩
  let Ω : Set ℂ := surfaceChartRegion e (Set.univ : Set X)
  have hΩ_eq : Ω = e.target := by
    ext z
    simp [Ω, surfaceChartRegion]
  have hu_chart_target :
      (fun z : ℂ ↦ u (e.symm z)) =ᵐ[MeasureTheory.volume.restrict e.target]
        fun z ↦ u' (e.symm z) :=
    smoothPositiveAreaMeasureOnSurface_chart_comp_symm_ae_eq μ hμ e he hu
  have hdu_chart_target :
      (fun z : ℂ ↦ du (e.symm z)) =ᵐ[MeasureTheory.volume.restrict e.target]
        fun z ↦ du' (e.symm z) :=
    smoothPositiveAreaMeasureOnSurface_chart_comp_symm_ae_eq μ hμ e he hdu
  have hu_chart :
      (fun z : ℂ ↦ u (e.symm z)) =ᵐ[MeasureTheory.volume.restrict Ω]
        fun z ↦ u' (e.symm z) := by
    simpa [hΩ_eq] using hu_chart_target
  have hdu_chart :
      (fun z : ℂ ↦ du (e.symm z)) =ᵐ[MeasureTheory.volume.restrict Ω]
        fun z ↦ du' (e.symm z) := by
    simpa [hΩ_eq] using hdu_chart_target
  have hlhs_eq :
      (fun z ↦ u (e.symm z) * fderiv ℝ (φ : ℂ → ℝ) z v) =ᵐ[
        MeasureTheory.volume.restrict Ω]
        fun z ↦ u' (e.symm z) * fderiv ℝ (φ : ℂ → ℝ) z v := by
    filter_upwards [hu_chart] with z hz
    rw [hz]
  have hrhs_eq :
      (fun z ↦ du (e.symm z) (surfaceChartTangentMap e z v) * φ z) =ᵐ[
        MeasureTheory.volume.restrict Ω]
        fun z ↦ du' (e.symm z) (surfaceChartTangentMap e z v) * φ z := by
    filter_upwards [hdu_chart] with z hz
    rw [hz]
  constructor
  · simpa [Ω] using hu_int.congr hlhs_eq
  · constructor
    · simpa [Ω] using hdu_int.congr hrhs_eq
    · calc
        ∫ z in Ω,
            u' (e.symm z) * fderiv ℝ (φ : ℂ → ℝ) z v
              ∂MeasureTheory.volume
            = ∫ z in Ω,
                u (e.symm z) * fderiv ℝ (φ : ℂ → ℝ) z v
                  ∂MeasureTheory.volume := by
                exact (integral_congr_ae hlhs_eq).symm
        _ = -∫ z in Ω,
              du (e.symm z) (surfaceChartTangentMap e z v) * φ z
                ∂MeasureTheory.volume := by
                simpa [Ω] using h_eq
        _ = -∫ z in Ω,
              du' (e.symm z) (surfaceChartTangentMap e z v) * φ z
                ∂MeasureTheory.volume := by
                rw [integral_congr_ae hrhs_eq]

/--
%%handwave
name:
  Canonical representatives of a weak-gradient graph element
statement:
  If an \(L^2\) pair lies in the weak-gradient graph, then the canonical pointwise representatives of its two components satisfy the surface distributional weak-gradient identity.
proof:
  Replace the witnessing representatives by the canonical \(L^2\) representatives using almost-everywhere equality, pull those equalities into every chart, and use congruence of the test integrals.
-/
theorem weakGradientGraphOnSurface_canonical_representatives {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [IsManifold SurfaceRealModel ∞ X]
    (μ : Measure X) (hμ : SmoothPositiveAreaMeasureOnSurface X μ)
    {p : Lp ℝ 2 μ × Lp (ℂ →L[ℝ] ℝ) 2 μ}
    (hp : WeakGradientGraphOnSurface μ p) :
    IsWeakGradientOnSurface μ (fun x ↦ p.1 x) (fun x ↦ p.2 x) := by
  rcases hp with ⟨u, du, hp_u, hp_du, hweak⟩
  exact IsWeakGradientOnSurface.congr_ae μ hμ hp_u.symm hp_du.symm hweak

/--
%%handwave
name:
  Dual-tested weak derivatives do not depend on representatives
statement:
  Changing a vector-valued map and its coordinate differential on a null set
  does not change the dual-tested weak-derivative identities.
proof:
  Apply the scalar representative-independence theorem after composing with
  each continuous linear functional on the target.
-/
theorem IsWeakDerivativeOnSurfaceWithValuesByDual.congr_ae {X E : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [IsManifold SurfaceRealModel ∞ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X) (hμ : SmoothPositiveAreaMeasureOnSurface X μ)
    {u u' : X → E}
    {du du' : X → SurfaceDifferentialCoordinateHilbertFiber E}
    (hu : u =ᵐ[μ] u') (hdu : du =ᵐ[μ] du')
    (hweak : IsWeakDerivativeOnSurfaceWithValuesByDual μ u du) :
    IsWeakDerivativeOnSurfaceWithValuesByDual μ u' du' := by
  intro Λ
  refine IsWeakGradientOnSurface.congr_ae μ hμ ?_ ?_ (hweak Λ)
  · filter_upwards [hu] with x hx
    rw [hx]
  · filter_upwards [hdu] with x hx
    rw [hx]

/--
%%handwave
name:
  Canonical representatives of a vector-valued weak-derivative graph element
statement:
  If a Hilbert-valued \(L^2\) pair lies in the weak-derivative graph, its canonical value and coordinate-differential representatives satisfy the weak derivative identity after every scalar dual projection.
proof:
  For each target functional, replace the witnessing representatives by the canonical ones almost everywhere and invoke the scalar canonical-representative result.
-/
theorem weakDerivativeGraphOnSurfaceWithValues_canonical_representatives
    {X E : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [IsManifold SurfaceRealModel ∞ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X) (hμ : SmoothPositiveAreaMeasureOnSurface X μ)
    {p : Lp E 2 μ × Lp (SurfaceDifferentialCoordinateHilbertFiber E) 2 μ}
    (hp : WeakDerivativeGraphOnSurfaceWithValues μ p) :
    IsWeakDerivativeOnSurfaceWithValuesByDual μ
      (fun x ↦ p.1 x) (fun x ↦ p.2 x) := by
  rcases hp with ⟨u, du, hp_u, hp_du, hweak⟩
  exact IsWeakDerivativeOnSurfaceWithValuesByDual.congr_ae μ hμ
    hp_u.symm hp_du.symm hweak

/--
%%handwave
name:
  The real inner product is multiplication
statement:
  For real numbers \(a,b\), \(\langle a,b\rangle_{\mathbb R}=ab\).
proof:
  This is the standard real inner-product formula.
-/
private theorem real_inner_eq_mul (a b : ℝ) : inner ℝ a b = a * b := by
  calc
    inner ℝ a b = b * (starRingEnd ℝ) a := RCLike.inner_apply a b
    _ = a * b := by simp [mul_comm]

/--
%%handwave
name:
  Support of a derivative of a compactly supported coordinate test
statement:
  For a compactly supported smooth coordinate test \(\varphi\), the support of \(z\mapsto D\varphi(z)v\) is contained in its coordinate region.
proof:
  Outside the support of \(\varphi\), the function vanishes on a neighborhood, so its derivative vanishes there; the original support lies in the region.
-/
private theorem smoothCompactlySupportedCoordinateFunction_fderiv_apply_tsupport_subset
    {Ω : Set ℂ} (φ : SmoothCompactlySupportedCoordinateFunction Ω) (v : ℂ) :
    tsupport (fun z : ℂ ↦ fderiv ℝ (φ : ℂ → ℝ) z v) ⊆ Ω :=
  (tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := (φ : ℂ → ℝ)) v).trans
    φ.support_subset

/--
%%handwave
name:
  Compact support of a directional derivative test
statement:
  For a compactly supported smooth coordinate test \(\varphi\), the directional derivative \(z\mapsto D\varphi(z)v\) has compact support.
proof:
  Its support is closed and contained in the compact support of \(\varphi\).
-/
private theorem smoothCompactlySupportedCoordinateFunction_fderiv_apply_tsupport_isCompact
    {Ω : Set ℂ} (φ : SmoothCompactlySupportedCoordinateFunction Ω) (v : ℂ) :
    IsCompact (tsupport (fun z : ℂ ↦ fderiv ℝ (φ : ℂ → ℝ) z v)) :=
  φ.compact_support.of_isClosed_subset (isClosed_tsupport _)
    (tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := (φ : ℂ → ℝ)) v)

/--
%%handwave
name:
  \(L^2\) inner pairings are continuous
statement:
  Pairing an \(L^2\)-convergent sequence of Hilbert-valued functions with a
  fixed \(L^2\) Hilbert-valued function gives convergent integrals of the
  pointwise inner products, and the limiting pointwise inner product is
  integrable.
proof:
  This is continuity of the Hilbert-space inner product on \(L^2\), together
  with the formula expressing the \(L^2\) inner product as the integral of the
  pointwise inner product.
-/
theorem l2_inner_pairing_tendsto_of_tendsto_Lp
    {α E : Type} [MeasurableSpace α] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {μ : Measure α}
    {ι : Type} {l : Filter ι} {u : ι → Lp E 2 μ} {uLim θ : Lp E 2 μ}
    (hu_tendsto : Filter.Tendsto u l (𝓝 uLim)) :
    Integrable (fun x ↦ inner ℝ (uLim x) (θ x)) μ ∧
      Filter.Tendsto
        (fun i ↦ ∫ x, inner ℝ (u i x) (θ x) ∂μ)
        l
        (𝓝 (∫ x, inner ℝ (uLim x) (θ x) ∂μ)) := by
  have h_inner_tendsto :
      Filter.Tendsto (fun i ↦ inner ℝ (u i) θ) l (𝓝 (inner ℝ uLim θ)) :=
    hu_tendsto.inner tendsto_const_nhds
  constructor
  · exact L2.integrable_inner (𝕜 := ℝ) uLim θ
  · simpa [L2.inner_def] using h_inner_tendsto

/--
%%handwave
name:
  \(L^2\) pairings are continuous
statement:
  Pairing \(L^2\)-convergent real functions with a fixed \(L^2\) real
  function gives convergent integrals, and the limiting product is
  integrable.
proof:
  This is continuity of the Hilbert-space inner product on \(L^2\), together
  with the formula expressing the \(L^2\) inner product as the integral of the
  pointwise product.
-/
theorem l2_real_pairing_tendsto_of_tendsto_Lp
    {α : Type} [MeasurableSpace α] {μ : Measure α}
    {ι : Type} {l : Filter ι} {u : ι → Lp ℝ 2 μ} {uLim θ : Lp ℝ 2 μ}
    (hu_tendsto : Filter.Tendsto u l (𝓝 uLim)) :
    Integrable (fun x ↦ uLim x * θ x) μ ∧
      Filter.Tendsto
        (fun i ↦ ∫ x, u i x * θ x ∂μ)
        l
        (𝓝 (∫ x, uLim x * θ x ∂μ)) := by
  have h_integral_eq (w : Lp ℝ 2 μ) :
      (∫ x, inner ℝ (w x) (θ x) ∂μ) = ∫ x, w x * θ x ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards with x
    exact real_inner_eq_mul (w x) (θ x)
  have h_integrable :
      Integrable (fun x ↦ uLim x * θ x) μ := by
    have h_inner_integrable :
        Integrable (fun x ↦ inner ℝ (uLim x) (θ x)) μ :=
      L2.integrable_inner (𝕜 := ℝ) uLim θ
    convert h_inner_integrable using 1
    funext x
    exact (real_inner_eq_mul (uLim x) (θ x)).symm
  have h_inner_tendsto :
      Filter.Tendsto (fun i ↦ inner ℝ (u i) θ) l (𝓝 (inner ℝ uLim θ)) :=
    hu_tendsto.inner tendsto_const_nhds
  have h_inner_integral_tendsto :
      Filter.Tendsto
        (fun i ↦ ∫ x, inner ℝ (u i x) (θ x) ∂μ)
        l
        (𝓝 (∫ x, inner ℝ (uLim x) (θ x) ∂μ)) := by
    simpa [L2.inner_def] using h_inner_tendsto
  have h_seq_eq :
      (fun i ↦ ∫ x, inner ℝ (u i x) (θ x) ∂μ) =
        fun i ↦ ∫ x, u i x * θ x ∂μ := by
    funext i
    exact h_integral_eq (u i)
  constructor
  · exact h_integrable
  · simpa [h_seq_eq, h_integral_eq uLim, mul_comm] using h_inner_integral_tendsto

/--
%%handwave
name:
  Coordinate scalar test pairings have \(L^2\) representatives
statement:
  A compactly supported coordinate scalar test functional is represented by a
  fixed \(L^2\) surface function: pairing any \(L^2\) surface function against
  the coordinate derivative test equals its \(L^2\) pairing with this
  representative, and the coordinate product is integrable.
proof:
  In the chart, the smooth positive area measure has a smooth strictly positive
  density.  Dividing the compactly supported derivative test by this density and
  extending by zero gives the representing \(L^2\) surface function.  The
  change-of-variables formula for the chart identifies the two pairings.
-/
theorem coordinateScalarTestPairing_has_L2_surface_representer {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [IsManifold SurfaceRealModel ∞ X]
    (μ : Measure X) (hμ : SmoothPositiveAreaMeasureOnSurface X μ)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    (φ : SmoothCompactlySupportedCoordinateFunction
      (surfaceChartRegion e (Set.univ : Set X))) (v : ℂ) :
    ∃ θ : Lp ℝ 2 μ, ∀ w : Lp ℝ 2 μ,
      Integrable
          (fun z ↦ w (e.symm z) * fderiv ℝ (φ : ℂ → ℝ) z v)
          (MeasureTheory.volume.restrict (surfaceChartRegion e (Set.univ : Set X))) ∧
        (∫ z in surfaceChartRegion e (Set.univ : Set X),
            w (e.symm z) * fderiv ℝ (φ : ℂ → ℝ) z v ∂MeasureTheory.volume) =
          ∫ x, w x * θ x ∂μ := by
  classical
  let Ω : Set ℂ := surfaceChartRegion e (Set.univ : Set X)
  have hΩ_eq : Ω = e.target := by
    ext z
    simp [Ω, surfaceChartRegion]
  obtain ⟨ρ, hρ_smooth, hρ_pos, hmap⟩ := hμ.chart_density e he
  let ψ : ℂ → ℝ := fun z ↦ fderiv ℝ (φ : ℂ → ℝ) z v
  let q : ℂ → ℝ := fun z ↦ ψ z / ρ z
  let θ0 : X → ℝ := e.source.indicator fun x : X ↦ q (e x)
  have hψ_support : tsupport ψ ⊆ e.target := by
    intro z hz
    have hzΩ :
        z ∈ surfaceChartRegion e (Set.univ : Set X) := by
      exact smoothCompactlySupportedCoordinateFunction_fderiv_apply_tsupport_subset φ v hz
    simpa [surfaceChartRegion] using hzΩ
  have hψ_compact : IsCompact (tsupport ψ) := by
    simpa [ψ] using
      smoothCompactlySupportedCoordinateFunction_fderiv_apply_tsupport_isCompact φ v
  have hψ_cont : Continuous ψ := by
    have hpair :
        Continuous fun p : ℂ × ℂ ↦ (fderiv ℝ (φ : ℂ → ℝ) p.1 : ℂ →L[ℝ] ℝ) p.2 :=
      φ.smooth.continuous_fderiv_apply (by simp)
    simpa [ψ] using hpair.comp (continuous_id.prodMk continuous_const)
  have hq_cont : ContinuousOn q (tsupport ψ) := by
    have hρ_cont : ContinuousOn ρ (tsupport ψ) :=
      hρ_smooth.continuousOn.mono hψ_support
    have hρ_ne : ∀ z ∈ tsupport ψ, ρ z ≠ 0 := by
      intro z hz
      exact ne_of_gt (hρ_pos z (hψ_support hz))
    simpa [q] using hψ_cont.continuousOn.div hρ_cont hρ_ne
  obtain ⟨C, hC⟩ := hψ_compact.exists_bound_of_continuousOn hq_cont
  have hmap_ac :
      Measure.map e (μ.restrict e.source) ≪
        MeasureTheory.volume.restrict e.target := by
    rw [hmap]
    exact withDensity_absolutelyContinuous _ _
  have he_aemeas : AEMeasurable e (μ.restrict e.source) :=
    openPartialHomeomorph_aemeasurable_restrict_source e μ
  have hρ_aemeas_target :
      AEMeasurable ρ (MeasureTheory.volume.restrict e.target) :=
    hρ_smooth.continuousOn.aemeasurable e.open_target.measurableSet
  have hρ_aemeas_map :
      AEMeasurable ρ (Measure.map e (μ.restrict e.source)) :=
    hρ_aemeas_target.mono_ac hmap_ac
  have hq_aemeas_source :
      AEMeasurable (fun x : X ↦ q (e x)) (μ.restrict e.source) := by
    have hψ_aemeas_map :
        AEMeasurable ψ (Measure.map e (μ.restrict e.source)) :=
      hψ_cont.aemeasurable
    have hψ_comp :
        AEMeasurable (fun x : X ↦ ψ (e x)) (μ.restrict e.source) :=
      hψ_aemeas_map.comp_aemeasurable he_aemeas
    have hρ_comp :
        AEMeasurable (fun x : X ↦ ρ (e x)) (μ.restrict e.source) :=
      hρ_aemeas_map.comp_aemeasurable he_aemeas
    simpa [q] using hψ_comp.div hρ_comp
  have hθ0_aestrongly :
      AEStronglyMeasurable θ0 μ := by
    exact (aestronglyMeasurable_indicator_iff e.open_source.measurableSet).2
      hq_aemeas_source.aestronglyMeasurable
  have hθ0_bound : ∀ᵐ x ∂μ, ‖θ0 x‖ ≤ max C 0 := by
    refine Filter.Eventually.of_forall ?_
    intro x
    by_cases hx : x ∈ e.source
    · by_cases hxts : e x ∈ tsupport ψ
      · have hq_le : |q (e x)| ≤ C := hC (e x) hxts
        calc
          ‖θ0 x‖ = |q (e x)| := by simp [θ0, hx, Real.norm_eq_abs]
          _ ≤ C := hq_le
          _ ≤ max C 0 := le_max_left C 0
      · have hψ_zero : ψ (e x) = 0 :=
          image_eq_zero_of_notMem_tsupport hxts
        calc
          ‖θ0 x‖ = 0 := by simp [θ0, q, hx, hψ_zero]
          _ ≤ max C 0 := le_max_right C 0
    · calc
        ‖θ0 x‖ = 0 := by simp [θ0, hx]
        _ ≤ max C 0 := le_max_right C 0
  have hθ0_top : MemLp θ0 ∞ μ :=
    memLp_top_of_bound hθ0_aestrongly (max C 0) hθ0_bound
  let Ksurf : Set X := e.symm '' tsupport ψ
  have hKsurf_compact : IsCompact Ksurf := by
    dsimp [Ksurf]
    exact hψ_compact.image_of_continuousOn
      (e.continuousOn_symm.mono hψ_support)
  have hθ0_support : ∀ x : X, x ∉ Ksurf → θ0 x = 0 := by
    intro x hxK
    by_cases hx : x ∈ e.source
    · have hnot : e x ∉ tsupport ψ := by
        intro hex
        exact hxK ⟨e x, hex, by simpa using e.left_inv hx⟩
      have hψ_zero : ψ (e x) = 0 :=
        image_eq_zero_of_notMem_tsupport hnot
      simp [θ0, q, hx, hψ_zero]
    · simp [θ0, hx]
  have hKsurf_measure : μ Ksurf ≠ (∞ : ℝ≥0∞) :=
    hμ.finite_on_compact Ksurf hKsurf_compact
  have hθ0_mem : MemLp θ0 2 μ :=
    hθ0_top.mono_exponent_of_measure_support_ne_top
      hθ0_support hKsurf_measure (by simp)
  let θ : Lp ℝ 2 μ := hθ0_mem.toLp θ0
  refine ⟨θ, ?_⟩
  intro w
  let δ : ℂ → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (ρ z)
  let F : ℂ → ℝ := fun z ↦ w (e.symm z) * q z
  have hδ_aemeas :
      AEMeasurable δ (MeasureTheory.volume.restrict e.target) :=
    hρ_aemeas_target.ennreal_ofReal
  have hδ_lt_top :
      ∀ᵐ z ∂MeasureTheory.volume.restrict e.target, δ z < (∞ : ℝ≥0∞) :=
    Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top
  have hsymm_aemeas :
      AEMeasurable e.symm (Measure.map e (μ.restrict e.source)) :=
    smoothPositiveAreaMeasureOnSurface_chart_symm_aemeasurable μ hμ e he
  have hmap_symm :
      Measure.map e.symm (Measure.map e (μ.restrict e.source)) =
        μ.restrict e.source :=
    smoothPositiveAreaMeasureOnSurface_chart_map_symm_map μ hμ e he
  have hw_aemeas_source :
      AEMeasurable (fun x : X ↦ w x) (μ.restrict e.source) :=
    (Lp.memLp w).aestronglyMeasurable.aemeasurable.mono_measure Measure.restrict_le_self
  have hw_aemeas_map_symm :
      AEMeasurable (fun x : X ↦ w x)
        (Measure.map e.symm (Measure.map e (μ.restrict e.source))) := by
    simpa [hmap_symm] using hw_aemeas_source
  have hw_symm_aemeas :
      AEMeasurable (fun z : ℂ ↦ w (e.symm z))
        (Measure.map e (μ.restrict e.source)) :=
    hw_aemeas_map_symm.comp_aemeasurable hsymm_aemeas
  have hq_aemeas_map :
      AEMeasurable q (Measure.map e (μ.restrict e.source)) := by
    have hψ_aemeas_map :
        AEMeasurable ψ (Measure.map e (μ.restrict e.source)) :=
      hψ_cont.aemeasurable
    simpa [q] using hψ_aemeas_map.div hρ_aemeas_map
  have hF_aestrongly :
      AEStronglyMeasurable F (Measure.map e (μ.restrict e.source)) := by
    simpa [F] using (hw_symm_aemeas.mul hq_aemeas_map).aestronglyMeasurable
  have hθ_ae : (fun x : X ↦ θ x) =ᵐ[μ] θ0 :=
    hθ0_mem.coeFn_toLp
  have hsurface_int :
      Integrable (fun x : X ↦ w x * θ x) μ := by
    have hinner : Integrable (fun x : X ↦ inner ℝ (w x) (θ x)) μ :=
      L2.integrable_inner (𝕜 := ℝ) w θ
    convert hinner using 1
    funext x
    exact (real_inner_eq_mul (w x) (θ x)).symm
  have hsurface0_int :
      Integrable (fun x : X ↦ w x * θ0 x) μ :=
    hsurface_int.congr (by
      filter_upwards [hθ_ae] with x hxθ
      rw [hxθ])
  have hsource_int :
      Integrable (fun x : X ↦ w x * q (e x)) (μ.restrict e.source) := by
    have hres := hsurface0_int.restrict (s := e.source)
    refine hres.congr ?_
    exact ae_restrict_of_forall_mem e.open_source.measurableSet fun x hx ↦ by
      simp [θ0, hx]
  have hF_comp_int :
      Integrable (fun x : X ↦ F (e x)) (μ.restrict e.source) := by
    refine hsource_int.congr ?_
    exact ae_restrict_of_forall_mem e.open_source.measurableSet fun x hx ↦ by
      simp [F, q, e.left_inv hx]
  have hF_map_int :
      Integrable F (Measure.map e (μ.restrict e.source)) :=
    (integrable_map_measure hF_aestrongly he_aemeas).2 hF_comp_int
  have hF_density_int :
      Integrable F ((MeasureTheory.volume.restrict e.target).withDensity δ) := by
    simpa [hmap, δ] using hF_map_int
  have hδF_int :
      Integrable (fun z : ℂ ↦ (δ z).toReal • F z)
        (MeasureTheory.volume.restrict e.target) :=
    (integrable_withDensity_iff_integrable_smul₀'
      hδ_aemeas hδ_lt_top).1 hF_density_int
  have hchart_int_target :
      Integrable (fun z : ℂ ↦ w (e.symm z) * ψ z)
        (MeasureTheory.volume.restrict e.target) := by
    refine hδF_int.congr ?_
    filter_upwards [ae_restrict_mem e.open_target.measurableSet] with z hz
    have hρ_nonneg : 0 ≤ ρ z := le_of_lt (hρ_pos z hz)
    have hρ_ne : ρ z ≠ 0 := ne_of_gt (hρ_pos z hz)
    calc
      (δ z).toReal • F z =
          ρ z * (w (e.symm z) * (ψ z / ρ z)) := by
            simp [F, q, δ, ENNReal.toReal_ofReal hρ_nonneg]
      _ = w (e.symm z) * ψ z := by
            field_simp [hρ_ne]
  have hchart_int :
      Integrable
          (fun z ↦ w (e.symm z) * fderiv ℝ (φ : ℂ → ℝ) z v)
          (MeasureTheory.volume.restrict (surfaceChartRegion e (Set.univ : Set X))) := by
    simpa [Ω, hΩ_eq, ψ] using hchart_int_target
  have hsurface_eq_source :
      (∫ x, w x * θ0 x ∂μ) =
        ∫ x, w x * q (e x) ∂(μ.restrict e.source) := by
    calc
      ∫ x, w x * θ0 x ∂μ
          = ∫ x in e.source, w x * θ0 x ∂μ := by
              refine (setIntegral_eq_integral_of_forall_compl_eq_zero
                (μ := μ) (s := e.source) (f := fun x : X ↦ w x * θ0 x) ?_).symm
              intro x hx
              simp [θ0, hx]
      _ = ∫ x, w x * q (e x) ∂(μ.restrict e.source) := by
              refine integral_congr_ae ?_
              exact ae_restrict_of_forall_mem e.open_source.measurableSet fun x hx ↦ by
                simp [θ0, hx]
  have hsource_eq_map :
      (∫ x, w x * q (e x) ∂(μ.restrict e.source)) =
        ∫ z, F z ∂Measure.map e (μ.restrict e.source) := by
    calc
      ∫ x, w x * q (e x) ∂(μ.restrict e.source)
          = ∫ x, F (e x) ∂(μ.restrict e.source) := by
              refine integral_congr_ae ?_
              exact ae_restrict_of_forall_mem e.open_source.measurableSet fun x hx ↦ by
                simp [F, e.left_inv hx]
      _ = ∫ z, F z ∂Measure.map e (μ.restrict e.source) :=
              (integral_map he_aemeas hF_aestrongly).symm
  have hmap_eq_chart :
      (∫ z, F z ∂Measure.map e (μ.restrict e.source)) =
        ∫ z in e.target, w (e.symm z) * ψ z ∂MeasureTheory.volume := by
    calc
      ∫ z, F z ∂Measure.map e (μ.restrict e.source)
          = ∫ z, F z ∂(MeasureTheory.volume.restrict e.target).withDensity δ := by
              simp [hmap, δ]
      _ = ∫ z, (δ z).toReal • F z ∂MeasureTheory.volume.restrict e.target := by
              rw [integral_withDensity_eq_integral_toReal_smul₀ hδ_aemeas hδ_lt_top]
      _ = ∫ z in e.target, w (e.symm z) * ψ z ∂MeasureTheory.volume := by
              refine integral_congr_ae ?_
              filter_upwards [ae_restrict_mem e.open_target.measurableSet] with z hz
              have hρ_nonneg : 0 ≤ ρ z := le_of_lt (hρ_pos z hz)
              have hρ_ne : ρ z ≠ 0 := ne_of_gt (hρ_pos z hz)
              calc
                (δ z).toReal • F z =
                    ρ z * (w (e.symm z) * (ψ z / ρ z)) := by
                      simp [F, q, δ, ENNReal.toReal_ofReal hρ_nonneg]
                _ = w (e.symm z) * ψ z := by
                      field_simp [hρ_ne]
  have hsurface_eq_chart :
      (∫ x, w x * θ0 x ∂μ) =
        ∫ z in e.target, w (e.symm z) * ψ z ∂MeasureTheory.volume :=
    hsurface_eq_source.trans (hsource_eq_map.trans hmap_eq_chart)
  have hsurfaceθ_eq_surface0 :
      (∫ x, w x * θ x ∂μ) = ∫ x, w x * θ0 x ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hθ_ae] with x hxθ
    rw [hxθ]
  constructor
  · exact hchart_int
  · calc
      ∫ z in surfaceChartRegion e (Set.univ : Set X),
          w (e.symm z) * fderiv ℝ (φ : ℂ → ℝ) z v ∂MeasureTheory.volume
          = ∫ z in e.target, w (e.symm z) * ψ z ∂MeasureTheory.volume := by
              simp [Ω, hΩ_eq, ψ]
      _ = ∫ x, w x * θ0 x ∂μ := hsurface_eq_chart.symm
      _ = ∫ x, w x * θ x ∂μ := hsurfaceθ_eq_surface0.symm

/--
%%handwave
name:
  Coordinate scalar test pairings are continuous from their \(L^2\) representative
statement:
  Once a coordinate scalar test pairing is represented by a fixed \(L^2\)
  surface function, its values are continuous under \(L^2\) convergence.
proof:
  Apply continuity of \(L^2\) pairings with the representing function, then use
  the representation identity for each approximating function and for the
  limit.
-/
theorem coordinateScalarTestPairing_tendsto_of_L2_surface_representer {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [IsManifold SurfaceRealModel ∞ X]
    (μ : Measure X)
    {ι : Type} {l : Filter ι} [l.NeBot]
    {u : ι → Lp ℝ 2 μ} {uLim θ : Lp ℝ 2 μ}
    (hu_tendsto : Filter.Tendsto u l (𝓝 uLim))
    (e : OpenPartialHomeomorph X ℂ)
    (φ : SmoothCompactlySupportedCoordinateFunction
      (surfaceChartRegion e (Set.univ : Set X))) (v : ℂ)
    (hθ : ∀ w : Lp ℝ 2 μ,
      Integrable
          (fun z ↦ w (e.symm z) * fderiv ℝ (φ : ℂ → ℝ) z v)
          (MeasureTheory.volume.restrict (surfaceChartRegion e (Set.univ : Set X))) ∧
        (∫ z in surfaceChartRegion e (Set.univ : Set X),
            w (e.symm z) * fderiv ℝ (φ : ℂ → ℝ) z v ∂MeasureTheory.volume) =
          ∫ x, w x * θ x ∂μ) :
    Integrable
        (fun z ↦ uLim (e.symm z) * fderiv ℝ (φ : ℂ → ℝ) z v)
        (MeasureTheory.volume.restrict (surfaceChartRegion e (Set.univ : Set X))) ∧
      Filter.Tendsto
        (fun i ↦
          ∫ z in surfaceChartRegion e (Set.univ : Set X),
            u i (e.symm z) * fderiv ℝ (φ : ℂ → ℝ) z v ∂MeasureTheory.volume)
        l
        (𝓝 (∫ z in surfaceChartRegion e (Set.univ : Set X),
            uLim (e.symm z) * fderiv ℝ (φ : ℂ → ℝ) z v ∂MeasureTheory.volume)) := by
  rcases hθ uLim with ⟨huLim_int, huLim_eq⟩
  rcases l2_real_pairing_tendsto_of_tendsto_Lp
      (u := u) (uLim := uLim) (θ := θ) hu_tendsto with
    ⟨_hsurface_int, hsurface_tendsto⟩
  have hseq_eq :
      (fun i ↦
          ∫ z in surfaceChartRegion e (Set.univ : Set X),
            u i (e.symm z) * fderiv ℝ (φ : ℂ → ℝ) z v ∂MeasureTheory.volume) =
        fun i ↦ ∫ x, u i x * θ x ∂μ := by
    funext i
    exact (hθ (u i)).2
  constructor
  · exact huLim_int
  · simpa [hseq_eq, huLim_eq] using hsurface_tendsto

/--
%%handwave
name:
  Coordinate scalar test pairings are continuous under \(L^2\) convergence
statement:
  If real-valued \(L^2\) functions converge in \(L^2\), then pairing their
  coordinate representatives with the derivative of a fixed compactly
  supported smooth test function converges to the corresponding limiting
  pairing.  The limiting pairing is integrable.
proof:
  The derivative of the test function is bounded and compactly supported.
  On this compact support the smooth positive area measure is comparable with
  coordinate Lebesgue measure.  Cauchy--Schwarz therefore bounds the difference
  of the coordinate pairings by a fixed local constant times the \(L^2\)
  distance of the surface functions.
-/
theorem coordinateScalarTestPairing_tendsto_of_tendsto_Lp {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [IsManifold SurfaceRealModel ∞ X]
    (μ : Measure X) (hμ : SmoothPositiveAreaMeasureOnSurface X μ)
    {ι : Type} {l : Filter ι} [l.NeBot]
    {u : ι → Lp ℝ 2 μ} {uLim : Lp ℝ 2 μ}
    (hu_tendsto : Filter.Tendsto u l (𝓝 uLim))
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    (φ : SmoothCompactlySupportedCoordinateFunction
      (surfaceChartRegion e (Set.univ : Set X))) (v : ℂ) :
    Integrable
        (fun z ↦ uLim (e.symm z) * fderiv ℝ (φ : ℂ → ℝ) z v)
        (MeasureTheory.volume.restrict (surfaceChartRegion e (Set.univ : Set X))) ∧
      Filter.Tendsto
        (fun i ↦
          ∫ z in surfaceChartRegion e (Set.univ : Set X),
            u i (e.symm z) * fderiv ℝ (φ : ℂ → ℝ) z v ∂MeasureTheory.volume)
        l
        (𝓝 (∫ z in surfaceChartRegion e (Set.univ : Set X),
            uLim (e.symm z) * fderiv ℝ (φ : ℂ → ℝ) z v ∂MeasureTheory.volume)) := by
  rcases coordinateScalarTestPairing_has_L2_surface_representer μ hμ e he φ v with
    ⟨θ, hθ⟩
  exact coordinateScalarTestPairing_tendsto_of_L2_surface_representer
    μ hu_tendsto e φ v hθ

private noncomputable def coordinateCotangentTestRieszField {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : OpenPartialHomeomorph X ℂ) (ρ : ℂ → ℝ)
    (φ : SmoothCompactlySupportedCoordinateFunction
      (surfaceChartRegion e (Set.univ : Set X))) (v : ℂ) :
    ℂ → ℂ →L[ℝ] ℝ :=
  fun z : ℂ ↦
    (φ z / ρ z) •
      (InnerProductSpace.toDual ℝ ℂ) (surfaceChartTangentMap e z v)

/--
%%handwave
name:
  Continuity of the chart tangent map in a fixed direction
statement:
  Under continuous preferred tangent coordinates, \(z\mapsto D(e^{-1})(z)v\) is continuous on the target of every surface chart.
proof:
  Translate continuity of the preferred tangent coordinate field through the chart trivialization.
-/
private theorem surfaceChartTangentMap_apply_continuousOn {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    [SecondCountableTopology X] [IsManifold SurfaceRealModel ∞ X]
    (hcoord : ContinuousPreferredTangentCoordinatesOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X) (v : ℂ) :
    ContinuousOn (fun z : ℂ ↦ surfaceChartTangentMap e z v) e.target := by
  exact hcoord e he v

/--
%%handwave
name:
  Continuity of the coordinate cotangent Riesz test field
statement:
  If \(\rho>0\) is smooth and \(\varphi\) is a smooth compactly supported test, then
  \[
    z\mapsto \frac{\varphi(z)}{\rho(z)}\big(D(e^{-1})(z)v\big)^\flat
  \]
  is continuous on the chart target.
proof:
  The tangent vector field is continuous, division by the positive smooth density is continuous, and the Riesz map and scalar multiplication are continuous.
-/
private theorem coordinateCotangentTestRieszField_continuousOn_target {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    [SecondCountableTopology X] [IsManifold SurfaceRealModel ∞ X]
    (hcoord : ContinuousPreferredTangentCoordinatesOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    (ρ : ℂ → ℝ)
    (hρ_smooth : ContDiffOn ℝ ∞ ρ e.target)
    (hρ_pos : ∀ z ∈ e.target, 0 < ρ z)
    (φ : SmoothCompactlySupportedCoordinateFunction
      (surfaceChartRegion e (Set.univ : Set X))) (v : ℂ) :
    ContinuousOn (coordinateCotangentTestRieszField e ρ φ v) e.target := by
  have hφ_cont : Continuous (φ : ℂ → ℝ) :=
    φ.smooth.continuous
  have hρ_cont : ContinuousOn ρ e.target :=
    hρ_smooth.continuousOn
  have hρ_ne : ∀ z ∈ e.target, ρ z ≠ 0 := by
    intro z hz
    exact ne_of_gt (hρ_pos z hz)
  have hscalar_cont : ContinuousOn (fun z : ℂ ↦ φ z / ρ z) e.target :=
    hφ_cont.continuousOn.div hρ_cont hρ_ne
  have htangent_cont :
      ContinuousOn (fun z : ℂ ↦ surfaceChartTangentMap e z v) e.target :=
    surfaceChartTangentMap_apply_continuousOn hcoord e he v
  have hdual_cont :
      Continuous (fun w : ℂ ↦ (InnerProductSpace.toDual ℝ ℂ) w) :=
    (InnerProductSpace.toDual ℝ ℂ).continuous
  have hdual_tangent_cont :
      ContinuousOn
        (fun z : ℂ ↦
          (InnerProductSpace.toDual ℝ ℂ) (surfaceChartTangentMap e z v))
        e.target :=
    hdual_cont.continuousOn.comp htangent_cont (fun _ hz ↦ Set.mem_univ _)
  simpa [coordinateCotangentTestRieszField] using
    hscalar_cont.smul hdual_tangent_cont

set_option maxHeartbeats 800000 in
/--
%%handwave
name:
  Measurability and boundedness of the coordinate cotangent test field
statement:
  The coordinate cotangent Riesz test field is almost everywhere measurable for the chart measure and is uniformly bounded on the compact support of the test function.
proof:
  Continuity on the chart target gives measurability; compactness of the support gives a finite maximum of its norm.
-/
private theorem coordinateCotangentTestRieszField_aemeasurable_bounded {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [IsManifold SurfaceRealModel ∞ X]
    (μ : Measure X) (hμ : SmoothPositiveAreaMeasureOnSurface X μ)
    (hcoord : ContinuousPreferredTangentCoordinatesOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    (ρ : ℂ → ℝ)
    (hρ_smooth : ContDiffOn ℝ ∞ ρ e.target)
    (hρ_pos : ∀ z ∈ e.target, 0 < ρ z)
    (φ : SmoothCompactlySupportedCoordinateFunction
      (surfaceChartRegion e (Set.univ : Set X))) (v : ℂ) :
    AEMeasurable (coordinateCotangentTestRieszField e ρ φ v)
        (Measure.map e (μ.restrict e.source)) ∧
      ∃ C : ℝ, ∀ z ∈ tsupport (φ : ℂ → ℝ),
        ‖coordinateCotangentTestRieszField e ρ φ v z‖ ≤ C := by
  classical
  obtain ⟨ρμ, hρμ_smooth, hρμ_pos, hmapμ⟩ := hμ.chart_density e he
  have hmap_ac :
      Measure.map e (μ.restrict e.source) ≪
        MeasureTheory.volume.restrict e.target := by
    rw [hmapμ]
    exact withDensity_absolutelyContinuous _ _
  have hq_cont_target :
      ContinuousOn (coordinateCotangentTestRieszField e ρ φ v) e.target :=
    coordinateCotangentTestRieszField_continuousOn_target
      hcoord e he ρ hρ_smooth hρ_pos φ v
  have hq_aemeas_target :
      AEMeasurable (coordinateCotangentTestRieszField e ρ φ v)
        (MeasureTheory.volume.restrict e.target) :=
    hq_cont_target.aemeasurable e.open_target.measurableSet
  have hφ_support : tsupport (φ : ℂ → ℝ) ⊆ e.target := by
    intro z hz
    have hzΩ :
        z ∈ surfaceChartRegion e (Set.univ : Set X) :=
      φ.support_subset hz
    simpa [surfaceChartRegion] using hzΩ
  have hK_compact : IsCompact (tsupport (φ : ℂ → ℝ)) :=
    φ.compact_support
  have hq_cont_support :
      ContinuousOn (coordinateCotangentTestRieszField e ρ φ v)
        (tsupport (φ : ℂ → ℝ)) :=
    hq_cont_target.mono hφ_support
  obtain ⟨C, hC⟩ :=
    hK_compact.exists_bound_of_continuousOn hq_cont_support
  exact ⟨hq_aemeas_target.mono_ac hmap_ac, C, hC⟩

/--
%%handwave
name:
  Finite chart measure of a compact test support
statement:
  The chart pushforward measure of the compact support of a coordinate test is finite.
proof:
  Map the compact support back to a compact subset of the surface and use finiteness of a smooth positive measure on compact sets.
-/
private theorem coordinateCotangentTestRieszField_map_tsupport_measure_ne_top {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [IsManifold SurfaceRealModel ∞ X]
    (μ : Measure X) (hμ : SmoothPositiveAreaMeasureOnSurface X μ)
    (e : OpenPartialHomeomorph X ℂ)
    (φ : SmoothCompactlySupportedCoordinateFunction
      (surfaceChartRegion e (Set.univ : Set X))) :
    Measure.map e (μ.restrict e.source) (tsupport (φ : ℂ → ℝ)) ≠
      (∞ : ℝ≥0∞) := by
  classical
  let K : Set ℂ := tsupport (φ : ℂ → ℝ)
  have he_aemeas : AEMeasurable e (μ.restrict e.source) :=
    openPartialHomeomorph_aemeasurable_restrict_source e μ
  have hφ_support : K ⊆ e.target := by
    intro z hz
    have hzΩ :
        z ∈ surfaceChartRegion e (Set.univ : Set X) :=
      φ.support_subset (by simpa [K] using hz)
    simpa [surfaceChartRegion] using hzΩ
  have hK_compact : IsCompact K := by
    simpa [K] using φ.compact_support
  have hK_meas : MeasurableSet K := by
    simpa [K] using (isClosed_tsupport (φ : ℂ → ℝ)).measurableSet
  let Ksurf : Set X := e.symm '' K
  have hKsurf_compact : IsCompact Ksurf := by
    dsimp [Ksurf]
    exact hK_compact.image_of_continuousOn
      (e.continuousOn_symm.mono hφ_support)
  have hKsurf_measure : μ Ksurf ≠ (∞ : ℝ≥0∞) :=
    hμ.finite_on_compact Ksurf hKsurf_compact
  have hpre_subset : e ⁻¹' K ∩ e.source ⊆ Ksurf := by
    intro x hx
    exact ⟨e x, hx.1, by simpa using e.left_inv hx.2⟩
  have hmapK_eq :
      Measure.map e (μ.restrict e.source) K =
        μ.restrict e.source (e ⁻¹' K) := by
    exact Measure.map_apply_of_aemeasurable he_aemeas hK_meas
  have hrestrict_eq :
      μ.restrict e.source (e ⁻¹' K) =
        μ ((e ⁻¹' K) ∩ e.source) := by
    exact Measure.restrict_apply' e.open_source.measurableSet
  have hle : Measure.map e (μ.restrict e.source) K ≤ μ Ksurf := by
    rw [hmapK_eq, hrestrict_eq]
    exact measure_mono hpre_subset
  have hlt : Measure.map e (μ.restrict e.source) K < (∞ : ℝ≥0∞) :=
    lt_of_le_of_lt hle (lt_top_iff_ne_top.2 hKsurf_measure)
  exact by
    simpa [K] using ne_of_lt hlt

set_option maxHeartbeats 800000 in
/--
%%handwave
name:
  A bounded cotangent test field is \(L^2\) on its compact support
statement:
  An almost everywhere measurable coordinate cotangent test field that is bounded on the test support belongs to \(L^2\) for the chart measure restricted to that support.
proof:
  The restricted support has finite measure, and an almost everywhere strongly measurable bounded function is in every finite \(L^p\).
-/
private theorem coordinateCotangentTestRieszField_memLp_restrict_tsupport_of_aemeasurable_bounded
    {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [IsManifold SurfaceRealModel ∞ X]
    (μ : Measure X) (hμ : SmoothPositiveAreaMeasureOnSurface X μ)
    (e : OpenPartialHomeomorph X ℂ) (ρ : ℂ → ℝ)
    (φ : SmoothCompactlySupportedCoordinateFunction
      (surfaceChartRegion e (Set.univ : Set X))) (v : ℂ)
    (hq_aemeas_map : AEMeasurable (coordinateCotangentTestRieszField e ρ φ v)
      (Measure.map e (μ.restrict e.source)))
    (hbound : ∃ C : ℝ, ∀ z ∈ tsupport (φ : ℂ → ℝ),
      ‖coordinateCotangentTestRieszField e ρ φ v z‖ ≤ C) :
    MemLp (coordinateCotangentTestRieszField e ρ φ v) 2
      ((Measure.map e (μ.restrict e.source)).restrict (tsupport (φ : ℂ → ℝ))) := by
  classical
  let q : ℂ → ℂ →L[ℝ] ℝ :=
    coordinateCotangentTestRieszField e ρ φ v
  let K : Set ℂ := tsupport (φ : ℂ → ℝ)
  rcases hbound with ⟨C, hC⟩
  have hmapK_ne :
      Measure.map e (μ.restrict e.source) K ≠ (∞ : ℝ≥0∞) := by
    simpa [K] using
      coordinateCotangentTestRieszField_map_tsupport_measure_ne_top
        μ hμ e φ
  haveI :
      IsFiniteMeasure ((Measure.map e (μ.restrict e.source)).restrict K) :=
    isFiniteMeasure_restrict.2 hmapK_ne
  have hq_aestrong :
      AEStronglyMeasurable q (Measure.map e (μ.restrict e.source)) := by
    simpa [q] using hq_aemeas_map.aestronglyMeasurable
  have hq_bound :
      ∀ᵐ z ∂(Measure.map e (μ.restrict e.source)).restrict K,
        ‖q z‖ ≤ max C 0 := by
    refine Filter.Eventually.of_forall ?_
    intro z
    by_cases hz : z ∈ K
    · exact (hC z (by simpa [K] using hz)).trans (le_max_left C 0)
    · have hφ_zero : φ z = 0 :=
        image_eq_zero_of_notMem_tsupport (by simpa [K] using hz)
      have hq_zero : q z = 0 := by
        dsimp [q, coordinateCotangentTestRieszField]
        rw [hφ_zero, zero_div, zero_smul]
      calc
        ‖q z‖ = 0 := by simp [hq_zero]
        _ ≤ max C 0 := le_max_right C 0
  have hq_restrict :
      MemLp q 2 ((Measure.map e (μ.restrict e.source)).restrict K) :=
    MemLp.of_bound hq_aestrong.restrict (max C 0) hq_bound
  simpa [q, K] using hq_restrict

/--
%%handwave
name:
  The support indicator does not change the coordinate cotangent test field
statement:
  Multiplying the coordinate cotangent Riesz test field by the indicator of the test support leaves it unchanged.
proof:
  Inside the support the indicator is one; outside it the test function, hence the whole Riesz field, is zero.
-/
private theorem coordinateCotangentTestRieszField_tsupport_indicator_eq_self {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : OpenPartialHomeomorph X ℂ) (ρ : ℂ → ℝ)
    (φ : SmoothCompactlySupportedCoordinateFunction
      (surfaceChartRegion e (Set.univ : Set X))) (v : ℂ) :
    (tsupport (φ : ℂ → ℝ)).indicator
        (coordinateCotangentTestRieszField e ρ φ v) =
      coordinateCotangentTestRieszField e ρ φ v := by
  ext z
  by_cases hz : z ∈ tsupport (φ : ℂ → ℝ)
  · simp [Set.indicator_of_mem hz]
  · have hφ_zero : φ z = 0 :=
      image_eq_zero_of_notMem_tsupport hz
    dsimp [coordinateCotangentTestRieszField]
    simp [Set.indicator_of_notMem hz, hφ_zero]

set_option maxHeartbeats 600000 in
/--
%%handwave
name:
  The supported coordinate cotangent test field is \(L^2\) for chart measure
statement:
  Under measurability and boundedness on the compact test support, the support-indicated coordinate cotangent test field belongs to \(L^2\) for the full chart measure.
proof:
  Use \(L^2\)-membership for the restricted measure and the equality between an indicator norm and restriction to its measurable support.
-/
private theorem coordinateCotangentTestRieszField_tsupport_indicator_memLp_map_of_aemeasurable_bounded
    {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [IsManifold SurfaceRealModel ∞ X]
    (μ : Measure X) (hμ : SmoothPositiveAreaMeasureOnSurface X μ)
    (e : OpenPartialHomeomorph X ℂ) (ρ : ℂ → ℝ)
    (φ : SmoothCompactlySupportedCoordinateFunction
      (surfaceChartRegion e (Set.univ : Set X))) (v : ℂ)
    (hq_aemeas_map : AEMeasurable (coordinateCotangentTestRieszField e ρ φ v)
      (Measure.map e (μ.restrict e.source)))
    (hbound : ∃ C : ℝ, ∀ z ∈ tsupport (φ : ℂ → ℝ),
      ‖coordinateCotangentTestRieszField e ρ φ v z‖ ≤ C) :
    MemLp ((tsupport (φ : ℂ → ℝ)).indicator
        (coordinateCotangentTestRieszField e ρ φ v)) 2
      (Measure.map e (μ.restrict e.source)) := by
  classical
  let q : ℂ → ℂ →L[ℝ] ℝ :=
    coordinateCotangentTestRieszField e ρ φ v
  let K : Set ℂ := tsupport (φ : ℂ → ℝ)
  have hK_meas : MeasurableSet K := by
    simpa [K] using (isClosed_tsupport (φ : ℂ → ℝ)).measurableSet
  have hq_restrict :
      MemLp q 2 ((Measure.map e (μ.restrict e.source)).restrict K) :=
    by
      simpa [q, K] using
        coordinateCotangentTestRieszField_memLp_restrict_tsupport_of_aemeasurable_bounded
          μ hμ e ρ φ v hq_aemeas_map hbound
  have hq_indicator_mem :
      MemLp (K.indicator q) 2 (Measure.map e (μ.restrict e.source)) :=
    ⟨(aestronglyMeasurable_indicator_iff hK_meas).2
        hq_restrict.aestronglyMeasurable,
      by
        have hnorm :
            eLpNorm (K.indicator q) 2
                (Measure.map e (μ.restrict e.source)) =
              eLpNorm q 2
                ((Measure.map e (μ.restrict e.source)).restrict K) :=
          eLpNorm_indicator_eq_eLpNorm_restrict
            (f := q) (p := (2 : ℝ≥0∞))
            (μ := Measure.map e (μ.restrict e.source)) hK_meas
        simpa [hnorm] using hq_restrict.eLpNorm_lt_top⟩
  simpa [q, K] using hq_indicator_mem

set_option maxHeartbeats 3000000 in
set_option synthInstance.maxHeartbeats 200000 in
/--
%%handwave
name:
  The pulled-back cotangent test field is \(L^2\) on the surface
statement:
  The chart-source indicator of a measurable bounded coordinate cotangent test field pulled back by the chart belongs to surface \(L^2\).
proof:
  Compose the chart-space \(L^2\) indicator with the chart map, use the pushforward measure identity, and convert restriction to a source indicator.
-/
private theorem coordinateCotangentTestRieszField_indicator_memLp_of_aemeasurable_bounded {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [IsManifold SurfaceRealModel ∞ X]
    (μ : Measure X) (hμ : SmoothPositiveAreaMeasureOnSurface X μ)
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
    (ρ : ℂ → ℝ)
    (_hρ_smooth : ContDiffOn ℝ ∞ ρ e.target)
    (_hρ_pos : ∀ z ∈ e.target, 0 < ρ z)
    (φ : SmoothCompactlySupportedCoordinateFunction
      (surfaceChartRegion e (Set.univ : Set X))) (v : ℂ)
    (hq_aemeas_map : AEMeasurable (coordinateCotangentTestRieszField e ρ φ v)
      (Measure.map e (μ.restrict e.source)))
    (hbound : ∃ C : ℝ, ∀ z ∈ tsupport (φ : ℂ → ℝ),
      ‖coordinateCotangentTestRieszField e ρ φ v z‖ ≤ C) :
    MemLp
        (e.source.indicator fun x : X ↦
          coordinateCotangentTestRieszField e ρ φ v (e x))
        2 μ := by
  classical
  let q : ℂ → ℂ →L[ℝ] ℝ :=
    coordinateCotangentTestRieszField e ρ φ v
  have he_aemeas : AEMeasurable e (μ.restrict e.source) :=
    openPartialHomeomorph_aemeasurable_restrict_source e μ
  have hq_indicator_mem_map :
      MemLp
        ((tsupport (φ : ℂ → ℝ)).indicator
          (coordinateCotangentTestRieszField e ρ φ v)) 2
        (Measure.map e (μ.restrict e.source)) :=
    by
      simpa [q] using
        coordinateCotangentTestRieszField_tsupport_indicator_memLp_map_of_aemeasurable_bounded
          μ hμ e ρ φ v hq_aemeas_map hbound
  have hcomp_indicator_mem :
      MemLp
        (fun x : X ↦
          ((tsupport (φ : ℂ → ℝ)).indicator
            (coordinateCotangentTestRieszField e ρ φ v)) (e x))
        2 (μ.restrict e.source) :=
    hq_indicator_mem_map.comp_of_map he_aemeas
  have hq_indicator :
      (tsupport (φ : ℂ → ℝ)).indicator
          (coordinateCotangentTestRieszField e ρ φ v) =
        coordinateCotangentTestRieszField e ρ φ v :=
    coordinateCotangentTestRieszField_tsupport_indicator_eq_self e ρ φ v
  have hcomp_mem : MemLp (fun x : X ↦ q (e x)) 2 (μ.restrict e.source) := by
    simpa [q, hq_indicator] using hcomp_indicator_mem
  exact
    (memLp_indicator_iff_restrict
      (f := fun x : X ↦ coordinateCotangentTestRieszField e ρ φ v (e x))
      (p := (2 : ℝ≥0∞)) (μ := μ) e.open_source.measurableSet).2
      (by simpa [q] using hcomp_mem)

/--
%%handwave
name:
  Measurable \(L^2\) Riesz representative for a coordinate cotangent test
statement:
  The density-corrected cotangent Riesz test is almost everywhere measurable in coordinates, and its chart pullback extended by zero is an \(L^2\) cotangent field on the surface.
proof:
  Combine continuity and compact-support boundedness of the test field with the preceding chart-to-surface \(L^2\) transfer.
-/
private theorem coordinateCotangentTestRieszField_aemeasurable_memLp {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [IsManifold SurfaceRealModel ∞ X]
    (μ : Measure X) (hμ : SmoothPositiveAreaMeasureOnSurface X μ)
    (hcoord : ContinuousPreferredTangentCoordinatesOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    (ρ : ℂ → ℝ)
    (hρ_smooth : ContDiffOn ℝ ∞ ρ e.target)
    (hρ_pos : ∀ z ∈ e.target, 0 < ρ z)
    (φ : SmoothCompactlySupportedCoordinateFunction
      (surfaceChartRegion e (Set.univ : Set X))) (v : ℂ) :
    AEMeasurable
        (fun z : ℂ ↦
          (φ z / ρ z) •
            (InnerProductSpace.toDual ℝ ℂ) (surfaceChartTangentMap e z v))
        (Measure.map e (μ.restrict e.source)) ∧
      MemLp
        (e.source.indicator fun x : X ↦
          (φ (e x) / ρ (e x)) •
            (InnerProductSpace.toDual ℝ ℂ) (surfaceChartTangentMap e (e x) v))
        2 μ := by
  rcases coordinateCotangentTestRieszField_aemeasurable_bounded
      μ hμ hcoord e he ρ hρ_smooth hρ_pos φ v with
    ⟨hq_aemeas_map, hbound⟩
  constructor
  · simpa [coordinateCotangentTestRieszField] using hq_aemeas_map
  · simpa [coordinateCotangentTestRieszField] using
      coordinateCotangentTestRieszField_indicator_memLp_of_aemeasurable_bounded
        μ hμ e he ρ hρ_smooth hρ_pos φ v hq_aemeas_map hbound

/--
%%handwave
name:
  Coordinate cotangent test pairings have \(L^2\) representatives
statement:
  A compactly supported coordinate cotangent test functional is represented by a
  fixed \(L^2\) cotangent field: pairing any \(L^2\) cotangent field with the
  coordinate tangent test equals its \(L^2\) inner product with this
  representative, and the coordinate product is integrable.
proof:
  In a chart, the smooth positive area measure has a smooth strictly positive
  density.  The test function and the chart tangent vector determine, by the
  Riesz representation theorem in the cotangent fiber, a compactly supported
  \(L^2\) cotangent representative after division by this density.  The chart
  change-of-variables formula identifies the coordinate and surface pairings.
-/
theorem coordinateCotangentTestPairing_has_L2_surface_representer {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [IsManifold SurfaceRealModel ∞ X]
    (μ : Measure X) (hμ : SmoothPositiveAreaMeasureOnSurface X μ)
    (hcoord : ContinuousPreferredTangentCoordinatesOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    (φ : SmoothCompactlySupportedCoordinateFunction
      (surfaceChartRegion e (Set.univ : Set X))) (v : ℂ) :
    ∃ Θ : Lp (ℂ →L[ℝ] ℝ) 2 μ, ∀ w : Lp (ℂ →L[ℝ] ℝ) 2 μ,
      Integrable
          (fun z ↦ w (e.symm z) (surfaceChartTangentMap e z v) * φ z)
          (MeasureTheory.volume.restrict (surfaceChartRegion e (Set.univ : Set X))) ∧
        (∫ z in surfaceChartRegion e (Set.univ : Set X),
            w (e.symm z) (surfaceChartTangentMap e z v) * φ z
              ∂MeasureTheory.volume) =
          ∫ x, inner ℝ (w x) (Θ x) ∂μ := by
  classical
  let Ω : Set ℂ := surfaceChartRegion e (Set.univ : Set X)
  have hΩ_eq : Ω = e.target := by
    ext z
    simp [Ω, surfaceChartRegion]
  obtain ⟨ρ, hρ_smooth, hρ_pos, hmap⟩ := hμ.chart_density e he
  let q : ℂ → ℂ →L[ℝ] ℝ :=
    fun z ↦
      (φ z / ρ z) •
        (InnerProductSpace.toDual ℝ ℂ) (surfaceChartTangentMap e z v)
  let Θ0 : X → ℂ →L[ℝ] ℝ := e.source.indicator fun x : X ↦ q (e x)
  rcases coordinateCotangentTestRieszField_aemeasurable_memLp
      μ hμ hcoord e he ρ hρ_smooth hρ_pos φ v with
    ⟨hq_aemeas_map, hΘ0_mem⟩
  have hΘ0_mem' : MemLp Θ0 2 μ := by
    simpa [Θ0, q] using hΘ0_mem
  let Θ : Lp (ℂ →L[ℝ] ℝ) 2 μ := hΘ0_mem'.toLp Θ0
  refine ⟨Θ, ?_⟩
  intro w
  let δ : ℂ → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (ρ z)
  let F : ℂ → ℝ := fun z ↦ inner ℝ (w (e.symm z)) (q z)
  have hmap_ac :
      Measure.map e (μ.restrict e.source) ≪
        MeasureTheory.volume.restrict e.target := by
    rw [hmap]
    exact withDensity_absolutelyContinuous _ _
  have hρ_aemeas_target :
      AEMeasurable ρ (MeasureTheory.volume.restrict e.target) :=
    hρ_smooth.continuousOn.aemeasurable e.open_target.measurableSet
  have hδ_aemeas :
      AEMeasurable δ (MeasureTheory.volume.restrict e.target) :=
    hρ_aemeas_target.ennreal_ofReal
  have hδ_lt_top :
      ∀ᵐ z ∂MeasureTheory.volume.restrict e.target, δ z < (∞ : ℝ≥0∞) :=
    Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top
  have he_aemeas : AEMeasurable e (μ.restrict e.source) :=
    openPartialHomeomorph_aemeasurable_restrict_source e μ
  have hsymm_aemeas :
      AEMeasurable e.symm (Measure.map e (μ.restrict e.source)) :=
    smoothPositiveAreaMeasureOnSurface_chart_symm_aemeasurable μ hμ e he
  have hmap_symm :
      Measure.map e.symm (Measure.map e (μ.restrict e.source)) =
        μ.restrict e.source :=
    smoothPositiveAreaMeasureOnSurface_chart_map_symm_map μ hμ e he
  have hw_aemeas_source :
      AEMeasurable (fun x : X ↦ w x) (μ.restrict e.source) :=
    (Lp.memLp w).aestronglyMeasurable.aemeasurable.mono_measure Measure.restrict_le_self
  have hw_aemeas_map_symm :
      AEMeasurable (fun x : X ↦ w x)
        (Measure.map e.symm (Measure.map e (μ.restrict e.source))) := by
    simpa [hmap_symm] using hw_aemeas_source
  have hw_symm_aemeas :
      AEMeasurable (fun z : ℂ ↦ w (e.symm z))
        (Measure.map e (μ.restrict e.source)) :=
    hw_aemeas_map_symm.comp_aemeasurable hsymm_aemeas
  have hq_aemeas_map' :
      AEMeasurable q (Measure.map e (μ.restrict e.source)) := by
    simpa [q] using hq_aemeas_map
  have hF_aestrongly :
      AEStronglyMeasurable F (Measure.map e (μ.restrict e.source)) := by
    simpa [F] using
      (hw_symm_aemeas.aestronglyMeasurable.inner hq_aemeas_map'.aestronglyMeasurable)
  have hΘ_ae : (fun x : X ↦ Θ x) =ᵐ[μ] Θ0 :=
    hΘ0_mem'.coeFn_toLp
  have hsurface_int :
      Integrable (fun x : X ↦ inner ℝ (w x) (Θ x)) μ :=
    L2.integrable_inner (𝕜 := ℝ) w Θ
  have hsurface0_int :
      Integrable (fun x : X ↦ inner ℝ (w x) (Θ0 x)) μ :=
    hsurface_int.congr (by
      filter_upwards [hΘ_ae] with x hxΘ
      rw [hxΘ])
  have hsource_int :
      Integrable (fun x : X ↦ inner ℝ (w x) (q (e x))) (μ.restrict e.source) := by
    have hres := hsurface0_int.restrict (s := e.source)
    refine hres.congr ?_
    exact ae_restrict_of_forall_mem e.open_source.measurableSet fun x hx ↦ by
      simp [Θ0, hx]
  have hF_comp_int :
      Integrable (fun x : X ↦ F (e x)) (μ.restrict e.source) := by
    refine hsource_int.congr ?_
    exact ae_restrict_of_forall_mem e.open_source.measurableSet fun x hx ↦ by
      simp [F, e.left_inv hx]
  have hF_map_int :
      Integrable F (Measure.map e (μ.restrict e.source)) :=
    (integrable_map_measure hF_aestrongly he_aemeas).2 hF_comp_int
  have hF_density_int :
      Integrable F ((MeasureTheory.volume.restrict e.target).withDensity δ) := by
    simpa [hmap, δ] using hF_map_int
  have hδF_int :
      Integrable (fun z : ℂ ↦ (δ z).toReal • F z)
        (MeasureTheory.volume.restrict e.target) :=
    (integrable_withDensity_iff_integrable_smul₀'
      hδ_aemeas hδ_lt_top).1 hF_density_int
  have hchart_int_target :
      Integrable
        (fun z : ℂ ↦ w (e.symm z) (surfaceChartTangentMap e z v) * φ z)
        (MeasureTheory.volume.restrict e.target) := by
    refine hδF_int.congr ?_
    filter_upwards [ae_restrict_mem e.open_target.measurableSet] with z hz
    have hρ_nonneg : 0 ≤ ρ z := le_of_lt (hρ_pos z hz)
    have hρ_ne : ρ z ≠ 0 := ne_of_gt (hρ_pos z hz)
    have hinnerq :
        inner ℝ (w (e.symm z)) (q z) =
          (φ z / ρ z) * w (e.symm z) (surfaceChartTangentMap e z v) := by
      simpa [q] using
        cotangent_inner_smul_toDual_eq_mul_eval
          (w (e.symm z)) (φ z / ρ z) (surfaceChartTangentMap e z v)
    calc
      (δ z).toReal • F z =
          ρ z * inner ℝ (w (e.symm z)) (q z) := by
            simp [F, δ, ENNReal.toReal_ofReal hρ_nonneg]
      _ = ρ z * ((φ z / ρ z) *
            w (e.symm z) (surfaceChartTangentMap e z v)) := by
            rw [hinnerq]
      _ = w (e.symm z) (surfaceChartTangentMap e z v) * φ z := by
            field_simp [hρ_ne]
  have hchart_int :
      Integrable
          (fun z ↦ w (e.symm z) (surfaceChartTangentMap e z v) * φ z)
          (MeasureTheory.volume.restrict (surfaceChartRegion e (Set.univ : Set X))) := by
    simpa [Ω, hΩ_eq] using hchart_int_target
  have hsurface_eq_source :
      (∫ x, inner ℝ (w x) (Θ0 x) ∂μ) =
        ∫ x, inner ℝ (w x) (q (e x)) ∂(μ.restrict e.source) := by
    calc
      ∫ x, inner ℝ (w x) (Θ0 x) ∂μ
          = ∫ x in e.source, inner ℝ (w x) (Θ0 x) ∂μ := by
              refine (setIntegral_eq_integral_of_forall_compl_eq_zero
                (μ := μ) (s := e.source)
                (f := fun x : X ↦ inner ℝ (w x) (Θ0 x)) ?_).symm
              intro x hx
              simp [Θ0, hx]
      _ = ∫ x, inner ℝ (w x) (q (e x)) ∂(μ.restrict e.source) := by
              refine integral_congr_ae ?_
              exact ae_restrict_of_forall_mem e.open_source.measurableSet fun x hx ↦ by
                simp [Θ0, hx]
  have hsource_eq_map :
      (∫ x, inner ℝ (w x) (q (e x)) ∂(μ.restrict e.source)) =
        ∫ z, F z ∂Measure.map e (μ.restrict e.source) := by
    calc
      ∫ x, inner ℝ (w x) (q (e x)) ∂(μ.restrict e.source)
          = ∫ x, F (e x) ∂(μ.restrict e.source) := by
              refine integral_congr_ae ?_
              exact ae_restrict_of_forall_mem e.open_source.measurableSet fun x hx ↦ by
                simp [F, e.left_inv hx]
      _ = ∫ z, F z ∂Measure.map e (μ.restrict e.source) :=
              (integral_map he_aemeas hF_aestrongly).symm
  have hmap_eq_chart :
      (∫ z, F z ∂Measure.map e (μ.restrict e.source)) =
        ∫ z in e.target,
          w (e.symm z) (surfaceChartTangentMap e z v) * φ z
            ∂MeasureTheory.volume := by
    calc
      ∫ z, F z ∂Measure.map e (μ.restrict e.source)
          = ∫ z, F z ∂(MeasureTheory.volume.restrict e.target).withDensity δ := by
              simp [hmap, δ]
      _ = ∫ z, (δ z).toReal • F z ∂MeasureTheory.volume.restrict e.target := by
              rw [integral_withDensity_eq_integral_toReal_smul₀ hδ_aemeas hδ_lt_top]
      _ = ∫ z in e.target,
            w (e.symm z) (surfaceChartTangentMap e z v) * φ z
              ∂MeasureTheory.volume := by
              refine integral_congr_ae ?_
              filter_upwards [ae_restrict_mem e.open_target.measurableSet] with z hz
              have hρ_nonneg : 0 ≤ ρ z := le_of_lt (hρ_pos z hz)
              have hρ_ne : ρ z ≠ 0 := ne_of_gt (hρ_pos z hz)
              have hinnerq :
                  inner ℝ (w (e.symm z)) (q z) =
                    (φ z / ρ z) *
                      w (e.symm z) (surfaceChartTangentMap e z v) := by
                simpa [q] using
                  cotangent_inner_smul_toDual_eq_mul_eval
                    (w (e.symm z)) (φ z / ρ z) (surfaceChartTangentMap e z v)
              calc
                (δ z).toReal • F z =
                    ρ z * inner ℝ (w (e.symm z)) (q z) := by
                      simp [F, δ, ENNReal.toReal_ofReal hρ_nonneg]
                _ = ρ z * ((φ z / ρ z) *
                      w (e.symm z) (surfaceChartTangentMap e z v)) := by
                      rw [hinnerq]
                _ = w (e.symm z) (surfaceChartTangentMap e z v) * φ z := by
                      field_simp [hρ_ne]
  have hsurface_eq_chart :
      (∫ x, inner ℝ (w x) (Θ0 x) ∂μ) =
        ∫ z in e.target,
          w (e.symm z) (surfaceChartTangentMap e z v) * φ z
            ∂MeasureTheory.volume :=
    hsurface_eq_source.trans (hsource_eq_map.trans hmap_eq_chart)
  have hsurfaceΘ_eq_surface0 :
      (∫ x, inner ℝ (w x) (Θ x) ∂μ) =
        ∫ x, inner ℝ (w x) (Θ0 x) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hΘ_ae] with x hxΘ
    rw [hxΘ]
  constructor
  · exact hchart_int
  · calc
      ∫ z in surfaceChartRegion e (Set.univ : Set X),
          w (e.symm z) (surfaceChartTangentMap e z v) * φ z
            ∂MeasureTheory.volume
          = ∫ z in e.target,
              w (e.symm z) (surfaceChartTangentMap e z v) * φ z
                ∂MeasureTheory.volume := by
              simp [Ω, hΩ_eq]
      _ = ∫ x, inner ℝ (w x) (Θ0 x) ∂μ := hsurface_eq_chart.symm
      _ = ∫ x, inner ℝ (w x) (Θ x) ∂μ := hsurfaceΘ_eq_surface0.symm

/--
%%handwave
name:
  Coordinate cotangent test pairings are continuous from their \(L^2\) representative
statement:
  Once a coordinate cotangent test pairing is represented by a fixed \(L^2\)
  cotangent field, its values are continuous under \(L^2\) convergence.
proof:
  Apply continuity of Hilbert-valued \(L^2\) inner pairings with the representing
  cotangent field, then use the representation identity for each approximating
  field and for the limit.
-/
theorem coordinateCotangentTestPairing_tendsto_of_L2_surface_representer {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [IsManifold SurfaceRealModel ∞ X]
    (μ : Measure X)
    {ι : Type} {l : Filter ι} [l.NeBot]
    {du : ι → Lp (ℂ →L[ℝ] ℝ) 2 μ}
    {duLim Θ : Lp (ℂ →L[ℝ] ℝ) 2 μ}
    (hdu_tendsto : Filter.Tendsto du l (𝓝 duLim))
    (e : OpenPartialHomeomorph X ℂ)
    (φ : SmoothCompactlySupportedCoordinateFunction
      (surfaceChartRegion e (Set.univ : Set X))) (v : ℂ)
    (hΘ : ∀ w : Lp (ℂ →L[ℝ] ℝ) 2 μ,
      Integrable
          (fun z ↦ w (e.symm z) (surfaceChartTangentMap e z v) * φ z)
          (MeasureTheory.volume.restrict (surfaceChartRegion e (Set.univ : Set X))) ∧
        (∫ z in surfaceChartRegion e (Set.univ : Set X),
            w (e.symm z) (surfaceChartTangentMap e z v) * φ z
              ∂MeasureTheory.volume) =
          ∫ x, inner ℝ (w x) (Θ x) ∂μ) :
    Integrable
        (fun z ↦ duLim (e.symm z) (surfaceChartTangentMap e z v) * φ z)
        (MeasureTheory.volume.restrict (surfaceChartRegion e (Set.univ : Set X))) ∧
      Filter.Tendsto
        (fun i ↦
          ∫ z in surfaceChartRegion e (Set.univ : Set X),
            du i (e.symm z) (surfaceChartTangentMap e z v) * φ z
              ∂MeasureTheory.volume)
        l
        (𝓝 (∫ z in surfaceChartRegion e (Set.univ : Set X),
            duLim (e.symm z) (surfaceChartTangentMap e z v) * φ z
              ∂MeasureTheory.volume)) := by
  rcases hΘ duLim with ⟨hduLim_int, hduLim_eq⟩
  rcases l2_inner_pairing_tendsto_of_tendsto_Lp
      (u := du) (uLim := duLim) (θ := Θ) hdu_tendsto with
    ⟨_hsurface_int, hsurface_tendsto⟩
  have hseq_eq :
      (fun i ↦
          ∫ z in surfaceChartRegion e (Set.univ : Set X),
            du i (e.symm z) (surfaceChartTangentMap e z v) * φ z
              ∂MeasureTheory.volume) =
        fun i ↦ ∫ x, inner ℝ (du i x) (Θ x) ∂μ := by
    funext i
    exact (hΘ (du i)).2
  constructor
  · exact hduLim_int
  · simpa [hseq_eq, hduLim_eq] using hsurface_tendsto

/--
%%handwave
name:
  Coordinate cotangent test pairings are continuous under \(L^2\) convergence
statement:
  If \(L^2\) cotangent fields converge in \(L^2\), then pairing their
  coordinate components with a fixed compactly supported smooth test function
  converges to the corresponding limiting pairing.  The limiting pairing is
  integrable.
proof:
  The test function and the chart tangent map are bounded on the compact
  support of the test function.  On that compact set the coordinate measure
  and the smooth positive area measure are comparable.  Cauchy--Schwarz then
  controls the pairing difference by a fixed local constant times the \(L^2\)
  distance of the cotangent fields.
-/
theorem coordinateCotangentTestPairing_tendsto_of_tendsto_Lp {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [IsManifold SurfaceRealModel ∞ X]
    (μ : Measure X) (hμ : SmoothPositiveAreaMeasureOnSurface X μ)
    (hcoord : ContinuousPreferredTangentCoordinatesOnSurface X)
    {ι : Type} {l : Filter ι} [l.NeBot]
    {du : ι → Lp (ℂ →L[ℝ] ℝ) 2 μ}
    {duLim : Lp (ℂ →L[ℝ] ℝ) 2 μ}
    (hdu_tendsto : Filter.Tendsto du l (𝓝 duLim))
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    (φ : SmoothCompactlySupportedCoordinateFunction
      (surfaceChartRegion e (Set.univ : Set X))) (v : ℂ) :
    Integrable
        (fun z ↦ duLim (e.symm z) (surfaceChartTangentMap e z v) * φ z)
        (MeasureTheory.volume.restrict (surfaceChartRegion e (Set.univ : Set X))) ∧
      Filter.Tendsto
        (fun i ↦
          ∫ z in surfaceChartRegion e (Set.univ : Set X),
            du i (e.symm z) (surfaceChartTangentMap e z v) * φ z
              ∂MeasureTheory.volume)
        l
        (𝓝 (∫ z in surfaceChartRegion e (Set.univ : Set X),
            duLim (e.symm z) (surfaceChartTangentMap e z v) * φ z
              ∂MeasureTheory.volume)) := by
  rcases coordinateCotangentTestPairing_has_L2_surface_representer μ hμ hcoord e he φ v with
    ⟨Θ, hΘ⟩
  exact coordinateCotangentTestPairing_tendsto_of_L2_surface_representer
    μ hdu_tendsto e φ v hΘ

/--
%%handwave
name:
  Weak gradients pass to \(L^2\) limits
statement:
  If functions and cotangent fields converge in \(L^2\), and the cotangent
  fields are weak gradients eventually along a nontrivial filter, then the
  limiting cotangent field is the weak gradient of the limiting function.
proof:
  Test the weak-gradient identities against a fixed compactly supported smooth
  coordinate function and a fixed tangent vector.  The multiplier coming from
  the test function and its derivative is bounded with compact support.  Hence
  Cauchy--Schwarz bounds the difference of each pairing by the relevant
  \(L^2\)-distance times a finite local constant.  Both pairings therefore
  converge, so the distributional identity passes to the limit.
-/
theorem isWeakGradientOnSurface_of_tendsto_Lp {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [IsManifold SurfaceRealModel ∞ X]
    (μ : Measure X) (hμ : SmoothPositiveAreaMeasureOnSurface X μ)
    (hcoord : ContinuousPreferredTangentCoordinatesOnSurface X)
    {ι : Type} {l : Filter ι} [l.NeBot]
    {u : ι → Lp ℝ 2 μ} {du : ι → Lp (ℂ →L[ℝ] ℝ) 2 μ}
    {uLim : Lp ℝ 2 μ} {duLim : Lp (ℂ →L[ℝ] ℝ) 2 μ}
    (hweak : ∀ᶠ i in l,
      IsWeakGradientOnSurface μ (fun x ↦ u i x) (fun x ↦ du i x))
    (hu_tendsto : Filter.Tendsto u l (𝓝 uLim))
    (hdu_tendsto : Filter.Tendsto du l (𝓝 duLim)) :
    IsWeakGradientOnSurface μ (fun x ↦ uLim x) (fun x ↦ duLim x) := by
  intro e he φ v
  let Ω : Set ℂ := surfaceChartRegion e (Set.univ : Set X)
  let L : ι → ℝ :=
    fun i ↦
      ∫ z in Ω, u i (e.symm z) * fderiv ℝ (φ : ℂ → ℝ) z v
        ∂MeasureTheory.volume
  let R : ι → ℝ :=
    fun i ↦
      ∫ z in Ω, du i (e.symm z) (surfaceChartTangentMap e z v) * φ z
        ∂MeasureTheory.volume
  let Llim : ℝ :=
    ∫ z in Ω, uLim (e.symm z) * fderiv ℝ (φ : ℂ → ℝ) z v
      ∂MeasureTheory.volume
  let Rlim : ℝ :=
    ∫ z in Ω, duLim (e.symm z) (surfaceChartTangentMap e z v) * φ z
      ∂MeasureTheory.volume
  rcases coordinateScalarTestPairing_tendsto_of_tendsto_Lp μ hμ
      hu_tendsto e he φ v with
    ⟨huLim_int, hL_tendsto⟩
  rcases coordinateCotangentTestPairing_tendsto_of_tendsto_Lp μ hμ
      hcoord hdu_tendsto e he φ v with
    ⟨hduLim_int, hR_tendsto⟩
  have hweak_eq_eventually : ∀ᶠ i in l, L i = -R i := by
    filter_upwards [hweak] with i hi
    simpa [L, R, Ω] using (hi e he φ v).2.2
  have hnegR_tendsto_to_Llim :
      Filter.Tendsto (fun i ↦ -R i) l (𝓝 Llim) := by
    exact Filter.Tendsto.congr' hweak_eq_eventually (by simpa [L, Llim, Ω] using hL_tendsto)
  have hnegR_tendsto_to_neg_Rlim :
      Filter.Tendsto (fun i ↦ -R i) l (𝓝 (-Rlim)) := by
    have hR_tendsto' : Filter.Tendsto R l (𝓝 Rlim) := by
      simpa [R, Rlim, Ω] using hR_tendsto
    exact hR_tendsto'.neg
  have hlim_eq : Llim = -Rlim :=
    tendsto_nhds_unique hnegR_tendsto_to_Llim hnegR_tendsto_to_neg_Rlim
  refine ⟨?_, ?_, ?_⟩
  · simpa [Ω] using huLim_int
  · simpa [Ω] using hduLim_int
  · simpa [Llim, Rlim, Ω] using hlim_eq

/--
%%handwave
name:
  Weak-gradient graph membership is stable under \(L^2\) limits
statement:
  If a net of weak-gradient pairs converges in the product \(L^2\) topology, then its limit is again a weak-gradient pair.
proof:
  Use canonical representatives, pass both compactly supported test pairings to the limit by local \(L^2\) bounds, and use uniqueness of limits to retain the distributional identity.
-/
theorem weakGradientGraphOnSurface_mem_of_tendsto {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [IsManifold SurfaceRealModel ∞ X]
    (μ : Measure X) (hμ : SmoothPositiveAreaMeasureOnSurface X μ)
    (hcoord : ContinuousPreferredTangentCoordinatesOnSurface X)
    {ι : Type} {l : Filter ι} [l.NeBot]
    {p : ι → Lp ℝ 2 μ × Lp (ℂ →L[ℝ] ℝ) 2 μ}
    {q : Lp ℝ 2 μ × Lp (ℂ →L[ℝ] ℝ) 2 μ}
    (hp : ∀ᶠ i in l, WeakGradientGraphOnSurface μ (p i))
    (hp_tendsto : Filter.Tendsto p l (𝓝 q)) :
    WeakGradientGraphOnSurface μ q := by
  have hweak_eventually :
      ∀ᶠ i in l,
        IsWeakGradientOnSurface μ (fun x ↦ (p i).1 x) (fun x ↦ (p i).2 x) :=
    hp.mono fun _i hi =>
      weakGradientGraphOnSurface_canonical_representatives μ hμ hi
  have hfst : Filter.Tendsto (fun i ↦ (p i).1) l (𝓝 q.1) :=
    hp_tendsto.fst_nhds
  have hsnd : Filter.Tendsto (fun i ↦ (p i).2) l (𝓝 q.2) :=
    hp_tendsto.snd_nhds
  have hweak :
      IsWeakGradientOnSurface μ (fun x ↦ q.1 x) (fun x ↦ q.2 x) :=
    isWeakGradientOnSurface_of_tendsto_Lp μ hμ hcoord hweak_eventually hfst hsnd
  refine ⟨fun x ↦ q.1 x, fun x ↦ q.2 x, ?_, ?_, hweak⟩
  · exact Filter.EventuallyEq.rfl
  · exact Filter.EventuallyEq.rfl

/--
%%handwave
name:
  Weak-gradient graph is closed
statement:
  For a smooth positive area measure, the weak-gradient graph is closed in
  the product \(L^2\) topology.
proof:
  If \(u_n\to u\) and \(\omega_n\to\omega\) in \(L^2\), and
  \(\omega_n\) is the weak gradient of \(u_n\), pass the distributional
  identity to the limit against every compactly supported coordinate test.
  Cauchy--Schwarz on the compact support controls the pairings, and the smooth
  positive area measure is locally comparable with coordinate Lebesgue
  measure.
-/
theorem weakGradientGraphOnSurface_isClosed {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [IsManifold SurfaceRealModel ∞ X]
    (μ : Measure X) (hμ : SmoothPositiveAreaMeasureOnSurface X μ)
    (hcoord : ContinuousPreferredTangentCoordinatesOnSurface X) :
    IsClosed
      {p : Lp ℝ 2 μ × Lp (ℂ →L[ℝ] ℝ) 2 μ |
        WeakGradientGraphOnSurface μ p} := by
  refine isClosed_iff_forall_filter.2 ?_
  intro q F hF_ne hF_graph hF_lim
  haveI : F.NeBot := hF_ne
  have hgraph_eventually :
      ∀ᶠ y in F, WeakGradientGraphOnSurface μ y :=
    hF_graph (by simp)
  have hid_tendsto :
      Filter.Tendsto
        (fun y : Lp ℝ 2 μ × Lp (ℂ →L[ℝ] ℝ) 2 μ ↦ y) F (𝓝 q) := by
    simpa using hF_lim
  exact weakGradientGraphOnSurface_mem_of_tendsto μ hμ hcoord hgraph_eventually hid_tendsto

/--
%%handwave
name:
  Scalar projection of a Hilbert-valued first-order \(L^2\) pair
statement:
  A continuous linear functional on the target sends a Hilbert-valued
  first-order \(L^2\) pair to the scalar \(L^2\) pair obtained by applying the
  functional to the value and differential components.
-/
noncomputable def weakDerivativeGraphWithValuesScalarProjectionCLM {X E : Type}
    [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X) (Λ : E →L[ℝ] ℝ) :
    (Lp E 2 μ × Lp (SurfaceDifferentialCoordinateHilbertFiber E) 2 μ) →L[ℝ]
      (Lp ℝ 2 μ × Lp (ℂ →L[ℝ] ℝ) 2 μ) :=
  ((Λ.compLpL (p := (2 : ℝ≥0∞)) μ).comp
      (ContinuousLinearMap.fst ℝ
        (Lp E 2 μ) (Lp (SurfaceDifferentialCoordinateHilbertFiber E) 2 μ))).prod
    (((SurfaceDifferentialCoordinateHilbertFiber.dualProjectionCLM Λ).compLpL
        (p := (2 : ℝ≥0∞)) μ).comp
      (ContinuousLinearMap.snd ℝ
        (Lp E 2 μ) (Lp (SurfaceDifferentialCoordinateHilbertFiber E) 2 μ)))

/--
%%handwave
name:
  Canonical first component of scalar projection
statement:
  Applying a target functional \(\Lambda\) to the value component of an \(L^2\) pair agrees almost everywhere with the first component produced by the induced scalar projection operator.
proof:
  This is the pointwise almost-everywhere formula for composition of an \(L^2\) function with a continuous linear map.
-/
private theorem weakDerivativeGraphWithValuesScalarProjectionCLM_fst_ae
    {X E : Type} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X) (Λ : E →L[ℝ] ℝ)
    (p : Lp E 2 μ × Lp (SurfaceDifferentialCoordinateHilbertFiber E) 2 μ) :
    (fun x ↦ (weakDerivativeGraphWithValuesScalarProjectionCLM μ Λ p).1 x) =ᵐ[μ]
      fun x ↦ Λ (p.1 x) := by
  simpa [weakDerivativeGraphWithValuesScalarProjectionCLM] using
    (Λ.coeFn_compLpL (p := (2 : ℝ≥0∞)) p.1)

/--
%%handwave
name:
  Canonical second component of scalar projection
statement:
  The second component produced by scalar projection agrees almost everywhere with pointwise composition of the coordinate differential by \(\Lambda\).
proof:
  Apply the almost-everywhere evaluation formula for the induced continuous linear map on \(L^2\).
-/
private theorem weakDerivativeGraphWithValuesScalarProjectionCLM_snd_ae
    {X E : Type} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X) (Λ : E →L[ℝ] ℝ)
    (p : Lp E 2 μ × Lp (SurfaceDifferentialCoordinateHilbertFiber E) 2 μ) :
    (fun x ↦ (weakDerivativeGraphWithValuesScalarProjectionCLM μ Λ p).2 x) =ᵐ[μ]
      fun x ↦
        SurfaceDifferentialCoordinateHilbertFiber.dualProjectionCLM Λ (p.2 x) := by
  simpa [weakDerivativeGraphWithValuesScalarProjectionCLM] using
    ((SurfaceDifferentialCoordinateHilbertFiber.dualProjectionCLM Λ).coeFn_compLpL
      (p := (2 : ℝ≥0∞)) p.2)

/--
%%handwave
name:
  Scalar projections of a vector-valued weak derivative lie in the weak-gradient graph
statement:
  If a Hilbert-valued pair satisfies the weak derivative identity after every target functional, then each induced scalar \(L^2\) pair belongs to the scalar weak-gradient graph.
proof:
  Use the projected value and differential as witnesses, their canonical almost-everywhere identities, and the assumed scalar distributional identity.
-/
private theorem weakDerivativeGraphWithValues_scalarProjection_mem
    {X E : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [IsManifold SurfaceRealModel ∞ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X) (_hμ : SmoothPositiveAreaMeasureOnSurface X μ)
    {p : Lp E 2 μ × Lp (SurfaceDifferentialCoordinateHilbertFiber E) 2 μ}
    (hweak : IsWeakDerivativeOnSurfaceWithValuesByDual μ
      (fun x ↦ p.1 x) (fun x ↦ p.2 x))
    (Λ : E →L[ℝ] ℝ) :
    WeakGradientGraphOnSurface μ
      (weakDerivativeGraphWithValuesScalarProjectionCLM μ Λ p) := by
  let pΛ := weakDerivativeGraphWithValuesScalarProjectionCLM μ Λ p
  refine ⟨fun x ↦ Λ (p.1 x),
    fun x ↦ SurfaceDifferentialCoordinateHilbertFiber.dualProjectionCLM Λ (p.2 x),
    ?_, ?_, hweak Λ⟩
  · exact weakDerivativeGraphWithValuesScalarProjectionCLM_fst_ae μ Λ p
  · exact weakDerivativeGraphWithValuesScalarProjectionCLM_snd_ae μ Λ p

/--
%%handwave
name:
  Hilbert-valued weak-derivative graph is stable under \(L^2\) limits
statement:
  Let the target be a real Hilbert space.  If a net of \(L^2\) function and
  coordinate differential pairs belongs eventually to the weak-derivative
  graph and converges in the product \(L^2\) topology, then its limit belongs
  to the weak-derivative graph.
proof:
  Pass the vector-valued distributional identity to the limit against every
  compactly supported coordinate test.  The value component is controlled by
  Hilbert-valued \(L^2\) pairing continuity, and the derivative component is
  controlled by the \(L^2\) pairing on the coordinate derivative Hilbert
  fiber.  The smooth positive area density makes the coordinate and surface
  \(L^2\) estimates locally equivalent.
-/
theorem weakDerivativeGraphOnSurfaceWithValues_mem_of_tendsto {X E : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [IsManifold SurfaceRealModel ∞ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X) (hμ : SmoothPositiveAreaMeasureOnSurface X μ)
    (hcoord : ContinuousPreferredTangentCoordinatesOnSurface X)
    {ι : Type} {l : Filter ι} [l.NeBot]
    {p : ι → Lp E 2 μ ×
      Lp (SurfaceDifferentialCoordinateHilbertFiber E) 2 μ}
    {q : Lp E 2 μ ×
      Lp (SurfaceDifferentialCoordinateHilbertFiber E) 2 μ}
    (hp : ∀ᶠ i in l, WeakDerivativeGraphOnSurfaceWithValues μ (p i))
    (hp_tendsto : Filter.Tendsto p l (𝓝 q)) :
    WeakDerivativeGraphOnSurfaceWithValues μ q := by
  refine ⟨fun x ↦ q.1 x, fun x ↦ q.2 x, Filter.EventuallyEq.rfl,
    Filter.EventuallyEq.rfl, ?_⟩
  intro Λ
  let P := weakDerivativeGraphWithValuesScalarProjectionCLM μ Λ
  have hp_scalar :
      ∀ᶠ i in l, WeakGradientGraphOnSurface μ (P (p i)) := by
    filter_upwards [hp] with i hi
    have hweak_i :
        IsWeakDerivativeOnSurfaceWithValuesByDual μ
          (fun x ↦ (p i).1 x) (fun x ↦ (p i).2 x) :=
      weakDerivativeGraphOnSurfaceWithValues_canonical_representatives μ hμ hi
    exact weakDerivativeGraphWithValues_scalarProjection_mem μ hμ hweak_i Λ
  have hP_tendsto : Filter.Tendsto (fun i ↦ P (p i)) l (𝓝 (P q)) :=
    (P.continuous.tendsto q).comp hp_tendsto
  have hscalar_graph :
      WeakGradientGraphOnSurface μ (P q) :=
    weakGradientGraphOnSurface_mem_of_tendsto μ hμ hcoord hp_scalar hP_tendsto
  have hscalar :
      IsWeakGradientOnSurface μ (fun x ↦ (P q).1 x) (fun x ↦ (P q).2 x) :=
    weakGradientGraphOnSurface_canonical_representatives μ hμ hscalar_graph
  exact IsWeakGradientOnSurface.congr_ae μ hμ
    (weakDerivativeGraphWithValuesScalarProjectionCLM_fst_ae μ Λ q)
    (weakDerivativeGraphWithValuesScalarProjectionCLM_snd_ae μ Λ q)
    hscalar

/--
%%handwave
name:
  Hilbert-valued weak-derivative graph is closed
statement:
  For a smooth positive area measure and a real Hilbert target, the
  weak-derivative graph is closed in the product \(L^2\) topology.
proof:
  Apply the stability of the weak-derivative identity under product \(L^2\)
  convergence.
-/
theorem weakDerivativeGraphOnSurfaceWithValues_isClosed {X E : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [IsManifold SurfaceRealModel ∞ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X) (hμ : SmoothPositiveAreaMeasureOnSurface X μ)
    (hcoord : ContinuousPreferredTangentCoordinatesOnSurface X) :
    IsClosed
      {p : Lp E 2 μ × Lp (SurfaceDifferentialCoordinateHilbertFiber E) 2 μ |
        WeakDerivativeGraphOnSurfaceWithValues μ p} := by
  refine isClosed_iff_forall_filter.2 ?_
  intro q F hF_ne hF_graph hF_lim
  haveI : F.NeBot := hF_ne
  have hgraph_eventually :
      ∀ᶠ y in F, WeakDerivativeGraphOnSurfaceWithValues μ y :=
    hF_graph (by simp)
  have hid_tendsto :
      Filter.Tendsto
        (fun y : Lp E 2 μ ×
          Lp (SurfaceDifferentialCoordinateHilbertFiber E) 2 μ ↦ y) F (𝓝 q) := by
    simpa using hF_lim
  exact weakDerivativeGraphOnSurfaceWithValues_mem_of_tendsto
    μ hμ hcoord hgraph_eventually hid_tendsto

/--
%%handwave
name:
  Hilbert-valued weak-derivative graph is a closed linear subspace
statement:
  For a smooth positive area measure and a real Hilbert target, the graph of
  the weak-derivative operator is a closed real linear subspace of the
  first-order \(L^2\) product.
proof:
  Linearity follows by adding and scaling the vector-valued
  integration-by-parts identities.  Closedness is the closed-graph statement
  for Hilbert-valued weak derivatives.
-/
theorem weakDerivativeGraph_closed_linear_subspace_on_surface_with_values
    {X E : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [IsManifold SurfaceRealModel ∞ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X) (hμ : SmoothPositiveAreaMeasureOnSurface X μ)
    (hcoord : ContinuousPreferredTangentCoordinatesOnSurface X) :
    ∃ G : Submodule ℝ
        (Lp E 2 μ × Lp (SurfaceDifferentialCoordinateHilbertFiber E) 2 μ),
      (G : Set
        (Lp E 2 μ × Lp (SurfaceDifferentialCoordinateHilbertFiber E) 2 μ)) =
          {p | WeakDerivativeGraphOnSurfaceWithValues μ p} ∧
        IsClosed (G : Set
          (Lp E 2 μ × Lp (SurfaceDifferentialCoordinateHilbertFiber E) 2 μ)) := by
  let G : Submodule ℝ
      (Lp E 2 μ × Lp (SurfaceDifferentialCoordinateHilbertFiber E) 2 μ) :=
    { carrier := {p | WeakDerivativeGraphOnSurfaceWithValues μ p}
      zero_mem' := weakDerivativeGraphOnSurfaceWithValues_zero μ
      add_mem' := by
        intro p q hp hq
        exact weakDerivativeGraphOnSurfaceWithValues_add hp hq
      smul_mem' := by
        intro c p hp
        exact weakDerivativeGraphOnSurfaceWithValues_const_smul c hp }
  refine ⟨G, rfl, ?_⟩
  simpa [G] using weakDerivativeGraphOnSurfaceWithValues_isClosed μ hμ hcoord

/--
%%handwave
name:
  Hilbert-valued weak-derivative graph on a Riemannian surface
statement:
  For the area measure associated to a smooth Riemannian surface metric and a
  real Hilbert target, the weak-derivative graph is a closed real linear
  subspace of the first-order \(L^2\) product.
proof:
  The Riemannian area measure is smooth and positive in coordinates, so the
  closed-graph theorem for smooth positive area measures applies.
-/
theorem weakDerivativeGraph_closed_linear_subspace_on_riemannian_surface_with_values
    {X E : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [IsManifold SurfaceRealModel ∞ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (metric : SmoothRiemannianMetricOnSurface X)
    (μg : SurfaceMetricMeasureGeometry X metric)
    (hcoord : ContinuousPreferredTangentCoordinatesOnSurface X) :
    ∃ G : Submodule ℝ
        (Lp E 2 μg.volume ×
          Lp (SurfaceDifferentialCoordinateHilbertFiber E) 2 μg.volume),
      (G : Set
        (Lp E 2 μg.volume ×
          Lp (SurfaceDifferentialCoordinateHilbertFiber E) 2 μg.volume)) =
          {p | WeakDerivativeGraphOnSurfaceWithValues μg.volume p} ∧
        IsClosed (G : Set
          (Lp E 2 μg.volume ×
            Lp (SurfaceDifferentialCoordinateHilbertFiber E) 2 μg.volume)) := by
  exact weakDerivativeGraph_closed_linear_subspace_on_surface_with_values
    μg.volume μg.smoothPositive hcoord

/--
%%handwave
name:
  Hilbert-valued weak-derivative graph in the Hilbert product
statement:
  The Hilbert-valued weak-derivative graph inside the square-sum first-order
  \(L^2\) product consists of the same function and derivative pairs as the
  weak-derivative graph, but viewed with the Hilbert product norm.
-/
def WeakDerivativeGraphOnSurfaceWithValuesHilbertSubmodule {X E : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [IsManifold SurfaceRealModel 1 X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (μ : Measure X) :
    Submodule ℝ (SobolevH1OnSurfaceWithValuesAmbientHilbertModel
      (X := X) (E := E) μ) where
  carrier :=
    {p | WeakDerivativeGraphOnSurfaceWithValues μ (WithLp.ofLp p)}
  zero_mem' := by
    simpa using
      (weakDerivativeGraphOnSurfaceWithValues_zero
        (X := X) (E := E) μ)
  add_mem' := by
    intro p q hp hq
    simpa using
      (weakDerivativeGraphOnSurfaceWithValues_add
        (X := X) (E := E) (μ := μ) hp hq)
  smul_mem' := by
    intro c p hp
    simpa using
      (weakDerivativeGraphOnSurfaceWithValues_const_smul
        (X := X) (E := E) (μ := μ) c hp)

/--
%%handwave
name:
  Hilbert-valued weak-derivative graph is closed in the Hilbert product
statement:
  For a smooth positive area measure and a real Hilbert target, the
  weak-derivative graph is a closed subspace of the square-sum first-order
  \(L^2\) Hilbert product.
proof:
  The graph is closed in the underlying product topology, and the identity
  from the square-sum Hilbert product to the underlying product is continuous.
-/
theorem weakDerivativeGraphOnSurfaceWithValuesHilbertSubmodule_isClosed
    {X E : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [IsManifold SurfaceRealModel ∞ X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (μ : Measure X) (hμ : SmoothPositiveAreaMeasureOnSurface X μ)
    (hcoord : ContinuousPreferredTangentCoordinatesOnSurface X) :
    IsClosed
      (WeakDerivativeGraphOnSurfaceWithValuesHilbertSubmodule
        (X := X) (E := E) μ :
        Set (SobolevH1OnSurfaceWithValuesAmbientHilbertModel
          (X := X) (E := E) μ)) := by
  change IsClosed
    ((fun p : SobolevH1OnSurfaceWithValuesAmbientHilbertModel
        (X := X) (E := E) μ ↦ WithLp.ofLp p) ⁻¹'
      {p : Lp E 2 μ × Lp (SurfaceDifferentialCoordinateHilbertFiber E) 2 μ |
        WeakDerivativeGraphOnSurfaceWithValues μ p})
  exact (weakDerivativeGraphOnSurfaceWithValues_isClosed μ hμ hcoord).preimage
    (WithLp.prod_continuous_ofLp (p := 2)
      (α := Lp E 2 μ)
      (β := Lp (SurfaceDifferentialCoordinateHilbertFiber E) 2 μ))

/--
%%handwave
name:
  Hilbert-valued graph model for surface \(W^{1,2}\)
statement:
  The graph Hilbert model of \(W^{1,2}\) consists of \(L^2\) maps together
  with their \(L^2\) weak derivatives, viewed as the closed weak-derivative
  graph inside the square-sum first-order \(L^2\) Hilbert product.
-/
abbrev SobolevH1OnSurfaceWithValuesGraphHilbertModel {X E : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [IsManifold SurfaceRealModel 1 X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (μ : Measure X) : Type _ :=
  WeakDerivativeGraphOnSurfaceWithValuesHilbertSubmodule
    (X := X) (E := E) μ

/--
%%handwave
name:
  Hilbert model for surface \(W^{1,2}\)
statement:
  The separated \(W^{1,2}\) model consists of \(L^2\)-class functions which
  admit an \(L^2\) weak gradient.
-/
def SobolevH1OnSurfaceHilbertModel {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) : Type _ :=
  { u : Lp ℝ 2 μ // HasWeakGradientInL2OnSurface μ u }

/--
%%handwave
name:
  Hilbert-valued model for surface \(W^{1,2}\)
statement:
  The Hilbert-valued separated \(W^{1,2}\) model consists of \(L^2\)-class maps
  into a real Hilbert space which admit an \(L^2\) weak derivative.
-/
def SobolevH1OnSurfaceWithValuesHilbertModel {X E : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [IsManifold SurfaceRealModel 1 X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X) : Type _ :=
  { u : Lp E 2 μ // HasWeakDerivativeInL2OnSurfaceWithValues μ u }

/--
%%handwave
name:
  The ambient first-order \(L^2\) model is Hilbert
statement:
  The product of the \(L^2\) function space and the \(L^2\) cotangent-field
  space is a real Hilbert space.
proof:
  Products of real Hilbert spaces are real Hilbert spaces.
-/
theorem surfaceH1AmbientModel_admits_hilbert_structure
    {X : Type} [MeasurableSpace X] (μ : Measure X) :
    AdmitsRealHilbertStructure (SobolevH1OnSurfaceAmbientHilbertModel μ) := by
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  exact ⟨HilbertSpace.mk⟩

/--
%%handwave
name:
  Hilbert-valued ambient first-order \(L^2\) model is Hilbert
statement:
  If the target is a real Hilbert space, then the first-order \(L^2\) ambient
  product of values and coordinate differential components is a real Hilbert
  space.
proof:
  Hilbert-valued \(L^2\) spaces are Hilbert spaces, and products of real
  Hilbert spaces are real Hilbert spaces.
-/
theorem surfaceH1WithValuesAmbientModel_admits_hilbert_structure
    {X E : Type} [MeasurableSpace X] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (μ : Measure X) :
    AdmitsRealHilbertStructure
      (SobolevH1OnSurfaceWithValuesAmbientHilbertModel (E := E) μ) := by
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  exact ⟨HilbertSpace.mk⟩

/--
%%handwave
name:
  Hilbert-valued graph \(W^{1,2}\) model is Hilbert
statement:
  For maps from a smooth Riemannian surface into a real Hilbert space, the
  weak-derivative graph model is a real Hilbert space with the graph inner
  product inherited from the square-sum first-order \(L^2\) Hilbert product.
proof:
  The first-order ambient product is a real Hilbert space.  The
  weak-derivative graph is a closed real linear subspace of it, hence is a
  real Hilbert space with the inherited inner product.
-/
theorem sobolevH1OnSurfaceWithValuesGraph_admits_hilbert_structure
    {X E : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [IsManifold SurfaceRealModel ∞ X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (μ : Measure X) (hμ : SmoothPositiveAreaMeasureOnSurface X μ)
    (hcoord : ContinuousPreferredTangentCoordinatesOnSurface X) :
    AdmitsRealHilbertStructure
      (SobolevH1OnSurfaceWithValuesGraphHilbertModel
        (X := X) (E := E) μ) := by
  let G :=
    WeakDerivativeGraphOnSurfaceWithValuesHilbertSubmodule
      (X := X) (E := E) μ
  have hG_closed : IsClosed (G : Set
      (SobolevH1OnSurfaceWithValuesAmbientHilbertModel
        (X := X) (E := E) μ)) := by
    simpa [G] using
      weakDerivativeGraphOnSurfaceWithValuesHilbertSubmodule_isClosed
        (X := X) (E := E) μ hμ hcoord
  haveI : IsClosed (G : Set
      (SobolevH1OnSurfaceWithValuesAmbientHilbertModel
        (X := X) (E := E) μ)) := hG_closed
  have hG_complete : CompleteSpace G := by
    change CompleteSpace (G : Set
      (SobolevH1OnSurfaceWithValuesAmbientHilbertModel
        (X := X) (E := E) μ))
    exact hG_closed.isComplete.completeSpace_coe
  haveI : CompleteSpace G := hG_complete
  change AdmitsRealHilbertStructure G
  refine ⟨inferInstance, inferInstance, hG_complete, ?_⟩
  exact ⟨@HilbertSpace.mk ℝ G _ _ _ hG_complete⟩

/--
%%handwave
name:
  Hilbert-valued graph \(W^{1,2}\) model on a Riemannian surface is Hilbert
statement:
  For the area measure associated to a smooth Riemannian surface metric, the
  Hilbert-valued weak-derivative graph model is a real Hilbert space.
proof:
  The Riemannian area measure is smooth and positive in coordinates, so the
  graph Hilbert-space theorem for smooth positive area measures applies.
-/
theorem sobolevH1OnRiemannianSurfaceWithValuesGraph_admits_hilbert_structure
    {X E : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [IsManifold SurfaceRealModel ∞ X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (metric : SmoothRiemannianMetricOnSurface X)
    (μg : SurfaceMetricMeasureGeometry X metric)
    (hcoord : ContinuousPreferredTangentCoordinatesOnSurface X) :
    AdmitsRealHilbertStructure
      (SobolevH1OnSurfaceWithValuesGraphHilbertModel
        (X := X) (E := E) μg.volume) := by
  exact sobolevH1OnSurfaceWithValuesGraph_admits_hilbert_structure
    μg.volume μg.smoothPositive hcoord

end

end Uniformization

end JJMath
