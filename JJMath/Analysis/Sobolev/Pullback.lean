import JJMath.Analysis.Sobolev.Rellich
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# Sobolev pullbacks under locally bi-Lipschitz maps

This file contains the local graph-density and locally bi-Lipschitz pullback
machinery used by the ball trace and extension arguments.
-/

namespace JJMath

open MeasureTheory
open scoped Manifold Topology ENNReal NNReal ContDiff Convolution

namespace Uniformization

noncomputable section

open ContinuousLinearMap

theorem memLp_of_integrable_and_restrict_support
    {α E : Type} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {s : Set α} {f : α → E}
    (hf_int : Integrable f μ)
    (hf_restrict : MemLp f 2 (μ.restrict s))
    (hsupport : Function.support f ⊆ s) :
    MemLp f 2 μ := by
  refine ⟨hf_int.aestronglyMeasurable, ?_⟩
  have hnorm :
      eLpNorm f 2 (μ.restrict s) = eLpNorm f 2 μ :=
    eLpNorm_restrict_eq_of_support_subset hsupport
  simpa [hnorm] using hf_restrict.2

theorem memLp_restrict_mul_left_of_isCompact_of_continuousOn
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    {K : Set H} (hK : IsCompact K)
    {a g : H → ℝ} (ha : ContinuousOn a K)
    (hg : MemLp g 2 (MeasureTheory.volume.restrict K)) :
    MemLp (fun z ↦ a z * g z) 2
      (MeasureTheory.volume.restrict K) := by
  let μK : Measure H := MeasureTheory.volume.restrict K
  have ha_aesm : AEStronglyMeasurable a μK := by
    simpa [μK] using
      ha.aestronglyMeasurable_of_isCompact hK hK.measurableSet
  have hprod_aesm :
      AEStronglyMeasurable (fun z ↦ a z * g z) μK :=
    ha_aesm.mul hg.aestronglyMeasurable
  rcases hK.exists_bound_of_continuousOn ha with ⟨C₀, hC₀⟩
  let C : ℝ := max C₀ 0
  have hC_bound : ∀ z ∈ K, ‖a z‖ ≤ C := by
    intro z hz
    exact le_trans (hC₀ z hz) (le_max_left C₀ 0)
  exact MemLp.of_le_mul hg hprod_aesm
    (ae_restrict_of_forall_mem hK.measurableSet fun z hz ↦ by
      calc
        ‖a z * g z‖ = ‖a z‖ * ‖g z‖ := norm_mul _ _
        _ ≤ C * ‖g z‖ :=
          mul_le_mul_of_nonneg_right (hC_bound z hz) (norm_nonneg _))

private theorem memLp_restrict_of_isCompact_of_continuousOn
    {H E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H] [NormedAddCommGroup E]
    {K : Set H} (hK : IsCompact K) {f : H → E}
    (hf : ContinuousOn f K) :
    MemLp f 2 (MeasureTheory.volume.restrict K) := by
  classical
  let μK : Measure H := MeasureTheory.volume.restrict K
  haveI : IsFiniteMeasure μK := isFiniteMeasure_restrict.2 hK.measure_ne_top
  have hf_aesm : AEStronglyMeasurable f μK := by
    simpa [μK] using
      hf.aestronglyMeasurable_of_isCompact hK hK.measurableSet
  rcases hK.exists_bound_of_continuousOn hf with ⟨C, hC⟩
  exact
    MemLp.of_bound (μ := μK) (p := (2 : ℝ≥0∞))
      hf_aesm C
      (ae_restrict_of_forall_mem hK.measurableSet hC)

theorem memLp_two_locallyIntegrableOn_univ
    {H E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H] [NormedAddCommGroup E]
    {f : H → E}
    (hf : MemLp f 2 (MeasureTheory.volume : Measure H)) :
    LocallyIntegrableOn f Set.univ (MeasureTheory.volume : Measure H) := by
  haveI : ProperSpace H := FiniteDimensional.proper ℝ H
  rw [locallyIntegrableOn_iff isOpen_univ.isLocallyClosed]
  intro K _hK_univ hK
  have hK_mem : MemLp f 2 (MeasureTheory.volume.restrict K) :=
    hf.mono_measure Measure.restrict_le_self
  haveI : IsFiniteMeasure (MeasureTheory.volume.restrict K) :=
    isFiniteMeasure_restrict.2 hK.measure_ne_top
  exact hK_mem.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)

private theorem memLp_two_locallyIntegrableOn_of_subset
    {H E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H] [NormedAddCommGroup E]
    {U P : Set H} (hU_open : IsOpen U) (hUP : U ⊆ P)
    {f : H → E}
    (hf : MemLp f 2 (MeasureTheory.volume.restrict P)) :
    LocallyIntegrableOn f U (MeasureTheory.volume : Measure H) := by
  rw [locallyIntegrableOn_iff hU_open.isLocallyClosed]
  intro K hKU hK
  have hK_mem : MemLp f 2 (MeasureTheory.volume.restrict K) :=
    hf.mono_measure (Measure.restrict_mono (hKU.trans hUP) le_rfl)
  haveI : IsFiniteMeasure (MeasureTheory.volume.restrict K) :=
    isFiniteMeasure_restrict.2 hK.measure_ne_top
  exact hK_mem.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)

private theorem continuousLinearMap_sequence_memLp_and_eLpNorm_tendsto_zero_of_basis_eval'
    {α H E : Type} [MeasurableSpace α]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {μ : Measure α} (Fseq : ℕ → α → H →L[ℝ] E)
    (h_eval_mem : ∀ (n : ℕ) (i : Fin (Module.finrank ℝ H)),
      MemLp (fun x ↦ Fseq n x (Module.finBasis ℝ H i)) 2 μ)
    (h_eval_tendsto : ∀ i : Fin (Module.finrank ℝ H),
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm (fun x ↦ Fseq n x (Module.finBasis ℝ H i)) 2 μ)
        Filter.atTop (𝓝 (0 : ℝ≥0∞))) :
    (∀ n : ℕ, MemLp (Fseq n) 2 μ) ∧
      Filter.Tendsto
        (fun n : ℕ ↦ eLpNorm (Fseq n) 2 μ)
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
  classical
  let ι := Fin (Module.finrank ℝ H)
  let B : ℕ → ℝ≥0∞ := fun n ↦
    ∑ i : ι, eLpNorm (fun x ↦ Fseq n x (Module.finBasis ℝ H i)) 2 μ
  let Ceval : ι → ℝ≥0∞ := fun _ ↦ 1
  have hCeval_top : ∀ i : ι, Ceval i < ⊤ := by
    intro i
    simp [Ceval]
  have h_eval_bound :
      ∀ (n : ℕ) (i : ι),
        MemLp (fun x ↦ Fseq n x (Module.finBasis ℝ H i)) 2 μ ∧
          eLpNorm (fun x ↦ Fseq n x (Module.finBasis ℝ H i)) 2 μ ≤
            Ceval i * B n := by
    intro n i
    refine ⟨h_eval_mem n i, ?_⟩
    calc
      eLpNorm (fun x ↦ Fseq n x (Module.finBasis ℝ H i)) 2 μ
          ≤ B n := by
            dsimp [B, ι]
            exact Finset.single_le_sum
              (f := fun j : ι ↦
                eLpNorm (fun x ↦ Fseq n x (Module.finBasis ℝ H j)) 2 μ)
              (fun j _hj ↦ zero_le)
              (Finset.mem_univ i)
      _ = Ceval i * B n := by simp [Ceval]
  rcases
    continuousLinearMap_sequence_memLp_and_eLpNorm_le_of_basis_eval_const_mul
      (Fseq := Fseq) (B := B) (Ceval := Ceval)
      hCeval_top h_eval_bound with
    ⟨C, hC_top, hfull⟩
  have hB_tendsto :
      Filter.Tendsto B Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
    dsimp [B]
    simpa using
      (tendsto_finsetSum (s := Finset.univ)
        (f := fun i n ↦
          eLpNorm (fun x ↦ Fseq n x (Module.finBasis ℝ H i)) 2 μ)
        (a := fun _i : ι ↦ (0 : ℝ≥0∞))
        (x := Filter.atTop)
        (fun i _hi ↦ h_eval_tendsto i))
  have hC_ne_top : C ≠ ⊤ := ne_of_lt hC_top
  have hCB_tendsto :
      Filter.Tendsto (fun n : ℕ ↦ C * B n)
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
    have hmul := ENNReal.Tendsto.const_mul hB_tendsto (Or.inr hC_ne_top)
    simpa using hmul
  refine ⟨fun n ↦ (hfull n).1, ?_⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hCB_tendsto
    (fun n ↦ zero_le)
    (fun n ↦ (hfull n).2)

/--
%%handwave
name:
  Lipschitz images have finite Lebesgue distortion
statement:
  Let \(F\) be Lipschitz on a subset \(A\) of a finite-dimensional Euclidean
  space.  Then there is a finite constant \(C\) such that, for every
  \(E\subset A\), the Lebesgue measure of \(F(E)\) is at most \(C\) times the
  Lebesgue measure of \(E\).
proof:
  Compare Lebesgue measure with the Hausdorff measure in the ambient
  dimension, and apply the standard Hausdorff-measure estimate for Lipschitz
  images.
-/
theorem lipschitzOnWith_volume_image_le_smul
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {A : Set H} {F : H → H} {L : ℝ≥0}
    (_hF_lip : LipschitzOnWith L F A) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ E : Set H, E ⊆ A →
        MeasureTheory.volume (F '' E) ≤ C * MeasureTheory.volume E := by
  let μHn : Measure H :=
    MeasureTheory.Measure.hausdorffMeasure (Module.finrank ℝ H : ℝ)
  haveI : Measure.IsAddHaarMeasure μHn := by
    simpa [μHn] using
      (MeasureTheory.isAddHaarMeasure_hausdorffMeasure (E := H))
  let c : ℝ≥0 :=
    MeasureTheory.Measure.addHaarScalarFactor
      (MeasureTheory.volume : Measure H) μHn
  have hvol_eq :
      (MeasureTheory.volume : Measure H) = c • μHn := by
    simpa [c, μHn] using
      (MeasureTheory.Measure.isAddLeftInvariant_eq_smul
        (MeasureTheory.volume : Measure H) μHn)
  let C : ℝ≥0∞ :=
    (L : ℝ≥0∞) ^ (Module.finrank ℝ H : ℝ)
  refine ⟨C, ?_, ?_⟩
  · exact
      (ENNReal.rpow_lt_top_of_nonneg
        (by positivity : 0 ≤ (Module.finrank ℝ H : ℝ))
        ENNReal.coe_ne_top).ne
  intro E hEA
  have hH :
      μHn (F '' E) ≤ C * μHn E := by
    simpa [μHn, C] using
      (_hF_lip.mono hEA).hausdorffMeasure_image_le
        (d := (Module.finrank ℝ H : ℝ)) (by positivity)
  have hscaled :
      (c : ℝ≥0∞) * μHn (F '' E) ≤
        C * ((c : ℝ≥0∞) * μHn E) := by
    have hright := mul_le_mul_right hH (c : ℝ≥0∞)
    simpa [mul_assoc, mul_left_comm, mul_comm] using hright
  simpa [hvol_eq, Measure.smul_apply, smul_eq_mul, mul_assoc] using hscaled

theorem measurePreserving_add_right_volume
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    (c : H) :
    MeasurePreserving (fun z : H ↦ z + c)
      (MeasureTheory.volume : Measure H) MeasureTheory.volume := by
  refine ⟨?_, ?_⟩
  · simpa [add_comm] using (measurable_const_add c : Measurable fun z : H ↦ c + z)
  · simpa [add_comm] using
      MeasureTheory.map_add_left_eq_self (MeasureTheory.volume : Measure H) c

theorem measurableEmbedding_add_right
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H]
    (c : H) :
    MeasurableEmbedding (fun z : H ↦ z + c) := by
  simpa [add_comm] using (measurableEmbedding_addLeft c)

theorem preimage_add_right_ball_center
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (c : H) (r : ℝ) :
    (fun z : H ↦ z + c) ⁻¹' Metric.ball c r =
      Metric.ball (0 : H) r := by
  ext z
  have hdist : dist (z + c) c = dist z (0 : H) := by
    rw [dist_eq_norm, dist_eq_norm]
    congr 1
    simp [sub_eq_add_neg, add_assoc]
  change z + c ∈ Metric.ball c r ↔ z ∈ Metric.ball (0 : H) r
  rw [Metric.mem_ball, Metric.mem_ball, hdist]

theorem preimage_add_right_neg_ball_zero
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (c : H) (r : ℝ) :
    (fun z : H ↦ z + (-c)) ⁻¹' Metric.ball (0 : H) r =
      Metric.ball c r := by
  ext z
  have hdist : dist (z + (-c)) (0 : H) = dist z c := by
    rw [dist_eq_norm, dist_eq_norm]
    congr 1
    simp [sub_eq_add_neg]
  change z + (-c) ∈ Metric.ball (0 : H) r ↔ z ∈ Metric.ball c r
  rw [Metric.mem_ball, Metric.mem_ball, hdist]

theorem preimage_const_smul_ball_zero_of_pos
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {a R : ℝ} (ha_pos : 0 < a) :
    (fun z : H ↦ a • z) ⁻¹' Metric.ball (0 : H) (a * R) =
      Metric.ball (0 : H) R := by
  ext z
  have hdist : dist (a • z) (0 : H) = a * dist z (0 : H) := by
    rw [dist_eq_norm, dist_eq_norm]
    simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha_pos.le]
  change a • z ∈ Metric.ball (0 : H) (a * R) ↔
    z ∈ Metric.ball (0 : H) R
  rw [Metric.mem_ball, Metric.mem_ball, hdist]
  constructor <;> intro h <;> nlinarith [ha_pos, h]

private theorem map_const_smul_volume_eq_smul
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {a : ℝ} (ha : a ≠ 0) :
    Measure.map (fun z : H ↦ a • z) MeasureTheory.volume =
      ENNReal.ofReal |(a ^ Module.finrank ℝ H)⁻¹| •
        (MeasureTheory.volume : Measure H) := by
  simpa using
    MeasureTheory.Measure.map_addHaar_smul
      (MeasureTheory.volume : Measure H) ha

private theorem map_const_smul_restrict_ball_zero_eq_smul
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {a R : ℝ} (ha_pos : 0 < a) :
    Measure.map (fun z : H ↦ a • z)
        (MeasureTheory.volume.restrict (Metric.ball (0 : H) R)) =
      ENNReal.ofReal |(a ^ Module.finrank ℝ H)⁻¹| •
        MeasureTheory.volume.restrict (Metric.ball (0 : H) (a * R)) := by
  let T : H → H := fun z ↦ a • z
  let B : Set H := Metric.ball (0 : H) R
  let BT : Set H := Metric.ball (0 : H) (a * R)
  let J : ℝ≥0∞ := ENNReal.ofReal |(a ^ Module.finrank ℝ H)⁻¹|
  have ha_ne : a ≠ 0 := ne_of_gt ha_pos
  have hT_meas : Measurable T := by
    dsimp [T]
    measurability
  have hpre : T ⁻¹' BT = B := by
    simpa [T, B, BT] using
      preimage_const_smul_ball_zero_of_pos (H := H) (a := a) (R := R) ha_pos
  have hmap_volume :
      Measure.map T MeasureTheory.volume = J •
        (MeasureTheory.volume : Measure H) := by
    simpa [T, J] using map_const_smul_volume_eq_smul (H := H) ha_ne
  calc
    Measure.map T (MeasureTheory.volume.restrict B)
        = Measure.map T (MeasureTheory.volume.restrict (T ⁻¹' BT)) := by
            rw [hpre]
    _ = (Measure.map T MeasureTheory.volume).restrict BT := by
            exact (Measure.restrict_map hT_meas measurableSet_ball).symm
    _ = (J • (MeasureTheory.volume : Measure H)).restrict BT := by
            rw [hmap_volume]
    _ = J • MeasureTheory.volume.restrict BT := by
            rw [Measure.restrict_smul]
    _ = ENNReal.ofReal |(a ^ Module.finrank ℝ H)⁻¹| •
        MeasureTheory.volume.restrict (Metric.ball (0 : H) (a * R)) := by
            rfl

theorem memLp_comp_const_smul_of_memLp_restrict_ball_zero
    {H E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H] [NormedAddCommGroup E]
    {a R : ℝ} (ha_pos : 0 < a)
    {f : H → E}
    (hf : MemLp f 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) (a * R)))) :
    MemLp (fun z : H ↦ f (a • z)) 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) R)) := by
  let T : H → H := fun z ↦ a • z
  let J : ℝ≥0∞ := ENNReal.ofReal |(a ^ Module.finrank ℝ H)⁻¹|
  have hT_meas : Measurable T := by
    dsimp [T]
    measurability
  have hT_aemeas :
      AEMeasurable T
        (MeasureTheory.volume.restrict (Metric.ball (0 : H) R)) :=
    hT_meas.aemeasurable
  have hJ_ne_top : J ≠ ⊤ := by
    simp [J]
  have hmap :
      Measure.map T
          (MeasureTheory.volume.restrict (Metric.ball (0 : H) R)) =
        J • MeasureTheory.volume.restrict
          (Metric.ball (0 : H) (a * R)) := by
    simpa [T, J] using
      map_const_smul_restrict_ball_zero_eq_smul
        (H := H) (a := a) (R := R) ha_pos
  have hf_map : MemLp f 2
      (Measure.map T
        (MeasureTheory.volume.restrict (Metric.ball (0 : H) R))) := by
    simpa [hmap] using hf.smul_measure hJ_ne_top
  simpa [T, Function.comp_def] using hf_map.comp_of_map hT_aemeas

theorem memLp_comp_const_smul_of_memLp_volume
    {H E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H] [NormedAddCommGroup E]
    {a : ℝ} (ha : a ≠ 0)
    {f : H → E}
    (hf : MemLp f 2 (MeasureTheory.volume : Measure H)) :
    MemLp (fun z : H ↦ f (a • z)) 2
      (MeasureTheory.volume : Measure H) := by
  let T : H → H := fun z ↦ a • z
  let J : ℝ≥0∞ := ENNReal.ofReal |(a ^ Module.finrank ℝ H)⁻¹|
  have hT_meas : Measurable T := by
    dsimp [T]
    measurability
  have hT_aemeas : AEMeasurable T (MeasureTheory.volume : Measure H) :=
    hT_meas.aemeasurable
  have hJ_ne_top : J ≠ ⊤ := by
    simp [J]
  have hmap :
      Measure.map T MeasureTheory.volume =
        J • (MeasureTheory.volume : Measure H) := by
    simpa [T, J] using map_const_smul_volume_eq_smul (H := H) ha
  have hf_map : MemLp f 2 (Measure.map T MeasureTheory.volume) := by
    simpa [hmap] using hf.smul_measure hJ_ne_top
  simpa [T, Function.comp_def] using hf_map.comp_of_map hT_aemeas

theorem quasiMeasurePreserving_const_smul_restrict_ball_zero
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {a R : ℝ} (ha_pos : 0 < a) :
    Measure.QuasiMeasurePreserving (fun z : H ↦ a • z)
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) R))
      (MeasureTheory.volume.restrict (Metric.ball (0 : H) (a * R))) := by
  refine ⟨?_, ?_⟩
  · measurability
  · rw [map_const_smul_restrict_ball_zero_eq_smul
        (H := H) (a := a) (R := R) ha_pos]
    exact Measure.smul_absolutelyContinuous

theorem IsWeakDerivativeOnEuclideanRegionWithValues.comp_add_right
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    {Ω : Set H} {u : H → ℝ} {du : H → H →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionWithValues Ω u du)
    (c : H) :
    IsWeakDerivativeOnEuclideanRegionWithValues
      ((fun z : H ↦ z + c) ⁻¹' Ω)
      (fun z : H ↦ u (z + c)) (fun z : H ↦ du (z + c)) := by
  intro φ v
  let T : H → H := fun z ↦ z + c
  let Ω' : Set H := T ⁻¹' Ω
  let left : H → ℝ :=
    fun z ↦ (fderiv ℝ (φ : H → ℝ) (z - c) v) • u z
  let right : H → ℝ := fun z ↦ φ (z - c) • du z v
  have hsupport : ∀ z ∈ tsupport (φ : H → ℝ), z + c ∈ Ω := by
    intro z hz
    exact φ.support_subset hz
  have hweak_scalar :
      IsWeakDerivativeOnEuclideanRegionScalar Ω u du := by
    simpa [IsWeakDerivativeOnEuclideanRegionScalar] using hweak
  have htranslated :=
    scalarWeakDerivativeOnEuclideanRegionScalar_translated_test
      hweak_scalar φ c v hsupport
  have hmp : MeasurePreserving T
      (MeasureTheory.volume : Measure H) MeasureTheory.volume := by
    simpa [T] using measurePreserving_add_right_volume (H := H) c
  have hT_emb : MeasurableEmbedding T := by
    simpa [T] using measurableEmbedding_add_right (H := H) c
  have hleft_int_pre :
      Integrable (left ∘ T) (MeasureTheory.volume.restrict Ω') := by
    have hiff :=
      hmp.integrableOn_comp_preimage hT_emb (f := left) (s := Ω)
    exact hiff.mpr (by simpa [left] using htranslated.1)
  have hright_int_pre :
      Integrable (right ∘ T) (MeasureTheory.volume.restrict Ω') := by
    have hiff :=
      hmp.integrableOn_comp_preimage hT_emb (f := right) (s := Ω)
    exact hiff.mpr (by simpa [right] using htranslated.2.1)
  have hleft_change :
      ∫ z in Ω', left (T z) ∂MeasureTheory.volume =
        ∫ z in Ω, left z ∂MeasureTheory.volume :=
    hmp.setIntegral_preimage_emb hT_emb left Ω
  have hright_change :
      ∫ z in Ω', right (T z) ∂MeasureTheory.volume =
        ∫ z in Ω, right z ∂MeasureTheory.volume :=
    hmp.setIntegral_preimage_emb hT_emb right Ω
  refine ⟨?_, ?_, ?_⟩
  · convert hleft_int_pre using 1
    ext z
    simp [left, T, sub_eq_add_neg, add_assoc]
  · convert hright_int_pre using 1
    ext z
    simp [right, T, sub_eq_add_neg, add_assoc]
  · calc
      ∫ z in (fun z : H ↦ z + c) ⁻¹' Ω,
          (fderiv ℝ (φ : H → ℝ) z v) • u (z + c)
          ∂MeasureTheory.volume
          =
        ∫ z in Ω', left (T z) ∂MeasureTheory.volume := by
          congr 1
          ext z
          simp [left, T, sub_eq_add_neg, add_assoc]
      _ = ∫ z in Ω, left z ∂MeasureTheory.volume := hleft_change
      _ = -∫ z in Ω, right z ∂MeasureTheory.volume := by
            simpa [left, right] using htranslated.2.2
      _ = -∫ z in Ω', right (T z) ∂MeasureTheory.volume := by
            rw [hright_change]
      _ =
        -∫ z in (fun z : H ↦ z + c) ⁻¹' Ω,
          φ z • du (z + c) v ∂MeasureTheory.volume := by
          change -∫ z in Ω', right (T z) ∂MeasureTheory.volume =
            -∫ z in Ω', φ z • du (T z) v ∂MeasureTheory.volume
          congr 1
          refine integral_congr_ae ?_
          exact Filter.Eventually.of_forall fun z ↦ by
            simp [right, T, sub_eq_add_neg, add_assoc]

private theorem integrableOn_comp_const_smul_of_integrableOn
    {H F : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup F]
    {f : H → F} {s : Set H} {a : ℝ} (ha : a ≠ 0)
    (hf : Integrable f (MeasureTheory.volume.restrict s)) :
    Integrable (fun z : H ↦ f (a • z))
      (MeasureTheory.volume.restrict ((fun z : H ↦ a • z) ⁻¹' s)) := by
  let T : H → H := fun z ↦ a • z
  let J : ℝ≥0∞ := ENNReal.ofReal |(a ^ Module.finrank ℝ H)⁻¹|
  have hT_emb : MeasurableEmbedding T := by
    simpa [T] using
      (Homeomorph.smulOfNeZero a ha : H ≃ₜ H).measurableEmbedding
  have hmap :
      Measure.map T (MeasureTheory.volume : Measure H) =
        J • (MeasureTheory.volume : Measure H) := by
    simpa [T, J] using map_const_smul_volume_eq_smul (H := H) ha
  have hf_map :
      Integrable f ((Measure.map T
        (MeasureTheory.volume : Measure H)).restrict s) := by
    have hf_smul : Integrable f (J • MeasureTheory.volume.restrict s) :=
      hf.smul_measure ENNReal.ofReal_ne_top
    simpa [hmap, Measure.restrict_smul, J] using hf_smul
  have hiff :=
    hT_emb.integrableOn_map_iff
      (μ := (MeasureTheory.volume : Measure H)) (f := f) (s := s)
  simpa [IntegrableOn, T, Function.comp_def] using hiff.mp hf_map

/--
%%handwave
name:
  Euclidean weak derivatives are invariant under nonzero dilations
statement:
  Let \(a\ne0\).  If a scalar function has weak derivative field \(du\) on a
  Euclidean region \(\Omega\), then the pullback \(z\mapsto u(az)\) has weak
  derivative field \(z\mapsto a\,du(az)\) on the preimage of \(\Omega\) under
  the dilation \(z\mapsto az\).
proof:
  Test against a compactly supported smooth function on the preimage region
  and push the test forward by the inverse dilation.  The chain rule gives
  the factor \(a\) in the derivative field, while the Haar-measure Jacobian
  factor appears on both sides of the integration-by-parts identity and
  cancels.
-/
theorem IsWeakDerivativeOnEuclideanRegionWithValues.comp_smul
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Ω : Set H} {u : H → ℝ} {du : H → H →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionWithValues Ω u du)
    {a : ℝ} (ha : a ≠ 0) :
    IsWeakDerivativeOnEuclideanRegionWithValues
      ((fun z : H ↦ a • z) ⁻¹' Ω)
      (fun z : H ↦ u (a • z))
      (fun z : H ↦ a • du (a • z)) := by
  intro φ v
  let T : H → H := fun z ↦ a • z
  let Ω' : Set H := T ⁻¹' Ω
  let e : H ≃ₜ H := Homeomorph.smulOfNeZero a ha
  let ψ : SmoothCompactlySupportedManifoldCoordinateFunction Ω :=
    { toFun := (φ : H → ℝ) ∘ e.symm
      smooth := by
        have hS : ContDiff ℝ ∞ (fun y : H ↦ a⁻¹ • y) :=
          contDiff_const_smul a⁻¹
        simpa [e, Function.comp_def,
          Homeomorph.smulOfNeZero_symm_apply] using φ.smooth.comp hS
      support_subset := by
        intro y hy
        have hy_pre : e.symm y ∈ tsupport (φ : H → ℝ) := by
          have h :=
            (Set.ext_iff.mp
              (tsupport_comp_eq_preimage (φ : H → ℝ) e.symm) y).mp hy
          simpa using h
        have hyΩ : a • e.symm y ∈ Ω := φ.support_subset hy_pre
        simpa [e, Homeomorph.smulOfNeZero_symm_apply,
          smul_smul, mul_inv_cancel₀ ha] using hyΩ
      compact_support := by
        rw [tsupport_comp_eq_preimage]
        exact e.symm.isCompact_preimage.2 φ.compact_support }
  have hψ := hweak ψ (a • v)
  have hψ_fderiv (y : H) :
      fderiv ℝ (ψ : H → ℝ) y (a • v) =
        fderiv ℝ (φ : H → ℝ) (a⁻¹ • y) v := by
    have hfd :
        fderiv ℝ (fun x : H ↦ (φ : H → ℝ) (a⁻¹ • x)) y =
          a⁻¹ • fderiv ℝ (φ : H → ℝ) (a⁻¹ • y) := by
      simpa using
        (fderiv_comp_smul (𝕜 := ℝ) (f := (φ : H → ℝ))
          (x := y) (c := a⁻¹))
    calc
      fderiv ℝ (ψ : H → ℝ) y (a • v)
          =
        fderiv ℝ (fun x : H ↦ (φ : H → ℝ) (a⁻¹ • x)) y (a • v) := by
          simp [ψ, e, Function.comp_def,
            Homeomorph.smulOfNeZero_symm_apply]
      _ = (a⁻¹ • fderiv ℝ (φ : H → ℝ) (a⁻¹ • y)) (a • v) := by
            rw [hfd]
      _ = fderiv ℝ (φ : H → ℝ) (a⁻¹ • y) v := by
            rw [ContinuousLinearMap.smul_apply, map_smul]
            change a⁻¹ * (a * (fderiv ℝ (φ : H → ℝ) (a⁻¹ • y)) v) =
              (fderiv ℝ (φ : H → ℝ) (a⁻¹ • y)) v
            rw [← mul_assoc, inv_mul_cancel₀ ha, one_mul]
  let F : H → ℝ :=
    fun y ↦ (fderiv ℝ (ψ : H → ℝ) y (a • v)) • u y
  let G : H → ℝ := fun y ↦ ψ y • du y (a • v)
  have hF_int : Integrable F (MeasureTheory.volume.restrict Ω) := by
    simpa [F] using hψ.1
  have hG_int : Integrable G (MeasureTheory.volume.restrict Ω) := by
    simpa [G] using hψ.2.1
  have hF_eq : ∫ y in Ω, F y ∂MeasureTheory.volume =
      -∫ y in Ω, G y ∂MeasureTheory.volume := by
    simpa [F, G] using hψ.2.2
  let J : ℝ≥0∞ := ENNReal.ofReal |(a ^ Module.finrank ℝ H)⁻¹|
  let j : ℝ := |(a ^ Module.finrank ℝ H)⁻¹|
  have hT_emb : MeasurableEmbedding T := by
    simpa [T] using
      (Homeomorph.smulOfNeZero a ha : H ≃ₜ H).measurableEmbedding
  have hmap :
      Measure.map T (MeasureTheory.volume : Measure H) =
        J • (MeasureTheory.volume : Measure H) := by
    simpa [T, J] using map_const_smul_volume_eq_smul (H := H) ha
  have hF_scale :
      ∫ z in Ω', F (T z) ∂MeasureTheory.volume =
        j • ∫ y in Ω, F y ∂MeasureTheory.volume := by
    calc
      ∫ z in Ω', F (T z) ∂MeasureTheory.volume =
          ∫ y in Ω, F y ∂(Measure.map T
            (MeasureTheory.volume : Measure H)) := by
            have hmap_int :=
              hT_emb.setIntegral_map
                (μ := (MeasureTheory.volume : Measure H)) F Ω
            simpa [Ω', T] using hmap_int.symm
      _ = ∫ y in Ω, F y ∂(J •
            (MeasureTheory.volume : Measure H)) := by
            rw [hmap]
      _ = j • ∫ y in Ω, F y ∂MeasureTheory.volume := by
            rw [Measure.restrict_smul, integral_smul_measure]
            simp [J, j]
  have hG_scale :
      ∫ z in Ω', G (T z) ∂MeasureTheory.volume =
        j • ∫ y in Ω, G y ∂MeasureTheory.volume := by
    calc
      ∫ z in Ω', G (T z) ∂MeasureTheory.volume =
          ∫ y in Ω, G y ∂(Measure.map T
            (MeasureTheory.volume : Measure H)) := by
            have hmap_int :=
              hT_emb.setIntegral_map
                (μ := (MeasureTheory.volume : Measure H)) G Ω
            simpa [Ω', T] using hmap_int.symm
      _ = ∫ y in Ω, G y ∂(J •
            (MeasureTheory.volume : Measure H)) := by
            rw [hmap]
      _ = j • ∫ y in Ω, G y ∂MeasureTheory.volume := by
            rw [Measure.restrict_smul, integral_smul_measure]
            simp [J, j]
  have hleft_int_pre :
      Integrable (fun z : H ↦ F (T z))
        (MeasureTheory.volume.restrict Ω') := by
    simpa [T, Ω'] using
      integrableOn_comp_const_smul_of_integrableOn
        (H := H) (F := ℝ) (a := a) (s := Ω) ha hF_int
  have hright_int_pre :
      Integrable (fun z : H ↦ G (T z))
        (MeasureTheory.volume.restrict Ω') := by
    simpa [T, Ω'] using
      integrableOn_comp_const_smul_of_integrableOn
        (H := H) (F := ℝ) (a := a) (s := Ω) ha hG_int
  refine ⟨?_, ?_, ?_⟩
  · convert hleft_int_pre using 1
    ext z
    simp [F, T, hψ_fderiv, smul_smul, inv_mul_cancel₀ ha]
  · convert hright_int_pre using 1
    ext z
    simp [G, T, ψ, e, Homeomorph.smulOfNeZero_symm_apply,
      smul_smul, inv_mul_cancel₀ ha]
  · calc
      ∫ z in (fun z : H ↦ a • z) ⁻¹' Ω,
          (fderiv ℝ (φ : H → ℝ) z v) • u (a • z)
          ∂MeasureTheory.volume
          =
        ∫ z in Ω', F (T z) ∂MeasureTheory.volume := by
          congr 1
          ext z
          simp [F, T, hψ_fderiv, smul_smul, inv_mul_cancel₀ ha]
      _ = j • ∫ y in Ω, F y ∂MeasureTheory.volume := hF_scale
      _ = j • (-∫ y in Ω, G y ∂MeasureTheory.volume) := by
            rw [hF_eq]
      _ = -(j • ∫ y in Ω, G y ∂MeasureTheory.volume) := by simp
      _ = -∫ z in Ω', G (T z) ∂MeasureTheory.volume := by
            rw [hG_scale]
      _ =
        -∫ z in (fun z : H ↦ a • z) ⁻¹' Ω,
          φ z • (a • du (a • z)) v ∂MeasureTheory.volume := by
          change -∫ z in Ω', G (T z) ∂MeasureTheory.volume =
            -∫ z in Ω',
              φ z • (a • du (a • z)) v ∂MeasureTheory.volume
          congr 1
          refine integral_congr_ae ?_
          exact Filter.Eventually.of_forall fun z ↦ by
            simp [G, T, ψ, e, Homeomorph.smulOfNeZero_symm_apply,
              smul_smul, inv_mul_cancel₀ ha]

/--
%%handwave
name:
  Finite distortion on compact sets for locally bi-Lipschitz changes of
  variables
statement:
  Let \(T:U\to\Omega\) be a locally bi-Lipschitz change of variables between
  open finite-dimensional Euclidean regions, with inverse \(S\).  If
  \(K\subset U\) is compact, then the pushforward of Lebesgue measure on
  \(K\) by \(T\) is bounded by a finite constant times Lebesgue measure on
  \(\Omega\).
proof:
  The set \(T(K)\) is compact and lies in \(\Omega\).  Cover it by finitely
  many neighborhoods on which the inverse map \(S\) is Lipschitz.  On each
  neighborhood, the standard Lipschitz image estimate for finite-dimensional
  Lebesgue measure bounds the measure of \(S(E)\) by a finite multiple of
  the measure of \(E\).  Since \(S\) recovers the points of \(K\) from their
  \(T\)-images, this gives the asserted domination of the pushforward
  measure after summing over the finite cover.
-/
theorem locallyBiLipschitz_map_restrict_compact_le_smul_volume
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {U Ω K : Set H} {T S : H → H}
    (_hU_open : IsOpen U) (_hΩ_open : IsOpen Ω)
    (_hT_maps : Set.MapsTo T U Ω) (_hS_maps : Set.MapsTo S Ω U)
    (_hS_left : ∀ x ∈ U, S (T x) = x)
    (_hT_left : ∀ y ∈ Ω, T (S y) = y)
    (_hT_lip : LocallyLipschitzOn U T)
    (_hS_lip : LocallyLipschitzOn Ω S)
    (_hT_qmp : Measure.QuasiMeasurePreserving T
      (MeasureTheory.volume.restrict U)
      (MeasureTheory.volume.restrict Ω))
    (_hS_qmp : Measure.QuasiMeasurePreserving S
      (MeasureTheory.volume.restrict Ω)
      (MeasureTheory.volume.restrict U))
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      Measure.map T (MeasureTheory.volume.restrict K) ≤
        C • MeasureTheory.volume.restrict Ω := by
  have hT_cont_K : ContinuousOn T K :=
    (_hT_lip.mono hKU).continuousOn
  have hTK_compact : IsCompact (T '' K) :=
    hK.image_of_continuousOn hT_cont_K
  have hTK_subset_Ω : T '' K ⊆ Ω := by
    rintro y ⟨x, hxK, rfl⟩
    exact _hT_maps (hKU hxK)
  have hS_lip_TK : LocallyLipschitzOn (T '' K) S :=
    _hS_lip.mono hTK_subset_Ω
  rcases
    LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
      hTK_compact hS_lip_TK with
    ⟨L, hS_lip_on_TK⟩
  rcases
    lipschitzOnWith_volume_image_le_smul
      (H := H) (A := T '' K) (F := S) hS_lip_on_TK with
    ⟨C, hC_ne_top, hS_image_le⟩
  refine ⟨C, hC_ne_top, ?_⟩
  have hK_le_U :
      MeasureTheory.volume.restrict K ≤ MeasureTheory.volume.restrict U :=
    Measure.restrict_mono hKU le_rfl
  have hT_aemeas_K :
      AEMeasurable T (MeasureTheory.volume.restrict K) :=
    _hT_qmp.aemeasurable.mono_measure hK_le_U
  refine Measure.le_iff.2 ?_
  intro B hB
  rw [Measure.map_apply_of_aemeasurable hT_aemeas_K hB,
    Measure.smul_apply, Measure.restrict_apply hB]
  have hpre_meas : MeasurableSet (T ⁻¹' B) :=
    _hT_qmp.measurable hB
  rw [Measure.restrict_apply hpre_meas]
  have hpre_subset :
      T ⁻¹' B ∩ K ⊆ S '' (B ∩ T '' K) := by
    intro x hx
    rcases hx with ⟨hxB, hxK⟩
    exact ⟨T x, ⟨hxB, ⟨x, hxK, rfl⟩⟩, _hS_left x (hKU hxK)⟩
  calc
    MeasureTheory.volume (T ⁻¹' B ∩ K)
        ≤ MeasureTheory.volume (S '' (B ∩ T '' K)) :=
      measure_mono hpre_subset
    _ ≤ C * MeasureTheory.volume (B ∩ T '' K) :=
      hS_image_le (B ∩ T '' K) Set.inter_subset_right
    _ ≤ C * MeasureTheory.volume (B ∩ Ω) := by
      simpa [mul_comm] using
        mul_le_mul_right
          (measure_mono (Set.inter_subset_inter_right B hTK_subset_Ω)) C

/--
%%handwave
name:
  Finite distortion into a compact target set
statement:
  Let \(T:U\to\Omega\) be a locally bi-Lipschitz change of variables between
  open finite-dimensional Euclidean regions.  If \(K\subset U\) is compact
  and \(T(K)\subset Q\), then the pushforward of Lebesgue measure on \(K\)
  is bounded by a finite constant times Lebesgue measure restricted to \(Q\).
proof:
  This is the same compact distortion argument as above.  The inverse map is
  Lipschitz on the compact image \(T(K)\), so the Lipschitz image estimate
  bounds the measure of \(S(E)\) by a finite multiple of the measure of
  \(E\cap T(K)\), and \(T(K)\subset Q\) replaces the ambient target region by
  the restricted target \(Q\).
-/
theorem locallyBiLipschitz_map_restrict_compact_le_smul_restrict_of_image_subset
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {U Ω K Q : Set H} {T S : H → H}
    (_hU_open : IsOpen U) (_hΩ_open : IsOpen Ω)
    (_hT_maps : Set.MapsTo T U Ω) (_hS_maps : Set.MapsTo S Ω U)
    (_hS_left : ∀ x ∈ U, S (T x) = x)
    (_hT_left : ∀ y ∈ Ω, T (S y) = y)
    (_hT_lip : LocallyLipschitzOn U T)
    (_hS_lip : LocallyLipschitzOn Ω S)
    (_hT_qmp : Measure.QuasiMeasurePreserving T
      (MeasureTheory.volume.restrict U)
      (MeasureTheory.volume.restrict Ω))
    (_hS_qmp : Measure.QuasiMeasurePreserving S
      (MeasureTheory.volume.restrict Ω)
      (MeasureTheory.volume.restrict U))
    (hK : IsCompact K) (hKU : K ⊆ U) (hTKQ : T '' K ⊆ Q) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      Measure.map T (MeasureTheory.volume.restrict K) ≤
        C • MeasureTheory.volume.restrict Q := by
  have hT_cont_K : ContinuousOn T K :=
    (_hT_lip.mono hKU).continuousOn
  have hTK_compact : IsCompact (T '' K) :=
    hK.image_of_continuousOn hT_cont_K
  have hTK_subset_Ω : T '' K ⊆ Ω := by
    rintro y ⟨x, hxK, rfl⟩
    exact _hT_maps (hKU hxK)
  have hS_lip_TK : LocallyLipschitzOn (T '' K) S :=
    _hS_lip.mono hTK_subset_Ω
  rcases
    LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
      hTK_compact hS_lip_TK with
    ⟨L, hS_lip_on_TK⟩
  rcases
    lipschitzOnWith_volume_image_le_smul
      (H := H) (A := T '' K) (F := S) hS_lip_on_TK with
    ⟨C, hC_ne_top, hS_image_le⟩
  refine ⟨C, hC_ne_top, ?_⟩
  have hK_le_U :
      MeasureTheory.volume.restrict K ≤ MeasureTheory.volume.restrict U :=
    Measure.restrict_mono hKU le_rfl
  have hT_aemeas_K :
      AEMeasurable T (MeasureTheory.volume.restrict K) :=
    _hT_qmp.aemeasurable.mono_measure hK_le_U
  refine Measure.le_iff.2 ?_
  intro B hB
  rw [Measure.map_apply_of_aemeasurable hT_aemeas_K hB,
    Measure.smul_apply, Measure.restrict_apply hB]
  have hpre_meas : MeasurableSet (T ⁻¹' B) :=
    _hT_qmp.measurable hB
  rw [Measure.restrict_apply hpre_meas]
  have hpre_subset :
      T ⁻¹' B ∩ K ⊆ S '' (B ∩ T '' K) := by
    intro x hx
    rcases hx with ⟨hxB, hxK⟩
    exact ⟨T x, ⟨hxB, ⟨x, hxK, rfl⟩⟩, _hS_left x (hKU hxK)⟩
  calc
    MeasureTheory.volume (T ⁻¹' B ∩ K)
        ≤ MeasureTheory.volume (S '' (B ∩ T '' K)) :=
      measure_mono hpre_subset
    _ ≤ C * MeasureTheory.volume (B ∩ T '' K) :=
      hS_image_le (B ∩ T '' K) Set.inter_subset_right
    _ ≤ C * MeasureTheory.volume (B ∩ Q) := by
      simpa [mul_comm] using
        mul_le_mul_right
          (measure_mono (Set.inter_subset_inter_right B hTKQ)) C

/--
%%handwave
name:
  Compact \(L^2\) pullback under a locally bi-Lipschitz change of variables
statement:
  Let \(T:U\to\Omega\) be a locally bi-Lipschitz change of variables between
  open finite-dimensional Euclidean regions.  If \(K\subset U\) is compact
  and \(u\in L^2(\Omega)\), then \(u\circ T\) belongs to \(L^2(K)\).
proof:
  The pushforward of Lebesgue measure on \(K\) by \(T\) is dominated by a
  finite multiple of Lebesgue measure on \(\Omega\).  Therefore an
  \(L^2(\Omega)\) function remains \(L^2\) with respect to this pushforward
  measure.  Pulling the resulting \(L^2\) statement back along \(T\) gives
  the claim on \(K\).
-/
theorem locallyBiLipschitz_value_pullback_memLp_on_compact
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {U Ω K : Set H} {T S : H → H}
    (hU_open : IsOpen U) (hΩ_open : IsOpen Ω)
    (hT_maps : Set.MapsTo T U Ω) (hS_maps : Set.MapsTo S Ω U)
    (hS_left : ∀ x ∈ U, S (T x) = x)
    (hT_left : ∀ y ∈ Ω, T (S y) = y)
    (hT_lip : LocallyLipschitzOn U T)
    (hS_lip : LocallyLipschitzOn Ω S)
    (hT_qmp : Measure.QuasiMeasurePreserving T
      (MeasureTheory.volume.restrict U)
      (MeasureTheory.volume.restrict Ω))
    (hS_qmp : Measure.QuasiMeasurePreserving S
      (MeasureTheory.volume.restrict Ω)
      (MeasureTheory.volume.restrict U))
    (hK : IsCompact K) (hKU : K ⊆ U)
    {u : H → ℝ}
    (hu : MemLp u 2 (MeasureTheory.volume.restrict Ω)) :
    MemLp (fun z : H ↦ u (T z)) 2
      (MeasureTheory.volume.restrict K) := by
  rcases
    locallyBiLipschitz_map_restrict_compact_le_smul_volume
      hU_open hΩ_open hT_maps hS_maps hS_left hT_left
      hT_lip hS_lip hT_qmp hS_qmp hK hKU with
    ⟨C, hC_ne_top, hmap_le⟩
  have hK_le_U :
      MeasureTheory.volume.restrict K ≤ MeasureTheory.volume.restrict U :=
    Measure.restrict_mono hKU le_rfl
  have hT_aemeas_K :
      AEMeasurable T (MeasureTheory.volume.restrict K) :=
    hT_qmp.aemeasurable.mono_measure hK_le_U
  have hu_map : MemLp u 2
      (Measure.map T (MeasureTheory.volume.restrict K)) :=
    hu.of_measure_le_smul hC_ne_top hmap_le
  simpa [Function.comp_def] using hu_map.comp_of_map hT_aemeas_K

/--
%%handwave
name:
  Vector-valued compact \(L^2\) pullbacks under a locally bi-Lipschitz
  change of variables
statement:
  Let \(T:U\to\Omega\) be a locally bi-Lipschitz change of variables between
  open finite-dimensional Euclidean regions.  If \(K\subset U\) is compact
  and \(u\in L^2(\Omega;E)\), for any normed target space \(E\), then
  \(u\circ T\) belongs to \(L^2(K;E)\).
proof:
  The pushforward of Lebesgue measure on \(K\) by \(T\) is dominated by a
  finite multiple of Lebesgue measure on \(\Omega\).  The \(L^2\) condition is
  monotone under such measure domination, and composition with \(T\) identifies
  the resulting norm with the \(L^2\) norm of \(u\circ T\) on \(K\).
-/
theorem locallyBiLipschitz_pullback_memLp_on_compact
    {H E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H] [NormedAddCommGroup E]
    {U Ω K : Set H} {T S : H → H}
    (hU_open : IsOpen U) (hΩ_open : IsOpen Ω)
    (hT_maps : Set.MapsTo T U Ω) (hS_maps : Set.MapsTo S Ω U)
    (hS_left : ∀ x ∈ U, S (T x) = x)
    (hT_left : ∀ y ∈ Ω, T (S y) = y)
    (hT_lip : LocallyLipschitzOn U T)
    (hS_lip : LocallyLipschitzOn Ω S)
    (hT_qmp : Measure.QuasiMeasurePreserving T
      (MeasureTheory.volume.restrict U)
      (MeasureTheory.volume.restrict Ω))
    (hS_qmp : Measure.QuasiMeasurePreserving S
      (MeasureTheory.volume.restrict Ω)
      (MeasureTheory.volume.restrict U))
    (hK : IsCompact K) (hKU : K ⊆ U)
    {u : H → E}
    (hu : MemLp u 2 (MeasureTheory.volume.restrict Ω)) :
    MemLp (fun z : H ↦ u (T z)) 2
      (MeasureTheory.volume.restrict K) := by
  rcases
    locallyBiLipschitz_map_restrict_compact_le_smul_volume
      hU_open hΩ_open hT_maps hS_maps hS_left hT_left
      hT_lip hS_lip hT_qmp hS_qmp hK hKU with
    ⟨C, hC_ne_top, hmap_le⟩
  have hK_le_U :
      MeasureTheory.volume.restrict K ≤ MeasureTheory.volume.restrict U :=
    Measure.restrict_mono hKU le_rfl
  have hT_aemeas_K :
      AEMeasurable T (MeasureTheory.volume.restrict K) :=
    hT_qmp.aemeasurable.mono_measure hK_le_U
  have hu_map : MemLp u 2
      (Measure.map T (MeasureTheory.volume.restrict K)) :=
    hu.of_measure_le_smul hC_ne_top hmap_le
  simpa [Function.comp_def] using hu_map.comp_of_map hT_aemeas_K

/--
%%handwave
name:
  Compact-target \(L^2\) pullbacks under locally bi-Lipschitz changes of
  variables
statement:
  Let \(T:U\to\Omega\) be a locally bi-Lipschitz change of variables.  If
  \(K\subset U\) is compact, \(T(K)\subset Q\), and \(u\in L^2(Q;E)\), then
  \(u\circ T\in L^2(K;E)\).
proof:
  Use the compact-target finite distortion estimate to dominate the
  pushforward of Lebesgue measure on \(K\) by a finite multiple of Lebesgue
  measure on \(Q\), then pull back the resulting \(L^2\) statement along
  \(T\).
-/
theorem locallyBiLipschitz_pullback_memLp_on_compact_of_image_subset
    {H E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H] [NormedAddCommGroup E]
    {U Ω K Q : Set H} {T S : H → H}
    (hU_open : IsOpen U) (hΩ_open : IsOpen Ω)
    (hT_maps : Set.MapsTo T U Ω) (hS_maps : Set.MapsTo S Ω U)
    (hS_left : ∀ x ∈ U, S (T x) = x)
    (hT_left : ∀ y ∈ Ω, T (S y) = y)
    (hT_lip : LocallyLipschitzOn U T)
    (hS_lip : LocallyLipschitzOn Ω S)
    (hT_qmp : Measure.QuasiMeasurePreserving T
      (MeasureTheory.volume.restrict U)
      (MeasureTheory.volume.restrict Ω))
    (hS_qmp : Measure.QuasiMeasurePreserving S
      (MeasureTheory.volume.restrict Ω)
      (MeasureTheory.volume.restrict U))
    (hK : IsCompact K) (hKU : K ⊆ U) (hTKQ : T '' K ⊆ Q)
    {u : H → E}
    (hu : MemLp u 2 (MeasureTheory.volume.restrict Q)) :
    MemLp (fun z : H ↦ u (T z)) 2
      (MeasureTheory.volume.restrict K) := by
  rcases
    locallyBiLipschitz_map_restrict_compact_le_smul_restrict_of_image_subset
      hU_open hΩ_open hT_maps hS_maps hS_left hT_left
      hT_lip hS_lip hT_qmp hS_qmp hK hKU hTKQ with
    ⟨C, hC_ne_top, hmap_le⟩
  have hK_le_U :
      MeasureTheory.volume.restrict K ≤ MeasureTheory.volume.restrict U :=
    Measure.restrict_mono hKU le_rfl
  have hT_aemeas_K :
      AEMeasurable T (MeasureTheory.volume.restrict K) :=
    hT_qmp.aemeasurable.mono_measure hK_le_U
  have hu_map : MemLp u 2
      (Measure.map T (MeasureTheory.volume.restrict K)) :=
    hu.of_measure_le_smul hC_ne_top hmap_le
  simpa [Function.comp_def] using hu_map.comp_of_map hT_aemeas_K

/--
%%handwave
name:
  Compact-target \(L^2\) convergence is preserved by pullback
statement:
  In the same locally bi-Lipschitz setting, if \(f_n\to0\) in \(L^2(Q;E)\)
  and \(T(K)\subset Q\), then \(f_n\circ T\to0\) in \(L^2(K;E)\).
proof:
  The compact-target measure distortion estimate gives a fixed finite
  constant \(C\) such that \(T_\#(dx|_K)\le C\,dx|_Q\).  Hence the
  \(L^2(K)\)-norm of \(f_n\circ T\) is bounded by a finite constant times the
  \(L^2(Q)\)-norm of \(f_n\), which tends to zero.
-/
theorem locallyBiLipschitz_pullback_memLp_and_eLpNorm_tendsto_zero_on_compact_of_image_subset
    {H E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H] [NormedAddCommGroup E]
    {U Ω K Q : Set H} {T S : H → H}
    (hU_open : IsOpen U) (hΩ_open : IsOpen Ω)
    (hT_maps : Set.MapsTo T U Ω) (hS_maps : Set.MapsTo S Ω U)
    (hS_left : ∀ x ∈ U, S (T x) = x)
    (hT_left : ∀ y ∈ Ω, T (S y) = y)
    (hT_lip : LocallyLipschitzOn U T)
    (hS_lip : LocallyLipschitzOn Ω S)
    (hT_qmp : Measure.QuasiMeasurePreserving T
      (MeasureTheory.volume.restrict U)
      (MeasureTheory.volume.restrict Ω))
    (hS_qmp : Measure.QuasiMeasurePreserving S
      (MeasureTheory.volume.restrict Ω)
      (MeasureTheory.volume.restrict U))
    (hK : IsCompact K) (hKU : K ⊆ U) (hTKQ : T '' K ⊆ Q)
    {f : ℕ → H → E}
    (hf_mem : ∀ n : ℕ, MemLp (f n) 2 (MeasureTheory.volume.restrict Q))
    (hf_tendsto :
      Filter.Tendsto
        (fun n : ℕ ↦ eLpNorm (f n) 2 (MeasureTheory.volume.restrict Q))
        Filter.atTop (𝓝 0)) :
    (∀ n : ℕ,
      MemLp (fun z : H ↦ f n (T z)) 2
        (MeasureTheory.volume.restrict K)) ∧
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm (fun z : H ↦ f n (T z)) 2
            (MeasureTheory.volume.restrict K))
        Filter.atTop (𝓝 0) := by
  rcases
    locallyBiLipschitz_map_restrict_compact_le_smul_restrict_of_image_subset
      hU_open hΩ_open hT_maps hS_maps hS_left hT_left
      hT_lip hS_lip hT_qmp hS_qmp hK hKU hTKQ with
    ⟨C, hC_ne_top, hmap_le⟩
  have hK_le_U :
      MeasureTheory.volume.restrict K ≤ MeasureTheory.volume.restrict U :=
    Measure.restrict_mono hKU le_rfl
  have hT_aemeas_K :
      AEMeasurable T (MeasureTheory.volume.restrict K) :=
    hT_qmp.aemeasurable.mono_measure hK_le_U
  have hmap_ac :
      Measure.map T (MeasureTheory.volume.restrict K) ≪
        MeasureTheory.volume.restrict Q :=
    Measure.absolutelyContinuous_of_le_smul hmap_le
  let A : ℝ≥0∞ := C ^ ((1 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal
  have hA_ne_top : A ≠ ⊤ := by
    dsimp [A]
    exact ENNReal.rpow_ne_top_of_nonneg
      (by positivity : 0 ≤ ((1 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal)
      hC_ne_top
  have hbound :
      ∀ n : ℕ,
        eLpNorm (fun z : H ↦ f n (T z)) 2
            (MeasureTheory.volume.restrict K) ≤
          A * eLpNorm (f n) 2 (MeasureTheory.volume.restrict Q) := by
    intro n
    have hf_map_aesm :
        AEStronglyMeasurable (f n)
          (Measure.map T (MeasureTheory.volume.restrict K)) :=
      (hf_mem n).aestronglyMeasurable.mono_ac hmap_ac
    calc
      eLpNorm (fun z : H ↦ f n (T z)) 2
          (MeasureTheory.volume.restrict K)
          = eLpNorm (f n) 2
              (Measure.map T (MeasureTheory.volume.restrict K)) := by
            exact (eLpNorm_map_measure hf_map_aesm hT_aemeas_K).symm
      _ ≤ eLpNorm (f n) 2 (C • MeasureTheory.volume.restrict Q) :=
            eLpNorm_mono_measure (f n) hmap_le
      _ = A * eLpNorm (f n) 2 (MeasureTheory.volume.restrict Q) := by
            rw [eLpNorm_smul_measure_of_ne_top
              (show (2 : ℝ≥0∞) ≠ (∞ : ℝ≥0∞) from ENNReal.coe_ne_top),
              smul_eq_mul]
  have hmul :
      Filter.Tendsto
        (fun n : ℕ ↦
          A * eLpNorm (f n) 2 (MeasureTheory.volume.restrict Q))
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
    have h := ENNReal.Tendsto.const_mul hf_tendsto (Or.inr hA_ne_top)
    simpa using h
  refine ⟨?_, ?_⟩
  · intro n
    exact
      locallyBiLipschitz_pullback_memLp_on_compact_of_image_subset
        hU_open hΩ_open hT_maps hS_maps hS_left hT_left
        hT_lip hS_lip hT_qmp hS_qmp hK hKU hTKQ (hf_mem n)
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hmul
      (fun n ↦ zero_le)
      hbound

/--
%%handwave
name:
  Compact \(L^2\) pullbacks under a finite distortion estimate
statement:
  Let \(T:U\to\Omega\) be a measurable map between finite-dimensional
  Euclidean regions.  If \(K\subset U\) is compact, \(T(K)\subset Q\), and the
  pushforward of Lebesgue measure on \(K\) is bounded by a finite multiple of
  Lebesgue measure on \(Q\), then every \(L^2(Q)\) field pulls back to an
  \(L^2(K)\) field.
proof:
  Use the measure domination to regard the \(L^2(Q)\) field as \(L^2\) for
  the pushed-forward measure, then identify this norm with the norm of the
  pulled-back field on \(K\).
-/
theorem compactDistortion_pullback_memLp_on_compact_of_image_subset
    {D H E : Type}
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [MeasureSpace D] [BorelSpace D]
    [Measure.IsAddHaarMeasure (volume : Measure D)]
    [FiniteDimensional ℝ D]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H] [NormedAddCommGroup E]
    {U K : Set D} {Ω QH : Set H} {T : D → H}
    (hT_qmp : Measure.QuasiMeasurePreserving T
      (MeasureTheory.volume.restrict U)
      (MeasureTheory.volume.restrict Ω))
    (_hK : IsCompact K) (hKU : K ⊆ U) (_hTKQ : T '' K ⊆ QH)
    (hmap :
      ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
        Measure.map T (MeasureTheory.volume.restrict K) ≤
          C • MeasureTheory.volume.restrict QH)
    {u : H → E}
    (hu : MemLp u 2 (MeasureTheory.volume.restrict QH)) :
    MemLp (fun z : D ↦ u (T z)) 2
      (MeasureTheory.volume.restrict K) := by
  rcases hmap with ⟨C, hC_ne_top, hmap_le⟩
  have hK_le_U :
      MeasureTheory.volume.restrict K ≤ MeasureTheory.volume.restrict U :=
    Measure.restrict_mono hKU le_rfl
  have hT_aemeas_K :
      AEMeasurable T (MeasureTheory.volume.restrict K) :=
    hT_qmp.aemeasurable.mono_measure hK_le_U
  have hu_map : MemLp u 2
      (Measure.map T (MeasureTheory.volume.restrict K)) :=
    hu.of_measure_le_smul hC_ne_top hmap_le
  simpa [Function.comp_def] using hu_map.comp_of_map hT_aemeas_K

/--
%%handwave
name:
  Compact \(L^2\) convergence pulls back under finite distortion
statement:
  Under the same compact finite-distortion estimate, if \(f_n\to0\) in
  \(L^2(Q)\), then \(f_n\circ T\to0\) in \(L^2(K)\).
proof:
  The finite measure domination gives a uniform bound of the pulled-back
  \(L^2(K)\) norm by a finite constant times the \(L^2(Q)\) norm.  The latter
  tends to zero.
-/
theorem compactDistortion_pullback_memLp_and_eLpNorm_tendsto_zero_on_compact_of_image_subset
    {D H E : Type}
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [MeasureSpace D] [BorelSpace D]
    [Measure.IsAddHaarMeasure (volume : Measure D)]
    [FiniteDimensional ℝ D]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H] [NormedAddCommGroup E]
    {U K : Set D} {Ω Q : Set H} {T : D → H}
    (hT_qmp : Measure.QuasiMeasurePreserving T
      (MeasureTheory.volume.restrict U)
      (MeasureTheory.volume.restrict Ω))
    (hK : IsCompact K) (hKU : K ⊆ U) (hTKQ : T '' K ⊆ Q)
    (hmap :
      ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
        Measure.map T (MeasureTheory.volume.restrict K) ≤
          C • MeasureTheory.volume.restrict Q)
    {f : ℕ → H → E}
    (hf_mem : ∀ n : ℕ, MemLp (f n) 2 (MeasureTheory.volume.restrict Q))
    (hf_tendsto :
      Filter.Tendsto
        (fun n : ℕ ↦ eLpNorm (f n) 2 (MeasureTheory.volume.restrict Q))
        Filter.atTop (𝓝 0)) :
    (∀ n : ℕ,
      MemLp (fun z : D ↦ f n (T z)) 2
        (MeasureTheory.volume.restrict K)) ∧
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm (fun z : D ↦ f n (T z)) 2
            (MeasureTheory.volume.restrict K))
        Filter.atTop (𝓝 0) := by
  rcases hmap with ⟨C, hC_ne_top, hmap_le⟩
  have hK_le_U :
      MeasureTheory.volume.restrict K ≤ MeasureTheory.volume.restrict U :=
    Measure.restrict_mono hKU le_rfl
  have hT_aemeas_K :
      AEMeasurable T (MeasureTheory.volume.restrict K) :=
    hT_qmp.aemeasurable.mono_measure hK_le_U
  have hmap_ac :
      Measure.map T (MeasureTheory.volume.restrict K) ≪
        MeasureTheory.volume.restrict Q :=
    Measure.absolutelyContinuous_of_le_smul hmap_le
  let A : ℝ≥0∞ := C ^ ((1 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal
  have hA_ne_top : A ≠ ⊤ := by
    dsimp [A]
    exact ENNReal.rpow_ne_top_of_nonneg
      (by positivity : 0 ≤ ((1 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal)
      hC_ne_top
  have hbound :
      ∀ n : ℕ,
        eLpNorm (fun z : D ↦ f n (T z)) 2
            (MeasureTheory.volume.restrict K) ≤
          A * eLpNorm (f n) 2 (MeasureTheory.volume.restrict Q) := by
    intro n
    have hf_map_aesm :
        AEStronglyMeasurable (f n)
          (Measure.map T (MeasureTheory.volume.restrict K)) :=
      (hf_mem n).aestronglyMeasurable.mono_ac hmap_ac
    calc
      eLpNorm (fun z : D ↦ f n (T z)) 2
          (MeasureTheory.volume.restrict K)
          = eLpNorm (f n) 2
              (Measure.map T (MeasureTheory.volume.restrict K)) := by
            exact (eLpNorm_map_measure hf_map_aesm hT_aemeas_K).symm
      _ ≤ eLpNorm (f n) 2 (C • MeasureTheory.volume.restrict Q) :=
            eLpNorm_mono_measure (f n) hmap_le
      _ = A * eLpNorm (f n) 2 (MeasureTheory.volume.restrict Q) := by
            rw [eLpNorm_smul_measure_of_ne_top
              (show (2 : ℝ≥0∞) ≠ (∞ : ℝ≥0∞) from ENNReal.coe_ne_top),
              smul_eq_mul]
  have hmul :
      Filter.Tendsto
        (fun n : ℕ ↦
          A * eLpNorm (f n) 2 (MeasureTheory.volume.restrict Q))
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
    have h := ENNReal.Tendsto.const_mul hf_tendsto (Or.inr hA_ne_top)
    simpa using h
  refine ⟨?_, ?_⟩
  · intro n
    exact
      compactDistortion_pullback_memLp_on_compact_of_image_subset
        hT_qmp hK hKU hTKQ ⟨C, hC_ne_top, hmap_le⟩ (hf_mem n)
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hmul
      (fun n ↦ zero_le)
      hbound

/--
%%handwave
name:
  Compact derivative bounds for locally Lipschitz maps
statement:
  Let \(T\) be locally Lipschitz on an open finite-dimensional Euclidean
  region \(U\).  If \(K\subset U\) is compact, then for each vector \(v\) the
  directional derivative \(dT_xv\) is uniformly bounded for \(x\in K\).
proof:
  Enlarge \(K\) to a compact closed metric thickening still contained in
  \(U\).  Local Lipschitzness gives a single Lipschitz constant on this
  compact thickening.  Since the thickening is a neighborhood of every point
  of \(K\), the standard bound of the derivative by a local Lipschitz
  constant gives a uniform operator-norm bound, and evaluating at \(v\) gives
  the claimed bound.
-/
theorem locallyLipschitzOn_fderiv_apply_norm_bound_on_compact
    {H E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ H]
    {U K : Set H} {T : H → E}
    (hU_open : IsOpen U)
    (hT_lip : LocallyLipschitzOn U T)
    (hK : IsCompact K) (hKU : K ⊆ U) (v : H) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ z ∈ K, ‖fderiv ℝ (fun x : H ↦ T x) z v‖ ≤ C := by
  haveI : ProperSpace H := FiniteDimensional.proper ℝ H
  rcases hK.exists_cthickening_subset_open hU_open hKU with
    ⟨δ, hδ_pos, hδU⟩
  let P : Set H := Metric.cthickening δ K
  have hP_compact : IsCompact P := by
    dsimp [P]
    exact hK.cthickening
  have hT_lip_P : LocallyLipschitzOn P T :=
    hT_lip.mono hδU
  rcases hT_lip_P.exists_lipschitzOnWith_of_compact hP_compact with
    ⟨L, hL⟩
  refine ⟨(L : ℝ) * ‖v‖, mul_nonneg L.coe_nonneg (norm_nonneg v), ?_⟩
  intro z hz
  have hz_thick : z ∈ Metric.thickening δ K :=
    Metric.self_subset_thickening hδ_pos K hz
  have hthick_nhds : Metric.thickening δ K ∈ 𝓝 z :=
    Metric.isOpen_thickening.mem_nhds hz_thick
  have hP_nhds : P ∈ 𝓝 z :=
    Filter.mem_of_superset hthick_nhds
      (by
        intro y hy
        exact Metric.thickening_subset_cthickening δ K hy)
  have hnorm_fderiv :
      ‖fderiv ℝ (fun x : H ↦ T x) z‖ ≤ (L : ℝ) := by
    simpa [P] using
      norm_fderiv_le_of_lipschitzOn (𝕜 := ℝ) hP_nhds hL
  calc
    ‖fderiv ℝ (fun x : H ↦ T x) z v‖
        ≤ ‖fderiv ℝ (fun x : H ↦ T x) z‖ * ‖v‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ (L : ℝ) * ‖v‖ :=
      mul_le_mul_of_nonneg_right hnorm_fderiv (norm_nonneg v)

/--
%%handwave
name:
  Compact \(L^2\) pullback of evaluated derivative fields under finite
  distortion
statement:
  Let \(T:U\to\Omega\) be locally Lipschitz and satisfy a finite compact
  distortion estimate from \(K\subset U\) into \(Q\subset\Omega\).  If
  \(A\in L^2(Q;\operatorname{Hom}(H,\mathbb R))\), then
  \(x\mapsto A(Tx)(dT_xv)\) is \(L^2\) on \(K\).
proof:
  Pull back the linear-map-valued field by the compact distortion estimate.
  The local Lipschitz bound gives a uniform bound for \(dT_xv\) on \(K\), and
  the operator norm estimate controls the evaluated scalar field.
-/
theorem compactDistortion_derivative_eval_pullback_memLp_on_compact_of_image_subset
    {D H : Type}
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [MeasureSpace D] [BorelSpace D]
    [Measure.IsAddHaarMeasure (volume : Measure D)]
    [FiniteDimensional ℝ D]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {U K : Set D} {Ω Q : Set H} {T : D → H}
    (hU_open : IsOpen U)
    (hT_lip : LocallyLipschitzOn U T)
    (hT_qmp : Measure.QuasiMeasurePreserving T
      (MeasureTheory.volume.restrict U)
      (MeasureTheory.volume.restrict Ω))
    (hK : IsCompact K) (hKU : K ⊆ U) (hTKQ : T '' K ⊆ Q)
    (hmap :
      ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
        Measure.map T (MeasureTheory.volume.restrict K) ≤
          C • MeasureTheory.volume.restrict Q)
    {du : H → H →L[ℝ] ℝ}
    (hdu : MemLp du 2 (MeasureTheory.volume.restrict Q))
    (v : D) :
    MemLp
      (fun z : D ↦
        ((du (T z)).comp (fderiv ℝ (fun x : D ↦ T x) z)) v)
      2 (MeasureTheory.volume.restrict K) := by
  haveI : CompleteSpace H := FiniteDimensional.complete ℝ H
  have hdu_pull_K : MemLp (fun z : D ↦ du (T z)) 2
      (MeasureTheory.volume.restrict K) :=
    compactDistortion_pullback_memLp_on_compact_of_image_subset
      hT_qmp hK hKU hTKQ hmap hdu
  let Dv : D → H :=
    fun z ↦ fderiv ℝ (fun x : D ↦ T x) z v
  have hDv_aesm : AEStronglyMeasurable Dv
      (MeasureTheory.volume.restrict K) := by
    dsimp [Dv]
    exact (measurable_fderiv_apply_const ℝ (fun x : D ↦ T x) v).aestronglyMeasurable
  let evalCLM : (H →L[ℝ] ℝ) →L[ℝ] H →L[ℝ] ℝ :=
    (isBoundedBilinearMap_apply
      (𝕜 := ℝ) (E := H) (F := ℝ)).toContinuousLinearMap
  have hfield_aesm :
      AEStronglyMeasurable
        (fun z : D ↦ du (T z) (Dv z))
        (MeasureTheory.volume.restrict K) := by
    simpa [evalCLM] using
      evalCLM.aestronglyMeasurable_comp₂
        hdu_pull_K.aestronglyMeasurable hDv_aesm
  rcases
    locallyLipschitzOn_fderiv_apply_norm_bound_on_compact
      hU_open hT_lip hK hKU v with
    ⟨C, _hC_nonneg, hC_bound⟩
  have hpointwise :
      ∀ᵐ z ∂MeasureTheory.volume.restrict K,
        ‖du (T z) (Dv z)‖ ≤ C * ‖du (T z)‖ :=
    ae_restrict_of_forall_mem hK.measurableSet fun z hz ↦ by
      have hDv_bound : ‖Dv z‖ ≤ C := by
        simpa [Dv] using hC_bound z hz
      calc
        ‖du (T z) (Dv z)‖ ≤ ‖du (T z)‖ * ‖Dv z‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖du (T z)‖ * C :=
          mul_le_mul_of_nonneg_left hDv_bound (norm_nonneg _)
        _ = C * ‖du (T z)‖ := by ring
  have hfield_mem : MemLp (fun z : D ↦ du (T z) (Dv z)) 2
      (MeasureTheory.volume.restrict K) :=
    MemLp.of_le_mul hdu_pull_K hfield_aesm hpointwise
  simpa [Dv, ContinuousLinearMap.comp_apply] using hfield_mem

/--
%%handwave
name:
  Compact \(L^2\) pullback of the evaluated derivative field
statement:
  Let \(T:U\to\Omega\) be a locally bi-Lipschitz change of variables between
  open finite-dimensional Euclidean regions.  If \(K\subset U\) is compact and
  \(du\in L^2(\Omega;\operatorname{Hom}(H,\mathbb R))\), then for every
  \(v\in H\) the scalar field
  \[
    x\mapsto du(Tx)(dT_xv)
  \]
  belongs to \(L^2(K)\).
proof:
  First pull back the linear-map-valued field \(du\) to \(K\).  On compact
  subsets of \(U\), the derivative of the locally Lipschitz map \(T\) is
  essentially bounded, with the bound obtained from finitely many local
  Lipschitz constants.  The pointwise operator estimate
  \(\lvert du(Tx)(dT_xv)\rvert\le C\|du(Tx)\|\) then gives the \(L^2\) bound.
-/
theorem locallyBiLipschitz_derivative_eval_pullback_memLp_on_compact
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {U Ω K : Set H} {T S : H → H}
    (hU_open : IsOpen U) (hΩ_open : IsOpen Ω)
    (hT_maps : Set.MapsTo T U Ω) (hS_maps : Set.MapsTo S Ω U)
    (hS_left : ∀ x ∈ U, S (T x) = x)
    (hT_left : ∀ y ∈ Ω, T (S y) = y)
    (hT_lip : LocallyLipschitzOn U T)
    (hS_lip : LocallyLipschitzOn Ω S)
    (hT_qmp : Measure.QuasiMeasurePreserving T
      (MeasureTheory.volume.restrict U)
      (MeasureTheory.volume.restrict Ω))
    (hS_qmp : Measure.QuasiMeasurePreserving S
      (MeasureTheory.volume.restrict Ω)
      (MeasureTheory.volume.restrict U))
    (hK : IsCompact K) (hKU : K ⊆ U)
    {du : H → H →L[ℝ] ℝ}
    (hdu : MemLp du 2 (MeasureTheory.volume.restrict Ω))
    (v : H) :
    MemLp
      (fun z : H ↦
        ((du (T z)).comp (fderiv ℝ (fun x : H ↦ T x) z)) v)
      2 (MeasureTheory.volume.restrict K) := by
  haveI : CompleteSpace H := FiniteDimensional.complete ℝ H
  have _hdu_pull_K : MemLp (fun z : H ↦ du (T z)) 2
      (MeasureTheory.volume.restrict K) :=
    locallyBiLipschitz_pullback_memLp_on_compact
      hU_open hΩ_open hT_maps hS_maps hS_left hT_left
      hT_lip hS_lip hT_qmp hS_qmp hK hKU hdu
  let Dv : H → H :=
    fun z ↦ fderiv ℝ (fun x : H ↦ T x) z v
  have hDv_aesm : AEStronglyMeasurable Dv
      (MeasureTheory.volume.restrict K) := by
    dsimp [Dv]
    exact (measurable_fderiv_apply_const ℝ (fun x : H ↦ T x) v).aestronglyMeasurable
  let evalCLM : (H →L[ℝ] ℝ) →L[ℝ] H →L[ℝ] ℝ :=
    (isBoundedBilinearMap_apply
      (𝕜 := ℝ) (E := H) (F := ℝ)).toContinuousLinearMap
  have hfield_aesm :
      AEStronglyMeasurable
        (fun z : H ↦ du (T z) (Dv z))
        (MeasureTheory.volume.restrict K) := by
    simpa [evalCLM] using
      evalCLM.aestronglyMeasurable_comp₂
        _hdu_pull_K.aestronglyMeasurable hDv_aesm
  rcases
    locallyLipschitzOn_fderiv_apply_norm_bound_on_compact
      hU_open hT_lip hK hKU v with
    ⟨C, _hC_nonneg, hC_bound⟩
  have hpointwise :
      ∀ᵐ z ∂MeasureTheory.volume.restrict K,
        ‖du (T z) (Dv z)‖ ≤ C * ‖du (T z)‖ :=
    ae_restrict_of_forall_mem hK.measurableSet fun z hz ↦ by
      have hDv_bound : ‖Dv z‖ ≤ C := by
        simpa [Dv] using hC_bound z hz
      calc
        ‖du (T z) (Dv z)‖ ≤ ‖du (T z)‖ * ‖Dv z‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖du (T z)‖ * C :=
          mul_le_mul_of_nonneg_left hDv_bound (norm_nonneg _)
        _ = C * ‖du (T z)‖ := by ring
  have hfield_mem : MemLp (fun z : H ↦ du (T z) (Dv z)) 2
      (MeasureTheory.volume.restrict K) :=
    MemLp.of_le_mul _hdu_pull_K hfield_aesm hpointwise
  simpa [Dv, ContinuousLinearMap.comp_apply] using hfield_mem

/--
%%handwave
name:
  Compact-target \(L^2\) pullback of evaluated derivative fields
statement:
  Let \(T:U\to\Omega\) be a locally bi-Lipschitz change of variables.  If
  \(K\subset U\) is compact, \(T(K)\subset Q\), and
  \(A\in L^2(Q;\operatorname{Hom}(H,\mathbb R))\), then
  \(x\mapsto A(Tx)(dT_xv)\) belongs to \(L^2(K)\).
proof:
  Pull back the linear-map-valued field from \(Q\) to \(K\) using the
  compact-target distortion estimate.  The derivative \(dT_xv\) is bounded on
  \(K\), so evaluating the pulled-back field on this bounded vector field
  preserves the \(L^2\) bound.
-/
theorem locallyBiLipschitz_derivative_eval_pullback_memLp_on_compact_of_image_subset
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {U Ω K Q : Set H} {T S : H → H}
    (hU_open : IsOpen U) (hΩ_open : IsOpen Ω)
    (hT_maps : Set.MapsTo T U Ω) (hS_maps : Set.MapsTo S Ω U)
    (hS_left : ∀ x ∈ U, S (T x) = x)
    (hT_left : ∀ y ∈ Ω, T (S y) = y)
    (hT_lip : LocallyLipschitzOn U T)
    (hS_lip : LocallyLipschitzOn Ω S)
    (hT_qmp : Measure.QuasiMeasurePreserving T
      (MeasureTheory.volume.restrict U)
      (MeasureTheory.volume.restrict Ω))
    (hS_qmp : Measure.QuasiMeasurePreserving S
      (MeasureTheory.volume.restrict Ω)
      (MeasureTheory.volume.restrict U))
    (hK : IsCompact K) (hKU : K ⊆ U) (hTKQ : T '' K ⊆ Q)
    {du : H → H →L[ℝ] ℝ}
    (hdu : MemLp du 2 (MeasureTheory.volume.restrict Q))
    (v : H) :
    MemLp
      (fun z : H ↦
        ((du (T z)).comp (fderiv ℝ (fun x : H ↦ T x) z)) v)
      2 (MeasureTheory.volume.restrict K) := by
  haveI : CompleteSpace H := FiniteDimensional.complete ℝ H
  have _hdu_pull_K : MemLp (fun z : H ↦ du (T z)) 2
      (MeasureTheory.volume.restrict K) :=
    locallyBiLipschitz_pullback_memLp_on_compact_of_image_subset
      hU_open hΩ_open hT_maps hS_maps hS_left hT_left
      hT_lip hS_lip hT_qmp hS_qmp hK hKU hTKQ hdu
  let Dv : H → H :=
    fun z ↦ fderiv ℝ (fun x : H ↦ T x) z v
  have hDv_aesm : AEStronglyMeasurable Dv
      (MeasureTheory.volume.restrict K) := by
    dsimp [Dv]
    exact (measurable_fderiv_apply_const ℝ (fun x : H ↦ T x) v).aestronglyMeasurable
  let evalCLM : (H →L[ℝ] ℝ) →L[ℝ] H →L[ℝ] ℝ :=
    (isBoundedBilinearMap_apply
      (𝕜 := ℝ) (E := H) (F := ℝ)).toContinuousLinearMap
  have hfield_aesm :
      AEStronglyMeasurable
        (fun z : H ↦ du (T z) (Dv z))
        (MeasureTheory.volume.restrict K) := by
    simpa [evalCLM] using
      evalCLM.aestronglyMeasurable_comp₂
        _hdu_pull_K.aestronglyMeasurable hDv_aesm
  rcases
    locallyLipschitzOn_fderiv_apply_norm_bound_on_compact
      hU_open hT_lip hK hKU v with
    ⟨C, _hC_nonneg, hC_bound⟩
  have hpointwise :
      ∀ᵐ z ∂MeasureTheory.volume.restrict K,
        ‖du (T z) (Dv z)‖ ≤ C * ‖du (T z)‖ :=
    ae_restrict_of_forall_mem hK.measurableSet fun z hz ↦ by
      have hDv_bound : ‖Dv z‖ ≤ C := by
        simpa [Dv] using hC_bound z hz
      calc
        ‖du (T z) (Dv z)‖ ≤ ‖du (T z)‖ * ‖Dv z‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖du (T z)‖ * C :=
          mul_le_mul_of_nonneg_left hDv_bound (norm_nonneg _)
        _ = C * ‖du (T z)‖ := by ring
  have hfield_mem : MemLp (fun z : H ↦ du (T z) (Dv z)) 2
      (MeasureTheory.volume.restrict K) :=
    MemLp.of_le_mul _hdu_pull_K hfield_aesm hpointwise
  simpa [Dv, ContinuousLinearMap.comp_apply] using hfield_mem

/--
%%handwave
name:
  Compactly supported value pullbacks are integrable under locally
  bi-Lipschitz changes of variables
statement:
  Let \(T:U\to\Omega\) be a locally bi-Lipschitz change of variables between
  open finite-dimensional Euclidean regions.  If \(u\in L^2(\Omega)\), then
  for every compactly supported smooth test \(\varphi\) on \(U\) and every
  direction \(v\), the function
  \[
    x\mapsto D\varphi(x)[v]\,u(Tx)
  \]
  is integrable on \(U\).
proof:
  The closed support of \(D\varphi(\cdot)[v]\) is compact and contained in
  \(U\).  On a compact neighborhood of this support the map \(T\) is
  bi-Lipschitz with finite distortion, so pullback by \(T\) is bounded from
  \(L^2\) on the image to \(L^2\) on the support.  Since the multiplier
  \(D\varphi(\cdot)[v]\) is continuous and compactly supported, the product
  is \(L^2\), hence integrable on this finite-measure support.
-/
theorem locallyBiLipschitz_value_pullback_test_integrable
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {U Ω : Set H} {T S : H → H}
    (_hU_open : IsOpen U) (_hΩ_open : IsOpen Ω)
    (_hT_maps : Set.MapsTo T U Ω) (_hS_maps : Set.MapsTo S Ω U)
    (_hS_left : ∀ x ∈ U, S (T x) = x)
    (_hT_left : ∀ y ∈ Ω, T (S y) = y)
    (_hT_lip : LocallyLipschitzOn U T)
    (_hS_lip : LocallyLipschitzOn Ω S)
    (_hT_qmp : Measure.QuasiMeasurePreserving T
      (MeasureTheory.volume.restrict U)
      (MeasureTheory.volume.restrict Ω))
    (_hS_qmp : Measure.QuasiMeasurePreserving S
      (MeasureTheory.volume.restrict Ω)
      (MeasureTheory.volume.restrict U))
    {u : H → ℝ}
    (_hu : MemLp u 2 (MeasureTheory.volume.restrict Ω))
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction U) (v : H) :
    Integrable
      (fun z : H ↦ (fderiv ℝ (φ : H → ℝ) z v) • u (T z))
      (MeasureTheory.volume.restrict U) := by
  let a : H → ℝ := fun z ↦ fderiv ℝ (φ : H → ℝ) z v
  let K : Set H := tsupport a
  have ha_cont : Continuous a :=
    ((φ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const)
  have ha_tsupport_subset :
      K ⊆ tsupport (φ : H → ℝ) := by
    simpa [K, a] using
      (tsupport_fderiv_apply_subset (𝕜 := ℝ)
        (f := (φ : H → ℝ)) v)
  have hK_compact : IsCompact K :=
    φ.compact_support.of_isClosed_subset
      (isClosed_tsupport _) ha_tsupport_subset
  have hK_U : K ⊆ U := ha_tsupport_subset.trans φ.support_subset
  have hu_pull_K : MemLp (fun z : H ↦ u (T z)) 2
      (MeasureTheory.volume.restrict K) :=
    locallyBiLipschitz_value_pullback_memLp_on_compact
      _hU_open _hΩ_open _hT_maps _hS_maps _hS_left _hT_left
      _hT_lip _hS_lip _hT_qmp _hS_qmp hK_compact hK_U _hu
  have hprod_K : MemLp (fun z : H ↦ a z * u (T z)) 2
      (MeasureTheory.volume.restrict K) :=
    memLp_restrict_mul_left_of_isCompact_of_continuousOn
      hK_compact ha_cont.continuousOn hu_pull_K
  haveI : IsFiniteMeasure (MeasureTheory.volume.restrict K) :=
    isFiniteMeasure_restrict.2 hK_compact.measure_ne_top
  have hprod_int_K : Integrable (fun z : H ↦ a z * u (T z))
      (MeasureTheory.volume.restrict K) :=
    hprod_K.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hprod_support :
      Function.support (fun z : H ↦ a z * u (T z)) ⊆ K := by
    intro z hz
    exact subset_tsupport a
      (Function.support_mul_subset_left
        (f := a) (g := fun z : H ↦ u (T z)) hz)
  have hprod_global : Integrable (fun z : H ↦ a z * u (T z))
      (MeasureTheory.volume : Measure H) :=
    (integrableOn_iff_integrable_of_support_subset hprod_support).mp
      hprod_int_K
  have hprod_U : Integrable (fun z : H ↦ a z * u (T z))
      (MeasureTheory.volume.restrict U) :=
    hprod_global.mono_measure
      (Measure.restrict_le_self (μ := MeasureTheory.volume) (s := U))
  simpa [a, smul_eq_mul] using hprod_U

/--
%%handwave
name:
  Compactly supported derivative pullbacks are integrable under locally
  bi-Lipschitz changes of variables
statement:
  Let \(T:U\to\Omega\) be a locally bi-Lipschitz change of variables between
  open finite-dimensional Euclidean regions.  If
  \(du\in L^2(\Omega;\operatorname{Hom}(H,\mathbb R))\), then for every
  compactly supported smooth test \(\varphi\) on \(U\) and every direction
  \(v\), the function
  \[
    x\mapsto \varphi(x)\,du(Tx)(dT_x v)
  \]
  is integrable on \(U\).
proof:
  On the compact support of \(\varphi\), the locally Lipschitz map \(T\) has
  an essentially bounded differential and bounded measure distortion.  Thus
  the pulled-back derivative field, evaluated on \(dT_xv\), is \(L^2\) on the
  support.  Multiplication by the bounded compactly supported test function
  preserves \(L^2\), and finite measure converts \(L^2\) to \(L^1\).
-/
theorem locallyBiLipschitz_derivative_pullback_test_integrable
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {U Ω : Set H} {T S : H → H}
    (_hU_open : IsOpen U) (_hΩ_open : IsOpen Ω)
    (_hT_maps : Set.MapsTo T U Ω) (_hS_maps : Set.MapsTo S Ω U)
    (_hS_left : ∀ x ∈ U, S (T x) = x)
    (_hT_left : ∀ y ∈ Ω, T (S y) = y)
    (_hT_lip : LocallyLipschitzOn U T)
    (_hS_lip : LocallyLipschitzOn Ω S)
    (_hT_qmp : Measure.QuasiMeasurePreserving T
      (MeasureTheory.volume.restrict U)
      (MeasureTheory.volume.restrict Ω))
    (_hS_qmp : Measure.QuasiMeasurePreserving S
      (MeasureTheory.volume.restrict Ω)
      (MeasureTheory.volume.restrict U))
    {du : H → H →L[ℝ] ℝ}
    (_hdu : MemLp du 2 (MeasureTheory.volume.restrict Ω))
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction U) (v : H) :
    Integrable
      (fun z : H ↦
        φ z • ((du (T z)).comp (fderiv ℝ (fun x : H ↦ T x) z)) v)
      (MeasureTheory.volume.restrict U) := by
  let g : H → ℝ := fun z ↦
    ((du (T z)).comp (fderiv ℝ (fun x : H ↦ T x) z)) v
  let K : Set H := tsupport (φ : H → ℝ)
  have hK_compact : IsCompact K := φ.compact_support
  have hK_U : K ⊆ U := φ.support_subset
  have hg_K : MemLp g 2 (MeasureTheory.volume.restrict K) :=
    locallyBiLipschitz_derivative_eval_pullback_memLp_on_compact
      _hU_open _hΩ_open _hT_maps _hS_maps _hS_left _hT_left
      _hT_lip _hS_lip _hT_qmp _hS_qmp hK_compact hK_U _hdu v
  have hprod_K : MemLp (fun z : H ↦ φ z * g z) 2
      (MeasureTheory.volume.restrict K) :=
    memLp_restrict_mul_left_of_isCompact_of_continuousOn
      hK_compact φ.smooth.continuous.continuousOn hg_K
  haveI : IsFiniteMeasure (MeasureTheory.volume.restrict K) :=
    isFiniteMeasure_restrict.2 hK_compact.measure_ne_top
  have hprod_int_K : Integrable (fun z : H ↦ φ z * g z)
      (MeasureTheory.volume.restrict K) :=
    hprod_K.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hprod_support :
      Function.support (fun z : H ↦ φ z * g z) ⊆ K := by
    intro z hz
    exact subset_tsupport (φ : H → ℝ)
      (Function.support_mul_subset_left (f := (φ : H → ℝ)) (g := g) hz)
  have hprod_global : Integrable (fun z : H ↦ φ z * g z)
      (MeasureTheory.volume : Measure H) :=
    (integrableOn_iff_integrable_of_support_subset hprod_support).mp
      hprod_int_K
  have hprod_U : Integrable (fun z : H ↦ φ z * g z)
      (MeasureTheory.volume.restrict U) :=
    hprod_global.mono_measure
      (Measure.restrict_le_self (μ := MeasureTheory.volume) (s := U))
  simpa [g, smul_eq_mul] using hprod_U

/--
%%handwave
name:
  Smooth outer functions preserve local Lipschitz regularity
statement:
  If \(T\) is locally Lipschitz on a region \(U\) and \(w\) is smooth on the
  ambient Euclidean space, then \(w\circ T\) is locally Lipschitz on \(U\).
proof:
  Smooth functions are locally Lipschitz.  Restrict \(T\) to \(U\), compose
  the two locally Lipschitz maps, and then regard the resulting statement as
  one on the original region.
-/
theorem locallyLipschitzOn_smooth_outer_comp
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {U : Set H} {T : H → H}
    {w : H → ℝ}
    (hT_lip : LocallyLipschitzOn U T)
    (hw_smooth : ContDiff ℝ ∞ w) :
    LocallyLipschitzOn U (fun z : H ↦ w (T z)) := by
  have hw_one : ContDiff ℝ 1 w :=
    hw_smooth.of_le (by simp : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  have hw_lip : LocallyLipschitz w :=
    hw_one.locallyLipschitz
  rw [locallyLipschitzOn_iff_restrict] at hT_lip ⊢
  have hcomp : LocallyLipschitz (w ∘ U.restrict T) :=
    hw_lip.comp hT_lip
  simpa [Function.comp_def, Set.restrict] using hcomp

/--
%%handwave
name:
  Locally Lipschitz functions give integrable value test pairings
statement:
  Let \(g\) be locally Lipschitz on an open finite-dimensional Euclidean
  region \(U\).  If \(\varphi\) is a compactly supported smooth test on
  \(U\), then \(D\varphi[v]\,g\) is integrable on \(U\).
proof:
  The closed support of \(D\varphi[v]\) is compact and is contained in the
  closed support of \(\varphi\), hence in \(U\).  On this compact set, local
  Lipschitz continuity makes \(g\) continuous and bounded.  The multiplier
  \(D\varphi[v]\) is continuous and compactly supported, so the product is
  integrable on this finite-measure compact support and therefore on \(U\).
-/
theorem locallyLipschitzOn_value_test_integrable
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {U : Set H} {g : H → ℝ}
    (_hU_open : IsOpen U)
    (_hg_lip : LocallyLipschitzOn U g)
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction U) (v : H) :
    Integrable
      (fun z : H ↦ (fderiv ℝ (φ : H → ℝ) z v) • g z)
      (MeasureTheory.volume.restrict U) := by
  let a : H → ℝ := fun z : H ↦ fderiv ℝ (φ : H → ℝ) z v
  let K : Set H := tsupport a
  have ha_cont : Continuous a :=
    ((φ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const)
  have ha_tsupport_subset :
      K ⊆ tsupport (φ : H → ℝ) := by
    simpa [K, a] using
      (tsupport_fderiv_apply_subset (𝕜 := ℝ)
        (f := (φ : H → ℝ)) v)
  have hK_compact : IsCompact K :=
    φ.compact_support.of_isClosed_subset
      (isClosed_tsupport _) ha_tsupport_subset
  have hK_U : K ⊆ U := ha_tsupport_subset.trans φ.support_subset
  have hg_K : MemLp g 2 (MeasureTheory.volume.restrict K) :=
    memLp_restrict_of_isCompact_of_continuousOn
      hK_compact ((_hg_lip.mono hK_U).continuousOn)
  have hprod_K : MemLp (fun z : H ↦ a z * g z) 2
      (MeasureTheory.volume.restrict K) :=
    memLp_restrict_mul_left_of_isCompact_of_continuousOn
      hK_compact ha_cont.continuousOn hg_K
  haveI : IsFiniteMeasure (MeasureTheory.volume.restrict K) :=
    isFiniteMeasure_restrict.2 hK_compact.measure_ne_top
  have hprod_int_K : Integrable (fun z : H ↦ a z * g z)
      (MeasureTheory.volume.restrict K) :=
    hprod_K.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hprod_support :
      Function.support (fun z : H ↦ a z * g z) ⊆ K := by
    intro z hz
    exact subset_tsupport a
      (Function.support_mul_subset_left
        (f := a) (g := g) hz)
  have hprod_global : Integrable (fun z : H ↦ a z * g z)
      (MeasureTheory.volume : Measure H) :=
    (integrableOn_iff_integrable_of_support_subset hprod_support).mp
      hprod_int_K
  have hprod_U : Integrable (fun z : H ↦ a z * g z)
      (MeasureTheory.volume.restrict U) :=
    hprod_global.mono_measure
      (Measure.restrict_le_self (μ := MeasureTheory.volume) (s := U))
  simpa [a, smul_eq_mul] using hprod_U

/--
%%handwave
name:
  Locally Lipschitz functions give integrable derivative test pairings
statement:
  Let \(g\) be locally Lipschitz on an open finite-dimensional Euclidean
  region \(U\).  If \(\varphi\) is a compactly supported smooth test on
  \(U\), then \(\varphi\,Dg[v]\), with \(Dg\) interpreted as the pointwise
  Fréchet derivative, is integrable on \(U\).
proof:
  On the compact support of \(\varphi\), local Lipschitz continuity gives a
  uniform bound for the directional pointwise derivative \(Dg[v]\).  The
  derivative field is measurable, and multiplying by the bounded smooth test
  preserves \(L^2\) on the finite-measure compact support.  This gives
  integrability on \(U\).
-/
theorem locallyLipschitzOn_fderiv_test_integrable
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {U : Set H} {g : H → ℝ}
    (_hU_open : IsOpen U)
    (_hg_lip : LocallyLipschitzOn U g)
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction U) (v : H) :
    Integrable
      (fun z : H ↦ φ z • fderiv ℝ (fun x : H ↦ g x) z v)
      (MeasureTheory.volume.restrict U) := by
  let Dv : H → ℝ := fun z : H ↦ fderiv ℝ (fun x : H ↦ g x) z v
  let K : Set H := tsupport (φ : H → ℝ)
  have hK_compact : IsCompact K := φ.compact_support
  have hK_U : K ⊆ U := φ.support_subset
  rcases
    locallyLipschitzOn_fderiv_apply_norm_bound_on_compact
      (E := ℝ) _hU_open _hg_lip hK_compact hK_U v with
    ⟨C, _hC_nonneg, hC_bound⟩
  have hDv_aesm : AEStronglyMeasurable Dv
      (MeasureTheory.volume.restrict K) := by
    dsimp [Dv]
    exact (measurable_fderiv_apply_const ℝ
      (fun x : H ↦ g x) v).aestronglyMeasurable
  haveI : IsFiniteMeasure (MeasureTheory.volume.restrict K) :=
    isFiniteMeasure_restrict.2 hK_compact.measure_ne_top
  have hDv_mem : MemLp Dv 2 (MeasureTheory.volume.restrict K) :=
    MemLp.of_bound (μ := MeasureTheory.volume.restrict K)
      (p := (2 : ℝ≥0∞)) hDv_aesm C
      (ae_restrict_of_forall_mem hK_compact.measurableSet fun z hz ↦ by
        simpa [Dv] using hC_bound z hz)
  have hprod_K : MemLp (fun z : H ↦ φ z * Dv z) 2
      (MeasureTheory.volume.restrict K) :=
    memLp_restrict_mul_left_of_isCompact_of_continuousOn
      hK_compact φ.smooth.continuous.continuousOn hDv_mem
  have hprod_int_K : Integrable (fun z : H ↦ φ z * Dv z)
      (MeasureTheory.volume.restrict K) :=
    hprod_K.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hprod_support :
      Function.support (fun z : H ↦ φ z * Dv z) ⊆ K := by
    intro z hz
    exact subset_tsupport (φ : H → ℝ)
      (Function.support_mul_subset_left
        (f := (φ : H → ℝ)) (g := Dv) hz)
  have hprod_global : Integrable (fun z : H ↦ φ z * Dv z)
      (MeasureTheory.volume : Measure H) :=
    (integrableOn_iff_integrable_of_support_subset hprod_support).mp
      hprod_int_K
  have hprod_U : Integrable (fun z : H ↦ φ z * Dv z)
      (MeasureTheory.volume.restrict U) :=
    hprod_global.mono_measure
      (Measure.restrict_le_self (μ := MeasureTheory.volume) (s := U))
  simpa [Dv, smul_eq_mul] using hprod_U

/--
%%handwave
name:
  Lipschitz functions satisfy the weak test identity near a compact support
statement:
  Let \(g\) be Lipschitz on a set \(V\) which is a neighborhood of the closed
  support of a compactly supported smooth test \(\varphi\).  Then, for every
  direction \(v\),
  \[
    \int_U D\varphi[v]\,g
      =
    -\int_U \varphi\,Dg[v],
  \]
  where \(Dg\) is the pointwise Fréchet derivative.
proof:
  Lipschitz functions are absolutely continuous on almost every line
  parallel to \(v\), and their line derivative agrees almost everywhere with
  the pointwise Fréchet derivative applied to \(v\).  Since both integrands
  are supported where \(\varphi\) or \(D\varphi[v]\) is supported, the
  neighborhood hypothesis keeps all relevant line segments inside \(V\).
  Fubini reduces the identity to one-dimensional integration by parts on the
  good lines.
-/
theorem lipschitzOnWith_nhds_support_ACL_weak_test_integral_eq_fderiv_volume
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {U V : Set H} {g : H → ℝ} {L : ℝ≥0}
    (_hg_lip : LipschitzOnWith L g V)
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction U) (v : H)
    (_hV_nhds_support :
      ∀ z ∈ tsupport (φ : H → ℝ), V ∈ 𝓝 z) :
    ∫ z, (fderiv ℝ (φ : H → ℝ) z v) • g z
        ∂MeasureTheory.volume =
      -∫ z, φ z • fderiv ℝ (fun x : H ↦ g x) z v
        ∂MeasureTheory.volume := by
  classical
  rcases _hg_lip.extend_real with ⟨G, hG_lip, hG_eq⟩
  obtain ⟨D, hφ_lip⟩ : ∃ D, LipschitzWith D (φ : H → ℝ) :=
    ContDiff.lipschitzWith_of_hasCompactSupport
      φ.compact_support φ.smooth (by simp)
  have hG_eventually :
      ∀ z ∈ tsupport (φ : H → ℝ), G =ᶠ[𝓝 z] g := by
    intro z hz
    filter_upwards [_hV_nhds_support z hz] with y hy
    exact (hG_eq hy).symm
  have hleft_point :
      ∀ z : H,
        fderiv ℝ (φ : H → ℝ) z v * g z =
          fderiv ℝ (φ : H → ℝ) z v * G z := by
    intro z
    by_cases hz :
        z ∈ tsupport (fun y : H ↦ fderiv ℝ (φ : H → ℝ) y v)
    · have hzφ : z ∈ tsupport (φ : H → ℝ) :=
        (tsupport_fderiv_apply_subset (𝕜 := ℝ)
          (f := (φ : H → ℝ)) v) hz
      have hzg : G z = g z := (hG_eventually z hzφ).eq_of_nhds
      rw [← hzg]
    · have hzero :
        fderiv ℝ (φ : H → ℝ) z v = 0 :=
        image_eq_zero_of_notMem_tsupport
          (f := fun y : H ↦ fderiv ℝ (φ : H → ℝ) y v) hz
      simp [hzero]
  have hright_point :
      ∀ z : H,
        fderiv ℝ G z v * (φ : H → ℝ) z =
          fderiv ℝ (fun x : H ↦ g x) z v * (φ : H → ℝ) z := by
    intro z
    by_cases hz : z ∈ tsupport (φ : H → ℝ)
    · have hderiv :
          fderiv ℝ G z = fderiv ℝ (fun x : H ↦ g x) z :=
        Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) (hG_eventually z hz)
      rw [hderiv]
    · have hzero : (φ : H → ℝ) z = 0 :=
        image_eq_zero_of_notMem_tsupport hz
      simp [hzero]
  have hline :
      ∫ z, lineDeriv ℝ G z v * (φ : H → ℝ) z
          ∂MeasureTheory.volume =
        ∫ z, lineDeriv ℝ (φ : H → ℝ) z (-v) * G z
          ∂MeasureTheory.volume :=
    LipschitzWith.integral_lineDeriv_mul_eq
      (μ := (MeasureTheory.volume : Measure H))
      hG_lip hφ_lip φ.compact_support v
  have hlineG_fderiv_ae :
      (fun z : H ↦ lineDeriv ℝ G z v * (φ : H → ℝ) z)
        =ᵐ[MeasureTheory.volume]
      (fun z : H ↦ fderiv ℝ G z v * (φ : H → ℝ) z) := by
    filter_upwards
      [hG_lip.ae_differentiableAt
        (μ := (MeasureTheory.volume : Measure H))] with z hz
    rw [hz.lineDeriv_eq_fderiv]
  have hlineφ (z : H) :
      lineDeriv ℝ (φ : H → ℝ) z (-v) =
        -fderiv ℝ (φ : H → ℝ) z v := by
    rw [(φ.smooth.differentiable (by simp) z).lineDeriv_eq_fderiv]
    simp
  have hG_identity :
      ∫ z, fderiv ℝ (φ : H → ℝ) z v * G z
          ∂MeasureTheory.volume =
        -∫ z, fderiv ℝ G z v * (φ : H → ℝ) z
          ∂MeasureTheory.volume := by
    have hline' :
        ∫ z, fderiv ℝ G z v * (φ : H → ℝ) z
            ∂MeasureTheory.volume =
          -∫ z, fderiv ℝ (φ : H → ℝ) z v * G z
            ∂MeasureTheory.volume := by
      calc
        ∫ z, fderiv ℝ G z v * (φ : H → ℝ) z
            ∂MeasureTheory.volume
            =
          ∫ z, lineDeriv ℝ G z v * (φ : H → ℝ) z
            ∂MeasureTheory.volume :=
              (integral_congr_ae hlineG_fderiv_ae).symm
        _ =
          ∫ z, lineDeriv ℝ (φ : H → ℝ) z (-v) * G z
            ∂MeasureTheory.volume := hline
        _ =
          ∫ z, (-fderiv ℝ (φ : H → ℝ) z v) * G z
            ∂MeasureTheory.volume := by
              simp [hlineφ]
        _ =
          -∫ z, fderiv ℝ (φ : H → ℝ) z v * G z
            ∂MeasureTheory.volume := by
              rw [← integral_neg]
              simp [neg_mul]
    calc
      ∫ z, fderiv ℝ (φ : H → ℝ) z v * G z
          ∂MeasureTheory.volume
          =
        -(-∫ z, fderiv ℝ (φ : H → ℝ) z v * G z
          ∂MeasureTheory.volume) := by simp
      _ =
        -∫ z, fderiv ℝ G z v * (φ : H → ℝ) z
          ∂MeasureTheory.volume := by
            rw [← hline']
  calc
    ∫ z, (fderiv ℝ (φ : H → ℝ) z v) • g z
        ∂MeasureTheory.volume
        =
      ∫ z, fderiv ℝ (φ : H → ℝ) z v * g z
        ∂MeasureTheory.volume := by simp [smul_eq_mul]
    _ =
      ∫ z, fderiv ℝ (φ : H → ℝ) z v * G z
        ∂MeasureTheory.volume :=
        integral_congr_ae (Filter.Eventually.of_forall hleft_point)
    _ =
      -∫ z, fderiv ℝ G z v * (φ : H → ℝ) z
        ∂MeasureTheory.volume := hG_identity
    _ =
      -∫ z, fderiv ℝ (fun x : H ↦ g x) z v * (φ : H → ℝ) z
        ∂MeasureTheory.volume := by
          congr 1
          exact integral_congr_ae (Filter.Eventually.of_forall hright_point)
    _ =
      -∫ z, φ z • fderiv ℝ (fun x : H ↦ g x) z v
        ∂MeasureTheory.volume := by
          simp [smul_eq_mul, mul_comm]

theorem lipschitzOnWith_nhds_support_ACL_weak_test_integral_eq_fderiv
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {U V : Set H} {g : H → ℝ} {L : ℝ≥0}
    (_hU_open : IsOpen U)
    (_hg_lip : LipschitzOnWith L g V)
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction U) (v : H)
    (_hV_nhds_support :
      ∀ z ∈ tsupport (φ : H → ℝ), V ∈ 𝓝 z)
    (_hleft :
      Integrable
        (fun z : H ↦ (fderiv ℝ (φ : H → ℝ) z v) • g z)
        (MeasureTheory.volume.restrict U))
    (_hright :
      Integrable
        (fun z : H ↦ φ z • fderiv ℝ (fun x : H ↦ g x) z v)
        (MeasureTheory.volume.restrict U)) :
    ∫ z in U, (fderiv ℝ (φ : H → ℝ) z v) • g z
        ∂MeasureTheory.volume =
      -∫ z in U, φ z • fderiv ℝ (fun x : H ↦ g x) z v
        ∂MeasureTheory.volume := by
  let left : H → ℝ :=
    fun z : H ↦ (fderiv ℝ (φ : H → ℝ) z v) • g z
  let right : H → ℝ :=
    fun z : H ↦ φ z • fderiv ℝ (fun x : H ↦ g x) z v
  have hleft_zero : ∀ z : H, z ∉ U → left z = 0 := by
    intro z hzU
    have hz_not : z ∉ tsupport (fun y : H ↦ fderiv ℝ (φ : H → ℝ) y v) := by
      intro hz
      exact hzU <| φ.support_subset <|
        (tsupport_fderiv_apply_subset (𝕜 := ℝ)
          (f := (φ : H → ℝ)) v) hz
    have hzero :
        fderiv ℝ (φ : H → ℝ) z v = 0 :=
      image_eq_zero_of_notMem_tsupport
        (f := fun y : H ↦ fderiv ℝ (φ : H → ℝ) y v) hz_not
    simp [left, hzero]
  have hright_zero : ∀ z : H, z ∉ U → right z = 0 := by
    intro z hzU
    have hz_not : z ∉ tsupport (φ : H → ℝ) := by
      intro hz
      exact hzU (φ.support_subset hz)
    have hzero : (φ : H → ℝ) z = 0 :=
      image_eq_zero_of_notMem_tsupport hz_not
    simp [right, hzero]
  have hleft_U_eq :
      ∫ z in U, left z ∂MeasureTheory.volume =
        ∫ z, left z ∂MeasureTheory.volume := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hleft_zero]
  have hright_U_eq :
      ∫ z in U, right z ∂MeasureTheory.volume =
        ∫ z, right z ∂MeasureTheory.volume := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hright_zero]
  have hvolume :
      ∫ z, left z ∂MeasureTheory.volume =
        -∫ z, right z ∂MeasureTheory.volume := by
    simpa [left, right] using
      lipschitzOnWith_nhds_support_ACL_weak_test_integral_eq_fderiv_volume
        _hg_lip φ v _hV_nhds_support
  calc
    ∫ z in U, (fderiv ℝ (φ : H → ℝ) z v) • g z
        ∂MeasureTheory.volume
        = ∫ z in U, left z ∂MeasureTheory.volume := rfl
    _ = ∫ z, left z ∂MeasureTheory.volume := hleft_U_eq
    _ = -∫ z, right z ∂MeasureTheory.volume := hvolume
    _ = -∫ z in U, right z ∂MeasureTheory.volume := by
      rw [hright_U_eq]
    _ = -∫ z in U, φ z • fderiv ℝ (fun x : H ↦ g x) z v
        ∂MeasureTheory.volume := rfl

/--
%%handwave
name:
  Locally Lipschitz functions satisfy the ACL weak test identity
statement:
  Let \(g\) be locally Lipschitz on an open finite-dimensional Euclidean
  region \(U\).  For every compactly supported smooth test \(\varphi\) and
  every direction \(v\),
  \[
    \int_U D\varphi[v]\,g
      =
    -\int_U \varphi\,Dg[v],
  \]
  where \(Dg\) is the pointwise Fréchet derivative.
proof:
  Enlarge the compact support of \(\varphi\) to a compact closed thickening
  contained in \(U\).  Local Lipschitz continuity gives a single Lipschitz
  constant on that thickening.  Apply the Lipschitz ACL/Fubini weak test
  identity on this neighborhood of the test support.
-/
theorem locallyLipschitzOn_ACL_weak_test_integral_eq_fderiv
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {U : Set H} {g : H → ℝ}
    (_hU_open : IsOpen U)
    (_hg_lip : LocallyLipschitzOn U g)
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction U) (v : H)
    (_hleft :
      Integrable
        (fun z : H ↦ (fderiv ℝ (φ : H → ℝ) z v) • g z)
        (MeasureTheory.volume.restrict U))
    (_hright :
      Integrable
        (fun z : H ↦ φ z • fderiv ℝ (fun x : H ↦ g x) z v)
        (MeasureTheory.volume.restrict U)) :
    ∫ z in U, (fderiv ℝ (φ : H → ℝ) z v) • g z
        ∂MeasureTheory.volume =
      -∫ z in U, φ z • fderiv ℝ (fun x : H ↦ g x) z v
        ∂MeasureTheory.volume := by
  classical
  haveI : ProperSpace H := FiniteDimensional.proper ℝ H
  let K : Set H := tsupport (φ : H → ℝ)
  have hK_compact : IsCompact K := φ.compact_support
  have hK_U : K ⊆ U := φ.support_subset
  rcases hK_compact.exists_cthickening_subset_open _hU_open hK_U with
    ⟨δ, hδ_pos, hδU⟩
  let V : Set H := Metric.cthickening δ K
  have hV_compact : IsCompact V := by
    dsimp [V]
    exact hK_compact.cthickening
  have hg_lip_V : LocallyLipschitzOn V g :=
    _hg_lip.mono (by simpa [V] using hδU)
  rcases hg_lip_V.exists_lipschitzOnWith_of_compact hV_compact with
    ⟨L, hL⟩
  have hV_nhds_support :
      ∀ z ∈ tsupport (φ : H → ℝ), V ∈ 𝓝 z := by
    intro z hz
    have hz_thick : z ∈ Metric.thickening δ K :=
      Metric.self_subset_thickening hδ_pos K (by simpa [K] using hz)
    have hthick_nhds : Metric.thickening δ K ∈ 𝓝 z :=
      Metric.isOpen_thickening.mem_nhds hz_thick
    exact Filter.mem_of_superset hthick_nhds
      (by
        intro y hy
        exact Metric.thickening_subset_cthickening δ K hy)
  exact
    lipschitzOnWith_nhds_support_ACL_weak_test_integral_eq_fderiv
      _hU_open hL φ v hV_nhds_support _hleft _hright

/--
%%handwave
name:
  The pointwise derivative of a locally Lipschitz function is its weak
  derivative
statement:
  If \(g\) is locally Lipschitz on an open finite-dimensional Euclidean
  region, then its pointwise Fréchet derivative represents its distributional
  weak derivative there.
proof:
  The two test pairings are integrable by compact support and local
  Lipschitz bounds.  The equality is the standard ACL integration-by-parts
  theorem for locally Lipschitz functions.
-/
theorem locallyLipschitzOn_isWeakDerivative_fderiv
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {U : Set H} {g : H → ℝ}
    (hU_open : IsOpen U)
    (hg_lip : LocallyLipschitzOn U g) :
    IsWeakDerivativeOnEuclideanRegionWithValues U g
      (fun z : H ↦ fderiv ℝ (fun x : H ↦ g x) z) := by
  intro φ v
  have hleft :
      Integrable
        (fun z : H ↦ (fderiv ℝ (φ : H → ℝ) z v) • g z)
        (MeasureTheory.volume.restrict U) :=
    locallyLipschitzOn_value_test_integrable hU_open hg_lip φ v
  have hright :
      Integrable
        (fun z : H ↦ φ z • fderiv ℝ (fun x : H ↦ g x) z v)
        (MeasureTheory.volume.restrict U) :=
    locallyLipschitzOn_fderiv_test_integrable hU_open hg_lip φ v
  refine ⟨hleft, hright, ?_⟩
  exact
    locallyLipschitzOn_ACL_weak_test_integral_eq_fderiv
      hU_open hg_lip φ v hleft hright

/--
%%handwave
name:
  Locally Lipschitz functions satisfy the compactly supported weak test
  identity
statement:
  Let \(g\) be locally Lipschitz on an open finite-dimensional Euclidean
  region \(U\).  For every compactly supported smooth test \(\varphi\) on
  \(U\) and every direction \(v\),
  \[
    \int_U D\varphi(x)[v]\,g(x)\,dx
      =
    -\int_U \varphi(x)\,Dg(x)[v]\,dx .
  \]
proof:
  Cover the compact support of \(\varphi\) by finitely many Lipschitz
  neighborhoods for \(g\).  Rademacher's theorem identifies the pointwise
  differential almost everywhere, and the standard one-dimensional
  fundamental theorem along lines gives the distributional integration by
  parts formula against compactly supported smooth tests.
-/
theorem locallyLipschitzOn_weak_test_integral_eq_fderiv
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {U : Set H} {g : H → ℝ}
    (_hU_open : IsOpen U)
    (_hg_lip : LocallyLipschitzOn U g)
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction U) (v : H) :
    ∫ z in U, (fderiv ℝ (φ : H → ℝ) z v) • g z
        ∂MeasureTheory.volume =
      -∫ z in U, φ z • fderiv ℝ (fun x : H ↦ g x) z v
        ∂MeasureTheory.volume := by
  exact
    (locallyLipschitzOn_isWeakDerivative_fderiv _hU_open _hg_lip φ v).2.2

/--
%%handwave
name:
  Smooth outer functions give locally Lipschitz weak test identities
statement:
  Let \(T\) be locally Lipschitz on an open finite-dimensional Euclidean
  region \(U\), and let \(w\) be smooth.  For every compactly supported
  smooth test \(\varphi\) on \(U\) and every direction \(v\),
  \[
    \int_U D\varphi(x)[v]\,w(Tx)\,dx
      =
    -\int_U \varphi(x)\,D(w\circ T)(x)[v]\,dx .
  \]
proof:
  On a compact neighborhood of the support of \(\varphi\), the smooth
  function \(w\) is Lipschitz on the image of the locally Lipschitz map
  \(T\).  Hence \(w\circ T\) is locally Lipschitz there.  Rademacher's
  theorem supplies an almost-everywhere differential, and the standard weak
  integration-by-parts formula for locally Lipschitz functions gives the
  stated test identity.
-/
theorem locallyLipschitz_smooth_outer_weak_test_integral_eq
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {U : Set H} {T : H → H}
    (_hU_open : IsOpen U)
    (_hT_lip : LocallyLipschitzOn U T)
    {w : H → ℝ} (_hw_smooth : ContDiff ℝ ∞ w)
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction U) (v : H) :
    ∫ z in U, (fderiv ℝ (φ : H → ℝ) z v) • w (T z)
        ∂MeasureTheory.volume =
      -∫ z in U, φ z • fderiv ℝ (fun x : H ↦ w (T x)) z v
        ∂MeasureTheory.volume := by
  exact
    locallyLipschitzOn_weak_test_integral_eq_fderiv
      _hU_open
      (locallyLipschitzOn_smooth_outer_comp _hT_lip _hw_smooth)
      φ v

/--
%%handwave
name:
  Locally Lipschitz maps on open Euclidean regions are differentiable almost
  everywhere
statement:
  If \(T\) is locally Lipschitz on an open finite-dimensional Euclidean
  region \(U\), then \(T\) is differentiable at almost every point of \(U\).
proof:
  Cover \(U\) by countably many compactly contained balls.  On each ball,
  local Lipschitz continuity gives a finite Lipschitz constant after passing
  to a slightly smaller compact neighborhood.  Rademacher's theorem applies
  on every ball, and countable subadditivity removes the exceptional sets.
-/
theorem locallyLipschitzOn_ae_differentiableAt_of_isOpen
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {U : Set H} {T : H → H}
    (_hU_open : IsOpen U)
    (_hT_lip : LocallyLipschitzOn U T) :
    ∀ᵐ z ∂MeasureTheory.volume.restrict U, DifferentiableAt ℝ T z := by
  classical
  haveI : ProperSpace H := FiniteDimensional.proper ℝ H
  haveI : SecondCountableTopology H := by infer_instance
  have hlocal :
      ∀ x : U, ∃ K : ℝ≥0, ∃ V : Set H,
        V ∈ 𝓝 (x : H) ∧ IsOpen V ∧ LipschitzOnWith K T V := by
    intro x
    rcases _hT_lip x.2 with ⟨K, t, ht_nhdsWithin, ht_lip⟩
    have ht_nhds : t ∈ 𝓝 (x : H) := by
      simpa [(_hU_open.nhdsWithin_eq x.2)] using ht_nhdsWithin
    rcases mem_nhds_iff.mp ht_nhds with ⟨V, hV_sub, hV_open, hxV⟩
    exact ⟨K, V, hV_open.mem_nhds hxV, hV_open, ht_lip.mono hV_sub⟩
  choose K V hV_nhds hV_open hV_lip using hlocal
  let W : H → Set H := fun x ↦ if hx : x ∈ U then V ⟨x, hx⟩ else ∅
  have hW_nhdsWithin : ∀ x ∈ U, W x ∈ 𝓝[U] x := by
    intro x hx
    have hVx : V ⟨x, hx⟩ ∈ 𝓝 x := hV_nhds ⟨x, hx⟩
    have hWx : W x ∈ 𝓝 x := by
      simpa [W, hx] using hVx
    exact mem_nhdsWithin_of_mem_nhds hWx
  rcases TopologicalSpace.countable_cover_nhdsWithin hW_nhdsWithin with
    ⟨C, hCU, hC_count, hU_cover⟩
  have h_each :
      ∀ x ∈ C,
        ∀ᵐ z ∂MeasureTheory.volume.restrict (W x),
          DifferentiableAt ℝ T z := by
    intro x hxC
    have hxU : x ∈ U := hCU hxC
    have hW_open : IsOpen (W x) := by
      simpa [W, hxU] using hV_open ⟨x, hxU⟩
    have hW_lip : LipschitzOnWith (K ⟨x, hxU⟩) T (W x) := by
      simpa [W, hxU] using hV_lip ⟨x, hxU⟩
    have hdwithin :
        ∀ᵐ z ∂MeasureTheory.volume.restrict (W x),
          DifferentiableWithinAt ℝ T (W x) z :=
      hW_lip.ae_differentiableWithinAt hW_open.measurableSet
    have hmem :
        ∀ᵐ z ∂MeasureTheory.volume.restrict (W x), z ∈ W x :=
      ae_restrict_of_forall_mem hW_open.measurableSet fun z hz ↦ hz
    filter_upwards [hdwithin, hmem] with z hzdiff hzW
    rcases hzdiff with ⟨f', hf'⟩
    exact ⟨f', (hasFDerivWithinAt_of_isOpen hW_open hzW).mp hf'⟩
  have h_union :
      ∀ᵐ z ∂MeasureTheory.volume.restrict (⋃ x ∈ C, W x),
        DifferentiableAt ℝ T z := by
    rw [ae_restrict_biUnion_iff W hC_count]
    exact h_each
  have hmono :
      MeasureTheory.volume.restrict U ≤
        MeasureTheory.volume.restrict (⋃ x ∈ C, W x) :=
    Measure.restrict_mono hU_cover le_rfl
  exact ae_mono hmono h_union

/--
%%handwave
name:
  Smooth outer functions satisfy the almost-everywhere chain rule
statement:
  Let \(T\) be locally Lipschitz on an open finite-dimensional Euclidean
  region \(U\), and let \(w\) be smooth.  For every direction \(v\),
  \[
    D(w\circ T)(x)[v] = Dw(Tx)[dT_xv]
  \]
  for almost every \(x\in U\).
proof:
  Rademacher's theorem gives differentiability of \(T\) almost everywhere in
  \(U\).  At each such point, compose the differential of \(T\) with the
  classical differential of the smooth outer function \(w\).
-/
theorem locallyLipschitz_smooth_outer_chain_rule_ae
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {U : Set H} {T : H → H}
    (_hU_open : IsOpen U)
    (_hT_lip : LocallyLipschitzOn U T)
    {w : H → ℝ} (_hw_smooth : ContDiff ℝ ∞ w)
    (v : H) :
    (fun z : H ↦ fderiv ℝ (fun x : H ↦ w (T x)) z v)
      =ᵐ[MeasureTheory.volume.restrict U]
        fun z : H ↦
          ((fderiv ℝ (fun x : H ↦ w x) (T z)).comp
            (fderiv ℝ (fun x : H ↦ T x) z)) v := by
  filter_upwards
    [locallyLipschitzOn_ae_differentiableAt_of_isOpen
      _hU_open _hT_lip] with z hz
  have hw_diff : DifferentiableAt ℝ (fun x : H ↦ w x) (T z) :=
    (_hw_smooth.differentiable (by simp)) (T z)
  have hcomp :
      fderiv ℝ (fun x : H ↦ w (T x)) z =
        (fderiv ℝ (fun x : H ↦ w x) (T z)).comp
          (fderiv ℝ (fun x : H ↦ T x) z) := by
    simpa [Function.comp_def] using
      (fderiv_comp z hw_diff hz)
  exact congrArg (fun A : H →L[ℝ] ℝ ↦ A v) hcomp

/--
%%handwave
name:
  Smooth outer functions satisfy the pullback test identity
statement:
  Let \(T\) be locally Lipschitz on an open finite-dimensional Euclidean
  region \(U\).  If \(w\) is smooth, then for every compactly supported
  smooth test \(\varphi\) on \(U\) and every direction \(v\),
  \[
    \int_U D\varphi(x)[v]\,w(Tx)\,dx
      =
    -\int_U \varphi(x)\,Dw(Tx)[dT_xv]\,dx .
  \]
proof:
  The composition \(w\circ T\) is locally Lipschitz on the compact support of
  \(\varphi\).  Rademacher's theorem gives the a.e. chain rule
  \(D(w\circ T)=Dw(Tx)\circ dT_x\).  The usual compactly supported
  integration-by-parts formula for locally Lipschitz functions then gives the
  identity.
-/
theorem locallyLipschitz_smooth_outer_pullback_test_integral_eq
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {U : Set H} {T : H → H}
    (_hU_open : IsOpen U)
    (_hT_lip : LocallyLipschitzOn U T)
    {w : H → ℝ} (_hw_smooth : ContDiff ℝ ∞ w)
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction U) (v : H) :
    ∫ z in U, (fderiv ℝ (φ : H → ℝ) z v) • w (T z)
        ∂MeasureTheory.volume =
      -∫ z in U,
        φ z •
          ((fderiv ℝ (fun x : H ↦ w x) (T z)).comp
            (fderiv ℝ (fun x : H ↦ T x) z)) v
        ∂MeasureTheory.volume := by
  have hweak :
      ∫ z in U, (fderiv ℝ (φ : H → ℝ) z v) • w (T z)
          ∂MeasureTheory.volume =
        -∫ z in U, φ z • fderiv ℝ (fun x : H ↦ w (T x)) z v
          ∂MeasureTheory.volume :=
    locallyLipschitz_smooth_outer_weak_test_integral_eq
      _hU_open _hT_lip _hw_smooth φ v
  have hchain :
      (fun z : H ↦ fderiv ℝ (fun x : H ↦ w (T x)) z v)
        =ᵐ[MeasureTheory.volume.restrict U]
          fun z : H ↦
            ((fderiv ℝ (fun x : H ↦ w x) (T z)).comp
              (fderiv ℝ (fun x : H ↦ T x) z)) v :=
    locallyLipschitz_smooth_outer_chain_rule_ae
      _hU_open _hT_lip _hw_smooth v
  have hright :
      ∫ z in U, φ z • fderiv ℝ (fun x : H ↦ w (T x)) z v
          ∂MeasureTheory.volume =
        ∫ z in U,
          φ z •
            ((fderiv ℝ (fun x : H ↦ w x) (T z)).comp
              (fderiv ℝ (fun x : H ↦ T x) z)) v
          ∂MeasureTheory.volume := by
    refine integral_congr_ae ?_
    exact hchain.mono fun z hz ↦ by
      simp [hz]
  calc
    ∫ z in U, (fderiv ℝ (φ : H → ℝ) z v) • w (T z)
        ∂MeasureTheory.volume
        =
          -∫ z in U, φ z • fderiv ℝ (fun x : H ↦ w (T x)) z v
            ∂MeasureTheory.volume := hweak
    _ =
      -∫ z in U,
        φ z •
          ((fderiv ℝ (fun x : H ↦ w x) (T z)).comp
            (fderiv ℝ (fun x : H ↦ T x) z)) v
        ∂MeasureTheory.volume := by
      rw [hright]

/--
%%handwave
name:
  Smooth graph-norm approximation data
statement:
  Smooth graph-norm approximation data consists of smooth functions \(w_n\)
  converging to a scalar weak Sobolev function in \(L^2\), with their full
  derivatives converging in \(L^2\) to the weak derivative field.
-/
structure ScalarWeakSobolevSmoothApproxGraphL2Data
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    (B : Set H) (w : H → ℝ) (dw : H → H →L[ℝ] ℝ) where
  approximants : ℕ → H → ℝ
  smooth : ∀ n : ℕ, ContDiff ℝ ∞ (approximants n)
  value_error_memLp :
    ∀ n : ℕ,
      MemLp (fun z ↦ approximants n z - w z) 2
        (MeasureTheory.volume.restrict B)
  value_tendsto_l2 :
    Filter.Tendsto
      (fun n : ℕ ↦
        eLpNorm (fun z ↦ approximants n z - w z) 2
          (MeasureTheory.volume.restrict B))
      Filter.atTop (𝓝 0)
  derivative_error_memLp :
    ∀ n : ℕ,
      MemLp (fun z ↦ fderiv ℝ (approximants n) z - dw z) 2
        (MeasureTheory.volume.restrict B)
  derivative_tendsto_l2 :
    Filter.Tendsto
      (fun n : ℕ ↦
        eLpNorm (fun z ↦ fderiv ℝ (approximants n) z - dw z) 2
          (MeasureTheory.volume.restrict B))
      Filter.atTop (𝓝 0)

/--
%%handwave
name:
  Local smooth graph-density in the full Euclidean Sobolev graph norm
statement:
  Let \(Q\Subset P\subset\Omega\), where \(Q\) and \(P\) are compact and
  \(\Omega\) is an open finite-dimensional Euclidean region.  If
  \(u\in L^2(P)\), \(du\in L^2(P;\operatorname{Hom}(H,\mathbb R))\), and
  \(du\) is the weak derivative of \(u\) on \(\Omega\), then there are smooth
  functions \(w_n\) such that \(w_n\to u\) and \(Dw_n\to du\) in \(L^2(Q)\).
proof:
  Localize inside \(P\), mollify on a positive collar around \(Q\), and apply
  the scalar directional density theorem in finitely many basis directions.
  The finite-dimensional comparison between the operator norm and the basis
  directional norms converts the directional convergence into convergence of
  the full derivative field.
-/
theorem euclideanSobolev_smooth_graph_density_l2_on_compact
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Q P Ω : Set H}
    (hQ : IsCompact Q) (_hP : IsCompact P)
    (hQP : ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ Q ⊆ P)
    (hPΩ : P ⊆ Ω) (_hΩ_open : IsOpen Ω)
    {u : H → ℝ} {du : H → H →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionWithValues Ω u du)
    (hu : MemLp u 2 (MeasureTheory.volume.restrict P))
    (hdu : MemLp du 2 (MeasureTheory.volume.restrict P)) :
    Nonempty (ScalarWeakSobolevSmoothApproxGraphL2Data Q u du) := by
  classical
  rcases hQP with ⟨δ, hδ_pos, hδP⟩
  let Ω₀ : Set H := Metric.thickening δ Q
  let η : ℝ := δ / 2
  let P₀ : Set H := Metric.cthickening η Q
  let μQ : Measure H := MeasureTheory.volume.restrict Q
  let μP₀ : Measure H := MeasureTheory.volume.restrict P₀
  have hη_pos : 0 < η := by
    dsimp [η]
    linarith
  have hη_ltδ : η < δ := by
    dsimp [η]
    linarith
  have hη_leδ : η ≤ δ := by
    dsimp [η]
    linarith
  have hΩ₀_open : IsOpen Ω₀ := by
    dsimp [Ω₀]
    exact Metric.isOpen_thickening
  have hΩ₀P : Ω₀ ⊆ P := by
    intro z hz
    exact hδP (Metric.thickening_subset_cthickening δ Q hz)
  have hΩ₀Ω : Ω₀ ⊆ Ω := hΩ₀P.trans hPΩ
  have hP₀_compact : IsCompact P₀ := by
    dsimp [P₀]
    exact hQ.cthickening
  have hP₀Ω₀ : P₀ ⊆ Ω₀ := by
    dsimp [P₀, Ω₀, η]
    exact Metric.cthickening_subset_thickening' hδ_pos hη_ltδ Q
  have hP₀P : P₀ ⊆ P := by
    exact (Metric.cthickening_mono hη_leδ Q).trans hδP
  have hQP₀ : ∃ ε : ℝ, 0 < ε ∧ Metric.cthickening ε Q ⊆ P₀ :=
    ⟨η, hη_pos, by intro z hz; exact hz⟩
  have hQP₀_subset : Q ⊆ P₀ := subset_of_exists_cthickening_subset hQP₀
  have hQP_subset : Q ⊆ P := hQP₀_subset.trans hP₀P
  have hQΩ₀ : Q ⊆ Ω₀ := by
    intro z hz
    exact Metric.self_subset_thickening hδ_pos Q hz
  have hweakΩ₀ :
      IsWeakDerivativeOnEuclideanRegionWithValues Ω₀ u du :=
    IsWeakDerivativeOnEuclideanRegionWithValues.mono_set hweak hΩ₀Ω
  have hweakK :
      KinnunenWeakDerivativeOnEuclideanRegionScalar Ω₀ u du := by
    simpa [KinnunenWeakDerivativeOnEuclideanRegionScalar,
      IsWeakDerivativeOnEuclideanRegionScalar,
      IsWeakDerivativeOnEuclideanRegionWithValues] using hweakΩ₀
  have hu_loc :
      LocallyIntegrableOn u Ω₀ (MeasureTheory.volume : Measure H) :=
    memLp_two_locallyIntegrableOn_of_subset hΩ₀_open hΩ₀P hu
  rcases exists_scalarWeakSobolevCutoff hQ hQΩ₀ hΩ₀_open with ⟨χ⟩
  let W : H → ℝ := fun z ↦ χ z * u z
  let DW : H → H →L[ℝ] ℝ :=
    scalarWeakSobolevCutoffDerivative (χ : H → ℝ) u du
  have hweak_cut :
      KinnunenWeakDerivativeOnEuclideanRegionScalar Ω₀ W DW := by
    simpa [W, DW] using
      scalarWeakSobolevCutoffDerivative_weakDerivative χ hweakK hu_loc
  have hW_int : Integrable W (MeasureTheory.volume : Measure H) := by
    simpa [W] using scalarWeakSobolevCutoff_value_integrable χ hu_loc
  have hu_P₀ : MemLp u 2 μP₀ :=
    hu.mono_measure (by
      dsimp [μP₀]
      exact Measure.restrict_mono hP₀P le_rfl)
  have hW_P₀ : MemLp W 2 μP₀ := by
    dsimp [W]
    exact
      memLp_restrict_mul_left_of_isCompact_of_continuousOn
        hP₀_compact χ.smooth.continuous.continuousOn hu_P₀
  have hDW_eval_int :
      ∀ i : Fin (Module.finrank ℝ H),
        Integrable (fun z : H ↦ DW z (Module.finBasis ℝ H i))
          (MeasureTheory.volume : Measure H) := by
    intro i
    let e : H := Module.finBasis ℝ H i
    let L : (H →L[ℝ] ℝ) →L[ℝ] ℝ :=
      ContinuousLinearMap.apply ℝ ℝ e
    have hdu_eval_P : MemLp (fun z : H ↦ du z e) 2
        (MeasureTheory.volume.restrict P) := by
      simpa [L, Function.comp_def] using L.comp_memLp' hdu
    have hdu_eval_loc :
        LocallyIntegrableOn (fun z : H ↦ du z e) Ω₀
          (MeasureTheory.volume : Measure H) :=
      memLp_two_locallyIntegrableOn_of_subset hΩ₀_open hΩ₀P hdu_eval_P
    simpa [DW, e] using
      scalarWeakSobolevCutoff_derivative_integrable χ hu_loc hdu_eval_loc
  have hDW_eval_P₀ :
      ∀ i : Fin (Module.finrank ℝ H),
        MemLp (fun z : H ↦ DW z (Module.finBasis ℝ H i)) 2 μP₀ := by
    intro i
    let e : H := Module.finBasis ℝ H i
    let L : (H →L[ℝ] ℝ) →L[ℝ] ℝ :=
      ContinuousLinearMap.apply ℝ ℝ e
    have hdu_eval_P : MemLp (fun z : H ↦ du z e) 2
        (MeasureTheory.volume.restrict P) := by
      simpa [L, Function.comp_def] using L.comp_memLp' hdu
    have hdu_eval_P₀ : MemLp (fun z : H ↦ du z e) 2 μP₀ :=
      hdu_eval_P.mono_measure (by
        dsimp [μP₀]
        exact Measure.restrict_mono hP₀P le_rfl)
    have hχ_du : MemLp (fun z : H ↦ χ z * du z e) 2 μP₀ :=
      memLp_restrict_mul_left_of_isCompact_of_continuousOn
        hP₀_compact χ.smooth.continuous.continuousOn hdu_eval_P₀
    have hDχ_cont :
        ContinuousOn (fun z : H ↦ fderiv ℝ (χ : H → ℝ) z e) P₀ :=
      ((χ.smooth.continuous_fderiv (by simp)).clm_apply
        continuous_const).continuousOn
    have hDχ_u : MemLp
        (fun z : H ↦ fderiv ℝ (χ : H → ℝ) z e * u z) 2 μP₀ :=
      memLp_restrict_mul_left_of_isCompact_of_continuousOn
        hP₀_compact hDχ_cont hu_P₀
    have hu_Dχ : MemLp
        (fun z : H ↦ u z * fderiv ℝ (χ : H → ℝ) z e) 2 μP₀ := by
      simpa [mul_comm] using hDχ_u
    simpa [DW, e, scalarWeakSobolevCutoffDerivative_apply] using
      hχ_du.add hu_Dχ
  let vseq : ℕ → H → ℝ := fun n ↦
    ((scalarWeakSobolevStandardMollifier H n).normed
      (MeasureTheory.volume : Measure H) ⋆[lsmul ℝ ℝ,
      (MeasureTheory.volume : Measure H)] W : H → ℝ)
  have hv_smooth : ∀ n : ℕ, ContDiff ℝ ∞ (vseq n) := by
    intro n
    let ρ : ContDiffBump (0 : H) := scalarWeakSobolevStandardMollifier H n
    change ContDiff ℝ ∞
      (ρ.normed (MeasureTheory.volume : Measure H) ⋆[lsmul ℝ ℝ,
        (MeasureTheory.volume : Measure H)] W : H → ℝ)
    exact
      ρ.hasCompactSupport_normed.contDiff_convolution_left
        (lsmul ℝ ℝ) ρ.contDiff_normed hW_int.locallyIntegrable
  have hvalue_tendsto_W :
      Filter.Tendsto
        (fun n : ℕ ↦ eLpNorm (fun z ↦ vseq n z - W z) 2 μQ)
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
    simpa [vseq, μQ] using
      scalarWeakSobolev_standardMollifier_value_eLpNorm_tendsto_zero_of_global_integrable
        hQ hP₀_compact hQP₀ hW_int hW_P₀
  let Fseq : ℕ → H → H →L[ℝ] ℝ :=
    fun n z ↦ fderiv ℝ (vseq n) z - DW z
  have h_eval_mem :
      ∀ (n : ℕ) (i : Fin (Module.finrank ℝ H)),
        MemLp (fun z ↦ Fseq n z (Module.finBasis ℝ H i)) 2 μQ := by
    intro n i
    let e : H := Module.finBasis ℝ H i
    let L : (H →L[ℝ] ℝ) →L[ℝ] ℝ :=
      ContinuousLinearMap.apply ℝ ℝ e
    have hD_cont :
        Continuous (fun z : H ↦ fderiv ℝ (vseq n) z) :=
      (hv_smooth n).continuous_fderiv (by simp)
    have hD_eval_cont :
        Continuous (fun z : H ↦ fderiv ℝ (vseq n) z e) :=
      hD_cont.clm_apply continuous_const
    have hD_eval_mem :
        MemLp (fun z : H ↦ fderiv ℝ (vseq n) z e) 2 μQ :=
      memLp_restrict_of_isCompact_of_continuousOn
        hQ hD_eval_cont.continuousOn
    have hDW_eval_Q :
        MemLp (fun z : H ↦ DW z e) 2 μQ := by
      have hDW_eval_P₀' := hDW_eval_P₀ i
      exact hDW_eval_P₀'.mono_measure (by
        dsimp [μQ, μP₀]
        exact Measure.restrict_mono hQP₀_subset le_rfl)
    simpa [Fseq, e, ContinuousLinearMap.sub_apply] using
      hD_eval_mem.sub hDW_eval_Q
  have h_eval_tendsto :
      ∀ i : Fin (Module.finrank ℝ H),
        Filter.Tendsto
          (fun n : ℕ ↦
            eLpNorm (fun z ↦ Fseq n z (Module.finBasis ℝ H i)) 2 μQ)
          Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
    intro i
    let e : H := Module.finBasis ℝ H i
    have hdir :=
      scalarWeakSobolev_standardMollifier_directionalDerivative_eLpNorm_tendsto_zero_of_global_integrable_pair
        hQ hP₀_compact hQP₀ hP₀Ω₀ hΩ₀_open hweak_cut
        hW_int (hDW_eval_int i) hW_P₀ (hDW_eval_P₀ i)
    simpa [Fseq, vseq, DW, W, e, μQ, ContinuousLinearMap.sub_apply] using hdir
  have hfull :
      (∀ n : ℕ, MemLp (Fseq n) 2 μQ) ∧
        Filter.Tendsto (fun n : ℕ ↦ eLpNorm (Fseq n) 2 μQ)
          Filter.atTop (𝓝 (0 : ℝ≥0∞)) :=
    continuousLinearMap_sequence_memLp_and_eLpNorm_tendsto_zero_of_basis_eval'
      (Fseq := Fseq) h_eval_mem h_eval_tendsto
  have hW_eq_u_Q : W =ᵐ[μQ] u := by
    exact ae_restrict_of_forall_mem hQ.measurableSet fun z hzQ ↦ by
      simp [W, χ.eq_one_on z hzQ]
  have hDW_eq_du_Q : DW =ᵐ[μQ] du := by
    exact ae_restrict_of_forall_mem hQ.measurableSet fun z hzQ ↦ by
      ext h
      exact χ.cutoffDerivative_eq_on z hzQ
  have hu_Q : MemLp u 2 μQ :=
    hu.mono_measure (by
      dsimp [μQ]
      exact Measure.restrict_mono hQP_subset le_rfl)
  refine
    ⟨{ approximants := vseq
       smooth := hv_smooth
       value_error_memLp := ?_
       value_tendsto_l2 := ?_
       derivative_error_memLp := ?_
       derivative_tendsto_l2 := ?_ }⟩
  · intro n
    have hv_mem : MemLp (vseq n) 2 μQ :=
      memLp_restrict_of_isCompact_of_continuousOn
        hQ (hv_smooth n).continuous.continuousOn
    exact hv_mem.sub hu_Q
  · have hseq :
        (fun n : ℕ ↦ eLpNorm (fun z ↦ vseq n z - u z) 2 μQ) =
          fun n : ℕ ↦ eLpNorm (fun z ↦ vseq n z - W z) 2 μQ := by
      funext n
      exact eLpNorm_congr_ae
        ((Filter.EventuallyEq.rfl.sub hW_eq_u_Q).symm)
    change
      Filter.Tendsto
        (fun n : ℕ ↦ eLpNorm (fun z ↦ vseq n z - u z) 2 μQ)
        Filter.atTop (𝓝 (0 : ℝ≥0∞))
    rw [hseq]
    exact hvalue_tendsto_W
  · intro n
    have hmem : MemLp (Fseq n) 2 μQ := hfull.1 n
    have hae :
        Fseq n =ᵐ[μQ]
          fun z : H ↦ fderiv ℝ (vseq n) z - du z := by
      simpa [Fseq] using (Filter.EventuallyEq.rfl.sub hDW_eq_du_Q)
    exact hmem.ae_eq hae
  · have hseq :
        (fun n : ℕ ↦
          eLpNorm (fun z ↦ fderiv ℝ (vseq n) z - du z) 2 μQ) =
          fun n : ℕ ↦ eLpNorm (Fseq n) 2 μQ := by
      funext n
      exact eLpNorm_congr_ae
        ((by
          simpa [Fseq] using
            (Filter.EventuallyEq.rfl.sub hDW_eq_du_Q) :
          Fseq n =ᵐ[μQ]
            fun z : H ↦ fderiv ℝ (vseq n) z - du z).symm)
    change
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm (fun z ↦ fderiv ℝ (vseq n) z - du z) 2 μQ)
        Filter.atTop (𝓝 (0 : ℝ≥0∞))
    rw [hseq]
    exact hfull.2

set_option maxHeartbeats 800000 in
/--
%%handwave
name:
  Compact graph convergence controls pulled-back test pairings
statement:
  Let \(T:U\to\Omega\) be a locally bi-Lipschitz change of variables between
  open finite-dimensional Euclidean regions.  Suppose \(Q\) is compact and
  contains the image under \(T\) of the closed supports of \(\varphi\) and of
  \(D\varphi[v]\).  If \(u\) and \(du\) are in \(L^2(Q)\), and
  \(w_n\to u\) and \(Dw_n\to du\) in the \(L^2\) graph norm on \(Q\), then
  the two pulled-back pairings against \(\varphi\) and \(D\varphi[v]\)
  converge to the corresponding pairings for \(u\) and \(du\).
proof:
  The integrands are supported on compact subsets of \(U\).  On such compact
  sets the locally bi-Lipschitz map has finite measure distortion, so
  \(L^2(Q)\)-convergence pulls back to \(L^2\)-convergence on the supports.
  The factors \(D\varphi[v]\), \(\varphi\), and \(dT_xv\) are bounded there.
  Cauchy--Schwarz on the finite-measure support then turns these pulled-back
  \(L^2\) bounds into convergence of the integrals.
-/
theorem locallyBiLipschitz_pullback_test_pairing_tendsto_of_graph_l2_on_compact
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {U Ω : Set H} {T S : H → H}
    (_hU_open : IsOpen U) (_hΩ_open : IsOpen Ω)
    (_hT_maps : Set.MapsTo T U Ω) (_hS_maps : Set.MapsTo S Ω U)
    (_hS_left : ∀ x ∈ U, S (T x) = x)
    (_hT_left : ∀ y ∈ Ω, T (S y) = y)
    (_hT_lip : LocallyLipschitzOn U T)
    (_hS_lip : LocallyLipschitzOn Ω S)
    (_hT_qmp : Measure.QuasiMeasurePreserving T
      (MeasureTheory.volume.restrict U)
      (MeasureTheory.volume.restrict Ω))
    (_hS_qmp : Measure.QuasiMeasurePreserving S
      (MeasureTheory.volume.restrict Ω)
      (MeasureTheory.volume.restrict U))
    {Q : Set H}
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction U) (v : H)
    (_hQ_compact : IsCompact Q)
    (_hQ_support :
      T '' (tsupport (φ : H → ℝ) ∪
        tsupport (fun z : H ↦ fderiv ℝ (φ : H → ℝ) z v)) ⊆ Q)
    {u : H → ℝ} {du : H → H →L[ℝ] ℝ} {w : ℕ → H → ℝ}
    (hu_mem : MemLp u 2 (MeasureTheory.volume.restrict Q))
    (hdu_mem : MemLp du 2 (MeasureTheory.volume.restrict Q))
    (_hvalue_mem :
      ∀ n : ℕ,
        MemLp (fun y : H ↦ w n y - u y) 2
          (MeasureTheory.volume.restrict Q))
    (hvalue_tendsto :
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm (fun y : H ↦ w n y - u y) 2
            (MeasureTheory.volume.restrict Q))
        Filter.atTop (𝓝 0))
    (_hderiv_mem :
      ∀ n : ℕ,
        MemLp (fun y : H ↦ fderiv ℝ (w n) y - du y) 2
          (MeasureTheory.volume.restrict Q))
    (hderiv_tendsto :
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm (fun y : H ↦ fderiv ℝ (w n) y - du y) 2
            (MeasureTheory.volume.restrict Q))
        Filter.atTop (𝓝 0)) :
    Filter.Tendsto
      (fun n : ℕ ↦
        ∫ z in U, (fderiv ℝ (φ : H → ℝ) z v) • w n (T z)
          ∂MeasureTheory.volume)
      Filter.atTop
      (𝓝
        (∫ z in U, (fderiv ℝ (φ : H → ℝ) z v) • u (T z)
          ∂MeasureTheory.volume)) ∧
    Filter.Tendsto
      (fun n : ℕ ↦
        ∫ z in U,
          φ z •
            ((fderiv ℝ (fun x : H ↦ w n x) (T z)).comp
              (fderiv ℝ (fun x : H ↦ T x) z)) v
          ∂MeasureTheory.volume)
      Filter.atTop
      (𝓝
        (∫ z in U,
          φ z • ((du (T z)).comp
            (fderiv ℝ (fun x : H ↦ T x) z)) v
          ∂MeasureTheory.volume)) := by
  classical
  haveI : CompleteSpace H := FiniteDimensional.complete ℝ H
  haveI : ENNReal.HolderTriple (2 : ℝ≥0∞) (2 : ℝ≥0∞) 1 := by
    rw [ENNReal.holderTriple_iff]
    simpa using ENNReal.inv_two_add_inv_two
  let μU : Measure H := MeasureTheory.volume.restrict U
  let μQ : Measure H := MeasureTheory.volume.restrict Q
  let a : H → ℝ := fun z : H ↦ fderiv ℝ (φ : H → ℝ) z v
  let Kφ : Set H := tsupport (φ : H → ℝ)
  let Ka : Set H := tsupport a
  let μKφ : Measure H := MeasureTheory.volume.restrict Kφ
  let μKa : Measure H := MeasureTheory.volume.restrict Ka
  have ha_cont : Continuous a :=
    ((φ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hKφ_compact : IsCompact Kφ := φ.compact_support
  have hKφ_U : Kφ ⊆ U := φ.support_subset
  have hKa_subset : Ka ⊆ Kφ := by
    simpa [Ka, Kφ, a] using
      (tsupport_fderiv_apply_subset (𝕜 := ℝ)
        (f := (φ : H → ℝ)) v)
  have hKa_compact : IsCompact Ka :=
    hKφ_compact.of_isClosed_subset (isClosed_tsupport _) hKa_subset
  have hKa_U : Ka ⊆ U := hKa_subset.trans hKφ_U
  have hTKφQ : T '' Kφ ⊆ Q := by
    rintro y ⟨z, hz, rfl⟩
    exact _hQ_support ⟨z, Or.inl hz, rfl⟩
  have hTKaQ : T '' Ka ⊆ Q := by
    rintro y ⟨z, hz, rfl⟩
    exact _hQ_support ⟨z, Or.inr (by simpa [Ka, a] using hz), rfl⟩
  have hu_mem_Q : MemLp u 2 μQ := by
    simpa [μQ] using hu_mem
  have hdu_mem_Q : MemLp du 2 μQ := by
    simpa [μQ] using hdu_mem
  have hvalue_mem_Q :
      ∀ n : ℕ, MemLp (fun y : H ↦ w n y - u y) 2 μQ := by
    intro n
    simpa [μQ] using _hvalue_mem n
  have hderiv_mem_Q :
      ∀ n : ℕ,
        MemLp (fun y : H ↦ fderiv ℝ (w n) y - du y) 2 μQ := by
    intro n
    simpa [μQ] using _hderiv_mem n
  have hw_mem_Q : ∀ n : ℕ, MemLp (w n) 2 μQ := by
    intro n
    have hsum : MemLp (fun y : H ↦ (w n y - u y) + u y) 2 μQ :=
      (hvalue_mem_Q n).add hu_mem_Q
    simpa only [sub_add_cancel] using hsum
  have value_integrable_of_mem :
      ∀ {g : H → ℝ}, MemLp g 2 μQ →
        Integrable (fun z : H ↦ a z • g (T z)) μU := by
    intro g hg
    have hg_pull : MemLp (fun z : H ↦ g (T z)) 2 μKa := by
      simpa [μKa] using
        locallyBiLipschitz_pullback_memLp_on_compact_of_image_subset
          _hU_open _hΩ_open _hT_maps _hS_maps _hS_left _hT_left
          _hT_lip _hS_lip _hT_qmp _hS_qmp
          hKa_compact hKa_U hTKaQ (by simpa [μQ] using hg)
    have hprod_K : MemLp (fun z : H ↦ a z * g (T z)) 2 μKa := by
      simpa [μKa] using
        memLp_restrict_mul_left_of_isCompact_of_continuousOn
          hKa_compact ha_cont.continuousOn (by simpa [μKa] using hg_pull)
    haveI : IsFiniteMeasure μKa := by
      dsimp [μKa]
      exact isFiniteMeasure_restrict.2 hKa_compact.measure_ne_top
    have hprod_int_K : Integrable (fun z : H ↦ a z * g (T z)) μKa :=
      hprod_K.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have hprod_support :
        Function.support (fun z : H ↦ a z * g (T z)) ⊆ Ka := by
      intro z hz
      exact subset_tsupport a
        (Function.support_mul_subset_left
          (f := a) (g := fun z : H ↦ g (T z)) hz)
    have hprod_global : Integrable (fun z : H ↦ a z * g (T z))
        (MeasureTheory.volume : Measure H) := by
      simpa [μKa] using
        (integrableOn_iff_integrable_of_support_subset hprod_support).mp
          hprod_int_K
    have hprod_U : Integrable (fun z : H ↦ a z * g (T z)) μU :=
      hprod_global.mono_measure
        (by
          dsimp [μU]
          exact Measure.restrict_le_self)
    simpa [μU, smul_eq_mul] using hprod_U
  have deriv_integrable_of_mem :
      ∀ {G : H → H →L[ℝ] ℝ}, MemLp G 2 μQ →
        Integrable
          (fun z : H ↦
            φ z • ((G (T z)).comp
              (fderiv ℝ (fun x : H ↦ T x) z)) v)
          μU := by
    intro G hG
    let field : H → ℝ := fun z : H ↦
      ((G (T z)).comp (fderiv ℝ (fun x : H ↦ T x) z)) v
    have hfield_K : MemLp field 2 μKφ := by
      simpa [field, μKφ] using
        locallyBiLipschitz_derivative_eval_pullback_memLp_on_compact_of_image_subset
          _hU_open _hΩ_open _hT_maps _hS_maps _hS_left _hT_left
          _hT_lip _hS_lip _hT_qmp _hS_qmp
          hKφ_compact hKφ_U hTKφQ (by simpa [μQ] using hG) v
    have hprod_K : MemLp (fun z : H ↦ φ z * field z) 2 μKφ := by
      simpa [μKφ] using
        memLp_restrict_mul_left_of_isCompact_of_continuousOn
          hKφ_compact φ.smooth.continuous.continuousOn
          (by simpa [μKφ] using hfield_K)
    haveI : IsFiniteMeasure μKφ := by
      dsimp [μKφ]
      exact isFiniteMeasure_restrict.2 hKφ_compact.measure_ne_top
    have hprod_int_K : Integrable (fun z : H ↦ φ z * field z) μKφ :=
      hprod_K.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have hprod_support :
        Function.support (fun z : H ↦ φ z * field z) ⊆ Kφ := by
      intro z hz
      exact subset_tsupport (φ : H → ℝ)
        (Function.support_mul_subset_left
          (f := (φ : H → ℝ)) (g := field) hz)
    have hprod_global : Integrable (fun z : H ↦ φ z * field z)
        (MeasureTheory.volume : Measure H) := by
      simpa [μKφ] using
        (integrableOn_iff_integrable_of_support_subset hprod_support).mp
          hprod_int_K
    have hprod_U : Integrable (fun z : H ↦ φ z * field z) μU :=
      hprod_global.mono_measure
        (by
          dsimp [μU]
          exact Measure.restrict_le_self)
    simpa [field, μU, smul_eq_mul] using hprod_U
  rcases
    locallyBiLipschitz_pullback_memLp_and_eLpNorm_tendsto_zero_on_compact_of_image_subset
      _hU_open _hΩ_open _hT_maps _hS_maps _hS_left _hT_left
      _hT_lip _hS_lip _hT_qmp _hS_qmp
      hKa_compact hKa_U hTKaQ
      (f := fun (n : ℕ) (y : H) ↦ w n y - u y)
      (by simpa [μQ] using hvalue_mem_Q)
      (by simpa [μQ] using hvalue_tendsto) with
    ⟨hvalue_pull_mem, hvalue_pull_tendsto⟩
  have ha_mem_Ka : MemLp a 2 μKa := by
    simpa [μKa] using
      memLp_restrict_of_isCompact_of_continuousOn
        hKa_compact ha_cont.continuousOn
  have hvalue_raw_bound :
      ∀ n : ℕ,
        eLpNorm (fun z : H ↦ a z • (w n (T z) - u (T z))) 1 μKa ≤
          eLpNorm a 2 μKa *
            eLpNorm (fun z : H ↦ w n (T z) - u (T z)) 2 μKa := by
    intro n
    have hdiff_aesm :
        AEStronglyMeasurable
          (fun z : H ↦ w n (T z) - u (T z)) μKa :=
      (by
        simpa [μKa] using hvalue_pull_mem n :
          MemLp (fun z : H ↦ w n (T z) - u (T z)) 2 μKa).aestronglyMeasurable
    simpa [μKa] using
      (eLpNorm_smul_le_mul_eLpNorm
        (μ := μKa) (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞))
        (r := (1 : ℝ≥0∞))
        (f := fun z : H ↦ w n (T z) - u (T z))
        (φ := a)
        (hf := hdiff_aesm)
        (hφ := ha_mem_Ka.aestronglyMeasurable))
  have hvalue_mul_tendsto_K :
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm (fun z : H ↦ a z • (w n (T z) - u (T z))) 1 μKa)
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
    have hmul :
        Filter.Tendsto
          (fun n : ℕ ↦
            eLpNorm a 2 μKa *
              eLpNorm (fun z : H ↦ w n (T z) - u (T z)) 2 μKa)
          Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
      have h := ENNReal.Tendsto.const_mul
        (by simpa [μKa] using hvalue_pull_tendsto)
        (Or.inr ha_mem_Ka.eLpNorm_ne_top)
      simpa using h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hmul
      (fun n ↦ zero_le)
      hvalue_raw_bound
  have hvalue_raw_support :
      ∀ n : ℕ,
        Function.support
          (fun z : H ↦ a z • (w n (T z) - u (T z))) ⊆ Ka := by
    intro n z hz
    exact subset_tsupport a
      (Function.support_smul_subset_left
        (f := a) (g := fun z : H ↦ w n (T z) - u (T z)) hz)
  have hvalue_raw_eLp_U_eq_K :
      ∀ n : ℕ,
        eLpNorm (fun z : H ↦ a z • (w n (T z) - u (T z))) 1 μU =
          eLpNorm (fun z : H ↦ a z • (w n (T z) - u (T z))) 1 μKa := by
    intro n
    have hrestrict :=
      eLpNorm_restrict_eq_of_support_subset
        (μ := μU) (s := Ka) (p := (1 : ℝ≥0∞))
        (f := fun z : H ↦ a z • (w n (T z) - u (T z)))
        (hvalue_raw_support n)
    rw [← hrestrict]
    change
      eLpNorm (fun z : H ↦ a z • (w n (T z) - u (T z))) 1
          ((MeasureTheory.volume.restrict U).restrict Ka) =
        eLpNorm (fun z : H ↦ a z • (w n (T z) - u (T z))) 1
          (MeasureTheory.volume.restrict Ka)
    rw [Measure.restrict_restrict_of_subset hKa_U]
  have hvalue_L1_raw_U :
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm (fun z : H ↦ a z • (w n (T z) - u (T z))) 1 μU)
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) :=
    Filter.Tendsto.congr'
      (Filter.Eventually.of_forall fun n ↦ (hvalue_raw_eLp_U_eq_K n).symm)
      hvalue_mul_tendsto_K
  have hvalue_L1 :
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm
            ((fun z : H ↦ a z • w n (T z)) -
              fun z : H ↦ a z • u (T z))
            1 μU)
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) :=
    Filter.Tendsto.congr'
      (Filter.Eventually.of_forall fun n ↦ by
        apply eLpNorm_congr_ae
        exact Filter.Eventually.of_forall fun z ↦ by
          simp [Pi.sub_apply, smul_eq_mul, mul_sub])
      hvalue_L1_raw_U
  have hvalue_tendsto' :
      Filter.Tendsto
        (fun n : ℕ ↦ ∫ z, a z • w n (T z) ∂μU)
        Filter.atTop
        (𝓝 (∫ z, a z • u (T z) ∂μU)) :=
    tendsto_integral_of_L1'
      (μ := μU)
      (f := fun z : H ↦ a z • u (T z))
      (hfi := (value_integrable_of_mem hu_mem_Q).aestronglyMeasurable)
      (F := fun (n : ℕ) (z : H) ↦ a z • w n (T z))
      (hFi := Filter.Eventually.of_forall fun n ↦ value_integrable_of_mem (hw_mem_Q n))
      hvalue_L1
  let fieldErr : ℕ → H → ℝ := fun n z ↦
    (((fderiv ℝ (fun x : H ↦ w n x) (T z) - du (T z)).comp
      (fderiv ℝ (fun x : H ↦ T x) z)) v)
  rcases
    locallyBiLipschitz_pullback_memLp_and_eLpNorm_tendsto_zero_on_compact_of_image_subset
      _hU_open _hΩ_open _hT_maps _hS_maps _hS_left _hT_left
      _hT_lip _hS_lip _hT_qmp _hS_qmp
      hKφ_compact hKφ_U hTKφQ
      (f := fun (n : ℕ) (y : H) ↦ fderiv ℝ (w n) y - du y)
      (by simpa [μQ] using hderiv_mem_Q)
      (by simpa [μQ] using hderiv_tendsto) with
    ⟨hderiv_pull_mem, hderiv_pull_tendsto⟩
  have hfield_mem : ∀ n : ℕ, MemLp (fieldErr n) 2 μKφ := by
    intro n
    simpa [fieldErr, μKφ] using
      locallyBiLipschitz_derivative_eval_pullback_memLp_on_compact_of_image_subset
        _hU_open _hΩ_open _hT_maps _hS_maps _hS_left _hT_left
        _hT_lip _hS_lip _hT_qmp _hS_qmp
        hKφ_compact hKφ_U hTKφQ
        (du := fun y : H ↦ fderiv ℝ (w n) y - du y)
        (by simpa [μQ] using hderiv_mem_Q n) v
  rcases
    locallyLipschitzOn_fderiv_apply_norm_bound_on_compact
      _hU_open _hT_lip hKφ_compact hKφ_U v with
    ⟨C, hC_nonneg, hC_bound⟩
  have hfield_bound :
      ∀ n : ℕ,
        eLpNorm (fieldErr n) 2 μKφ ≤
          ENNReal.ofReal C *
            eLpNorm
              (fun z : H ↦ fderiv ℝ (w n) (T z) - du (T z))
              2 μKφ := by
    intro n
    calc
      eLpNorm (fieldErr n) 2 μKφ
          ≤ eLpNorm
              (fun z : H ↦
                (C : ℝ) • (fderiv ℝ (w n) (T z) - du (T z)))
              2 μKφ := by
            apply eLpNorm_mono_ae
            refine ae_restrict_of_forall_mem hKφ_compact.measurableSet ?_
            intro z hz
            have hDv_bound :
                ‖fderiv ℝ (fun x : H ↦ T x) z v‖ ≤ C :=
              hC_bound z hz
            calc
              ‖fieldErr n z‖
                  ≤ ‖fderiv ℝ (w n) (T z) - du (T z)‖ *
                      ‖fderiv ℝ (fun x : H ↦ T x) z v‖ := by
                    dsimp [fieldErr]
                    simpa [ContinuousLinearMap.comp_apply] using
                      ContinuousLinearMap.le_opNorm
                        (fderiv ℝ (w n) (T z) - du (T z))
                        (fderiv ℝ (fun x : H ↦ T x) z v)
              _ ≤ ‖fderiv ℝ (w n) (T z) - du (T z)‖ * C :=
                    mul_le_mul_of_nonneg_left hDv_bound (norm_nonneg _)
              _ = C * ‖fderiv ℝ (w n) (T z) - du (T z)‖ := by ring
              _ = ‖(C : ℝ) • (fderiv ℝ (w n) (T z) - du (T z))‖ := by
                    rw [norm_smul, Real.norm_of_nonneg hC_nonneg]
      _ = ENNReal.ofReal C *
            eLpNorm
              (fun z : H ↦ fderiv ℝ (w n) (T z) - du (T z))
              2 μKφ := by
            change
              eLpNorm
                ((C : ℝ) •
                  (fun z : H ↦ fderiv ℝ (w n) (T z) - du (T z)))
                2 μKφ =
                ENNReal.ofReal C *
                  eLpNorm
                    (fun z : H ↦ fderiv ℝ (w n) (T z) - du (T z))
                    2 μKφ
            have hconst :=
              eLpNorm_const_smul
                (c := (C : ℝ))
                (f := fun z : H ↦ fderiv ℝ (w n) (T z) - du (T z))
                (p := (2 : ℝ≥0∞)) (μ := μKφ)
            simpa [← ofReal_norm, Real.norm_of_nonneg hC_nonneg]
              using hconst
  have hfield_tendsto :
      Filter.Tendsto
        (fun n : ℕ ↦ eLpNorm (fieldErr n) 2 μKφ)
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
    have hmul :
        Filter.Tendsto
          (fun n : ℕ ↦
            ENNReal.ofReal C *
              eLpNorm
                (fun z : H ↦ fderiv ℝ (w n) (T z) - du (T z))
                2 μKφ)
          Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
      have h := ENNReal.Tendsto.const_mul
        (by simpa [μKφ] using hderiv_pull_tendsto)
        (Or.inr (show ENNReal.ofReal C ≠ (∞ : ℝ≥0∞) from ENNReal.ofReal_ne_top))
      simpa using h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hmul
      (fun n ↦ zero_le)
      hfield_bound
  have hφ_mem_Kφ : MemLp (φ : H → ℝ) 2 μKφ := by
    simpa [μKφ] using
      memLp_restrict_of_isCompact_of_continuousOn
        hKφ_compact φ.smooth.continuous.continuousOn
  have hderiv_raw_bound :
      ∀ n : ℕ,
        eLpNorm (fun z : H ↦ φ z • fieldErr n z) 1 μKφ ≤
          eLpNorm (φ : H → ℝ) 2 μKφ *
            eLpNorm (fieldErr n) 2 μKφ := by
    intro n
    simpa [μKφ] using
      (eLpNorm_smul_le_mul_eLpNorm
        (μ := μKφ) (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞))
        (r := (1 : ℝ≥0∞))
        (f := fieldErr n) (φ := (φ : H → ℝ))
        (hf := (hfield_mem n).aestronglyMeasurable)
        (hφ := hφ_mem_Kφ.aestronglyMeasurable))
  have hderiv_raw_tendsto_K :
      Filter.Tendsto
        (fun n : ℕ ↦ eLpNorm (fun z : H ↦ φ z • fieldErr n z) 1 μKφ)
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
    have hmul :
        Filter.Tendsto
          (fun n : ℕ ↦
            eLpNorm (φ : H → ℝ) 2 μKφ *
              eLpNorm (fieldErr n) 2 μKφ)
          Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
      have h := ENNReal.Tendsto.const_mul
        hfield_tendsto (Or.inr hφ_mem_Kφ.eLpNorm_ne_top)
      simpa using h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hmul
      (fun n ↦ zero_le)
      hderiv_raw_bound
  have hderiv_raw_support :
      ∀ n : ℕ,
        Function.support (fun z : H ↦ φ z • fieldErr n z) ⊆ Kφ := by
    intro n z hz
    exact subset_tsupport (φ : H → ℝ)
      (Function.support_smul_subset_left
        (f := (φ : H → ℝ)) (g := fieldErr n) hz)
  have hderiv_raw_eLp_U_eq_K :
      ∀ n : ℕ,
        eLpNorm (fun z : H ↦ φ z • fieldErr n z) 1 μU =
          eLpNorm (fun z : H ↦ φ z • fieldErr n z) 1 μKφ := by
    intro n
    have hrestrict :=
      eLpNorm_restrict_eq_of_support_subset
        (μ := μU) (s := Kφ) (p := (1 : ℝ≥0∞))
        (f := fun z : H ↦ φ z • fieldErr n z)
        (hderiv_raw_support n)
    rw [← hrestrict]
    change
      eLpNorm (fun z : H ↦ φ z • fieldErr n z) 1
          ((MeasureTheory.volume.restrict U).restrict Kφ) =
        eLpNorm (fun z : H ↦ φ z • fieldErr n z) 1
          (MeasureTheory.volume.restrict Kφ)
    rw [Measure.restrict_restrict_of_subset hKφ_U]
  have hderiv_L1_raw_U :
      Filter.Tendsto
        (fun n : ℕ ↦ eLpNorm (fun z : H ↦ φ z • fieldErr n z) 1 μU)
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) :=
    Filter.Tendsto.congr'
      (Filter.Eventually.of_forall fun n ↦ (hderiv_raw_eLp_U_eq_K n).symm)
      hderiv_raw_tendsto_K
  have hderiv_L1 :
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm
            ((fun z : H ↦
              φ z •
                ((fderiv ℝ (fun x : H ↦ w n x) (T z)).comp
                  (fderiv ℝ (fun x : H ↦ T x) z)) v) -
              fun z : H ↦
                φ z • ((du (T z)).comp
                  (fderiv ℝ (fun x : H ↦ T x) z)) v)
            1 μU)
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) :=
    Filter.Tendsto.congr'
      (Filter.Eventually.of_forall fun n ↦ by
        apply eLpNorm_congr_ae
        exact Filter.Eventually.of_forall fun z ↦ by
          simp [fieldErr, Pi.sub_apply, ContinuousLinearMap.comp_apply,
            smul_eq_mul, mul_sub])
      hderiv_L1_raw_U
  have hderiv_tendsto' :
      Filter.Tendsto
        (fun n : ℕ ↦
          ∫ z,
            φ z •
              ((fderiv ℝ (fun x : H ↦ w n x) (T z)).comp
                (fderiv ℝ (fun x : H ↦ T x) z)) v ∂μU)
        Filter.atTop
        (𝓝
          (∫ z,
            φ z • ((du (T z)).comp
              (fderiv ℝ (fun x : H ↦ T x) z)) v ∂μU)) :=
    tendsto_integral_of_L1'
      (μ := μU)
      (f := fun z : H ↦
        φ z • ((du (T z)).comp
          (fderiv ℝ (fun x : H ↦ T x) z)) v)
      (hfi := (deriv_integrable_of_mem hdu_mem_Q).aestronglyMeasurable)
      (F := fun (n : ℕ) (z : H) ↦
        φ z •
          ((fderiv ℝ (fun x : H ↦ w n x) (T z)).comp
            (fderiv ℝ (fun x : H ↦ T x) z)) v)
      (hFi := Filter.Eventually.of_forall fun n ↦ by
        have hraw_int : Integrable (fun z : H ↦ φ z • fieldErr n z) μU := by
          simpa [fieldErr] using
            deriv_integrable_of_mem
              (G := fun y : H ↦ fderiv ℝ (w n) y - du y)
              (hderiv_mem_Q n)
        have hlim_int :
            Integrable
              (fun z : H ↦
                φ z • ((du (T z)).comp
                  (fderiv ℝ (fun x : H ↦ T x) z)) v)
              μU :=
          deriv_integrable_of_mem hdu_mem_Q
        have hsum_int := hraw_int.add hlim_int
        exact hsum_int.congr <| Filter.Eventually.of_forall fun z ↦ by
          simp [fieldErr, ContinuousLinearMap.comp_apply, smul_eq_mul, mul_sub])
      hderiv_L1
  exact ⟨by simpa [a, μU] using hvalue_tendsto',
    by simpa [fieldErr, μU] using hderiv_tendsto'⟩

/--
%%handwave
name:
  Smooth graph approximants converge in the pulled-back test pairings
statement:
  Let \(T:U\to\Omega\) be a locally bi-Lipschitz change of variables between
  open finite-dimensional Euclidean regions.  If \(u\in W^{1,2}(\Omega)\)
  with weak derivative \(du\), then for each compactly supported smooth test
  \(\varphi\) on \(U\) and direction \(v\) there are smooth functions \(w_n\)
  such that
  \[
    \int_U D\varphi[v]\,w_n(Tx)\to
      \int_U D\varphi[v]\,u(Tx)
  \]
  and
  \[
    \int_U \varphi(x)\,Dw_n(Tx)[dT_xv]\to
      \int_U \varphi(x)\,du(Tx)[dT_xv].
  \]
proof:
  Work on a compact neighborhood of \(T(\operatorname{supp}\varphi)\).
  Smooth Sobolev graph density gives \(w_n\to u\) and \(Dw_n\to du\) in the
  local \(L^2\) graph norm.  The compact locally bi-Lipschitz distortion
  estimates pull these convergences back to the support of \(\varphi\), while
  the compact derivative bound for \(T\) controls the variable direction
  \(dT_xv\).  Pairing with the bounded compactly supported test factors gives
  convergence of the two integrals.
-/
theorem locallyBiLipschitz_pullback_test_pairing_tendsto_of_smooth_graph_density
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {U Ω : Set H} {T S : H → H}
    (_hU_open : IsOpen U) (_hΩ_open : IsOpen Ω)
    (_hT_maps : Set.MapsTo T U Ω) (_hS_maps : Set.MapsTo S Ω U)
    (_hS_left : ∀ x ∈ U, S (T x) = x)
    (_hT_left : ∀ y ∈ Ω, T (S y) = y)
    (_hT_lip : LocallyLipschitzOn U T)
    (_hS_lip : LocallyLipschitzOn Ω S)
    (_hT_qmp : Measure.QuasiMeasurePreserving T
      (MeasureTheory.volume.restrict U)
      (MeasureTheory.volume.restrict Ω))
    (_hS_qmp : Measure.QuasiMeasurePreserving S
      (MeasureTheory.volume.restrict Ω)
      (MeasureTheory.volume.restrict U))
    {u : H → ℝ} {du : H → H →L[ℝ] ℝ}
    (_hweak : IsWeakDerivativeOnEuclideanRegionWithValues Ω u du)
    (_hu : MemLp u 2 (MeasureTheory.volume.restrict Ω))
    (_hdu : MemLp du 2 (MeasureTheory.volume.restrict Ω))
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction U) (v : H) :
    ∃ w : ℕ → H → ℝ,
      (∀ n : ℕ, ContDiff ℝ ∞ (w n)) ∧
        Filter.Tendsto
          (fun n : ℕ ↦
            ∫ z in U, (fderiv ℝ (φ : H → ℝ) z v) • w n (T z)
              ∂MeasureTheory.volume)
          Filter.atTop
          (𝓝
            (∫ z in U, (fderiv ℝ (φ : H → ℝ) z v) • u (T z)
              ∂MeasureTheory.volume)) ∧
        Filter.Tendsto
          (fun n : ℕ ↦
            ∫ z in U,
              φ z •
                ((fderiv ℝ (fun x : H ↦ w n x) (T z)).comp
                  (fderiv ℝ (fun x : H ↦ T x) z)) v
              ∂MeasureTheory.volume)
          Filter.atTop
          (𝓝
            (∫ z in U,
              φ z • ((du (T z)).comp
                (fderiv ℝ (fun x : H ↦ T x) z)) v
              ∂MeasureTheory.volume)) := by
  classical
  haveI : ProperSpace H := FiniteDimensional.proper ℝ H
  let a : H → ℝ := fun z : H ↦ fderiv ℝ (φ : H → ℝ) z v
  let Kφ : Set H := tsupport (φ : H → ℝ)
  let Ka : Set H := tsupport a
  let K : Set H := Kφ ∪ Ka
  have hKφ_compact : IsCompact Kφ := φ.compact_support
  have hKa_subset : Ka ⊆ Kφ := by
    simpa [Ka, Kφ, a] using
      (tsupport_fderiv_apply_subset (𝕜 := ℝ)
        (f := (φ : H → ℝ)) v)
  have hKa_compact : IsCompact Ka :=
    hKφ_compact.of_isClosed_subset (isClosed_tsupport _) hKa_subset
  have hK_compact : IsCompact K := hKφ_compact.union hKa_compact
  have hK_U : K ⊆ U := by
    intro z hz
    rcases hz with hz | hz
    · exact φ.support_subset hz
    · exact φ.support_subset (hKa_subset hz)
  let Q : Set H := T '' K
  have hT_cont_K : ContinuousOn T K :=
    (_hT_lip.mono hK_U).continuousOn
  have hQ_compact : IsCompact Q := by
    simpa [Q] using hK_compact.image_of_continuousOn hT_cont_K
  have hQΩ : Q ⊆ Ω := by
    rintro y ⟨x, hxK, rfl⟩
    exact _hT_maps (hK_U hxK)
  rcases hQ_compact.exists_cthickening_subset_open _hΩ_open hQΩ with
    ⟨δ, hδ_pos, hδΩ⟩
  let P : Set H := Metric.cthickening δ Q
  have hP_compact : IsCompact P := by
    dsimp [P]
    exact hQ_compact.cthickening
  have hQP : ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ Q ⊆ P :=
    ⟨δ, hδ_pos, by intro y hy; exact hy⟩
  have hPΩ : P ⊆ Ω := by
    simpa [P] using hδΩ
  have huP : MemLp u 2 (MeasureTheory.volume.restrict P) :=
    _hu.mono_measure (Measure.restrict_mono hPΩ le_rfl)
  have hduP : MemLp du 2 (MeasureTheory.volume.restrict P) :=
    _hdu.mono_measure (Measure.restrict_mono hPΩ le_rfl)
  rcases
    euclideanSobolev_smooth_graph_density_l2_on_compact
      (Q := Q) (P := P) (Ω := Ω)
      hQ_compact hP_compact hQP hPΩ _hΩ_open
      _hweak huP hduP with
    ⟨hgraph⟩
  have hQ_support :
      T '' (tsupport (φ : H → ℝ) ∪
        tsupport (fun z : H ↦ fderiv ℝ (φ : H → ℝ) z v)) ⊆ Q := by
    intro y hy
    simpa [Q, K, Kφ, Ka, a, Set.union_comm] using hy
  rcases
    locallyBiLipschitz_pullback_test_pairing_tendsto_of_graph_l2_on_compact
      _hU_open _hΩ_open _hT_maps _hS_maps _hS_left _hT_left
      _hT_lip _hS_lip _hT_qmp _hS_qmp
      (Q := Q) φ v hQ_compact hQ_support
      (u := u) (du := du) (w := hgraph.approximants)
      (_hu.mono_measure (Measure.restrict_mono hQΩ le_rfl))
      (_hdu.mono_measure (Measure.restrict_mono hQΩ le_rfl))
      hgraph.value_error_memLp hgraph.value_tendsto_l2
      hgraph.derivative_error_memLp hgraph.derivative_tendsto_l2 with
    ⟨hvalue_tendsto, hderiv_tendsto⟩
  exact
    ⟨hgraph.approximants, hgraph.smooth,
      hvalue_tendsto, hderiv_tendsto⟩

/--
%%handwave
name:
  The weak identity pulls back under a locally bi-Lipschitz change of variables
statement:
  Let \(T:U\to\Omega\) be a locally bi-Lipschitz change of variables between
  open finite-dimensional Euclidean regions, with inverse \(S\).  If \(u\)
  has weak derivative \(du\) on \(\Omega\), then for every compactly supported
  smooth test \(\varphi\) on \(U\) and every direction \(v\),
  \[
    \int_U D\varphi(x)[v]\,u(Tx)\,dx
      =
    -\int_U \varphi(x)\,du(Tx)(dT_xv)\,dx .
  \]
proof:
  Approximate \(u\) by smooth Sobolev graph approximants on a compact
  neighborhood of \(T(\operatorname{supp}\varphi)\).  For smooth functions,
  the identity follows from the classical chain rule and change of variables.
  The compact bi-Lipschitz distortion bounds make the pullback operator
  continuous in the local graph norm, so both integrals pass to the limit.
-/
theorem locallyBiLipschitz_pullback_test_integral_eq
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {U Ω : Set H} {T S : H → H}
    (_hU_open : IsOpen U) (_hΩ_open : IsOpen Ω)
    (_hT_maps : Set.MapsTo T U Ω) (_hS_maps : Set.MapsTo S Ω U)
    (_hS_left : ∀ x ∈ U, S (T x) = x)
    (_hT_left : ∀ y ∈ Ω, T (S y) = y)
    (_hT_lip : LocallyLipschitzOn U T)
    (_hS_lip : LocallyLipschitzOn Ω S)
    (_hT_qmp : Measure.QuasiMeasurePreserving T
      (MeasureTheory.volume.restrict U)
      (MeasureTheory.volume.restrict Ω))
    (_hS_qmp : Measure.QuasiMeasurePreserving S
      (MeasureTheory.volume.restrict Ω)
      (MeasureTheory.volume.restrict U))
    {u : H → ℝ} {du : H → H →L[ℝ] ℝ}
    (_hweak : IsWeakDerivativeOnEuclideanRegionWithValues Ω u du)
    (_hu : MemLp u 2 (MeasureTheory.volume.restrict Ω))
    (_hdu : MemLp du 2 (MeasureTheory.volume.restrict Ω))
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction U) (v : H) :
    ∫ z in U, (fderiv ℝ (φ : H → ℝ) z v) • u (T z)
        ∂MeasureTheory.volume =
      -∫ z in U,
        φ z • ((du (T z)).comp (fderiv ℝ (fun x : H ↦ T x) z)) v
        ∂MeasureTheory.volume := by
  let L : ℝ :=
    ∫ z in U, (fderiv ℝ (φ : H → ℝ) z v) • u (T z)
      ∂MeasureTheory.volume
  let R : ℝ :=
    ∫ z in U,
      φ z • ((du (T z)).comp (fderiv ℝ (fun x : H ↦ T x) z)) v
      ∂MeasureTheory.volume
  rcases
    locallyBiLipschitz_pullback_test_pairing_tendsto_of_smooth_graph_density
      _hU_open _hΩ_open _hT_maps _hS_maps _hS_left _hT_left
      _hT_lip _hS_lip _hT_qmp _hS_qmp _hweak _hu _hdu φ v with
    ⟨w, hw_smooth, hleft_tendsto, hright_tendsto⟩
  let leftSeq : ℕ → ℝ := fun n ↦
    ∫ z in U, (fderiv ℝ (φ : H → ℝ) z v) • w n (T z)
      ∂MeasureTheory.volume
  let rightSeq : ℕ → ℝ := fun n ↦
    ∫ z in U,
      φ z •
        ((fderiv ℝ (fun x : H ↦ w n x) (T z)).comp
          (fderiv ℝ (fun x : H ↦ T x) z)) v
      ∂MeasureTheory.volume
  have hsmooth_eq : ∀ n : ℕ, leftSeq n = -rightSeq n := by
    intro n
    simpa [leftSeq, rightSeq] using
      locallyLipschitz_smooth_outer_pullback_test_integral_eq
        _hU_open _hT_lip (hw_smooth n) φ v
  have hleft_seq_tendsto : Filter.Tendsto leftSeq Filter.atTop (𝓝 L) := by
    simpa [leftSeq, L] using hleft_tendsto
  have hright_seq_tendsto : Filter.Tendsto rightSeq Filter.atTop (𝓝 R) := by
    simpa [rightSeq, R] using hright_tendsto
  have hleft_eq_neg_right :
      leftSeq = fun n : ℕ ↦ -rightSeq n := by
    funext n
    exact hsmooth_eq n
  have hneg_right_tendsto_L :
      Filter.Tendsto (fun n : ℕ ↦ -rightSeq n) Filter.atTop (𝓝 L) := by
    simpa [hleft_eq_neg_right] using hleft_seq_tendsto
  have hneg_right_tendsto_negR :
      Filter.Tendsto (fun n : ℕ ↦ -rightSeq n) Filter.atTop (𝓝 (-R)) :=
    hright_seq_tendsto.neg
  have hLR : L = -R :=
    tendsto_nhds_unique hneg_right_tendsto_L hneg_right_tendsto_negR
  simpa [L, R] using hLR

/--
%%handwave
name:
  Graph approximants converge in pulled-back test pairings under compact
  finite distortion
statement:
  Let \(T:U\to\Omega\) be locally Lipschitz and suppose that, on every compact
  subset of \(U\), the pushforward of Lebesgue measure by \(T\) is dominated
  by a finite multiple of Lebesgue measure on any compact target set
  containing the image.  If smooth functions converge to \(u\) in the local
  \(W^{1,2}\) graph norm on such a target compact set, then their pulled-back
  value and derivative test pairings converge to the pairings for \(u\).
proof:
  The compact distortion bound pulls \(L^2\)-convergence on the target back
  to \(L^2\)-convergence on the compact supports of \(\varphi\) and
  \(D\varphi[v]\).  The test factors and \(dT_xv\) are bounded on those
  supports.  Hölder's inequality gives \(L^1\)-convergence of the integrands,
  and therefore convergence of the integrals.
-/
theorem compactDistortion_pullback_test_pairing_data_of_graph_l2_on_compact
    {D H : Type}
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [MeasureSpace D] [BorelSpace D]
    [Measure.IsAddHaarMeasure (volume : Measure D)]
    [FiniteDimensional ℝ D]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {U : Set D} {Ω : Set H} {T : D → H}
    (_hU_open : IsOpen U)
    (_hT_lip : LocallyLipschitzOn U T)
    (_hT_qmp : Measure.QuasiMeasurePreserving T
      (MeasureTheory.volume.restrict U)
      (MeasureTheory.volume.restrict Ω))
    (_hT_compactPull :
      ∀ {K : Set D} {Q : Set H}, IsCompact K → K ⊆ U → T '' K ⊆ Q →
        ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
          Measure.map T (MeasureTheory.volume.restrict K) ≤
            C • MeasureTheory.volume.restrict Q)
    {Q : Set H}
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction U) (v : D)
    (_hQ_compact : IsCompact Q)
    (_hQ_support :
      T '' (tsupport (φ : D → ℝ) ∪
        tsupport (fun z : D ↦ fderiv ℝ (φ : D → ℝ) z v)) ⊆ Q)
    {u : H → ℝ} {du : H → H →L[ℝ] ℝ} {w : ℕ → H → ℝ}
    (hu_mem : MemLp u 2 (MeasureTheory.volume.restrict Q))
    (hdu_mem : MemLp du 2 (MeasureTheory.volume.restrict Q))
    (_hvalue_mem :
      ∀ n : ℕ,
        MemLp (fun y : H ↦ w n y - u y) 2
          (MeasureTheory.volume.restrict Q))
    (hvalue_tendsto :
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm (fun y : H ↦ w n y - u y) 2
            (MeasureTheory.volume.restrict Q))
        Filter.atTop (𝓝 0))
    (_hderiv_mem :
      ∀ n : ℕ,
        MemLp (fun y : H ↦ fderiv ℝ (w n) y - du y) 2
          (MeasureTheory.volume.restrict Q))
    (hderiv_tendsto :
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm (fun y : H ↦ fderiv ℝ (w n) y - du y) 2
            (MeasureTheory.volume.restrict Q))
        Filter.atTop (𝓝 0)) :
    Integrable
        (fun z : D ↦ (fderiv ℝ (φ : D → ℝ) z v) • u (T z))
        (MeasureTheory.volume.restrict U) ∧
      Integrable
        (fun z : D ↦
          φ z • ((du (T z)).comp (fderiv ℝ T z)) v)
        (MeasureTheory.volume.restrict U) ∧
      Filter.Tendsto
        (fun n : ℕ ↦
          ∫ z in U, (fderiv ℝ (φ : D → ℝ) z v) • w n (T z)
            ∂MeasureTheory.volume)
        Filter.atTop
        (𝓝
          (∫ z in U, (fderiv ℝ (φ : D → ℝ) z v) • u (T z)
            ∂MeasureTheory.volume)) ∧
      Filter.Tendsto
        (fun n : ℕ ↦
          ∫ z in U,
            φ z •
              ((fderiv ℝ (fun x : H ↦ w n x) (T z)).comp
                (fderiv ℝ (fun x : D ↦ T x) z)) v
            ∂MeasureTheory.volume)
        Filter.atTop
        (𝓝
          (∫ z in U,
            φ z • ((du (T z)).comp
              (fderiv ℝ (fun x : D ↦ T x) z)) v
            ∂MeasureTheory.volume)) := by
  classical
  haveI : CompleteSpace H := FiniteDimensional.complete ℝ H
  haveI : ENNReal.HolderTriple (2 : ℝ≥0∞) (2 : ℝ≥0∞) 1 := by
    rw [ENNReal.holderTriple_iff]
    simpa using ENNReal.inv_two_add_inv_two
  let μU : Measure D := MeasureTheory.volume.restrict U
  let μQ : Measure H := MeasureTheory.volume.restrict Q
  let a : D → ℝ := fun z : D ↦ fderiv ℝ (φ : D → ℝ) z v
  let Kφ : Set D := tsupport (φ : D → ℝ)
  let Ka : Set D := tsupport a
  let μKφ : Measure D := MeasureTheory.volume.restrict Kφ
  let μKa : Measure D := MeasureTheory.volume.restrict Ka
  have ha_cont : Continuous a :=
    ((φ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hKφ_compact : IsCompact Kφ := φ.compact_support
  have hKφ_U : Kφ ⊆ U := φ.support_subset
  have hKa_subset : Ka ⊆ Kφ := by
    simpa [Ka, Kφ, a] using
      (tsupport_fderiv_apply_subset (𝕜 := ℝ)
        (f := (φ : D → ℝ)) v)
  have hKa_compact : IsCompact Ka :=
    hKφ_compact.of_isClosed_subset (isClosed_tsupport _) hKa_subset
  have hKa_U : Ka ⊆ U := hKa_subset.trans hKφ_U
  have hTKφQ : T '' Kφ ⊆ Q := by
    rintro y ⟨z, hz, rfl⟩
    exact _hQ_support ⟨z, Or.inl hz, rfl⟩
  have hTKaQ : T '' Ka ⊆ Q := by
    rintro y ⟨z, hz, rfl⟩
    exact _hQ_support ⟨z, Or.inr (by simpa [Ka, a] using hz), rfl⟩
  have hu_mem_Q : MemLp u 2 μQ := by
    simpa [μQ] using hu_mem
  have hdu_mem_Q : MemLp du 2 μQ := by
    simpa [μQ] using hdu_mem
  have hvalue_mem_Q :
      ∀ n : ℕ, MemLp (fun y : H ↦ w n y - u y) 2 μQ := by
    intro n
    simpa [μQ] using _hvalue_mem n
  have hderiv_mem_Q :
      ∀ n : ℕ,
        MemLp (fun y : H ↦ fderiv ℝ (w n) y - du y) 2 μQ := by
    intro n
    simpa [μQ] using _hderiv_mem n
  have hw_mem_Q : ∀ n : ℕ, MemLp (w n) 2 μQ := by
    intro n
    have hsum : MemLp (fun y : H ↦ (w n y - u y) + u y) 2 μQ :=
      (hvalue_mem_Q n).add hu_mem_Q
    simpa only [sub_add_cancel] using hsum
  have value_integrable_of_mem :
      ∀ {g : H → ℝ}, MemLp g 2 μQ →
        Integrable (fun z : D ↦ a z • g (T z)) μU := by
    intro g hg
    have hg_pull : MemLp (fun z : D ↦ g (T z)) 2 μKa := by
      simpa [μKa] using
        compactDistortion_pullback_memLp_on_compact_of_image_subset
          _hT_qmp hKa_compact hKa_U hTKaQ
          (_hT_compactPull hKa_compact hKa_U hTKaQ)
          (by simpa [μQ] using hg)
    have hprod_K : MemLp (fun z : D ↦ a z * g (T z)) 2 μKa := by
      simpa [μKa] using
        memLp_restrict_mul_left_of_isCompact_of_continuousOn
          hKa_compact ha_cont.continuousOn (by simpa [μKa] using hg_pull)
    haveI : IsFiniteMeasure μKa := by
      dsimp [μKa]
      exact isFiniteMeasure_restrict.2 hKa_compact.measure_ne_top
    have hprod_int_K : Integrable (fun z : D ↦ a z * g (T z)) μKa :=
      hprod_K.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have hprod_support :
        Function.support (fun z : D ↦ a z * g (T z)) ⊆ Ka := by
      intro z hz
      exact subset_tsupport a
        (Function.support_mul_subset_left
          (f := a) (g := fun z : D ↦ g (T z)) hz)
    have hprod_global : Integrable (fun z : D ↦ a z * g (T z))
        (MeasureTheory.volume : Measure D) := by
      simpa [μKa] using
        (integrableOn_iff_integrable_of_support_subset hprod_support).mp
          hprod_int_K
    have hprod_U : Integrable (fun z : D ↦ a z * g (T z)) μU :=
      hprod_global.mono_measure
        (by
          dsimp [μU]
          exact Measure.restrict_le_self)
    simpa [μU, smul_eq_mul] using hprod_U
  have deriv_integrable_of_mem :
      ∀ {G : H → H →L[ℝ] ℝ}, MemLp G 2 μQ →
        Integrable
          (fun z : D ↦
            φ z • ((G (T z)).comp
              (fderiv ℝ (fun x : D ↦ T x) z)) v)
          μU := by
    intro G hG
    let field : D → ℝ := fun z : D ↦
      ((G (T z)).comp (fderiv ℝ (fun x : D ↦ T x) z)) v
    have hfield_K : MemLp field 2 μKφ := by
      simpa [field, μKφ] using
        compactDistortion_derivative_eval_pullback_memLp_on_compact_of_image_subset
          _hU_open _hT_lip _hT_qmp
          hKφ_compact hKφ_U hTKφQ
          (_hT_compactPull hKφ_compact hKφ_U hTKφQ)
          (by simpa [μQ] using hG) v
    have hprod_K : MemLp (fun z : D ↦ φ z * field z) 2 μKφ := by
      simpa [μKφ] using
        memLp_restrict_mul_left_of_isCompact_of_continuousOn
          hKφ_compact φ.smooth.continuous.continuousOn
          (by simpa [μKφ] using hfield_K)
    haveI : IsFiniteMeasure μKφ := by
      dsimp [μKφ]
      exact isFiniteMeasure_restrict.2 hKφ_compact.measure_ne_top
    have hprod_int_K : Integrable (fun z : D ↦ φ z * field z) μKφ :=
      hprod_K.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have hprod_support :
        Function.support (fun z : D ↦ φ z * field z) ⊆ Kφ := by
      intro z hz
      exact subset_tsupport (φ : D → ℝ)
        (Function.support_mul_subset_left
          (f := (φ : D → ℝ)) (g := field) hz)
    have hprod_global : Integrable (fun z : D ↦ φ z * field z)
        (MeasureTheory.volume : Measure D) := by
      simpa [μKφ] using
        (integrableOn_iff_integrable_of_support_subset hprod_support).mp
          hprod_int_K
    have hprod_U : Integrable (fun z : D ↦ φ z * field z) μU :=
      hprod_global.mono_measure
        (by
          dsimp [μU]
          exact Measure.restrict_le_self)
    simpa [field, μU, smul_eq_mul] using hprod_U
  rcases
    compactDistortion_pullback_memLp_and_eLpNorm_tendsto_zero_on_compact_of_image_subset
      _hT_qmp hKa_compact hKa_U hTKaQ
      (_hT_compactPull hKa_compact hKa_U hTKaQ)
      (f := fun (n : ℕ) (y : H) ↦ w n y - u y)
      (by simpa [μQ] using hvalue_mem_Q)
      (by simpa [μQ] using hvalue_tendsto) with
    ⟨hvalue_pull_mem, hvalue_pull_tendsto⟩
  have ha_mem_Ka : MemLp a 2 μKa := by
    simpa [μKa] using
      memLp_restrict_of_isCompact_of_continuousOn
        hKa_compact ha_cont.continuousOn
  have hvalue_raw_bound :
      ∀ n : ℕ,
        eLpNorm (fun z : D ↦ a z • (w n (T z) - u (T z))) 1 μKa ≤
          eLpNorm a 2 μKa *
            eLpNorm (fun z : D ↦ w n (T z) - u (T z)) 2 μKa := by
    intro n
    have hdiff_aesm :
        AEStronglyMeasurable
          (fun z : D ↦ w n (T z) - u (T z)) μKa :=
      (by
        simpa [μKa] using hvalue_pull_mem n :
          MemLp (fun z : D ↦ w n (T z) - u (T z)) 2 μKa).aestronglyMeasurable
    simpa [μKa] using
      (eLpNorm_smul_le_mul_eLpNorm
        (μ := μKa) (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞))
        (r := (1 : ℝ≥0∞))
        (f := fun z : D ↦ w n (T z) - u (T z))
        (φ := a)
        (hf := hdiff_aesm)
        (hφ := ha_mem_Ka.aestronglyMeasurable))
  have hvalue_mul_tendsto_K :
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm (fun z : D ↦ a z • (w n (T z) - u (T z))) 1 μKa)
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
    have hmul :
        Filter.Tendsto
          (fun n : ℕ ↦
            eLpNorm a 2 μKa *
              eLpNorm (fun z : D ↦ w n (T z) - u (T z)) 2 μKa)
          Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
      have h := ENNReal.Tendsto.const_mul
        (by simpa [μKa] using hvalue_pull_tendsto)
        (Or.inr ha_mem_Ka.eLpNorm_ne_top)
      simpa using h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hmul
      (fun n ↦ zero_le)
      hvalue_raw_bound
  have hvalue_raw_support :
      ∀ n : ℕ,
        Function.support
          (fun z : D ↦ a z • (w n (T z) - u (T z))) ⊆ Ka := by
    intro n z hz
    exact subset_tsupport a
      (Function.support_smul_subset_left
        (f := a) (g := fun z : D ↦ w n (T z) - u (T z)) hz)
  have hvalue_raw_eLp_U_eq_K :
      ∀ n : ℕ,
        eLpNorm (fun z : D ↦ a z • (w n (T z) - u (T z))) 1 μU =
          eLpNorm (fun z : D ↦ a z • (w n (T z) - u (T z))) 1 μKa := by
    intro n
    have hrestrict :=
      eLpNorm_restrict_eq_of_support_subset
        (μ := μU) (s := Ka) (p := (1 : ℝ≥0∞))
        (f := fun z : D ↦ a z • (w n (T z) - u (T z)))
        (hvalue_raw_support n)
    rw [← hrestrict]
    change
      eLpNorm (fun z : D ↦ a z • (w n (T z) - u (T z))) 1
          ((MeasureTheory.volume.restrict U).restrict Ka) =
        eLpNorm (fun z : D ↦ a z • (w n (T z) - u (T z))) 1
          (MeasureTheory.volume.restrict Ka)
    rw [Measure.restrict_restrict_of_subset hKa_U]
  have hvalue_L1_raw_U :
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm (fun z : D ↦ a z • (w n (T z) - u (T z))) 1 μU)
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) :=
    Filter.Tendsto.congr'
      (Filter.Eventually.of_forall fun n ↦ (hvalue_raw_eLp_U_eq_K n).symm)
      hvalue_mul_tendsto_K
  have hvalue_L1 :
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm
            ((fun z : D ↦ a z • w n (T z)) -
              fun z : D ↦ a z • u (T z))
            1 μU)
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) :=
    Filter.Tendsto.congr'
      (Filter.Eventually.of_forall fun n ↦ by
        apply eLpNorm_congr_ae
        exact Filter.Eventually.of_forall fun z ↦ by
          simp [Pi.sub_apply, smul_eq_mul, mul_sub])
      hvalue_L1_raw_U
  have hvalue_tendsto' :
      Filter.Tendsto
        (fun n : ℕ ↦ ∫ z, a z • w n (T z) ∂μU)
        Filter.atTop
        (𝓝 (∫ z, a z • u (T z) ∂μU)) :=
    tendsto_integral_of_L1'
      (μ := μU)
      (f := fun z : D ↦ a z • u (T z))
      (hfi := (value_integrable_of_mem hu_mem_Q).aestronglyMeasurable)
      (F := fun (n : ℕ) (z : D) ↦ a z • w n (T z))
      (hFi := Filter.Eventually.of_forall fun n ↦ value_integrable_of_mem (hw_mem_Q n))
      hvalue_L1
  let fieldErr : ℕ → D → ℝ := fun n z ↦
    (((fderiv ℝ (fun x : H ↦ w n x) (T z) - du (T z)).comp
      (fderiv ℝ (fun x : D ↦ T x) z)) v)
  rcases
    compactDistortion_pullback_memLp_and_eLpNorm_tendsto_zero_on_compact_of_image_subset
      _hT_qmp hKφ_compact hKφ_U hTKφQ
      (_hT_compactPull hKφ_compact hKφ_U hTKφQ)
      (f := fun (n : ℕ) (y : H) ↦ fderiv ℝ (w n) y - du y)
      (by simpa [μQ] using hderiv_mem_Q)
      (by simpa [μQ] using hderiv_tendsto) with
    ⟨hderiv_pull_mem, hderiv_pull_tendsto⟩
  have hfield_mem : ∀ n : ℕ, MemLp (fieldErr n) 2 μKφ := by
    intro n
    simpa [fieldErr, μKφ] using
      compactDistortion_derivative_eval_pullback_memLp_on_compact_of_image_subset
        _hU_open _hT_lip _hT_qmp
        hKφ_compact hKφ_U hTKφQ
        (_hT_compactPull hKφ_compact hKφ_U hTKφQ)
        (du := fun y : H ↦ fderiv ℝ (w n) y - du y)
        (by simpa [μQ] using hderiv_mem_Q n) v
  rcases
    locallyLipschitzOn_fderiv_apply_norm_bound_on_compact
      _hU_open _hT_lip hKφ_compact hKφ_U v with
    ⟨C, hC_nonneg, hC_bound⟩
  have hfield_bound :
      ∀ n : ℕ,
        eLpNorm (fieldErr n) 2 μKφ ≤
          ENNReal.ofReal C *
            eLpNorm
              (fun z : D ↦ fderiv ℝ (w n) (T z) - du (T z))
              2 μKφ := by
    intro n
    calc
      eLpNorm (fieldErr n) 2 μKφ
          ≤ eLpNorm
              (fun z : D ↦
                (C : ℝ) • (fderiv ℝ (w n) (T z) - du (T z)))
              2 μKφ := by
            apply eLpNorm_mono_ae
            refine ae_restrict_of_forall_mem hKφ_compact.measurableSet ?_
            intro z hz
            have hDv_bound :
                ‖fderiv ℝ (fun x : D ↦ T x) z v‖ ≤ C :=
              hC_bound z hz
            calc
              ‖fieldErr n z‖
                  ≤ ‖fderiv ℝ (w n) (T z) - du (T z)‖ *
                      ‖fderiv ℝ (fun x : D ↦ T x) z v‖ := by
                    dsimp [fieldErr]
                    simpa [ContinuousLinearMap.comp_apply] using
                      ContinuousLinearMap.le_opNorm
                        (fderiv ℝ (w n) (T z) - du (T z))
                        (fderiv ℝ (fun x : D ↦ T x) z v)
              _ ≤ ‖fderiv ℝ (w n) (T z) - du (T z)‖ * C :=
                    mul_le_mul_of_nonneg_left hDv_bound (norm_nonneg _)
              _ = C * ‖fderiv ℝ (w n) (T z) - du (T z)‖ := by ring
              _ = ‖(C : ℝ) • (fderiv ℝ (w n) (T z) - du (T z))‖ := by
                    rw [norm_smul, Real.norm_of_nonneg hC_nonneg]
      _ = ENNReal.ofReal C *
            eLpNorm
              (fun z : D ↦ fderiv ℝ (w n) (T z) - du (T z))
              2 μKφ := by
            change
              eLpNorm
                ((C : ℝ) •
                  (fun z : D ↦ fderiv ℝ (w n) (T z) - du (T z)))
                2 μKφ =
                ENNReal.ofReal C *
                  eLpNorm
                    (fun z : D ↦ fderiv ℝ (w n) (T z) - du (T z))
                    2 μKφ
            have hconst :=
              eLpNorm_const_smul
                (c := (C : ℝ))
                (f := fun z : D ↦ fderiv ℝ (w n) (T z) - du (T z))
                (p := (2 : ℝ≥0∞)) (μ := μKφ)
            simpa [← ofReal_norm, Real.norm_of_nonneg hC_nonneg]
              using hconst
  have hfield_tendsto :
      Filter.Tendsto
        (fun n : ℕ ↦ eLpNorm (fieldErr n) 2 μKφ)
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
    have hmul :
        Filter.Tendsto
          (fun n : ℕ ↦
            ENNReal.ofReal C *
              eLpNorm
                (fun z : D ↦ fderiv ℝ (w n) (T z) - du (T z))
                2 μKφ)
          Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
      have h := ENNReal.Tendsto.const_mul
        (by simpa [μKφ] using hderiv_pull_tendsto)
        (Or.inr (show ENNReal.ofReal C ≠ (∞ : ℝ≥0∞) from ENNReal.ofReal_ne_top))
      simpa using h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hmul
      (fun n ↦ zero_le)
      hfield_bound
  have hφ_mem_Kφ : MemLp (φ : D → ℝ) 2 μKφ := by
    simpa [μKφ] using
      memLp_restrict_of_isCompact_of_continuousOn
        hKφ_compact φ.smooth.continuous.continuousOn
  have hderiv_raw_bound :
      ∀ n : ℕ,
        eLpNorm (fun z : D ↦ φ z • fieldErr n z) 1 μKφ ≤
          eLpNorm (φ : D → ℝ) 2 μKφ *
            eLpNorm (fieldErr n) 2 μKφ := by
    intro n
    simpa [μKφ] using
      (eLpNorm_smul_le_mul_eLpNorm
        (μ := μKφ) (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞))
        (r := (1 : ℝ≥0∞))
        (f := fieldErr n) (φ := (φ : D → ℝ))
        (hf := (hfield_mem n).aestronglyMeasurable)
        (hφ := hφ_mem_Kφ.aestronglyMeasurable))
  have hderiv_raw_tendsto_K :
      Filter.Tendsto
        (fun n : ℕ ↦ eLpNorm (fun z : D ↦ φ z • fieldErr n z) 1 μKφ)
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
    have hmul :
        Filter.Tendsto
          (fun n : ℕ ↦
            eLpNorm (φ : D → ℝ) 2 μKφ *
              eLpNorm (fieldErr n) 2 μKφ)
          Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
      have h := ENNReal.Tendsto.const_mul
        hfield_tendsto (Or.inr hφ_mem_Kφ.eLpNorm_ne_top)
      simpa using h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hmul
      (fun n ↦ zero_le)
      hderiv_raw_bound
  have hderiv_raw_support :
      ∀ n : ℕ,
        Function.support (fun z : D ↦ φ z • fieldErr n z) ⊆ Kφ := by
    intro n z hz
    exact subset_tsupport (φ : D → ℝ)
      (Function.support_smul_subset_left
        (f := (φ : D → ℝ)) (g := fieldErr n) hz)
  have hderiv_raw_eLp_U_eq_K :
      ∀ n : ℕ,
        eLpNorm (fun z : D ↦ φ z • fieldErr n z) 1 μU =
          eLpNorm (fun z : D ↦ φ z • fieldErr n z) 1 μKφ := by
    intro n
    have hrestrict :=
      eLpNorm_restrict_eq_of_support_subset
        (μ := μU) (s := Kφ) (p := (1 : ℝ≥0∞))
        (f := fun z : D ↦ φ z • fieldErr n z)
        (hderiv_raw_support n)
    rw [← hrestrict]
    change
      eLpNorm (fun z : D ↦ φ z • fieldErr n z) 1
          ((MeasureTheory.volume.restrict U).restrict Kφ) =
        eLpNorm (fun z : D ↦ φ z • fieldErr n z) 1
          (MeasureTheory.volume.restrict Kφ)
    rw [Measure.restrict_restrict_of_subset hKφ_U]
  have hderiv_L1_raw_U :
      Filter.Tendsto
        (fun n : ℕ ↦ eLpNorm (fun z : D ↦ φ z • fieldErr n z) 1 μU)
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) :=
    Filter.Tendsto.congr'
      (Filter.Eventually.of_forall fun n ↦ (hderiv_raw_eLp_U_eq_K n).symm)
      hderiv_raw_tendsto_K
  have hderiv_L1 :
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm
            ((fun z : D ↦
              φ z •
                ((fderiv ℝ (fun x : H ↦ w n x) (T z)).comp
                  (fderiv ℝ (fun x : D ↦ T x) z)) v) -
              fun z : D ↦
                φ z • ((du (T z)).comp
                  (fderiv ℝ (fun x : D ↦ T x) z)) v)
            1 μU)
        Filter.atTop (𝓝 (0 : ℝ≥0∞)) :=
    Filter.Tendsto.congr'
      (Filter.Eventually.of_forall fun n ↦ by
        apply eLpNorm_congr_ae
        exact Filter.Eventually.of_forall fun z ↦ by
          simp [fieldErr, Pi.sub_apply, ContinuousLinearMap.comp_apply,
            smul_eq_mul, mul_sub])
      hderiv_L1_raw_U
  have hderiv_tendsto' :
      Filter.Tendsto
        (fun n : ℕ ↦
          ∫ z,
            φ z •
              ((fderiv ℝ (fun x : H ↦ w n x) (T z)).comp
                (fderiv ℝ (fun x : D ↦ T x) z)) v ∂μU)
        Filter.atTop
        (𝓝
          (∫ z,
            φ z • ((du (T z)).comp
              (fderiv ℝ (fun x : D ↦ T x) z)) v ∂μU)) :=
    tendsto_integral_of_L1'
      (μ := μU)
      (f := fun z : D ↦
        φ z • ((du (T z)).comp
          (fderiv ℝ (fun x : D ↦ T x) z)) v)
      (hfi := (deriv_integrable_of_mem hdu_mem_Q).aestronglyMeasurable)
      (F := fun (n : ℕ) (z : D) ↦
        φ z •
          ((fderiv ℝ (fun x : H ↦ w n x) (T z)).comp
            (fderiv ℝ (fun x : D ↦ T x) z)) v)
      (hFi := Filter.Eventually.of_forall fun n ↦ by
        have hraw_int : Integrable (fun z : D ↦ φ z • fieldErr n z) μU := by
          simpa [fieldErr] using
            deriv_integrable_of_mem
              (G := fun y : H ↦ fderiv ℝ (w n) y - du y)
              (hderiv_mem_Q n)
        have hlim_int :
            Integrable
              (fun z : D ↦
                φ z • ((du (T z)).comp
                  (fderiv ℝ (fun x : D ↦ T x) z)) v)
              μU :=
          deriv_integrable_of_mem hdu_mem_Q
        have hsum_int := hraw_int.add hlim_int
        exact hsum_int.congr <| Filter.Eventually.of_forall fun z ↦ by
          simp [fieldErr, ContinuousLinearMap.comp_apply, smul_eq_mul, mul_sub])
      hderiv_L1
  exact
    ⟨by simpa [a, μU] using value_integrable_of_mem hu_mem_Q,
      by simpa [μU] using deriv_integrable_of_mem hdu_mem_Q,
      by simpa [a, μU] using hvalue_tendsto',
      by simpa [fieldErr, μU] using hderiv_tendsto'⟩

/--
%%handwave
name:
  Smooth graph approximants give smooth-map pullback pairings
statement:
  Let \(T:U\to\Omega\) be a smooth map between open finite-dimensional
  Euclidean regions.  Assume the compact change-of-variables estimates
  supplied by the area theorem on the support of a test function.  Then smooth
  Sobolev graph approximants \(w_n\) for \(u\) can be chosen so that the two
  pulled-back pairings
  \[
    \int_U D\varphi[v]\,w_n(Tx),\qquad
    \int_U \varphi(x)\,Dw_n(Tx)[dT_xv]
  \]
  converge to the corresponding pairings with \(u\) and \(du\).
proof:
  Choose a compact neighborhood of \(T(\operatorname{supp}\varphi)\) in
  \(\Omega\), apply local smooth graph-density there, and use the compact
  area estimates for \(T\) to pull the \(L^2\) graph convergence back to the
  compact supports of \(D\varphi[v]\) and \(\varphi\).  Boundedness of the
  smooth test factors and of \(dT\) on these compact sets, followed by
  Cauchy--Schwarz, gives convergence of the pairings.
-/
theorem contDiff_pullback_test_data_of_smooth_graph_density
    {D H : Type}
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [MeasureSpace D] [BorelSpace D]
    [Measure.IsAddHaarMeasure (volume : Measure D)]
    [FiniteDimensional ℝ D]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {U : Set D} {Ω : Set H} {T : D → H}
    (_hU_open : IsOpen U) (_hΩ_open : IsOpen Ω)
    (_hT_maps : Set.MapsTo T U Ω)
    (_hT_smooth : ContDiff ℝ ⊤ T)
    (_hT_qmp : Measure.QuasiMeasurePreserving T
      (MeasureTheory.volume.restrict U)
      (MeasureTheory.volume.restrict Ω))
    (_hT_compactPull :
      ∀ {K : Set D} {Q : Set H}, IsCompact K → K ⊆ U → T '' K ⊆ Q →
        ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
          Measure.map T (MeasureTheory.volume.restrict K) ≤
            C • MeasureTheory.volume.restrict Q)
    {u : H → ℝ} {du : H → H →L[ℝ] ℝ}
    (_hweak : IsWeakDerivativeOnEuclideanRegionWithValues Ω u du)
    (_hu : MemLp u 2 (MeasureTheory.volume.restrict Ω))
    (_hdu : MemLp du 2 (MeasureTheory.volume.restrict Ω))
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction U) (v : D) :
    Integrable
        (fun z : D ↦ (fderiv ℝ (φ : D → ℝ) z v) • u (T z))
        (MeasureTheory.volume.restrict U) ∧
      Integrable
        (fun z : D ↦
          φ z • ((du (T z)).comp (fderiv ℝ T z)) v)
        (MeasureTheory.volume.restrict U) ∧
      ∃ w : ℕ → H → ℝ,
        (∀ n : ℕ, ContDiff ℝ ∞ (w n)) ∧
          Filter.Tendsto
            (fun n : ℕ ↦
              ∫ z in U, (fderiv ℝ (φ : D → ℝ) z v) • w n (T z)
                ∂MeasureTheory.volume)
            Filter.atTop
            (𝓝
              (∫ z in U, (fderiv ℝ (φ : D → ℝ) z v) • u (T z)
                ∂MeasureTheory.volume)) ∧
          Filter.Tendsto
            (fun n : ℕ ↦
              ∫ z in U,
                φ z •
                  ((fderiv ℝ (fun x : H ↦ w n x) (T z)).comp
                    (fderiv ℝ T z)) v
                ∂MeasureTheory.volume)
            Filter.atTop
            (𝓝
              (∫ z in U,
                φ z • ((du (T z)).comp (fderiv ℝ T z)) v
                ∂MeasureTheory.volume)) := by
  classical
  haveI : ProperSpace H := FiniteDimensional.proper ℝ H
  have hT_one : ContDiff ℝ 1 T :=
    _hT_smooth.of_le (by simp : (1 : WithTop ℕ∞) ≤ (⊤ : WithTop ℕ∞))
  have hT_lip : LocallyLipschitzOn U T :=
    hT_one.locallyLipschitz.locallyLipschitzOn
  let a : D → ℝ := fun z : D ↦ fderiv ℝ (φ : D → ℝ) z v
  let Kφ : Set D := tsupport (φ : D → ℝ)
  let Ka : Set D := tsupport a
  let K : Set D := Kφ ∪ Ka
  have hKφ_compact : IsCompact Kφ := φ.compact_support
  have hKa_subset : Ka ⊆ Kφ := by
    simpa [Ka, Kφ, a] using
      (tsupport_fderiv_apply_subset (𝕜 := ℝ)
        (f := (φ : D → ℝ)) v)
  have hKa_compact : IsCompact Ka :=
    hKφ_compact.of_isClosed_subset (isClosed_tsupport _) hKa_subset
  have hK_compact : IsCompact K := hKφ_compact.union hKa_compact
  have hK_U : K ⊆ U := by
    intro z hz
    rcases hz with hz | hz
    · exact φ.support_subset hz
    · exact φ.support_subset (hKa_subset hz)
  let Q : Set H := T '' K
  have hT_cont_K : ContinuousOn T K :=
    (hT_lip.mono hK_U).continuousOn
  have hQ_compact : IsCompact Q := by
    simpa [Q] using hK_compact.image_of_continuousOn hT_cont_K
  have hQΩ : Q ⊆ Ω := by
    rintro y ⟨x, hxK, rfl⟩
    exact _hT_maps (hK_U hxK)
  rcases hQ_compact.exists_cthickening_subset_open _hΩ_open hQΩ with
    ⟨δ, hδ_pos, hδΩ⟩
  let P : Set H := Metric.cthickening δ Q
  have hP_compact : IsCompact P := by
    dsimp [P]
    exact hQ_compact.cthickening
  have hQP : ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ Q ⊆ P :=
    ⟨δ, hδ_pos, by intro y hy; exact hy⟩
  have hPΩ : P ⊆ Ω := by
    simpa [P] using hδΩ
  have huP : MemLp u 2 (MeasureTheory.volume.restrict P) :=
    _hu.mono_measure (Measure.restrict_mono hPΩ le_rfl)
  have hduP : MemLp du 2 (MeasureTheory.volume.restrict P) :=
    _hdu.mono_measure (Measure.restrict_mono hPΩ le_rfl)
  rcases
    euclideanSobolev_smooth_graph_density_l2_on_compact
      (Q := Q) (P := P) (Ω := Ω)
      hQ_compact hP_compact hQP hPΩ _hΩ_open
      _hweak huP hduP with
    ⟨hgraph⟩
  have hQ_support :
      T '' (tsupport (φ : D → ℝ) ∪
        tsupport (fun z : D ↦ fderiv ℝ (φ : D → ℝ) z v)) ⊆ Q := by
    intro y hy
    simpa [Q, K, Kφ, Ka, a, Set.union_comm] using hy
  rcases
    compactDistortion_pullback_test_pairing_data_of_graph_l2_on_compact
      _hU_open hT_lip _hT_qmp _hT_compactPull
      (Q := Q) φ v hQ_compact hQ_support
      (u := u) (du := du) (w := hgraph.approximants)
      (_hu.mono_measure (Measure.restrict_mono hQΩ le_rfl))
      (_hdu.mono_measure (Measure.restrict_mono hQΩ le_rfl))
      hgraph.value_error_memLp hgraph.value_tendsto_l2
      hgraph.derivative_error_memLp hgraph.derivative_tendsto_l2 with
    ⟨hleft_int, hright_int, hvalue_tendsto, hderiv_tendsto⟩
  exact
    ⟨hleft_int, hright_int, hgraph.approximants, hgraph.smooth,
      hvalue_tendsto, hderiv_tendsto⟩

/--
%%handwave
name:
  Smooth outer functions satisfy the pullback identity for smooth maps
statement:
  If \(T:U\to\Omega\) is smooth and \(w\) is smooth on the target, then for
  every compactly supported smooth test \(\varphi\) on \(U\) and every
  direction \(v\),
  \[
    \int_U D\varphi[v]\,w(Tx)
      =
    -\int_U \varphi(x)\,Dw(Tx)[dT_xv].
  \]
proof:
  The composition \(w\circ T\) is smooth on the source, hence is a legitimate
  locally Lipschitz weak Sobolev function with classical derivative.  Apply
  the compactly supported integration-by-parts identity on \(U\), and identify
  the derivative of \(w\circ T\) by the classical chain rule.
-/
theorem contDiff_smooth_outer_pullback_test_integral_eq
    {D H : Type}
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [MeasureSpace D] [BorelSpace D]
    [Measure.IsAddHaarMeasure (volume : Measure D)]
    [FiniteDimensional ℝ D]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [FiniteDimensional ℝ H]
    {U : Set D} {T : D → H}
    (_hU_open : IsOpen U)
    (_hT_smooth : ContDiff ℝ ⊤ T)
    {w : H → ℝ} (_hw_smooth : ContDiff ℝ ∞ w)
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction U) (v : D) :
    ∫ z in U, (fderiv ℝ (φ : D → ℝ) z v) • w (T z)
        ∂MeasureTheory.volume =
      -∫ z in U,
        φ z •
          ((fderiv ℝ (fun x : H ↦ w x) (T z)).comp
            (fderiv ℝ T z)) v
        ∂MeasureTheory.volume := by
  let g : D → ℝ := fun z ↦ w (T z)
  have hw_one : ContDiff ℝ 1 (fun x : H ↦ w x) :=
    _hw_smooth.of_le (by simp : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  have hT_one : ContDiff ℝ 1 T :=
    _hT_smooth.of_le (by simp : (1 : WithTop ℕ∞) ≤ (⊤ : WithTop ℕ∞))
  have hg_one : ContDiff ℝ 1 g :=
    hw_one.comp hT_one
  have hg_lip : LocallyLipschitzOn U g := by
    exact hg_one.locallyLipschitz.locallyLipschitzOn
  have hweak :
      ∫ z in U, (fderiv ℝ (φ : D → ℝ) z v) • g z
          ∂MeasureTheory.volume =
        -∫ z in U, φ z • fderiv ℝ g z v
          ∂MeasureTheory.volume :=
    locallyLipschitzOn_weak_test_integral_eq_fderiv
      _hU_open hg_lip φ v
  have hchain :
      (fun z : D ↦ fderiv ℝ g z v)
        =ᵐ[MeasureTheory.volume.restrict U]
          fun z : D ↦
            ((fderiv ℝ (fun x : H ↦ w x) (T z)).comp
              (fderiv ℝ T z)) v := by
    exact Filter.Eventually.of_forall fun z ↦ by
      have hw_diff :
          DifferentiableAt ℝ (fun x : H ↦ w x) (T z) :=
        (_hw_smooth.differentiable (by simp)) (T z)
      have hT_diff : DifferentiableAt ℝ T z :=
        (_hT_smooth.differentiable (by simp)) z
      have hcomp :
          fderiv ℝ g z =
            (fderiv ℝ (fun x : H ↦ w x) (T z)).comp
              (fderiv ℝ T z) := by
        simpa [g, Function.comp_def] using
          (fderiv_comp z hw_diff hT_diff)
      exact congrArg (fun A : D →L[ℝ] ℝ ↦ A v) hcomp
  have hright :
      ∫ z in U, φ z • fderiv ℝ g z v
          ∂MeasureTheory.volume =
        ∫ z in U,
          φ z •
            ((fderiv ℝ (fun x : H ↦ w x) (T z)).comp
              (fderiv ℝ T z)) v
          ∂MeasureTheory.volume := by
    refine integral_congr_ae ?_
    exact hchain.mono fun z hz ↦ by simp [hz]
  calc
    ∫ z in U, (fderiv ℝ (φ : D → ℝ) z v) • w (T z)
        ∂MeasureTheory.volume
        = ∫ z in U, (fderiv ℝ (φ : D → ℝ) z v) • g z
            ∂MeasureTheory.volume := by rfl
    _ = -∫ z in U, φ z • fderiv ℝ g z v
          ∂MeasureTheory.volume := hweak
    _ = -∫ z in U,
          φ z •
            ((fderiv ℝ (fun x : H ↦ w x) (T z)).comp
              (fderiv ℝ T z)) v
          ∂MeasureTheory.volume := by rw [hright]

/--
%%handwave
name:
  Weak derivatives pull back under smooth measure-controlled maps
statement:
  Let \(T:U\to\Omega\) be a smooth map between open finite-dimensional
  Euclidean regions, and assume that pulling sets back by \(T\) preserves
  null sets for the restricted Lebesgue measures.  If \(u\) has weak
  derivative \(du\) on \(\Omega\), with \(u\) and \(du\) square integrable
  there, then \(u\circ T\) has weak derivative \(du(Tx)\circ dT_x\) on \(U\).
proof:
  Test against a compactly supported smooth function on \(U\).  On its compact
  support the map \(T\) and its derivative are bounded, and the image is a
  compact subset of \(\Omega\).  Approximate \(u\) in the local graph norm on
  that compact image by smooth functions, apply the classical chain rule to
  the smooth approximants, and pass to the limit using the null-set
  preservation and the compact derivative bounds.
-/
theorem IsWeakDerivativeOnEuclideanRegionWithValues.comp_contDiff_qmp
    {D H : Type}
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [MeasureSpace D] [BorelSpace D]
    [Measure.IsAddHaarMeasure (volume : Measure D)]
    [FiniteDimensional ℝ D]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {U : Set D} {Ω : Set H} {T : D → H}
    (_hU_open : IsOpen U) (_hΩ_open : IsOpen Ω)
    (_hT_maps : Set.MapsTo T U Ω)
    (_hT_smooth : ContDiff ℝ ⊤ T)
    (_hT_qmp : Measure.QuasiMeasurePreserving T
      (MeasureTheory.volume.restrict U)
      (MeasureTheory.volume.restrict Ω))
    (_hT_compactPull :
      ∀ {K : Set D} {Q : Set H}, IsCompact K → K ⊆ U → T '' K ⊆ Q →
        ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
          Measure.map T (MeasureTheory.volume.restrict K) ≤
            C • MeasureTheory.volume.restrict Q)
    {u : H → ℝ} {du : H → H →L[ℝ] ℝ}
    (_hweak : IsWeakDerivativeOnEuclideanRegionWithValues Ω u du)
    (_hu : MemLp u 2 (MeasureTheory.volume.restrict Ω))
    (_hdu : MemLp du 2 (MeasureTheory.volume.restrict Ω)) :
    IsWeakDerivativeOnEuclideanRegionWithValues U
      (fun x : D ↦ u (T x))
      (fun x : D ↦ (du (T x)).comp (fderiv ℝ T x)) := by
  intro φ v
  rcases
    contDiff_pullback_test_data_of_smooth_graph_density
      _hU_open _hΩ_open _hT_maps _hT_smooth _hT_qmp
      _hT_compactPull
      _hweak _hu _hdu φ v with
    ⟨hleft_int, hright_int, w, hw_smooth, hleft_tendsto, hright_tendsto⟩
  refine ⟨hleft_int, hright_int, ?_⟩
  let L : ℝ :=
    ∫ z in U, (fderiv ℝ (φ : D → ℝ) z v) • u (T z)
      ∂MeasureTheory.volume
  let R : ℝ :=
    ∫ z in U, φ z • ((du (T z)).comp (fderiv ℝ T z)) v
      ∂MeasureTheory.volume
  let leftSeq : ℕ → ℝ := fun n ↦
    ∫ z in U, (fderiv ℝ (φ : D → ℝ) z v) • w n (T z)
      ∂MeasureTheory.volume
  let rightSeq : ℕ → ℝ := fun n ↦
    ∫ z in U,
      φ z •
        ((fderiv ℝ (fun x : H ↦ w n x) (T z)).comp
          (fderiv ℝ T z)) v
      ∂MeasureTheory.volume
  have hsmooth_eq : ∀ n : ℕ, leftSeq n = -rightSeq n := by
    intro n
    simpa [leftSeq, rightSeq] using
      contDiff_smooth_outer_pullback_test_integral_eq
        _hU_open _hT_smooth (hw_smooth n) φ v
  have hleft_seq_tendsto : Filter.Tendsto leftSeq Filter.atTop (𝓝 L) := by
    simpa [leftSeq, L] using hleft_tendsto
  have hright_seq_tendsto : Filter.Tendsto rightSeq Filter.atTop (𝓝 R) := by
    simpa [rightSeq, R] using hright_tendsto
  have hleft_eq_neg_right :
      leftSeq = fun n : ℕ ↦ -rightSeq n := by
    funext n
    exact hsmooth_eq n
  have hneg_right_tendsto_L :
      Filter.Tendsto (fun n : ℕ ↦ -rightSeq n) Filter.atTop (𝓝 L) := by
    simpa [hleft_eq_neg_right] using hleft_seq_tendsto
  have hneg_right_tendsto_negR :
      Filter.Tendsto (fun n : ℕ ↦ -rightSeq n) Filter.atTop (𝓝 (-R)) :=
    hright_seq_tendsto.neg
  have hLR : L = -R :=
    tendsto_nhds_unique hneg_right_tendsto_L hneg_right_tendsto_negR
  simpa [L, R] using hLR

/--
%%handwave
name:
  Weak derivatives pull back under locally bi-Lipschitz changes of variables
statement:
  Let \(T:U\to\Omega\) be a locally bi-Lipschitz change of variables between
  open finite-dimensional Euclidean regions, with inverse \(S\), and assume
  both maps preserve null sets locally.  If \(u\) has weak derivative \(du\)
  on \(\Omega\), with \(u\) and \(du\) square integrable there, then
  \(u\circ T\) has weak derivative \(du(Tx)\circ dT_x\) on \(U\).
proof:
  Fix a compactly supported smooth test and a direction.  Use
  [integrability of the value pullback against the differentiated test](lean:JJMath.Uniformization.locallyBiLipschitz_value_pullback_test_integrable),
  [integrability of the pulled-back derivative against the test](lean:JJMath.Uniformization.locallyBiLipschitz_derivative_pullback_test_integrable),
  and
  [the pulled-back integration-by-parts identity](lean:JJMath.Uniformization.locallyBiLipschitz_pullback_test_integral_eq).
  Since this holds for every test and direction, it is exactly the weak
  derivative identity on \(U\).
-/
theorem IsWeakDerivativeOnEuclideanRegionWithValues.comp_locallyBiLipschitz
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {U Ω : Set H} {T S : H → H}
    (hU_open : IsOpen U) (hΩ_open : IsOpen Ω)
    (hT_maps : Set.MapsTo T U Ω) (hS_maps : Set.MapsTo S Ω U)
    (hS_left : ∀ x ∈ U, S (T x) = x)
    (hT_left : ∀ y ∈ Ω, T (S y) = y)
    (_hT_lip : LocallyLipschitzOn U T)
    (_hS_lip : LocallyLipschitzOn Ω S)
    (_hT_qmp : Measure.QuasiMeasurePreserving T
      (MeasureTheory.volume.restrict U)
      (MeasureTheory.volume.restrict Ω))
    (_hS_qmp : Measure.QuasiMeasurePreserving S
      (MeasureTheory.volume.restrict Ω)
      (MeasureTheory.volume.restrict U))
    {u : H → ℝ} {du : H → H →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionWithValues Ω u du)
    (_hu : MemLp u 2 (MeasureTheory.volume.restrict Ω))
    (_hdu : MemLp du 2 (MeasureTheory.volume.restrict Ω)) :
    IsWeakDerivativeOnEuclideanRegionWithValues U
      (fun x : H ↦ u (T x))
      (fun x : H ↦ (du (T x)).comp (fderiv ℝ T x)) := by
  intro φ v
  refine ⟨?_, ?_, ?_⟩
  · exact
      locallyBiLipschitz_value_pullback_test_integrable
        hU_open hΩ_open hT_maps hS_maps hS_left hT_left
        _hT_lip _hS_lip _hT_qmp _hS_qmp _hu φ v
  · exact
      locallyBiLipschitz_derivative_pullback_test_integrable
        hU_open hΩ_open hT_maps hS_maps hS_left hT_left
        _hT_lip _hS_lip _hT_qmp _hS_qmp _hdu φ v
  · exact
      locallyBiLipschitz_pullback_test_integral_eq
        hU_open hΩ_open hT_maps hS_maps hS_left hT_left
        _hT_lip _hS_lip _hT_qmp _hS_qmp hweak _hu _hdu φ v


end

end Uniformization
end JJMath
