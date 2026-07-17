import JJMath.RiemannianGeometry.Basic

/-!
# Smooth Riemannian metrics on Riemann surfaces

This file constructs smooth Riemannian metrics on Riemann surfaces.
-/

namespace JJMath

open MeasureTheory
open scoped Manifold Topology ENNReal ContDiff

namespace Uniformization
/--
%%handwave
name:
  Complex smoothness gives real smoothness
statement:
  A complex one-dimensional manifold has the underlying real smooth structure
  obtained by forgetting complex linearity.
proof:
  Holomorphic transition maps between complex charts are smooth as real maps.
  Therefore the same atlas, read in the real model of the complex plane,
  defines a smooth real two-manifold.
-/
theorem complexOneManifold_has_real_smooth_structure
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexOneManifold X] :
    IsManifold SurfaceRealModel ∞ X := by
  apply isManifold_of_contDiffOn SurfaceRealModel ∞ X
  intro e e' he he'
  have hcomplex_top :
      ContDiffOn ℂ ⊤ ((𝓘(ℂ)).extendCoordChange e e')
        ((𝓘(ℂ)).extendCoordChange e e').source :=
    (𝓘(ℂ)).contDiffOn_extendCoordChange
      (IsManifold.subset_maximalAtlas (I := 𝓘(ℂ)) (n := ⊤) he)
      (IsManifold.subset_maximalAtlas (I := 𝓘(ℂ)) (n := ⊤) he')
  have hcomplex :
      ContDiffOn ℂ ∞ ((𝓘(ℂ)).extendCoordChange e e')
        ((𝓘(ℂ)).extendCoordChange e e').source :=
    hcomplex_top.of_le le_top
  have hreal :
      ContDiffOn ℝ ∞ ((𝓘(ℂ)).extendCoordChange e e')
        ((𝓘(ℂ)).extendCoordChange e e').source :=
    @ContDiffOn.restrict_scalars ℝ inferInstance
      ℂ inferInstance inferInstance ℂ inferInstance inferInstance
      ((𝓘(ℂ)).extendCoordChange e e').source
      ((𝓘(ℂ)).extendCoordChange e e') ∞
      ℂ inferInstance inferInstance inferInstance
      (IsScalarTower.right : IsScalarTower ℝ ℂ ℂ)
      inferInstance (IsScalarTower.right : IsScalarTower ℝ ℂ ℂ)
      hcomplex
  simpa [SurfaceRealModel, ModelWithCorners.extendCoordChange] using hreal

/--
%%handwave
name:
  Positive bilinear forms on the model plane are coercive
statement:
  A continuous positive definite symmetric real bilinear form on the complex
  plane dominates a positive multiple of the squared Euclidean norm.
proof:
  Restrict the associated quadratic form to the Euclidean unit circle.  By
  compactness it has a minimum there, and positivity makes this minimum
  strictly positive.  Scaling any nonzero vector onto the unit circle gives
  the desired lower bound.
-/
theorem positiveDefiniteSymmetricBilinearForm_complex_isCoercive
    (b : ℂ →L[ℝ] ℂ →L[ℝ] ℝ)
    (hb : (∀ v w : ℂ, b v w = b w v) ∧
      ∀ v : ℂ, v ≠ 0 → 0 < b v v) :
    IsCoercive b := by
  let q : ℂ → ℝ := fun v ↦ b v v
  have hq_cont : Continuous q := by
    change Continuous (fun v : ℂ ↦ b v v)
    fun_prop
  have hs_comp : IsCompact (Metric.sphere (0 : ℂ) 1) := isCompact_sphere 0 1
  have hs_nonempty : (Metric.sphere (0 : ℂ) 1).Nonempty := by
    exact ⟨1, by simp⟩
  obtain ⟨u, hu, hu_min⟩ :=
    hs_comp.exists_isMinOn hs_nonempty hq_cont.continuousOn
  have hu_ne : u ≠ 0 := by
    have hnorm : ‖u‖ = 1 := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hu
    intro h
    rw [h] at hnorm
    norm_num at hnorm
  have hCpos : 0 < q u := hb.2 u hu_ne
  refine ⟨q u, hCpos, ?_⟩
  intro v
  by_cases hv : v = 0
  · simp [hv, q]
  · have hnorm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    let w : ℂ := (‖v‖⁻¹ : ℝ) • v
    have hw_sphere : w ∈ Metric.sphere (0 : ℂ) 1 := by
      simp [w, hnorm_pos.ne']
    have hmin_w : q u ≤ q w := hu_min hw_sphere
    have hq_w : q w = ‖v‖⁻¹ * ‖v‖⁻¹ * q v := by
      rw [show w = (‖v‖⁻¹ : ℝ) • v by rfl]
      change b ((‖v‖⁻¹ : ℝ) • v) ((‖v‖⁻¹ : ℝ) • v) =
        ‖v‖⁻¹ * ‖v‖⁻¹ * b v v
      rw [map_smul, map_smul]
      simp [mul_assoc]
    rw [hq_w] at hmin_w
    calc
      q u * ‖v‖ * ‖v‖ = q u * (‖v‖ * ‖v‖) := by ring
      _ ≤ (‖v‖⁻¹ * ‖v‖⁻¹ * q v) * (‖v‖ * ‖v‖) := by
        exact mul_le_mul_of_nonneg_right hmin_w
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = q v := by
        field_simp [hnorm_pos.ne']

/--
%%handwave
name:
  Conformal tangent forms are positive definite
statement:
  A conformal tangent form is positive definite and symmetric.
proof:
  A positive multiple of the Euclidean inner product is symmetric and is
  positive on every nonzero tangent vector.
-/
theorem conformalTangentForm_positiveDefinite
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X]
    {x : X} {b : TangentBilinearFormAt X x}
    (hb : IsConformalTangentForm x b) :
    IsPositiveDefiniteSymmetricTangentForm x b := by
  rcases hb with ⟨c, hcpos, hc⟩
  constructor
  · intro v w
    rw [hc v w, hc w v]
    simp [real_inner_comm]
  · intro v hv
    rw [hc v v]
    have hv_complex : (show ℂ from v) ≠ 0 := hv
    exact mul_pos hcpos (real_inner_self_pos.mpr hv_complex)

/--
%%handwave
name:
  Conformal tangent forms form a convex cone
statement:
  At each point of a Riemann surface, the conformal tangent forms form a
  convex subset of the vector space of tangent-bilinear forms.
proof:
  A convex combination of positive scalar multiples of the Euclidean inner
  product is again a positive scalar multiple of the Euclidean inner product.
-/
theorem conformalTangentForm_convex
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X] (x : X) :
    Convex ℝ {b : TangentBilinearFormAt X x | IsConformalTangentForm x b} := by
  rw [convex_iff_add_mem]
  intro b₁ hb₁ b₂ hb₂ a c ha hc hac
  rcases hb₁ with ⟨r₁, hr₁pos, hb₁⟩
  rcases hb₂ with ⟨r₂, hr₂pos, hb₂⟩
  refine ⟨a * r₁ + c * r₂, ?_, ?_⟩
  · have hcoeff : 0 < a ∨ 0 < c := by
      by_contra h
      push Not at h
      nlinarith
    rcases hcoeff with ha_pos | hc_pos
    · have hterm : 0 < a * r₁ := mul_pos ha_pos hr₁pos
      have hterm₂ : 0 ≤ c * r₂ := mul_nonneg hc hr₂pos.le
      nlinarith
    · have hterm : 0 < c * r₂ := mul_pos hc_pos hr₂pos
      have hterm₁ : 0 ≤ a * r₁ := mul_nonneg ha hr₁pos.le
      nlinarith
  · intro v w
    change a * ((b₁ v) w) + c * ((b₂ v) w) =
      (a * r₁ + c * r₂) * inner ℝ (show ℂ from v) (show ℂ from w)
    rw [hb₁ v w, hb₂ v w]
    ring

/--
%%handwave
name:
  Positive definite tangent forms have bounded unit balls
statement:
  The sublevel set of a positive definite symmetric tangent form is von
  Neumann bounded in the tangent space.
proof:
  In the finite-dimensional model tangent plane, a positive definite symmetric
  bilinear form defines a norm equivalent to the ambient norm.  Hence its unit
  ball is bounded.
-/
theorem positiveDefiniteSymmetricTangentForm_isVonNBounded
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X]
    (x : X) (b : TangentBilinearFormAt X x)
    (hb : IsPositiveDefiniteSymmetricTangentForm x b) :
    Bornology.IsVonNBounded ℝ {v : TangentSpace SurfaceRealModel x | b v v < 1} := by
  change Bornology.IsVonNBounded ℝ {v : ℂ | b v v < 1}
  rcases positiveDefiniteSymmetricBilinearForm_complex_isCoercive b hb with
    ⟨C, hCpos, hcoer⟩
  refine (NormedSpace.isVonNBounded_iff' (𝕜 := ℝ) (E := ℂ)).2 ⟨max 1 C⁻¹, ?_⟩
  intro v hv
  by_cases hnorm_le : ‖v‖ ≤ 1
  · exact le_trans hnorm_le (le_max_left _ _)
  · have hnorm_gt : 1 < ‖v‖ := lt_of_not_ge hnorm_le
    have hcoer_v : C * ‖v‖ * ‖v‖ ≤ b v v := hcoer v
    have hC_norm_lt : C * ‖v‖ < 1 := by
      have hC_norm_lt_sq : C * ‖v‖ < C * ‖v‖ * ‖v‖ := by
        have hC_norm_pos : 0 < C * ‖v‖ :=
          mul_pos hCpos (lt_trans zero_lt_one hnorm_gt)
        calc
          C * ‖v‖ = (C * ‖v‖) * 1 := by ring
          _ < (C * ‖v‖) * ‖v‖ := by
            exact mul_lt_mul_of_pos_left hnorm_gt hC_norm_pos
          _ = C * ‖v‖ * ‖v‖ := by ring
      exact lt_trans (lt_of_lt_of_le hC_norm_lt_sq hcoer_v) hv
    have hnorm_lt_inv : ‖v‖ < C⁻¹ := by
      have hnorm_mul_C_lt : ‖v‖ * C < 1 := by
        simpa [mul_comm] using hC_norm_lt
      rw [inv_eq_one_div]
      exact (lt_div_iff₀ hCpos).2 hnorm_mul_C_lt
    exact le_trans hnorm_lt_inv.le (le_max_right _ _)

/--
%%handwave
name:
  Euclidean tangent-bilinear form on the model plane
statement:
  The model tangent plane carries its Euclidean real inner product, regarded
  as a continuous real bilinear form.
-/
noncomputable def euclideanTangentBilinearForm : TangentBilinearFormModel :=
  innerSL ℝ

/--
%%handwave
name:
  The Euclidean tangent form is positive definite
statement:
  The Euclidean real inner product on the model tangent plane is positive
  definite and symmetric.
proof:
  This is the usual symmetry and positivity of the real inner product.
-/
theorem euclideanTangentBilinearForm_positiveDefinite :
    (∀ v w : ℂ, euclideanTangentBilinearForm v w =
      euclideanTangentBilinearForm w v) ∧
      ∀ v : ℂ, v ≠ 0 → 0 < euclideanTangentBilinearForm v v := by
  constructor
  · intro v w
    change inner ℝ v w = inner ℝ w v
    exact (real_inner_comm v w).symm
  · intro v hv
    change 0 < inner ℝ v v
    exact real_inner_self_pos.mpr hv

/--
%%handwave
name:
  Pullbacks preserve positive definite symmetric forms
statement:
  Pulling back a positive definite symmetric bilinear form along an injective
  linear map again gives a positive definite symmetric bilinear form.
proof:
  Symmetry is immediate by applying symmetry of the original form to the
  images of the two vectors.  Positivity follows because injectivity sends a
  nonzero vector to a nonzero vector.
-/
theorem positiveDefiniteSymmetricBilinearForm_pullback
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (hL : Function.Injective L)
    (b : F →L[ℝ] F →L[ℝ] ℝ)
    (hb : (∀ v w : F, b v w = b w v) ∧
      ∀ v : F, v ≠ 0 → 0 < b v v) :
    (∀ v w : E, b (L v) (L w) = b (L w) (L v)) ∧
      ∀ v : E, v ≠ 0 → 0 < b (L v) (L v) := by
  constructor
  · intro v w
    exact hb.1 (L v) (L w)
  · intro v hv
    have hLv : L v ≠ 0 := by
      intro hzero
      apply hv
      apply hL
      simpa using hzero
    exact hb.2 (L v) hLv

/--
%%handwave
name:
  Positive tangent forms form a convex cone
statement:
  At each point of a surface, the positive definite symmetric tangent-bilinear
  forms form a convex subset of the vector space of tangent-bilinear forms.
proof:
  Symmetry is preserved by linear combinations.  If two quadratic forms are
  positive on every nonzero vector, then every convex combination of them is
  also positive on every nonzero vector.
-/
theorem positiveDefiniteSymmetricTangentForm_convex
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X] (x : X) :
    Convex ℝ {b : TangentBilinearFormAt X x |
      IsPositiveDefiniteSymmetricTangentForm x b} := by
  rw [convex_iff_add_mem]
  intro b₁ hb₁ b₂ hb₂ a c ha hc hac
  constructor
  · intro v w
    simp [hb₁.1 v w, hb₂.1 v w]
  · intro v hv
    have hb₁pos : 0 < b₁ v v := hb₁.2 v hv
    have hb₂pos : 0 < b₂ v v := hb₂.2 v hv
    have hcoeff : 0 < a ∨ 0 < c := by
      by_contra h
      push Not at h
      nlinarith
    have h₁nonneg : 0 ≤ a * b₁ v v := mul_nonneg ha hb₁pos.le
    have h₂nonneg : 0 ≤ c * b₂ v v := mul_nonneg hc hb₂pos.le
    simp
    rcases hcoeff with ha_pos | hc_pos
    · have h₁pos : 0 < a * b₁ v v := mul_pos ha_pos hb₁pos
      nlinarith
    · have h₂pos : 0 < c * b₂ v v := mul_pos hc_pos hb₂pos
      nlinarith

set_option maxHeartbeats 1000000

/--
%%handwave
name:
  Coordinates of tangent-bilinear-form trivializations
statement:
  The coordinate expression of a tangent-bilinear form under the
  tangent-bilinear-form bundle trivialization is the form obtained by reading
  the bilinear form in tangent-coordinate trivializations.
proof:
  The tangent-bilinear-form bundle is the hom-bundle built from the tangent
  bundle and the trivial real line bundle.  Mathlib's hom-bundle
  trivialization formula identifies its coordinate map with the usual
  coordinate expression for continuous linear maps.
-/
theorem tangentBilinearForm_trivializationAt_continuousLinearMapAt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X] (x₀ y : X)
    (hy : y ∈
      (trivializationAt TangentBilinearFormModel
        (fun x : X ↦ TangentBilinearFormAt X x) x₀).baseSet)
    (b : TangentBilinearFormAt X y) :
    (trivializationAt TangentBilinearFormModel
      (fun x : X ↦ TangentBilinearFormAt X x) x₀).continuousLinearMapAt ℝ y b =
      ContinuousLinearMap.inCoordinates ℂ
        (TangentSpace SurfaceRealModel : X → Type)
        (ℂ →L[ℝ] ℝ)
        (fun x : X ↦ TangentSpace SurfaceRealModel x →L[ℝ] ℝ)
        x₀ y x₀ y b := by
  let e :=
    trivializationAt TangentBilinearFormModel
      (fun x : X ↦ TangentBilinearFormAt X x) x₀
  have hye : y ∈ e.baseSet := by
    simpa [e] using hy
  have h :=
    hom_trivializationAt_apply (RingHom.id ℝ)
      (F₁ := ℂ)
      (E₁ := (TangentSpace SurfaceRealModel : X → Type))
      (F₂ := ℂ →L[ℝ] ℝ)
      (E₂ := fun x : X ↦ TangentSpace SurfaceRealModel x →L[ℝ] ℝ)
      x₀ (Bundle.TotalSpace.mk' TangentBilinearFormModel y b)
  have hlin :
      e.continuousLinearMapAt ℝ y b =
        (e (Bundle.TotalSpace.mk' TangentBilinearFormModel y b)).2 := by
    rw [Bundle.Trivialization.continuousLinearMapAt_apply,
      Bundle.Trivialization.linearMapAt_apply]
    simp [hye]
  change e.continuousLinearMapAt ℝ y b =
    ContinuousLinearMap.inCoordinates ℂ
      (TangentSpace SurfaceRealModel : X → Type)
      (ℂ →L[ℝ] ℝ)
      (fun x : X ↦ TangentSpace SurfaceRealModel x →L[ℝ] ℝ)
      x₀ y x₀ y b
  rw [hlin]
  simpa [e, TangentBilinearFormAt, TangentBilinearFormModel] using congrArg Prod.snd h

/--
%%handwave
name:
  Pulling back the Euclidean tangent form preserves positivity
statement:
  In a local trivialization of the tangent-bilinear-form bundle, the section
  whose coordinate expression is the Euclidean model form is positive
  definite and symmetric on every fiber over the trivializing neighborhood.
proof:
  The trivialization of the bilinear-form bundle is induced from the tangent
  bundle trivialization.  Thus the pulled-back form evaluates as the Euclidean
  form on the tangent-coordinate images of its vector arguments.  Since the
  tangent-coordinate map is a linear isomorphism on the trivializing
  neighborhood, symmetry and strict positivity are transported from the model
  Euclidean form.
-/
theorem trivialization_symmL_euclideanTangentBilinearForm_positive
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X] (x₀ y : X)
    (hy : y ∈
      (trivializationAt TangentBilinearFormModel
        (fun x : X ↦ TangentBilinearFormAt X x) x₀).baseSet) :
    IsPositiveDefiniteSymmetricTangentForm y
      ((trivializationAt TangentBilinearFormModel
        (fun x : X ↦ TangentBilinearFormAt X x) x₀).symmL ℝ y
          euclideanTangentBilinearForm) := by
  let eT := trivializationAt ℂ (TangentSpace SurfaceRealModel : X → Type) x₀
  let eB :=
    trivializationAt TangentBilinearFormModel
      (fun x : X ↦ TangentBilinearFormAt X x) x₀
  let b : TangentBilinearFormAt X y :=
    eB.symmL ℝ y euclideanTangentBilinearForm
  have hyB : y ∈ eB.baseSet := by
    simpa [eB] using hy
  have hyT : y ∈ eT.baseSet := by
    simpa [eT, eB, TangentBilinearFormAt, TangentBilinearFormModel,
      hom_trivializationAt] using hy
  have hR : y ∈ (trivializationAt ℝ (Bundle.Trivial X ℝ) x₀).baseSet := by
    simp
  have hcoord :
      ContinuousLinearMap.inCoordinates ℂ
        (TangentSpace SurfaceRealModel : X → Type)
        (ℂ →L[ℝ] ℝ)
        (fun x : X ↦ TangentSpace SurfaceRealModel x →L[ℝ] ℝ)
        x₀ y x₀ y b = euclideanTangentBilinearForm := by
    have h1 :
        eB.continuousLinearMapAt ℝ y b =
          euclideanTangentBilinearForm := by
      exact eB.continuousLinearMapAt_symmL (R := ℝ) hyB
        euclideanTangentBilinearForm
    have h2 :
        eB.continuousLinearMapAt ℝ y b =
          ContinuousLinearMap.inCoordinates ℂ
            (TangentSpace SurfaceRealModel : X → Type)
            (ℂ →L[ℝ] ℝ)
            (fun x : X ↦ TangentSpace SurfaceRealModel x →L[ℝ] ℝ)
            x₀ y x₀ y b := by
      have h :=
        hom_trivializationAt_apply (RingHom.id ℝ)
          (F₁ := ℂ)
          (E₁ := (TangentSpace SurfaceRealModel : X → Type))
          (F₂ := ℂ →L[ℝ] ℝ)
          (E₂ := fun x : X ↦ TangentSpace SurfaceRealModel x →L[ℝ] ℝ)
          x₀ (Bundle.TotalSpace.mk' TangentBilinearFormModel y b)
      have hlin :
          eB.continuousLinearMapAt ℝ y b =
            (eB (Bundle.TotalSpace.mk' TangentBilinearFormModel y b)).2 := by
        rw [Bundle.Trivialization.continuousLinearMapAt_apply,
          Bundle.Trivialization.linearMapAt_apply]
        simp [hyB]
      rw [hlin]
      simpa [eB, TangentBilinearFormAt, TangentBilinearFormModel] using congrArg Prod.snd h
    rw [h2] at h1
    exact h1
  have eval_eq (v w : TangentSpace SurfaceRealModel y) :
      b v w =
        euclideanTangentBilinearForm
          (eT.continuousLinearMapAt ℝ y v)
          (eT.continuousLinearMapAt ℝ y w) := by
    have heq :=
      congrArg
        (fun q : TangentBilinearFormModel ↦
          q (eT.continuousLinearMapAt ℝ y v)
            (eT.continuousLinearMapAt ℝ y w))
        hcoord
    change
      (ContinuousLinearMap.inCoordinates ℂ
        (TangentSpace SurfaceRealModel : X → Type)
        (ℂ →L[ℝ] ℝ)
        (fun x : X ↦ TangentSpace SurfaceRealModel x →L[ℝ] ℝ)
        x₀ y x₀ y b)
          (eT.continuousLinearMapAt ℝ y v)
          (eT.continuousLinearMapAt ℝ y w) =
        euclideanTangentBilinearForm
          (eT.continuousLinearMapAt ℝ y v)
          (eT.continuousLinearMapAt ℝ y w) at heq
    rw [inCoordinates_apply_eq₂ hyT hyT hR] at heq
    have hv_back : eT.symm y (eT.continuousLinearMapAt ℝ y v) = v := by
      simpa [Bundle.Trivialization.coe_symmₗ] using
        eT.symmL_continuousLinearMapAt (R := ℝ) hyT v
    have hw_back : eT.symm y (eT.continuousLinearMapAt ℝ y w) = w := by
      simpa [Bundle.Trivialization.coe_symmₗ] using
        eT.symmL_continuousLinearMapAt (R := ℝ) hyT w
    rw [hv_back, hw_back] at heq
    simpa using heq
  constructor
  · intro v w
    rw [eval_eq v w, eval_eq w v]
    exact euclideanTangentBilinearForm_positiveDefinite.1 _ _
  · intro v hv
    have hcoord_ne : eT.continuousLinearMapAt ℝ y v ≠ 0 := by
      intro hzero
      have hv_zero : v = 0 := by
        rw [← eT.symmL_continuousLinearMapAt (R := ℝ) hyT v, hzero, map_zero]
      exact hv hv_zero
    rw [eval_eq v v]
    exact euclideanTangentBilinearForm_positiveDefinite.2 _ hcoord_ne

set_option maxHeartbeats 200000

/--
%%handwave
name:
  Coordinate charts give local positive tangent forms
statement:
  Around every point of a smooth surface there is a smooth local section of
  positive definite symmetric tangent-bilinear forms.
proof:
  Choose a coordinate chart and pull back the Euclidean inner product on the
  model tangent plane by the chart differential.  The chart derivative is a
  smooth bundle isomorphism on the chart domain, so the pulled-back Euclidean
  form is a smooth positive definite symmetric local section.
-/
theorem exists_local_contMDiff_positiveDefiniteSymmetricTangentForm
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X] :
    ∀ x₀ : X, ∃ U ∈ 𝓝 x₀, ∃ s_loc : (x : X) → TangentBilinearFormAt X x,
      ContMDiffOn SurfaceRealModel
        (SurfaceRealModel.prod 𝓘(ℝ, TangentBilinearFormModel)) ∞
        (fun x ↦ Bundle.TotalSpace.mk' TangentBilinearFormModel x (s_loc x)) U ∧
        ∀ y ∈ U, IsPositiveDefiniteSymmetricTangentForm y (s_loc y) := by
  intro x₀
  let e :=
    trivializationAt TangentBilinearFormModel
      (fun x : X ↦ TangentBilinearFormAt X x) x₀
  let s_loc : (x : X) → TangentBilinearFormAt X x :=
    fun x ↦ e.symmL ℝ x euclideanTangentBilinearForm
  refine ⟨e.baseSet, ?_, s_loc, ?_, ?_⟩
  · exact e.open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt TangentBilinearFormModel
        (fun x : X ↦ TangentBilinearFormAt X x) x₀)
  · rw [Bundle.Trivialization.contMDiffOn_section_baseSet_iff
      (𝕜 := ℝ) (B := X) (F := TangentBilinearFormModel)
      (E := fun x : X ↦ TangentBilinearFormAt X x)
      (IB := SurfaceRealModel) (n := ∞) (s := s_loc) e]
    refine ((contMDiff_const (c := euclideanTangentBilinearForm)).contMDiffOn.congr ?_)
    intro x hx
    have hcoord :=
      e.continuousLinearMapAt_symmL (R := ℝ) hx euclideanTangentBilinearForm
    simp [s_loc, Bundle.Trivialization.continuousLinearMapAt_apply,
      Bundle.Trivialization.linearMapAt_apply, hx] at hcoord ⊢
  · intro y hy
    exact trivialization_symmL_euclideanTangentBilinearForm_positive x₀ y (by simpa [e] using hy)

/--
%%handwave
name:
  Partition of unity gives a smooth positive tangent form
statement:
  On a Hausdorff sigma-compact smooth surface, there is a smooth family of
  positive definite symmetric tangent-bilinear forms.
proof:
  In each coordinate chart, pull back the Euclidean inner product from the
  model tangent plane.  These local sections are smooth and land in the convex
  fiberwise cone of positive definite symmetric bilinear forms.  Apply the
  partition-of-unity theorem for smooth sections with values in convex
  fiberwise sets to patch the local sections globally.
-/
theorem exists_contMDiff_positiveDefiniteSymmetricTangentForm_via_partitionOfUnity
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X] [T2Space X] [SigmaCompactSpace X] :
    ∃ inner : (x : X) → TangentBilinearFormAt X x,
      ContMDiff SurfaceRealModel
        (SurfaceRealModel.prod 𝓘(ℝ, TangentBilinearFormModel)) ∞
        (fun x ↦ Bundle.TotalSpace.mk' TangentBilinearFormModel x (inner x)) ∧
        ∀ x : X, IsPositiveDefiniteSymmetricTangentForm x (inner x) := by
  let t : ∀ x : X, Set (TangentBilinearFormAt X x) :=
    fun x ↦ {b | IsPositiveDefiniteSymmetricTangentForm x b}
  obtain ⟨s, hs⟩ :=
    exists_contMDiffSection_forall_mem_convex_of_local
      (I := SurfaceRealModel) (M := X) (F_fiber := TangentBilinearFormModel)
      (V := fun x : X ↦ TangentBilinearFormAt X x) t
      (fun x ↦ positiveDefiniteSymmetricTangentForm_convex x)
      (exists_local_contMDiff_positiveDefiniteSymmetricTangentForm X)
  exact ⟨fun x ↦ s x, s.contMDiff, hs⟩

/--
%%handwave
name:
  Smooth Riemannian metrics from partitions of unity
statement:
  A Hausdorff sigma-compact smooth surface admits a smooth Riemannian metric.
proof:
  Use
  [a smooth family of positive definite symmetric tangent-bilinear
  forms](lean:JJMath.Uniformization.exists_contMDiff_positiveDefiniteSymmetricTangentForm_via_partitionOfUnity)
  obtained by patching the Euclidean coordinate inner products.  The symmetry,
  positivity, and smoothness fields give the Mathlib smooth Riemannian metric;
  [the positive definite sublevel sets are von Neumann
  bounded](lean:JJMath.Uniformization.positiveDefiniteSymmetricTangentForm_isVonNBounded),
  which supplies the remaining boundedness field.
tags:
  milestone
-/
theorem exists_smoothRiemannianMetricOnSurface_via_partitionOfUnity
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X] [T2Space X] [SigmaCompactSpace X] :
    Nonempty (SmoothRiemannianMetricOnSurface X) := by
  rcases exists_contMDiff_positiveDefiniteSymmetricTangentForm_via_partitionOfUnity X with
    ⟨inner, hcont, hinner⟩
  refine ⟨
    { isManifold_real := inferInstance
      toContMDiffRiemannianMetric := ?_ }⟩
  refine
    { inner := inner
      symm := fun x v w ↦ (hinner x).1 v w
      pos := fun x v hv ↦ (hinner x).2 v hv
      isVonNBounded := fun x ↦
        positiveDefiniteSymmetricTangentForm_isVonNBounded x (inner x) (hinner x)
      contMDiff := hcont }

/--
%%handwave
name:
  Riemann surfaces have smooth Riemannian metrics
statement:
  Every Riemann surface admits a smooth Riemannian metric.
proof:
  [Radó second countability](lean:JJMath.Uniformization.rado_secondCountableTopology_riemannSurface)
  gives sigma-compactness because Riemann surfaces are locally compact.  After
  forgetting complex linearity, the real smooth surface has
  [a smooth Riemannian metric](lean:JJMath.Uniformization.exists_smoothRiemannianMetricOnSurface_via_partitionOfUnity)
  by a partition of unity.
tags:
  milestone
-/
theorem riemannSurface_has_smoothRiemannianMetric
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] :
    Nonempty (SmoothRiemannianMetricOnSurface X) := by
  haveI : IsManifold SurfaceRealModel ∞ X :=
    complexOneManifold_has_real_smooth_structure X
  haveI : SecondCountableTopology X :=
    rado_secondCountableTopology_riemannSurface X
  haveI : SigmaCompactSpace X := inferInstance
  exact exists_smoothRiemannianMetricOnSurface_via_partitionOfUnity X


end Uniformization

end JJMath
