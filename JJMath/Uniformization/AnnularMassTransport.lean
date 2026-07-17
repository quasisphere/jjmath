import JJMath.Uniformization.CompactSupportTransfer

/-!
# Compactly supported mass transport through an end

This file iterates finite coordinate transport along a sequence of paths in
locally finite open corridors.  The successive two-form remainders escape to
infinity, while the locally finite sum of the correction one-forms provides
a global primitive of the initial two-form.
-/

open Set MeasureTheory
open scoped Interval Manifold ContDiff Topology

namespace JJMath.Uniformization

open JJMath.Manifold

noncomputable section

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
variable [IsManifold SurfaceRealModel ∞ X] [T2Space X]

/-- The data carried at one stage of compactly supported transport through
a sequence of open corridors. -/
structure CompactSupportTransportState
    (W : ℕ → TopologicalSpace.Opens X) (x : ℕ → X) (n : ℕ) where
  chartOpen : TopologicalSpace.Opens X
  chartOpen_subset : chartOpen ≤ W n
  point_mem : x n ∈ chartOpen
  planarChart : Nonempty
    (chartOpen ≃ₘ⟮SurfaceRealModel, SurfaceRealModel⟯ complexPlanarModelOpen)
  form : SmoothForms (I := SurfaceRealModel) (M := X) ℝ 2
  core : Set chartOpen
  core_isCompact : IsCompact core
  form_zero_outside :
    ∀ y : X, y ∉ smoothFormCompactCore chartOpen core → form.toFun y = 0

/-- One transport step consists of a correction one-form and the next
compactly supported remainder. -/
structure CompactSupportTransportStep
    (W : ℕ → TopologicalSpace.Opens X) (x : ℕ → X) (n : ℕ)
    (state : CompactSupportTransportState W x n) where
  correction : SmoothForms (I := SurfaceRealModel) (M := X) ℝ 1
  next : CompactSupportTransportState W x (n + 1)
  differential :
    deRhamDifferential (I := SurfaceRealModel) (M := X) (A := ℝ) 1 correction =
      state.form - next.form
  correction_zero_outside :
    ∀ y : X, y ∉ W n → correction.toFun y = 0

/-- A path from one marked point to the next produces one compactly
supported transport step. -/
theorem CompactSupportTransportState.step_nonempty
    (W : ℕ → TopologicalSpace.Opens X) (x : ℕ → X) (n : ℕ)
    (state : CompactSupportTransportState W x n)
    (gamma : Path (x n) (x (n + 1)))
    (hgamma : ∀ t : unitInterval, gamma t ∈ W n)
    (hxnext : x (n + 1) ∈ W (n + 1)) :
    Nonempty (CompactSupportTransportStep W x n state) := by
  classical
  let phi := Classical.choice state.planarChart
  obtain ⟨eta, beta, V, KV, hxV, hVW, hphiV, hKV, hd, heta, hbeta⟩ :=
    exists_compactSupport_transport_along_path
      (W n) (W (n + 1)) state.chartOpen phi gamma hgamma hxnext
      state.point_mem state.chartOpen_subset state.core state.core_isCompact
      state.form state.form_zero_outside
  let nextState : CompactSupportTransportState W x (n + 1) :=
    { chartOpen := V
      chartOpen_subset := hVW.trans inf_le_right
      point_mem := hxV
      planarChart := hphiV
      form := beta
      core := KV
      core_isCompact := hKV
      form_zero_outside := hbeta }
  exact ⟨
    { correction := eta
      next := nextState
      differential := hd
      correction_zero_outside := heta }⟩

/-- Iterating the pathwise transport step yields a telescoping sequence of
two-form remainders and corridor-supported correction one-forms. -/
theorem exists_compactSupport_transport_sequences
    (W : ℕ → TopologicalSpace.Opens X) (x : ℕ → X)
    (gamma : ∀ n : ℕ, Path (x n) (x (n + 1)))
    (hgamma : ∀ n : ℕ, ∀ t : unitInterval, gamma n t ∈ W n)
    (hxnext : ∀ n : ℕ, x (n + 1) ∈ W (n + 1))
    (initial : CompactSupportTransportState W x 0) :
    ∃ (beta : ℕ → SmoothForms (I := SurfaceRealModel) (M := X) ℝ 2)
        (eta : ℕ → SmoothForms (I := SurfaceRealModel) (M := X) ℝ 1),
      beta 0 = initial.form ∧
      (∀ n : ℕ,
        deRhamDifferential (I := SurfaceRealModel) (M := X) (A := ℝ) 1
          (eta n) = beta n - beta (n + 1)) ∧
      (∀ n : ℕ, ∀ y : X, y ∉ W n → (eta n).toFun y = 0) ∧
      (∀ n : ℕ, ∀ y : X, y ∉ W n → (beta n).toFun y = 0) := by
  classical
  let transition : (n : ℕ) →
      (state : CompactSupportTransportState W x n) →
        CompactSupportTransportStep W x n state := fun n state =>
    Classical.choice
      (state.step_nonempty W x n (gamma n) (hgamma n) (hxnext n))
  let states : (n : ℕ) → CompactSupportTransportState W x n := fun n =>
    Nat.rec (motive := CompactSupportTransportState W x)
      initial (fun n state => (transition n state).next) n
  let beta : ℕ → SmoothForms (I := SurfaceRealModel) (M := X) ℝ 2 :=
    fun n => (states n).form
  let eta : ℕ → SmoothForms (I := SurfaceRealModel) (M := X) ℝ 1 :=
    fun n => (transition n (states n)).correction
  refine ⟨beta, eta, ?_, ?_, ?_, ?_⟩
  · rfl
  · intro n
    change deRhamDifferential (I := SurfaceRealModel) (M := X) (A := ℝ) 1
        (transition n (states n)).correction =
      (states n).form - (states (n + 1)).form
    simpa [states] using (transition n (states n)).differential
  · intro n y hy
    exact (transition n (states n)).correction_zero_outside y hy
  · intro n y hy
    apply (states n).form_zero_outside y
    intro hycore
    apply hy
    exact (states n).chartOpen_subset
      (smoothFormCompactCore_subset (states n).chartOpen (states n).core hycore)

omit [IsManifold SurfaceRealModel ∞ X] [T2Space X] in
/-- Vanishing outside a locally finite family of corridors makes the closed
supports of the corresponding forms locally finite. -/
theorem locallyFinite_smoothFormTSupport_of_zero_outside
    (W : ℕ → TopologicalSpace.Opens X)
    (eta : ℕ → SmoothForms (I := SurfaceRealModel) (M := X) ℝ 1)
    (hlocW : LocallyFinite (fun n => closure (W n : Set X)))
    (heta : ∀ n : ℕ, ∀ y : X, y ∉ W n → (eta n).toFun y = 0) :
    LocallyFinite (fun n => smoothFormTSupport SurfaceRealModel (eta n)) := by
  apply hlocW.subset
  intro n
  apply closure_mono
  intro y hy
  by_contra hyW
  exact hy (heta n y hyW)

/-- A locally finite sequence of path corridors transports every compactly
supported initial two-form to infinity and therefore gives it a global
primitive.  The primitive is supported in the union of the corridors. -/
theorem exists_primitive_of_compactSupport_transport_along_paths_with_support
    (W : ℕ → TopologicalSpace.Opens X) (x : ℕ → X)
    (gamma : ∀ n : ℕ, Path (x n) (x (n + 1)))
    (hgamma : ∀ n : ℕ, ∀ t : unitInterval, gamma n t ∈ W n)
    (hxnext : ∀ n : ℕ, x (n + 1) ∈ W (n + 1))
    (hlocW : LocallyFinite (fun n => closure (W n : Set X)))
    (initial : CompactSupportTransportState W x 0) :
    ∃ theta : SmoothForms (I := SurfaceRealModel) (M := X) ℝ 1,
      deRhamDifferential (I := SurfaceRealModel) (M := X) (A := ℝ) 1 theta =
        initial.form ∧
      ∀ y : X, y ∉ ⋃ n : ℕ, (W n : Set X) → theta.toFun y = 0 := by
  obtain ⟨beta, eta, hbeta0, hd, heta, hbetaSupport⟩ :=
    exists_compactSupport_transport_sequences W x gamma hgamma hxnext initial
  have hlocEta :
      LocallyFinite (fun n => smoothFormTSupport SurfaceRealModel (eta n)) :=
    locallyFinite_smoothFormTSupport_of_zero_outside W eta hlocW heta
  have hbetaEventually : ∀ y : X, ∃ N : ℕ, ∀ n ≥ N, (beta n).toFun y = 0 := by
    intro y
    obtain ⟨N, hN⟩ := (hlocW.point_finite y).exists_le
    refine ⟨N + 1, ?_⟩
    intro n hn
    apply hbetaSupport n y
    intro hyW
    have hnClosure : n ∈ {k : ℕ | y ∈ closure (W k : Set X)} :=
      subset_closure hyW
    have hnN : n ≤ N := hN n hnClosure
    omega
  let theta := smoothFormsLocallyFiniteFinsum SurfaceRealModel eta hlocEta
  refine ⟨theta, ?_, ?_⟩
  · rw [show deRhamDifferential
        (I := SurfaceRealModel) (M := X) (A := ℝ) 1 theta =
        smoothFormsLocallyFiniteFinsum SurfaceRealModel
          (fun k ↦ deRhamDifferential
            (I := SurfaceRealModel) (M := X) (A := ℝ) 1 (eta k))
          (hlocEta.subset (fun k ↦ closure_minimal
            (deRhamDifferential_support_subset_tsupport
              SurfaceRealModel (eta k)) isClosed_closure)) by
      exact deRhamDifferential_smoothFormsLocallyFiniteFinsum
        SurfaceRealModel eta hlocEta]
    apply DifferentialForm.ext
    intro y
    rw [smoothFormsLocallyFiniteFinsum_toFun]
    have hpoint : ∀ k : ℕ,
        (deRhamDifferential
          (I := SurfaceRealModel) (M := X) (A := ℝ) 1 (eta k)).toFun y =
          (beta k).toFun y - (beta (k + 1)).toFun y := by
      intro k
      rw [hd]
      rfl
    rw [finsum_congr hpoint]
    rw [finsum_nat_sub_succ_eq_of_eventually_zero
      (fun k ↦ (beta k).toFun y) (hbetaEventually y)]
    exact congrArg (fun form ↦ form.toFun y) hbeta0
  · intro y hy
    change ∑ᶠ n : ℕ, (eta n).toFun y = 0
    apply finsum_eq_zero_of_forall_eq_zero
    intro n
    apply heta n y
    intro hyW
    exact hy (mem_iUnion.mpr ⟨n, hyW⟩)

/-- A locally finite sequence of path corridors transports every compactly
supported initial two-form to infinity and therefore gives it a global
primitive. -/
theorem exists_primitive_of_compactSupport_transport_along_paths
    (W : ℕ → TopologicalSpace.Opens X) (x : ℕ → X)
    (gamma : ∀ n : ℕ, Path (x n) (x (n + 1)))
    (hgamma : ∀ n : ℕ, ∀ t : unitInterval, gamma n t ∈ W n)
    (hxnext : ∀ n : ℕ, x (n + 1) ∈ W (n + 1))
    (hlocW : LocallyFinite (fun n ↦ closure (W n : Set X)))
    (initial : CompactSupportTransportState W x 0) :
    ∃ theta : SmoothForms (I := SurfaceRealModel) (M := X) ℝ 1,
      deRhamDifferential (I := SurfaceRealModel) (M := X) (A := ℝ) 1 theta =
        initial.form := by
  rcases exists_primitive_of_compactSupport_transport_along_paths_with_support
      W x gamma hgamma hxnext hlocW initial with
    ⟨theta, htheta, _hsupport⟩
  exact ⟨theta, htheta⟩

end

end JJMath.Uniformization
