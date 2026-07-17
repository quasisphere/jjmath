import JJMath.Uniformization.HubbardExhaustion
import JJMath.Uniformization.BoundedGreenUniformization
import JJMath.Uniformization.H1ZeroExhaustion

/-!
# Hubbard's exhaustion proof of open-surface uniformization

This file applies the Koebe and normal-family estimates to a connected
exhaustion by zero-cohomology bordered domains.  Each domain is first
uniformized by its Green function.  The centered disk maps are normalized in
the coordinate supplied by the first member, and their conformal radii decide
whether the limiting target is a disk or the complex plane.
-/

open scoped Manifold ContDiff Topology

open Filter Metric Set

noncomputable section

namespace JJMath.Uniformization

open JJMath.Manifold

/--
%%handwave
name:
  Simultaneous pointed disk uniformizations
statement:
  A simultaneous pointed disk uniformization of a pointed exhaustion assigns
  to every exhaustion member a biholomorphism onto the unit disk which sends
  the common base point to the origin.
-/
structure PointedDiskUniformization
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    (E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p) where
  equiv : (n : ℕ) → Biholomorphic (E.domain n).openCarrier Complex.UnitDisc
  base_eq : ∀ n,
    (equiv n).toHomeomorph ⟨p, E.domain_base_mem n⟩ = 0

/--
%%handwave
name:
  Zero-cohomology exhaustion members admit pointed disk maps
statement:
  Every pointed smooth exhaustion of a connected noncompact Riemann surface
  by path-connected domains with vanishing first real de Rham cohomology
  admits simultaneous pointed disk uniformizations.
proof:
  The bounded-domain Green construction gives a bijective holomorphic map
  from each member to the unit disk with the common base point mapped to zero.
  A bijective unbranched holomorphic map is biholomorphic.
-/
theorem PointedH1ZeroSmoothRelativelyCompactExhaustion.has_pointedDiskUniformization
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    (hX : ¬ CompactSpace X)
    (E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p) :
    Nonempty (PointedDiskUniformization E) := by
  rcases E.has_bijective_pointedDiskMaps hX with ⟨F⟩
  refine ⟨{
    equiv := fun n ↦ by
      letI : PathConnectedSpace (E.domain n).carrier := E.pathConnected n
      letI : Nonempty (E.domain n).carrier :=
        ⟨⟨p, E.domain_base_mem n⟩⟩
      letI : RiemannSurface (E.domain n).openCarrier :=
        (E.domain n).openCarrier_riemannSurface
      exact (F n).1.biholomorphicOfBijective (F n).2
    base_eq := ?_ }⟩
  intro n
  letI : PathConnectedSpace (E.domain n).carrier := E.pathConnected n
  letI : Nonempty (E.domain n).carrier :=
    ⟨⟨p, E.domain_base_mem n⟩⟩
  letI : RiemannSurface (E.domain n).openCarrier :=
    (E.domain n).openCarrier_riemannSurface
  exact (F n).1.biholomorphicOfBijective_base (F n).2

/-- The holomorphic transition from the disk uniformizing an earlier member
to the disk uniformizing a later member. -/
noncomputable def PointedDiskUniformization.transition
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    {E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p}
    (P : PointedDiskUniformization E)
    (m n : ℕ) (hmn : m ≤ n) : Complex.UnitDisc → Complex.UnitDisc :=
  (P.equiv n).toHomeomorph ∘
    (TopologicalSpace.Opens.inclusion (E.domain_carrier_mono hmn)) ∘
      (P.equiv m).toHomeomorph.symm

theorem PointedDiskUniformization.transition_holomorphic
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    {E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p}
    (P : PointedDiskUniformization E)
    (m n : ℕ) (hmn : m ≤ n) :
    HolomorphicMap Complex.UnitDisc Complex.UnitDisc (P.transition m n hmn) := by
  have hinc : HolomorphicMap (E.domain m).openCarrier
      (E.domain n).openCarrier
      (TopologicalSpace.Opens.inclusion (E.domain_carrier_mono hmn)) := by
    exact (contMDiff_inclusion (I := 𝓘(ℂ)) (n := (⊤ : WithTop ℕ∞))
      (E.domain_carrier_mono hmn)).mdifferentiable (by simp)
  exact (P.equiv n).holomorphic_toFun.comp
    (hinc.comp (P.equiv m).holomorphic_invFun)

theorem PointedDiskUniformization.transition_zero
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    {E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p}
    (P : PointedDiskUniformization E)
    (m n : ℕ) (hmn : m ≤ n) :
    P.transition m n hmn 0 = 0 := by
  have hm := P.base_eq m
  have hn := P.base_eq n
  have hinv : (P.equiv m).toHomeomorph.symm 0 =
      ⟨p, E.domain_base_mem m⟩ := by
    exact (P.equiv m).toHomeomorph.injective
      (by simpa using hm.symm)
  simp [PointedDiskUniformization.transition, hinv, hn]

/-- The standard complex-coordinate representative of a holomorphic disk
self-map. -/
noncomputable def diskCoordinateRepresentative
    (T : Complex.UnitDisc → Complex.UnitDisc) : ℂ → ℂ :=
  fun z ↦ (T ((chartAt ℂ (0 : Complex.UnitDisc)).symm z) : ℂ)

theorem diskCoordinateRepresentative_analyticOnNhd
    {T : Complex.UnitDisc → Complex.UnitDisc}
    (hT : HolomorphicMap Complex.UnitDisc Complex.UnitDisc T) :
    AnalyticOnNhd ℂ (diskCoordinateRepresentative T) (ball 0 1) := by
  let hOpen : Topology.IsOpenEmbedding
      ((↑) : Complex.UnitDisc → ℂ) :=
    (Metric.isOpen_ball : IsOpen (ball (0 : ℂ) 1)).isOpenEmbedding_subtypeVal
  letI : IsManifold 𝓘(ℂ) ⊤ Complex.UnitDisc :=
    hOpen.isManifold_singleton
  letI : ComplexOneManifold Complex.UnitDisc :=
    { toT2Space := inferInstance
      toIsManifold := inferInstance }
  let χ : PointedSurfaceCoordinate Complex.UnitDisc (0 : Complex.UnitDisc) :=
    { chart := chartAt ℂ (0 : Complex.UnitDisc)
      chart_mem_atlas := chart_mem_atlas ℂ (0 : Complex.UnitDisc)
      base_mem_source := mem_chart_source ℂ (0 : Complex.UnitDisc) }
  have hdiff : DifferentiableOn ℂ (diskCoordinateRepresentative T)
      χ.chart.target := by
    simpa [diskCoordinateRepresentative, χ] using
      differentiableOn_surfaceCoordinate_symm
        (holomorphicMap_unitDisc_coe.comp hT) χ
  have hanalytic := hdiff.analyticOnNhd χ.chart.open_target
  apply hanalytic.mono
  intro z hz
  let zD : Complex.UnitDisc := ⟨z, by simpa using hz⟩
  rw [← χ.chart.image_source_eq_target]
  refine ⟨zD, mem_chart_source ℂ zD, ?_⟩
  have hchart :
      ⇑(chartAt ℂ (0 : Complex.UnitDisc)) =
        ((↑) : Complex.UnitDisc → ℂ) :=
    hOpen.singletonChartedSpace_chartAt_eq
  change (chartAt ℂ (0 : Complex.UnitDisc)) zD = z
  rw [hchart]
  rfl

theorem diskCoordinateRepresentative_zero
    {T : Complex.UnitDisc → Complex.UnitDisc} (hT0 : T 0 = 0) :
    diskCoordinateRepresentative T 0 = 0 := by
  let e := chartAt ℂ (0 : Complex.UnitDisc)
  have htarget : e (0 : Complex.UnitDisc) ∈ e.target :=
    e.map_source (mem_chart_source ℂ (0 : Complex.UnitDisc))
  have hinv : e.symm 0 = (0 : Complex.UnitDisc) := by
    have hleft := e.left_inv (mem_chart_source ℂ (0 : Complex.UnitDisc))
    let hOpen : Topology.IsOpenEmbedding
        ((↑) : Complex.UnitDisc → ℂ) :=
      (Metric.isOpen_ball : IsOpen (ball (0 : ℂ) 1)).isOpenEmbedding_subtypeVal
    have hchart0 : e (0 : Complex.UnitDisc) = 0 := by
      exact congrFun hOpen.singletonChartedSpace_chartAt_eq 0
    rw [hchart0] at hleft
    exact hleft
  change (T ((chartAt ℂ (0 : Complex.UnitDisc)).symm 0) : ℂ) = 0
  rw [hinv, hT0]
  rfl

theorem diskCoordinateRepresentative_apply_of_mem
    (T : Complex.UnitDisc → Complex.UnitDisc)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    diskCoordinateRepresentative T z = T ⟨z, hz⟩ := by
  let e := chartAt ℂ (0 : Complex.UnitDisc)
  let zD : Complex.UnitDisc := ⟨z, hz⟩
  let hOpen : Topology.IsOpenEmbedding
      ((↑) : Complex.UnitDisc → ℂ) :=
    (Metric.isOpen_ball : IsOpen (ball (0 : ℂ) 1)).isOpenEmbedding_subtypeVal
  have hchart : e zD = z := by
    have heq : ⇑e = ((↑) : Complex.UnitDisc → ℂ) :=
      hOpen.singletonChartedSpace_chartAt_eq
    change e zD = z
    rw [heq]
    rfl
  have hinv : e.symm z = zD := by
    have hleft := e.left_inv (mem_chart_source ℂ zD)
    rw [hchart] at hleft
    exact hleft
  change (T (e.symm z) : ℂ) = (T zD : ℂ)
  rw [hinv]

/-- On its unit-ball target, the inverse of the standard disk chart is the
obvious subtype constructor. -/
theorem unitDisc_chartAt_symm_apply_of_mem
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    (chartAt ℂ (0 : Complex.UnitDisc)).symm z =
      (⟨z, hz⟩ : Complex.UnitDisc) := by
  let e := chartAt ℂ (0 : Complex.UnitDisc)
  let zD : Complex.UnitDisc := ⟨z, hz⟩
  let hOpen : Topology.IsOpenEmbedding
      ((↑) : Complex.UnitDisc → ℂ) :=
    (Metric.isOpen_ball : IsOpen (ball (0 : ℂ) 1)).isOpenEmbedding_subtypeVal
  have hchart : e zD = z := by
    have heq : ⇑e = ((↑) : Complex.UnitDisc → ℂ) :=
      hOpen.singletonChartedSpace_chartAt_eq
    change e zD = z
    rw [heq]
    rfl
  have hleft := e.left_inv (mem_chart_source ℂ zD)
  rw [hchart] at hleft
  exact hleft

theorem PointedDiskUniformization.transition_injective
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    {E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p}
    (P : PointedDiskUniformization E)
    (m n : ℕ) (hmn : m ≤ n) :
    Function.Injective (P.transition m n hmn) := by
  intro z w hzw
  apply (P.equiv m).toHomeomorph.symm.injective
  apply Subtype.ext
  have hinc := (P.equiv n).toHomeomorph.injective hzw
  have hincVal := congrArg
    (fun q : (E.domain n).openCarrier ↦ (q : X)) hinc
  simpa [PointedDiskUniformization.transition, Function.comp_def] using hincVal

/-- The derivative, in the standard disk coordinate, of the transition from
the first exhaustion member to the `n`-th member. -/
noncomputable def PointedDiskUniformization.coefficient
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    {E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p}
    (P : PointedDiskUniformization E) (n : ℕ) : ℂ :=
  deriv (diskCoordinateRepresentative (P.transition 0 n (Nat.zero_le n))) 0

theorem PointedDiskUniformization.coefficient_ne_zero
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    {E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p}
    (P : PointedDiskUniformization E) (n : ℕ) :
    P.coefficient n ≠ 0 := by
  let T := P.transition 0 n (Nat.zero_le n)
  have hT := P.transition_holomorphic 0 n (Nat.zero_le n)
  have hA := diskCoordinateRepresentative_analyticOnNhd hT
  have hI : InjOn (diskCoordinateRepresentative T) (ball (0 : ℂ) 1) := by
    intro z hz w hw hzw
    have hzw' : T ⟨z, hz⟩ = T ⟨w, hw⟩ := by
      apply Subtype.ext
      change (T ⟨z, hz⟩ : ℂ) = (T ⟨w, hw⟩ : ℂ)
      rw [← diskCoordinateRepresentative_apply_of_mem T hz,
        ← diskCoordinateRepresentative_apply_of_mem T hw]
      exact hzw
    have := P.transition_injective 0 n (Nat.zero_le n) hzw'
    exact congrArg Subtype.val this
  exact analyticOnNhd_deriv_ne_zero_of_injOn hA hI
    (mem_ball_self zero_lt_one)

/-- The conformal radius associated with the normalized map on the `n`-th
exhaustion member. -/
noncomputable def PointedDiskUniformization.radius
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    {E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p}
    (P : PointedDiskUniformization E) (n : ℕ) : ℝ :=
  ‖P.coefficient n‖⁻¹

theorem PointedDiskUniformization.radius_pos
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    {E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p}
    (P : PointedDiskUniformization E) (n : ℕ) :
    0 < P.radius n := by
  exact inv_pos.mpr (norm_pos_iff.mpr (P.coefficient_ne_zero n))

/-- The disk uniformization divided by its derivative in the initial disk
coordinate, extended set-theoretically by zero outside its member. -/
noncomputable def PointedDiskUniformization.normalizedMap
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    {E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p}
    (P : PointedDiskUniformization E) (n : ℕ) : X → ℂ :=
  Subtype.val.extend
    (fun x : (E.domain n).openCarrier ↦
      ((P.equiv n).toHomeomorph x : ℂ) / P.coefficient n) 0

@[simp]
theorem PointedDiskUniformization.normalizedMap_apply_of_mem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    {E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p}
    (P : PointedDiskUniformization E) (n : ℕ) {x : X}
    (hx : x ∈ (E.domain n).carrier) :
    P.normalizedMap n x =
      ((P.equiv n).toHomeomorph ⟨x, hx⟩ : ℂ) / P.coefficient n := by
  exact Subtype.val_injective.extend_apply _ _ ⟨x, hx⟩

/-- The point of the surface whose coordinate in the first exhaustion disk
is `z`; only its restriction to the unit disk is used. -/
noncomputable def PointedDiskUniformization.initialDiskParameter
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    {E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p}
    (P : PointedDiskUniformization E) (z : ℂ) : X :=
  ((P.equiv 0).toHomeomorph.symm
    ((chartAt ℂ (0 : Complex.UnitDisc)).symm z) :
      (E.domain 0).openCarrier)

/-- In the initial disk coordinate, the normalized map on the `n`-th member
is the transition map divided by its derivative at the origin. -/
noncomputable def PointedDiskUniformization.initialCoordinateMap
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    {E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p}
    (P : PointedDiskUniformization E) (n : ℕ) (z : ℂ) : ℂ :=
  diskCoordinateRepresentative
      (P.transition 0 n (Nat.zero_le n)) z / P.coefficient n

theorem PointedDiskUniformization.initialCoordinateMap_analyticOnNhd
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    {E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p}
    (P : PointedDiskUniformization E) (n : ℕ) :
    AnalyticOnNhd ℂ (P.initialCoordinateMap n) (ball 0 1) := by
  exact (diskCoordinateRepresentative_analyticOnNhd
    (P.transition_holomorphic 0 n (Nat.zero_le n))).div
      analyticOnNhd_const (fun _ _ ↦ P.coefficient_ne_zero n)

theorem PointedDiskUniformization.initialCoordinateMap_deriv_zero
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    {E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p}
    (P : PointedDiskUniformization E) (n : ℕ) :
    deriv (P.initialCoordinateMap n) 0 = 1 := by
  let A := diskCoordinateRepresentative
    (P.transition 0 n (Nat.zero_le n))
  have hA : HasDerivAt A (P.coefficient n) 0 := by
    exact (diskCoordinateRepresentative_analyticOnNhd
      (P.transition_holomorphic 0 n (Nat.zero_le n))
        0 (mem_ball_self zero_lt_one)).differentiableAt.hasDerivAt
  have hdiv := hA.div_const (P.coefficient n)
  change deriv (fun z ↦ A z / P.coefficient n) 0 = 1
  rw [hdiv.deriv]
  exact div_self (P.coefficient_ne_zero n)

theorem PointedDiskUniformization.initialDiskParameter_continuousOn
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    {E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p}
    (P : PointedDiskUniformization E) :
    ContinuousOn P.initialDiskParameter (ball (0 : ℂ) 1) := by
  let e := chartAt ℂ (0 : Complex.UnitDisc)
  have htarget : ball (0 : ℂ) 1 ⊆ e.target := by
    intro z hz
    let zD : Complex.UnitDisc := ⟨z, hz⟩
    rw [← e.image_source_eq_target]
    refine ⟨zD, mem_chart_source ℂ zD, ?_⟩
    let hOpen : Topology.IsOpenEmbedding
        ((↑) : Complex.UnitDisc → ℂ) :=
      (Metric.isOpen_ball : IsOpen (ball (0 : ℂ) 1)).isOpenEmbedding_subtypeVal
    change e zD = z
    rw [hOpen.singletonChartedSpace_chartAt_eq]
    rfl
  have houter : Continuous
      (fun y : Complex.UnitDisc ↦
        ((P.equiv 0).toHomeomorph.symm y : X)) :=
    continuous_subtype_val.comp (P.equiv 0).toHomeomorph.symm.continuous
  simpa [PointedDiskUniformization.initialDiskParameter, e,
    Function.comp_def] using
      houter.comp_continuousOn (e.symm.continuousOn.mono htarget)

theorem PointedDiskUniformization.normalizedMap_initialDiskParameter
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    {E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p}
    (P : PointedDiskUniformization E) (n : ℕ)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    P.normalizedMap n (P.initialDiskParameter z) =
      P.initialCoordinateMap n z := by
  let zD : Complex.UnitDisc := ⟨z, hz⟩
  let x₀ : (E.domain 0).openCarrier :=
    (P.equiv 0).toHomeomorph.symm zD
  have hx₀ : (x₀ : X) = P.initialDiskParameter z := by
    change ((P.equiv 0).toHomeomorph.symm zD : X) =
      ((P.equiv 0).toHomeomorph.symm
        ((chartAt ℂ (0 : Complex.UnitDisc)).symm z) : X)
    rw [unitDisc_chartAt_symm_apply_of_mem hz]
  have hxn : P.initialDiskParameter z ∈ (E.domain n).carrier := by
    rw [← hx₀]
    exact E.domain_carrier_mono (Nat.zero_le n) x₀.2
  rw [P.normalizedMap_apply_of_mem n hxn]
  change (((P.equiv n).toHomeomorph
      ⟨P.initialDiskParameter z, hxn⟩ : Complex.UnitDisc) : ℂ) /
        P.coefficient n = _
  have heq : (P.equiv n).toHomeomorph
      ⟨P.initialDiskParameter z, hxn⟩ =
        P.transition 0 n (Nat.zero_le n) zD := by
    change (P.equiv n).toHomeomorph ⟨P.initialDiskParameter z, hxn⟩ =
      (P.equiv n).toHomeomorph
        (TopologicalSpace.Opens.inclusion
          (E.domain_carrier_mono (Nat.zero_le n))
            ((P.equiv 0).toHomeomorph.symm zD))
    congr 1
    exact Subtype.ext hx₀.symm
  rw [heq]
  change ((P.transition 0 n (Nat.zero_le n) zD : Complex.UnitDisc) : ℂ) /
      P.coefficient n = _
  rw [← diskCoordinateRepresentative_apply_of_mem _ hz]
  rfl

theorem PointedDiskUniformization.transition_comp
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    {E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p}
    (P : PointedDiskUniformization E)
    (m n : ℕ) (hmn : m ≤ n) :
    P.transition 0 n (Nat.zero_le n) =
      P.transition m n hmn ∘ P.transition 0 m (Nat.zero_le m) := by
  funext z
  simp [PointedDiskUniformization.transition, Function.comp_def]

theorem diskCoordinateRepresentative_comp_eqOn
    (T S : Complex.UnitDisc → Complex.UnitDisc) :
    EqOn (diskCoordinateRepresentative (T ∘ S))
      (diskCoordinateRepresentative T ∘ diskCoordinateRepresentative S)
      (ball (0 : ℂ) 1) := by
  intro z hz
  have hS : (S ⟨z, hz⟩ : ℂ) ∈ ball (0 : ℂ) 1 :=
    (S ⟨z, hz⟩).property
  rw [diskCoordinateRepresentative_apply_of_mem (T ∘ S) hz]
  simp only [Function.comp_apply]
  change ((T (S ⟨z, hz⟩) : Complex.UnitDisc) : ℂ) =
    diskCoordinateRepresentative T (diskCoordinateRepresentative S z)
  rw [diskCoordinateRepresentative_apply_of_mem S hz]
  rw [diskCoordinateRepresentative_apply_of_mem T hS]
  rfl

theorem PointedDiskUniformization.coefficient_eq_transition_deriv_mul
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    {E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p}
    (P : PointedDiskUniformization E)
    (m n : ℕ) (hmn : m ≤ n) :
    P.coefficient n =
      deriv (diskCoordinateRepresentative (P.transition m n hmn)) 0 *
        P.coefficient m := by
  let A := diskCoordinateRepresentative (P.transition 0 m (Nat.zero_le m))
  let B := diskCoordinateRepresentative (P.transition m n hmn)
  let C := diskCoordinateRepresentative (P.transition 0 n (Nat.zero_le n))
  have hA := diskCoordinateRepresentative_analyticOnNhd
    (P.transition_holomorphic 0 m (Nat.zero_le m))
  have hB := diskCoordinateRepresentative_analyticOnNhd
    (P.transition_holomorphic m n hmn)
  have hA0 : A 0 = 0 := by
    exact diskCoordinateRepresentative_zero
      (P.transition_zero 0 m (Nat.zero_le m))
  have heqOn : EqOn C (B ∘ A) (ball (0 : ℂ) 1) := by
    intro z hz
    dsimp [A, B, C]
    rw [show P.transition 0 n (Nat.zero_le n) =
      P.transition m n hmn ∘ P.transition 0 m (Nat.zero_le m) from
        P.transition_comp m n hmn]
    exact diskCoordinateRepresentative_comp_eqOn _ _ hz
  have heq : C =ᶠ[𝓝 (0 : ℂ)] B ∘ A := by
    filter_upwards [ball_mem_nhds (0 : ℂ) zero_lt_one] with z hz
    exact heqOn hz
  change deriv C 0 = deriv B 0 * deriv A 0
  rw [heq.deriv_eq]
  have hBAt : HasDerivAt B (deriv B 0) (A 0) := by
    simpa [hA0] using
      (hB 0 (mem_ball_self zero_lt_one)).differentiableAt.hasDerivAt
  have hcomp := hBAt.comp 0
    (hA 0 (mem_ball_self zero_lt_one)).differentiableAt.hasDerivAt
  exact hcomp.deriv

/-- The transition between normalized disks. -/
noncomputable def PointedDiskUniformization.normalizedTransition
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    {E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p}
    (P : PointedDiskUniformization E)
    (m n : ℕ) (hmn : m ≤ n) : ℂ → ℂ :=
  fun z ↦
    diskCoordinateRepresentative (P.transition m n hmn)
        (P.coefficient m * z) / P.coefficient n

theorem PointedDiskUniformization.normalizedTransition_analyticOnNhd
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    {E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p}
    (P : PointedDiskUniformization E)
    (m n : ℕ) (hmn : m ≤ n) :
    AnalyticOnNhd ℂ (P.normalizedTransition m n hmn)
      (ball 0 (P.radius m)) := by
  let c := P.coefficient m
  have hc : c ≠ 0 := P.coefficient_ne_zero m
  have hinner : AnalyticOnNhd ℂ (fun z : ℂ ↦ c * z)
      (ball 0 (P.radius m)) :=
    analyticOnNhd_const.mul analyticOnNhd_id
  have hmaps : MapsTo (fun z : ℂ ↦ c * z)
      (ball 0 (P.radius m)) (ball (0 : ℂ) 1) := by
    intro z hz
    rw [mem_ball_zero_iff] at hz ⊢
    rw [norm_mul]
    have hcNorm : 0 < ‖c‖ := norm_pos_iff.mpr hc
    change ‖z‖ < ‖c‖⁻¹ at hz
    calc
      ‖c‖ * ‖z‖ < ‖c‖ * ‖c‖⁻¹ := mul_lt_mul_of_pos_left hz hcNorm
      _ = 1 := mul_inv_cancel₀ (norm_ne_zero_iff.mpr hc)
  have hcomp :=
    (diskCoordinateRepresentative_analyticOnNhd
      (P.transition_holomorphic m n hmn)).comp hinner hmaps
  exact hcomp.div analyticOnNhd_const
    (fun _ _ ↦ P.coefficient_ne_zero n)

theorem PointedDiskUniformization.normalizedTransition_zero
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    {E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p}
    (P : PointedDiskUniformization E)
    (m n : ℕ) (hmn : m ≤ n) :
    P.normalizedTransition m n hmn 0 = 0 := by
  simp [PointedDiskUniformization.normalizedTransition,
    diskCoordinateRepresentative_zero (P.transition_zero m n hmn)]

theorem PointedDiskUniformization.normalizedTransition_deriv_zero
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    {E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p}
    (P : PointedDiskUniformization E)
    (m n : ℕ) (hmn : m ≤ n) :
    deriv (P.normalizedTransition m n hmn) 0 = 1 := by
  let B := diskCoordinateRepresentative (P.transition m n hmn)
  let cm := P.coefficient m
  let cn := P.coefficient n
  have hB := diskCoordinateRepresentative_analyticOnNhd
    (P.transition_holomorphic m n hmn)
  have hinner : HasDerivAt (fun z : ℂ ↦ cm * z) cm 0 := by
    convert (hasDerivAt_const 0 cm).mul (hasDerivAt_id 0) using 1 <;> simp
  have hcomp : HasDerivAt (fun z : ℂ ↦ B (cm * z))
      (deriv B 0 * cm) 0 := by
    have hB0 : HasDerivAt B (deriv B 0) (cm * 0) := by
      simpa using
        (hB 0 (mem_ball_self zero_lt_one)).differentiableAt.hasDerivAt
    simpa [Function.comp_def] using hB0.comp 0 hinner
  have hdiv := hcomp.div_const cn
  change deriv (fun z : ℂ ↦ B (cm * z) / cn) 0 = 1
  rw [hdiv.deriv]
  rw [← P.coefficient_eq_transition_deriv_mul m n hmn]
  exact div_self (P.coefficient_ne_zero n)

theorem PointedDiskUniformization.normalizedTransition_injOn
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    {E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p}
    (P : PointedDiskUniformization E)
    (m n : ℕ) (hmn : m ≤ n) :
    InjOn (P.normalizedTransition m n hmn) (ball 0 (P.radius m)) := by
  intro z hz w hw hzw
  let cm := P.coefficient m
  let cn := P.coefficient n
  have hcm : cm ≠ 0 := P.coefficient_ne_zero m
  have hcn : cn ≠ 0 := P.coefficient_ne_zero n
  have hcmz : cm * z ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff] at hz ⊢
    rw [norm_mul]
    have hpos : 0 < ‖cm‖ := norm_pos_iff.mpr hcm
    change ‖z‖ < ‖cm‖⁻¹ at hz
    calc
      ‖cm‖ * ‖z‖ < ‖cm‖ * ‖cm‖⁻¹ := mul_lt_mul_of_pos_left hz hpos
      _ = 1 := mul_inv_cancel₀ (norm_ne_zero_iff.mpr hcm)
  have hcmw : cm * w ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff] at hw ⊢
    rw [norm_mul]
    have hpos : 0 < ‖cm‖ := norm_pos_iff.mpr hcm
    change ‖w‖ < ‖cm‖⁻¹ at hw
    calc
      ‖cm‖ * ‖w‖ < ‖cm‖ * ‖cm‖⁻¹ := mul_lt_mul_of_pos_left hw hpos
      _ = 1 := mul_inv_cancel₀ (norm_ne_zero_iff.mpr hcm)
  have hrep :
      diskCoordinateRepresentative (P.transition m n hmn) (cm * z) =
        diskCoordinateRepresentative (P.transition m n hmn) (cm * w) := by
    dsimp [PointedDiskUniformization.normalizedTransition, cm, cn] at hzw
    have hmul := (div_eq_div_iff hcn hcn).mp hzw
    exact mul_right_cancel₀ hcn hmul
  have htrans : P.transition m n hmn ⟨cm * z, hcmz⟩ =
      P.transition m n hmn ⟨cm * w, hcmw⟩ := by
    apply Subtype.ext
    calc
      (P.transition m n hmn ⟨cm * z, hcmz⟩ : ℂ) =
          diskCoordinateRepresentative (P.transition m n hmn) (cm * z) :=
        (diskCoordinateRepresentative_apply_of_mem _ hcmz).symm
      _ = diskCoordinateRepresentative (P.transition m n hmn) (cm * w) := hrep
      _ = (P.transition m n hmn ⟨cm * w, hcmw⟩ : ℂ) :=
        diskCoordinateRepresentative_apply_of_mem _ hcmw
  have harg := P.transition_injective m n hmn htrans
  have hmul : cm * z = cm * w := congrArg Subtype.val harg
  exact mul_left_cancel₀ hcm hmul

theorem PointedDiskUniformization.normalizedTransition_mapsTo
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    {E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p}
    (P : PointedDiskUniformization E)
    (m n : ℕ) (hmn : m ≤ n) :
    MapsTo (P.normalizedTransition m n hmn)
      (ball 0 (P.radius m)) (ball 0 (P.radius n)) := by
  intro z hz
  let cm := P.coefficient m
  let cn := P.coefficient n
  have hcm : cm ≠ 0 := P.coefficient_ne_zero m
  have hcn : cn ≠ 0 := P.coefficient_ne_zero n
  have hcmz : cm * z ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff] at hz ⊢
    rw [norm_mul]
    have hpos : 0 < ‖cm‖ := norm_pos_iff.mpr hcm
    change ‖z‖ < ‖cm‖⁻¹ at hz
    calc
      ‖cm‖ * ‖z‖ < ‖cm‖ * ‖cm‖⁻¹ := mul_lt_mul_of_pos_left hz hpos
      _ = 1 := mul_inv_cancel₀ (norm_ne_zero_iff.mpr hcm)
  rw [mem_ball_zero_iff]
  rw [PointedDiskUniformization.normalizedTransition]
  rw [diskCoordinateRepresentative_apply_of_mem _ hcmz]
  rw [norm_div]
  have hcnPos : 0 < ‖cn‖ := norm_pos_iff.mpr hcn
  calc
    ‖((P.transition m n hmn ⟨cm * z, hcmz⟩ : Complex.UnitDisc) : ℂ)‖ / ‖cn‖
        < 1 / ‖cn‖ :=
      (div_lt_div_iff_of_pos_right hcnPos).2
        (Complex.UnitDisc.norm_lt_one _)
    _ = P.radius n := by
      change 1 / ‖cn‖ = ‖cn‖⁻¹
      exact one_div _

/--
%%handwave
name:
  Monotonicity of conformal radii
statement:
  After normalizing the disk maps to fix the origin and have derivative one,
  the conformal radii of an increasing pointed exhaustion form a monotone
  sequence.
proof:
  The transition from an earlier normalized disk to a later one fixes zero
  and has derivative one.  Schwarz's lemma says that its source radius cannot
  exceed its target radius.
-/
theorem PointedDiskUniformization.radius_mono
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    {E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p}
    (P : PointedDiskUniformization E) : Monotone P.radius := by
  intro m n hmn
  exact normalized_transition_source_radius_le_target_radius
    (P.radius_pos m)
    (P.normalizedTransition_analyticOnNhd m n hmn)
    (P.normalizedTransition_mapsTo m n hmn)
    (P.normalizedTransition_zero m n hmn)
    (P.normalizedTransition_deriv_zero m n hmn)

/-- A normalized transition rescaled in both source and target to the unit
disk. -/
noncomputable def PointedDiskUniformization.unitTransition
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    {E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p}
    (P : PointedDiskUniformization E)
    (m n : ℕ) (hmn : m ≤ n) (z : ℂ) : ℂ :=
  P.normalizedTransition m n hmn ((P.radius m : ℂ) * z) /
    (P.radius n : ℂ)

theorem PointedDiskUniformization.unitTransition_analyticOnNhd
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    {E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p}
    (P : PointedDiskUniformization E)
    (m n : ℕ) (hmn : m ≤ n) :
    AnalyticOnNhd ℂ (P.unitTransition m n hmn) (ball 0 1) := by
  have hinner : AnalyticOnNhd ℂ
      (fun z : ℂ ↦ (P.radius m : ℂ) * z) (ball 0 1) :=
    analyticOnNhd_const.mul analyticOnNhd_id
  have hmaps : MapsTo (fun z : ℂ ↦ (P.radius m : ℂ) * z)
      (ball 0 1) (ball (0 : ℂ) (P.radius m)) := by
    intro z hz
    rw [mem_ball_zero_iff] at hz ⊢
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (P.radius_pos m)]
    simpa using mul_lt_mul_of_pos_left hz (P.radius_pos m)
  exact ((P.normalizedTransition_analyticOnNhd m n hmn).comp hinner hmaps).div
    analyticOnNhd_const
      (fun _ _ ↦ by exact_mod_cast (P.radius_pos n).ne')

theorem PointedDiskUniformization.unitTransition_injOn
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    {E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p}
    (P : PointedDiskUniformization E)
    (m n : ℕ) (hmn : m ≤ n) :
    InjOn (P.unitTransition m n hmn) (ball 0 1) := by
  intro z hz w hw hzw
  have hrm : (P.radius m : ℂ) ≠ 0 := by
    exact_mod_cast (P.radius_pos m).ne'
  have hrn : (P.radius n : ℂ) ≠ 0 := by
    exact_mod_cast (P.radius_pos n).ne'
  have hzm : (P.radius m : ℂ) * z ∈ ball (0 : ℂ) (P.radius m) := by
    rw [mem_ball_zero_iff] at hz ⊢
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (P.radius_pos m)]
    simpa using mul_lt_mul_of_pos_left hz (P.radius_pos m)
  have hwm : (P.radius m : ℂ) * w ∈ ball (0 : ℂ) (P.radius m) := by
    rw [mem_ball_zero_iff] at hw ⊢
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (P.radius_pos m)]
    simpa using mul_lt_mul_of_pos_left hw (P.radius_pos m)
  have hS : P.normalizedTransition m n hmn ((P.radius m : ℂ) * z) =
      P.normalizedTransition m n hmn ((P.radius m : ℂ) * w) := by
    exact mul_right_cancel₀ hrn ((div_eq_div_iff hrn hrn).mp hzw)
  exact mul_left_cancel₀ hrm
    ((P.normalizedTransition_injOn m n hmn) hzm hwm hS)

theorem PointedDiskUniformization.unitTransition_mapsTo
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    {E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p}
    (P : PointedDiskUniformization E)
    (m n : ℕ) (hmn : m ≤ n) :
    MapsTo (P.unitTransition m n hmn) (ball 0 1) (ball 0 1) := by
  intro z hz
  have hzm : (P.radius m : ℂ) * z ∈ ball (0 : ℂ) (P.radius m) := by
    rw [mem_ball_zero_iff] at hz ⊢
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (P.radius_pos m)]
    simpa using mul_lt_mul_of_pos_left hz (P.radius_pos m)
  have hS := P.normalizedTransition_mapsTo m n hmn hzm
  rw [mem_ball_zero_iff] at hS ⊢
  rw [PointedDiskUniformization.unitTransition, norm_div,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (P.radius_pos n)]
  exact (div_lt_iff₀ (P.radius_pos n)).2 (by simpa using hS)

theorem PointedDiskUniformization.unitTransition_zero
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    {E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p}
    (P : PointedDiskUniformization E)
    (m n : ℕ) (hmn : m ≤ n) :
    P.unitTransition m n hmn 0 = 0 := by
  simp [PointedDiskUniformization.unitTransition,
    P.normalizedTransition_zero m n hmn]

theorem PointedDiskUniformization.unitTransition_deriv_zero
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    {E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p}
    (P : PointedDiskUniformization E)
    (m n : ℕ) (hmn : m ≤ n) :
    deriv (P.unitTransition m n hmn) 0 =
      ((P.radius m / P.radius n : ℝ) : ℂ) := by
  have hS : HasDerivAt (P.normalizedTransition m n hmn) 1 0 := by
    simpa [P.normalizedTransition_deriv_zero m n hmn] using
      ((P.normalizedTransition_analyticOnNhd m n hmn)
        0 (mem_ball_self (P.radius_pos m))).differentiableAt.hasDerivAt
  have hinner : HasDerivAt
      (fun z : ℂ ↦ (P.radius m : ℂ) * z) (P.radius m : ℂ) 0 := by
    convert (hasDerivAt_const 0 (P.radius m : ℂ)).mul
      (hasDerivAt_id 0) using 1 <;> simp
  have hS' : HasDerivAt (P.normalizedTransition m n hmn) 1
      ((P.radius m : ℂ) * 0) := by
    simpa using hS
  have hraw := (hS'.comp 0 hinner).div_const (P.radius n : ℂ)
  convert hraw.deriv using 1;
    simp

theorem PointedDiskUniformization.normalizedTransition_compat
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    {E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p}
    (P : PointedDiskUniformization E)
    (m n : ℕ) (hmn : m ≤ n) {x : X}
    (hx : x ∈ (E.domain m).carrier) :
    P.normalizedTransition m n hmn (P.normalizedMap m x) =
      P.normalizedMap n x := by
  let cm := P.coefficient m
  have hcm : cm ≠ 0 := P.coefficient_ne_zero m
  have hxn : x ∈ (E.domain n).carrier := E.domain_carrier_mono hmn hx
  let zm : Complex.UnitDisc := (P.equiv m).toHomeomorph ⟨x, hx⟩
  have hzm : (zm : ℂ) ∈ ball (0 : ℂ) 1 := zm.property
  rw [P.normalizedMap_apply_of_mem m hx,
    P.normalizedMap_apply_of_mem n hxn]
  rw [PointedDiskUniformization.normalizedTransition]
  have harg : P.coefficient m *
      (((P.equiv m).toHomeomorph ⟨x, hx⟩ : ℂ) / P.coefficient m) =
        (zm : ℂ) := by
    have harg' : cm * ((zm : ℂ) / cm) = (zm : ℂ) := by
      field_simp [hcm]
    simpa [cm, zm] using harg'
  rw [harg]
  rw [diskCoordinateRepresentative_apply_of_mem _ hzm]
  have hzSubtype : (⟨(zm : ℂ), hzm⟩ : Complex.UnitDisc) = zm := by
    ext
    rfl
  have hinv : (P.equiv m).toHomeomorph.symm
      ⟨(zm : ℂ), hzm⟩ = ⟨x, hx⟩ := by
    rw [hzSubtype]
    exact (P.equiv m).toHomeomorph.symm_apply_apply ⟨x, hx⟩
  rw [PointedDiskUniformization.transition, Function.comp_apply,
    Function.comp_apply, hinv]

theorem PointedDiskUniformization.normalizedMap_image
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    {E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p}
    (P : PointedDiskUniformization E) (n : ℕ) :
    P.normalizedMap n '' (E.domain n).carrier = ball 0 (P.radius n) := by
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [P.normalizedMap_apply_of_mem n hx, mem_ball_zero_iff, norm_div]
    have hcPos : 0 < ‖P.coefficient n‖ :=
      norm_pos_iff.mpr (P.coefficient_ne_zero n)
    calc
      ‖((P.equiv n).toHomeomorph ⟨x, hx⟩ : ℂ)‖ / ‖P.coefficient n‖
          < 1 / ‖P.coefficient n‖ :=
        (div_lt_div_iff_of_pos_right hcPos).2
          (Complex.UnitDisc.norm_lt_one _)
      _ = P.radius n := by
        change 1 / ‖P.coefficient n‖ = ‖P.coefficient n‖⁻¹
        exact one_div _
  · intro hw
    have hc : P.coefficient n ≠ 0 := P.coefficient_ne_zero n
    have hcw : P.coefficient n * w ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff] at hw ⊢
      rw [norm_mul]
      have hcPos : 0 < ‖P.coefficient n‖ := norm_pos_iff.mpr hc
      change ‖w‖ < ‖P.coefficient n‖⁻¹ at hw
      calc
        ‖P.coefficient n‖ * ‖w‖ <
            ‖P.coefficient n‖ * ‖P.coefficient n‖⁻¹ :=
          mul_lt_mul_of_pos_left hw hcPos
        _ = 1 := mul_inv_cancel₀ (norm_ne_zero_iff.mpr hc)
    let z : Complex.UnitDisc := ⟨P.coefficient n * w, hcw⟩
    let x : (E.domain n).openCarrier := (P.equiv n).toHomeomorph.symm z
    refine ⟨(x : X), x.2, ?_⟩
    rw [P.normalizedMap_apply_of_mem n x.2]
    have hex : (P.equiv n).toHomeomorph x = z :=
      (P.equiv n).toHomeomorph.apply_symm_apply z
    rw [hex]
    change (P.coefficient n * w) / P.coefficient n = w
    field_simp [hc]

/-- Each normalized map is injective on the exhaustion member on which it is
holomorphic. -/
theorem PointedDiskUniformization.normalizedMap_injOn
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    {E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p}
    (P : PointedDiskUniformization E) (n : ℕ) :
    InjOn (P.normalizedMap n) (E.domain n).carrier := by
  intro x hx y hy hxy
  rw [P.normalizedMap_apply_of_mem n hx,
    P.normalizedMap_apply_of_mem n hy] at hxy
  have hc := P.coefficient_ne_zero n
  have heq : (P.equiv n).toHomeomorph ⟨x, hx⟩ =
      (P.equiv n).toHomeomorph ⟨y, hy⟩ := by
    apply Subtype.ext
    have hmul := (div_eq_div_iff hc hc).mp hxy
    exact mul_right_cancel₀ hc hmul
  exact congrArg Subtype.val ((P.equiv n).toHomeomorph.injective heq)

@[simp]
theorem PointedDiskUniformization.normalizedMap_base
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    {E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p}
    (P : PointedDiskUniformization E) (n : ℕ) :
    P.normalizedMap n p = 0 := by
  rw [P.normalizedMap_apply_of_mem n (E.domain_base_mem n), P.base_eq n]
  simp

theorem PointedDiskUniformization.normalizedMap_mdifferentiableOn
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    {E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p}
    (P : PointedDiskUniformization E) (n : ℕ) :
    MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (P.normalizedMap n)
      (E.domain n).carrier := by
  let U : TopologicalSpace.Opens X := (E.domain n).openCarrier
  let g : U → ℂ := fun x ↦
    ((P.equiv n).toHomeomorph x : ℂ) / P.coefficient n
  have hcoe : HolomorphicMap U ℂ
      (fun x ↦ ((P.equiv n).toHomeomorph x : ℂ)) :=
    holomorphicMap_unitDisc_coe.comp (P.equiv n).holomorphic_toFun
  have hscale : HolomorphicMap ℂ ℂ (fun z ↦ z / P.coefficient n) := by
    exact (show Differentiable ℂ (fun z : ℂ ↦ z / P.coefficient n) by
      fun_prop).mdifferentiable
  have hg : HolomorphicMap U ℂ g := by
    exact hscale.comp hcoe
  intro x hx
  apply MDifferentiableAt.mdifferentiableWithinAt
  have heq : (fun y : U ↦ P.normalizedMap n y) = g := by
    funext y
    exact P.normalizedMap_apply_of_mem n y.2
  have hrestrict : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)
      (fun y : U ↦ P.normalizedMap n y) ⟨x, hx⟩ := by
    rw [heq]
    exact hg ⟨x, hx⟩
  exact ((differentiableWithinAt_localInvariantProp
    (I := 𝓘(ℂ)) (I' := 𝓘(ℂ))).liftPropAt_iff_comp_subtype_val
      (U := U) (P.normalizedMap n) (⟨x, hx⟩ : U)).mpr
        (by simpa [Function.comp_def] using hrestrict)

/-- A compactly contained earlier exhaustion member occupies only a fixed
fraction of the normalized disk of the next member. -/
theorem PointedDiskUniformization.exists_core_fraction_bound
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    {E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p}
    (P : PointedDiskUniformization E) (j : ℕ) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧
      ∀ x ∈ (E.domain j).carrier,
        ‖P.normalizedMap (j + 1) x‖ ≤ ρ * P.radius (j + 1) := by
  let k := j + 1
  let c := P.coefficient k
  let q : X → ℝ := fun x ↦ ‖c * P.normalizedMap k x‖
  have hclosure : closure (E.domain j).carrier ⊆ (E.domain k).carrier := by
    simpa [k] using
      E.toSmoothRelativelyCompactExhaustion.closure_subset_next j
  have hmapCont : ContinuousOn (P.normalizedMap k)
      (closure (E.domain j).carrier) :=
    (P.normalizedMap_mdifferentiableOn k).continuousOn.mono hclosure
  have hqCont : ContinuousOn q (closure (E.domain j).carrier) := by
    exact (continuousOn_const.mul hmapCont).norm
  have hne : (closure (E.domain j).carrier).Nonempty :=
    ⟨p, subset_closure (E.domain_base_mem j)⟩
  obtain ⟨x₀, hx₀, hx₀max⟩ :=
    (E.domain j).compact_closure.exists_isMaxOn hne hqCont
  refine ⟨q x₀, norm_nonneg _, ?_, ?_⟩
  · have hx₀k : x₀ ∈ (E.domain k).carrier := hclosure hx₀
    have hcancel : c * P.normalizedMap k x₀ =
        ((P.equiv k).toHomeomorph ⟨x₀, hx₀k⟩ : ℂ) := by
      rw [P.normalizedMap_apply_of_mem k hx₀k]
      dsimp [c]
      field_simp [P.coefficient_ne_zero k]
    change ‖c * P.normalizedMap k x₀‖ < 1
    rw [hcancel]
    exact Complex.UnitDisc.norm_lt_one _
  · intro x hx
    have hcpos : 0 < ‖c‖ :=
      norm_pos_iff.mpr (P.coefficient_ne_zero k)
    have hq : ‖c * P.normalizedMap k x‖ ≤ q x₀ :=
      hx₀max (subset_closure hx)
    rw [norm_mul] at hq
    have hdiv : ‖P.normalizedMap k x‖ ≤ q x₀ / ‖c‖ :=
      (le_div_iff₀ hcpos).2 (by simpa [mul_comm] using hq)
    simpa [PointedDiskUniformization.radius, k, c, div_eq_mul_inv,
      mul_comm] using hdiv

/-- The normalized exhaustion maps are eventually uniformly bounded and
holomorphic on a neighborhood of each member of any compact exhaustion. -/
theorem PointedDiskUniformization.eventually_boundedOn_exhaustion_neighborhoods
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    {E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p}
    (P : PointedDiskUniformization E) (Kex : CompactExhaustion X) :
    ∀ m : ℕ, ∃ V : Set X, ∃ N : ℕ, ∃ B : ℝ,
      IsOpen V ∧ Kex m ⊆ V ∧ 0 < B ∧
        ∀ n : ℕ, N ≤ n →
          MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (P.normalizedMap n) V ∧
            ∀ x ∈ V, ‖P.normalizedMap n x‖ ≤ B := by
  intro m
  obtain ⟨j, hj⟩ :=
    E.toSmoothRelativelyCompactExhaustion.compact_subset_domain
      (Kex.isCompact m)
  let k := j + 1
  obtain ⟨ρ, hρ0, hρ1, hρ⟩ := P.exists_core_fraction_bound j
  let C : ℝ := P.radius k *
    (ρ * Real.exp (4 * ρ / (1 - ρ)))
  refine ⟨(E.domain j).carrier, k, C + 1,
    (E.domain j).isOpen, hj, ?_, ?_⟩
  · have hC : 0 ≤ C := by
      dsimp [C]
      exact mul_nonneg (P.radius_pos k).le
        (mul_nonneg hρ0 (Real.exp_pos _).le)
    linarith
  · intro n hkn
    constructor
    · exact (P.normalizedMap_mdifferentiableOn n).mono
        (E.domain_carrier_mono ((Nat.le_succ j).trans hkn))
    · intro x hx
      have hcompat := P.normalizedTransition_compat k n hkn
        (E.domain_carrier_mono (Nat.le_succ j) hx)
      rw [← hcompat]
      have hbound := univalent_disk_normalized_norm_le_exp_scaled
        (P.radius_pos k)
        (P.normalizedTransition_analyticOnNhd k n hkn)
        (P.normalizedTransition_injOn k n hkn)
        (P.normalizedTransition_zero k n hkn)
        (P.normalizedTransition_deriv_zero k n hkn)
        hρ0 hρ1 (hρ x hx)
      have hlt : C < C + 1 := by linarith
      exact hbound.trans hlt.le

/--
%%handwave
name:
  Montel limit of normalized exhaustion maps
statement:
  The normalized maps associated with simultaneous pointed disk
  uniformizations have a subsequence converging locally uniformly on the
  whole surface to a holomorphic complex-valued function.
proof:
  Koebe growth bounds give eventual uniform bounds on a neighborhood of every
  member of a compact exhaustion.  The changing-domain form of Montel's
  theorem then supplies a locally uniformly convergent subsequence and a
  global holomorphic limit.
-/
theorem PointedDiskUniformization.exists_normalizedMap_limit
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    {E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p}
    (P : PointedDiskUniformization E) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : X → ℂ,
      HolomorphicMap X ℂ f ∧
        TendstoLocallyUniformly
          (fun n : ℕ ↦ P.normalizedMap (φ n)) f Filter.atTop := by
  letI : SecondCountableTopology X :=
    rado_secondCountableTopology_riemannSurface X
  obtain ⟨Kex⟩ := riemannSurface_compactExhaustion X
  exact eventualDomain_montel_of_eventually_boundedOn_exhaustion_neighborhoods
    X Kex P.normalizedMap
      (P.eventually_boundedOn_exhaustion_neighborhoods Kex)

/-- On every compact set, all sufficiently late normalized maps are
injective. -/
theorem PointedDiskUniformization.eventually_normalizedMap_injOn_compact
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    {E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p}
    (P : PointedDiskUniformization E) {K : Set X} (hK : IsCompact K) :
    ∀ᶠ n : ℕ in Filter.atTop, InjOn (P.normalizedMap n) K := by
  filter_upwards [
    E.toSmoothRelativelyCompactExhaustion.eventually_compact_subset_domain hK]
      with n hn
  exact (P.normalizedMap_injOn n).mono hn

/-- The derivative normalization survives a locally uniform subsequential
limit, so the limit cannot be constant. -/
theorem PointedDiskUniformization.normalizedMap_limit_range_nontrivial
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    {E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p}
    (P : PointedDiskUniformization E) {φ : ℕ → ℕ} {f : X → ℂ}
    (hconv : TendstoLocallyUniformly
      (fun n : ℕ ↦ P.normalizedMap (φ n)) f Filter.atTop) :
    (range f).Nontrivial := by
  have hcomp : TendstoLocallyUniformlyOn
      (fun n : ℕ ↦ P.normalizedMap (φ n) ∘ P.initialDiskParameter)
      (f ∘ P.initialDiskParameter) Filter.atTop (ball (0 : ℂ) 1) := by
    exact hconv.tendstoLocallyUniformlyOn.comp P.initialDiskParameter
      (fun _ _ ↦ mem_univ _)
      P.initialDiskParameter_continuousOn
  have hcoord : TendstoLocallyUniformlyOn
      (fun n : ℕ ↦ P.initialCoordinateMap (φ n))
      (f ∘ P.initialDiskParameter) Filter.atTop (ball (0 : ℂ) 1) := by
    apply hcomp.congr
    intro n z hz
    exact P.normalizedMap_initialDiskParameter (φ n) hz
  have hdiff : ∀ᶠ n : ℕ in Filter.atTop,
      DifferentiableOn ℂ (P.initialCoordinateMap (φ n))
        (ball (0 : ℂ) 1) := by
    exact Filter.Eventually.of_forall fun n ↦
      (P.initialCoordinateMap_analyticOnNhd (φ n)).differentiableOn
  have hderConv := hcoord.deriv hdiff (Metric.isOpen_ball)
  have hderAt := hderConv.tendsto_at
    (mem_ball_self (show (0 : ℝ) < 1 by norm_num))
  have hder : deriv (f ∘ P.initialDiskParameter) 0 = 1 := by
    have hone : Tendsto (fun _ : ℕ ↦ (1 : ℂ)) Filter.atTop
        (𝓝 (deriv (f ∘ P.initialDiskParameter) 0)) := by
      simpa [Function.comp_def,
        P.initialCoordinateMap_deriv_zero] using hderAt
    exact tendsto_nhds_unique hone tendsto_const_nhds
  by_contra htriv
  have hsub : (range f).Subsingleton :=
    Set.not_nontrivial_iff.mp htriv
  have hconst : f ∘ P.initialDiskParameter =
      fun _ ↦ f (P.initialDiskParameter 0) := by
    funext z
    exact hsub (mem_range_self _) (mem_range_self _)
  rw [hconst, deriv_const] at hder
  exact zero_ne_one hder

/--
%%handwave
name:
  Injectivity of the normalized exhaustion limit
statement:
  A locally uniform subsequential limit of the normalized exhaustion maps is
  injective on the whole connected surface.
proof:
  The derivative normalization survives in the first disk coordinate, so the
  limit is not constant.  Every compact set is eventually contained in an
  exhaustion member, where the approximating maps are injective.  The
  changing-domain Hurwitz theorem therefore makes the limit injective.
-/
theorem PointedDiskUniformization.normalizedMap_limit_injective
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    {E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p}
    (P : PointedDiskUniformization E) {φ : ℕ → ℕ} {f : X → ℂ}
    (hφ : StrictMono φ)
    (hconv : TendstoLocallyUniformly
      (fun n : ℕ ↦ P.normalizedMap (φ n)) f Filter.atTop) :
    Function.Injective f := by
  have hholo : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (P.normalizedMap (φ n)) U := by
    intro x
    obtain ⟨m, hxm⟩ := E.domain_exhausts x
    refine ⟨(E.domain m).carrier, (E.domain m).isOpen, hxm, ?_⟩
    filter_upwards [Filter.eventually_atTop.2
      ⟨m, fun n hn ↦ hn.trans (StrictMono.id_le hφ n)⟩] with n hn
    exact (P.normalizedMap_mdifferentiableOn (φ n)).mono
      (E.domain_carrier_mono hn)
  have hinj : ∀ K : Set X, IsCompact K →
      ∀ᶠ n : ℕ in Filter.atTop,
        InjOn (P.normalizedMap (φ n)) K := by
    intro K hK
    exact hφ.tendsto_atTop.eventually
      (P.eventually_normalizedMap_injOn_compact hK)
  exact locallyUniformLimit_injective_of_eventuallyInjectiveOn_compacts
    X (fun n : ℕ ↦ P.normalizedMap (φ n)) f hconv hholo hinj
      (P.normalizedMap_limit_range_nontrivial hconv)

/-- If one value belongs eventually to the images of a fixed compact set,
then it belongs to the image of the locally uniform limit. -/
theorem locallyUniformLimit_mem_image_of_eventually_mem_image_compact
    {X : Type} [TopologicalSpace X] [LocallyCompactSpace X]
    {F : ℕ → X → ℂ} {f : X → ℂ}
    (hconv : TendstoLocallyUniformly F f Filter.atTop)
    (hf : Continuous f) {K : Set X} (hK : IsCompact K) {w : ℂ}
    (hw : ∀ᶠ n : ℕ in Filter.atTop, w ∈ F n '' K) :
    w ∈ f '' K := by
  have huniform : TendstoUniformlyOn F f Filter.atTop K :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mp
      hconv.tendstoLocallyUniformlyOn K (subset_univ K) hK
  have hwclosure : w ∈ closure (f '' K) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hclose : ∀ᶠ n : ℕ in Filter.atTop,
        ∀ x ∈ K, dist (f x) (F n x) < ε :=
      (Metric.tendstoUniformlyOn_iff.mp huniform) ε hε
    obtain ⟨n, hnclose, hnimage⟩ := (hclose.and hw).exists
    rcases hnimage with ⟨x, hxK, hFx⟩
    refine ⟨f x, ⟨x, hxK, rfl⟩, ?_⟩
    simpa [hFx, dist_comm] using hnclose x hxK
  have hclosed : IsClosed (f '' K) := (hK.image hf).isClosed
  rwa [hclosed.closure_eq] at hwclosure

/--
%%handwave
name:
  The unbounded-radius limit covers the plane
statement:
  If the conformal radii of the normalized exhaustion maps are unbounded,
  every locally uniform normalized limit is surjective onto the complex
  plane.
proof:
  Given a complex number, choose an earlier exhaustion member whose conformal
  radius is more than four times its norm.  The scaled quarter theorem puts
  that number in every sufficiently late image, with preimages in the compact
  closure of the chosen member.  Local uniform convergence then places it in
  the limiting image.
-/
theorem PointedDiskUniformization.normalizedMap_limit_surjective_of_not_bddAbove_radius
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    {E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p}
    (P : PointedDiskUniformization E) {φ : ℕ → ℕ} {f : X → ℂ}
    (hφ : StrictMono φ) (hf : HolomorphicMap X ℂ f)
    (hconv : TendstoLocallyUniformly
      (fun n : ℕ ↦ P.normalizedMap (φ n)) f Filter.atTop)
    (hunbounded : ¬ BddAbove (range P.radius)) :
    Function.Surjective f := by
  intro w
  rcases not_bddAbove_iff.mp hunbounded (4 * ‖w‖) with
    ⟨r, ⟨m, rfl⟩, hm⟩
  have hwball : w ∈ ball (0 : ℂ) (P.radius m / 4) := by
    rw [mem_ball_zero_iff]
    nlinarith
  let K : Set X := closure (E.domain m).carrier
  have hK : IsCompact K := (E.domain m).compact_closure
  have hevent : ∀ᶠ n : ℕ in Filter.atTop,
      w ∈ P.normalizedMap (φ n) '' K := by
    filter_upwards [Filter.eventually_atTop.2
      ⟨m, fun n hn ↦ hn.trans (StrictMono.id_le hφ n)⟩] with n hmn
    have hquarter := koebe_quarter_normalized_scaled
      (P.radius_pos m)
      (P.normalizedTransition_analyticOnNhd m (φ n) hmn)
      (P.normalizedTransition_injOn m (φ n) hmn)
      (P.normalizedTransition_zero m (φ n) hmn)
      (P.normalizedTransition_deriv_zero m (φ n) hmn)
    obtain ⟨z, hz, hzw⟩ := hquarter hwball
    have hzimage : z ∈ P.normalizedMap m '' (E.domain m).carrier := by
      rw [P.normalizedMap_image m]
      exact hz
    rcases hzimage with ⟨x, hxm, hzx⟩
    refine ⟨x, subset_closure hxm, ?_⟩
    rw [← P.normalizedTransition_compat m (φ n) hmn hxm,
      hzx, hzw]
  have hwimage := locallyUniformLimit_mem_image_of_eventually_mem_image_compact
    hconv hf.continuous hK hevent
  rcases hwimage with ⟨x, _hxK, hfx⟩
  exact ⟨x, hfx⟩

/--
%%handwave
name:
  The bounded-radius limit covers the limiting disk
statement:
  If the conformal radii are bounded, the image of every locally uniform
  normalized limit contains the open disk whose radius is their supremum.
proof:
  For a point strictly inside the limiting disk, choose an earlier radius
  sufficiently close to the supremum.  Later normalized transition maps have
  derivative close to one and hence cover the chosen point by quantitative
  kernel convergence.  The preimages remain in one compact exhaustion
  closure, so local uniform convergence transfers the point to the limiting
  image.
-/
theorem PointedDiskUniformization.ball_csSup_radius_subset_range_normalizedMap_limit
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    {E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p}
    (P : PointedDiskUniformization E) {φ : ℕ → ℕ} {f : X → ℂ}
    (hφ : StrictMono φ) (hf : HolomorphicMap X ℂ f)
    (hconv : TendstoLocallyUniformly
      (fun n : ℕ ↦ P.normalizedMap (φ n)) f Filter.atTop)
    (hbounded : BddAbove (range P.radius)) :
    ball (0 : ℂ) (sSup (range P.radius)) ⊆ range f := by
  let R : ℝ := sSup (range P.radius)
  have hRupper : ∀ n : ℕ, P.radius n ≤ R := by
    intro n
    exact le_csSup hbounded (mem_range_self n)
  have hRpos : 0 < R :=
    (P.radius_pos 0).trans_le (hRupper 0)
  intro w hw
  have hwnorm : ‖w‖ < R := by
    simpa [R, mem_ball_zero_iff] using hw
  let q : ℝ := (‖w‖ / R + 1) / 2
  have hratio0 : 0 ≤ ‖w‖ / R := div_nonneg (norm_nonneg w) hRpos.le
  have hratio1 : ‖w‖ / R < 1 := (div_lt_one hRpos).2 hwnorm
  have hq0 : 0 < q := by
    dsimp [q]
    linarith
  have hq1 : q < 1 := by
    dsimp [q]
    linarith
  let δ : ℝ := (1 - q) / 2
  let ρ : ℝ := (q + 1) / 2
  let C : ℝ := ρ * (2 * ρ / (1 - ρ) + 1)
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hρ0 : 0 < ρ := by dsimp [ρ]; linarith
  have hρ1 : ρ < 1 := by dsimp [ρ]; linarith
  have hC : 0 < C := by
    dsimp [C]
    have : 0 < 1 - ρ := sub_pos.mpr hρ1
    positivity
  let η : ℝ := δ / (8 * C)
  have hη : 0 < η := by dsimp [η]; positivity
  have hwqR : ‖w‖ < q * R := by
    dsimp [q]
    field_simp [hRpos.ne']
    linarith
  have hwdivq : ‖w‖ / q < R :=
    (div_lt_iff₀ hq0).2 (by simpa [mul_comm] using hwqR)
  have hReta : R * (1 - η) < R := by
    nlinarith
  have hthreshold : max (‖w‖ / q) (R * (1 - η)) < R :=
    max_lt hwdivq hReta
  obtain ⟨r, ⟨m, hrm⟩, hm⟩ :=
    exists_lt_of_lt_csSup (range_nonempty P.radius) hthreshold
  subst r
  have hmNorm : ‖w‖ / q < P.radius m :=
    (le_max_left _ _).trans_lt hm
  have hmEta : R * (1 - η) < P.radius m :=
    (le_max_right _ _).trans_lt hm
  let K : Set X := closure (E.domain m).carrier
  have hK : IsCompact K := (E.domain m).compact_closure
  have hevent : ∀ᶠ n : ℕ in Filter.atTop,
      w ∈ P.normalizedMap (φ n) '' K := by
    filter_upwards [Filter.eventually_atTop.2
      ⟨m, fun n hn ↦ hn.trans (StrictMono.id_le hφ n)⟩] with n hmn
    let rn : ℝ := P.radius (φ n)
    let a : ℝ := P.radius m / rn
    let u : ℂ := w / (rn : ℂ)
    have hrnPos : 0 < rn := P.radius_pos (φ n)
    have hmrn : P.radius m ≤ rn := P.radius_mono hmn
    have hrnR : rn ≤ R := hRupper (φ n)
    have ha0 : 0 < a := div_pos (P.radius_pos m) hrnPos
    have ha1 : a ≤ 1 := (div_le_one hrnPos).2 hmrn
    have huq : ‖u‖ ≤ q := by
      have hwdivm : ‖w‖ / P.radius m < q :=
        (div_lt_iff₀ (P.radius_pos m)).2
          (by simpa [mul_comm] using (div_lt_iff₀ hq0).mp hmNorm)
      have hdiv : ‖w‖ / rn ≤ ‖w‖ / P.radius m :=
        div_le_div_of_nonneg_left (norm_nonneg w) (P.radius_pos m) hmrn
      rw [show ‖u‖ = ‖w‖ / rn by
        simp [u, rn, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hrnPos]]
      exact hdiv.trans hwdivm.le
    have hratioLower : P.radius m / R ≤ a := by
      exact div_le_div_of_nonneg_left (P.radius_pos m).le hrnPos hrnR
    have hetaRatio : 1 - P.radius m / R < η := by
      have : 1 - η < P.radius m / R :=
        (lt_div_iff₀ hRpos).2 (by simpa [mul_comm] using hmEta)
      linarith
    have honea : 1 - a ≤ 1 - P.radius m / R := sub_le_sub_left hratioLower 1
    have hsmall : (1 - a) * C < δ / 8 := by
      have hfactor : 1 - a < η := honea.trans_lt hetaRatio
      have hmul := mul_lt_mul_of_pos_right hfactor hC
      have hηC : η * C = δ / 8 := by
        dsimp [η]
        field_simp [hC.ne']
      simpa [hηC] using hmul
    have huimage := normalized_diskSelfMap_mem_image_of_deriv_close
      (P.unitTransition_analyticOnNhd m (φ n) hmn)
      (P.unitTransition_injOn m (φ n) hmn)
      (P.unitTransition_mapsTo m (φ n) hmn)
      (P.unitTransition_zero m (φ n) hmn)
      (by simpa [a, rn] using
        P.unitTransition_deriv_zero m (φ n) hmn)
      ha0 ha1 hq0.le hq1 huq
      (by simpa [δ, ρ, C] using hsmall)
    rcases huimage with ⟨z, hz, hzu⟩
    have hrnC : (rn : ℂ) ≠ 0 := by exact_mod_cast hrnPos.ne'
    have hS : P.normalizedTransition m (φ n) hmn
        ((P.radius m : ℂ) * z) = w := by
      dsimp [PointedDiskUniformization.unitTransition, u] at hzu
      exact mul_right_cancel₀ hrnC
        ((div_eq_div_iff hrnC hrnC).mp hzu)
    have hzScaled : (P.radius m : ℂ) * z ∈
        ball (0 : ℂ) (P.radius m) := by
      rw [mem_ball_zero_iff] at hz ⊢
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (P.radius_pos m)]
      simpa using mul_lt_mul_of_pos_left hz (P.radius_pos m)
    have hzimage : (P.radius m : ℂ) * z ∈
        P.normalizedMap m '' (E.domain m).carrier := by
      rw [P.normalizedMap_image m]
      exact hzScaled
    rcases hzimage with ⟨x, hxm, hzx⟩
    refine ⟨x, subset_closure hxm, ?_⟩
    rw [← P.normalizedTransition_compat m (φ n) hmn hxm,
      hzx, hS]
  have hwimage := locallyUniformLimit_mem_image_of_eventually_mem_image_compact
    hconv hf.continuous hK hevent
  rcases hwimage with ⟨x, _hxK, hfx⟩
  exact ⟨x, hfx⟩

/-- The base point remains at the origin in every normalized Montel limit. -/
theorem PointedDiskUniformization.normalizedMap_limit_base
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    {E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p}
    (P : PointedDiskUniformization E) {φ : ℕ → ℕ} {f : X → ℂ}
    (hconv : TendstoLocallyUniformly
      (fun n : ℕ ↦ P.normalizedMap (φ n)) f Filter.atTop) :
    f p = 0 := by
  have hp := hconv.tendstoLocallyUniformlyOn.tendsto_at (mem_univ p)
  have hp' : Tendsto (fun _ : ℕ ↦ (0 : ℂ)) Filter.atTop (𝓝 (f p)) := by
    simpa using hp
  exact (tendsto_nhds_unique tendsto_const_nhds hp').symm

/-- In the bounded-radius case every value of the Montel limit has norm at
most the limiting conformal radius. -/
theorem PointedDiskUniformization.normalizedMap_limit_norm_le_csSup_radius
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    {E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p}
    (P : PointedDiskUniformization E) {φ : ℕ → ℕ} {f : X → ℂ}
    (hφ : StrictMono φ)
    (hconv : TendstoLocallyUniformly
      (fun n : ℕ ↦ P.normalizedMap (φ n)) f Filter.atTop)
    (hbounded : BddAbove (range P.radius)) (x : X) :
    ‖f x‖ ≤ sSup (range P.radius) := by
  let R : ℝ := sSup (range P.radius)
  have hRupper : ∀ n : ℕ, P.radius n ≤ R := fun n ↦
    le_csSup hbounded (mem_range_self n)
  obtain ⟨m, hxm⟩ := E.domain_exhausts x
  have hevent : ∀ᶠ n : ℕ in Filter.atTop,
      P.normalizedMap (φ n) x ∈ closedBall (0 : ℂ) R := by
    filter_upwards [Filter.eventually_atTop.2
      ⟨m, fun n hn ↦ hn.trans (StrictMono.id_le hφ n)⟩] with n hmn
    have hxlate : x ∈ (E.domain (φ n)).carrier :=
      E.domain_carrier_mono hmn hxm
    have himage : P.normalizedMap (φ n) x ∈
        ball (0 : ℂ) (P.radius (φ n)) := by
      rw [← P.normalizedMap_image (φ n)]
      exact ⟨x, hxlate, rfl⟩
    rw [mem_closedBall, dist_zero_right]
    have hlt : ‖P.normalizedMap (φ n) x‖ < P.radius (φ n) := by
      simpa [mem_ball_zero_iff] using himage
    exact hlt.le.trans (hRupper (φ n))
  have hxlim := hconv.tendstoLocallyUniformlyOn.tendsto_at (mem_univ x)
  have hmem := (isClosed_closedBall : IsClosed (closedBall (0 : ℂ) R)).mem_of_tendsto
    hxlim hevent
  simpa [R, mem_closedBall, dist_zero_left] using hmem

/--
%%handwave
name:
  The bounded-radius limit lands in the limiting disk
statement:
  In the bounded-radius case, every value of a normalized limit has norm
  strictly smaller than the supremum of the conformal radii.
proof:
  Local uniform convergence first places the range in the corresponding
  closed disk.  Equality at one point would contradict openness of the
  nonconstant holomorphic limit, because every neighborhood of a boundary
  point contains values outside that closed disk.
-/
theorem PointedDiskUniformization.normalizedMap_limit_norm_lt_csSup_radius
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    {E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p}
    (P : PointedDiskUniformization E) {φ : ℕ → ℕ} {f : X → ℂ}
    (hφ : StrictMono φ) (hf : HolomorphicMap X ℂ f)
    (hconv : TendstoLocallyUniformly
      (fun n : ℕ ↦ P.normalizedMap (φ n)) f Filter.atTop)
    (hbounded : BddAbove (range P.radius)) (x : X) :
    ‖f x‖ < sSup (range P.radius) := by
  let R : ℝ := sSup (range P.radius)
  have hRpos : 0 < R :=
    (P.radius_pos 0).trans_le
      (le_csSup hbounded (mem_range_self 0))
  have hle : ‖f x‖ ≤ R := by
    simpa [R] using P.normalizedMap_limit_norm_le_csSup_radius
      hφ hconv hbounded x
  by_contra hnot
  have heq : ‖f x‖ = R := le_antisymm hle (not_lt.mp hnot)
  have hnontrivial := P.normalizedMap_limit_range_nontrivial hconv
  have hopen : IsOpen (range f) :=
    (nonconstant_holomorphicMap_isOpenMap hf hnontrivial).isOpen_range
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp
    (hopen.mem_nhds (mem_range_self x))
  let t : ℝ := ε / (2 * R)
  let y : ℂ := ((1 + t : ℝ) : ℂ) * f x
  have ht : 0 < t := by dsimp [t]; positivity
  have hyball : y ∈ ball (f x) ε := by
    rw [mem_ball, dist_eq_norm]
    have hySub : y - f x = (t : ℂ) * f x := by
      dsimp [y]
      push_cast
      ring
    rw [hySub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht, heq]
    dsimp [t]
    field_simp [hRpos.ne']
    linarith
  rcases hεsub hyball with ⟨z, hzy⟩
  have hzle : ‖f z‖ ≤ R := by
    simpa [R] using P.normalizedMap_limit_norm_le_csSup_radius
      hφ hconv hbounded z
  have hynorm : ‖y‖ = (1 + t) * R := by
    dsimp [y]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith : 0 < 1 + t), heq]
  rw [hzy, hynorm] at hzle
  nlinarith

/--
%%handwave
name:
  Hubbard normal-family dichotomy
statement:
  A Riemann surface with a pointed exhaustion whose members admit
  simultaneous pointed disk uniformizations is biholomorphic either to the
  complex plane or to the unit disk.
proof:
  Extract a normalized locally uniform limit; it is nonconstant and
  injective.  If the conformal radii are unbounded, the quarter theorem makes
  the limit surjective onto the plane.  If they are bounded, quantitative
  kernel convergence identifies the range with the disk of radius equal to
  their supremum, which rescales biholomorphically to the unit disk.
-/
theorem PointedDiskUniformization.biholomorphic_complexPlane_or_unitDisc
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    {E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p}
    (P : PointedDiskUniformization E) :
    BiholomorphicSurfaces X ℂ ∨
      BiholomorphicSurfaces X Complex.UnitDisc := by
  obtain ⟨φ, hφ, f, hf, hconv⟩ := P.exists_normalizedMap_limit
  have hinj : Function.Injective f :=
    P.normalizedMap_limit_injective hφ hconv
  by_cases hbounded : BddAbove (range P.radius)
  · right
    let R : ℝ := sSup (range P.radius)
    have hRpos : 0 < R :=
      (P.radius_pos 0).trans_le
        (le_csSup hbounded (mem_range_self 0))
    have hRC : (R : ℂ) ≠ 0 := by exact_mod_cast hRpos.ne'
    let Fto : X → Complex.UnitDisc := fun x ↦
      ⟨f x / (R : ℂ), by
        rw [Subsemigroup.mem_unitBall, norm_div, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hRpos]
        exact (div_lt_one hRpos).2
          (by simpa [R] using
            (P.normalizedMap_limit_norm_lt_csSup_radius
              hφ hf hconv hbounded x))⟩
    have hFcoe : HolomorphicMap X ℂ (fun x ↦ (Fto x : ℂ)) := by
      have hscale : HolomorphicMap ℂ ℂ (fun z ↦ z / (R : ℂ)) := by
        exact (show Differentiable ℂ (fun z : ℂ ↦ z / (R : ℂ)) by
          fun_prop).mdifferentiable
      simpa [Fto, Function.comp_def] using hscale.comp hf
    let F : PointedHolomorphicMap X Complex.UnitDisc p 0 :=
      { toFun := Fto
        holomorphic := holomorphicMap_unitDisc_of_coe hFcoe
        base_eq := by
          apply Subtype.ext
          change f p / (R : ℂ) = 0
          rw [P.normalizedMap_limit_base hconv]
          simp }
    have hFinj : Function.Injective F.toFun := by
      intro x y hxy
      apply hinj
      have hxy' := congrArg Subtype.val hxy
      change f x / (R : ℂ) = f y / (R : ℂ) at hxy'
      exact mul_right_cancel₀ hRC
        ((div_eq_div_iff hRC hRC).mp hxy')
    have hFsurj : Function.Surjective F.toFun := by
      intro z
      let w : ℂ := (R : ℂ) * (z : ℂ)
      have hw : w ∈ ball (0 : ℂ) R := by
        rw [mem_ball_zero_iff, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hRpos]
        simpa using mul_lt_mul_of_pos_left
          (Complex.UnitDisc.norm_lt_one z) hRpos
      have hwRange :=
        P.ball_csSup_radius_subset_range_normalizedMap_limit
          hφ hf hconv hbounded (by simpa [R] using hw)
      rcases hwRange with ⟨x, hfx⟩
      refine ⟨x, ?_⟩
      apply Subtype.ext
      change f x / (R : ℂ) = (z : ℂ)
      rw [hfx]
      dsimp [w]
      field_simp [hRC]
    exact ⟨F.biholomorphicOfBijective ⟨hFinj, hFsurj⟩⟩
  · left
    have hsurj : Function.Surjective f :=
      P.normalizedMap_limit_surjective_of_not_bddAbove_radius
        hφ hf hconv hbounded
    have hunbranched : ∀ x : X, ∀ χx : PointedSurfaceCoordinate X x,
        surfaceComplexDerivativeInCoordinate χx f ≠ 0 := by
      intro x χx
      exact injective_holomorphicMap_surfaceComplexDerivative_ne_zero
        χx hf hinj
    exact biholomorphicToComplexPlane_of_bijective_unbranched_holomorphicPlaneMap
      X f hf hunbranched hinj hsurj

/-- The exhaustion form of the noncompact zero-cohomology uniformization
theorem, with noncompactness supplied as an explicit hypothesis. -/
theorem deRhamH1Zero_biholomorphic_complexPlane_or_unitDisc_of_not_compactSpace
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    [Subsingleton
      (DeRhamCohomology
        (I := SurfaceRealModel) (M := X) (A := ℝ) 1)]
    (hnoncompact : ¬ CompactSpace X) :
    BiholomorphicSurfaces X ℂ ∨
      BiholomorphicSurfaces X Complex.UnitDisc := by
  obtain ⟨E⟩ := connected_noncompact_has_smoothRelativelyCompactExhaustion
    X hnoncompact
  let p : X := Classical.choice (inferInstance : Nonempty X)
  obtain ⟨EH⟩ :=
    smoothRelativelyCompactExhaustion_exists_pointedH1Zero_filling_of_ambientDeRhamH1Zero
      hnoncompact E p
  obtain ⟨P⟩ := EH.has_pointedDiskUniformization hnoncompact
  exact P.biholomorphic_complexPlane_or_unitDisc

/--
%%handwave
name:
  Uniformization of a noncompact surface with vanishing first cohomology
statement:
  A noncompact Riemann surface whose first real de Rham cohomology
  vanishes is biholomorphic either to the complex plane or to the unit disk.
proof:
  Fill a smooth exhaustion so that every connected member still has vanishing
  first cohomology, and uniformize each member by a pointed Green-function map
  to the disk.  Divide these maps by their derivative in the first disk
  coordinate.  Koebe distortion gives compact-local bounds, hence Montel gives
  a locally uniform holomorphic limit.  Its normalized derivative is one, and
  injectivity survives the limit.  If the conformal radii are unbounded,
  Koebe's quarter theorem makes the limit onto the plane.  If they are bounded,
  quantitative kernel convergence makes it onto the disk whose radius is the
  supremum of the conformal radii; rescaling gives the unit disk.
-/
theorem noncompact_deRhamH1Zero_biholomorphic_complexPlane_or_unitDisc
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    [NoncompactSpace X]
    [Subsingleton
      (DeRhamCohomology
        (I := SurfaceRealModel) (M := X) (A := ℝ) 1)] :
    BiholomorphicSurfaces X ℂ ∨
      BiholomorphicSurfaces X Complex.UnitDisc := by
  exact deRhamH1Zero_biholomorphic_complexPlane_or_unitDisc_of_not_compactSpace
    X (not_compactSpace_iff.mpr inferInstance)

end JJMath.Uniformization
