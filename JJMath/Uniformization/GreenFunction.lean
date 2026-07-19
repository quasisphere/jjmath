import JJMath.Uniformization.EvansPotential
import JJMath.Uniformization.GreenFunctionCompactSuperlevel
import JJMath.Uniformization.GreenFunctionCore
import JJMath.Uniformization.H1ZeroExhaustion
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Algebra.Order.Field

/-!
# Green-function route to uniformization

This file records the high-level formalization targets for proving the
hyperbolic case of uniformization by constructing Green functions with one
pole and exponentiating their harmonic conjugates.
-/

namespace JJMath

open scoped _root_.Manifold _root_.Topology ContDiff

namespace Uniformization

/--
%%handwave
name:
  Singular Perron admissible function
statement:
  A singular Perron admissible function for a pole \(p\) is a nonnegative
  superharmonic competitor on the punctured surface, with at least the
  prescribed logarithmic singularity at the pole and boundary value zero at
  infinity.
-/
def IsGreenPerronAdmissible (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    (p : X) (u : X → ℝ) : Prop :=
  (∀ x : X, 0 ≤ u x) ∧
    IsSuperharmonicOnSurface {x : X | x ≠ p} u ∧
      (∀ χ : PointedSurfaceCoordinate X p,
        ∃ C : ℝ,
          ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
            -Real.log ‖χ.chart x - χ.chart p‖ - C ≤ u x) ∧
        Filter.Tendsto u (Filter.cocompact X) (𝓝 0)

/-- The Green function with its pole value reset to zero. -/
noncomputable def GreenFunctionWithPole.perronCompetitor
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {p : X}
    (G : GreenFunctionWithPole X p) : X → ℝ := by
  classical
  exact Function.update G.toFun p 0

/--
%%handwave
name:
  Green functions are singular Perron competitors
statement:
  A Green function with pole \(p\), with its value at \(p\) reset to zero, is
  an admissible singular Perron competitor.
proof:
  Away from \(p\) it is positive and harmonic, hence superharmonic.  The
  removable logarithmic singularity writes \(G+\log |z-z(p)|\) as a harmonic,
  hence continuous, function near \(p\), giving the required logarithmic lower
  bound.  Changing one point does not affect the value at infinity.
-/
theorem greenFunctionWithPole_to_greenPerronAdmissible
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    (G : GreenFunctionWithPole X p) :
    IsGreenPerronAdmissible X p G.perronCompetitor := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    by_cases hxp : x = p
    · simp [GreenFunctionWithPole.perronCompetitor, Function.update, hxp]
    · exact le_of_lt (by
        simpa [GreenFunctionWithPole.perronCompetitor, Function.update, hxp] using
          G.positive_away_pole x hxp)
  · have hpunc_open : IsOpen ({x : X | x ≠ p}) := by
      simpa using (isOpen_ne (x := p) : IsOpen {x : X | x ≠ p})
    have hsuper :
        IsSuperharmonicOnSurface {x : X | x ≠ p} G.toFun :=
      harmonicOnSurface_superharmonic hpunc_open G.harmonic_away_pole
    simpa [IsSuperharmonicOnSurface] using
      subharmonicOnSurface_congr_on hsuper (by
        intro x hx
        have hxp : x ≠ p := hx
        simp [GreenFunctionWithPole.perronCompetitor, Function.update, hxp])
  · intro χ
    rcases G.logarithmic_singularity χ with ⟨h, hharm, hEq⟩
    refine ⟨1 - h p, ?_⟩
    have hcont : ContinuousOn h χ.chart.source :=
      harmonicOnSurface_continuousOn χ.chart.open_source hharm
    have htendsto_source :
        Filter.Tendsto h (𝓝[χ.chart.source] p) (𝓝 (h p)) :=
      hcont p χ.base_mem_source
    have htendsto :
        Filter.Tendsto h (𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p)
          (𝓝 (h p)) :=
      htendsto_source.mono_left
        (nhdsWithin_mono p (Set.inter_subset_left :
          χ.chart.source ∩ {x : X | x ≠ p} ⊆ χ.chart.source))
    have hlower :
        ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
          h p - 1 ≤ h x := by
      have hlt :
          ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
            h p - 1 < h x :=
        htendsto (Ioi_mem_nhds (by linarith : h p - 1 < h p))
      exact hlt.mono (fun _ hx ↦ le_of_lt hx)
    filter_upwards [hEq, hlower, self_mem_nhdsWithin] with x hxEq hxLower hxself
    have hxp : x ≠ p := hxself.2
    have hupdate : G.perronCompetitor x = G.toFun x := by
      simp [GreenFunctionWithPole.perronCompetitor, Function.update, hxp]
    rw [hupdate]
    linarith
  · have heq :
        G.toFun =ᶠ[Filter.cocompact X] G.perronCompetitor := by
      filter_upwards [isCompact_singleton.compl_mem_cocompact] with x hxp
      have hx_ne : x ≠ p := by
        simpa using hxp
      simp [GreenFunctionWithPole.perronCompetitor, Function.update, hx_ne]
    exact Filter.Tendsto.congr' heq G.tends_to_zero_at_infinity

/--
%%handwave
name:
  Green functions make the singular Perron family nonempty
statement:
  If a Green function with pole \(p\) exists, then the singular Perron family
  for \(p\) is nonempty.
proof:
  Use the Green function itself, with the pole value reset to zero.
-/
theorem greenFunctionWithPole_greenPerron_family_nonempty
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    (hG : Nonempty (GreenFunctionWithPole X p)) :
    ∃ u : X → ℝ, IsGreenPerronAdmissible X p u := by
  rcases hG with ⟨G⟩
  exact ⟨G.perronCompetitor, greenFunctionWithPole_to_greenPerronAdmissible X G⟩

/--
%%handwave
name:
  Singular Perron envelope
statement:
  The singular Perron envelope is the pointwise infimum of all nonnegative
  superharmonic functions with the prescribed logarithmic pole and zero
  boundary value at infinity.
-/
noncomputable def greenPerronEnvelope
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] (p : X) : X → ℝ :=
  fun x ↦ sInf {a : ℝ | ∃ u : X → ℝ, IsGreenPerronAdmissible X p u ∧ a = u x}

/--
%%handwave
name:
  The singular Perron envelope is nonnegative
statement:
  The singular Perron envelope is nonnegative everywhere.
proof:
  Every admissible competitor is nonnegative at every point.  Therefore the
  pointwise infimum of all admissible values is also nonnegative.
-/
theorem greenPerronEnvelope_nonnegative
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] (p : X) :
    ∀ x : X, 0 ≤ greenPerronEnvelope X p x := by
  intro x
  rw [greenPerronEnvelope]
  refine Real.sInf_nonneg ?_
  intro a ha
  rcases ha with ⟨u, hu, rfl⟩
  exact hu.1 x

/--
%%handwave
name:
  The singular Perron envelope lies below each competitor
statement:
  The singular Perron envelope is bounded above by every admissible
  superharmonic competitor.
proof:
  At a fixed point, the envelope is the infimum of all admissible values, and
  the chosen competitor contributes one of those values.  Nonnegativity of all
  competitors supplies the lower bound needed for the real infimum.
-/
theorem greenPerronEnvelope_le_admissible
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    {p : X} {u : X → ℝ}
    (hu : IsGreenPerronAdmissible X p u) :
    ∀ x : X, greenPerronEnvelope X p x ≤ u x := by
  intro x
  rw [greenPerronEnvelope]
  refine csInf_le ?_ ⟨u, hu, rfl⟩
  exact ⟨0, by
    intro a ha
    rcases ha with ⟨v, hv, rfl⟩
    exact hv.1 x⟩

/--
%%handwave
name:
  Minima of singular Perron competitors are admissible
statement:
  The pointwise minimum of two singular Perron admissible competitors is again
  singular Perron admissible.
proof:
  Nonnegativity is preserved by minimum.  Superharmonic functions are closed
  under minimum.  Near the pole, take the worse of the two logarithmic
  constants.  At infinity, the minimum is squeezed between zero and either
  competitor, so it also tends to zero.
-/
theorem greenPerronAdmissible_inf
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    {p : X} {u v : X → ℝ}
    (hu : IsGreenPerronAdmissible X p u)
    (hv : IsGreenPerronAdmissible X p v) :
    IsGreenPerronAdmissible X p (fun x ↦ u x ⊓ v x) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    exact le_inf (hu.1 x) (hv.1 x)
  · exact superharmonicOnSurface_inf hu.2.1 hv.2.1
  · intro χ
    rcases hu.2.2.1 χ with ⟨Cu, huχ⟩
    rcases hv.2.2.1 χ with ⟨Cv, hvχ⟩
    refine ⟨Cu ⊔ Cv, ?_⟩
    filter_upwards [huχ, hvχ] with x hux hvx
    refine le_inf ?_ ?_
    · calc
        -Real.log ‖χ.chart x - χ.chart p‖ - (Cu ⊔ Cv)
            ≤ -Real.log ‖χ.chart x - χ.chart p‖ - Cu := by
              gcongr
              exact le_sup_left
        _ ≤ u x := hux
    · calc
        -Real.log ‖χ.chart x - χ.chart p‖ - (Cu ⊔ Cv)
            ≤ -Real.log ‖χ.chart x - χ.chart p‖ - Cv := by
              gcongr
              exact le_sup_right
        _ ≤ v x := hvx
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hu.2.2.2
      (fun x ↦ le_inf (hu.1 x) (hv.1 x))
      (fun x ↦ inf_le_left)

/--
%%handwave
name:
  Singular Perron competitors approximate the envelope from above
statement:
  If the singular Perron family is nonempty, then at every point and for
  every positive \(\varepsilon\), some admissible competitor has value less
  than the envelope plus \(\varepsilon\).
proof:
  This is the defining approximation property of the infimum.  The family of
  admissible values is nonempty by hypothesis and bounded below by zero
  because all admissible competitors are nonnegative.
-/
theorem exists_greenPerronAdmissible_lt_envelope_add
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    {p : X}
    (hfamily : ∃ u : X → ℝ, IsGreenPerronAdmissible X p u)
    (x : X) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : X → ℝ,
      IsGreenPerronAdmissible X p u ∧
        u x < greenPerronEnvelope X p x + ε := by
  let S : Set ℝ :=
    {a : ℝ | ∃ u : X → ℝ, IsGreenPerronAdmissible X p u ∧ a = u x}
  have hS_bdd : BddBelow S := by
    refine ⟨0, ?_⟩
    intro a ha
    rcases ha with ⟨u, hu, rfl⟩
    exact hu.1 x
  have hS_nonempty : S.Nonempty := by
    rcases hfamily with ⟨u, hu⟩
    exact ⟨u x, u, hu, rfl⟩
  have hsInf_lt : sInf S < sInf S + ε := by
    linarith
  rcases (csInf_lt_iff hS_bdd hS_nonempty).mp hsInf_lt with
    ⟨a, haS, halt⟩
  rcases haS with ⟨u, hu, rfl⟩
  refine ⟨u, hu, ?_⟩
  simpa [greenPerronEnvelope, S] using halt

/--
%%handwave
name:
  Harmonic majorants generated by singular Perron liftings
statement:
  A local harmonic majorant of the singular Perron envelope on a coordinate
  disk is a harmonic lifting of an admissible singular superharmonic
  competitor; it lies above the envelope, lies below the original competitor on
  the disk, and the function obtained by patching it into the competitor is
  still admissible.
-/
def IsGreenPerronHarmonicMajorantOn
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    (p : X) (V : PerronDomain X) (h : X → ℝ) : Prop :=
  IsHarmonicOnSurface V.carrier h ∧
    (∀ x ∈ V.carrier, greenPerronEnvelope X p x ≤ h x) ∧
      ∃ u : X → ℝ,
        IsGreenPerronAdmissible X p u ∧
          (∀ x ∈ V.carrier, h x ≤ u x) ∧
            IsGreenPerronAdmissible X p (harmonicReplacementPatch V u h)

/--
%%handwave
name:
  Harmonic reduction of a singular Perron competitor
statement:
  A harmonic reduction of a singular Perron competitor on a coordinate disk
  away from the pole is harmonic on the disk, lies below the competitor there,
  and remains singular Perron admissible after it is patched into the
  competitor.
-/
def IsGreenPerronHarmonicReduction
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    (p : X) (V : PerronDomain X) (u h : X → ℝ) : Prop :=
  IsHarmonicOnSurface V.carrier h ∧
    (∀ x ∈ V.carrier, h x ≤ u x) ∧
      IsGreenPerronAdmissible X p (harmonicReplacementPatch V u h)













/--
%%handwave
name:
  Pointed logarithmic model
statement:
  In a pointed coordinate at the pole, the logarithmic model with constant
  \(A\) is \(-\log |z-z(p)|+A\).
-/
noncomputable def pointedCoordinateLogarithmicModel
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    {p : X} (χ : PointedSurfaceCoordinate X p) (A : ℝ) : X → ℝ :=
  fun x : X ↦ -Real.log ‖χ.chart x - χ.chart p‖ + A

/--
%%handwave
name:
  Pointed coordinate logarithmic distances are comparable
statement:
  For two pointed coordinates at the same point, the negative logarithmic
  coordinate distances differ by a bounded amount near the point.
proof:
  The transition map between the coordinates is holomorphic with nonzero
  derivative at the marked point.  Hence the quotient of the two coordinate
  distances tends to a positive finite limit, so its logarithm is bounded near
  the point.
-/
theorem pointedCoordinate_negative_log_distances_eventually_comparable
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    (χ ψ : PointedSurfaceCoordinate X p) :
    ∃ B : ℝ,
      ∀ᶠ x in 𝓝[ψ.chart.source ∩ {x : X | x ≠ p}] p,
        -Real.log ‖ψ.chart x - ψ.chart p‖ - B ≤
          -Real.log ‖χ.chart x - χ.chart p‖ := by
  rcases pointedCoordinate_distances_eventually_le_mul X χ ψ with
    ⟨C, hC_one, hC⟩
  refine ⟨Real.log C, ?_⟩
  have hC_pos : 0 < C := lt_of_lt_of_le zero_lt_one hC_one
  filter_upwards [hC, self_mem_nhdsWithin] with x hxC hxψ
  rcases hxC with ⟨hxχsource, hdist⟩
  have hψ_ne : ψ.chart x ≠ ψ.chart p := by
    intro hEq
    exact hxψ.2 (ψ.chart.injOn hxψ.1 ψ.base_mem_source hEq)
  have hχ_ne : χ.chart x ≠ χ.chart p := by
    intro hEq
    exact hxψ.2 (χ.chart.injOn hxχsource χ.base_mem_source hEq)
  have hψ_pos : 0 < ‖ψ.chart x - ψ.chart p‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hψ_ne)
  have hχ_pos : 0 < ‖χ.chart x - χ.chart p‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hχ_ne)
  have hlog_le :
      Real.log ‖χ.chart x - χ.chart p‖ ≤
        Real.log C + Real.log ‖ψ.chart x - ψ.chart p‖ := by
    calc
      Real.log ‖χ.chart x - χ.chart p‖
          ≤ Real.log (C * ‖ψ.chart x - ψ.chart p‖) :=
            Real.log_le_log hχ_pos hdist
      _ = Real.log C + Real.log ‖ψ.chart x - ψ.chart p‖ := by
            rw [Real.log_mul hC_pos.ne' hψ_pos.ne']
  linarith

/--
%%handwave
name:
  An exact local logarithmic model has the prescribed pole
statement:
  If a function agrees with \(-\log |z-z(p)|\) plus a constant on a
  punctured coordinate ball around \(p\), then it has the standard logarithmic
  lower bound at \(p\) in every pointed coordinate.
proof:
  In the chosen coordinate this is immediate from the assumed equality.  In
  any other pointed coordinate, the two coordinate distance functions are
  comparable up to a bounded logarithmic error near \(p\).
-/
theorem exact_pointedCoordinate_logarithmic_model_has_logPole
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (p : X) {b : X → ℝ} (A : ℝ)
    (χ : PointedSurfaceCoordinate X p) {R : ℝ}
    (hR : 0 < R)
    (hb_model :
      ∀ x ∈ χ.chart.source,
        ‖χ.chart x - χ.chart p‖ < R →
          x ≠ p →
            b x = -Real.log ‖χ.chart x - χ.chart p‖ + A) :
    ∀ ψ : PointedSurfaceCoordinate X p,
      ∃ C₀ : ℝ,
        ∀ᶠ x in 𝓝[ψ.chart.source ∩ {x : X | x ≠ p}] p,
          -Real.log ‖ψ.chart x - ψ.chart p‖ - C₀ ≤ b x := by
  intro ψ
  rcases pointedCoordinate_negative_log_distances_eventually_comparable
      X χ ψ with ⟨B, hB⟩
  refine ⟨B - A, ?_⟩
  filter_upwards
    [hB, pointedCoordinate_eventually_mem_inner_ball X χ ψ hR,
      self_mem_nhdsWithin]
    with x hlog hxinner hxψ
  have hb :
      b x = -Real.log ‖χ.chart x - χ.chart p‖ + A :=
    hb_model x hxinner.1 hxinner.2 hxψ.2
  calc
    -Real.log ‖ψ.chart x - ψ.chart p‖ - (B - A)
        = (-Real.log ‖ψ.chart x - ψ.chart p‖ - B) + A := by ring
    _ ≤ -Real.log ‖χ.chart x - χ.chart p‖ + A := by
        linarith
    _ = b x := hb.symm

/--
%%handwave
name:
  A logarithmic model is locally nonnegative and below a competitor
statement:
  Given a singular Perron competitor and a pointed coordinate at the pole, one
  can choose a small coordinate ball and a constant \(A\) so that
  \(-\log |z-z(p)|+A\) is nonnegative and lies below the competitor throughout
  the punctured ball.
proof:
  The competitor has a logarithmic lower bound
  \(-\log |z-z(p)|-C\le u\) near the pole.  Take \(A=-C\) and shrink the
  coordinate ball so that this lower bound holds and the radius is at most
  \(e^A\); then the logarithmic model is also nonnegative on the ball.
-/
theorem exists_pointedCoordinate_logarithmic_model_nonnegative_below_admissible_on_ball
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (p : X) (u₀ : X → ℝ)
    (hu₀ : IsGreenPerronAdmissible X p u₀)
    (χ : PointedSurfaceCoordinate X p) :
    ∃ A R : ℝ, 0 < R ∧
      Metric.closedBall (χ.chart p) R ⊆ χ.chart.target ∧
        (∀ x ∈ χ.chart.source,
          ‖χ.chart x - χ.chart p‖ < R →
            x ≠ p →
              0 ≤ -Real.log ‖χ.chart x - χ.chart p‖ + A) ∧
          ∀ x ∈ χ.chart.source,
            ‖χ.chart x - χ.chart p‖ < R →
              x ≠ p →
                -Real.log ‖χ.chart x - χ.chart p‖ + A ≤ u₀ x := by
  rcases hu₀.2.2.1 χ with ⟨C, hC⟩
  let A : ℝ := -C
  let E : Set X :=
    {y : X | y ∈ χ.chart.source ∩ {x : X | x ≠ p} →
      -Real.log ‖χ.chart y - χ.chart p‖ - C ≤ u₀ y}
  have hE_nhds : E ∈ 𝓝 p := by
    simpa [E] using eventually_nhdsWithin_iff.mp hC
  have hc_target : χ.chart p ∈ χ.chart.target :=
    χ.chart.map_source χ.base_mem_source
  have hpre_map :
      E ∈ Filter.map χ.chart.symm (𝓝 (χ.chart p)) :=
    χ.chart.continuousAt_symm hc_target
      (by simpa [χ.chart.left_inv χ.base_mem_source] using hE_nhds)
  have hpre : χ.chart.symm ⁻¹' E ∈ 𝓝 (χ.chart p) := by
    simpa [Filter.mem_map] using hpre_map
  rcases Metric.eventually_nhds_iff.mp hpre with ⟨δE, hδE_pos, hδE⟩
  rcases Metric.mem_nhds_iff.mp (χ.chart.open_target.mem_nhds hc_target) with
    ⟨δT, hδT_pos, hball_target⟩
  let δ : ℝ := min (min δE δT) (Real.exp A)
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    exact lt_min (lt_min hδE_pos hδT_pos) (Real.exp_pos A)
  let R : ℝ := δ / 2
  have hR_pos : 0 < R := by
    dsimp [R]
    linarith
  have hR_lt_δ : R < δ := by
    dsimp [R]
    linarith
  have hδ_le_δE : δ ≤ δE := by
    dsimp [δ]
    exact (min_le_left _ _).trans (min_le_left _ _)
  have hδ_le_δT : δ ≤ δT := by
    dsimp [δ]
    exact (min_le_left _ _).trans (min_le_right _ _)
  have hδ_le_expA : δ ≤ Real.exp A := by
    dsimp [δ]
    exact min_le_right _ _
  have hR_lt_δE : R < δE := hR_lt_δ.trans_le hδ_le_δE
  have hR_lt_δT : R < δT := hR_lt_δ.trans_le hδ_le_δT
  have hR_lt_expA : R < Real.exp A := hR_lt_δ.trans_le hδ_le_expA
  have hclosed_R : Metric.closedBall (χ.chart p) R ⊆ χ.chart.target :=
    (Metric.closedBall_subset_ball hR_lt_δT).trans hball_target
  refine ⟨A, R, hR_pos, hclosed_R, ?_, ?_⟩
  · intro x hxsource hxR hxp
    have hnorm_pos : 0 < ‖χ.chart x - χ.chart p‖ := by
      refine norm_pos_iff.mpr ?_
      exact sub_ne_zero.mpr (by
        intro hchart
        exact hxp (χ.chart.injOn hxsource χ.base_mem_source hchart))
    have hnorm_lt_expA : ‖χ.chart x - χ.chart p‖ < Real.exp A :=
      hxR.trans hR_lt_expA
    have hlog_lt_A :
        Real.log ‖χ.chart x - χ.chart p‖ < A :=
      (Real.log_lt_iff_lt_exp hnorm_pos).mpr hnorm_lt_expA
    linarith
  · intro x hxsource hxR hxp
    have hx_ball : dist (χ.chart x) (χ.chart p) < δE := by
      simpa [dist_eq_norm] using hxR.trans hR_lt_δE
    have hsymm_eq : χ.chart.symm (χ.chart x) = x :=
      χ.chart.left_inv hxsource
    have hsymm_source : χ.chart.symm (χ.chart x) ∈ χ.chart.source := by
      simpa [hsymm_eq] using hxsource
    have hsymm_ne : χ.chart.symm (χ.chart x) ≠ p := by
      simpa [hsymm_eq] using hxp
    have hineq := hδE hx_ball ⟨hsymm_source, hsymm_ne⟩
    simpa [E, A, hsymm_eq] using hineq


/--
%%handwave
name:
  Taking the smaller of a competitor and a logarithmic barrier is admissible
statement:
  The pointwise minimum of a singular Perron competitor and a nonnegative
  superharmonic local logarithmic barrier is again a singular Perron
  competitor.
proof:
  Nonnegativity and superharmonicity are preserved by taking pointwise minima.
  The original competitor and the exact local logarithmic model each give the
  required logarithmic lower bound near the pole, so their minimum does too.
  At infinity, the minimum is squeezed between zero and the original
  competitor.
-/
theorem greenPerronAdmissible_inf_logarithmic_barrier
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (p : X) {u₀ b : X → ℝ} {A R : ℝ}
    (hu₀ : IsGreenPerronAdmissible X p u₀)
    (χ : PointedSurfaceCoordinate X p)
    (hR : 0 < R)
    (hb_nonneg : ∀ x : X, 0 ≤ b x)
    (hb_super : IsSuperharmonicOnSurface {x : X | x ≠ p} b)
    (hb_model :
      ∀ x ∈ χ.chart.source,
        ‖χ.chart x - χ.chart p‖ < R →
          x ≠ p →
            b x = -Real.log ‖χ.chart x - χ.chart p‖ + A) :
    IsGreenPerronAdmissible X p (fun x ↦ u₀ x ⊓ b x) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    exact le_inf (hu₀.1 x) (hb_nonneg x)
  · exact superharmonicOnSurface_inf hu₀.2.1 hb_super
  · intro ψ
    rcases hu₀.2.2.1 ψ with ⟨Cu, huψ⟩
    rcases exact_pointedCoordinate_logarithmic_model_has_logPole
        X p A χ hR hb_model ψ with
      ⟨Cb, hbψ⟩
    refine ⟨Cu ⊔ Cb, ?_⟩
    filter_upwards [huψ, hbψ] with x hux hbx
    refine le_inf ?_ ?_
    · calc
        -Real.log ‖ψ.chart x - ψ.chart p‖ - (Cu ⊔ Cb)
            ≤ -Real.log ‖ψ.chart x - ψ.chart p‖ - Cu := by
              gcongr
              exact le_sup_left
        _ ≤ u₀ x := hux
    · calc
        -Real.log ‖ψ.chart x - ψ.chart p‖ - (Cu ⊔ Cb)
            ≤ -Real.log ‖ψ.chart x - ψ.chart p‖ - Cb := by
              gcongr
              exact le_sup_right
        _ ≤ b x := hbx
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hu₀.2.2.2
      (fun x ↦ le_inf (hu₀.1 x) (hb_nonneg x))
      (fun x ↦ inf_le_left)






/--
%%handwave
name:
  Annular comparison gives a coordinate-ball lower barrier
statement:
  In a pointed coordinate, every nonnegative superharmonic function with at
  least the standard logarithmic pole dominates one fixed logarithmic lower
  barrier on a sufficiently small coordinate ball.
proof:
  Fix an outer coordinate circle.  For each admissible function and each
  smaller inner circle where its logarithmic lower bound is already valid,
  compare it on the annulus with a logarithmic harmonic function whose outer
  boundary is below zero.  Letting the inner circle shrink gives a constant
  independent of the function.
-/
noncomputable def pointedCoordinateAnnularLogComparator
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    {p : X} (χ : PointedSurfaceCoordinate X p) (ρ R C : ℝ) : X → ℝ :=
  fun x : X ↦
    ((Real.log R - Real.log ‖χ.chart x - χ.chart p‖) /
        (Real.log R - Real.log ρ)) *
      (-Real.log ρ - C)

/--
%%handwave
name:
  Pointed coordinate annuli are open
statement:
  A pointed coordinate annulus is open in the surface.
proof:
  It is the chart preimage of the open interval of coordinate radii.
-/
theorem pointedCoordinateAnnulus_isOpen
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    {p : X} (χ : PointedSurfaceCoordinate X p) (ρ R : ℝ) :
    IsOpen (pointedCoordinateAnnulus X χ ρ R) := by
  have hdist : Continuous fun z : ℂ ↦ dist z (χ.chart p) :=
    continuous_id.dist continuous_const
  simpa [pointedCoordinateAnnulus, Set.mem_Ioo, dist_eq_norm] using
    χ.chart.isOpen_inter_preimage (isOpen_Ioo.preimage hdist)

/--
%%handwave
name:
  Pointed coordinate annuli lie in the chart source
statement:
  A pointed coordinate annulus is contained in the source of its coordinate.
proof:
  Membership in the annulus includes membership in the chart source by
  definition.
-/
theorem pointedCoordinateAnnulus_subset_chart_source
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    {p : X} (χ : PointedSurfaceCoordinate X p) (ρ R : ℝ) :
    pointedCoordinateAnnulus X χ ρ R ⊆ χ.chart.source := by
  intro x hx
  exact hx.1

/--
%%handwave
name:
  Positive-radius pointed coordinate annuli avoid the pole
statement:
  If the inner radius is positive, then the pointed coordinate annulus is
  contained in the punctured surface.
proof:
  At the pole the coordinate distance is zero, contradicting the strict
  lower bound by the positive inner radius.
-/
theorem pointedCoordinateAnnulus_subset_punctured
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    {p : X} (χ : PointedSurfaceCoordinate X p) {ρ R : ℝ}
    (hρ : 0 < ρ) :
    pointedCoordinateAnnulus X χ ρ R ⊆ {x : X | x ≠ p} := by
  intro x hx hxp
  have hnorm_zero : ‖χ.chart x - χ.chart p‖ = 0 := by
    rw [hxp, sub_self, norm_zero]
  linarith [hx.2.1]

/--
%%handwave
name:
  Superharmonicity restricts to pointed coordinate annuli
statement:
  A superharmonic function on the punctured surface is superharmonic on every
  pointed coordinate annulus with positive inner radius.
proof:
  The positive inner radius makes the annulus a subset of the punctured
  surface, and superharmonicity restricts to smaller open sets.
-/
theorem superharmonicOnSurface_pointedCoordinateAnnulus
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    {p : X} (χ : PointedSurfaceCoordinate X p) {ρ R : ℝ} (hρ : 0 < ρ)
    {u : X → ℝ}
    (hu : IsSuperharmonicOnSurface {x : X | x ≠ p} u) :
    IsSuperharmonicOnSurface (pointedCoordinateAnnulus X χ ρ R) u :=
  superharmonicOnSurface_mono
    (pointedCoordinateAnnulus_subset_punctured X χ hρ) hu

/--
%%handwave
name:
  The annular logarithmic comparator has the inner boundary value
statement:
  On the inner coordinate circle \(|z-z(p)|=\rho\), the annular logarithmic
  comparator equals \(-\log \rho-C\).
proof:
  Substituting \(|z-z(p)|=\rho\) makes the logarithmic interpolation factor
  equal to \(1\); its denominator is nonzero because \(0<\rho<R\).
-/
theorem pointedCoordinateAnnularLogComparator_inner_boundary
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    {p : X} (χ : PointedSurfaceCoordinate X p) {ρ R C : ℝ}
    (hρ : 0 < ρ) (hρR : ρ < R) {x : X}
    (hxnorm : ‖χ.chart x - χ.chart p‖ = ρ) :
    pointedCoordinateAnnularLogComparator X χ ρ R C x = -Real.log ρ - C := by
  have hden_ne : Real.log R - Real.log ρ ≠ 0 := by
    have hlog_lt : Real.log ρ < Real.log R := Real.log_lt_log hρ hρR
    linarith
  simp [pointedCoordinateAnnularLogComparator, hxnorm, hden_ne]

/--
%%handwave
name:
  The annular logarithmic comparator has the outer boundary value
statement:
  On the outer coordinate circle \(|z-z(p)|=R\), the annular logarithmic
  comparator equals \(0\).
proof:
  Substituting \(|z-z(p)|=R\) makes the numerator
  \(\log R-\log R\) vanish.
-/
theorem pointedCoordinateAnnularLogComparator_outer_boundary
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    {p : X} (χ : PointedSurfaceCoordinate X p) {ρ R C : ℝ} {x : X}
    (hxnorm : ‖χ.chart x - χ.chart p‖ = R) :
    pointedCoordinateAnnularLogComparator X χ ρ R C x = 0 := by
  simp [pointedCoordinateAnnularLogComparator, hxnorm]

/--
%%handwave
name:
  The annular logarithmic comparator is harmonic
statement:
  The logarithmic interpolant between the two coordinate circles is harmonic
  on the pointed coordinate annulus.
proof:
  It is an affine multiple of \(\log R-\log |z-z(p)|\), and
  \(\log |z-z(p)|\) is harmonic away from the pole.
-/
theorem pointedCoordinateAnnularLogComparator_harmonicOn_annulus
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    (χ : PointedSurfaceCoordinate X p) {ρ R C : ℝ} (hρ : 0 < ρ) :
    IsHarmonicOnSurface (pointedCoordinateAnnulus X χ ρ R)
      (pointedCoordinateAnnularLogComparator X χ ρ R C) := by
  let U : Set X := pointedCoordinateAnnulus X χ ρ R
  have hlog :
      IsHarmonicOnSurface U
        (fun x : X ↦ Real.log ‖χ.chart x - χ.chart p‖) :=
    coordinateLogDistance_harmonicOnSurface χ.chart χ.chart_mem_atlas
      (by
        intro x hx
        exact hx.1)
      (by
        intro x hx hEq
        have hnorm_zero : ‖χ.chart x - χ.chart p‖ = 0 := by
          rw [hEq, sub_self, norm_zero]
        have hpos : 0 < ‖χ.chart x - χ.chart p‖ := hρ.trans hx.2.1
        linarith)
  have hbase :
      IsHarmonicOnSurface U
        (fun x : X ↦ Real.log R - Real.log ‖χ.chart x - χ.chart p‖) :=
    harmonicOnSurface_sub
      (harmonicOnSurface_const U (Real.log R)) hlog
  have hquot :
      IsHarmonicOnSurface U
        (fun x : X ↦
          (Real.log R - Real.log ‖χ.chart x - χ.chart p‖) /
            (Real.log R - Real.log ρ)) := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      harmonicOnSurface_const_mul
        (c := (Real.log R - Real.log ρ)⁻¹) hbase
  have hscaled :
      IsHarmonicOnSurface U
        (fun x : X ↦
          ((Real.log R - Real.log ‖χ.chart x - χ.chart p‖) /
              (Real.log R - Real.log ρ)) *
            (-Real.log ρ - C)) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
    harmonicOnSurface_const_mul
      (c := -Real.log ρ - C) hquot
  simpa [U, pointedCoordinateAnnularLogComparator] using hscaled

/--
%%handwave
name:
  The closed pointed annulus stays in the coordinate source
statement:
  If the outer closed coordinate ball is contained in the chart target, then
  every limit point of the pointed coordinate annulus still lies in the chart
  source.
proof:
  In coordinates, the annulus has closure contained in the closed Euclidean
  ball of radius \(R\).  Compact containment of that ball in the chart target
  lets the inverse chart pull the limit point back inside the chart source.
-/
theorem pointedCoordinateAnnulus_closure_subset_chart_source
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [T2Space X]
    {p : X} (χ : PointedSurfaceCoordinate X p) {ρ R : ℝ}
    (_hρ : 0 < ρ) (_hρR : ρ < R)
    (hclosed : Metric.closedBall (χ.chart p) R ⊆ χ.chart.target) :
    closure (pointedCoordinateAnnulus X χ ρ R) ⊆ χ.chart.source := by
  let K : Set X := χ.chart.symm '' Metric.closedBall (χ.chart p) R
  have hU_subset_K :
      pointedCoordinateAnnulus X χ ρ R ⊆ K := by
    intro x hx
    refine ⟨χ.chart x, ?_, ?_⟩
    · exact Metric.ball_subset_closedBall
        (by simpa [Metric.mem_ball, dist_eq_norm] using hx.2.2)
    · exact χ.chart.left_inv hx.1
  have hK_compact : IsCompact K :=
    (isCompact_closedBall (χ.chart p) R).image_of_continuousOn
      (χ.chart.continuousOn_symm.mono hclosed)
  have hclosure_subset_K :
      closure (pointedCoordinateAnnulus X χ ρ R) ⊆ K :=
    closure_minimal hU_subset_K hK_compact.isClosed
  have hK_subset_source : K ⊆ χ.chart.source := by
    intro x hx
    rcases hx with ⟨z, hz, rfl⟩
    exact χ.chart.map_target (hclosed hz)
  exact hclosure_subset_K.trans hK_subset_source

/--
%%handwave
name:
  The closed pointed annulus has the lower radius bound
statement:
  Every limit point of the pointed coordinate annulus has coordinate distance
  at least the inner radius.
proof:
  Once the closure is known to stay inside the chart source, the coordinate
  distance is continuous there.  Therefore the inequality
  \(\rho<|z-z(p)|\) on the annulus closes to
  \(\rho\le |z-z(p)|\) on its closure.
-/
theorem pointedCoordinateAnnulus_closure_radius_lower
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [T2Space X]
    {p : X} (χ : PointedSurfaceCoordinate X p) {ρ R : ℝ}
    (hρ : 0 < ρ) (hρR : ρ < R)
    (hclosed : Metric.closedBall (χ.chart p) R ⊆ χ.chart.target) :
    ∀ x ∈ closure (pointedCoordinateAnnulus X χ ρ R),
      ρ ≤ ‖χ.chart x - χ.chart p‖ := by
  intro x hxcl
  have hxsource :
      x ∈ χ.chart.source :=
    pointedCoordinateAnnulus_closure_subset_chart_source
      X χ hρ hρR hclosed hxcl
  have hcont :
      ContinuousAt (fun y : X ↦ ‖χ.chart y - χ.chart p‖) x :=
    (χ.chart.continuousAt hxsource).sub continuousAt_const |>.norm
  by_contra hnot
  have hxlt : ‖χ.chart x - χ.chart p‖ < ρ := lt_of_not_ge hnot
  have hnear :
      {y : X | ‖χ.chart y - χ.chart p‖ < ρ} ∈ 𝓝 x :=
    hcont.preimage_mem_nhds (Iio_mem_nhds hxlt)
  rcases mem_closure_iff_nhds.mp hxcl
      {y : X | ‖χ.chart y - χ.chart p‖ < ρ} hnear with
    ⟨y, hylt, hyU⟩
  exact not_lt_of_ge (le_of_lt hylt) hyU.2.1

/--
%%handwave
name:
  The closed pointed annulus avoids the pole
statement:
  If the inner radius is positive, then the closure of a compactly contained
  pointed annulus is contained in the punctured surface.
proof:
  The coordinate radius is at least the positive inner radius on the closed
  annulus, while the pole has coordinate radius zero.
-/
theorem pointedCoordinateAnnulus_closure_subset_punctured
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [T2Space X]
    {p : X} (χ : PointedSurfaceCoordinate X p) {ρ R : ℝ}
    (hρ : 0 < ρ) (hρR : ρ < R)
    (hclosed : Metric.closedBall (χ.chart p) R ⊆ χ.chart.target) :
    closure (pointedCoordinateAnnulus X χ ρ R) ⊆ {x : X | x ≠ p} := by
  intro x hxcl hxp
  have hρle :
      ρ ≤ ‖χ.chart x - χ.chart p‖ :=
    pointedCoordinateAnnulus_closure_radius_lower
      X χ hρ hρR hclosed x hxcl
  have hzero : ‖χ.chart x - χ.chart p‖ = 0 := by
    rw [hxp, sub_self, norm_zero]
  linarith

/--
%%handwave
name:
  The closed pointed annulus has the upper radius bound
statement:
  Every limit point of the pointed coordinate annulus has coordinate distance
  at most the outer radius.
proof:
  The coordinate distance is continuous on the chart source, and the annulus
  satisfies \(|z-z(p)|<R\).  Taking closure gives
  \(|z-z(p)|\le R\).
-/
theorem pointedCoordinateAnnulus_closure_radius_upper
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [T2Space X]
    {p : X} (χ : PointedSurfaceCoordinate X p) {ρ R : ℝ}
    (hρ : 0 < ρ) (hρR : ρ < R)
    (hclosed : Metric.closedBall (χ.chart p) R ⊆ χ.chart.target) :
    ∀ x ∈ closure (pointedCoordinateAnnulus X χ ρ R),
      ‖χ.chart x - χ.chart p‖ ≤ R := by
  intro x hxcl
  have hxsource :
      x ∈ χ.chart.source :=
    pointedCoordinateAnnulus_closure_subset_chart_source
      X χ hρ hρR hclosed hxcl
  have hcont :
      ContinuousAt (fun y : X ↦ ‖χ.chart y - χ.chart p‖) x :=
    (χ.chart.continuousAt hxsource).sub continuousAt_const |>.norm
  by_contra hnot
  have hxgt : R < ‖χ.chart x - χ.chart p‖ := lt_of_not_ge hnot
  have hnear :
      {y : X | R < ‖χ.chart y - χ.chart p‖} ∈ 𝓝 x :=
    hcont.preimage_mem_nhds (Ioi_mem_nhds hxgt)
  rcases mem_closure_iff_nhds.mp hxcl
      {y : X | R < ‖χ.chart y - χ.chart p‖} hnear with
    ⟨y, hygt, hyU⟩
  exact not_lt_of_ge (le_of_lt hyU.2.2) hygt

/--
%%handwave
name:
  The closure of a compactly contained pointed annulus stays in the closed annulus
statement:
  If the outer closed coordinate ball lies in the chart target, then the
  closure of the pointed coordinate annulus lies in the chart source and has
  coordinate radius between the two annular radii.
proof:
  Transport to the coordinate chart.  The Euclidean closure of
  \(\rho<|z-z(p)|<R\) is contained in
  \(\rho\le |z-z(p)|\le R\), and compact containment of the outer closed ball
  prevents extra closure points from appearing at the edge of the chart.
-/
theorem pointedCoordinateAnnulus_closure_subset_closed_annulus
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [T2Space X]
    {p : X} (χ : PointedSurfaceCoordinate X p) {ρ R : ℝ}
    (hρ : 0 < ρ) (hρR : ρ < R)
    (hclosed : Metric.closedBall (χ.chart p) R ⊆ χ.chart.target) :
    closure (pointedCoordinateAnnulus X χ ρ R) ⊆
      {x : X | x ∈ χ.chart.source ∧
        ρ ≤ ‖χ.chart x - χ.chart p‖ ∧
          ‖χ.chart x - χ.chart p‖ ≤ R} := by
  intro x hx
  exact ⟨
    pointedCoordinateAnnulus_closure_subset_chart_source X χ hρ hρR hclosed hx,
    pointedCoordinateAnnulus_closure_radius_lower X χ hρ hρR hclosed x hx,
    pointedCoordinateAnnulus_closure_radius_upper X χ hρ hρR hclosed x hx⟩

/--
%%handwave
name:
  The annular logarithmic comparator is continuous on the closed annulus
statement:
  The explicit logarithmic interpolant is continuous on the closure of a
  compactly contained pointed annulus.
proof:
  The coordinate radius is continuous on the closed annulus and is bounded
  below by the positive inner radius, so its logarithm is continuous there.
  The comparator is obtained from this logarithm by affine operations.
-/
theorem pointedCoordinateAnnularLogComparator_continuousOn_closure
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [T2Space X]
    {p : X} (χ : PointedSurfaceCoordinate X p) {ρ R C : ℝ}
    (hρ : 0 < ρ) (hρR : ρ < R)
    (hclosed : Metric.closedBall (χ.chart p) R ⊆ χ.chart.target) :
    ContinuousOn
      (pointedCoordinateAnnularLogComparator X χ ρ R C)
      (closure (pointedCoordinateAnnulus X χ ρ R)) := by
  let U : Set X := pointedCoordinateAnnulus X χ ρ R
  have hclosure_source : closure U ⊆ χ.chart.source :=
    pointedCoordinateAnnulus_closure_subset_chart_source
      X χ hρ hρR hclosed
  have hchart_cont : ContinuousOn χ.chart (closure U) :=
    χ.chart.continuousOn.mono hclosure_source
  have hdist_cont :
      ContinuousOn
        (fun x : X ↦ ‖χ.chart x - χ.chart p‖)
        (closure U) :=
    (hchart_cont.sub continuousOn_const).norm
  have hdist_ne :
      ∀ x ∈ closure U, ‖χ.chart x - χ.chart p‖ ≠ 0 := by
    intro x hx
    have hρle :
        ρ ≤ ‖χ.chart x - χ.chart p‖ :=
      pointedCoordinateAnnulus_closure_radius_lower
        X χ hρ hρR hclosed x hx
    exact ne_of_gt (hρ.trans_le hρle)
  have hlog_cont :
      ContinuousOn
        (fun x : X ↦ Real.log ‖χ.chart x - χ.chart p‖)
        (closure U) :=
    hdist_cont.log hdist_ne
  have hquot_cont :
      ContinuousOn
        (fun x : X ↦
          (Real.log R - Real.log ‖χ.chart x - χ.chart p‖) /
            (Real.log R - Real.log ρ))
        (closure U) := by
    simpa [div_eq_mul_inv] using
      (continuousOn_const.sub hlog_cont).mul continuousOn_const
  have hscaled :
      ContinuousOn
        (fun x : X ↦
          ((Real.log R - Real.log ‖χ.chart x - χ.chart p‖) /
              (Real.log R - Real.log ρ)) *
            (-Real.log ρ - C))
        (closure U) :=
    hquot_cont.mul continuousOn_const
  simpa [U, pointedCoordinateAnnularLogComparator] using hscaled

/--
%%handwave
name:
  The frontier of a compactly contained pointed annulus is the two circles
statement:
  If the outer closed coordinate ball lies in the chart target, then the
  frontier of the pointed coordinate annulus is contained in the union of the
  inner coordinate circle and the outer coordinate circle.
proof:
  Inside the chart source, the annulus is the inverse image of the Euclidean
  annulus \(\rho<|z-z(p)|<R\).  The compact containment keeps the closure away
  from the edge of the chart, so no additional frontier points appear from the
  chart source.
-/
theorem pointedCoordinateAnnulus_frontier_subset_inner_or_outer
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [T2Space X]
    {p : X} (χ : PointedSurfaceCoordinate X p) {ρ R : ℝ}
    (hρ : 0 < ρ) (hρR : ρ < R)
    (hclosed : Metric.closedBall (χ.chart p) R ⊆ χ.chart.target) :
    frontier (pointedCoordinateAnnulus X χ ρ R) ⊆
      {x : X | x ∈ χ.chart.source ∧
        (‖χ.chart x - χ.chart p‖ = ρ ∨
          ‖χ.chart x - χ.chart p‖ = R)} := by
  intro x hxfront
  have hxclosed :=
    pointedCoordinateAnnulus_closure_subset_closed_annulus
      X χ hρ hρR hclosed (frontier_subset_closure hxfront)
  rcases hxclosed with ⟨hxsource, hρle, hRle⟩
  have hUopen : IsOpen (pointedCoordinateAnnulus X χ ρ R) :=
    pointedCoordinateAnnulus_isOpen X χ ρ R
  have hxnotU : x ∉ pointedCoordinateAnnulus X χ ρ R := by
    intro hxU
    have hx_inter :
        x ∈ pointedCoordinateAnnulus X χ ρ R ∩
          frontier (pointedCoordinateAnnulus X χ ρ R) := ⟨hxU, hxfront⟩
    have h_empty :
        pointedCoordinateAnnulus X χ ρ R ∩
          frontier (pointedCoordinateAnnulus X χ ρ R) = ∅ :=
      hUopen.inter_frontier_eq
    rw [h_empty] at hx_inter
    exact hx_inter
  refine ⟨hxsource, ?_⟩
  by_cases hinner : ‖χ.chart x - χ.chart p‖ = ρ
  · exact Or.inl hinner
  · right
    have hρlt : ρ < ‖χ.chart x - χ.chart p‖ :=
      lt_of_le_of_ne hρle (by
        intro h
        exact hinner h.symm)
    by_contra houter_ne
    have hltR : ‖χ.chart x - χ.chart p‖ < R := lt_of_le_of_ne hRle houter_ne
    exact hxnotU ⟨hxsource, ⟨hρlt, hltR⟩⟩

/--
%%handwave
name:
  Euclidean annuli are connected
statement:
  A round Euclidean annulus \(\rho<|z-c|<R\) in the complex plane is
  preconnected whenever \(0<\rho<R\).
proof:
  Radially retract each point to the middle circle
  \(|z-c|=(\rho+R)/2\).  The radial segments remain in the annulus because
  the interval \((\rho,R)\) is convex, and the middle circle is path-connected
  in the plane.
-/
theorem complex_annulus_preconnected
    (c : ℂ) {ρ R : ℝ} (hρ : 0 < ρ) (_hρR : ρ < R) :
    IsPreconnected {z : ℂ | ρ < ‖z - c‖ ∧ ‖z - c‖ < R} := by
  let S : Set (ℝ × ℂ) := Set.Ioo ρ R ×ˢ Metric.sphere (0 : ℂ) 1
  let F : ℝ × ℂ → ℂ := fun q ↦ c + q.1 • q.2
  have hsphere : IsPreconnected (Metric.sphere (0 : ℂ) 1) :=
    isPreconnected_sphere
      (Complex.rank_real_complex ▸ (by norm_num : (1 : Cardinal) < 2))
      (0 : ℂ) 1
  have hS : IsPreconnected S := isPreconnected_Ioo.prod hsphere
  have hcont : ContinuousOn F S := by
    dsimp [F]
    fun_prop
  have hpre : IsPreconnected (F '' S) := hS.image F hcont
  have himage :
      F '' S = {z : ℂ | ρ < ‖z - c‖ ∧ ‖z - c‖ < R} := by
    ext z
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases q with ⟨r, u⟩
      rcases hq with ⟨hr, hu⟩
      have hrpos : 0 < r := hρ.trans hr.1
      have hunorm : ‖u‖ = 1 := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hu
      have hnorm : ‖c + r • u - c‖ = r := by
        simp [sub_eq_add_neg, add_assoc, hunorm, abs_of_nonneg hrpos.le]
      change ρ < ‖c + r • u - c‖ ∧ ‖c + r • u - c‖ < R
      rw [hnorm]
      exact hr
    · intro hz
      let r : ℝ := ‖z - c‖
      rcases hz with ⟨hzρ, hzR⟩
      have hrpos : 0 < r := hρ.trans hzρ
      have hr_ne : r ≠ 0 := ne_of_gt hrpos
      let u : ℂ := (r⁻¹ : ℝ) • (z - c)
      have hu_sphere : u ∈ Metric.sphere (0 : ℂ) 1 := by
        have hunorm : ‖u‖ = 1 := by
          simp [u, r, inv_mul_cancel₀ hr_ne]
        simp [hunorm]
      refine ⟨(r, u), ⟨⟨hzρ, hzR⟩, hu_sphere⟩, ?_⟩
      have hscale : (r : ℝ) • u = z - c := by
        simp [u, hr_ne]
      dsimp [F]
      change c + r • u = z
      rw [hscale]
      simp [sub_eq_add_neg]
  simpa [himage] using hpre

/--
%%handwave
name:
  Pointed coordinate annuli are connected
statement:
  A compactly contained pointed coordinate annulus with positive inner radius
  and larger outer radius is preconnected.
proof:
  The coordinate chart identifies the annulus with the ordinary Euclidean
  annulus \(\rho<|z-z(p)|<R\), which is path-connected.  The chart transports
  preconnectedness back to the surface.
-/
theorem pointedCoordinateAnnulus_preconnected
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    (χ : PointedSurfaceCoordinate X p) {ρ R : ℝ}
    (hρ : 0 < ρ) (hρR : ρ < R)
    (hclosed : Metric.closedBall (χ.chart p) R ⊆ χ.chart.target) :
    IsPreconnected (pointedCoordinateAnnulus X χ ρ R) := by
  let A : Set ℂ := {z : ℂ | ρ < ‖z - χ.chart p‖ ∧ ‖z - χ.chart p‖ < R}
  have hA_target : A ⊆ χ.chart.target := by
    intro z hz
    exact hclosed (by
      rw [Metric.mem_closedBall, dist_eq_norm]
      exact le_of_lt hz.2)
  have hU_image :
      pointedCoordinateAnnulus X χ ρ R = χ.chart.symm '' A := by
    ext x
    constructor
    · intro hx
      refine ⟨χ.chart x, ?_, χ.chart.left_inv hx.1⟩
      exact hx.2
    · rintro ⟨z, hz, rfl⟩
      have hz_target : z ∈ χ.chart.target := hA_target hz
      exact ⟨χ.chart.map_target hz_target, by
        simpa [χ.chart.right_inv hz_target] using hz⟩
  rw [hU_image]
  exact (complex_annulus_preconnected (χ.chart p) hρ hρR).image
    χ.chart.symm (χ.chart.continuousOn_symm.mono hA_target)

/--
%%handwave
name:
  Pointed coordinate annuli have compact closure
statement:
  A compactly contained pointed coordinate annulus has compact closure.
proof:
  Its closure is contained in the inverse image of the closed Euclidean
  annulus \(\rho\le |z-z(p)|\le R\).  This closed annulus is compact in the
  plane and lies inside the chart target, so its inverse image under the
  chart is compact on the surface.
-/
theorem pointedCoordinateAnnulus_compact_closure
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    (χ : PointedSurfaceCoordinate X p) {ρ R : ℝ}
    (_hρ : 0 < ρ) (_hρR : ρ < R)
    (hclosed : Metric.closedBall (χ.chart p) R ⊆ χ.chart.target) :
    IsCompact (closure (pointedCoordinateAnnulus X χ ρ R)) := by
  let K : Set X := χ.chart.symm '' Metric.closedBall (χ.chart p) R
  have hU_subset_K :
      pointedCoordinateAnnulus X χ ρ R ⊆ K := by
    intro x hx
    refine ⟨χ.chart x, ?_, ?_⟩
    · exact Metric.ball_subset_closedBall
        (by simpa [Metric.mem_ball, dist_eq_norm] using hx.2.2)
    · exact χ.chart.left_inv hx.1
  have hK_compact : IsCompact K :=
    (isCompact_closedBall (χ.chart p) R).image_of_continuousOn
      (χ.chart.continuousOn_symm.mono hclosed)
  have hclosure_subset_K :
      closure (pointedCoordinateAnnulus X χ ρ R) ⊆ K :=
    closure_minimal hU_subset_K hK_compact.isClosed
  exact hK_compact.of_isClosed_subset isClosed_closure hclosure_subset_K

/--
%%handwave
name:
  Pointed coordinate annuli have nonempty frontier
statement:
  A pointed coordinate annulus with positive inner radius and larger outer
  radius has nonempty frontier.
proof:
  In the chart, either coordinate circle \(|z-z(p)|=\rho\) or
  \(|z-z(p)|=R\) gives a boundary point.  Compact containment of the outer
  ball in the chart target transports such a point back to the surface.
-/
theorem pointedCoordinateAnnulus_frontier_nonempty
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    (χ : PointedSurfaceCoordinate X p) {ρ R : ℝ}
    (hρ : 0 < ρ) (hρR : ρ < R)
    (hclosed : Metric.closedBall (χ.chart p) R ⊆ χ.chart.target) :
    (frontier (pointedCoordinateAnnulus X χ ρ R)).Nonempty := by
  let U : Set X := pointedCoordinateAnnulus X χ ρ R
  let s : ℝ := (ρ + R) / 2
  have hρs : ρ < s := by
    dsimp [s]
    linarith
  have hsR : s < R := by
    dsimp [s]
    linarith
  have hspos : 0 < s := hρ.trans hρs
  let z : ℂ := χ.chart p + (s : ℂ)
  have hz_closed : z ∈ Metric.closedBall (χ.chart p) R := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    calc
      ‖z - χ.chart p‖ = s := by
        simp [z, sub_eq_add_neg, add_comm, add_assoc, hspos.le]
      _ ≤ R := hsR.le
  have hz_target : z ∈ χ.chart.target := hclosed hz_closed
  let x : X := χ.chart.symm z
  have hxsource : x ∈ χ.chart.source := χ.chart.map_target hz_target
  have hchart_x : χ.chart x = z := χ.chart.right_inv hz_target
  have hnorm_x : ‖χ.chart x - χ.chart p‖ = s := by
    rw [hchart_x]
    simp [z, sub_eq_add_neg, add_comm, add_assoc, hspos.le]
  have hU_nonempty : U.Nonempty := by
    refine ⟨x, ?_⟩
    exact ⟨hxsource, by simpa [U, hnorm_x] using ⟨hρs, hsR⟩⟩
  have hp_notU : p ∉ U := by
    intro hpU
    have hpρ : ρ < ‖χ.chart p - χ.chart p‖ := hpU.2.1
    simp at hpρ
    linarith
  by_contra hnot
  have hfrontier_empty : frontier U = ∅ :=
    Set.not_nonempty_iff_eq_empty.mp hnot
  have hU_clopen : IsClopen U :=
    isClopen_iff_frontier_eq_empty.mpr hfrontier_empty
  have hU_univ : U = Set.univ :=
    hU_clopen.eq_univ hU_nonempty
  have hpU : p ∈ U := by
    rw [hU_univ]
    exact Set.mem_univ p
  exact hp_notU hpU

/--
%%handwave
name:
  Pointed coordinate annuli have componentwise maximum-principle geometry
statement:
  A compactly contained pointed coordinate annulus has the componentwise
  geometry needed for the maximum principle.
proof:
  In coordinates, the annulus is a Euclidean annulus.  Its components are
  ordinary annular domains with compact closure and nonempty boundary, and
  the chart transports this geometry back to the surface.
-/
theorem pointedCoordinateAnnulus_hasComponentwiseMaximumPrincipleGeometry
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    (χ : PointedSurfaceCoordinate X p) {ρ R : ℝ}
    (hρ : 0 < ρ) (hρR : ρ < R)
    (hclosed : Metric.closedBall (χ.chart p) R ⊆ χ.chart.target) :
    HasComponentwiseMaximumPrincipleGeometry
      (pointedCoordinateAnnulus X χ ρ R) := by
  exact hasComponentwiseMaximumPrincipleGeometry_of_preconnected
    (pointedCoordinateAnnulus_isOpen X χ ρ R)
    (pointedCoordinateAnnulus_preconnected X χ hρ hρR hclosed)
    (pointedCoordinateAnnulus_compact_closure X χ hρ hρR hclosed)
    (pointedCoordinateAnnulus_frontier_nonempty X χ hρ hρR hclosed)

/--
%%handwave
name:
  Componentwise maximum-principle geometry makes a set open
statement:
  Every set with componentwise maximum-principle geometry is open.
proof:
  Each point lies in an open comparison component contained in the set, so
  each point has a neighborhood contained in the set.
-/
theorem isOpen_of_hasComponentwiseMaximumPrincipleGeometry
    {X : Type} [TopologicalSpace X] {U : Set X}
    (hU_geometry : HasComponentwiseMaximumPrincipleGeometry U) :
    IsOpen U := by
  rw [isOpen_iff_mem_nhds]
  intro x hxU
  rcases hU_geometry x hxU with
    ⟨C, hxC, hC_open, _hC_preconnected, hCU, _hC_compact,
      _hC_frontier_nonempty, _hC_frontier_subset⟩
  exact Filter.mem_of_superset (hC_open.mem_nhds hxC) hCU

/--
%%handwave
name:
  Componentwise subharmonic maximum principle
statement:
  On a region with componentwise maximum-principle geometry, a subharmonic
  function whose frontier values are nonpositive is nonpositive throughout
  the region.
proof:
  Apply the subharmonic maximum principle on the connected comparison
  component through the chosen point.  If a positive superlevel component
  existed, the componentwise geometry would force it to meet the frontier,
  where the assumed nonpositive boundary values rule it out.
-/
theorem subharmonic_nonpositive_of_frontier_nonpositive_componentwise
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    {U : Set X} {w : X → ℝ}
    (hU_geometry : HasComponentwiseMaximumPrincipleGeometry U)
    (hw_cont : ContinuousOn w (closure U))
    (hw_sub : IsSubharmonicOnSurface U w)
    (hboundary : ∀ x ∈ frontier U, w x ≤ 0) :
    ∀ x ∈ U, w x ≤ 0 := by
  intro x hxU
  rcases hU_geometry x hxU with
    ⟨C, hxC, hC_open, hC_preconnected, hCU, hC_compact,
      hC_frontier_nonempty, hC_frontier_subset⟩
  let Ω : PerronDomain X :=
    { carrier := C
      isOpen := hC_open
      nonempty := ⟨x, hxC⟩
      compact_closure := hC_compact }
  have hC_geometry : HasComponentwiseMaximumPrincipleGeometry Ω.carrier :=
    hasComponentwiseMaximumPrincipleGeometry_of_preconnected
      hC_open hC_preconnected hC_compact hC_frontier_nonempty
  have hw_cont_C : ContinuousOn w (closure Ω.carrier) :=
    hw_cont.mono (closure_mono hCU)
  have hw_sub_C : IsSubharmonicOnSurface Ω.carrier w :=
    subharmonicOnSurface_mono hCU hw_sub
  have hboundary_C : ∀ y ∈ Ω.boundary, w y ≤ 0 := by
    intro y hy
    have hyC : y ∈ frontier C := by
      simpa [Ω, PerronDomain.boundary] using hy
    exact hboundary y (hC_frontier_subset hyC)
  exact subharmonic_le_constant_of_boundary_le Ω hC_geometry
    hw_cont_C hw_sub_C hboundary_C x hxC

/--
%%handwave
name:
  Harmonic functions compare with superharmonic majorants on componentwise domains
statement:
  On a domain with componentwise maximum-principle geometry, a harmonic
  function that is bounded by a superharmonic function on the frontier is
  bounded by it throughout the domain.
proof:
  Apply the componentwise maximum principle to \(h-u\).  Since \(h\) is
  harmonic and \(u\) is superharmonic, \(h-u\) is subharmonic; the frontier
  inequality says this subharmonic function is nonpositive on the boundary.
-/
theorem harmonic_le_superharmonic_of_frontier_le_componentwise
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    {U : Set X} {h u : X → ℝ}
    (hU_geometry : HasComponentwiseMaximumPrincipleGeometry U)
    (hharm : IsHarmonicOnSurface U h)
    (hh_cont : ContinuousOn h (closure U))
    (hsuper : IsSuperharmonicOnSurface U u)
    (hu_cont : ContinuousOn u (closure U))
    (hboundary : ∀ x ∈ frontier U, h x ≤ u x) :
    ∀ x ∈ U, h x ≤ u x := by
  have hU_open : IsOpen U :=
    isOpen_of_hasComponentwiseMaximumPrincipleGeometry hU_geometry
  have hh_sub : IsSubharmonicOnSurface U h :=
    harmonicOnSurface_subharmonic hU_open hharm
  have hdiff_sub : IsSubharmonicOnSurface U (fun x ↦ h x - u x) :=
    subharmonicOnSurface_sub_superharmonic hU_open hh_sub hsuper
  have hdiff_cont : ContinuousOn (fun x ↦ h x - u x) (closure U) :=
    hh_cont.sub hu_cont
  have hdiff_boundary : ∀ x ∈ frontier U, h x - u x ≤ 0 := by
    intro x hx
    linarith [hboundary x hx]
  have hdiff_nonpos :
      ∀ x ∈ U, h x - u x ≤ 0 :=
    subharmonic_nonpositive_of_frontier_nonpositive_componentwise
      hU_geometry hdiff_cont hdiff_sub hdiff_boundary
  intro x hx
  linarith [hdiff_nonpos x hx]

/--
%%handwave
name:
  Harmonic-superharmonic comparison on a pointed annulus
statement:
  On a compactly contained pointed coordinate annulus, a harmonic function
  below a superharmonic function on the annulus frontier is below it throughout
  the annulus.
proof:
  Apply the subharmonic maximum principle to the difference of the harmonic
  function and the superharmonic function.
-/
theorem harmonic_le_superharmonic_on_pointedCoordinateAnnulus_of_frontier_le
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    (χ : PointedSurfaceCoordinate X p) {ρ R : ℝ}
    (hρ : 0 < ρ) (hρR : ρ < R)
    (hclosed : Metric.closedBall (χ.chart p) R ⊆ χ.chart.target)
    {h u : X → ℝ}
    (hharm : IsHarmonicOnSurface (pointedCoordinateAnnulus X χ ρ R) h)
    (hcont : ContinuousOn h (closure (pointedCoordinateAnnulus X χ ρ R)))
    (hsuper : IsSuperharmonicOnSurface {x : X | x ≠ p} u)
    (hboundary :
      ∀ x ∈ frontier (pointedCoordinateAnnulus X χ ρ R), h x ≤ u x) :
    ∀ x ∈ pointedCoordinateAnnulus X χ ρ R, h x ≤ u x := by
  let V : Set X := pointedCoordinateAnnulus X χ ρ R
  have hV_open : IsOpen V :=
    pointedCoordinateAnnulus_isOpen X χ ρ R
  have hV_preconnected : IsPreconnected V :=
    pointedCoordinateAnnulus_preconnected X χ hρ hρR hclosed
  have hV_frontier_nonempty : (frontier V).Nonempty :=
    pointedCoordinateAnnulus_frontier_nonempty X χ hρ hρR hclosed
  have hV_subset_punctured : V ⊆ {x : X | x ≠ p} :=
    pointedCoordinateAnnulus_subset_punctured X χ hρ
  have hV_compact : IsCompact (closure V) :=
    pointedCoordinateAnnulus_compact_closure X χ hρ hρR hclosed
  have hV_closure_punctured : closure V ⊆ {x : X | x ≠ p} :=
    pointedCoordinateAnnulus_closure_subset_punctured X χ hρ hρR hclosed
  have hneg_harm : IsHarmonicOnSurface V (fun x : X ↦ -h x) :=
    harmonicOnSurface_neg hharm
  have hneg_cont : ContinuousOn (fun x : X ↦ -h x) (closure V) :=
    hcont.neg
  have hboundary_neg :
      ∀ x ∈ frontier V, -u x ≤ -h x := by
    intro x hx
    linarith [hboundary x hx]
  have hneg_le :
      ∀ x ∈ V, -u x ≤ -h x :=
    hsuper.2 V hV_open hV_preconnected hV_frontier_nonempty
      hV_subset_punctured hV_compact hV_closure_punctured
      (fun x : X ↦ -h x) hneg_harm hneg_cont hboundary_neg
  intro x hx
  have hxle := hneg_le x hx
  linarith

/--
%%handwave
name:
  The annular logarithmic comparator is below on the annulus frontier
statement:
  If a nonnegative superharmonic function is above the prescribed logarithmic
  value on the inner circle, then the annular logarithmic comparator is below
  it on the frontier of the annulus.
proof:
  The frontier is contained in the two coordinate circles.  On the inner
  circle this is the assumed logarithmic lower bound.  On the outer circle the
  comparator is \(0\), and the superharmonic function is nonnegative.
-/
theorem pointedCoordinateAnnularLogComparator_frontier_le
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    (χ : PointedSurfaceCoordinate X p) {ρ R C : ℝ}
    (hρ : 0 < ρ) (hρR : ρ < R)
    (hclosed : Metric.closedBall (χ.chart p) R ⊆ χ.chart.target)
    (u : X → ℝ)
    (hnonneg : ∀ x : X, 0 ≤ u x)
    (hinner :
      ∀ x ∈ χ.chart.source,
        ‖χ.chart x - χ.chart p‖ = ρ →
          -Real.log ρ - C ≤ u x) :
    ∀ x ∈ frontier (pointedCoordinateAnnulus X χ ρ R),
      pointedCoordinateAnnularLogComparator X χ ρ R C x ≤ u x := by
  intro x hxfront
  have hfront :=
    pointedCoordinateAnnulus_frontier_subset_inner_or_outer
      X χ hρ hρR hclosed hxfront
  rcases hfront with ⟨hxsource, hinner_or_outer⟩
  rcases hinner_or_outer with hnorm | hnorm
  · rw [pointedCoordinateAnnularLogComparator_inner_boundary X χ hρ hρR hnorm]
    exact hinner x hxsource hnorm
  · rw [pointedCoordinateAnnularLogComparator_outer_boundary X χ hnorm]
    exact hnonneg x

/--
%%handwave
name:
  Finite annular logarithmic comparison
statement:
  On a coordinate annulus \(\rho<|z-z(p)|<R\), a nonnegative
  superharmonic function whose inner boundary is at least
  \(-\log \rho-C\) dominates the harmonic logarithmic interpolant between
  \(-\log \rho-C\) on the inner circle and \(0\) on the outer circle.
proof:
  The interpolant is harmonic on the annulus.  It is bounded above by the
  superharmonic function on the inner circle by hypothesis and on the outer
  circle by nonnegativity.  The subharmonic-superharmonic comparison principle
  on the annulus gives the inequality in the interior.
-/
theorem nonnegative_superharmonic_logPole_finite_annulus_comparison
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (p : X)
    (χ : PointedSurfaceCoordinate X p) {ρ R C : ℝ}
    (hρ : 0 < ρ) (hρR : ρ < R)
    (hclosed : Metric.closedBall (χ.chart p) R ⊆ χ.chart.target)
    (u : X → ℝ)
    (hnonneg : ∀ x : X, 0 ≤ u x)
    (hsuper : IsSuperharmonicOnSurface {x : X | x ≠ p} u)
    (hinner :
      ∀ x ∈ χ.chart.source,
        ‖χ.chart x - χ.chart p‖ = ρ →
          -Real.log ρ - C ≤ u x) :
    ∀ x ∈ χ.chart.source,
      ρ < ‖χ.chart x - χ.chart p‖ →
        ‖χ.chart x - χ.chart p‖ < R →
          pointedCoordinateAnnularLogComparator X χ ρ R C x ≤ u x := by
  have hcomp_harm :
      IsHarmonicOnSurface (pointedCoordinateAnnulus X χ ρ R)
        (pointedCoordinateAnnularLogComparator X χ ρ R C) :=
    pointedCoordinateAnnularLogComparator_harmonicOn_annulus X χ hρ
  have hcomp_cont :
      ContinuousOn (pointedCoordinateAnnularLogComparator X χ ρ R C)
        (closure (pointedCoordinateAnnulus X χ ρ R)) :=
    pointedCoordinateAnnularLogComparator_continuousOn_closure
      X χ hρ hρR hclosed
  have hboundary :
      ∀ x ∈ frontier (pointedCoordinateAnnulus X χ ρ R),
        pointedCoordinateAnnularLogComparator X χ ρ R C x ≤ u x :=
    pointedCoordinateAnnularLogComparator_frontier_le
      X χ hρ hρR hclosed u hnonneg hinner
  have hcomparison :=
    harmonic_le_superharmonic_on_pointedCoordinateAnnulus_of_frontier_le
      X χ hρ hρR hclosed hcomp_harm hcomp_cont hsuper hboundary
  intro x hxsource hρx hxR
  exact hcomparison x ⟨hxsource, ⟨hρx, hxR⟩⟩

/--
%%handwave
name:
  Limiting annular comparison with a fixed pole constant
statement:
  Fix the logarithmic pole constant \(C\).  If a nonnegative superharmonic
  function is eventually at least \(-\log |z-z(p)|-C\) near the pole, then on
  every smaller point of a fixed coordinate ball it is at least
  \(-\log |z-z(p)|+\log R\).
proof:
  Apply the
  [finite annular comparison](lean:JJMath.Uniformization.nonnegative_superharmonic_logPole_finite_annulus_comparison)
  on annuli whose inner radius \(\rho\) tends to \(0\).  The eventual lower
  bound supplies the inner-circle inequality for all sufficiently small
  \(\rho\).  The logarithmic interpolants converge pointwise to
  \(-\log |z-z(p)|+\log R\).
-/
theorem exists_small_radius_logPole_bound_on_coordinate_circles
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (p : X)
    (χ : PointedSurfaceCoordinate X p) {C : ℝ}
    (u : X → ℝ)
    (hC :
      ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
        -Real.log ‖χ.chart x - χ.chart p‖ - C ≤ u x) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ < δ →
        ∀ y ∈ χ.chart.source,
          ‖χ.chart y - χ.chart p‖ = ρ →
            -Real.log ρ - C ≤ u y := by
  let E : Set X :=
    {y : X | y ∈ χ.chart.source ∩ {x : X | x ≠ p} →
      -Real.log ‖χ.chart y - χ.chart p‖ - C ≤ u y}
  have hnear :
      E ∈ 𝓝 p := by
    simpa [E] using eventually_nhdsWithin_iff.mp hC
  have htarget : χ.chart p ∈ χ.chart.target :=
    χ.chart.map_source χ.base_mem_source
  have hpre_map :
      E ∈ Filter.map χ.chart.symm (𝓝 (χ.chart p)) :=
    χ.chart.continuousAt_symm htarget
      (by simpa [χ.chart.left_inv χ.base_mem_source] using hnear)
  have hpre :
      χ.chart.symm ⁻¹' E ∈ 𝓝 (χ.chart p) := by
    simpa [Filter.mem_map] using hpre_map
  rcases Metric.eventually_nhds_iff.mp hpre with ⟨δ, hδ_pos, hδ⟩
  refine ⟨δ, hδ_pos, ?_⟩
  intro ρ hρ_pos hρδ y hysource hynorm
  have hy_ne : y ≠ p := by
    intro hyp
    have hzero : ‖χ.chart y - χ.chart p‖ = 0 := by
      rw [hyp, sub_self, norm_zero]
    linarith
  have hyball : dist (χ.chart y) (χ.chart p) < δ := by
    simpa [dist_eq_norm, hynorm] using hρδ
  have hsymm_eq : χ.chart.symm (χ.chart y) = y :=
    χ.chart.left_inv hysource
  have hsymm_source : χ.chart.symm (χ.chart y) ∈ χ.chart.source := by
    simpa [hsymm_eq] using hysource
  have hsymm_ne : χ.chart.symm (χ.chart y) ≠ p := by
    simpa [hsymm_eq] using hy_ne
  have hineq :=
    hδ hyball ⟨hsymm_source, hsymm_ne⟩
  simpa [E, hsymm_eq, hynorm] using hineq

/--
%%handwave
name:
  The annular logarithmic comparator has the expected zero-inner-radius limit
statement:
  At a fixed point of the outer coordinate ball, the logarithmic interpolant
  on the annulus tends to \(-\log |z-z(p)|+\log R\) as the inner radius tends
  to zero.
proof:
  Write the comparator as
  \[
    (\log R-\log |z-z(p)|)
    \frac{-\log \rho-C}{\log R-\log \rho}.
  \]
  Since \(-\log \rho\to+\infty\), the quotient tends to \(1\), giving the
  claimed limit.
-/
theorem pointedCoordinateAnnularLogComparator_tendsto_innerRadius_zero
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (p : X)
    (χ : PointedSurfaceCoordinate X p) {R C : ℝ}
    (_hR : 0 < R)
    {x : X} (_hxsource : x ∈ χ.chart.source)
    (_hxR : ‖χ.chart x - χ.chart p‖ < R) (_hxp : x ≠ p) :
    Filter.Tendsto
      (fun ρ : ℝ ↦ pointedCoordinateAnnularLogComparator X χ ρ R C x)
      (𝓝[>] (0 : ℝ))
      (𝓝 (-Real.log ‖χ.chart x - χ.chart p‖ + Real.log R)) := by
  let d : ℝ := ‖χ.chart x - χ.chart p‖
  let a : ℝ := Real.log R - Real.log d
  let b : ℝ := Real.log R
  have ht :
      Filter.Tendsto (fun ρ : ℝ ↦ -Real.log ρ) (𝓝[>] (0 : ℝ)) Filter.atTop := by
    simpa [Function.comp_def] using
      (Filter.tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero)
  have hden :
      Filter.Tendsto (fun ρ : ℝ ↦ -Real.log ρ + b)
        (𝓝[>] (0 : ℝ)) Filter.atTop :=
    ht.atTop_add (tendsto_const_nhds (x := b))
  have hden_pos :
      ∀ᶠ ρ in 𝓝[>] (0 : ℝ), 0 < -Real.log ρ + b :=
    hden.eventually_gt_atTop 0
  have hconst_div :
      Filter.Tendsto (fun ρ : ℝ ↦ (C + b) / (-Real.log ρ + b))
        (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have hratio :
      Filter.Tendsto
        (fun ρ : ℝ ↦ (-Real.log ρ - C) / (-Real.log ρ + b))
        (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hratio₀ :
        Filter.Tendsto
          (fun ρ : ℝ ↦ (-Real.log ρ - C) / (-Real.log ρ + b))
          (𝓝[>] (0 : ℝ)) (𝓝 (1 - 0)) := by
      refine ((tendsto_const_nhds (x := (1 : ℝ))).sub hconst_div).congr' ?_
      filter_upwards [hden_pos] with ρ hρden
      field_simp [hρden.ne']
      ring_nf
    simpa using hratio₀
  have hscaled :
      Filter.Tendsto
        (fun ρ : ℝ ↦ a * ((-Real.log ρ - C) / (-Real.log ρ + b)))
        (𝓝[>] (0 : ℝ)) (𝓝 a) := by
    simpa using tendsto_const_nhds.mul hratio
  have hmain :
      Filter.Tendsto
        (fun ρ : ℝ ↦ pointedCoordinateAnnularLogComparator X χ ρ R C x)
        (𝓝[>] (0 : ℝ)) (𝓝 a) := by
    refine hscaled.congr' ?_
    filter_upwards [hden_pos] with ρ hρden
    dsimp [pointedCoordinateAnnularLogComparator, a, b, d]
    ring_nf
  simpa [a, d, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hmain

/--
%%handwave
name:
  Annular logarithmic comparators approach their limiting barrier
statement:
  Let \(x\ne p\) lie in the coordinate ball of radius \(R>0\), and let
  \(\varepsilon>0\).  For all sufficiently small inner radii
  \(0<\rho<\min\{|z(x)-z(p)|,R\}\),
  \[
    -\log|z(x)-z(p)|+\log R-\varepsilon
      \le A_{\rho,R,C}(x),
  \]
  where \(A_{\rho,R,C}\) is the annular logarithmic comparator.
proof:
  As \(\rho\to0^+\), the comparator at \(x\) tends to
  \(-\log|z(x)-z(p)|+\log R\).  Eventual membership in the interval above
  this limit minus \(\varepsilon\) gives a positive radius threshold.
-/
theorem exists_small_radius_annularLogComparator_limit_sub_epsilon
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (p : X)
    (χ : PointedSurfaceCoordinate X p) {R C : ℝ}
    (hR : 0 < R)
    {x : X} (hxsource : x ∈ χ.chart.source)
    (hxR : ‖χ.chart x - χ.chart p‖ < R) (hxp : x ≠ p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ < δ →
        ρ < ‖χ.chart x - χ.chart p‖ → ρ < R →
          -Real.log ‖χ.chart x - χ.chart p‖ + Real.log R - ε ≤
            pointedCoordinateAnnularLogComparator X χ ρ R C x := by
  let L : ℝ := -Real.log ‖χ.chart x - χ.chart p‖ + Real.log R
  have htend :
      Filter.Tendsto
        (fun ρ : ℝ ↦ pointedCoordinateAnnularLogComparator X χ ρ R C x)
        (𝓝[>] (0 : ℝ)) (𝓝 L) := by
    simpa [L] using
      pointedCoordinateAnnularLogComparator_tendsto_innerRadius_zero
        X p χ hR hxsource hxR hxp
  have hnear_within :
      ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
        L - ε ≤ pointedCoordinateAnnularLogComparator X χ ρ R C x := by
    have hIoi : Set.Ioi (L - ε) ∈ 𝓝 L :=
      Ioi_mem_nhds (by linarith)
    exact (htend.eventually hIoi).mono (by
      intro ρ hρ
      exact le_of_lt hρ)
  have hnear_nhds :
      ∀ᶠ ρ in 𝓝 (0 : ℝ),
        ρ ∈ Set.Ioi (0 : ℝ) →
          L - ε ≤ pointedCoordinateAnnularLogComparator X χ ρ R C x :=
    eventually_nhdsWithin_iff.mp hnear_within
  rcases Metric.eventually_nhds_iff.mp hnear_nhds with ⟨δ, hδ_pos, hδ⟩
  refine ⟨δ, hδ_pos, ?_⟩
  intro ρ hρ_pos hρδ _hρx _hρR
  have hdist : dist ρ (0 : ℝ) < δ := by
    simpa [Real.dist_eq, abs_of_pos hρ_pos] using hρδ
  simpa [L] using hδ hdist (by simpa [Set.mem_Ioi] using hρ_pos)

/--
%%handwave
name:
  An inner circle supporting the annular comparison
statement:
  Suppose \(u\) has the eventual pole bound
  \[
    -\log|z(y)-z(p)|-C\le u(y)
  \]
  near \(p\).  For \(x\ne p\) in the coordinate \(R\)-ball and
  \(\varepsilon>0\), there is
  \(0<\rho<\min\{|z(x)-z(p)|,R\}\) such that the pole bound holds on the
  entire coordinate circle of radius \(\rho\) and
  \[
    -\log|z(x)-z(p)|+\log R-\varepsilon
      \le A_{\rho,R,C}(x).
  \]
proof:
  One sufficiently small radius threshold makes the eventual pole bound
  uniform on coordinate circles; another controls the comparator's limit.
  Choose half the minimum of these thresholds, the distance to \(x\), and
  \(R\).
-/
theorem exists_inner_radius_for_annular_epsilon_comparison
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (p : X)
    (χ : PointedSurfaceCoordinate X p) {R C : ℝ}
    (hR : 0 < R)
    (_hclosed : Metric.closedBall (χ.chart p) R ⊆ χ.chart.target)
    (u : X → ℝ)
    (hC :
      ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
        -Real.log ‖χ.chart x - χ.chart p‖ - C ≤ u x)
    {x : X} (hxsource : x ∈ χ.chart.source)
    (hxR : ‖χ.chart x - χ.chart p‖ < R) (hxp : x ≠ p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ,
      0 < ρ ∧ ρ < ‖χ.chart x - χ.chart p‖ ∧ ρ < R ∧
        (∀ y ∈ χ.chart.source,
          ‖χ.chart y - χ.chart p‖ = ρ →
            -Real.log ρ - C ≤ u y) ∧
          -Real.log ‖χ.chart x - χ.chart p‖ + Real.log R - ε ≤
            pointedCoordinateAnnularLogComparator X χ ρ R C x := by
  rcases exists_small_radius_logPole_bound_on_coordinate_circles
      X p χ u hC with
    ⟨δC, hδC_pos, hδC⟩
  rcases exists_small_radius_annularLogComparator_limit_sub_epsilon
      X p χ hR hxsource hxR hxp hε with
    ⟨δL, hδL_pos, hδL⟩
  have hnorm_pos : 0 < ‖χ.chart x - χ.chart p‖ := by
    refine norm_pos_iff.mpr ?_
    exact sub_ne_zero.mpr (by
      intro hchart
      exact hxp (χ.chart.injOn hxsource χ.base_mem_source hchart))
  let η : ℝ := min (min δC δL) (min ‖χ.chart x - χ.chart p‖ R)
  have hη_pos : 0 < η := by
    dsimp [η]
    exact lt_min (lt_min hδC_pos hδL_pos) (lt_min hnorm_pos hR)
  let ρ : ℝ := η / 2
  have hρ_pos : 0 < ρ := by
    dsimp [ρ]
    linarith
  have hρ_lt_η : ρ < η := by
    dsimp [ρ]
    linarith
  have hη_le_δC : η ≤ δC := by
    dsimp [η]
    exact (min_le_left _ _).trans (min_le_left _ _)
  have hη_le_δL : η ≤ δL := by
    dsimp [η]
    exact (min_le_left _ _).trans (min_le_right _ _)
  have hη_le_norm : η ≤ ‖χ.chart x - χ.chart p‖ := by
    dsimp [η]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hη_le_R : η ≤ R := by
    dsimp [η]
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hρ_lt_δC : ρ < δC := hρ_lt_η.trans_le hη_le_δC
  have hρ_lt_δL : ρ < δL := hρ_lt_η.trans_le hη_le_δL
  have hρ_lt_norm : ρ < ‖χ.chart x - χ.chart p‖ :=
    hρ_lt_η.trans_le hη_le_norm
  have hρ_lt_R : ρ < R := hρ_lt_η.trans_le hη_le_R
  refine ⟨ρ, hρ_pos, hρ_lt_norm, hρ_lt_R, ?_, ?_⟩
  · exact hδC ρ hρ_pos hρ_lt_δC
  · exact hδL ρ hρ_pos hρ_lt_δL hρ_lt_norm hρ_lt_R

/--
%%handwave
name:
  Fixed-ball logarithmic lower bound up to epsilon
statement:
  Let \(u\ge0\) be superharmonic on \(X\setminus\{p\}\) and have at least a
  logarithmic pole at \(p\).  If the closed coordinate \(R\)-ball lies in
  the chart target, then for every \(x\ne p\) in its open ball and every
  \(\varepsilon>0\),
  \[
    -\log|z(x)-z(p)|+\log R-\varepsilon\le u(x).
  \]
proof:
  Choose an inner circle on which the logarithmic pole bound holds and whose
  annular comparator is within \(\varepsilon\) of the limiting barrier.
  Finite-annulus comparison puts that comparator below \(u(x)\).
-/
theorem nonnegative_superharmonic_logPole_annular_fixed_chart_ball_lower_bound_sub_epsilon
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (p : X)
    (χ : PointedSurfaceCoordinate X p) {R C : ℝ}
    (hR : 0 < R)
    (hclosed : Metric.closedBall (χ.chart p) R ⊆ χ.chart.target)
    (u : X → ℝ)
    (hnonneg : ∀ x : X, 0 ≤ u x)
    (hsuper : IsSuperharmonicOnSurface {x : X | x ≠ p} u)
    (hC :
      ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
        -Real.log ‖χ.chart x - χ.chart p‖ - C ≤ u x)
    {x : X} (hxsource : x ∈ χ.chart.source)
    (hxR : ‖χ.chart x - χ.chart p‖ < R) (hxp : x ≠ p)
    {ε : ℝ} (hε : 0 < ε) :
    -Real.log ‖χ.chart x - χ.chart p‖ + Real.log R - ε ≤ u x := by
  rcases exists_inner_radius_for_annular_epsilon_comparison
      X p χ hR hclosed u hC hxsource hxR hxp hε with
    ⟨ρ, hρ_pos, hρx, hρR, hinner, hlimit_lower⟩
  have hfinite :
      pointedCoordinateAnnularLogComparator X χ ρ R C x ≤ u x :=
    nonnegative_superharmonic_logPole_finite_annulus_comparison
      X p χ hρ_pos hρR hclosed u hnonneg hsuper hinner
      x hxsource hρx hxR
  exact hlimit_lower.trans hfinite

/--
%%handwave
name:
  Fixed-ball logarithmic lower bound with a chosen pole constant
statement:
  Under the preceding hypotheses with a fixed eventual pole constant \(C\),
  every \(x\ne p\) in the coordinate \(R\)-ball satisfies
  \[
    -\log|z(x)-z(p)|+\log R\le u(x).
  \]
proof:
  The same inequality holds with an arbitrary positive
  \(\varepsilon\) subtracted from the left-hand side.  Let
  \(\varepsilon\downarrow0\).
-/
theorem nonnegative_superharmonic_logPole_annular_fixed_chart_ball_lower_bound_of_eventual_constant
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (p : X)
    (χ : PointedSurfaceCoordinate X p) {R C : ℝ}
    (hR : 0 < R)
    (hclosed : Metric.closedBall (χ.chart p) R ⊆ χ.chart.target)
    (u : X → ℝ)
    (hnonneg : ∀ x : X, 0 ≤ u x)
    (hsuper : IsSuperharmonicOnSurface {x : X | x ≠ p} u)
    (hC :
      ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
        -Real.log ‖χ.chart x - χ.chart p‖ - C ≤ u x) :
    ∀ x ∈ χ.chart.source,
      ‖χ.chart x - χ.chart p‖ < R →
        x ≠ p →
          -Real.log ‖χ.chart x - χ.chart p‖ + Real.log R ≤ u x := by
  intro x hxsource hxR hxp
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  have hsubε :
      -Real.log ‖χ.chart x - χ.chart p‖ + Real.log R - ε ≤ u x :=
    nonnegative_superharmonic_logPole_annular_fixed_chart_ball_lower_bound_sub_epsilon
      X p χ hR hclosed u hnonneg hsuper hC hxsource hxR hxp hε
  linarith

/--
%%handwave
name:
  Fixed-ball lower barrier for nonnegative logarithmic superharmonic functions
statement:
  Let \(u\ge0\) be superharmonic on \(X\setminus\{p\}\), and suppose that for
  some \(C\),
  \[
    -\log|z(x)-z(p)|-C\le u(x)
  \]
  eventually near \(p\).  If the closed coordinate \(R\)-ball lies in the
  chart target, then throughout its punctured open ball,
  \[
    -\log|z(x)-z(p)|+\log R\le u(x).
  \]
proof:
  Choose the supplied pole constant \(C\) and apply the fixed-constant
  annular comparison result.
-/
theorem nonnegative_superharmonic_logPole_annular_fixed_chart_ball_lower_bound
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (p : X)
    (χ : PointedSurfaceCoordinate X p) {R : ℝ}
    (hR : 0 < R)
    (hclosed : Metric.closedBall (χ.chart p) R ⊆ χ.chart.target) :
    ∀ u : X → ℝ,
      (∀ x : X, 0 ≤ u x) →
        IsSuperharmonicOnSurface {x : X | x ≠ p} u →
          (∃ C : ℝ,
            ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
              -Real.log ‖χ.chart x - χ.chart p‖ - C ≤ u x) →
            ∀ x ∈ χ.chart.source,
              ‖χ.chart x - χ.chart p‖ < R →
                x ≠ p →
                  -Real.log ‖χ.chart x - χ.chart p‖ + Real.log R ≤ u x := by
  intro u hnonneg hsuper hlog
  rcases hlog with ⟨C, hC⟩
  exact
    nonnegative_superharmonic_logPole_annular_fixed_chart_ball_lower_bound_of_eventual_constant
      X p χ hR hclosed u hnonneg hsuper hC

/--
%%handwave
name:
  Annular comparison gives a coordinate-ball lower barrier
statement:
  In a pointed coordinate, every nonnegative superharmonic function with at
  least the standard logarithmic pole dominates one fixed logarithmic lower
  barrier on a sufficiently small coordinate ball.
proof:
  Choose a coordinate ball around the pole and apply
  [the fixed-radius annular comparison theorem](lean:JJMath.Uniformization.nonnegative_superharmonic_logPole_annular_fixed_chart_ball_lower_bound).
  Writing the lower bound as \(-\log |z-z(p)|-A\) just means taking
  \(A=-\log R\).
-/
theorem nonnegative_superharmonic_logPole_annular_uniform_lower_bound_on_chart_ball
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (p : X)
    (χ : PointedSurfaceCoordinate X p) :
    ∃ A R : ℝ, 0 < R ∧
      Metric.closedBall (χ.chart p) R ⊆ χ.chart.target ∧
        ∀ u : X → ℝ,
          (∀ x : X, 0 ≤ u x) →
            IsSuperharmonicOnSurface {x : X | x ≠ p} u →
              (∃ C : ℝ,
                ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
                  -Real.log ‖χ.chart x - χ.chart p‖ - C ≤ u x) →
                ∀ x ∈ χ.chart.source,
                  ‖χ.chart x - χ.chart p‖ < R →
                    x ≠ p →
                      -Real.log ‖χ.chart x - χ.chart p‖ - A ≤ u x := by
  let c : ℂ := χ.chart p
  have hc_target : c ∈ χ.chart.target :=
    χ.chart.map_source χ.base_mem_source
  rcases Metric.mem_nhds_iff.mp (χ.chart.open_target.mem_nhds hc_target) with
    ⟨R₀, hR₀_pos, hball_target⟩
  let R : ℝ := R₀ / 2
  have hR_pos : 0 < R := by
    dsimp [R]
    linarith
  have hR_R₀ : R < R₀ := by
    dsimp [R]
    linarith
  have hclosed_R : Metric.closedBall c R ⊆ χ.chart.target :=
    (Metric.closedBall_subset_ball hR_R₀).trans hball_target
  refine ⟨-Real.log R, R, hR_pos, hclosed_R, ?_⟩
  intro u hnonneg hsuper hlog x hxsource hdist hxp
  have hlower :=
    nonnegative_superharmonic_logPole_annular_fixed_chart_ball_lower_bound
      X p χ hR_pos hclosed_R u hnonneg hsuper hlog x hxsource hdist hxp
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hlower

/--
%%handwave
name:
  Annular comparison gives a neighborhood lower barrier
statement:
  In a pointed coordinate, every nonnegative superharmonic function with at
  least the standard logarithmic pole dominates one fixed logarithmic lower
  barrier near the pole.
proof:
  Use
  [the coordinate-ball lower barrier](lean:JJMath.Uniformization.nonnegative_superharmonic_logPole_annular_uniform_lower_bound_on_chart_ball)
  and take the inverse image of the coordinate ball.
-/
theorem nonnegative_superharmonic_logPole_annular_uniform_lower_bound
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (p : X)
    (χ : PointedSurfaceCoordinate X p) :
    ∃ A : ℝ, ∃ N : Set X,
      IsOpen N ∧ p ∈ N ∧ N ⊆ χ.chart.source ∧
        ∀ u : X → ℝ,
          (∀ x : X, 0 ≤ u x) →
            IsSuperharmonicOnSurface {x : X | x ≠ p} u →
              (∃ C : ℝ,
                ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
                  -Real.log ‖χ.chart x - χ.chart p‖ - C ≤ u x) →
                ∀ x ∈ N, x ≠ p →
                  -Real.log ‖χ.chart x - χ.chart p‖ - A ≤ u x := by
  rcases nonnegative_superharmonic_logPole_annular_uniform_lower_bound_on_chart_ball
      X p χ with
    ⟨A, R, hR_pos, _hclosed, hlower⟩
  let N : Set X := χ.chart.source ∩ χ.chart ⁻¹' Metric.ball (χ.chart p) R
  refine ⟨A, N, ?_, ?_, ?_, ?_⟩
  · exact χ.chart.isOpen_inter_preimage Metric.isOpen_ball
  · exact ⟨χ.base_mem_source, by simp [Metric.mem_ball, hR_pos]⟩
  · intro x hx
    exact hx.1
  · intro u hnonneg hsuper hlog x hxN hxp
    have hdist : ‖χ.chart x - χ.chart p‖ < R := by
      simpa [Metric.mem_ball, dist_eq_norm] using hxN.2
    exact hlower u hnonneg hsuper hlog x hxN.1 hdist hxp

/--
%%handwave
name:
  Singular Perron competitors have a neighborhood lower barrier
statement:
  In every pointed coordinate at the pole, all admissible singular Perron
  competitors dominate one fixed logarithmic lower barrier on a neighborhood
  of the pole.
proof:
  Apply
  [annular comparison for nonnegative superharmonic functions with a logarithmic pole](lean:JJMath.Uniformization.nonnegative_superharmonic_logPole_annular_uniform_lower_bound)
  to each admissible competitor.
-/
theorem greenPerronAdmissible_annular_logarithmic_lower_comparison_on_neighborhood
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (p : X)
    (_hfamily : ∃ u : X → ℝ, IsGreenPerronAdmissible X p u)
    (_hloc :
      ∀ x : X, x ≠ p →
        ∃ U : Set X, x ∈ U ∧ IsOpen U ∧
          ∃ C : ℝ, ∀ u : X → ℝ,
            IsGreenPerronAdmissible X p u → ∀ y ∈ U, u y ≤ C)
    (χ : PointedSurfaceCoordinate X p) :
    ∃ A : ℝ, ∃ N : Set X,
      IsOpen N ∧ p ∈ N ∧ N ⊆ χ.chart.source ∧
        ∀ x ∈ N, x ≠ p →
          ∀ u : X → ℝ,
            IsGreenPerronAdmissible X p u →
              -Real.log ‖χ.chart x - χ.chart p‖ - A ≤ u x := by
  rcases nonnegative_superharmonic_logPole_annular_uniform_lower_bound
      X p χ with
    ⟨A, N, hN_open, hpN, hN_source, hlower⟩
  refine ⟨A, N, hN_open, hpN, hN_source, ?_⟩
  intro x hxN hxp u hu
  exact hlower u hu.1 hu.2.1 (hu.2.2.1 χ) x hxN hxp

/--
%%handwave
name:
  Annular logarithmic comparison gives a uniform lower pole barrier
statement:
  In every pointed coordinate at the pole, all admissible singular Perron
  competitors dominate one fixed logarithmic lower barrier near the pole.
proof:
  Use
  [the neighborhood lower barrier for all admissible competitors](lean:JJMath.Uniformization.greenPerronAdmissible_annular_logarithmic_lower_comparison_on_neighborhood)
  and translate the neighborhood statement into the corresponding eventual
  statement at the pole.
-/
theorem greenPerronAdmissible_annular_logarithmic_lower_comparison
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (p : X)
    (hfamily : ∃ u : X → ℝ, IsGreenPerronAdmissible X p u)
    (hloc :
      ∀ x : X, x ≠ p →
        ∃ U : Set X, x ∈ U ∧ IsOpen U ∧
          ∃ C : ℝ, ∀ u : X → ℝ,
            IsGreenPerronAdmissible X p u → ∀ y ∈ U, u y ≤ C)
    (χ : PointedSurfaceCoordinate X p) :
    ∃ A : ℝ,
      ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
        ∀ u : X → ℝ,
          IsGreenPerronAdmissible X p u →
            -Real.log ‖χ.chart x - χ.chart p‖ - A ≤ u x := by
  rcases greenPerronAdmissible_annular_logarithmic_lower_comparison_on_neighborhood
      X p hfamily hloc χ with
    ⟨A, N, hN_open, hpN, _hN_source, hlower⟩
  refine ⟨A, ?_⟩
  filter_upwards
    [mem_nhdsWithin_of_mem_nhds (hN_open.mem_nhds hpN), self_mem_nhdsWithin]
    with x hxN hxsource
  exact hlower x hxN hxsource.2

/--
%%handwave
name:
  Singular Perron competitors have a uniform logarithmic lower barrier
statement:
  In every pointed coordinate at the pole, all singular Perron admissible
  competitors dominate one fixed logarithmic lower barrier near the pole.
proof:
  Apply the
  [annular logarithmic comparison](lean:JJMath.Uniformization.greenPerronAdmissible_annular_logarithmic_lower_comparison).
-/
theorem greenPerronAdmissible_uniform_logarithmic_lower_barrier_near_pole
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (p : X)
    (hfamily : ∃ u : X → ℝ, IsGreenPerronAdmissible X p u)
    (hloc :
      ∀ x : X, x ≠ p →
        ∃ U : Set X, x ∈ U ∧ IsOpen U ∧
          ∃ C : ℝ, ∀ u : X → ℝ,
            IsGreenPerronAdmissible X p u → ∀ y ∈ U, u y ≤ C)
    (χ : PointedSurfaceCoordinate X p) :
    ∃ A : ℝ,
      ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
        ∀ u : X → ℝ,
          IsGreenPerronAdmissible X p u →
            -Real.log ‖χ.chart x - χ.chart p‖ - A ≤ u x := by
  exact greenPerronAdmissible_annular_logarithmic_lower_comparison
    X p hfamily hloc χ


/--
%%handwave
name:
  The corrected Green Perron envelope is bounded below near the pole
statement:
  In a pointed coordinate at the pole, the singular Perron envelope plus
  \(\log |z-z(p)|\) is bounded below in a punctured neighborhood of the pole.
proof:
  Use the
  [uniform logarithmic lower barrier for all admissible competitors](lean:JJMath.Uniformization.greenPerronAdmissible_uniform_logarithmic_lower_barrier_near_pole).
  Since every admissible value at a nearby point is above this logarithmic
  barrier, the infimum envelope is above it too.  Adding
  \(\log |z-z(p)|\) gives the lower bound for the corrected envelope.
-/
theorem greenPerronEnvelope_corrected_bounded_below_near_pole
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (p : X)
    (hfamily : ∃ u : X → ℝ, IsGreenPerronAdmissible X p u)
    (hloc :
      ∀ x : X, x ≠ p →
        ∃ U : Set X, x ∈ U ∧ IsOpen U ∧
          ∃ C : ℝ, ∀ u : X → ℝ,
            IsGreenPerronAdmissible X p u → ∀ y ∈ U, u y ≤ C)
    (χ : PointedSurfaceCoordinate X p) :
    ∃ A : ℝ,
      ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
        -A ≤ greenPerronEnvelope X p x +
          Real.log ‖χ.chart x - χ.chart p‖ := by
  rcases greenPerronAdmissible_uniform_logarithmic_lower_barrier_near_pole
      X p hfamily hloc χ with
    ⟨A, hA⟩
  refine ⟨A, ?_⟩
  filter_upwards [hA] with x hx
  have hS_nonempty :
      ({a : ℝ | ∃ u : X → ℝ,
        IsGreenPerronAdmissible X p u ∧ a = u x}).Nonempty := by
    rcases hfamily with ⟨u, hu⟩
    exact ⟨u x, u, hu, rfl⟩
  have henv_lower :
      -Real.log ‖χ.chart x - χ.chart p‖ - A ≤
        greenPerronEnvelope X p x := by
    rw [greenPerronEnvelope]
    refine le_csInf hS_nonempty ?_
    intro b hb
    rcases hb with ⟨u, hu, rfl⟩
    exact hx u hu
  linarith






/--
%%handwave
name:
  The singular Perron envelope vanishes at infinity
statement:
  The singular Perron envelope tends to zero along the cocompact filter.
proof:
  The envelope is nonnegative because all admissible competitors are
  nonnegative.  Since the family is nonempty, fix one admissible competitor;
  the envelope is bounded above by that competitor pointwise, and that
  competitor tends to zero at infinity.  The squeeze theorem gives the result.
-/
theorem greenPerronEnvelope_tends_to_zero_at_infinity
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (p : X)
    (hfamily : ∃ u : X → ℝ, IsGreenPerronAdmissible X p u)
    (_hloc :
      ∀ x : X, x ≠ p →
        ∃ U : Set X, x ∈ U ∧ IsOpen U ∧
          ∃ C : ℝ, ∀ u : X → ℝ,
            IsGreenPerronAdmissible X p u → ∀ y ∈ U, u y ≤ C) :
    Filter.Tendsto (greenPerronEnvelope X p) (Filter.cocompact X) (𝓝 0) := by
  rcases hfamily with ⟨u₀, hu₀⟩
  have hnonneg : ∀ x : X, 0 ≤ greenPerronEnvelope X p x :=
    greenPerronEnvelope_nonnegative X p
  have hupper : ∀ x : X, greenPerronEnvelope X p x ≤ u₀ x := by
    intro x
    rw [greenPerronEnvelope]
    refine csInf_le ?_ ⟨u₀, hu₀, rfl⟩
    exact ⟨0, by
      intro a ha
      rcases ha with ⟨u, hu, rfl⟩
      exact hu.1 x⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hu₀.2.2.2 hnonneg hupper










/--
%%handwave
name:
  Local punctured logarithms for Evans potentials
statement:
  Local punctured logarithms for an Evans potential are local holomorphic
  functions on punctured neighborhoods whose real parts are the Evans
  potential.
-/
def EvansPotentialLocalPuncturedLogs
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] {p : X}
    (E : EvansPotentialAt X p) : Prop :=
  ∀ x : X, x ≠ p →
    ∃ U : Set X,
      x ∈ U ∧ IsOpen U ∧ U ⊆ {y : X | y ≠ p} ∧
        ∃ L : X → ℂ,
          MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) L U ∧
            ∀ y ∈ U, (L y).re = E.toFun y

/--
%%handwave
name:
  Evans potentials have local punctured logarithms
statement:
  Around every point away from the logarithmic zero, an Evans potential is the
  real part of a holomorphic function on a punctured neighborhood.
proof:
  Choose a coordinate ball contained in the punctured surface.  Harmonicity of
  the Evans potential on that ball gives a holomorphic harmonic conjugate in
  the coordinate plane, and pulling it back through the chart gives the
  desired local logarithm.
-/
theorem evansPotential_has_local_punctured_logs
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {p : X} (E : EvansPotentialAt X p) :
    EvansPotentialLocalPuncturedLogs X E := by
  intro x hx_punctured
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ x
  have he : e ∈ atlas ℂ X := chart_mem_atlas ℂ x
  have hx_source : x ∈ e.source := by
    simp [e]
  let S : Set ℂ := e.target ∩ e.symm ⁻¹' {y : X | y ≠ p}
  have hS_open : IsOpen S := by
    simpa [S] using e.isOpen_inter_preimage_symm (isOpen_ne (x := p))
  have hexS : e x ∈ S := by
    refine ⟨?_, ?_⟩
    · simp [e]
    · have hsymm : e.symm (e x) = x := e.left_inv hx_source
      simpa [S, hsymm] using hx_punctured
  rcases Metric.isOpen_iff.mp hS_open (e x) hexS with
    ⟨R, hR_pos, hball_subset⟩
  have hcoord_harm :
      InnerProductSpace.HarmonicOnNhd
        (fun z : ℂ ↦ E.toFun (e.symm z)) (Metric.ball (e x) R) :=
    (E.harmonic_away_pole e he).mono (by
      intro z hz
      exact hball_subset hz)
  rcases hcoord_harm.exists_analyticOnNhd_ball_re_eq with
    ⟨F, hF_hol, hF_re⟩
  let U : Set X := e.source ∩ e ⁻¹' Metric.ball (e x) R
  let L : X → ℂ := fun y : X ↦ F (e y)
  have hU_open : IsOpen U := by
    dsimp [U]
    exact e.isOpen_inter_preimage Metric.isOpen_ball
  have hxU : x ∈ U := by
    refine ⟨hx_source, ?_⟩
    simpa using Metric.mem_ball_self (x := e x) hR_pos
  have hU_punctured : U ⊆ {y : X | y ≠ p} := by
    intro y hy
    have hy_source : y ∈ e.source := hy.1
    have hy_ball : e y ∈ Metric.ball (e x) R := hy.2
    have hey_punctured : e.symm (e y) ≠ p :=
      (hball_subset hy_ball).2
    have hsymm : e.symm (e y) = y := e.left_inv hy_source
    simpa [hsymm] using hey_punctured
  have hL_mdiff : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) L U := by
    have hchart :
        MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e U :=
      (mdifferentiableOn_atlas (I := 𝓘(ℂ)) he).mono (by
        intro y hy
        exact hy.1)
    have hF_mdiff :
        MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) F (Metric.ball (e x) R) := by
      exact mdifferentiableOn_iff_differentiableOn.mpr
        hF_hol.differentiableOn
    have hmaps : U ⊆ e ⁻¹' Metric.ball (e x) R := by
      intro y hy
      exact hy.2
    simpa [L, Function.comp_def] using hF_mdiff.comp hchart hmaps
  refine ⟨U, hxU, hU_open, hU_punctured, L, hL_mdiff, ?_⟩
  intro y hy
  have hy_source : y ∈ e.source := hy.1
  have hy_ball : e y ∈ Metric.ball (e x) R := hy.2
  have hsymm : e.symm (e y) = y := e.left_inv hy_source
  calc
    (L y).re = E.toFun (e.symm (e y)) := by
      simpa [L] using hF_re hy_ball
    _ = E.toFun y := by rw [hsymm]

/--
%%handwave
name:
  Chosen Evans punctured logarithm domain
statement:
  From local punctured logarithms of an Evans potential, choose one logarithm
  domain around each punctured point.
-/
noncomputable def evansPotentialLocalPuncturedLogDomain
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {p : X} {E : EvansPotentialAt X p}
    (hlocal : EvansPotentialLocalPuncturedLogs X E)
    (q : {x : X // x ≠ p}) : Set X :=
  Classical.choose (hlocal q.1 q.2)

/--
%%handwave
name:
  Properties of the chosen local Evans logarithm domain
statement:
  For each \(q\ne p\), the chosen set \(U_q\) is an open neighborhood of
  \(q\) contained in \(X\setminus\{p\}\), and there is a holomorphic
  \(L_q:X\to\mathbb C\) on \(U_q\) satisfying
  \[
    \operatorname{Re}L_q(y)=E(y)\qquad(y\in U_q).
  \]
proof:
  These are exactly the properties retained when choosing one witness from
  the local punctured-logarithm hypothesis at \(q\).
-/
theorem evansPotentialLocalPuncturedLogDomain_spec
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {p : X} {E : EvansPotentialAt X p}
    (hlocal : EvansPotentialLocalPuncturedLogs X E)
    (q : {x : X // x ≠ p}) :
    q.1 ∈ evansPotentialLocalPuncturedLogDomain hlocal q ∧
      IsOpen (evansPotentialLocalPuncturedLogDomain hlocal q) ∧
        evansPotentialLocalPuncturedLogDomain hlocal q ⊆
          {y : X | y ≠ p} ∧
          ∃ L : X → ℂ,
            MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) L
              (evansPotentialLocalPuncturedLogDomain hlocal q) ∧
              ∀ y ∈ evansPotentialLocalPuncturedLogDomain hlocal q,
                (L y).re = E.toFun y :=
  Classical.choose_spec (hlocal q.1 q.2)

/--
%%handwave
name:
  Chosen Evans punctured logarithm
statement:
  From local punctured logarithms of an Evans potential, choose one
  holomorphic logarithm around each punctured point.
-/
noncomputable def evansPotentialLocalPuncturedLogFunction
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {p : X} {E : EvansPotentialAt X p}
    (hlocal : EvansPotentialLocalPuncturedLogs X E)
    (q : {x : X // x ≠ p}) : X → ℂ :=
  Classical.choose
    (evansPotentialLocalPuncturedLogDomain_spec hlocal q).2.2.2

/--
%%handwave
name:
  Properties of the chosen local Evans logarithm
statement:
  For every \(q\ne p\), the chosen function \(L_q\) is holomorphic on its
  chosen punctured neighborhood \(U_q\) and satisfies
  \[
    \operatorname{Re}L_q=E\quad\text{on }U_q.
  \]
proof:
  This is the specification of the holomorphic function selected from the
  chosen domain's local-logarithm witness.
-/
theorem evansPotentialLocalPuncturedLogFunction_spec
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {p : X} {E : EvansPotentialAt X p}
    (hlocal : EvansPotentialLocalPuncturedLogs X E)
    (q : {x : X // x ≠ p}) :
    MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ)
      (evansPotentialLocalPuncturedLogFunction hlocal q)
      (evansPotentialLocalPuncturedLogDomain hlocal q) ∧
      ∀ y ∈ evansPotentialLocalPuncturedLogDomain hlocal q,
        (evansPotentialLocalPuncturedLogFunction hlocal q y).re =
          E.toFun y :=
  Classical.choose_spec
    (evansPotentialLocalPuncturedLogDomain_spec hlocal q).2.2.2

/--
%%handwave
name:
  Local punctured exponentials for Evans potentials
statement:
  Local punctured exponentials for an Evans potential are local nonvanishing
  holomorphic functions on punctured neighborhoods whose logarithmic moduli
  are the Evans potential.
-/
def EvansPotentialLocalPuncturedExponentials
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] {p : X}
    (E : EvansPotentialAt X p) : Prop :=
  ∀ x : X, x ≠ p →
    ∃ U : Set X,
      x ∈ U ∧ IsOpen U ∧ U ⊆ {y : X | y ≠ p} ∧
        ∃ F : X → ℂ,
          MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) F U ∧
            (∀ y ∈ U, Real.log ‖F y‖ = E.toFun y) ∧
              ∀ y ∈ U, F y ≠ 0

/--
%%handwave
name:
  Local Evans logarithms exponentiate locally
statement:
  Local holomorphic logarithms with real part equal to an Evans potential
  exponentiate to local nonvanishing holomorphic functions whose logarithmic
  moduli are the Evans potential.
proof:
  Compose each local logarithm with the complex exponential.  Holomorphicity
  follows by composition, nonvanishing from nonvanishing of the exponential,
  and the modulus identity from \(|e^z|=e^{\operatorname{Re}z}\).
-/
theorem evansPotential_local_punctured_logs_exponentiate
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    {p : X} (E : EvansPotentialAt X p)
    (hlocal : EvansPotentialLocalPuncturedLogs X E) :
    EvansPotentialLocalPuncturedExponentials X E := by
  intro x hxp
  rcases hlocal x hxp with
    ⟨U, hxU, hU_open, hU_punctured, L, hL_hol, hL_re⟩
  let F : X → ℂ := fun y : X ↦ Complex.exp (L y)
  have hexp_mdiff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
      (fun z : ℂ ↦ Complex.exp z) := by
    exact mdifferentiable_iff_differentiable.mpr
      (Complex.differentiable_exp (𝕜 := ℂ))
  have hF_hol : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) F U := by
    simpa [F, Function.comp_def] using
      hexp_mdiff.comp_mdifferentiableOn hL_hol
  refine ⟨U, hxU, hU_open, hU_punctured, F, hF_hol, ?_, ?_⟩
  · intro y hy
    simp [F, Complex.norm_exp, hL_re y hy]
  · intro y _hy
    exact Complex.exp_ne_zero (L y)

/--
%%handwave
name:
  Evans pole exponential branch
statement:
  An Evans pole exponential branch is a holomorphic branch through the
  logarithmic zero whose logarithmic modulus is the Evans potential off the
  zero, whose off-zero restriction admits local holomorphic logarithms, and
  whose coordinate expression has a first-order zero at the marked point.
-/
structure EvansPotentialPoleExponentialBranch
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] {p : X}
    (E : EvansPotentialAt X p) where
  domain : Set X
  domain_open : IsOpen domain
  mem_domain : p ∈ domain
  branch : X → ℂ
  branch_holomorphicOn :
    MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) branch domain
  zero_at_zero : branch p = 0
  log_norm_eq :
    ∀ x : X, x ∈ domain → x ≠ p →
      Real.log ‖branch x‖ = E.toFun x
  nonzero_away_zero :
    ∀ x : X, x ∈ domain → x ≠ p → branch x ≠ 0
  local_holomorphic_logs :
    ∀ x : X, x ∈ domain → x ≠ p →
      ∃ U : Set X,
        x ∈ U ∧ IsOpen U ∧ U ⊆ domain ∩ {y : X | y ≠ p} ∧
          ∃ L : X → ℂ,
            MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) L U ∧
              (∀ y ∈ U, (L y).re = E.toFun y) ∧
                ∀ y ∈ U, branch y = Complex.exp (L y)
  zero_factorizations :
    ∀ χ : PointedSurfaceCoordinate X p,
      ∃ r : ℝ,
        0 < r ∧ Metric.ball (χ.chart p) r ⊆ χ.chart.target ∧
          ∃ A : ℂ → ℂ,
            DifferentiableOn ℂ A (Metric.ball (χ.chart p) r) ∧
              A (χ.chart p) ≠ 0 ∧
                ∀ z ∈ Metric.ball (χ.chart p) r,
                  z ≠ χ.chart p →
                    branch (χ.chart.symm z) =
                    (z - χ.chart p) * A z

/--
%%handwave
name:
  Evans logarithmic zero gives a pole exponential branch
statement:
  The logarithmic zero of an Evans potential determines a holomorphic
  exponential branch through the marked point with a simple zero there.
proof:
  In a pointed coordinate, write the removable logarithmic singularity as
  \(E-\log|z-z(p)|=H\).  Choose a holomorphic function with real part \(H\)
  on a small coordinate ball and set \(f=(z-z(p))\exp F\).  Then
  \(\log|f|=E\) off the marked point, \(f\) is nonzero there, and the displayed
  formula is already a first-order factorization.  Changing pointed
  coordinates multiplies the factor by the holomorphic transition divided
  difference, whose value at the base point is nonzero.
-/
theorem evansPotential_poleExponentialBranch
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {p : X} (E : EvansPotentialAt X p) :
    Nonempty (EvansPotentialPoleExponentialBranch X E) := by
  classical
  let χ : PointedSurfaceCoordinate X p :=
    { chart := chartAt ℂ p
      chart_mem_atlas := chart_mem_atlas ℂ p
      base_mem_source := by simp }
  let z₀ : ℂ := χ.chart p
  rcases E.logarithmic_zero χ with ⟨H, hH_harm, hH_eq⟩
  have hH_eq_nhds :
      {x : X |
        x ∈ χ.chart.source ∩ {x : X | x ≠ p} →
          E.toFun x - Real.log ‖χ.chart x - χ.chart p‖ = H x} ∈ 𝓝 p := by
    simpa using eventually_nhdsWithin_iff.mp hH_eq
  rcases mem_nhds_iff.mp hH_eq_nhds with
    ⟨W, hW_subset, hW_open, hpW⟩
  let Scoord : Set ℂ := χ.chart.target ∩ χ.chart.symm ⁻¹' W
  have hScoord_open : IsOpen Scoord := by
    simpa [Scoord] using χ.chart.isOpen_inter_preimage_symm hW_open
  have hz₀_Scoord : z₀ ∈ Scoord := by
    refine ⟨?_, ?_⟩
    · exact χ.chart.map_source χ.base_mem_source
    · simpa [z₀, χ.chart.left_inv χ.base_mem_source] using hpW
  rcases Metric.isOpen_iff.mp hScoord_open z₀ hz₀_Scoord with
    ⟨R, hR_pos, hball_subset_Scoord⟩
  let B : Set ℂ := Metric.ball z₀ R
  have hB_open : IsOpen B := by
    simp [B]
  have hB_target : B ⊆ χ.chart.target := by
    intro z hz
    exact (hball_subset_Scoord (by simpa [B] using hz)).1
  have hB_W : ∀ z ∈ B, χ.chart.symm z ∈ W := by
    intro z hz
    exact (hball_subset_Scoord (by simpa [B] using hz)).2
  have hcoord_harm :
      InnerProductSpace.HarmonicOnNhd
        (fun z : ℂ ↦ H (χ.chart.symm z)) B :=
    (hH_harm χ.chart χ.chart_mem_atlas).mono (by
      intro z hz
      exact ⟨hB_target hz, χ.chart.map_target (hB_target hz)⟩)
  rcases hcoord_harm.exists_analyticOnNhd_ball_re_eq with
    ⟨F, hF_hol, hF_re⟩
  let domain : Set X := χ.chart.source ∩ χ.chart ⁻¹' B
  let branch : X → ℂ := fun x : X ↦
    (χ.chart x - z₀) * Complex.exp (F (χ.chart x))
  have hdomain_open : IsOpen domain := by
    dsimp [domain]
    exact χ.chart.isOpen_inter_preimage hB_open
  have hp_domain : p ∈ domain := by
    refine ⟨χ.base_mem_source, ?_⟩
    simpa [B, z₀] using Metric.mem_ball_self (x := z₀) hR_pos
  have hbranch_hol :
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) branch domain := by
    let C : ℂ → ℂ := fun z : ℂ ↦ (z - z₀) * Complex.exp (F z)
    have hC_diff : DifferentiableOn ℂ C B := by
      dsimp [C]
      exact (differentiableOn_id.sub_const z₀).mul
        hF_hol.differentiableOn.cexp
    have hC_mdiff : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) C B :=
      mdifferentiableOn_iff_differentiableOn.mpr hC_diff
    have hchart :
        MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) χ.chart domain :=
      (mdifferentiableOn_atlas (I := 𝓘(ℂ)) χ.chart_mem_atlas).mono
        (by intro x hx; exact hx.1)
    have hmaps : domain ⊆ χ.chart ⁻¹' B := by
      intro x hx
      exact hx.2
    simpa [branch, C, Function.comp_def] using hC_mdiff.comp hchart hmaps
  have hbranch_zero : branch p = 0 := by
    simp [branch, z₀]
  have hlog_norm :
      ∀ x : X, x ∈ domain → x ≠ p →
        Real.log ‖branch x‖ = E.toFun x := by
    intro x hx hx_ne
    have hx_source : x ∈ χ.chart.source := hx.1
    have hxB : χ.chart x ∈ B := hx.2
    have hxW : x ∈ W := by
      have hsymm : χ.chart.symm (χ.chart x) = x :=
        χ.chart.left_inv hx_source
      simpa [hsymm] using hB_W (χ.chart x) hxB
    have hregular :
        E.toFun x - Real.log ‖χ.chart x - χ.chart p‖ = H x :=
      hW_subset hxW ⟨hx_source, hx_ne⟩
    have hcoord_ne : χ.chart x - z₀ ≠ 0 := by
      intro hzero
      have hx_eq : χ.chart x = χ.chart p := by
        simpa [sub_eq_zero, z₀] using hzero
      exact hx_ne (χ.chart.injOn hx_source χ.base_mem_source hx_eq)
    have hcoord_pos : 0 < ‖χ.chart x - z₀‖ :=
      norm_pos_iff.mpr hcoord_ne
    have hexp_pos : 0 < Real.exp (F (χ.chart x)).re :=
      Real.exp_pos _
    have hF_re_x : (F (χ.chart x)).re = H x := by
      have hsymm : χ.chart.symm (χ.chart x) = x :=
        χ.chart.left_inv hx_source
      simpa [hsymm] using hF_re hxB
    calc
      Real.log ‖branch x‖ =
          Real.log (‖χ.chart x - z₀‖ *
            ‖Complex.exp (F (χ.chart x))‖) := by
        simp [branch]
      _ = Real.log (‖χ.chart x - z₀‖ *
            Real.exp (F (χ.chart x)).re) := by
        rw [Complex.norm_exp]
      _ = Real.log ‖χ.chart x - z₀‖ + (F (χ.chart x)).re := by
        rw [Real.log_mul hcoord_pos.ne' hexp_pos.ne', Real.log_exp]
      _ = Real.log ‖χ.chart x - χ.chart p‖ + H x := by
        rw [hF_re_x]
      _ = E.toFun x := by
        linarith
  have hnonzero :
      ∀ x : X, x ∈ domain → x ≠ p → branch x ≠ 0 := by
    intro x hx hx_ne
    have hx_source : x ∈ χ.chart.source := hx.1
    have hcoord_ne : χ.chart x - z₀ ≠ 0 := by
      intro hzero
      have hx_eq : χ.chart x = χ.chart p := by
        simpa [sub_eq_zero, z₀] using hzero
      exact hx_ne (χ.chart.injOn hx_source χ.base_mem_source hx_eq)
    exact mul_ne_zero hcoord_ne (Complex.exp_ne_zero (F (χ.chart x)))
  have hlocal_logs :
      ∀ x : X, x ∈ domain → x ≠ p →
        ∃ U : Set X,
          x ∈ U ∧ IsOpen U ∧ U ⊆ domain ∩ {y : X | y ≠ p} ∧
            ∃ L : X → ℂ,
              MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) L U ∧
                (∀ y ∈ U, (L y).re = E.toFun y) ∧
                  ∀ y ∈ U, branch y = Complex.exp (L y) := by
    let U₀ : Set X := domain ∩ {y : X | y ≠ p}
    have hU₀_open : IsOpen U₀ :=
      hdomain_open.inter (isOpen_ne (x := p))
    have hbranch_U₀ :
        MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) branch U₀ :=
      hbranch_hol.mono (by intro y hy; exact hy.1)
    have hnonzero_U₀ : ∀ y : X, y ∈ U₀ → branch y ≠ 0 := by
      intro y hy
      exact hnonzero y hy.1 hy.2
    have hlog_U₀ : ∀ y : X, y ∈ U₀ → Real.log ‖branch y‖ = E.toFun y := by
      intro y hy
      exact hlog_norm y hy.1 hy.2
    have hhelper :=
      local_holomorphic_logs_of_nonzero_holomorphic_branch
        hU₀_open hbranch_U₀ hnonzero_U₀ hlog_U₀
    intro x hx hx_ne
    exact hhelper x ⟨hx, hx_ne⟩
  have hfactor :
      ∀ ψ : PointedSurfaceCoordinate X p,
        ∃ r : ℝ,
          0 < r ∧ Metric.ball (ψ.chart p) r ⊆ ψ.chart.target ∧
            ∃ A : ℂ → ℂ,
              DifferentiableOn ℂ A (Metric.ball (ψ.chart p) r) ∧
                A (ψ.chart p) ≠ 0 ∧
                  ∀ z ∈ Metric.ball (ψ.chart p) r,
                    z ≠ ψ.chart p →
                      branch (ψ.chart.symm z) =
                      (z - ψ.chart p) * A z := by
    intro ψ
    let w₀ : ℂ := ψ.chart p
    let T : ℂ → ℂ := fun z : ℂ ↦ χ.chart (ψ.chart.symm z)
    let q : ℂ → ℂ := dslope T w₀
    have hw₀_target : w₀ ∈ ψ.chart.target := by
      dsimp [w₀]
      exact ψ.chart.map_source ψ.base_mem_source
    have hw₀_sourceχ : ψ.chart.symm w₀ ∈ χ.chart.source := by
      dsimp [w₀]
      simpa [ψ.chart.left_inv ψ.base_mem_source] using χ.base_mem_source
    have hT_w₀ : T w₀ = z₀ := by
      dsimp [T, w₀, z₀]
      rw [ψ.chart.left_inv ψ.base_mem_source]
    have hT_an : AnalyticAt ℂ T w₀ := by
      dsimp [T, w₀]
      exact chartTransition_analyticAt ψ.chart ψ.chart_mem_atlas
        χ.chart χ.chart_mem_atlas hw₀_target hw₀_sourceχ
    rcases hT_an.exists_ball_analyticOnNhd with
      ⟨rT, hrT_pos, hT_hol⟩
    have hpre_B : T ⁻¹' B ∈ 𝓝 w₀ := by
      have hT_cont : ContinuousAt T w₀ := hT_an.differentiableAt.continuousAt
      have hTw₀B : T w₀ ∈ B := by
        rw [hT_w₀]
        simpa [B] using Metric.mem_ball_self (x := z₀) hR_pos
      exact hT_cont.preimage_mem_nhds (hB_open.mem_nhds hTw₀B)
    have htarget_nhds : ψ.chart.target ∈ 𝓝 w₀ :=
      ψ.chart.open_target.mem_nhds hw₀_target
    have hballT_nhds : Metric.ball w₀ rT ∈ 𝓝 w₀ :=
      Metric.ball_mem_nhds w₀ hrT_pos
    have hgood_nhds :
        ψ.chart.target ∩ (T ⁻¹' B ∩ Metric.ball w₀ rT) ∈ 𝓝 w₀ :=
      Filter.inter_mem htarget_nhds (Filter.inter_mem hpre_B hballT_nhds)
    rcases Metric.mem_nhds_iff.mp hgood_nhds with
      ⟨r, hr_pos, hball_good⟩
    have hball_target : Metric.ball w₀ r ⊆ ψ.chart.target := by
      intro z hz
      exact (hball_good hz).1
    have hball_T_B : ∀ z ∈ Metric.ball w₀ r, T z ∈ B := by
      intro z hz
      exact (hball_good hz).2.1
    have hball_T_hol : Metric.ball w₀ r ⊆ Metric.ball w₀ rT := by
      intro z hz
      exact (hball_good hz).2.2
    let A : ℂ → ℂ := fun z : ℂ ↦ q z * Complex.exp (F (T z))
    have hT_diff :
        DifferentiableOn ℂ T (Metric.ball w₀ r) :=
      hT_hol.differentiableOn.mono hball_T_hol
    have hq_diff :
        DifferentiableOn ℂ q (Metric.ball w₀ r) := by
      exact (Complex.differentiableOn_dslope
        (Metric.ball_mem_nhds w₀ hr_pos)).mpr hT_diff
    have hF_comp_diff :
        DifferentiableOn ℂ (fun z : ℂ ↦ F (T z)) (Metric.ball w₀ r) :=
      hF_hol.differentiableOn.comp hT_diff (by
        intro z hz
        exact hball_T_B z hz)
    have hA_diff :
        DifferentiableOn ℂ A (Metric.ball w₀ r) := by
      dsimp [A]
      exact hq_diff.mul hF_comp_diff.cexp
    have hq_w₀_ne : q w₀ ≠ 0 := by
      dsimp [q, T, w₀]
      simpa [dslope_same] using
        pointedCoordinate_transition_deriv_ne_zero X χ ψ
    have hA_ne : A w₀ ≠ 0 := by
      dsimp [A]
      rw [hT_w₀]
      exact mul_ne_zero hq_w₀_ne (Complex.exp_ne_zero (F z₀))
    refine ⟨r, hr_pos, by simpa [w₀] using hball_target, A, hA_diff, ?_, ?_⟩
    · simpa [w₀] using hA_ne
    · intro z hz _hz_ne
      have hT_factor :
          T z - z₀ = (z - w₀) * q z := by
        have h := sub_smul_dslope T w₀ z
        simpa [q, smul_eq_mul, hT_w₀] using h.symm
      calc
        branch (ψ.chart.symm z) =
            (T z - z₀) * Complex.exp (F (T z)) := by
          simp [branch, T]
        _ = ((z - w₀) * q z) * Complex.exp (F (T z)) := by
          rw [hT_factor]
        _ = (z - w₀) * A z := by
          ring
        _ = (z - ψ.chart p) * A z := by
          simp [w₀]
  refine ⟨
    { domain := domain
      domain_open := hdomain_open
      mem_domain := hp_domain
      branch := branch
      branch_holomorphicOn := hbranch_hol
      zero_at_zero := hbranch_zero
      log_norm_eq := hlog_norm
      nonzero_away_zero := hnonzero
      local_holomorphic_logs := hlocal_logs
      zero_factorizations := hfactor }⟩

/-- Branch labels for the Evans pole branch and one punctured branch at each punctured point. -/
abbrev EvansPotentialLocalExponentialBranchIndex (X : Type) (p : X) : Type :=
  Unit ⊕ {x : X // x ≠ p}

/-- The concrete domain family associated to an Evans pole branch and chosen punctured logarithms. -/
noncomputable def evansPotentialPolePuncturedBranchDomain
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {p : X} {E : EvansPotentialAt X p}
    (P : EvansPotentialPoleExponentialBranch X E)
    (hlocal : EvansPotentialLocalPuncturedLogs X E) :
    EvansPotentialLocalExponentialBranchIndex X p → Set X
  | Sum.inl _ => P.domain
  | Sum.inr q => evansPotentialLocalPuncturedLogDomain hlocal q

/-- The concrete branch family associated to an Evans pole branch and chosen punctured logarithms. -/
noncomputable def evansPotentialPolePuncturedBranch
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {p : X} {E : EvansPotentialAt X p}
    (P : EvansPotentialPoleExponentialBranch X E)
    (hlocal : EvansPotentialLocalPuncturedLogs X E) :
    EvansPotentialLocalExponentialBranchIndex X p → X → ℂ
  | Sum.inl _ => P.branch
  | Sum.inr q =>
      fun y : X ↦
        Complex.exp (evansPotentialLocalPuncturedLogFunction hlocal q y)

/--
%%handwave
name:
  Local circle transitions for Evans pole and punctured branches
statement:
  The pole branch of an Evans potential and the punctured exponential
  branches have local unit-circle transition constants on every overlap.
proof:
  Away from the marked point, both branches admit holomorphic logarithms with
  the same real part, namely the Evans potential.  Such logarithms differ by
  an imaginary constant on a small connected coordinate disk, so their
  exponentials differ by a unit complex constant.  At the marked point, only
  the pole branch occurs, and the transition is the identity.
-/
def EvansPotentialPolePuncturedBranchesHaveLocalCircleTransitions
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {p : X} {E : EvansPotentialAt X p}
    (P : EvansPotentialPoleExponentialBranch X E)
    (hlocal : EvansPotentialLocalPuncturedLogs X E) : Prop :=
  ∀ i j : EvansPotentialLocalExponentialBranchIndex X p,
    ∀ x : X,
      x ∈ evansPotentialPolePuncturedBranchDomain P hlocal i ∩
          evansPotentialPolePuncturedBranchDomain P hlocal j →
        ∃ U : Set X,
          IsOpen U ∧ x ∈ U ∧
            U ⊆ evansPotentialPolePuncturedBranchDomain P hlocal i ∩
                evansPotentialPolePuncturedBranchDomain P hlocal j ∧
              ∃ γ : Circle,
                ∀ y : X, y ∈ U →
                  evansPotentialPolePuncturedBranch P hlocal j y =
                    (γ : ℂ) *
                      evansPotentialPolePuncturedBranch P hlocal i y

/--
%%handwave
name:
  Local unit-circle transitions between Evans exponential branches
statement:
  Let \(F_0\) be the Evans exponential branch through \(p\), and for each
  \(q\ne p\) let \(F_q=e^{L_q}\) on a chosen punctured neighborhood.
  Whenever two branch domains meet at \(x\), there are a neighborhood
  \(V\) of \(x\) in their overlap and a constant
  \(\gamma\in S^1\) such that
  \[
    F_j(y)=\gamma F_i(y)\qquad(y\in V).
  \]
proof:
  At \(p\), only the pole branch can occur, so take \(\gamma=1\).
  Away from \(p\), both branches admit holomorphic logarithms with common
  real part \(E\).  On a smaller connected neighborhood their difference is
  a constant imaginary number, and exponentiation gives the unit transition
  factor.
-/
theorem evansPotential_polePuncturedBranches_haveLocalCircleTransitions
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {p : X} {E : EvansPotentialAt X p}
    (P : EvansPotentialPoleExponentialBranch X E)
    (hlocal : EvansPotentialLocalPuncturedLogs X E) :
    EvansPotentialPolePuncturedBranchesHaveLocalCircleTransitions
      P hlocal := by
  intro i j x hx
  by_cases hxp : x = p
  · subst hxp
    cases i with
    | inl _ =>
        cases j with
        | inl _ =>
            refine ⟨P.domain, P.domain_open, P.mem_domain, ?_, 1, ?_⟩
            · intro y hy
              simp [evansPotentialPolePuncturedBranchDomain, hy]
            · intro y hy
              simp [evansPotentialPolePuncturedBranch]
        | inr q =>
            have hp_ne :=
              (evansPotentialLocalPuncturedLogDomain_spec hlocal q).2.2.1 hx.2
            exact False.elim (hp_ne rfl)
    | inr q =>
        have hp_ne :=
          (evansPotentialLocalPuncturedLogDomain_spec hlocal q).2.2.1 hx.1
        exact False.elim (hp_ne rfl)
  · have hi_log :
        ∃ U : Set X,
          x ∈ U ∧ IsOpen U ∧
            U ⊆ evansPotentialPolePuncturedBranchDomain P hlocal i ∩
                {y : X | y ≠ p} ∧
              ∃ L : X → ℂ,
                MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) L U ∧
                  (∀ y ∈ U, (L y).re = E.toFun y) ∧
                    ∀ y ∈ U,
                      evansPotentialPolePuncturedBranch P hlocal i y =
                        Complex.exp (L y) := by
      cases i with
      | inl _ =>
          simpa [evansPotentialPolePuncturedBranch,
            evansPotentialPolePuncturedBranchDomain] using
            P.local_holomorphic_logs x hx.1 hxp
      | inr q =>
          refine
            ⟨evansPotentialLocalPuncturedLogDomain hlocal q,
              hx.1,
              (evansPotentialLocalPuncturedLogDomain_spec hlocal q).2.1,
              ?_,
              evansPotentialLocalPuncturedLogFunction hlocal q,
              (evansPotentialLocalPuncturedLogFunction_spec hlocal q).1,
              (evansPotentialLocalPuncturedLogFunction_spec hlocal q).2,
              ?_⟩
          · intro y hy
            exact
              ⟨hy,
                (evansPotentialLocalPuncturedLogDomain_spec hlocal q).2.2.1 hy⟩
          · intro y hy
            rfl
    have hj_log :
        ∃ U : Set X,
          x ∈ U ∧ IsOpen U ∧
            U ⊆ evansPotentialPolePuncturedBranchDomain P hlocal j ∩
                {y : X | y ≠ p} ∧
              ∃ L : X → ℂ,
                MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) L U ∧
                  (∀ y ∈ U, (L y).re = E.toFun y) ∧
                    ∀ y ∈ U,
                      evansPotentialPolePuncturedBranch P hlocal j y =
                        Complex.exp (L y) := by
      cases j with
      | inl _ =>
          simpa [evansPotentialPolePuncturedBranch,
            evansPotentialPolePuncturedBranchDomain] using
            P.local_holomorphic_logs x hx.2 hxp
      | inr q =>
          refine
            ⟨evansPotentialLocalPuncturedLogDomain hlocal q,
              hx.2,
              (evansPotentialLocalPuncturedLogDomain_spec hlocal q).2.1,
              ?_,
              evansPotentialLocalPuncturedLogFunction hlocal q,
              (evansPotentialLocalPuncturedLogFunction_spec hlocal q).1,
              (evansPotentialLocalPuncturedLogFunction_spec hlocal q).2,
              ?_⟩
          · intro y hy
            exact
              ⟨hy,
                (evansPotentialLocalPuncturedLogDomain_spec hlocal q).2.2.1 hy⟩
          · intro y hy
            rfl
    rcases hi_log with
      ⟨Uᵢ, hxUᵢ, hUᵢ_open, hUᵢ_subset, Lᵢ, hLᵢ, hLᵢ_re, hbranchᵢ⟩
    rcases hj_log with
      ⟨Uⱼ, hxUⱼ, hUⱼ_open, hUⱼ_subset, Lⱼ, hLⱼ, hLⱼ_re, hbranchⱼ⟩
    rcases
      local_circle_transition_of_holomorphic_logs
        (u := E.toFun)
        (U₁ := Uᵢ) (U₂ := Uⱼ)
        (L₁ := Lᵢ) (L₂ := Lⱼ)
        (E₁ := evansPotentialPolePuncturedBranch P hlocal i)
        (E₂ := evansPotentialPolePuncturedBranch P hlocal j)
        hUᵢ_open hUⱼ_open hxUᵢ hxUⱼ
        hLᵢ hLⱼ hLᵢ_re hLⱼ_re hbranchᵢ hbranchⱼ with
      ⟨V, hV_open, hxV, hV_subset_logs, γ, hγ⟩
    refine ⟨V, hV_open, hxV, ?_, γ, hγ⟩
    intro y hy
    have hy_logs : y ∈ Uᵢ ∩ Uⱼ := hV_subset_logs hy
    exact ⟨(hUᵢ_subset hy_logs.1).1, (hUⱼ_subset hy_logs.2).1⟩

/--
%%handwave
name:
  Evans local exponential branch atlas
statement:
  An Evans local exponential branch atlas is an open cover by holomorphic
  complex branches with unit-circle transition constants, logarithmic modulus
  equal to the Evans potential away from the marked point, local logarithms on
  the punctured surface, and first-order factorizations for branches through
  the marked point.
-/
structure EvansPotentialLocalExponentialBranchAtlas
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] {p : X}
    (E : EvansPotentialAt X p) where
  branchIndex : Type
  domain : branchIndex → Set X
  domain_open : ∀ i : branchIndex, IsOpen (domain i)
  branch : branchIndex → X → ℂ
  branch_holomorphicOn :
    ∀ i : branchIndex,
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (branch i) (domain i)
  covers : ∀ x : X, ∃ i : branchIndex, x ∈ domain i
  local_transition :
    ∀ i j : branchIndex, ∀ x : X, x ∈ domain i ∩ domain j →
      ∃ U : Set X,
        IsOpen U ∧ x ∈ U ∧ U ⊆ domain i ∩ domain j ∧
          ∃ γ : Circle,
            ∀ y : X, y ∈ U → branch j y = (γ : ℂ) * branch i y
  log_norm_eq :
    ∀ i : branchIndex, ∀ x : X, x ∈ domain i →
      x ≠ p → Real.log ‖branch i x‖ = E.toFun x
  nonzero_away_zero :
    ∀ i : branchIndex, ∀ x : X, x ∈ domain i →
      x ≠ p → branch i x ≠ 0
  local_holomorphic_logs :
    ∀ i : branchIndex, ∀ x : X, x ∈ domain i →
      x ≠ p →
        ∃ U : Set X,
          x ∈ U ∧ IsOpen U ∧ U ⊆ domain i ∩ {y : X | y ≠ p} ∧
            ∃ L : X → ℂ,
              MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) L U ∧
                (∀ y ∈ U, (L y).re = E.toFun y) ∧
                  ∀ y ∈ U, branch i y = Complex.exp (L y)
  zero_at_zero :
    ∀ i : branchIndex, p ∈ domain i → branch i p = 0
  zero_factorizations :
    ∀ i : branchIndex, p ∈ domain i →
      ∀ χ : PointedSurfaceCoordinate X p,
        ∃ r : ℝ,
          0 < r ∧ Metric.ball (χ.chart p) r ⊆ χ.chart.target ∧
            ∃ A : ℂ → ℂ,
              DifferentiableOn ℂ A (Metric.ball (χ.chart p) r) ∧
                A (χ.chart p) ≠ 0 ∧
                  ∀ z ∈ Metric.ball (χ.chart p) r,
                    z ≠ χ.chart p →
                      branch i (χ.chart.symm z) =
                      (z - χ.chart p) * A z

namespace EvansPotentialLocalExponentialBranchAtlas

/--
%%handwave
name:
  Evans local branch atlases give branch systems
statement:
  An Evans local exponential branch atlas canonically packages as a
  holomorphic local branch system with the unit circle acting by
  multiplication.
-/
def toBranchSystem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {p : X} {E : EvansPotentialAt X p}
    (A : EvansPotentialLocalExponentialBranchAtlas X E) :
    AnalyticContinuation.HolomorphicLocalBranchSystem
      Circle X ℂ A.branchIndex where
  act := fun γ z ↦ (γ : ℂ) * z
  act_holomorphic := by
    intro γ
    exact mdifferentiable_iff_differentiable.mpr
      ((differentiable_const (γ : ℂ)).mul differentiable_id)
  act_one := by
    intro z
    simp
  act_mul := by
    intro γ δ z
    simp [mul_assoc]
  domain := A.domain
  domain_open := A.domain_open
  branch := A.branch
  branch_holomorphicOn := A.branch_holomorphicOn
  covers := A.covers

/--
%%handwave
name:
  An Evans branch atlas has local circle transitions
statement:
  The holomorphic branch system associated with an Evans local exponential
  atlas satisfies the local-transition condition: near every point of an
  overlap, one branch is a constant unit complex multiple of the other.
proof:
  Package the open neighborhood, circle constant, and pointwise transition
  equation supplied by the atlas's transition property.
-/
theorem toBranchSystem_hasLocalTransitions
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {p : X} {E : EvansPotentialAt X p}
    (A : EvansPotentialLocalExponentialBranchAtlas X E) :
    A.toBranchSystem.HasLocalTransitions := by
  intro i j x hx
  rcases A.local_transition i j x hx with
    ⟨U, hU_open, hxU, hU_subset, γ, hγ⟩
  exact ⟨
    { neighborhood := U
      neighborhood_open := hU_open
      mem_neighborhood := hxU
      subset_overlap := hU_subset
      transition := γ
      transition_eq := by
        intro y hy
        exact hγ y hy }⟩

end EvansPotentialLocalExponentialBranchAtlas

/--
%%handwave
name:
  Pole and punctured Evans branches form a local exponential branch atlas
statement:
  An Evans pole exponential branch, chosen punctured logarithms, and local
  unit-circle transition constants package as a local exponential branch
  atlas.
proof:
  Use the pole branch as the distinguished branch through the marked point.
  For each punctured point, exponentiate the chosen local logarithm.  The
  logarithmic modulus, nonvanishing, local logarithm, zero value, and
  first-order factorization fields are inherited from the pole branch and the
  chosen logarithm data.  The transition field is exactly the supplied local
  circle-transition datum.
-/
noncomputable def evansPotentialLocalExponentialBranchAtlasOfPoleBranch
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {p : X} {E : EvansPotentialAt X p}
    (P : EvansPotentialPoleExponentialBranch X E)
    (hlocal : EvansPotentialLocalPuncturedLogs X E)
    (htrans :
      EvansPotentialPolePuncturedBranchesHaveLocalCircleTransitions
        P hlocal) :
    EvansPotentialLocalExponentialBranchAtlas X E := by
  classical
  refine
    { branchIndex := EvansPotentialLocalExponentialBranchIndex X p
      domain := evansPotentialPolePuncturedBranchDomain P hlocal
      domain_open := ?_
      branch := evansPotentialPolePuncturedBranch P hlocal
      branch_holomorphicOn := ?_
      covers := ?_
      local_transition := ?_
      log_norm_eq := ?_
      nonzero_away_zero := ?_
      local_holomorphic_logs := ?_
      zero_at_zero := ?_
      zero_factorizations := ?_ }
  · intro i
    cases i with
    | inl _ =>
        simpa [evansPotentialPolePuncturedBranchDomain] using
          P.domain_open
    | inr q =>
        exact (evansPotentialLocalPuncturedLogDomain_spec hlocal q).2.1
  · intro i
    cases i with
    | inl _ =>
        simpa [evansPotentialPolePuncturedBranch,
          evansPotentialPolePuncturedBranchDomain] using
          P.branch_holomorphicOn
    | inr q =>
        have hL :
            MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ)
              (evansPotentialLocalPuncturedLogFunction hlocal q)
              (evansPotentialLocalPuncturedLogDomain hlocal q) :=
          (evansPotentialLocalPuncturedLogFunction_spec hlocal q).1
        have hexp_mdiff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
            (fun z : ℂ ↦ Complex.exp z) := by
          exact mdifferentiable_iff_differentiable.mpr
            (Complex.differentiable_exp (𝕜 := ℂ))
        simpa [evansPotentialPolePuncturedBranch,
          evansPotentialPolePuncturedBranchDomain,
          Function.comp_def] using
          hexp_mdiff.comp_mdifferentiableOn hL
  · intro x
    by_cases hxp : x = p
    · refine ⟨Sum.inl (), ?_⟩
      simpa [evansPotentialPolePuncturedBranchDomain, hxp] using
        P.mem_domain
    · let q : {x : X // x ≠ p} := ⟨x, hxp⟩
      refine ⟨Sum.inr q, ?_⟩
      simpa [evansPotentialPolePuncturedBranchDomain, q] using
        (evansPotentialLocalPuncturedLogDomain_spec hlocal q).1
  · exact htrans
  · intro i x hx hxp
    cases i with
    | inl _ =>
        simpa [evansPotentialPolePuncturedBranch,
          evansPotentialPolePuncturedBranchDomain] using
          P.log_norm_eq x hx hxp
    | inr q =>
        have hLre :
            (evansPotentialLocalPuncturedLogFunction hlocal q x).re =
              E.toFun x :=
          (evansPotentialLocalPuncturedLogFunction_spec hlocal q).2 x hx
        simp [evansPotentialPolePuncturedBranch, Complex.norm_exp, hLre]
  · intro i x hx hxp
    cases i with
    | inl _ =>
        simpa [evansPotentialPolePuncturedBranch,
          evansPotentialPolePuncturedBranchDomain] using
          P.nonzero_away_zero x hx hxp
    | inr q =>
        exact Complex.exp_ne_zero
          (evansPotentialLocalPuncturedLogFunction hlocal q x)
  · intro i x hx hxp
    cases i with
    | inl _ =>
        simpa [evansPotentialPolePuncturedBranch,
          evansPotentialPolePuncturedBranchDomain] using
          P.local_holomorphic_logs x hx hxp
    | inr q =>
        refine
          ⟨evansPotentialLocalPuncturedLogDomain hlocal q,
            hx,
            (evansPotentialLocalPuncturedLogDomain_spec hlocal q).2.1,
            ?_,
            evansPotentialLocalPuncturedLogFunction hlocal q,
            (evansPotentialLocalPuncturedLogFunction_spec hlocal q).1,
            (evansPotentialLocalPuncturedLogFunction_spec hlocal q).2,
            ?_⟩
        · intro y hy
          exact
            ⟨hy,
              (evansPotentialLocalPuncturedLogDomain_spec hlocal q).2.2.1 hy⟩
        · intro y hy
          rfl
  · intro i hp_domain
    cases i with
    | inl _ =>
        simpa [evansPotentialPolePuncturedBranch,
          evansPotentialPolePuncturedBranchDomain] using P.zero_at_zero
    | inr q =>
        have hp_ne : p ≠ p :=
          (evansPotentialLocalPuncturedLogDomain_spec hlocal q).2.2.1 hp_domain
        exact False.elim (hp_ne rfl)
  · intro i hp_domain χ
    cases i with
    | inl _ =>
        exact P.zero_factorizations χ
    | inr q =>
        have hp_ne : p ≠ p :=
          (evansPotentialLocalPuncturedLogDomain_spec hlocal q).2.2.1 hp_domain
        exact False.elim (hp_ne rfl)

/--
%%handwave
name:
  Existence of an Evans local exponential branch atlas
statement:
  If an Evans potential \(E\) has local holomorphic logarithms on
  \(X\setminus\{p\}\), then it admits a local exponential branch atlas whose
  transitions are constant elements of \(S^1\), whose logarithmic modulus is
  \(E\), and whose branch through \(p\) has a simple zero there.
proof:
  Choose the canonical pole exponential branch and exponentiate one chosen
  local logarithm around every punctured point.  Their common real part gives
  the local circle transitions, and the pole branch supplies the
  first-order zero factorization.
-/
theorem evansPotential_localExponentialBranchAtlas
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {p : X} (E : EvansPotentialAt X p)
    (hlocalLogs : EvansPotentialLocalPuncturedLogs X E) :
    Nonempty (EvansPotentialLocalExponentialBranchAtlas X E) := by
  rcases evansPotential_poleExponentialBranch X E with ⟨P⟩
  exact ⟨
    evansPotentialLocalExponentialBranchAtlasOfPoleBranch
      P hlocalLogs
      (evansPotential_polePuncturedBranches_haveLocalCircleTransitions
        X P hlocalLogs)⟩

/--
%%handwave
name:
  Evans potentials exponentiate to plane maps
statement:
  On a simply connected surface, an Evans potential exponentiates to a
  holomorphic map to the complex plane with a simple zero at the marked point.
proof:
  On the punctured surface choose local harmonic conjugates of the Evans
  potential.  The logarithmic singularity has integral period \(2\pi\) around
  the marked point, so the exponential is single-valued around the puncture;
  simple connectedness kills all remaining monodromy.  The local form
  \(\log |z-z(p)|\) makes the exponential extend holomorphically across
  \(p\) with a simple zero.
-/
theorem evansPotential_exponential_planeMap
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [SimplyConnectedSpace X]
    {p : X} (E : EvansPotentialAt X p) :
    Nonempty (EvansPotentialPlaneMap X E) := by
  classical
  let hlocalLogs : EvansPotentialLocalPuncturedLogs X E :=
    evansPotential_has_local_punctured_logs X E
  rcases evansPotential_localExponentialBranchAtlas X E hlocalLogs with
    ⟨A⟩
  let S := A.toBranchSystem
  have htrans : S.HasLocalTransitions := by
    simpa [S] using
      (EvansPotentialLocalExponentialBranchAtlas.toBranchSystem_hasLocalTransitions
        A)
  rcases
    AnalyticContinuation.HolomorphicLocalBranchSystem.exists_singleValuedContinuation_of_simplyConnected_localTransitions
      (S := S) htrans with
    ⟨C⟩
  let F : X → ℂ := C.global
  have hF_hol : HolomorphicMap X ℂ F := by
    simpa [F, S] using
      (AnalyticContinuation.HolomorphicLocalBranchSystem.SingleValuedContinuation.mdifferentiable
        (S := S) C)
  have hlog : ∀ x : X, x ≠ p → Real.log ‖F x‖ = E.toFun x := by
    intro x hxp
    rcases C.local_agreement x with
      ⟨U, _hU_open, hxU, i, γ, hU_domain, hglobal_eq⟩
    have hx_domain : x ∈ A.domain i := by
      simpa [S, EvansPotentialLocalExponentialBranchAtlas.toBranchSystem] using
        hU_domain hxU
    have hglobal : F x = (γ : ℂ) * A.branch i x := by
      simpa [F, S, EvansPotentialLocalExponentialBranchAtlas.toBranchSystem]
        using hglobal_eq x hxU
    calc
      Real.log ‖F x‖ =
          Real.log ‖(γ : ℂ) * A.branch i x‖ := by
        rw [hglobal]
      _ = Real.log ‖A.branch i x‖ := by
        rw [norm_mul, Circle.norm_coe, one_mul]
      _ = E.toFun x := A.log_norm_eq i x hx_domain hxp
  have hzero : ∀ x : X, F x = 0 ↔ x = p := by
    intro x
    constructor
    · intro hxzero
      by_cases hxp : x = p
      · exact hxp
      · rcases C.local_agreement x with
          ⟨U, _hU_open, hxU, i, γ, hU_domain, hglobal_eq⟩
        have hx_domain : x ∈ A.domain i := by
          simpa [S, EvansPotentialLocalExponentialBranchAtlas.toBranchSystem]
            using hU_domain hxU
        have hglobal : F x = (γ : ℂ) * A.branch i x := by
          simpa [F, S, EvansPotentialLocalExponentialBranchAtlas.toBranchSystem]
            using hglobal_eq x hxU
        have hF_ne : F x ≠ 0 := by
          rw [hglobal]
          exact mul_ne_zero (Circle.coe_ne_zero γ)
            (A.nonzero_away_zero i x hx_domain hxp)
        exact False.elim (hF_ne hxzero)
    · intro hxp
      rcases C.local_agreement p with
        ⟨U, _hU_open, hpU, i, γ, hU_domain, hglobal_eq⟩
      have hp_domain : p ∈ A.domain i := by
        simpa [S, EvansPotentialLocalExponentialBranchAtlas.toBranchSystem] using
          hU_domain hpU
      have hglobal : F p = (γ : ℂ) * A.branch i p := by
        simpa [F, S, EvansPotentialLocalExponentialBranchAtlas.toBranchSystem]
          using hglobal_eq p hpU
      simpa [hxp] using by
        rw [hglobal, A.zero_at_zero i hp_domain, mul_zero]
  have hsimple :
      ∀ χ : PointedSurfaceCoordinate X p,
        surfaceComplexDerivativeInCoordinate χ F ≠ 0 := by
    intro χ
    rcases C.local_agreement p with
      ⟨U, hU_open, hpU, i, γ, hU_domain, hglobal_eq⟩
    have hp_domain : p ∈ A.domain i := by
      simpa [S, EvansPotentialLocalExponentialBranchAtlas.toBranchSystem] using
        hU_domain hpU
    rcases A.zero_factorizations i hp_domain χ with
      ⟨r₀, hr₀_pos, _hball₀_target, Afac, hAfac_diff,
        hAfac_ne, hfactor⟩
    let V : Set ℂ := χ.chart.target ∩ χ.chart.symm ⁻¹' U
    have hV_open : IsOpen V := by
      simpa [V] using χ.chart.isOpen_inter_preimage_symm hU_open
    have hpV : χ.chart p ∈ V := by
      refine ⟨?_, ?_⟩
      · exact χ.chart.map_source χ.base_mem_source
      · simpa [V, χ.chart.left_inv χ.base_mem_source] using hpU
    rcases Metric.isOpen_iff.mp hV_open (χ.chart p) hpV with
      ⟨r₁, hr₁_pos, hball₁_subset⟩
    let r : ℝ := min r₀ r₁
    have hr_pos : 0 < r := lt_min hr₀_pos hr₁_pos
    let Aunit : ℂ → ℂ := fun z : ℂ ↦ (γ : ℂ) * Afac z
    have hball_r_r₀ : Metric.ball (χ.chart p) r ⊆ Metric.ball (χ.chart p) r₀ := by
      intro z hz
      exact Metric.mem_ball.mpr
        (lt_of_lt_of_le (Metric.mem_ball.mp hz) (min_le_left r₀ r₁))
    have hball_r_r₁ : Metric.ball (χ.chart p) r ⊆ Metric.ball (χ.chart p) r₁ := by
      intro z hz
      exact Metric.mem_ball.mpr
        (lt_of_lt_of_le (Metric.mem_ball.mp hz) (min_le_right r₀ r₁))
    have hAunit_diff :
        DifferentiableOn ℂ Aunit (Metric.ball (χ.chart p) r) :=
      (hAfac_diff.mono hball_r_r₀).const_mul (γ : ℂ)
    have hAunit_ne : Aunit (χ.chart p) ≠ 0 := by
      exact mul_ne_zero (Circle.coe_ne_zero γ) hAfac_ne
    have hlocal :
        (fun z : ℂ ↦ F (χ.chart.symm z))
          =ᶠ[𝓝 (χ.chart p)]
        (fun z : ℂ ↦ (z - χ.chart p) * Aunit z) := by
      filter_upwards [Metric.ball_mem_nhds (χ.chart p) hr_pos] with z hz
      have hz₀ : z ∈ Metric.ball (χ.chart p) r₀ := hball_r_r₀ hz
      have hz₁ : z ∈ Metric.ball (χ.chart p) r₁ := hball_r_r₁ hz
      have hzU : χ.chart.symm z ∈ U := (hball₁_subset hz₁).2
      by_cases hz_center : z = χ.chart p
      · subst hz_center
        have hsymm :
            χ.chart.symm (χ.chart p) = p :=
          χ.chart.left_inv χ.base_mem_source
        have hglobal_p : F p = (γ : ℂ) * A.branch i p := by
          simpa [F, S, EvansPotentialLocalExponentialBranchAtlas.toBranchSystem]
            using hglobal_eq p hpU
        calc
          F (χ.chart.symm (χ.chart p)) = F p := by rw [hsymm]
          _ = (γ : ℂ) * A.branch i p := hglobal_p
          _ = 0 := by rw [A.zero_at_zero i hp_domain, mul_zero]
          _ = (χ.chart p - χ.chart p) * Aunit (χ.chart p) := by simp
      · have hglobal_z :
            F (χ.chart.symm z) =
              (γ : ℂ) * A.branch i (χ.chart.symm z) := by
          simpa [F, S, EvansPotentialLocalExponentialBranchAtlas.toBranchSystem]
            using hglobal_eq (χ.chart.symm z) hzU
        calc
          F (χ.chart.symm z) =
              (γ : ℂ) * A.branch i (χ.chart.symm z) := hglobal_z
          _ = (γ : ℂ) * ((z - χ.chart p) * Afac z) := by
            rw [hfactor z hz₀ hz_center]
          _ = (z - χ.chart p) * Aunit z := by
            ring
    have hz_ball : χ.chart p ∈ Metric.ball (χ.chart p) r := by
      simpa using Metric.mem_ball_self (x := χ.chart p) hr_pos
    have hAunit_at : DifferentiableAt ℂ Aunit (χ.chart p) :=
      hAunit_diff.differentiableAt (Metric.isOpen_ball.mem_nhds hz_ball)
    have hderiv_left :
        deriv (fun z : ℂ ↦ F (χ.chart.symm z)) (χ.chart p) =
        deriv (fun z : ℂ ↦ (z - χ.chart p) * Aunit z) (χ.chart p) :=
      hlocal.deriv_eq
    have hfirst :
        DifferentiableAt ℂ (fun z : ℂ ↦ z - χ.chart p) (χ.chart p) :=
      differentiableAt_id.sub_const _
    have hderiv_right :
        deriv (fun z : ℂ ↦ (z - χ.chart p) * Aunit z) (χ.chart p) =
          Aunit (χ.chart p) := by
      rw [deriv_fun_mul hfirst hAunit_at]
      simp
    have hderiv :
        surfaceComplexDerivativeInCoordinate χ F =
          Aunit (χ.chart p) := by
      simpa [surfaceComplexDerivativeInCoordinate] using
        hderiv_left.trans hderiv_right
    simpa [hderiv] using hAunit_ne
  exact ⟨
    { toFun := F
      holomorphic := hF_hol
      log_norm_eq := hlog
      zero_fiber := hzero
      simple_zero := hsimple }⟩

/--
%%handwave
name:
  Evans-potential growth makes the associated plane map proper
statement:
  A holomorphic plane map whose logarithmic modulus is an Evans potential, and
  whose only zero is the logarithmic zero of that potential, is proper.
proof:
  Outside the zero, preimages of closed disks are sublevel sets of the Evans
  potential.  The zero is adjoined explicitly in the compact-sublevel property,
  so compact subsets of the plane have compact preimage.
-/
theorem planeMap_isProper_of_log_norm_evansPotential
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {p : X} (E : EvansPotentialAt X p) (F : X → ℂ)
    (hF : HolomorphicMap X ℂ F)
    (hlog : ∀ x : X, x ≠ p → Real.log ‖F x‖ = E.toFun x)
    (hzero : ∀ x : X, F x = 0 ↔ x = p) :
    IsProperMap F := by
  classical
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨hF.continuous, ?_⟩
  intro K hK
  rcases hK.isBounded.subset_closedBall_lt (0 : ℝ) (0 : ℂ) with
    ⟨R, hR_pos, hK_bound⟩
  let a : ℝ := Real.log R
  let C : Set X := {p} ∪ {x : X | E.toFun x ≤ a}
  have hpre_subset : F ⁻¹' K ⊆ C := by
    intro x hxK
    by_cases hxp : x = p
    · exact Or.inl hxp
    · right
      have hxnorm_le : ‖F x‖ ≤ R := by
        have hxclosed : F x ∈ Metric.closedBall (0 : ℂ) R := hK_bound hxK
        simpa [Metric.mem_closedBall, dist_eq_norm] using hxclosed
      have hxF_ne_zero : F x ≠ 0 := by
        intro hxzero
        exact hxp ((hzero x).mp hxzero)
      have hxnorm_pos : 0 < ‖F x‖ := norm_pos_iff.mpr hxF_ne_zero
      have hlog_le : Real.log ‖F x‖ ≤ Real.log R :=
        Real.log_le_log hxnorm_pos hxnorm_le
      dsimp [a]
      simpa [hlog x hxp] using hlog_le
  have hpre_closed : IsClosed (F ⁻¹' K) :=
    hK.isClosed.preimage hF.continuous
  exact IsCompact.of_isClosed_subset
    (by simpa [C, a] using E.compact_sublevel_with_zero a)
    hpre_closed hpre_subset

/--
%%handwave
name:
  Evans plane maps are proper
statement:
  The holomorphic plane map associated to an Evans potential is proper.
proof:
  This is the properness criterion for
  [plane maps controlled by an Evans potential](lean:JJMath.Uniformization.planeMap_isProper_of_log_norm_evansPotential).
-/
theorem EvansPotentialPlaneMap.isProper
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {p : X} {E : EvansPotentialAt X p}
    (F : EvansPotentialPlaneMap X E) :
    IsProperMap F.toFun := by
  exact planeMap_isProper_of_log_norm_evansPotential X E F.toFun
    F.holomorphic F.log_norm_eq F.zero_fiber

/--
%%handwave
name:
  A proper holomorphic plane map with one simple zero has degree one
statement:
  A proper holomorphic map to the complex plane whose fiber over \(0\) consists
  of one simple zero has degree one.
proof:
  Proper holomorphic maps between Riemann surfaces have constant
  finite degree.  The fiber over \(0\) consists of a single simple point, so the
  global degree is one.
-/
theorem proper_holomorphicPlaneMap_degree_one_of_simple_single_zero
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {p : X} (F : X → ℂ)
    (hF : HolomorphicMap X ℂ F)
    (hproper : IsProperMap F)
    (hzero : ∀ x : X, F x = 0 ↔ x = p)
    (hsimple : ∀ χ : PointedSurfaceCoordinate X p,
      surfaceComplexDerivativeInCoordinate χ F ≠ 0) :
    ∀ z : ℂ, ∃! x : X, F x = z := by
  classical
  have hφ_open : Topology.IsOpenEmbedding (fun z : ℂ ↦ z) := by
    simpa [id] using
      (Topology.IsOpenEmbedding.id : Topology.IsOpenEmbedding (id : ℂ → ℂ))
  have _hp_multiplicity_one :
      ∀ χ : PointedSurfaceCoordinate X p,
        holomorphicMapLocalMultiplicityAtValueInCoordinate χ F 0 = 1 := by
    intro χ
    exact
      holomorphicMapLocalMultiplicityAtValueInCoordinate_eq_one_of_deriv_ne_zero
        χ hF ((hzero p).mpr rfl) (hsimple χ)
  simpa using
    proper_holomorphicMap_degree_one_of_simple_single_zero_to_openComplexModel
      (X := X) (Y := ℂ) (p := p) (F := F) (φ := fun z : ℂ ↦ z)
      hφ_open hF hproper hzero _hp_multiplicity_one

/--
%%handwave
name:
  Evans plane maps have degree one
statement:
  The proper holomorphic plane map associated to an Evans potential has degree
  one.
proof:
  Apply the degree-one criterion for
  [proper holomorphic plane maps with one simple zero](lean:JJMath.Uniformization.proper_holomorphicPlaneMap_degree_one_of_simple_single_zero).
-/
theorem EvansPotentialPlaneMap.degree_one
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {p : X} {E : EvansPotentialAt X p}
    (F : EvansPotentialPlaneMap X E)
    (hproper : IsProperMap F.toFun) :
    ∀ z : ℂ, ∃! x : X, F.toFun x = z := by
  exact proper_holomorphicPlaneMap_degree_one_of_simple_single_zero
    X F.toFun F.holomorphic hproper F.zero_fiber F.simple_zero

/--
%%handwave
name:
  Degree-one holomorphic plane maps are unbranched
statement:
  A holomorphic map to the complex plane whose fibers all consist of one point
  has no critical points.
proof:
  Degree one gives injectivity.  An injective holomorphic map has no critical
  points, because a critical point has a genuine local branch form and hence
  cannot be locally injective.
-/
theorem degree_one_holomorphicPlaneMap_unbranched
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (F : X → ℂ)
    (hF : HolomorphicMap X ℂ F)
    (hdegree : ∀ z : ℂ, ∃! x : X, F x = z) :
    ∀ x : X, ∀ χx : PointedSurfaceCoordinate X x,
      surfaceComplexDerivativeInCoordinate χx F ≠ 0 := by
  classical
  have _hinjective : Function.Injective F :=
    (bijective_of_existsUnique_preimage hdegree).1
  intro x χx
  exact
    injective_holomorphicMap_surfaceComplexDerivative_ne_zero
      χx hF _hinjective

/--
%%handwave
name:
  Proper degree-one holomorphic plane maps are unbranched
statement:
  A proper holomorphic map to the complex plane of degree one has no critical
  points.
proof:
  This is the unbranchedness of degree-one holomorphic plane maps; properness
  is part of the standard source theorem that supplies degree one, but is not
  needed after degree one is known.
-/
theorem proper_degree_one_holomorphicPlaneMap_unbranched
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (F : X → ℂ)
    (hF : HolomorphicMap X ℂ F)
    (_hproper : IsProperMap F)
    (hdegree : ∀ z : ℂ, ∃! x : X, F x = z) :
    ∀ x : X, ∀ χx : PointedSurfaceCoordinate X x,
      surfaceComplexDerivativeInCoordinate χx F ≠ 0 :=
  degree_one_holomorphicPlaneMap_unbranched X F hF hdegree

/--
%%handwave
name:
  Unbranched holomorphic plane maps are local homeomorphisms
statement:
  A holomorphic map from a Riemann surface to the complex plane whose
  coordinate derivative is nonzero at every point is a local homeomorphism.
proof:
  In a source coordinate the map is a holomorphic function of one complex
  variable with nonzero derivative.  The inverse function theorem gives a
  local inverse in the coordinate plane, and composing with the source chart
  gives a local homeomorphism on the surface.
-/
theorem unbranched_holomorphicPlaneMap_isLocalHomeomorph
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (F : X → ℂ)
    (hF : HolomorphicMap X ℂ F)
    (hunbranched : ∀ x : X, ∀ χx : PointedSurfaceCoordinate X x,
      surfaceComplexDerivativeInCoordinate χx F ≠ 0) :
    IsLocalHomeomorph F := by
  classical
  refine IsLocalHomeomorph.mk F ?_
  intro x
  let χx : PointedSurfaceCoordinate X x :=
    { chart := chartAt ℂ x
      chart_mem_atlas := chart_mem_atlas ℂ x
      base_mem_source := mem_chart_source ℂ x }
  let e : OpenPartialHomeomorph X ℂ := χx.chart
  let a : ℂ := e x
  let fcoord : ℂ → ℂ := fun z : ℂ ↦ F (e.symm z)
  have ha_target : a ∈ e.target := by
    dsimp [a, e, χx]
    exact (chartAt ℂ x).map_source (mem_chart_source ℂ x)
  have hdiff_on : DifferentiableOn ℂ fcoord e.target := by
    simpa [fcoord, e] using
      differentiableOn_surfaceCoordinate_symm
        (X := X) hF χx
  have hcontdiff_on :
      ContDiffOn ℂ (1 : WithTop ℕ∞) fcoord e.target :=
    hdiff_on.contDiffOn e.open_target
  have hcontdiff_at :
      ContDiffAt ℂ (1 : WithTop ℕ∞) fcoord a :=
    hcontdiff_on.contDiffAt (e.open_target.mem_nhds ha_target)
  have hdiff_at : DifferentiableAt ℂ fcoord a :=
    (hdiff_on a ha_target).differentiableAt
      (e.open_target.mem_nhds ha_target)
  have hderiv_at : HasDerivAt fcoord (deriv fcoord a) a :=
    hdiff_at.hasDerivAt
  have hstrict : HasStrictDerivAt fcoord (deriv fcoord a) a :=
    hcontdiff_at.hasStrictDerivAt' hderiv_at one_ne_zero
  have hderiv_ne : deriv fcoord a ≠ 0 := by
    simpa [surfaceComplexDerivativeInCoordinate, χx, e, a, fcoord] using
      hunbranched x χx
  let einv : OpenPartialHomeomorph ℂ ℂ :=
    (hstrict.hasStrictFDerivAt_equiv hderiv_ne).toOpenPartialHomeomorph
      fcoord
  have ha_einv : a ∈ einv.source := by
    simpa [einv] using
      HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source
        (hstrict.hasStrictFDerivAt_equiv hderiv_ne)
  let E : OpenPartialHomeomorph X ℂ := e.trans einv
  refine ⟨E, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.trans_source]
    exact ⟨χx.base_mem_source, ha_einv⟩
  · intro y hy
    have hy_source : y ∈ e.source := by
      have hy_e_trans : y ∈ (e.trans einv).source := hy
      rw [OpenPartialHomeomorph.trans_source] at hy_e_trans
      exact hy_e_trans.1
    calc
      F y = einv (e y) := by
        simp [einv, fcoord, e.left_inv hy_source]
      _ = E y := rfl

/--
%%handwave
name:
  Inverses of bijective unbranched plane maps are holomorphic
statement:
  The inverse homeomorphism of a bijective unbranched holomorphic map from a
  Riemann surface to the complex plane is holomorphic.
proof:
  Around each image point, use the one-variable inverse function theorem in a
  source coordinate.  The resulting holomorphic inverse branch agrees with the
  global inverse because the original map is injective.
-/
theorem bijective_unbranched_holomorphicPlaneMap_inverse_holomorphic
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (F : X → ℂ)
    (hF : HolomorphicMap X ℂ F)
    (hunbranched : ∀ x : X, ∀ χx : PointedSurfaceCoordinate X x,
      surfaceComplexDerivativeInCoordinate χx F ≠ 0)
    (hinj : Function.Injective F)
    (hsurj : Function.Surjective F) :
    HolomorphicMap ℂ X
      ((unbranched_holomorphicPlaneMap_isLocalHomeomorph X F hF hunbranched).toHomeomorphOfBijective
        ⟨hinj, hsurj⟩).symm := by
  classical
  let hlocal : IsLocalHomeomorph F :=
    unbranched_holomorphicPlaneMap_isLocalHomeomorph X F hF hunbranched
  let H : X ≃ₜ ℂ :=
    hlocal.toHomeomorphOfBijective ⟨hinj, hsurj⟩
  change MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H.symm
  intro z
  let x : X := H.symm z
  have hxF : F x = z := by
    change H x = z
    exact H.apply_symm_apply z
  let χx : PointedSurfaceCoordinate X x :=
    { chart := chartAt ℂ x
      chart_mem_atlas := chart_mem_atlas ℂ x
      base_mem_source := mem_chart_source ℂ x }
  let e : OpenPartialHomeomorph X ℂ := χx.chart
  let a : ℂ := e x
  let fcoord : ℂ → ℂ := fun w : ℂ ↦ F (e.symm w)
  have ha_target : a ∈ e.target := by
    dsimp [a, e, χx]
    exact (chartAt ℂ x).map_source (mem_chart_source ℂ x)
  have hfa : fcoord a = z := by
    have hleft : e.symm (e x) = x := e.left_inv χx.base_mem_source
    simpa [fcoord, a, hleft] using hxF
  have hdiff_on : DifferentiableOn ℂ fcoord e.target := by
    simpa [fcoord, e] using
      differentiableOn_surfaceCoordinate_symm
        (X := X) hF χx
  have hcontdiff_on :
      ContDiffOn ℂ (1 : WithTop ℕ∞) fcoord e.target :=
    hdiff_on.contDiffOn e.open_target
  have hcontdiff_at :
      ContDiffAt ℂ (1 : WithTop ℕ∞) fcoord a :=
    hcontdiff_on.contDiffAt (e.open_target.mem_nhds ha_target)
  have hdiff_at : DifferentiableAt ℂ fcoord a :=
    (hdiff_on a ha_target).differentiableAt
      (e.open_target.mem_nhds ha_target)
  have hderiv_at : HasDerivAt fcoord (deriv fcoord a) a :=
    hdiff_at.hasDerivAt
  have hstrict : HasStrictDerivAt fcoord (deriv fcoord a) a :=
    hcontdiff_at.hasStrictDerivAt' hderiv_at one_ne_zero
  have hderiv_ne : deriv fcoord a ≠ 0 := by
    simpa [surfaceComplexDerivativeInCoordinate, χx, e, a, fcoord] using
      hunbranched x χx
  let einv : OpenPartialHomeomorph ℂ ℂ :=
    (hstrict.hasStrictFDerivAt_equiv hderiv_ne).toOpenPartialHomeomorph
      fcoord
  have ha_einv : a ∈ einv.source := by
    simpa [einv] using
      HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source
        (hstrict.hasStrictFDerivAt_equiv hderiv_ne)
  have hinv_strict :
      HasStrictDerivAt einv.symm (deriv fcoord a)⁻¹ (fcoord a) := by
    simpa [einv] using hstrict.to_localInverse hderiv_ne
  have hinv_diff_at_z : DifferentiableAt ℂ einv.symm z := by
    have hinv_diff_at_fa : DifferentiableAt ℂ einv.symm (fcoord a) :=
      hinv_strict.hasDerivAt.differentiableAt
    simpa [hfa] using hinv_diff_at_fa
  have hinv_mdiff_at_z :
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) einv.symm z :=
    hinv_diff_at_z.mdifferentiableAt
  have hinv_at_z : einv.symm z = a := by
    have hleft : einv.symm (einv a) = a := einv.left_inv ha_einv
    simpa [einv, hfa] using hleft
  have he_symm_mdiff_at_a :
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) e.symm a :=
    mdifferentiableAt_atlas_symm χx.chart_mem_atlas ha_target
  have he_symm_mdiff :
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) e.symm (einv.symm z) := by
    simpa [hinv_at_z] using he_symm_mdiff_at_a
  let branch : ℂ → X :=
    fun w : ℂ ↦ e.symm (einv.symm w)
  have hbranch_mdiff :
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) branch z := by
    simpa [branch] using
      he_symm_mdiff.comp z hinv_mdiff_at_z
  have hright :
      ∀ᶠ w in 𝓝 (fcoord a), fcoord (einv.symm w) = w := by
    filter_upwards
      [einv.open_target.mem_nhds (einv.map_source ha_einv)] with w hw
    exact einv.right_inv hw
  have hright_at_z :
      ∀ᶠ w in 𝓝 z, fcoord (einv.symm w) = w := by
    simpa [hfa] using hright
  have hevent :
      (fun w : ℂ ↦ H.symm w) =ᶠ[𝓝 z] branch := by
    filter_upwards [hright_at_z] with w hw
    have hFbranch : F (branch w) = w := by
      simpa [branch, fcoord] using hw
    have hHbranch : H (branch w) = w := by
      simpa [H, hlocal] using hFbranch
    exact (H.symm_apply_eq).2 hHbranch.symm
  exact hbranch_mdiff.congr_of_eventuallyEq hevent

/--
%%handwave
name:
  Bijective unbranched holomorphic plane maps are biholomorphic
statement:
  A bijective holomorphic map from a Riemann surface to the complex
  plane, with nonzero derivative everywhere, is biholomorphic.
proof:
  The local inverse theorem gives holomorphic inverse branches.  Bijectivity
  glues these local branches into the inverse homeomorphism, hence the inverse
  is holomorphic.
-/
theorem biholomorphicToComplexPlane_of_bijective_unbranched_holomorphicPlaneMap
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (F : X → ℂ)
    (hF : HolomorphicMap X ℂ F)
    (hunbranched : ∀ x : X, ∀ χx : PointedSurfaceCoordinate X x,
      surfaceComplexDerivativeInCoordinate χx F ≠ 0)
    (hinj : Function.Injective F)
    (hsurj : Function.Surjective F) :
    BiholomorphicToComplexPlane X := by
  let hloc : IsLocalHomeomorph F :=
    unbranched_holomorphicPlaneMap_isLocalHomeomorph X F hF hunbranched
  let e : X ≃ₜ ℂ :=
    hloc.toHomeomorphOfBijective ⟨hinj, hsurj⟩
  refine ⟨{
    toHomeomorph := e
    holomorphic_toFun := ?_
    holomorphic_invFun := ?_
  }⟩
  · simpa [e, hloc] using hF
  · simpa [e, hloc] using
      bijective_unbranched_holomorphicPlaneMap_inverse_holomorphic
        X F hF hunbranched hinj hsurj

/--
%%handwave
name:
  Degree-one plane maps are biholomorphic
statement:
  A degree-one holomorphic map from a Riemann surface to the complex
  plane is a biholomorphic equivalence.
proof:
  Degree one gives bijectivity and makes the map unbranched.
  Then use the local inverse theorem for
  [bijective unbranched holomorphic plane maps](lean:JJMath.Uniformization.biholomorphicToComplexPlane_of_bijective_unbranched_holomorphicPlaneMap).
-/
theorem degree_one_holomorphicPlaneMap_biholomorphic
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (F : X → ℂ)
    (hF : HolomorphicMap X ℂ F)
    (hdegree : ∀ z : ℂ, ∃! x : X, F x = z) :
    BiholomorphicToComplexPlane X := by
  have hunbranched :
      ∀ x : X, ∀ χx : PointedSurfaceCoordinate X x,
        surfaceComplexDerivativeInCoordinate χx F ≠ 0 :=
    degree_one_holomorphicPlaneMap_unbranched X F hF hdegree
  have hbij : Function.Bijective F :=
    bijective_of_existsUnique_preimage hdegree
  exact biholomorphicToComplexPlane_of_bijective_unbranched_holomorphicPlaneMap
    X F hF hunbranched hbij.1 hbij.2

/--
%%handwave
name:
  Proper degree-one plane maps are biholomorphic
statement:
  A proper degree-one holomorphic map from a Riemann surface to the
  complex plane is a biholomorphic equivalence.
proof:
  Once degree one is known, properness is no longer used; apply the
  degree-one biholomorphism criterion.
-/
theorem proper_degree_one_holomorphicPlaneMap_biholomorphic
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (F : X → ℂ)
    (hF : HolomorphicMap X ℂ F)
    (_hproper : IsProperMap F)
    (hdegree : ∀ z : ℂ, ∃! x : X, F x = z) :
    BiholomorphicToComplexPlane X :=
  degree_one_holomorphicPlaneMap_biholomorphic X F hF hdegree

/--
%%handwave
name:
  Evans potentials uniformize parabolic simply connected surfaces
statement:
  A simply connected surface carrying an Evans potential is biholomorphic to
  the complex plane.
proof:
  Exponentiate the Evans potential and its harmonic conjugate to obtain a
  holomorphic map to the complex plane.  The growth of the potential at
  infinity makes this map proper, and the logarithmic zero gives degree one.
  A proper degree-one holomorphic plane map is biholomorphic.
-/
theorem evansPotential_biholomorphic_complexPlane
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [SimplyConnectedSpace X]
    {p : X} (E : EvansPotentialAt X p) :
    BiholomorphicToComplexPlane X := by
  rcases evansPotential_exponential_planeMap X E with ⟨F⟩
  have hproper : IsProperMap F.toFun :=
    F.isProper X
  have hdegree : ∀ z : ℂ, ∃! x : X, F.toFun x = z :=
    F.degree_one X hproper
  exact degree_one_holomorphicPlaneMap_biholomorphic
    X F.toFun F.holomorphic hdegree

/--
%%handwave
name:
  An Evans potential uniformizes a simply connected surface by the plane
statement:
  A simply connected Riemann surface carrying an Evans potential at
  some point is biholomorphic to the complex plane.
proof:
  Choose the Evans potential and apply the Evans-potential plane-map
  construction: exponentiate a harmonic conjugate, use properness from growth
  at infinity, and use the logarithmic zero to get degree one.
-/
theorem simplyConnected_evansPotential_biholomorphic_complexPlane
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [SimplyConnectedSpace X]
    (hE : ∃ p : X, Nonempty (EvansPotentialAt X p)) :
    BiholomorphicToComplexPlane X := by
  rcases hE with ⟨p, hEp⟩
  rcases hEp with ⟨E⟩
  exact evansPotential_biholomorphic_complexPlane X E



/--
%%handwave
name:
  Some-pole dichotomy from Evans potentials
statement:
  Suppose every noncompact potential-theoretically parabolic simply connected
  surface carries an Evans potential at some point.  Then a noncompact simply
  connected surface either has a Green function for at least one pole or is
  biholomorphic to the complex plane.
proof:
  If some Green function exists, this is the first alternative.  Otherwise the
  surface is potential-theoretically parabolic by definition.  The assumed
  Evans potential then uniformizes the simply connected surface by the complex
  plane.
-/
theorem simplyConnected_potentialTheoretic_dichotomy_some_of_evansPotential
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [SimplyConnectedSpace X]
    (_hnoncompact : ¬ CompactSpace X)
    (hevans :
      IsPotentialTheoreticallyParabolic X →
        ∃ p : X, Nonempty (EvansPotentialAt X p)) :
    (∃ p : X, Nonempty (GreenFunctionWithPole X p)) ∨
      BiholomorphicToComplexPlane X := by
  by_cases hgreen : ∃ p : X, Nonempty (GreenFunctionWithPole X p)
  · exact Or.inl hgreen
  · refine Or.inr ?_
    have hparabolic : IsPotentialTheoreticallyParabolic X := by
      intro p hp
      exact hgreen ⟨p, hp⟩
    exact simplyConnected_evansPotential_biholomorphic_complexPlane X
      (hevans hparabolic)



/--
%%handwave
name:
  Hyperbolic simply connected surfaces have a Green pole from Evans potentials
statement:
  Suppose every potential-theoretically parabolic simply connected surface
  carries an Evans potential at some point.  Then a simply connected surface
  in the hyperbolic case has a Green function for at least one pole.
proof:
  Apply the some-pole potential-theoretic dichotomy with the assumed
  Evans-potential supply in the parabolic alternative.  The plane alternative
  contradicts the hyperbolic-case hypothesis, so the Green-function
  alternative remains.
-/
theorem simplyConnected_hyperbolic_case_has_some_greenFunction_of_evansPotential
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [SimplyConnectedSpace X]
    (hcase : IsSimplyConnectedHyperbolicCase X)
    (hevans :
      IsPotentialTheoreticallyParabolic X →
        ∃ p : X, Nonempty (EvansPotentialAt X p)) :
    ∃ p : X, Nonempty (GreenFunctionWithPole X p) := by
  rcases simplyConnected_potentialTheoretic_dichotomy_some_of_evansPotential
      X hcase.1 hevans with hgreen | hplane
  · exact hgreen
  · exact False.elim (hcase.2 hplane)


/--
%%handwave
name:
  Green functions have compact-superlevel Green data
statement:
  A Green function with pole \(p\) gives compact-superlevel Green data with
  the same function and logarithmic singularity.
proof:
  Forget only the separate cocompact convergence-to-zero field; all remaining
  fields are part of the Green function structure.
-/
def GreenFunctionWithPole.toCompactSuperlevel
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {p : X}
    (G : GreenFunctionWithPole X p) :
    CompactSuperlevelGreenFunctionWithPole X p where
  toFun := G.toFun
  positive_away_pole := G.positive_away_pole
  harmonic_away_pole := G.harmonic_away_pole
  tends_to_infinity_at_pole := G.tends_to_infinity_at_pole
  logarithmic_singularity := G.logarithmic_singularity
  compact_positive_superlevel := G.compact_positive_superlevel

/--
%%handwave
name:
  Compact positive superlevels force decay to zero at infinity
statement:
  Let \(G:X\to\mathbb R\) satisfy \(G(x)>0\) for \(x\ne p\).  If
  \[
    \{p\}\cup\{x:G(x)\ge a\}
  \]
  is compact for every \(a>0\), then
  \[
    G(x)\longrightarrow0
    \quad\text{along the cocompact filter of }X.
  \]
proof:
  Outside the compact singleton \(\{p\}\), positivity gives every prescribed
  negative lower bound near zero.  For \(a>0\), outside the compact
  \(a\)-superlevel set one has \(G<a\).  These two estimates are the order
  criterion for convergence to zero.
-/
theorem tendsto_zero_at_infinity_of_positive_away_pole_compact_positive_superlevel
    {X : Type} [TopologicalSpace X] {p : X} {G : X → ℝ}
    (hpositive : ∀ x : X, x ≠ p → 0 < G x)
    (hcompact : ∀ a : ℝ, 0 < a → IsCompact ({p} ∪ {x : X | a ≤ G x})) :
    Filter.Tendsto G (Filter.cocompact X) (𝓝 0) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    have hp_compact : IsCompact ({p} : Set X) := isCompact_singleton
    filter_upwards [hp_compact.compl_mem_cocompact] with x hx
    have hxp : x ≠ p := by
      intro hxp
      exact hx (by simp [hxp])
    exact ha.trans (hpositive x hxp)
  · intro a ha
    have hK : IsCompact ({p} ∪ {x : X | a ≤ G x}) :=
      hcompact a ha
    refine Filter.mem_of_superset hK.compl_mem_cocompact ?_
    intro x hxK
    have hnot_ge : ¬ a ≤ G x := by
      intro hge
      exact hxK (Or.inr hge)
    exact lt_of_not_ge hnot_ge

/--
Compact-superlevel Green data upgrades to a full Green function because its
compact positive superlevels force vanishing at infinity.
-/
def CompactSuperlevelGreenFunctionWithPole.toGreenFunction
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] {p : X}
    (G : CompactSuperlevelGreenFunctionWithPole X p) :
    GreenFunctionWithPole X p where
  toFun := G.toFun
  positive_away_pole := G.positive_away_pole
  harmonic_away_pole := G.harmonic_away_pole
  tends_to_infinity_at_pole := G.tends_to_infinity_at_pole
  logarithmic_singularity := G.logarithmic_singularity
  tends_to_zero_at_infinity :=
    tendsto_zero_at_infinity_of_positive_away_pole_compact_positive_superlevel
      G.positive_away_pole G.compact_positive_superlevel
  compact_positive_superlevel := G.compact_positive_superlevel

/--
%%handwave
name:
  Disk map associated to a Green function
statement:
  A pointed disk map is associated to a Green function with pole \(p\) when
  its modulus is \(\exp(-G)\) away from \(p\), its only zero is \(p\), and the
  zero at \(p\) is simple.
-/
def IsGreenFunctionExponentialPointedDiskMap
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] {p : X}
    (G : GreenFunctionWithPole X p)
    (F : PointedHolomorphicMap X Complex.UnitDisc p 0) : Prop :=
  (∀ x : X, x ≠ p → Real.log ‖((F.toFun x : Complex.UnitDisc) : ℂ)‖ = -G.toFun x) ∧
    (∀ x : X, (((F.toFun x : Complex.UnitDisc) : ℂ) = 0) ↔ x = p) ∧
      ∀ χ : PointedSurfaceCoordinate X p,
        surfaceComplexDerivativeInCoordinate χ
          (fun x : X ↦ ((F.toFun x : Complex.UnitDisc) : ℂ)) ≠ 0

/--
%%handwave
name:
  Green functions exponentiate to pointed disk maps
statement:
  On a simply connected surface, the Green function with pole \(p\)
  exponentiates to a holomorphic map to the unit disk, sending \(p\) to zero.
proof:
  On the punctured surface choose local harmonic conjugates of the Green
  function.  Around the pole the conjugate has period \(2\pi\), exactly the
  period killed by the exponential.  Since the original surface is simply
  connected, the remaining monodromy vanishes.  Thus
  \(\exp(-G-iG^*)\) is a single-valued holomorphic disk map, and the
  logarithmic pole makes the zero at \(p\) simple.
-/
theorem greenFunction_exponential_pointedDiskMap
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [SimplyConnectedSpace X]
    {p : X} (G : GreenFunctionWithPole X p) :
    ∃ F : PointedHolomorphicMap X Complex.UnitDisc p 0,
      IsGreenFunctionExponentialPointedDiskMap X G F := by
  let Gc : CompactSuperlevelGreenFunctionWithPole X p :=
    G.toCompactSuperlevel
  rcases compactSuperlevelGreenFunction_exponential_pointedDiskMap X Gc with
    ⟨F, hF⟩
  refine ⟨F, ?_⟩
  simpa [Gc, GreenFunctionWithPole.toCompactSuperlevel,
    IsGreenFunctionExponentialPointedDiskMap,
    IsCompactSuperlevelGreenFunctionExponentialPointedDiskMap] using hF

/--
%%handwave
name:
  Green functions exponentiate from zero first cohomology
statement:
  Let a simply connected Riemann surface carry a Green function with pole
  \(p\) and a pointed smooth exhaustion by connected domains containing
  \(p\) and having vanishing first real de Rham cohomology.  Then the Green
  function exponentiates to a holomorphic map to the unit disk, sending
  \(p\) to zero.
proof:
  Apply the Green-function exponentiation theorem on the ambient simply
  connected surface.  Simple connectedness kills the non-pole monodromy and
  the logarithmic \(2\pi\)-period is killed by exponentiation.  The connected
  zero-cohomology exhaustion is used in the preceding construction rather
  than in this final exponentiation step.
-/
theorem greenFunction_exponential_pointedDiskMap_of_pointedH1Zero_exhaustion
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [SimplyConnectedSpace X] {p : X}
    (_E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p)
    (G : GreenFunctionWithPole X p) :
    ∃ F : PointedHolomorphicMap X Complex.UnitDisc p 0,
      IsGreenFunctionExponentialPointedDiskMap X G F := by
  exact greenFunction_exponential_pointedDiskMap X G

/--
%%handwave
name:
  Green-function modulus makes the pointed disk map proper
statement:
  A pointed disk map whose logarithmic modulus is \(-G\), for a Green function
  \(G\), is proper.
proof:
  Compact subsets of the unit disk are contained in a closed subdisk
  \(\{|z|\le r\}\) with \(r<1\).  The logarithmic modulus identity turns the
  preimage of such a subdisk into the positive superlevel set
  \(G\ge-\log r\), together with the pole.  This set is compact by the
  compact-superlevel field of the Green function.
-/
theorem pointedDiskMap_isProper_of_greenFunction_modulus
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {p : X} (G : GreenFunctionWithPole X p)
    (F : PointedHolomorphicMap X Complex.UnitDisc p 0)
    (hlog : ∀ x : X, x ≠ p →
      Real.log ‖((F.toFun x : Complex.UnitDisc) : ℂ)‖ = -G.toFun x)
    (hzero : ∀ x : X, (((F.toFun x : Complex.UnitDisc) : ℂ) = 0) ↔ x = p) :
    IsProperMap F.toFun := by
  classical
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨F.holomorphic.continuous, ?_⟩
  intro K hK
  rcases compact_unitDisc_subset_closed_norm_lt_one hK with
    ⟨r, hr_pos, hr_lt_one, hK_norm⟩
  let a : ℝ := -Real.log r
  have ha : 0 < a := by
    dsimp [a]
    exact neg_pos.mpr (Real.log_neg hr_pos hr_lt_one)
  let C : Set X := {p} ∪ {x : X | a ≤ G.toFun x}
  have hpre_subset : F.toFun ⁻¹' K ⊆ C := by
    intro x hxK
    by_cases hxp : x = p
    · exact Or.inl hxp
    · right
      have hxnorm_le :
          ‖((F.toFun x : Complex.UnitDisc) : ℂ)‖ ≤ r :=
        hK_norm (F.toFun x) hxK
      have hxF_ne_zero : ((F.toFun x : Complex.UnitDisc) : ℂ) ≠ 0 := by
        intro hxzero
        exact hxp ((hzero x).mp hxzero)
      have hxnorm_pos : 0 < ‖((F.toFun x : Complex.UnitDisc) : ℂ)‖ :=
        norm_pos_iff.mpr hxF_ne_zero
      have hlog_le :
          Real.log ‖((F.toFun x : Complex.UnitDisc) : ℂ)‖ ≤ Real.log r :=
        Real.log_le_log hxnorm_pos hxnorm_le
      have hneg_le : -G.toFun x ≤ Real.log r := by
        simpa [hlog x hxp] using hlog_le
      dsimp [a]
      linarith
  have hpre_closed : IsClosed (F.toFun ⁻¹' K) :=
    hK.isClosed.preimage F.holomorphic.continuous
  exact IsCompact.of_isClosed_subset
    (by simpa [C, a] using G.compact_positive_superlevel a ha)
    hpre_closed hpre_subset

/--
%%handwave
name:
  Green function disk maps are proper
statement:
  The disk map obtained from a Green function is proper.
proof:
  Apply the properness criterion for
  [pointed disk maps controlled by a Green function](lean:JJMath.Uniformization.pointedDiskMap_isProper_of_greenFunction_modulus).
-/
theorem greenFunction_pointedDiskMap_isProper
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {p : X} (G : GreenFunctionWithPole X p)
    (F : PointedHolomorphicMap X Complex.UnitDisc p 0)
    (hF : IsGreenFunctionExponentialPointedDiskMap X G F) :
    IsProperMap F.toFun := by
  exact pointedDiskMap_isProper_of_greenFunction_modulus
    X G F hF.1 hF.2.1

/--
%%handwave
name:
  A proper pointed disk map with one simple zero has degree one
statement:
  A proper pointed holomorphic disk map whose fiber over \(0\) consists of one
  simple zero has degree one.
proof:
  Proper holomorphic maps between Riemann surfaces have constant
  finite degree.  The fiber over \(0\) consists of the single marked point, and
  the derivative condition says that this point contributes multiplicity one.
-/
theorem proper_pointedDiskMap_degree_one_of_simple_single_zero
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {p : X} (F : PointedHolomorphicMap X Complex.UnitDisc p 0)
    (hproper : IsProperMap F.toFun)
    (hzero : ∀ x : X, (((F.toFun x : Complex.UnitDisc) : ℂ) = 0) ↔ x = p)
    (hsimple : ∀ χ : PointedSurfaceCoordinate X p,
      surfaceComplexDerivativeInCoordinate χ
        (fun x : X ↦ ((F.toFun x : Complex.UnitDisc) : ℂ)) ≠ 0) :
    ∀ z : Complex.UnitDisc, ∃! x : X, F.toFun x = z := by
  classical
  have hφ_open :
      Topology.IsOpenEmbedding (fun z : Complex.UnitDisc ↦ (z : ℂ)) := by
    simpa using
      ((Metric.isOpen_ball : IsOpen (Metric.ball (0 : ℂ) 1)).isOpenEmbedding_subtypeVal)
  have _hp_multiplicity_one :
      ∀ χ : PointedSurfaceCoordinate X p,
        holomorphicMapLocalMultiplicityAtValueInCoordinate χ
          (fun x : X ↦ ((F.toFun x : Complex.UnitDisc) : ℂ)) 0 = 1 := by
    intro χ
    exact
      holomorphicMapLocalMultiplicityAtValueInCoordinate_eq_one_of_deriv_ne_zero
        χ F.holomorphic_coe_unitDisc ((hzero p).mpr rfl) (hsimple χ)
  exact
    proper_holomorphicMap_degree_one_of_simple_single_zero_to_openComplexModel
      (X := X) (Y := Complex.UnitDisc) (p := p) (F := F.toFun)
      (φ := fun z : Complex.UnitDisc ↦ (z : ℂ))
      hφ_open F.holomorphic_coe_unitDisc hproper hzero _hp_multiplicity_one

/--
%%handwave
name:
  Green function disk maps have degree one
statement:
  The proper disk map obtained from a Green function has topological degree
  one.
proof:
  Apply the degree-one criterion for
  [proper pointed disk maps with one simple zero](lean:JJMath.Uniformization.proper_pointedDiskMap_degree_one_of_simple_single_zero).
-/
theorem greenFunction_pointedDiskMap_has_degree_one
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {p : X} (G : GreenFunctionWithPole X p)
    (F : PointedHolomorphicMap X Complex.UnitDisc p 0)
    (hF : IsGreenFunctionExponentialPointedDiskMap X G F)
    (hproper : IsProperMap F.toFun) :
    ∀ z : Complex.UnitDisc, ∃! x : X, F.toFun x = z := by
  exact proper_pointedDiskMap_degree_one_of_simple_single_zero
    X F hproper hF.2.1 hF.2.2

/--
%%handwave
name:
  Degree-one pointed disk maps are unbranched
statement:
  A pointed holomorphic disk map whose fibers all consist of one point has no
  critical points.
proof:
  Degree one gives injectivity.  The complex coordinate of an injective
  holomorphic disk map is injective, so the local branch obstruction rules out
  critical points.
-/
theorem degree_one_pointedDiskMap_unbranched
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    (F : PointedHolomorphicMap X Complex.UnitDisc p 0)
    (hdegree : ∀ z : Complex.UnitDisc, ∃! x : X, F.toFun x = z) :
    ∀ x : X, ∀ χx : PointedSurfaceCoordinate X x,
      surfaceComplexDerivativeInCoordinate χx
        (fun y ↦ (F.toFun y : ℂ)) ≠ 0 := by
  classical
  have hinjective : Function.Injective F.toFun :=
    (bijective_of_existsUnique_preimage hdegree).1
  have _hcomplex_injective :
      ∀ {x y : X},
        ((F.toFun x : Complex.UnitDisc) : ℂ) =
          ((F.toFun y : Complex.UnitDisc) : ℂ) →
          x = y := by
    intro x y hxy
    exact hinjective (Subtype.ext hxy)
  intro x χx
  exact
    injective_holomorphicMap_surfaceComplexDerivative_ne_zero
      χx F.holomorphic_coe_unitDisc
      (fun x y hxy => _hcomplex_injective hxy)

/--
%%handwave
name:
  Proper degree-one pointed disk maps are unbranched
statement:
  A proper holomorphic pointed disk map of degree one has no critical points.
proof:
  This is the unbranchedness of degree-one pointed disk maps; properness is
  only needed earlier to establish degree one.
-/
theorem proper_degree_one_pointedDiskMap_unbranched
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    (F : PointedHolomorphicMap X Complex.UnitDisc p 0)
    (_hproper : IsProperMap F.toFun)
    (hdegree : ∀ z : Complex.UnitDisc, ∃! x : X, F.toFun x = z) :
    ∀ x : X, ∀ χx : PointedSurfaceCoordinate X x,
      surfaceComplexDerivativeInCoordinate χx
        (fun y ↦ (F.toFun y : ℂ)) ≠ 0 :=
  degree_one_pointedDiskMap_unbranched X F hdegree

/--
%%handwave
name:
  Degree-one disk maps are biholomorphic
statement:
  A pointed holomorphic disk map of degree one is a biholomorphic equivalence
  with the unit disk.
proof:
  Degree one gives bijectivity.  Also, a
  [degree-one pointed disk map is unbranched](lean:JJMath.Uniformization.degree_one_pointedDiskMap_unbranched).
  A bijective unbranched pointed holomorphic disk map is biholomorphic.
-/
theorem degree_one_pointedDiskMap_biholomorphic
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    (F : PointedHolomorphicMap X Complex.UnitDisc p 0)
    (hdegree : ∀ z : Complex.UnitDisc, ∃! x : X, F.toFun x = z) :
    BiholomorphicSurfaces X Complex.UnitDisc := by
  let χ : PointedSurfaceCoordinate X p :=
    { chart := chartAt ℂ p
      chart_mem_atlas := chart_mem_atlas ℂ p
      base_mem_source := mem_chart_source ℂ p }
  have hunbranched :
      ∀ x : X, ∀ χx : PointedSurfaceCoordinate X x,
        surfaceComplexDerivativeInCoordinate χx
          (fun y ↦ (F.toFun y : ℂ)) ≠ 0 :=
    degree_one_pointedDiskMap_unbranched X F hdegree
  have hbij : Function.Bijective F.toFun :=
    bijective_of_existsUnique_preimage hdegree
  exact biholomorphicSurfaces_of_bijective_unbranched_pointedDiskMap
    X χ F hunbranched hbij.1 hbij.2

/--
%%handwave
name:
  Proper degree-one disk maps are biholomorphic
statement:
  A proper holomorphic disk map of degree one is a biholomorphic equivalence
  with the unit disk.
proof:
  Once degree one is known, properness is no longer used; apply the
  degree-one biholomorphism criterion.
-/
theorem proper_degree_one_pointedDiskMap_biholomorphic
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    (F : PointedHolomorphicMap X Complex.UnitDisc p 0)
    (_hproper : IsProperMap F.toFun)
    (hdegree : ∀ z : Complex.UnitDisc, ∃! x : X, F.toFun x = z) :
    BiholomorphicSurfaces X Complex.UnitDisc :=
  degree_one_pointedDiskMap_biholomorphic X F hdegree

/--
%%handwave
name:
  Green functions uniformize simply connected surfaces by the disk
statement:
  A simply connected Riemann surface with a Green function for some
  pole is biholomorphic to the unit disk.
proof:
  Exponentiate the Green function and a harmonic conjugate to obtain a
  pointed holomorphic disk map.  The logarithmic pole gives a single simple
  zero, compact positive superlevel sets make the map proper, and the proper
  degree-one criterion makes it a biholomorphism.
-/
theorem simplyConnected_uniformization_via_greenFunction_of_has_greenFunction
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [SimplyConnectedSpace X]
    (hgreen : ∃ p : X, Nonempty (GreenFunctionWithPole X p)) :
    BiholomorphicSurfaces X Complex.UnitDisc := by
  classical
  letI : PathConnectedSpace X := inferInstance
  rcases hgreen with ⟨p, hGp⟩
  rcases hGp with ⟨G⟩
  rcases greenFunction_exponential_pointedDiskMap X G with ⟨F, hF⟩
  have hproper : IsProperMap F.toFun :=
    greenFunction_pointedDiskMap_isProper X G F hF
  have hdegree : ∀ z : Complex.UnitDisc, ∃! x : X, F.toFun x = z :=
    greenFunction_pointedDiskMap_has_degree_one X G F hF hproper
  exact degree_one_pointedDiskMap_biholomorphic X F hdegree

/--
%%handwave
name:
  Zero-cohomology Green functions uniformize by the disk
statement:
  A simply connected Riemann surface with a Green function at \(p\) and a
  pointed smooth exhaustion by connected domains containing \(p\) with
  vanishing first real de Rham cohomology is biholomorphic to the unit disk.
proof:
  Use the zero-cohomology exhaustion to exponentiate the Green function to a
  pointed disk map.  The Green superlevel compactness makes this map proper,
  and the logarithmic pole gives a single simple zero.  The proper degree-one
  criterion then makes the map biholomorphic.
-/
theorem uniformization_via_greenFunction_of_pointedH1Zero_exhaustion
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [SimplyConnectedSpace X] {p : X}
    (E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p)
    (G : GreenFunctionWithPole X p) :
    BiholomorphicSurfaces X Complex.UnitDisc := by
  rcases greenFunction_exponential_pointedDiskMap_of_pointedH1Zero_exhaustion
      X E G with
    ⟨F, hF⟩
  have hproper : IsProperMap F.toFun :=
    greenFunction_pointedDiskMap_isProper X G F hF
  have hdegree : ∀ z : Complex.UnitDisc, ∃! x : X, F.toFun x = z :=
    greenFunction_pointedDiskMap_has_degree_one X G F hF hproper
  exact degree_one_pointedDiskMap_biholomorphic X F hdegree

/--
%%handwave
name:
  Evans potentials give the Green-function disk uniformization in the
  hyperbolic case
statement:
  Suppose every potential-theoretically parabolic simply connected surface
  carries an Evans potential at some point.  Then a simply connected surface
  in the hyperbolic case is biholomorphic to the unit disk by the
  Green-function construction.
proof:
  The Evans-potential hypothesis rules out the parabolic alternative in the
  hyperbolic case, so a Green function exists for some pole.  The
  Green-function disk construction then gives a biholomorphism to the disk.
-/
theorem simplyConnected_hyperbolic_uniformization_via_greenFunction_of_evansPotential
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [SimplyConnectedSpace X]
    (hcase : IsSimplyConnectedHyperbolicCase X)
    (hevans :
      IsPotentialTheoreticallyParabolic X →
        ∃ p : X, Nonempty (EvansPotentialAt X p)) :
    BiholomorphicSurfaces X Complex.UnitDisc := by
  rcases simplyConnected_hyperbolic_case_has_some_greenFunction_of_evansPotential
      X hcase hevans with
    ⟨p, hGp⟩
  rcases hGp with ⟨G⟩
  rcases connected_noncompact_has_smoothRelativelyCompactExhaustion
      X hcase.1 with
    ⟨E₀⟩
  rcases smoothRelativelyCompactExhaustion_exists_pointedH1Zero_filling
      hcase.1 E₀ p with
    ⟨E⟩
  exact uniformization_via_greenFunction_of_pointedH1Zero_exhaustion X E G


/--
%%handwave
name:
  Green functions uniformize simply connected surfaces by the upper half-plane
statement:
  A simply connected Riemann surface with a Green function for some
  pole is biholomorphic to the upper half-plane.
proof:
  First uniformize the surface by the unit disk using the Green-function disk
  construction, then compose with the Cayley transform from the disk to the
  upper half-plane.
-/
theorem simplyConnected_upperHalfPlane_via_greenFunction_of_has_greenFunction
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [SimplyConnectedSpace X]
    (hgreen : ∃ p : X, Nonempty (GreenFunctionWithPole X p)) :
    BiholomorphicToUpperHalfPlane X := by
  exact biholomorphicToUpperHalfPlane_of_biholomorphicSurfaces_unitDisc X
    (simplyConnected_uniformization_via_greenFunction_of_has_greenFunction X hgreen)

/--
%%handwave
name:
  Evans potentials give the Green-function upper-half-plane uniformization in
  the hyperbolic case
statement:
  Suppose every potential-theoretically parabolic simply connected surface
  carries an Evans potential at some point.  Then a simply connected surface
  in the hyperbolic case is biholomorphic to the upper half-plane by the
  Green-function construction.
proof:
  The Evans-potential hypothesis supplies a Green pole in the hyperbolic
  case.  The Green-function construction uniformizes by the disk, and the
  Cayley transform sends the disk biholomorphically to the upper half-plane.
-/
theorem simplyConnected_hyperbolic_upperHalfPlane_via_greenFunction_of_evansPotential
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [SimplyConnectedSpace X]
    (hcase : IsSimplyConnectedHyperbolicCase X)
    (hevans :
      IsPotentialTheoreticallyParabolic X →
        ∃ p : X, Nonempty (EvansPotentialAt X p)) :
    BiholomorphicToUpperHalfPlane X := by
  exact biholomorphicToUpperHalfPlane_of_biholomorphicSurfaces_unitDisc X
    (simplyConnected_hyperbolic_uniformization_via_greenFunction_of_evansPotential
      X hcase hevans)


/--
%%handwave
name:
  Spherical universal cover
statement:
  A Riemann surface has spherical universal cover when each based
  universal cover is biholomorphic to the Riemann sphere.
-/
def HasSphericalUniversalCover (X : Type)
    [TopologicalSpace X] [ChartedSpace ℂ X] [LocallySimplyConnectedSpace X] : Prop :=
  ∀ x₀ : X,
    @BiholomorphicSurfaces (PathHomotopyUniversalCover X x₀) RiemannSphere
      inferInstance inferInstance inferInstance inferInstance

/--
%%handwave
name:
  Hyperbolic universal-cover case
statement:
  The hyperbolic universal-cover case is the case where the universal cover is
  neither spherical nor parabolic.
-/
def IsHyperbolicUniversalCoverCase (X : Type)
    [TopologicalSpace X] [ChartedSpace ℂ X] [LocallySimplyConnectedSpace X] : Prop :=
  ¬ HasSphericalUniversalCover X ∧ ¬ HasParabolicUniversalCover X







/--
%%handwave
name:
  Uniformizing universal cover
statement:
  A Riemann surface has a uniformizing universal cover when that
  cover is biholomorphic to one of the three standard simply connected models:
  the Riemann sphere, the complex plane, or the upper half-plane.
-/
def HasUniformizingUniversalCover (X : Type)
    [TopologicalSpace X] [ChartedSpace ℂ X] [LocallySimplyConnectedSpace X] : Prop :=
  HasSphericalUniversalCover X ∨
    HasParabolicUniversalCover X ∨
      HasUpperHalfPlaneUniformizingCover X

/--
%%handwave
name:
  The sphere and plane are not biholomorphic
statement:
  No Riemann surface is biholomorphic both to the Riemann sphere and to the
  complex plane.
proof:
  A biholomorphism is in particular a homeomorphism.  The Riemann sphere is
  compact, while the complex plane is not compact.
-/
theorem not_biholomorphicToRiemannSphere_and_complexPlane
    (Y : Type) [TopologicalSpace Y] [ChartedSpace ℂ Y] :
    BiholomorphicSurfaces Y RiemannSphere → ¬ BiholomorphicToComplexPlane Y := by
  intro hsphere hplane
  rcases hsphere with ⟨eSphere⟩
  rcases hplane with ⟨ePlane⟩
  letI : CompactSpace Y := Homeomorph.compactSpace eSphere.toHomeomorph.symm
  letI : CompactSpace ℂ := Homeomorph.compactSpace ePlane.toHomeomorph
  exact (not_compactSpace_iff.mpr (inferInstance : NoncompactSpace ℂ)) inferInstance

/--
%%handwave
name:
  The sphere and upper half-plane are not biholomorphic
statement:
  No Riemann surface is biholomorphic both to the Riemann sphere and to the
  upper half-plane.
proof:
  A biholomorphism is in particular a homeomorphism.  The Riemann sphere is
  compact, while the upper half-plane is not compact.
-/
theorem not_biholomorphicToRiemannSphere_and_upperHalfPlane
    (Y : Type) [TopologicalSpace Y] [ChartedSpace ℂ Y] :
    BiholomorphicSurfaces Y RiemannSphere → ¬ BiholomorphicToUpperHalfPlane Y := by
  intro hsphere hupper
  rcases hsphere with ⟨eSphere⟩
  rcases hupper with ⟨eUpper⟩
  letI : CompactSpace Y := Homeomorph.compactSpace eSphere.toHomeomorph.symm
  letI : CompactSpace UpperHalfPlane := Homeomorph.compactSpace eUpper.toHomeomorph
  exact
    (not_compactSpace_iff.mpr (inferInstance : NoncompactSpace UpperHalfPlane))
      inferInstance

/--
%%handwave
name:
  Bounded nonconstant holomorphic functions pull back
statement:
  A biholomorphism pulls bounded nonconstant holomorphic functions back to
  bounded nonconstant holomorphic functions.
proof:
  Compose the function with the biholomorphic equivalence.  Holomorphicity
  follows by composition, and the range is unchanged because the underlying
  homeomorphism is surjective.
-/
theorem biholomorphicSurfaces_preserves_bounded_nonconstant_holomorphicFunction
    {X Y : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y]
    (hXY : BiholomorphicSurfaces X Y)
    (hY : HasBoundedNonconstantHolomorphicFunction Y) :
    HasBoundedNonconstantHolomorphicFunction X := by
  rcases hXY with ⟨e⟩
  rcases hY with ⟨f, hf, hbdd, hnonconstant⟩
  refine ⟨fun x : X ↦ f (e.toHomeomorph x), ?_, ?_, ?_⟩
  · change HolomorphicMap X ℂ (f ∘ e.toHomeomorph)
    exact hf.comp e.holomorphic_toFun
  · have hrange :
        Set.range (fun x : X ↦ f (e.toHomeomorph x)) = Set.range f := by
      ext z
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨e.toHomeomorph x, rfl⟩
      · rintro ⟨y, rfl⟩
        rcases e.toHomeomorph.surjective y with ⟨x, hx⟩
        exact ⟨x, by simp [hx]⟩
    rwa [hrange]
  · have hrange :
        Set.range (fun x : X ↦ f (e.toHomeomorph x)) = Set.range f := by
      ext z
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨e.toHomeomorph x, rfl⟩
      · rintro ⟨y, rfl⟩
        rcases e.toHomeomorph.surjective y with ⟨x, hx⟩
        exact ⟨x, by simp [hx]⟩
    rwa [hrange]

/--
%%handwave
name:
  The plane has no bounded nonconstant holomorphic functions
statement:
  Every bounded holomorphic function on the complex plane is constant.
proof:
  This is Mathlib's Liouville theorem.
-/
theorem complexPlane_has_no_bounded_nonconstant_holomorphicFunction :
    ¬ HasBoundedNonconstantHolomorphicFunction ℂ := by
  rintro ⟨f, hf, hbdd, hnonconstant⟩
  have hdiff : Differentiable ℂ f :=
    (show MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f from hf).differentiable
  have hsubsingleton : (Set.range f).Subsingleton := by
    rintro _ ⟨z, rfl⟩ _ ⟨w, rfl⟩
    exact hdiff.apply_eq_apply_of_bounded hbdd z w
  exact hnonconstant.not_subsingleton hsubsingleton

/--
%%handwave
name:
  The unit disk has a bounded nonconstant holomorphic function
statement:
  The open unit disk carries a bounded nonconstant holomorphic complex-valued
  function.
proof:
  Use the inclusion of the disk into the complex plane.  It is holomorphic for
  the charted structure induced by the open embedding, its range is contained
  in the unit ball, and its range contains both \(0\) and \(1/2\).
-/
theorem unitDisc_has_bounded_nonconstant_holomorphicFunction :
    HasBoundedNonconstantHolomorphicFunction Complex.UnitDisc := by
  refine ⟨fun z : Complex.UnitDisc ↦ (z : ℂ), ?_, ?_, ?_⟩
  · let hOpen : Topology.IsOpenEmbedding ((↑) : Complex.UnitDisc → ℂ) :=
      (Metric.isOpen_ball : IsOpen (Metric.ball (0 : ℂ) 1)).isOpenEmbedding_subtypeVal
    have hcoe : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ((↑) : Complex.UnitDisc → ℂ) := by
      have h :
          ContMDiff 𝓘(ℂ) 𝓘(ℂ) (1 : WithTop ℕ∞)
            ((↑) : Complex.UnitDisc → ℂ) := by
        simpa using
          (contMDiff_isOpenEmbedding
            (I := 𝓘(ℂ)) (n := (1 : WithTop ℕ∞)) hOpen)
      exact h.mdifferentiable one_ne_zero
    exact hcoe
  · exact isBounded_iff_forall_norm_le.2
      ⟨1, by
        rintro _ ⟨z, rfl⟩
        exact le_of_lt (Complex.UnitDisc.norm_lt_one z)⟩
  · have hhalf_norm : ‖(((1 / 2 : ℝ) : ℂ))‖ < 1 := by
      rw [Complex.norm_real]
      norm_num
    let half : Complex.UnitDisc :=
      Complex.UnitDisc.mk (((1 / 2 : ℝ) : ℂ)) hhalf_norm
    refine Set.nontrivial_of_mem_mem_ne
      (show (0 : ℂ) ∈ Set.range (fun z : Complex.UnitDisc ↦ (z : ℂ)) from
        ⟨0, by simp⟩)
      (show (((1 / 2 : ℝ) : ℂ)) ∈
          Set.range (fun z : Complex.UnitDisc ↦ (z : ℂ)) from
        ⟨half, rfl⟩)
      ?_
    norm_num

/--
%%handwave
name:
  The Cayley transform maps the upper half-plane into the unit disk
statement:
  For every \(z\) in the upper half-plane,
  \[
    \left|\frac{z-i}{z+i}\right|<1.
  \]
proof:
  The denominator is nonzero because \(\operatorname{Im}z>0\).  Squaring the
  two norms reduces the inequality
  \(|z-i|<|z+i|\) to
  \((\operatorname{Im}z-1)^2<
    (\operatorname{Im}z+1)^2\), which follows from
  \(\operatorname{Im}z>0\).
-/
private theorem green_upperHalfPlane_cayley_norm_lt_one (z : UpperHalfPlane) :
    ‖((z : ℂ) - Complex.I) / ((z : ℂ) + Complex.I)‖ < 1 := by
  have hden : (z : ℂ) + Complex.I ≠ 0 := by
    intro hzero
    have him : ((z : ℂ) + Complex.I).im = 0 := by rw [hzero]; simp
    have : z.im + 1 = 0 := by simpa [UpperHalfPlane.coe_im] using him
    linarith [z.im_pos]
  rw [Complex.norm_div]
  refine (div_lt_one (norm_pos_iff.mpr hden)).2 ?_
  rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [Complex.sq_norm, Complex.sq_norm]
  simp [Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  nlinarith [z.im_pos]

/--
%%handwave
name:
  The upper half-plane has a bounded nonconstant holomorphic function
statement:
  The upper half-plane carries a bounded nonconstant holomorphic complex-valued
  function.
proof:
  Use \(z\mapsto (z-i)/(z+i)\).  It is holomorphic on the upper half-plane
  because the denominator is nonzero there, and
  [its absolute value is strictly less than one](lean:JJMath.Uniformization.upperHalfPlane_cayley_norm_lt_one).  It is
  not constant, since it sends \(i\) to \(0\) but does not send \(1+i\) to
  \(0\).
-/
theorem upperHalfPlane_has_bounded_nonconstant_holomorphicFunction :
    HasBoundedNonconstantHolomorphicFunction UpperHalfPlane := by
  let f : UpperHalfPlane → ℂ :=
    fun z ↦ ((z : ℂ) - Complex.I) / ((z : ℂ) + Complex.I)
  refine ⟨f, ?_, ?_, ?_⟩
  · change MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f
    rw [UpperHalfPlane.mdifferentiable_iff]
    let g : ℂ → ℂ := fun z ↦ (z - Complex.I) / (z + Complex.I)
    have hg : DifferentiableOn ℂ g {z : ℂ | 0 < z.im} := by
      have hnum : DifferentiableOn ℂ (fun z : ℂ ↦ z - Complex.I)
          {z : ℂ | 0 < z.im} :=
        (differentiable_id.sub (differentiable_const (c := Complex.I))).differentiableOn
      have hden_diff : DifferentiableOn ℂ (fun z : ℂ ↦ z + Complex.I)
          {z : ℂ | 0 < z.im} :=
        (differentiable_id.add (differentiable_const (c := Complex.I))).differentiableOn
      exact hnum.div hden_diff (by
        intro z hz hzero
        have him : (z + Complex.I).im = 0 := by rw [hzero]; simp
        have : z.im + 1 = 0 := by simpa using him
        have hzpos : 0 < z.im := hz
        linarith)
    exact hg.congr (by
      intro z hz
      simp [f, g, UpperHalfPlane.ofComplex_apply_of_im_pos hz])
  · exact isBounded_iff_forall_norm_le.2
      ⟨1, by
        rintro _ ⟨z, rfl⟩
        exact le_of_lt (green_upperHalfPlane_cayley_norm_lt_one z)⟩
  · let w : UpperHalfPlane := (1 : ℝ) +ᵥ UpperHalfPlane.I
    refine Set.nontrivial_of_mem_mem_ne
      (show (0 : ℂ) ∈ Set.range f from
        ⟨UpperHalfPlane.I, by simp [f]⟩)
      (show f w ∈ Set.range f from ⟨w, rfl⟩)
      ?_
    have hnum : ((w : ℂ) - Complex.I) ≠ 0 := by
      simp [w]
    have hden : ((w : ℂ) + Complex.I) ≠ 0 := by
      apply ne_of_apply_ne Complex.im
      simp [w]
    exact (div_ne_zero hnum hden).symm

/--
%%handwave
name:
  The plane and upper half-plane are not biholomorphic
statement:
  No Riemann surface is biholomorphic both to the complex plane and to the
  upper half-plane.
proof:
  The
  [upper half-plane has nonconstant bounded holomorphic functions](lean:JJMath.Uniformization.upperHalfPlane_has_bounded_nonconstant_holomorphicFunction),
  while [the complex plane has none](lean:JJMath.Uniformization.complexPlane_has_no_bounded_nonconstant_holomorphicFunction)
  by Liouville's theorem.  Pulling such a function back along a biholomorphism
  would contradict this.
-/
theorem not_biholomorphicToComplexPlane_and_upperHalfPlane
    (Y : Type) [TopologicalSpace Y] [ChartedSpace ℂ Y] :
    BiholomorphicToComplexPlane Y → ¬ BiholomorphicToUpperHalfPlane Y := by
  intro hplane hupper
  rcases hplane with ⟨ePlane⟩
  rcases hupper with ⟨eUpper⟩
  let ePlaneInv : Biholomorphic ℂ Y :=
    { toHomeomorph := ePlane.toHomeomorph.symm
      holomorphic_toFun := ePlane.holomorphic_invFun
      holomorphic_invFun := ePlane.holomorphic_toFun }
  have hCUpper : BiholomorphicSurfaces ℂ UpperHalfPlane :=
    ⟨ePlaneInv.trans eUpper⟩
  exact complexPlane_has_no_bounded_nonconstant_holomorphicFunction
    (biholomorphicSurfaces_preserves_bounded_nonconstant_holomorphicFunction
      hCUpper upperHalfPlane_has_bounded_nonconstant_holomorphicFunction)

/--
%%handwave
name:
  Standard universal covers are mutually exclusive
statement:
  The spherical, parabolic, and hyperbolic universal-cover alternatives are
  mutually exclusive.
proof:
  The sphere is compact while the complex plane and upper half-plane are not.
  The complex plane is parabolic: every bounded holomorphic function on it is
  constant.  The upper half-plane has nonconstant bounded holomorphic
  functions, for instance the Cayley disk coordinate.  Biholomorphic
  equivalence preserves compactness and bounded holomorphic function theory,
  so no two alternatives can hold at once.
-/
theorem uniformizing_universal_cover_models_mutually_exclusive
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] :
    (HasSphericalUniversalCover X →
        ¬ HasParabolicUniversalCover X ∧ ¬ HasUpperHalfPlaneUniformizingCover X) ∧
      (HasParabolicUniversalCover X →
        ¬ HasSphericalUniversalCover X ∧ ¬ HasUpperHalfPlaneUniformizingCover X) ∧
        (HasUpperHalfPlaneUniformizingCover X →
          ¬ HasSphericalUniversalCover X ∧ ¬ HasParabolicUniversalCover X) := by
  classical
  letI : PathConnectedSpace X := inferInstance
  rcases (inferInstance : PathConnectedSpace X).nonempty with ⟨x₀⟩
  constructor
  · intro hsphere
    constructor
    · intro hplane
      exact
        (not_biholomorphicToRiemannSphere_and_complexPlane
          (PathHomotopyUniversalCover X x₀) (hsphere x₀)) (hplane x₀)
    · intro hupper
      exact
        (not_biholomorphicToRiemannSphere_and_upperHalfPlane
          (PathHomotopyUniversalCover X x₀) (hsphere x₀)) (hupper x₀)
  · constructor
    · intro hplane
      constructor
      · intro hsphere
        exact
          (not_biholomorphicToRiemannSphere_and_complexPlane
            (PathHomotopyUniversalCover X x₀) (hsphere x₀)) (hplane x₀)
      · intro hupper
        exact
          (not_biholomorphicToComplexPlane_and_upperHalfPlane
            (PathHomotopyUniversalCover X x₀) (hplane x₀)) (hupper x₀)
    · intro hupper
      constructor
      · intro hsphere
        exact
          (not_biholomorphicToRiemannSphere_and_upperHalfPlane
            (PathHomotopyUniversalCover X x₀) (hsphere x₀)) (hupper x₀)
      · intro hplane
        exact
          (not_biholomorphicToComplexPlane_and_upperHalfPlane
            (PathHomotopyUniversalCover X x₀) (hplane x₀)) (hupper x₀)

/--
%%handwave
name:
  Uniformization trichotomy
statement:
  A Riemann surface satisfies the uniformization trichotomy when its
  universal cover is one of the three standard models and the three alternatives
  are mutually exclusive.
-/
def HasUniformizationTrichotomy (X : Type)
    [TopologicalSpace X] [ChartedSpace ℂ X] [LocallySimplyConnectedSpace X] : Prop :=
  HasUniformizingUniversalCover X ∧
    (HasSphericalUniversalCover X →
      ¬ HasParabolicUniversalCover X ∧ ¬ HasUpperHalfPlaneUniformizingCover X) ∧
      (HasParabolicUniversalCover X →
        ¬ HasSphericalUniversalCover X ∧ ¬ HasUpperHalfPlaneUniformizingCover X) ∧
        (HasUpperHalfPlaneUniformizingCover X →
          ¬ HasSphericalUniversalCover X ∧ ¬ HasParabolicUniversalCover X)


end Uniformization

end JJMath
