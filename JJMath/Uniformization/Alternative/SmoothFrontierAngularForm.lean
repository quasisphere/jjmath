import JJMath.Uniformization.SmoothFrontierLocalCollar
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# An alternative angular-form construction on a smooth frontier collar

This file isolates the intrinsic obstruction behind the horizontal form on a
frontier collar.  A real function on a compact frontier component has a
critical point.  Consequently, a covector which is everywhere positive in
the oriented frontier direction cannot be the differential of a globally
defined real function.
-/

open Set Filter
open JJMath.Manifold
open scoped Manifold Topology ContDiff

namespace JJMath.Uniformization

noncomputable section

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
variable [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]

/-- Rotate the differential of the global signed boundary coordinate by a
quarter turn in the complex tangent line.  Along the frontier this is the
intrinsic horizontal covector complementary to the normal differential. -/
noncomputable def smoothBoundaryAngularCovector
    (D : SmoothBoundaryDomain X) (x : X) : ℂ →L[ℝ] ℝ :=
  surfaceQuarterTurnCovector
    (mfderiv SurfaceRealModel (modelWithCornersSelf ℝ ℝ)
      (smoothBoundaryGlobalSignedCoordinate D) x)

/--
%%handwave
name:
  Nonvanishing of the angular frontier covector
statement:
  Let \(s\) be the global signed coordinate of a smooth domain in a Riemann
  surface, and let \(J\) denote quarter-turn in the complex tangent line.  At
  every \(x\in\partial D\), the angular covector
  \[
    \alpha_x(v)=ds_x(Jv)
  \]
  is nonzero.
proof:
  The normal covector \(ds_x\) is nonzero on the frontier.  Quarter-turn is an
  invertible real-linear map, so precomposing a nonzero covector with it
  remains nonzero.
-/
theorem smoothBoundaryAngularCovector_ne_zero
    (D : SmoothBoundaryDomain X) {x : X}
    (hx : x ∈ frontier D.carrier) :
    smoothBoundaryAngularCovector D x ≠ 0 := by
  exact surfaceQuarterTurnCovector_ne_zero
    (smoothBoundaryGlobalSignedCoordinate_mfderiv_ne_zero D hx)

/-- The covector at a frontier point obtained by differentiating the centered
frontier chart at that point. -/
noncomputable def smoothFrontierCenteredChartCovector
    (D : SmoothBoundaryDomain X) (q : frontier D.carrier) : ℝ →L[ℝ] ℝ := by
  letI := smoothBoundaryFrontierChartedSpace D
  exact mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ)
    (smoothBoundaryFrontierChart D q) q

omit [RiemannSurface X] in
/-- The centered frontier-chart covector is nonzero. -/
theorem smoothFrontierCenteredChartCovector_ne_zero
    (D : SmoothBoundaryDomain X) (q : frontier D.carrier) :
    smoothFrontierCenteredChartCovector D q ≠ 0 := by
  letI := smoothBoundaryFrontierChartedSpace D
  letI : IsManifold (modelWithCornersSelf ℝ ℝ) ∞
      (frontier D.carrier) := smoothBoundaryDomain_frontier_isSmoothOneManifold D
  have hself := mfderiv_extChartAt_self
    (I := modelWithCornersSelf ℝ ℝ) (x := q)
  have hchart : (chartAt ℝ q : frontier D.carrier → ℝ) =
      smoothBoundaryFrontierChart D q := rfl
  have hderiv : smoothFrontierCenteredChartCovector D q =
      ContinuousLinearMap.id ℝ ℝ := by
    simpa [smoothFrontierCenteredChartCovector, extChartAt_coe,
      hchart, Function.comp_def] using hself
  rw [hderiv]
  intro hzero
  have happ := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) hzero
  norm_num at happ

omit [RiemannSurface X] in
/-- A continuously differentiable real function on a compact connected
frontier component has a critical point on that component. -/
theorem exists_mfderiv_eq_zero_on_frontierComponent
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier)
    (f : frontier D.carrier → ℝ) :
    letI := smoothBoundaryFrontierChartedSpace D
    ContMDiff (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ) 1 f →
      ∃ q ∈ connectedComponent p,
        mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ) f q = 0 := by
  letI := smoothBoundaryFrontierChartedSpace D
  letI : IsManifold (modelWithCornersSelf ℝ ℝ) ∞
      (frontier D.carrier) := smoothBoundaryDomain_frontier_isSmoothOneManifold D
  letI : LocallyConnectedSpace (frontier D.carrier) :=
    ChartedSpace.locallyConnectedSpace ℝ (frontier D.carrier)
  letI : CompactSpace (frontier D.carrier) :=
    isCompact_iff_compactSpace.mp
      (D.compact_closure.of_isClosed_subset
        isClosed_frontier frontier_subset_closure)
  intro hf
  have hcompact : IsCompact (connectedComponent p) :=
    isClosed_connectedComponent.isCompact
  have hnonempty : (connectedComponent p).Nonempty :=
    ⟨p, mem_connectedComponent⟩
  rcases hcompact.exists_isMaxOn hnonempty hf.continuous.continuousOn with
    ⟨q, hq, hqmax⟩
  have hlocal : IsLocalMax f q := by
    filter_upwards [isOpen_connectedComponent.mem_nhds hq] with y hy
    exact hqmax hy
  have hinvContinuous : ContinuousAt
      (extChartAt (modelWithCornersSelf ℝ ℝ) q).symm
      ((extChartAt (modelWithCornersSelf ℝ ℝ) q) q) :=
    (chartAt ℝ q).continuousAt_extend_symm (mem_chart_source ℝ q)
  have hcoordMax : IsLocalMax
      (writtenInExtChartAt (modelWithCornersSelf ℝ ℝ)
        (modelWithCornersSelf ℝ ℝ) q f)
      ((extChartAt (modelWithCornersSelf ℝ ℝ) q) q) := by
    have hlocal' : IsLocalMax f
        ((extChartAt (modelWithCornersSelf ℝ ℝ) q).symm
          ((extChartAt (modelWithCornersSelf ℝ ℝ) q) q)) := by
      simpa only [extChartAt_to_inv] using hlocal
    have hcomp := hlocal'.comp_continuous hinvContinuous
    simpa [writtenInExtChartAt] using hcomp
  refine ⟨q, hq, ?_⟩
  rw [(hf.mdifferentiableAt (by norm_num) :
    MDifferentiableAt (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ ℝ) f q).mfderiv]
  simpa using hcoordMax.fderiv_eq_zero

omit [RiemannSurface X] in
/--
%%handwave
name:
  A nowhere-zero covector on a compact frontier component has no primitive
statement:
  Let \(C\) be a compact connected component of a smooth frontier and let
  \(\alpha_q\in T_q^*C\) be nonzero for every \(q\in C\).  There is no
  \(C^1\) function \(f\) on the frontier satisfying
  \[
    df_q=\alpha_q\qquad(q\in C).
  \]
proof:
  The restriction of \(f\) to the compact connected component attains a
  maximum.  Its derivative vanishes at that point, contradicting the assumed
  nonvanishing of \(\alpha\).
-/
theorem no_primitive_of_frontierComponent_covector_ne_zero
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier)
    (omega : frontier D.carrier → (ℝ →L[ℝ] ℝ))
    (homega : ∀ q ∈ connectedComponent p, omega q ≠ 0) :
    letI := smoothBoundaryFrontierChartedSpace D
    ¬ ∃ f : frontier D.carrier → ℝ,
      ContMDiff (modelWithCornersSelf ℝ ℝ)
        (modelWithCornersSelf ℝ ℝ) 1 f ∧
      ∀ q ∈ connectedComponent p,
        mfderiv (modelWithCornersSelf ℝ ℝ)
          (modelWithCornersSelf ℝ ℝ) f q = omega q := by
  letI := smoothBoundaryFrontierChartedSpace D
  intro hprimitive
  rcases hprimitive with ⟨f, hf, hdf⟩
  rcases exists_mfderiv_eq_zero_on_frontierComponent D p f hf with
    ⟨q, hq, hzero⟩
  exact homega q hq ((hdf q hq).symm.trans hzero)

omit [RiemannSurface X] in
/-- The pointwise oriented chart covectors on a compact frontier component
have no continuously differentiable global primitive. -/
theorem smoothFrontierCenteredChartCovector_has_no_primitive
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) :
    letI := smoothBoundaryFrontierChartedSpace D
    ¬ ∃ f : frontier D.carrier → ℝ,
      ContMDiff (modelWithCornersSelf ℝ ℝ)
        (modelWithCornersSelf ℝ ℝ) 1 f ∧
      ∀ q ∈ connectedComponent p,
        mfderiv (modelWithCornersSelf ℝ ℝ)
          (modelWithCornersSelf ℝ ℝ) f q =
            smoothFrontierCenteredChartCovector D q := by
  letI := smoothBoundaryFrontierChartedSpace D
  exact no_primitive_of_frontierComponent_covector_ne_zero D p
    (smoothFrontierCenteredChartCovector D)
    (fun q _hq => smoothFrontierCenteredChartCovector_ne_zero D q)

end

end JJMath.Uniformization
