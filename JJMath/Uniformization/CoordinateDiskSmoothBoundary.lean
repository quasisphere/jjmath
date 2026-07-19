import JJMath.Manifold.DeRhamComparison.Base
import JJMath.Uniformization.EvansPotential

/-!
# Smooth coordinate-disk boundaries

This file packages the open interior of a closed coordinate disk as a smooth
relatively compact domain.  The radial defining function is used directly in
the chosen complex coordinate.
-/

open Set
open scoped Manifold ContDiff Topology

namespace JJMath.Uniformization

noncomputable section

open JJMath.Manifold

/--
%%handwave
name: Smooth boundary of a coordinate disk
statement:
  Let $D$ be a closed coordinate disk of radius $R>0$ in a Riemann surface. Its open coordinate disk $\{|z-c|<R\}$ has smooth boundary.
proof:
  In the defining chart use the real function $r(z)=|z-c|^2-R^2$. Its derivative at a boundary point is $v\mapsto2\langle z-c,v\rangle$, which is nonzero because $|z-c|=R>0$. The regular zero-set description agrees locally with the disk and its boundary.
-/
theorem ClosedCoordinateDisk.expandedOpenDisk_hasSmoothBoundary
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (D : ClosedCoordinateDisk X) :
    HasSmoothBoundary (D.expandedOpenDisk D.closedRadius) := by
  intro x hx_frontier
  let e : OpenPartialHomeomorph X ℂ := D.openDisk.chart
  let c : ℂ := D.openDisk.center
  let R : ℝ := D.closedRadius
  let r : ℂ → ℝ := fun z ↦ ‖z - c‖ ^ 2 - R ^ 2
  have hx_circle := D.frontier_expandedOpenDisk_subset_radiusBoundaryCircle
    D.closedRadius_lt_openRadius hx_frontier
  have hx_source : x ∈ e.source := hx_circle.1
  have hdist_eq : dist (e x) c = R := by
    simpa [ClosedCoordinateDisk.radiusBoundaryCircle, e, c, R,
      Metric.mem_sphere, dist_eq_norm] using hx_circle.2
  have hnorm_eq : ‖e x - c‖ = R := by
    simpa [dist_eq_norm] using hdist_eq
  have hr_smooth : ContDiffOnNhdAt r (e x) := by
    have hshift : ContDiff ℝ ∞ (fun z : ℂ ↦ z - c) :=
      contDiff_id.sub contDiff_const
    refine ⟨Set.univ, Filter.univ_mem, ?_⟩
    simpa [r] using ((hshift.norm_sq ℝ).sub contDiff_const).contDiffOn
  let v : ℂ := e x - c
  let dr : ℂ →L[ℝ] ℝ :=
    2 • (((innerSL ℝ) v).comp (1 : ℂ →L[ℝ] ℂ))
  have hshift_deriv :
      HasFDerivAt (fun z : ℂ ↦ z - c) (1 : ℂ →L[ℝ] ℂ) (e x) := by
    simpa using ((hasFDerivAt_id (𝕜 := ℝ) (E := ℂ) (e x)).sub_const c)
  have hr_deriv : HasFDerivAt r dr (e x) := by
    have hnorm_deriv := hshift_deriv.norm_sq
    simpa [r, dr, v] using hnorm_deriv.sub_const (R ^ 2)
  have hdr_ne : dr ≠ 0 := by
    intro hdr_zero
    have hz : dr v = 0 := by simp [hdr_zero]
    have hcalc : dr v = 2 * ‖v‖ ^ 2 := by
      simp only [dr, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply]
      rw [innerSL_apply_apply, real_inner_self_eq_norm_sq]
      ring
    have hzero : 2 * R ^ 2 = 0 := by
      simpa [hcalc, v, hnorm_eq] using hz
    have hRpos : 0 < R := by simpa [R] using D.closedRadius_pos
    nlinarith [sq_pos_of_pos hRpos]
  refine ⟨e, D.openDisk.chart_mem_atlas, hx_source, r, hr_smooth,
    dr, hr_deriv, hdr_ne, ?_⟩
  let S : Set X := D.expandedOpenDisk D.closedRadius
  let V : Set ℂ := {z : ℂ | r z < 0}
  let T : Set X := e ⁻¹' V
  have hr_zero : r (e x) = 0 := by simp [r, hnorm_eq]
  have hlocal_eq : S ∩ e.source = T ∩ e.source := by
    ext y
    simp only [S, T, V, Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hy, hy_source⟩
      refine ⟨?_, hy_source⟩
      have hdist_norm : dist (e y) c = ‖e y - c‖ := dist_eq_norm _ _
      rw [ClosedCoordinateDisk.expandedOpenDisk] at hy
      have hylt : dist (e y) c < R := by
        simpa [e, c, R, Metric.mem_ball] using hy.2
      have hRnonneg : 0 ≤ R := by simpa [R] using D.closedRadius_pos.le
      have hsq : ‖e y - c‖ ^ 2 < R ^ 2 :=
        (sq_lt_sq₀ (norm_nonneg _) hRnonneg).2 (by simpa [hdist_norm] using hylt)
      simpa [r] using sub_neg.mpr hsq
    · rintro ⟨hry, hy_source⟩
      refine ⟨?_, hy_source⟩
      have hsq : ‖e y - c‖ ^ 2 < R ^ 2 := sub_neg.mp (by simpa [r] using hry)
      have hRnonneg : 0 ≤ R := by simpa [R] using D.closedRadius_pos.le
      have hnormlt : ‖e y - c‖ < R :=
        (sq_lt_sq₀ (norm_nonneg _) hRnonneg).1 hsq
      rw [ClosedCoordinateDisk.expandedOpenDisk]
      exact ⟨hy_source, by simpa [e, c, R, Metric.mem_ball, dist_eq_norm] using hnormlt⟩
  have hfrontier_congr :
      ∀ᶠ y in nhds x, (y ∈ frontier S ↔ y ∈ frontier T) :=
    eventually_frontier_congr_of_inter_eq e.open_source hx_source hlocal_eq
  have hchart_frontier :
      ∀ᶠ y in nhds x, (y ∈ frontier T ↔ e y ∈ frontier V) := by
    filter_upwards [e.open_source.mem_nhds hx_source] with y hy_source
    have hmem := congrArg (fun A : Set X ↦ y ∈ A) (e.preimage_frontier V)
    have hiff : y ∈ frontier T ↔ y ∈ e ⁻¹' frontier V := by
      simpa [T, hy_source] using hmem.symm
    simpa [T] using hiff
  have hplane :
      ∀ᶠ y in nhds x, (e y ∈ frontier V ↔ r (e y) = 0) :=
    (e.continuousAt hx_source).eventually
      (smoothPlaneRegularZeroSublevel_eventually_frontier_eq_zero
        hr_smooth.contDiffAt hr_deriv hdr_ne hr_zero)
  filter_upwards [e.open_source.mem_nhds hx_source,
    hfrontier_congr, hchart_frontier, hplane] with
      y hy_source hy_congr hy_chart hy_plane
  have hmem := congrArg (fun A : Set X ↦ y ∈ A) hlocal_eq
  have hmem' : y ∈ S ↔ r (e y) < 0 := by
    simpa [T, V, hy_source] using hmem
  exact ⟨hy_source, hmem', hy_congr.trans (hy_chart.trans hy_plane)⟩

/--
%%handwave
name:
  The closure of the open coordinate disk is the closed coordinate disk
statement:
  The closure of the coordinate disk with radius (R>0) is the corresponding
  closed coordinate disk of radius (R).
proof:
  In the coordinate chart this is the equality between the closure of an open
  Euclidean ball and the corresponding closed ball.  The chart source is an
  open neighborhood of every point of the closed disk, so taking its
  intersection does not alter the local closure statement.
-/
theorem ClosedCoordinateDisk.closure_expandedOpenDisk_closedRadius
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (D : ClosedCoordinateDisk X) :
    closure (D.expandedOpenDisk D.closedRadius) = D.carrier := by
  apply Set.Subset.antisymm
  · apply closure_minimal
    · intro x hx
      rw [ClosedCoordinateDisk.expandedOpenDisk] at hx
      rw [D.carrier_eq]
      exact ⟨hx.1, Metric.ball_subset_closedBall hx.2⟩
    · exact D.compact.isClosed
  · intro x hxD
    let e : OpenPartialHomeomorph X ℂ := D.openDisk.chart
    let c : ℂ := D.openDisk.center
    let R : ℝ := D.closedRadius
    have hxD' : x ∈ e.source ∩ e ⁻¹' Metric.closedBall c R := by
      simpa [e, c, R, D.carrier_eq] using hxD
    have hx_preimage_closure :
        x ∈ e.source ∩ e ⁻¹' closure (Metric.ball c R) := by
      simpa [closure_ball c D.closedRadius_pos.ne', R] using hxD'
    have hpreimage := e.preimage_closure (Metric.ball c R)
    have hx_closure_preimage : x ∈ closure (e ⁻¹' Metric.ball c R) := by
      have hx' : x ∈ e.source ∩ closure (e ⁻¹' Metric.ball c R) := by
        rw [← hpreimage]
        exact hx_preimage_closure
      exact hx'.2
    rw [mem_closure_iff_nhds] at hx_closure_preimage ⊢
    intro U hU
    have hsource : e.source ∈ nhds x :=
      e.open_source.mem_nhds hxD'.1
    rcases hx_closure_preimage (U ∩ e.source) (Filter.inter_mem hU hsource) with
      ⟨y, hyU, hyball⟩
    refine ⟨y, hyU.1, ?_⟩
    rw [ClosedCoordinateDisk.expandedOpenDisk]
    exact ⟨hyU.2, hyball⟩

/--
%%handwave
name:
  The open interior of a closed coordinate disk is a smooth domain
statement:
  The open coordinate disk with the closed disk's radius is a nonempty smooth
  relatively compact domain whose closure lies in the closed coordinate disk.
proof:
  Its center supplies a point.  The open disk lies in the compact closed disk,
  so its closure is compact, and the radial defining function gives its smooth
  boundary.
-/
noncomputable def ClosedCoordinateDisk.toSmoothBoundaryDomain
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (D : ClosedCoordinateDisk X) : SmoothBoundaryDomain X where
  carrier := D.expandedOpenDisk D.closedRadius
  isOpen := D.expandedOpenDisk_isOpen D.closedRadius
  nonempty := by
    let x : X := D.openDisk.chart.symm D.openDisk.center
    have hc_ball : D.openDisk.center ∈
        Metric.ball D.openDisk.center D.closedRadius := by
      simpa [Metric.mem_ball] using D.closedRadius_pos
    have hc_target : D.openDisk.center ∈ D.openDisk.chart.target :=
      D.closedBall_subset_chart_target (Metric.ball_subset_closedBall hc_ball)
    refine ⟨x, ?_⟩
    rw [ClosedCoordinateDisk.expandedOpenDisk]
    refine ⟨D.openDisk.chart.map_target hc_target, ?_⟩
    change D.openDisk.chart x ∈
      Metric.ball D.openDisk.center D.closedRadius
    rw [show D.openDisk.chart x = D.openDisk.center by
      simpa [x] using D.openDisk.chart.right_inv hc_target]
    exact hc_ball
  compact_closure := by
    have hsubset : D.expandedOpenDisk D.closedRadius ⊆ D.carrier := by
      intro x hx
      rw [ClosedCoordinateDisk.expandedOpenDisk] at hx
      rw [D.carrier_eq]
      exact ⟨hx.1, Metric.ball_subset_closedBall hx.2⟩
    exact D.compact.of_isClosed_subset isClosed_closure
      (closure_minimal hsubset D.compact.isClosed)
  smooth_boundary := D.expandedOpenDisk_hasSmoothBoundary

/-- The smooth open interior of a closed coordinate disk is path connected.

%%handwave
name: Path connectedness of a coordinate-disk interior
statement:
  The open interior of every closed coordinate disk in a Riemann surface is path connected.
proof:
  Regard it as the coordinate disk defined by the same chart, center, and radius. Its chart image is a convex Euclidean ball, hence it is path connected.
-/
theorem ClosedCoordinateDisk.toSmoothBoundaryDomain_isPathConnected
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (D : ClosedCoordinateDisk X) :
    IsPathConnected D.toSmoothBoundaryDomain.carrier := by
  let C : CoordinateDisk X :=
    { carrier := D.expandedOpenDisk D.closedRadius
      chart := D.openDisk.chart
      chart_mem_atlas := D.openDisk.chart_mem_atlas
      center := D.openDisk.center
      radius := D.closedRadius
      radius_pos := D.closedRadius_pos
      ball_subset_target :=
        (Metric.ball_subset_closedBall.trans D.closedBall_subset_chart_target)
      carrier_eq := rfl }
  simpa [ClosedCoordinateDisk.toSmoothBoundaryDomain, C] using C.isPathConnected

/-- The open interior of a closed coordinate disk is smoothly equivalent to
the corresponding Euclidean ball in its defining coordinate.

%%handwave
name: Coordinate-disk interior is diffeomorphic to a Euclidean ball
statement:
  The open interior of a closed coordinate disk is diffeomorphic, as a real smooth surface, to the Euclidean ball with the same center and radius in $\mathbb C$.
proof:
  Restrict the defining complex chart to the open disk. Its source and target are exactly the two stated open sets, and a complex chart is a real-smooth diffeomorphism on such restrictions.
-/
theorem ClosedCoordinateDisk.expandedOpenDisk_diffeomorphic_ball
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    (D : ClosedCoordinateDisk X) :
    Nonempty
      ((⟨D.expandedOpenDisk D.closedRadius,
          D.expandedOpenDisk_isOpen D.closedRadius⟩ :
          TopologicalSpace.Opens X) ≃ₘ⟮SurfaceRealModel, 𝓘(ℝ, ℂ)⟯
        (⟨Metric.ball D.openDisk.center D.closedRadius,
          Metric.isOpen_ball⟩ : TopologicalSpace.Opens ℂ)) := by
  let U : TopologicalSpace.Opens X :=
    ⟨D.expandedOpenDisk D.closedRadius,
      D.expandedOpenDisk_isOpen D.closedRadius⟩
  let V : TopologicalSpace.Opens ℂ :=
    ⟨Metric.ball D.openDisk.center D.closedRadius, Metric.isOpen_ball⟩
  apply deRham_boundarylessExtendedChart_restriction_diffeomorph
    SurfaceRealModel D.openDisk.chart D.openDisk.chart_mem_atlas U V
  · simp [U, V, ClosedCoordinateDisk.expandedOpenDisk,
      deRham_boundarylessExtendedChart, SurfaceRealModel]
  · intro y hy
    have hy' : y ∈ D.openDisk.chart.target :=
      D.closedBall_subset_chart_target (Metric.ball_subset_closedBall hy)
    simpa [deRham_boundarylessExtendedChart, SurfaceRealModel] using hy'

/-- The first real de Rham cohomology of the open interior of a closed
coordinate disk vanishes.

%%handwave
name: Vanishing first cohomology of a coordinate-disk interior
statement:
  The first real de Rham cohomology of the open interior of a closed coordinate disk is zero.
proof:
  Transfer de Rham cohomology through the diffeomorphism with a Euclidean ball, then apply the Poincaré lemma to that nonempty convex open set.
-/
theorem ClosedCoordinateDisk.expandedOpenDisk_deRhamH1_subsingleton
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    (D : ClosedCoordinateDisk X) :
    Subsingleton
      (DeRhamCohomology (I := SurfaceRealModel)
        (M := (⟨D.expandedOpenDisk D.closedRadius,
          D.expandedOpenDisk_isOpen D.closedRadius⟩ :
          TopologicalSpace.Opens X)) (A := ℝ) 1) := by
  rcases D.expandedOpenDisk_diffeomorphic_ball with ⟨phi⟩
  apply deRhamCohomology_subsingleton_of_diffeomorphic
    SurfaceRealModel (𝓘(ℝ, ℂ)) phi 1
  apply deRham_poincareLemma_convex_open
  · exact convex_ball D.openDisk.center D.closedRadius
  · exact ⟨D.openDisk.center,
      Metric.mem_ball_self D.closedRadius_pos⟩

end
end JJMath.Uniformization
