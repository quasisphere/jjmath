import JJMath.Uniformization.SmoothBoundaryProductChart

/-!
# Smooth frontier components as one-manifolds

The product-ball coordinates on a smooth surface frontier restrict to genuine
real interval charts.  This file packages those restrictions as a charted
space structure on the whole frontier.  In particular, the classification or
flow argument for a compact connected frontier component can now be stated as
a one-dimensional manifold problem rather than in ambient surface coordinates.
-/

open Set
open scoped Manifold Topology ContDiff

namespace JJMath.Uniformization

noncomputable section

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
variable [IsManifold 𝓘(ℝ, ℂ) ∞ X]

/-- The interval coordinate on a product-ball frontier arc, with its source
written as an open subset of the frontier subtype. -/
noncomputable def smoothBoundaryProductBall_frontierNestedHomeomorph
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) :
    {x : frontier D.carrier |
        (x : X) ∈ smoothBoundaryProductBallSource D p} ≃ₜ
      Metric.ball (0 : ℝ) (smoothBoundaryProductChartRadius D p) :=
  ({ toFun := fun x => ⟨(x : X), x.1.2, x.2⟩
     invFun := fun x => ⟨⟨(x : X), x.2.1⟩, x.2.2⟩
     left_inv := fun x => by cases x; rfl
     right_inv := fun x => by cases x; rfl
     continuous_toFun := by
       exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
     continuous_invFun := by
       exact (Continuous.subtype_mk continuous_subtype_val
         (fun x => x.2.1)).subtype_mk (fun x => x.2.2) } :
    {x : frontier D.carrier |
        (x : X) ∈ smoothBoundaryProductBallSource D p} ≃ₜ
      ↑(frontier D.carrier ∩ smoothBoundaryProductBallSource D p)).trans
    (smoothBoundaryProductBall_frontierHomeomorph D p)

/-- The one-dimensional partial chart obtained by restricting a centered
surface product chart to the frontier. -/
noncomputable def smoothBoundaryFrontierChart
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) :
    OpenPartialHomeomorph (frontier D.carrier) ℝ := by
  classical
  let S : Set (frontier D.carrier) :=
    (fun x : frontier D.carrier => (x : X)) ⁻¹'
      smoothBoundaryProductBallSource D p
  let J : Set ℝ :=
    Metric.ball 0 (smoothBoundaryProductChartRadius D p)
  let e := smoothBoundaryProductBall_frontierNestedHomeomorph D p
  let f : frontier D.carrier → ℝ := fun x =>
    ((smoothBoundaryProductChartAt D p).coordinate (x : X)).2
  let g : ℝ → frontier D.carrier := fun t =>
    if ht : t ∈ J then (e.symm ⟨t, ht⟩).1 else p
  have hf_eq : ∀ x : S, f x = (e x : ℝ) := by
    intro x
    rfl
  refine
    { toPartialEquiv :=
        { toFun := f
          invFun := g
          source := S
          target := J
          map_source' := ?_
          map_target' := ?_
          left_inv' := ?_
          right_inv' := ?_ }
      open_source := (smoothBoundaryProductBallSource_isOpen D p).preimage
        continuous_subtype_val
      open_target := Metric.isOpen_ball
      continuousOn_toFun := ?_
      continuousOn_invFun := ?_ }
  · intro x hx
    rw [show f x = (e ⟨x, hx⟩ : ℝ) from hf_eq ⟨x, hx⟩]
    exact (e ⟨x, hx⟩).2
  · intro t ht
    simp only [g, dif_pos ht]
    exact (e.symm ⟨t, ht⟩).2
  · intro x hx
    have hfx : f x ∈ J := by
      rw [show f x = (e ⟨x, hx⟩ : ℝ) from hf_eq ⟨x, hx⟩]
      exact (e ⟨x, hx⟩).2
    rw [show f x = (e ⟨x, hx⟩ : ℝ) from hf_eq ⟨x, hx⟩]
    simp only [g]
    rw [dif_pos (e ⟨x, hx⟩).2]
    exact congrArg (fun y : S => (y : frontier D.carrier))
      (e.left_inv ⟨x, hx⟩)
  · intro t ht
    simp only [g, dif_pos ht]
    rw [hf_eq (e.symm ⟨t, ht⟩)]
    exact congrArg Subtype.val (e.right_inv ⟨t, ht⟩)
  · rw [continuousOn_iff_continuous_restrict]
    have he : Continuous (fun x : S => (e x : ℝ)) :=
      continuous_subtype_val.comp e.continuous
    exact he.congr (fun x => (hf_eq x).symm)
  · rw [continuousOn_iff_continuous_restrict]
    have he : Continuous (fun t : J => ((e.symm t).1 : frontier D.carrier)) :=
      continuous_subtype_val.comp e.symm.continuous
    exact he.congr (fun t => by simp [g, t.2])

/--
%%handwave
name:
  Formula for the induced boundary chart
statement:
  The one-dimensional boundary chart induced by a product coordinate
  \(C\) sends a boundary point \(x\) to the second coordinate of \(C(x)\).
proof:
  This is the defining formula for the restricted product chart.
-/
@[simp]
theorem smoothBoundaryFrontierChart_apply
    (D : SmoothBoundaryDomain X) (p x : frontier D.carrier) :
    smoothBoundaryFrontierChart D p x =
      ((smoothBoundaryProductChartAt D p).coordinate (x : X)).2 := by
  simp [smoothBoundaryFrontierChart,
    smoothBoundaryProductBall_frontierNestedHomeomorph,
    smoothBoundaryProductBall_frontierHomeomorph]

/--
%%handwave
name:
  Source of the induced boundary chart
statement:
  The source of the boundary chart centered at \(p\) consists exactly of the
  boundary points lying in the source of the centered product-ball chart.
proof:
  This is the source chosen in the construction of the restricted chart.
-/
@[simp]
theorem smoothBoundaryFrontierChart_source
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) :
    (smoothBoundaryFrontierChart D p).source =
      (fun x : frontier D.carrier => (x : X)) ⁻¹'
        smoothBoundaryProductBallSource D p := by
  rfl

/--
%%handwave
name:
  Target of the induced boundary chart
statement:
  The target of the boundary chart centered at \(p\) is the interval
  \((-r_p,r_p)\), where \(r_p>0\) is the radius of the centered boundary
  product chart.
proof:
  This interval is the target chosen when restricting the product chart to
  its boundary axis.
-/
@[simp]
theorem smoothBoundaryFrontierChart_target
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) :
    (smoothBoundaryFrontierChart D p).target =
      Metric.ball 0 (smoothBoundaryProductChartRadius D p) := by
  rfl

/--
%%handwave
name:
  Inverse boundary chart along the product-chart axis
statement:
  If \(t\in(-r_p,r_p)\), then the inverse of the boundary chart at \(p\),
  viewed in the ambient surface, is \(C_p^{-1}(0,t)\).
proof:
  Let \(y\) be the inverse boundary-chart image of \(t\).  Since \(y\) lies on
  the boundary, its first product coordinate is zero; the right-inverse
  identity for the boundary chart makes its second coordinate \(t\).  Apply
  the inverse identity for the ambient product chart.
-/
theorem smoothBoundaryFrontierChart_symm_apply_of_mem_target
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) (t : ℝ)
    (ht : t ∈ (smoothBoundaryFrontierChart D p).target) :
    (((smoothBoundaryFrontierChart D p).symm t : frontier D.carrier) : X) =
      (smoothBoundaryProductChartAt D p).coordinate.symm (0, t) := by
  let y := (smoothBoundaryFrontierChart D p).symm t
  have hyChartSource : y ∈ (smoothBoundaryFrontierChart D p).source :=
    (smoothBoundaryFrontierChart D p).symm.map_source ht
  have hyBall : (y : X) ∈ smoothBoundaryProductBallSource D p := by
    simpa only [smoothBoundaryFrontierChart_source] using hyChartSource
  have hsecond :
      ((smoothBoundaryProductChartAt D p).coordinate (y : X)).2 = t := by
    have hright := (smoothBoundaryFrontierChart D p).right_inv ht
    simpa only [smoothBoundaryFrontierChart_apply] using hright
  have hfirst :
      ((smoothBoundaryProductChartAt D p).coordinate (y : X)).1 = 0 :=
    ((smoothBoundaryProductChartAt D p).frontier_iff_zero
      (y : X) hyBall.1).mp y.2
  have hcoord :
      (smoothBoundaryProductChartAt D p).coordinate (y : X) = (0, t) :=
    Prod.ext hfirst hsecond
  rw [← hcoord]
  exact ((smoothBoundaryProductChartAt D p).coordinate.left_inv hyBall.1).symm

/--
%%handwave
name:
  The center lies in its boundary chart
statement:
  The boundary point \(p\) belongs to the source of the boundary chart
  centered at \(p\).
proof:
  The centered product-ball chart contains its center, hence so does its
  restriction to the boundary.
-/
theorem smoothBoundaryFrontierChart_point_mem
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) :
    p ∈ (smoothBoundaryFrontierChart D p).source := by
  exact smoothBoundaryProductBallSource_point_mem D p

/-- The atlas on a smooth frontier obtained by restricting its centered
surface product charts. -/
@[reducible] noncomputable def smoothBoundaryFrontierChartedSpace
    (D : SmoothBoundaryDomain X) :
    ChartedSpace ℝ (frontier D.carrier) where
  atlas := Set.range (smoothBoundaryFrontierChart D)
  chartAt := smoothBoundaryFrontierChart D
  mem_chart_source := smoothBoundaryFrontierChart_point_mem D
  chart_mem_atlas := fun x => ⟨x, rfl⟩

/--
%%handwave
name:
  A smooth surface boundary is a topological one-manifold
statement:
  The atlas obtained by restricting centered boundary product charts makes
  the boundary of a smooth surface domain a topological one-manifold without
  boundary.
proof:
  Each restricted product chart is a homeomorphism from an open boundary arc
  to an open interval, and every boundary point lies in its centered chart.
-/
theorem smoothBoundaryDomain_frontier_isTopologicalOneManifold
    (D : SmoothBoundaryDomain X) :
    letI := smoothBoundaryFrontierChartedSpace D
    IsManifold 𝓘(ℝ, ℝ) 0 (frontier D.carrier) := by
  letI := smoothBoundaryFrontierChartedSpace D
  infer_instance

/--
%%handwave
name:
  A smooth surface frontier is a smooth one-manifold
statement:
  Let \(D\) be a smooth domain in a surface.  Restricting each boundary
  product chart \((s,t)\) to \(\partial D=\{s=0\}\) and using \(t\) as its
  coordinate makes \(\partial D\) a one-dimensional smooth manifold without
  boundary.
proof:
  The restricted charts identify frontier arcs with open real intervals.
  On an overlap, the transition is the second component of the ambient smooth
  product-chart transition evaluated along \((0,t)\), so every transition map
  is smooth.
-/
theorem smoothBoundaryDomain_frontier_isSmoothOneManifold
    (D : SmoothBoundaryDomain X) :
    letI := smoothBoundaryFrontierChartedSpace D
    IsManifold 𝓘(ℝ, ℝ) ∞ (frontier D.carrier) := by
  letI := smoothBoundaryFrontierChartedSpace D
  apply isManifold_of_contDiffOn
  intro e e' he he'
  rcases he with ⟨p, rfl⟩
  rcases he' with ⟨q, rfl⟩
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Set.range_id, Set.inter_univ, Set.preimage_id_eq, Function.id_comp,
    Function.comp_id]
  change ContDiffOn ℝ ∞
    (↑((smoothBoundaryFrontierChart D p).symm ≫ₕ smoothBoundaryFrontierChart D q))
    ((smoothBoundaryFrontierChart D p).symm ≫ₕ
      smoothBoundaryFrontierChart D q).source
  let ep := smoothBoundaryFrontierChart D p
  let eq := smoothBoundaryFrontierChart D q
  let Cp := smoothBoundaryProductChartAt D p
  let Cq := smoothBoundaryProductChartAt D q
  let A := (ep.symm ≫ₕ eq).source
  change ContDiffOn ℝ ∞ (↑(ep.symm ≫ₕ eq)) A
  have htargetP : ∀ t ∈ A, t ∈ ep.target := by
    intro t ht
    change t ∈ (ep.symm ≫ₕ eq).source at ht
    rw [OpenPartialHomeomorph.trans_source] at ht
    exact ht.1
  have hsourceQ : ∀ t ∈ A, ep.symm t ∈ eq.source := by
    intro t ht
    change t ∈ (ep.symm ≫ₕ eq).source at ht
    rw [OpenPartialHomeomorph.trans_source] at ht
    exact ht.2
  have hmapP : A ⊆
      (fun t : ℝ => ((0 : ℝ), t)) ⁻¹' Cp.coordinate.target := by
    intro t ht
    apply smoothBoundaryProductChart_ball_subset_target D p
    rw [← ball_prod_same]
    refine ⟨Metric.mem_ball_self (smoothBoundaryProductChartRadius_pos D p), ?_⟩
    have htTarget := htargetP t ht
    simpa only [ep, smoothBoundaryFrontierChart_target] using htTarget
  have hmapQ : A ⊆
      (fun t : ℝ => Cp.coordinate.symm ((0 : ℝ), t)) ⁻¹'
        Cq.coordinate.source := by
    intro t ht
    have htQ := hsourceQ t ht
    have htQBall : ((ep.symm t : frontier D.carrier) : X) ∈
        smoothBoundaryProductBallSource D q := by
      simpa only [eq, smoothBoundaryFrontierChart_source] using htQ
    have htTarget := htargetP t ht
    have hsymm : ((ep.symm t : frontier D.carrier) : X) =
        Cp.coordinate.symm ((0 : ℝ), t) := by
      simpa only [ep, Cp] using
        smoothBoundaryFrontierChart_symm_apply_of_mem_target D p t htTarget
    rw [hsymm] at htQBall
    exact htQBall.1
  have hinc : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) ∞
      (fun t : ℝ => ((0 : ℝ), t)) := by
    exact (contDiff_prodMk_right (0 : ℝ)).contMDiff
  have hp : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℂ) ∞
      Cp.coordinate.symm Cp.coordinate.target :=
    Cp.coordinate.contMDiffOn_invFun.of_le
      (by exact WithTop.coe_le_coe.mpr le_top)
  have hpA : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞
      (fun t : ℝ => Cp.coordinate.symm ((0 : ℝ), t)) A := by
    simpa only [Function.comp_apply] using
      hp.comp hinc.contMDiffOn hmapP
  have hq : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ × ℝ) ∞
      Cq.coordinate Cq.coordinate.source :=
    Cq.coordinate.contMDiffOn_toFun.of_le
      (by exact WithTop.coe_le_coe.mpr le_top)
  have hpq : ContDiffOn ℝ ∞
      (fun t : ℝ =>
        (Cq.coordinate (Cp.coordinate.symm ((0 : ℝ), t))).2) A := by
    have hcomp := hq.comp hpA hmapQ
    simpa only [Function.comp_apply] using hcomp.contDiffOn.snd
  apply hpq.congr
  intro t ht
  rw [OpenPartialHomeomorph.trans_apply]
  rw [show eq (ep.symm t) =
      (Cq.coordinate (((ep.symm t : frontier D.carrier) : X))).2 by
        simp only [eq, Cq, smoothBoundaryFrontierChart_apply]]
  rw [show ((ep.symm t : frontier D.carrier) : X) =
      Cp.coordinate.symm ((0 : ℝ), t) by
        simpa only [ep, Cp] using
          smoothBoundaryFrontierChart_symm_apply_of_mem_target D p t
          (htargetP t ht)]

/--
%%handwave
name:
  A smooth surface boundary is a twice differentiable one-manifold
statement:
  With the restricted product-chart atlas, the boundary of a smooth surface
  domain is a one-dimensional \(C^2\) manifold without boundary.
proof:
  The boundary is a smooth one-manifold, and smooth transition maps are in
  particular twice continuously differentiable.
-/
theorem smoothBoundaryDomain_frontier_isC2OneManifold
    (D : SmoothBoundaryDomain X) :
    letI := smoothBoundaryFrontierChartedSpace D
    IsManifold 𝓘(ℝ, ℝ) 2 (frontier D.carrier) := by
  letI := smoothBoundaryFrontierChartedSpace D
  letI : IsManifold 𝓘(ℝ, ℝ) ∞ (frontier D.carrier) :=
    smoothBoundaryDomain_frontier_isSmoothOneManifold D
  exact IsManifold.of_le (I := 𝓘(ℝ, ℝ))
    (M := frontier D.carrier) (m := 2) (n := ∞)
      (WithTop.coe_le_coe.mpr le_top)

/--
%%handwave
name:
  A smooth surface boundary is a continuously differentiable one-manifold
statement:
  With the restricted product-chart atlas, the boundary of a smooth surface
  domain is a one-dimensional \(C^1\) manifold without boundary.
proof:
  The boundary has already been shown to be a \(C^2\) one-manifold, and
  \(C^2\) regularity implies \(C^1\) regularity.
-/
theorem smoothBoundaryDomain_frontier_isC1OneManifold
    (D : SmoothBoundaryDomain X) :
    letI := smoothBoundaryFrontierChartedSpace D
    IsManifold 𝓘(ℝ, ℝ) 1 (frontier D.carrier) := by
  letI := smoothBoundaryFrontierChartedSpace D
  letI : IsManifold 𝓘(ℝ, ℝ) 2 (frontier D.carrier) :=
    smoothBoundaryDomain_frontier_isC2OneManifold D
  exact IsManifold.of_le (I := 𝓘(ℝ, ℝ))
    (M := frontier D.carrier) (m := 1) (n := 2) (by norm_num)

end

end JJMath.Uniformization
