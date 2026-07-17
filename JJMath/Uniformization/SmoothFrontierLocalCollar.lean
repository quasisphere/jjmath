import JJMath.Uniformization.SmoothFrontierFlow

/-!
# Local collars from the transverse flow

A product chart supplies the tangent direction along the frontier, while the
transverse vector field supplies an independent normal direction.  The
time-zero derivative formula for the local flow therefore makes the
boundary-restricted flow map locally invertible.  This produces a genuine
product-coordinate germ at every frontier point.
-/


open Bundle Filter Function Set
open JJMath.Manifold
open scoped Manifold Topology ContDiff

namespace JJMath.Uniformization

noncomputable section

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
variable [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]

/-- Restricting a map to an open set on which it agrees with an open partial
homeomorphism gives an open map. -/
theorem isOpenMap_restrict_of_eqOn_openPartialHomeomorph
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {S : Set A} (hS : IsOpen S) {f : A → B}
    (e : OpenPartialHomeomorph A B) (hsource : S ⊆ e.source)
    (heq : EqOn f e S) : IsOpenMap (S.restrict f) := by
  intro U hU
  have hUambient : IsOpen (((↑) : S → A) '' U) :=
    hS.isOpenMap_subtype_val U hU
  have hUsource : ((↑) : S → A) '' U ⊆ e.source := by
    rintro a ⟨z, hzU, rfl⟩
    exact hsource z.2
  have heU : IsOpen (e '' (((↑) : S → A) '' U)) :=
    e.isOpen_image_of_subset_source hUambient hUsource
  convert heU using 1
  ext b
  constructor
  · rintro ⟨z, hzU, rfl⟩
    exact ⟨(z : A), ⟨z, hzU, rfl⟩, (heq z.2).symm⟩
  · rintro ⟨a, ⟨z, hzU, rfl⟩, rfl⟩
    exact ⟨z, hzU, heq z.2⟩

/-- An open restriction of an open map is still open. -/
theorem isOpenMap_restrict_mono
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {S T : Set A} {f : A → B} (hf : IsOpenMap (S.restrict f))
    (hT : IsOpen T) (hsub : T ⊆ S) : IsOpenMap (T.restrict f) := by
  simpa only [Set.restrict_eq, Function.comp_def, Set.inclusion_mk]
    using hf.comp (hT.isOpenMap_inclusion hsub)

omit [RiemannSurface X] in
/-- Near the center of a frontier chart, applying the preferred chart and
then its inverse to the product-chart boundary axis returns that axis.  The
same neighborhood lies in the target of the restricted frontier chart. -/
theorem eventually_extChartAt_symm_productAxis_eq
    (D : SmoothBoundaryDomain X) (x : frontier D.carrier) :
    ∀ᶠ s : ℝ in 𝓝 0,
      s ∈ (smoothBoundaryFrontierChart D x).target ∧
      (extChartAt SurfaceRealModel (x : X)).symm
          (extChartAt SurfaceRealModel (x : X)
            ((smoothBoundaryProductChartAt D x).coordinate.symm (0, s))) =
        (smoothBoundaryProductChartAt D x).coordinate.symm (0, s) := by
  let e := smoothBoundaryFrontierChart D x
  have hzeroTarget : (0 : ℝ) ∈ e.target := by
    rw [smoothBoundaryFrontierChart_target]
    exact Metric.mem_ball_self (smoothBoundaryProductChartRadius_pos D x)
  have hex : e x = 0 := by
    rw [smoothBoundaryFrontierChart_apply]
    simp only [(smoothBoundaryProductChartAt D x).point_coord]
  have he0 : e.symm 0 = x := by
    rw [← hex]
    exact e.left_inv (smoothBoundaryFrontierChart_point_mem D x)
  have hycont : ContinuousAt
      (fun s : ℝ => (((e.symm s : frontier D.carrier) : X))) 0 := by
    simpa only [Function.comp_def] using
      continuous_subtype_val.continuousAt.comp
        (e.continuousAt_symm hzeroTarget)
  have hy0 : (((e.symm 0 : frontier D.carrier) : X)) = (x : X) := by
    rw [he0]
  have hysource : ∀ᶠ s : ℝ in 𝓝 0,
      (((e.symm s : frontier D.carrier) : X)) ∈
        (extChartAt SurfaceRealModel (x : X)).source := by
    have htend : Tendsto
        (fun s : ℝ => (((e.symm s : frontier D.carrier) : X)))
        (𝓝 0) (𝓝 (x : X)) := by
      rw [← hy0]
      exact hycont
    exact htend (isOpen_extChartAt_source (x : X) |>.mem_nhds
      (mem_extChartAt_source (x : X)))
  have htarget : ∀ᶠ s : ℝ in 𝓝 0, s ∈ e.target :=
    e.open_target.mem_nhds hzeroTarget
  filter_upwards [htarget, hysource] with s hsTarget hsSource
  have haxis : (((e.symm s : frontier D.carrier) : X)) =
      (smoothBoundaryProductChartAt D x).coordinate.symm (0, s) :=
    smoothBoundaryFrontierChart_symm_apply_of_mem_target D x s hsTarget
  refine ⟨hsTarget, ?_⟩
  rw [← haxis]
  exact (extChartAt SurfaceRealModel (x : X)).left_inv hsSource
/--
%%handwave
name:
  A nonzero coordinate tangent to the frontier
statement:
  For \(x\in\partial D\), there are a smooth curve
  \(b:\mathbb R\to\mathbb C\) and \(w\in\mathbb C\setminus\{0\}\) such
  that, near \(0\), \(\phi_x^{-1}(b(s))\in\partial D\),
  \[
    b(0)=\phi_x(x),\qquad b'(0)=w,
    \qquad D(s\circ\phi_x^{-1})_{\phi_x(x)}(w)=0.
  \]
proof:
  Parameterize the central diameter of a boundary product chart and express
  it in the fixed surface chart.  The transition is a local diffeomorphism,
  so its tangent \(w\) is nonzero.  Since the resulting curve stays in the
  zero set of the global signed coordinate, differentiating gives the kernel
  identity.
-/
theorem exists_smoothFrontierCoordinateTangent
    (D : SmoothBoundaryDomain X) (x : frontier D.carrier) :
    ∃ b : ℝ → ℂ, ∃ w : ℂ,
      ContDiffAt ℝ ∞ b 0 ∧
      (∀ᶠ s in 𝓝 (0 : ℝ), ContDiffAt ℝ ∞ b s) ∧
      b = (fun s : ℝ => extChartAt SurfaceRealModel (x : X)
        ((smoothBoundaryProductChartAt D x).coordinate.symm (0, s))) ∧
      HasDerivAt b w 0 ∧
      b 0 = extChartAt SurfaceRealModel (x : X) x ∧
      w ≠ 0 ∧
      (∀ᶠ s in nhds (0 : ℝ),
        (extChartAt SurfaceRealModel (x : X)).symm (b s) ∈ frontier D.carrier) ∧
      fderiv ℝ
          (fun z : ℂ => smoothBoundaryGlobalSignedCoordinate D
            ((extChartAt SurfaceRealModel (x : X)).symm z))
          (extChartAt SurfaceRealModel (x : X) x) w = 0 := by
  let C := smoothBoundaryProductChartAt D x
  let eInf : PartialDiffeomorph
      𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) X ℂ ∞ :=
    JJMath.Manifold.partialDiffeomorphOfMemMaximalAtlas (chartAt ℂ (x : X))
      (IsManifold.chart_mem_maximalAtlas
        (I := SurfaceRealModel) (n := ∞) (x : X))
  let e : PartialDiffeomorph
      𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) X ℂ ∞ :=
    { eInf with
      contMDiffOn_toFun := eInf.contMDiffOn_toFun.of_le
        (by exact WithTop.coe_le_coe.mpr le_top)
      contMDiffOn_invFun := eInf.contMDiffOn_invFun.of_le
        (by exact WithTop.coe_le_coe.mpr le_top) }
  let C2 : PartialDiffeomorph
      𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ × ℝ) X (ℝ × ℝ) ∞ :=
    { C.coordinate with
      contMDiffOn_toFun := C.coordinate.contMDiffOn_toFun.of_le
        (by exact WithTop.coe_le_coe.mpr le_top)
      contMDiffOn_invFun := C.coordinate.contMDiffOn_invFun.of_le
        (by exact WithTop.coe_le_coe.mpr le_top) }
  let T : PartialDiffeomorph
      𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℂ) (ℝ × ℝ) ℂ ∞ :=
    JJMath.Manifold.PartialDiffeomorph.trans C2.symm e
  let q₀ : ℝ × ℝ := (0, 0)
  let b : ℝ → ℂ := fun s => e (C.coordinate.symm (0, s))
  have hq₀target : q₀ ∈ C.coordinate.target := by
    have hmap := C.coordinate.map_source C.point_mem
    simpa only [C.point_coord, q₀] using hmap
  have hCinv : C.coordinate.symm q₀ = (x : X) := by
    rw [show q₀ = C.coordinate x by simp only [C.point_coord, q₀]]
    exact C.coordinate.left_inv C.point_mem
  have hq₀T : q₀ ∈ T.source := by
    rw [show T.source = C.coordinate.target ∩
        C.coordinate.symm ⁻¹' e.source from
      PartialEquiv.trans_source C.coordinate.symm.toPartialEquiv e.toPartialEquiv]
    refine ⟨hq₀target, ?_⟩
    change C.coordinate.symm q₀ ∈ e.source
    rw [hCinv]
    change (x : X) ∈ (chartAt ℂ (x : X)).source
    exact mem_chart_source ℂ (x : X)
  have hTq₀ : T q₀ = extChartAt SurfaceRealModel (x : X) x := by
    change e (C.coordinate.symm q₀) = _
    rw [hCinv]
    rfl
  have hTdiff : DifferentiableAt ℝ T q₀ :=
    (T.contMDiffOn_toFun.contMDiffAt
      (T.open_source.mem_nhds hq₀T)).mdifferentiableAt (by norm_num)
      |>.differentiableAt
  have hTsmooth : ContDiffAt ℝ ∞ T q₀ :=
    T.contMDiffOn_toFun.contMDiffAt
      (T.open_source.mem_nhds hq₀T) |>.contDiffAt
  have hTbij : Function.Bijective (fderiv ℝ T q₀) := by
    have heT : T.toOpenPartialHomeomorph.MDifferentiable
        𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℂ) := by
      exact ⟨T.mdifferentiableOn (by norm_num),
        T.symm.mdifferentiableOn (by norm_num)⟩
    simpa only [mfderiv_eq_fderiv] using heT.mfderiv_bijective hq₀T
  let w : ℂ := fderiv ℝ T q₀ (0, 1)
  have hline : HasDerivAt (fun s : ℝ => ((0 : ℝ), s)) (0, 1) 0 := by
    simpa using (hasDerivAt_const (x := (0 : ℝ)) (0 : ℝ)).prodMk
      (hasDerivAt_id (x := (0 : ℝ)))
  have hb : HasDerivAt b w 0 := by
    simpa only [b, w, q₀] using
      hTdiff.hasFDerivAt.comp_hasDerivAt 0 hline
  have hbsmooth : ContDiffAt ℝ ∞ b 0 := by
    have hlineSmooth : ContDiffAt ℝ ∞ (fun s : ℝ => ((0 : ℝ), s)) 0 := by
      fun_prop
    simpa only [b, T, Function.comp_def] using hTsmooth.comp 0 hlineSmooth
  have hbsmoothNear : ∀ᶠ s in 𝓝 (0 : ℝ), ContDiffAt ℝ ∞ b s := by
    have hlinecont : ContinuousAt (fun s : ℝ => ((0 : ℝ), s)) 0 := by
      fun_prop
    have hsource : ∀ᶠ s : ℝ in 𝓝 0, ((0 : ℝ), s) ∈ T.source :=
      hlinecont.eventually (T.open_source.mem_nhds (by simpa [q₀] using hq₀T))
    filter_upwards [hsource] with s hs
    have hTs : ContDiffAt ℝ ∞ T (0, s) :=
      T.contMDiffOn_toFun.contMDiffAt (T.open_source.mem_nhds hs) |>.contDiffAt
    have hlineSmooth : ContDiffAt ℝ ∞ (fun r : ℝ => ((0 : ℝ), r)) s := by
      fun_prop
    simpa only [b, T, Function.comp_def] using hTs.comp s hlineSmooth
  have hb0 : b 0 = extChartAt SurfaceRealModel (x : X) x := by
    simpa only [b, q₀] using hTq₀
  have hw : w ≠ 0 := by
    intro hw0
    have hzero : fderiv ℝ T q₀ (0, 1) = fderiv ℝ T q₀ 0 := by
      simp [w, hw0]
    have := hTbij.1 hzero
    norm_num at this
  let hcoord : ℂ → ℝ := fun z => smoothBoundaryGlobalSignedCoordinate D
    ((extChartAt SurfaceRealModel (x : X)).symm z)
  have hhcoord : DifferentiableAt ℝ hcoord
      (extChartAt SurfaceRealModel (x : X) x) := by
    have hcont : ContDiffAt ℝ ∞ hcoord
        (extChartAt SurfaceRealModel (x : X) x) := by
      have hsymm : ContMDiffAt 𝓘(ℝ, ℂ) SurfaceRealModel ∞
          (extChartAt SurfaceRealModel (x : X)).symm
          (extChartAt SurfaceRealModel (x : X) x) :=
        (contMDiffWithinAt_extChartAt_symm_target_self (n := ∞) (x : X)).contMDiffAt
          (isOpen_extChartAt_target (x : X) |>.mem_nhds
            (mem_extChartAt_target (x : X)))
      exact (smoothBoundaryGlobalSignedCoordinate_contMDiff D).contMDiffAt.comp _ hsymm
        |>.contDiffAt
    exact hcont.differentiableAt (by norm_num)
  have hboundary : ∀ᶠ s in nhds (0 : ℝ),
      (extChartAt SurfaceRealModel (x : X)).symm (b s) ∈
        frontier D.carrier := by
    have hlinecont : ContinuousAt (fun s : ℝ => ((0 : ℝ), s)) 0 := by
      fun_prop
    have hsource : ∀ᶠ s : ℝ in nhds 0, ((0 : ℝ), s) ∈ T.source :=
      hlinecont.eventually (T.open_source.mem_nhds (by simpa [q₀] using hq₀T))
    filter_upwards [hsource] with s hs
    have hs' : (0, s) ∈ C.coordinate.target ∧
        C.coordinate.symm (0, s) ∈ e.source := by
      simpa only [T, PartialEquiv.trans_source] using hs
    let y : X := C.coordinate.symm (0, s)
    have hyC : y ∈ C.coordinate.source := C.coordinate.symm.map_source hs'.1
    have hCy : C.coordinate y = (0, s) := C.coordinate.right_inv hs'.1
    have hyfrontier : y ∈ frontier D.carrier :=
      (C.frontier_iff_zero y hyC).mpr (by simp [hCy])
    have hey : e y = extChartAt SurfaceRealModel (x : X) y := rfl
    have heinv : (extChartAt SurfaceRealModel (x : X)).symm (e y) = y := by
      rw [hey]
      exact (extChartAt SurfaceRealModel (x : X)).left_inv (by
        simpa [e] using hs'.2)
    change (extChartAt SurfaceRealModel (x : X)).symm
      (e (C.coordinate.symm (0, s))) ∈ frontier D.carrier
    change (extChartAt SurfaceRealModel (x : X)).symm (e y) ∈
      frontier D.carrier
    rw [heinv]
    exact hyfrontier
  have heqzero : hcoord ∘ b =ᶠ[nhds (0 : ℝ)] fun _ => 0 := by
    filter_upwards [hboundary] with s hs
    exact smoothBoundaryGlobalSignedCoordinate_eq_zero_of_mem_frontier D hs
  have hcomp : HasDerivAt (hcoord ∘ b)
      (fderiv ℝ hcoord (extChartAt SurfaceRealModel (x : X) x) w) 0 := by
    exact hhcoord.hasFDerivAt.comp_hasDerivAt_of_eq 0 hb hb0.symm
  have hzero : HasDerivAt (hcoord ∘ b) 0 0 :=
    (hasDerivAt_const (x := (0 : ℝ)) (0 : ℝ)).congr_of_eventuallyEq heqzero
  have hkernel := hcomp.unique hzero
  have hb_eq : b = fun s : ℝ =>
      extChartAt SurfaceRealModel (x : X) (C.coordinate.symm (0, s)) := by
    rfl
  exact ⟨b, w, hbsmooth, hbsmoothNear, by simpa only [C] using hb_eq, hb, hb0, hw,
    hboundary, by simpa only [hcoord] using hkernel⟩
/--
%%handwave
name:
  Local flow collar at a frontier point
statement:
  For \(x\in\partial D\), there are local coordinates
  \(G(s,t)\) near \((0,0)\) such that \(G(s,0)\) parameterizes the frontier,
  \(G(0,0)=\phi_x(x)\), every derivative \(DG_{(s,t)}\) is invertible near
  the origin, and
  \[
    t\longmapsto\phi_x^{-1}(G(s,t))
  \]
  is an integral curve of the chosen transverse field.
proof:
  Feed the smooth frontier curve into the jointly smooth coordinate flow.
  At \((0,0)\), its two derivative columns are the nonzero frontier tangent
  and the transverse vector.  The signed-coordinate differential annihilates
  the first and is positive on the second, so the columns are independent;
  the inverse-function theorem gives the local collar and invertibility nearby.
-/
theorem exists_smoothFrontierLocalCollar
    (D : SmoothBoundaryDomain X) (x : frontier D.carrier) :
    ∃ b : ℝ → ℂ, ∃ G : (ℝ × ℝ) → ℂ,
      ∃ P : OpenPartialHomeomorph (ℝ × ℝ) ℂ,
        ContDiffAt ℝ ∞ b 0 ∧
        b = (fun s : ℝ => extChartAt SurfaceRealModel (x : X)
          ((smoothBoundaryProductChartAt D x).coordinate.symm (0, s))) ∧
        (∀ᶠ s in nhds (0 : ℝ),
          (extChartAt SurfaceRealModel (x : X)).symm (b s) ∈
            frontier D.carrier) ∧
        ContDiffAt ℝ ∞ G (0, 0) ∧
        (∀ᶠ p : ℝ × ℝ in nhds (0, 0), ContDiffAt ℝ ∞ G p) ∧
        (P : (ℝ × ℝ) → ℂ) = G ∧
        (0, 0) ∈ P.source ∧
        G (0, 0) = extChartAt SurfaceRealModel (x : X) x ∧
        (∀ᶠ s in nhds (0 : ℝ), G (s, 0) = b s) ∧
        (∀ᶠ s : ℝ in nhds 0,
          s ∈ (smoothBoundaryFrontierChart D x).target ∧
          (extChartAt SurfaceRealModel (x : X)).symm (b s) =
            (((smoothBoundaryFrontierChart D x).symm s :
              frontier D.carrier) : X)) ∧
        (∀ᶠ p : ℝ × ℝ in nhds (0, 0),
          ∃ Lp : (ℝ × ℝ) ≃L[ℝ] ℂ,
            HasFDerivAt G (Lp : (ℝ × ℝ) →L[ℝ] ℂ) p) ∧
        (∀ᶠ p : ℝ × ℝ in nhds (0, 0),
          G p ∈ (extChartAt SurfaceRealModel (x : X)).target) ∧
        ∀ᶠ p : ℝ × ℝ in nhds (0, 0),
          HasMFDerivAt 𝓘(ℝ) SurfaceRealModel
            (fun t : ℝ => (extChartAt SurfaceRealModel (x : X)).symm
              (G (p.1, t))) p.2
            ((1 : ℝ →L[ℝ] ℝ).smulRight
              (smoothFrontierTransverseVectorField D
                ((extChartAt SurfaceRealModel (x : X)).symm (G p)))) := by
  rcases exists_smoothFrontierCoordinateTangent D x with
    ⟨b, w, hbsmooth, hbsmoothNear, hb_eq, hb, hb0, hw, hboundary, hkernel⟩
  rcases exists_smoothFrontierCoordinateLocalFlow_with_fderiv_and_ode D (x : X) with
    ⟨f, hf, hfeq, ε, hε, ψ, hψ0, hinit, hfixed, hsmooth, hflowDeriv,
      hcoordinateODE⟩
  let z₀ : ℂ := extChartAt SurfaceRealModel (x : X) x
  let F : ℂ × ℝ → ℂ := fun p =>
    extendLocalCurve ε hε.le (ψ p.1) p.2
  let Q : ℝ × ℝ → ℂ × ℝ := fun p => (b p.1, p.2)
  let G : ℝ × ℝ → ℂ := fun p => F (Q p)
  let ℓ : ℂ →L[ℝ] ℝ := fderiv ℝ
    (fun z : ℂ => smoothBoundaryGlobalSignedCoordinate D
      ((extChartAt SurfaceRealModel (x : X)).symm z)) z₀
  have hfz₀ : f z₀ = smoothFrontierCoordinateVectorField D x z₀ := by
    simpa only [z₀] using mem_of_mem_nhds hfeq
  have hnormal : 0 < ℓ (f z₀) := by
    rw [hfz₀]
    exact fderiv_smoothBoundaryGlobalSignedCoordinate_comp_extChartAt_symm_pos D x
  have hQ0 : Q (0, 0) = (z₀, 0) := by
    simp [Q, z₀, hb0]
  have hFsmooth : ContDiffAt ℝ ∞ F (z₀, 0) := by
    exact (mem_of_mem_nhds hsmooth) 0 (by constructor <;> linarith [hε])
  have hQsmooth : ContDiffAt ℝ ∞ Q (0, 0) := by
    have hbcomp : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => b p.1) (0, 0) :=
      hbsmooth.comp (0, 0) contDiffAt_fst
    exact hbcomp.prodMk contDiffAt_snd
  have hGsmooth : ContDiffAt ℝ ∞ G (0, 0) := by
    have hFQ : ContDiffAt ℝ ∞ F (Q (0, 0)) := by
      rw [hQ0]
      exact hFsmooth
    simpa only [G, Function.comp_def] using hFQ.comp (0, 0) hQsmooth
  have hQsmoothNear : ∀ᶠ p : ℝ × ℝ in 𝓝 (0, 0),
      ContDiffAt ℝ ∞ Q p := by
    have hbNear : ∀ᶠ p : ℝ × ℝ in 𝓝 (0, 0),
        ContDiffAt ℝ ∞ b p.1 := continuousAt_fst.eventually hbsmoothNear
    filter_upwards [hbNear] with p hbp
    simpa only [Q] using (hbp.comp p contDiffAt_fst).prodMk contDiffAt_snd
  have hbTend : Tendsto b (𝓝 (0 : ℝ)) (𝓝 z₀) := by
    have h := hbsmooth.continuousAt
    rw [ContinuousAt, hb0] at h
    simpa only [z₀] using h
  have hFsmoothInitial : ∀ᶠ s : ℝ in 𝓝 0,
      ∀ t ∈ Ioo (-ε) ε, ContDiffAt ℝ ∞ F (b s, t) := by
    simpa only [F] using hbTend.eventually hsmooth
  have hFsmoothPull : ∀ᶠ p : ℝ × ℝ in 𝓝 (0, 0),
      ∀ t ∈ Ioo (-ε) ε, ContDiffAt ℝ ∞ F (b p.1, t) :=
    (show Tendsto (fun p : ℝ × ℝ => p.1) (𝓝 (0, 0)) (𝓝 (0 : ℝ)) from
      continuousAt_fst).eventually hFsmoothInitial
  have htimeNear : ∀ᶠ p : ℝ × ℝ in 𝓝 (0, 0), p.2 ∈ Ioo (-ε) ε :=
    continuousAt_snd.eventually
      (Ioo_mem_nhds (by linarith [hε]) (by linarith [hε]))
  have hGsmoothNear : ∀ᶠ p : ℝ × ℝ in 𝓝 (0, 0),
      ContDiffAt ℝ ∞ G p := by
    filter_upwards [hQsmoothNear, hFsmoothPull, htimeNear]
      with p hQp hFp htp
    have hFQ : ContDiffAt ℝ ∞ F (Q p) := by
      simpa only [Q] using hFp p.2 htp
    simpa only [G, Function.comp_def] using hFQ.comp p hQp
  let Q' : (ℝ × ℝ) →L[ℝ] (ℂ × ℝ) :=
    ((ContinuousLinearMap.toSpanSingleton ℝ w).comp
      (ContinuousLinearMap.fst ℝ ℝ ℝ)).prod
        (ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hQderiv : HasFDerivAt Q Q' (0, 0) := by
    have hbcomp : HasFDerivAt (fun p : ℝ × ℝ => b p.1)
        ((ContinuousLinearMap.toSpanSingleton ℝ w).comp
          (ContinuousLinearMap.fst ℝ ℝ ℝ)) (0, 0) := by
      exact hb.hasFDerivAt.comp (0, 0) hasFDerivAt_fst
    simpa only [Q, Q'] using hbcomp.prodMk hasFDerivAt_snd
  let L : (ℝ × ℝ) →L[ℝ] ℂ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight w +
      (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (f z₀)
  have hFderiv : HasFDerivAt F (fderiv ℝ F (z₀, 0)) (z₀, 0) :=
    hFsmooth.differentiableAt (by norm_num) |>.hasFDerivAt
  have hcompDeriv : HasFDerivAt G
      ((fderiv ℝ F (z₀, 0)).comp Q') (0, 0) := by
    have hFQ : HasFDerivAt F (fderiv ℝ F (z₀, 0)) (Q (0, 0)) := by
      rw [hQ0]
      exact hFderiv
    simpa only [G, Function.comp_def] using hFQ.comp (0, 0) hQderiv
  have hcompEq : (fderiv ℝ F (z₀, 0)).comp Q' = L := by
    apply ContinuousLinearMap.ext
    intro p
    change fderiv ℝ F (z₀, 0) (p.1 • w, p.2) =
      p.1 • w + p.2 • f z₀
    exact hflowDeriv (p.1 • w) p.2
  have hGderiv : HasFDerivAt G L (0, 0) := by
    rw [← hcompEq]
    exact hcompDeriv
  have hLinj : Function.Injective L := by
    intro p q hpq
    rw [← sub_eq_zero]
    let d : ℝ × ℝ := p - q
    have hLd : L d = 0 := by
      dsimp [d]
      rw [map_sub, hpq, sub_self]
    have hsecond : d.2 = 0 := by
      have happ := congrArg ℓ hLd
      change ℓ (d.1 • w + d.2 • f z₀) = ℓ 0 at happ
      rw [map_add, map_smul, map_smul, hkernel, smul_zero,
        zero_add, map_zero] at happ
      exact (smul_eq_zero.mp happ).resolve_right hnormal.ne'
    have hfirst : d.1 = 0 := by
      have hfirstmul : d.1 • w = 0 := by
        change d.1 • w + d.2 • f z₀ = 0 at hLd
        simpa [hsecond] using hLd
      exact (smul_eq_zero.mp hfirstmul).resolve_right hw
    apply Prod.ext
    · exact hfirst
    · exact hsecond
  have hLsurj : Function.Surjective L := by
    let A : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
      Complex.equivRealProdLm.toLinearMap.comp L.toLinearMap
    have hAinj : Function.Injective A :=
      Complex.equivRealProdLm.injective.comp hLinj
    have hAsurj : Function.Surjective A :=
      LinearMap.surjective_of_injective hAinj
    intro z
    obtain ⟨p, hp⟩ := hAsurj (Complex.equivRealProdLm z)
    refine ⟨p, Complex.equivRealProdLm.injective ?_⟩
    simpa [A] using hp
  have hLbij : Function.Bijective L := ⟨hLinj, hLsurj⟩
  let eL : (ℝ × ℝ) ≃L[ℝ] ℂ :=
    (LinearEquiv.ofBijective L.toLinearMap hLbij).toContinuousLinearEquiv
  have heL : (eL : (ℝ × ℝ) →L[ℝ] ℂ) = L := by
    apply ContinuousLinearMap.ext
    intro p
    rfl
  have hGderiv' : HasFDerivAt G (eL : (ℝ × ℝ) →L[ℝ] ℂ) (0, 0) := by
    rw [heL]
    exact hGderiv
  let P : OpenPartialHomeomorph (ℝ × ℝ) ℂ :=
    hGsmooth.toOpenPartialHomeomorph G hGderiv' (by norm_num)
  have hPcoe : (P : (ℝ × ℝ) → ℂ) = G := by
    exact hGsmooth.toOpenPartialHomeomorph_coe hGderiv' (by norm_num)
  have hPmem : (0, 0) ∈ P.source := by
    exact hGsmooth.mem_toOpenPartialHomeomorph_source hGderiv' (by norm_num)
  have hderivContinuous : ContinuousAt (fderiv ℝ G) (0, 0) :=
    hGsmooth.continuousAt_fderiv (by norm_num)
  have hderiv0 : fderiv ℝ G (0, 0) =
      (eL : (ℝ × ℝ) →L[ℝ] ℂ) := hGderiv'.fderiv
  have hderivEquiv : ∀ᶠ p : ℝ × ℝ in nhds (0, 0),
      fderiv ℝ G p ∈
        range ((↑) : ((ℝ × ℝ) ≃L[ℝ] ℂ) →
          ((ℝ × ℝ) →L[ℝ] ℂ)) := by
    apply hderivContinuous.eventually
      (ContinuousLinearEquiv.isOpen.mem_nhds ?_)
    exact ⟨eL, hderiv0.symm⟩
  have hregular : ∀ᶠ p : ℝ × ℝ in nhds (0, 0),
      ∃ Lp : (ℝ × ℝ) ≃L[ℝ] ℂ,
        HasFDerivAt G (Lp : (ℝ × ℝ) →L[ℝ] ℂ) p := by
    filter_upwards [hGsmoothNear, hderivEquiv]
      with p hp hpequiv
    rcases hpequiv with ⟨Lp, hLp⟩
    refine ⟨Lp, ?_⟩
    rw [hLp]
    exact hp.differentiableAt (by norm_num) |>.hasFDerivAt
  have hG0 : G (0, 0) = z₀ := by
    rw [show G (0, 0) = extendLocalCurve ε hε.le (ψ z₀) 0 by
      simp [G, F, Q, hb0, z₀]]
    rw [extendLocalCurve_apply_of_mem ε hε.le (ψ z₀)
      (show (0 : ℝ) ∈ Icc (-ε) ε by constructor <;> linarith [hε])]
    simpa only [z₀] using mem_of_mem_nhds hinit
  have hGboundary : ∀ᶠ s in nhds (0 : ℝ), G (s, 0) = b s := by
    have hbcont : Tendsto b (nhds 0) (nhds z₀) := by
      rw [show z₀ = b 0 by simpa only [z₀] using hb0.symm]
      exact hb.continuousAt
    have hinitb := hbcont.eventually hinit
    filter_upwards [hinitb] with s hs
    rw [show G (s, 0) = extendLocalCurve ε hε.le (ψ (b s)) 0 by
      simp [G, F, Q]]
    rw [extendLocalCurve_apply_of_mem ε hε.le (ψ (b s))
      (show (0 : ℝ) ∈ Icc (-ε) ε by constructor <;> linarith [hε])]
    exact hs
  have haxis : ∀ᶠ s : ℝ in nhds 0,
      s ∈ (smoothBoundaryFrontierChart D x).target ∧
      (extChartAt SurfaceRealModel (x : X)).symm (b s) =
        (((smoothBoundaryFrontierChart D x).symm s :
          frontier D.carrier) : X) := by
    filter_upwards [eventually_extChartAt_symm_productAxis_eq D x]
      with s hs
    refine ⟨hs.1, ?_⟩
    rw [hb_eq, hs.2]
    exact (smoothBoundaryFrontierChart_symm_apply_of_mem_target
      D x s hs.1).symm
  have hQtend : Tendsto Q (nhds (0, 0)) (nhds (z₀, 0)) := by
    have hcont := hQsmooth.continuousAt
    rw [continuousAt_def, hQ0] at hcont
    exact hcont
  have hcoordinateODEQ := hQtend.eventually hcoordinateODE
  have htargetFlow : ∀ᶠ p : ℝ × ℝ in nhds (0, 0),
      G p ∈ (extChartAt SurfaceRealModel (x : X)).target := by
    filter_upwards [hcoordinateODEQ] with p hp
    simpa only [G, F, Q] using hp.1
  have hmanifoldFlow : ∀ᶠ p : ℝ × ℝ in nhds (0, 0),
      HasMFDerivAt 𝓘(ℝ) SurfaceRealModel
        (fun t : ℝ => (extChartAt SurfaceRealModel (x : X)).symm
          (G (p.1, t))) p.2
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (smoothFrontierTransverseVectorField D
            ((extChartAt SurfaceRealModel (x : X)).symm (G p)))) := by
    filter_upwards [hcoordinateODEQ] with p hp
    apply hasMFDerivAt_extChartAt_symm_of_hasDerivAt_smoothFrontierCoordinateVectorField
      D (x : X) (fun t : ℝ => G (p.1, t)) p.2
    · simpa only [G, F, Q] using hp.1
    · simpa only [G, F, Q] using hp.2
  exact ⟨b, G, P, hbsmooth, hb_eq, hboundary, hGsmooth, hGsmoothNear, hPcoe, hPmem,
    by simpa only [z₀] using hG0, hGboundary, haxis, hregular, htargetFlow,
      hmanifoldFlow⟩

/--
%%handwave
name:
  Rectangular local collar
statement:
  The local flow collar at \(x\in\partial D\) can be restricted to some
  rectangle \(( -\delta,\delta)^2\), \(\delta>0\), on which \(G\) is smooth
  with invertible derivative, \(G(s,0)\) is the frontier parameterization,
  and every curve
  \[
    t\longmapsto\phi_x^{-1}(G(s,t))
  \]
  is an integral curve for \(|t|<\delta\).
proof:
  Intersect the finitely many neighborhoods supplied by the local collar,
  its inverse-function chart, the frontier parameterization, and the flow
  equation.  A sufficiently small product ball, hence a smaller square, lies
  in their intersection.
-/
theorem exists_smoothFrontierLocalCollar_rectangle
    (D : SmoothBoundaryDomain X) (x : frontier D.carrier) :
    ∃ b : ℝ → ℂ, ∃ G : (ℝ × ℝ) → ℂ,
      ∃ P : OpenPartialHomeomorph (ℝ × ℝ) ℂ, ∃ δ : ℝ,
        0 < δ ∧
        Ioo (-δ) δ ×ˢ Ioo (-δ) δ ⊆ P.source ∧
        ContDiffAt ℝ ∞ b 0 ∧
        b = (fun s : ℝ => extChartAt SurfaceRealModel (x : X)
          ((smoothBoundaryProductChartAt D x).coordinate.symm (0, s))) ∧
        (∀ᶠ s in nhds (0 : ℝ),
          (extChartAt SurfaceRealModel (x : X)).symm (b s) ∈
            frontier D.carrier) ∧
        ContDiffAt ℝ ∞ G (0, 0) ∧
        (P : (ℝ × ℝ) → ℂ) = G ∧
        G (0, 0) = extChartAt SurfaceRealModel (x : X) x ∧
        (∀ᶠ s in nhds (0 : ℝ), G (s, 0) = b s) ∧
        (∀ p ∈ Ioo (-δ) δ ×ˢ Ioo (-δ) δ, ContDiffAt ℝ ∞ G p) ∧
        (∀ p ∈ Ioo (-δ) δ ×ˢ Ioo (-δ) δ,
          ∃ Lp : (ℝ × ℝ) ≃L[ℝ] ℂ,
            HasFDerivAt G (Lp : (ℝ × ℝ) →L[ℝ] ℂ) p) ∧
        (∀ p ∈ Ioo (-δ) δ ×ˢ Ioo (-δ) δ,
          G p ∈ (extChartAt SurfaceRealModel (x : X)).target) ∧
        (∀ s ∈ Ioo (-δ) δ,
          s ∈ (smoothBoundaryFrontierChart D x).target ∧
          (extChartAt SurfaceRealModel (x : X)).symm (G (s, 0)) =
            (((smoothBoundaryFrontierChart D x).symm s :
              frontier D.carrier) : X)) ∧
        ∀ s ∈ Ioo (-δ) δ,
          IsMIntegralCurveOn
            (fun t : ℝ => (extChartAt SurfaceRealModel (x : X)).symm
              (G (s, t)))
            (smoothFrontierTransverseVectorField D) (Ioo (-δ) δ) := by
  rcases exists_smoothFrontierLocalCollar D x with
    ⟨b, G, P, hbsmooth, hb_eq, hboundary, hGsmooth, hGsmoothNear, hPcoe, hPmem,
      hG0, hGboundary, haxis, hregularDeriv, htargetFlow, hmanifoldFlow⟩
  have hinitial₀ : ∀ᶠ s : ℝ in nhds 0,
      s ∈ (smoothBoundaryFrontierChart D x).target ∧
      (extChartAt SurfaceRealModel (x : X)).symm (G (s, 0)) =
        (((smoothBoundaryFrontierChart D x).symm s :
          frontier D.carrier) : X) := by
    filter_upwards [hGboundary, haxis] with s hGs hs
    refine ⟨hs.1, ?_⟩
    rw [hGs]
    exact hs.2
  have hinitial : ∀ᶠ p : ℝ × ℝ in nhds (0, 0),
      p.1 ∈ (smoothBoundaryFrontierChart D x).target ∧
      (extChartAt SurfaceRealModel (x : X)).symm (G (p.1, 0)) =
        (((smoothBoundaryFrontierChart D x).symm p.1 :
          frontier D.carrier) : X) :=
    (show Tendsto (fun p : ℝ × ℝ => p.1) (nhds (0, 0)) (nhds 0) from
      continuousAt_fst) hinitial₀
  have hevent : ∀ᶠ p : ℝ × ℝ in nhds (0, 0),
      p ∈ P.source ∧
        ContDiffAt ℝ ∞ G p ∧
        (∃ Lp : (ℝ × ℝ) ≃L[ℝ] ℂ,
          HasFDerivAt G (Lp : (ℝ × ℝ) →L[ℝ] ℂ) p) ∧
        G p ∈ (extChartAt SurfaceRealModel (x : X)).target ∧
        HasMFDerivAt 𝓘(ℝ) SurfaceRealModel
          (fun t : ℝ => (extChartAt SurfaceRealModel (x : X)).symm
            (G (p.1, t))) p.2
          ((1 : ℝ →L[ℝ] ℝ).smulRight
            (smoothFrontierTransverseVectorField D
              ((extChartAt SurfaceRealModel (x : X)).symm (G p)))) ∧
        (p.1 ∈ (smoothBoundaryFrontierChart D x).target ∧
          (extChartAt SurfaceRealModel (x : X)).symm (G (p.1, 0)) =
            (((smoothBoundaryFrontierChart D x).symm p.1 :
              frontier D.carrier) : X)) := by
    filter_upwards [P.open_source.mem_nhds hPmem,
      hGsmoothNear, hregularDeriv, htargetFlow,
      hmanifoldFlow, hinitial]
      with p hp hsmooth hregular htarget hflow hinit
    exact ⟨hp, hsmooth, hregular, htarget, hflow, hinit⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp hevent
  have hrect : Metric.ball (0 : ℝ) δ ×ˢ Metric.ball (0 : ℝ) δ ⊆
      P.source := by
    intro p hp
    exact (hball p (by simpa only [ball_prod_same] using hp)).1
  have hcurves : ∀ s ∈ Ioo (-δ) δ,
      IsMIntegralCurveOn
        (fun t : ℝ => (extChartAt SurfaceRealModel (x : X)).symm
          (G (s, t)))
        (smoothFrontierTransverseVectorField D) (Ioo (-δ) δ) := by
    intro s hs t ht
    have hp : (s, t) ∈ Metric.ball ((0 : ℝ), (0 : ℝ)) δ := by
      have hp' : (s, t) ∈ Metric.ball (0 : ℝ) δ ×ˢ
          Metric.ball (0 : ℝ) δ := by
        simpa only [Real.ball_zero_eq_Ioo] using And.intro hs ht
      rw [ball_prod_same] at hp'
      exact hp'
    exact (hball (s, t) hp).2.2.2.2.1.hasMFDerivWithinAt
  have hregular : ∀ p ∈ Ioo (-δ) δ ×ˢ Ioo (-δ) δ,
      ContDiffAt ℝ ∞ G p := by
    intro p hp
    have hp' : p ∈ Metric.ball ((0 : ℝ), (0 : ℝ)) δ := by
      rw [← ball_prod_same]
      simpa only [Real.ball_zero_eq_Ioo] using hp
    exact (hball p hp').2.1
  have hregularDeriv' : ∀ p ∈ Ioo (-δ) δ ×ˢ Ioo (-δ) δ,
      ∃ Lp : (ℝ × ℝ) ≃L[ℝ] ℂ,
        HasFDerivAt G (Lp : (ℝ × ℝ) →L[ℝ] ℂ) p := by
    intro p hp
    have hp' : p ∈ Metric.ball ((0 : ℝ), (0 : ℝ)) δ := by
      rw [← ball_prod_same]
      simpa only [Real.ball_zero_eq_Ioo] using hp
    exact (hball p hp').2.2.1
  have htarget : ∀ p ∈ Ioo (-δ) δ ×ˢ Ioo (-δ) δ,
      G p ∈ (extChartAt SurfaceRealModel (x : X)).target := by
    intro p hp
    have hp' : p ∈ Metric.ball ((0 : ℝ), (0 : ℝ)) δ := by
      rw [← ball_prod_same]
      simpa only [Real.ball_zero_eq_Ioo] using hp
    exact (hball p hp').2.2.2.1
  have hinitial' : ∀ s ∈ Ioo (-δ) δ,
      s ∈ (smoothBoundaryFrontierChart D x).target ∧
      (extChartAt SurfaceRealModel (x : X)).symm (G (s, 0)) =
        (((smoothBoundaryFrontierChart D x).symm s :
          frontier D.carrier) : X) := by
    intro s hs
    have hp : (s, (0 : ℝ)) ∈ Metric.ball ((0 : ℝ), (0 : ℝ)) δ := by
      have hp' : (s, (0 : ℝ)) ∈ Metric.ball (0 : ℝ) δ ×ˢ
          Metric.ball (0 : ℝ) δ := by
        rw [mem_prod]
        refine ⟨?_, Metric.mem_ball_self hδ⟩
        simpa only [Real.ball_zero_eq_Ioo] using hs
      rw [ball_prod_same] at hp'
      exact hp'
    exact (hball (s, 0) hp).2.2.2.2.2
  refine ⟨b, G, P, δ, hδ, ?_, hbsmooth, hb_eq, hboundary, hGsmooth,
    hPcoe, hG0, hGboundary, hregular, hregularDeriv', htarget, hinitial',
    hcurves⟩
  simpa only [Real.ball_zero_eq_Ioo] using hrect

/--
%%handwave
name:
  A transverse-flow patch on the frontier
statement:
  Every \(x\in\partial D\) has a relatively open neighborhood \(V\), a
  number \(\delta>0\), and a map
  \(\Phi:V\times(-\delta,\delta)\to X\) such that
  \(\Phi(q,0)=q\), each \(t\mapsto\Phi(q,t)\) is an integral curve of the
  transverse field, and \(\Phi\) is smooth, injective, open, and has a smooth
  local inverse on its image.
proof:
  Reparameterize the rectangular local collar by the intrinsic frontier
  coordinate.  The inverse-function chart supplies injectivity, openness, and
  the inverse; the collar identities give the initial condition and integral
  curves, and composition of the smooth coordinate maps gives smoothness.
-/
theorem exists_smoothFrontierFlowPatch
    (D : SmoothBoundaryDomain X) (x : frontier D.carrier) :
    ∃ V : Set (frontier D.carrier),
      IsOpen V ∧ x ∈ V ∧
      ∃ δ : ℝ, 0 < δ ∧
      ∃ Φ : frontier D.carrier × ℝ → X,
        (letI := smoothBoundaryFrontierChartedSpace D
         ∀ q ∈ V, ∀ t ∈ Ioo (-δ) δ,
          ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod
              (modelWithCornersSelf ℝ ℝ))
            SurfaceRealModel ∞ Φ (q, t)) ∧
        InjOn Φ (V ×ˢ Ioo (-δ) δ) ∧
        IsOpenMap ((V ×ˢ Ioo (-δ) δ).restrict Φ) ∧
        (∃ Θ : X → frontier D.carrier × ℝ,
          (letI := smoothBoundaryFrontierChartedSpace D
           ∀ z ∈ V ×ˢ Ioo (-δ) δ,
            ContMDiffAt SurfaceRealModel
              ((modelWithCornersSelf ℝ ℝ).prod
                (modelWithCornersSelf ℝ ℝ)) ∞ Θ (Φ z)) ∧
          LeftInvOn Θ Φ (V ×ˢ Ioo (-δ) δ)) ∧
        (∀ q ∈ V, Φ (q, 0) = q) ∧
        ∀ q ∈ V,
          IsMIntegralCurveOn (fun t : ℝ => Φ (q, t))
            (smoothFrontierTransverseVectorField D) (Ioo (-δ) δ) := by
  rcases exists_smoothFrontierLocalCollar_rectangle D x with
    ⟨b, G, P, δ, hδ, hrect, hbsmooth, hb_eq, hboundary, hGsmooth,
      hPcoe, hG0, hGboundary, hregular, hregularDeriv, htarget, hinitial,
      hcurves⟩
  letI := smoothBoundaryFrontierChartedSpace D
  letI : IsManifold (modelWithCornersSelf ℝ ℝ) ∞
      (frontier D.carrier) := smoothBoundaryDomain_frontier_isSmoothOneManifold D
  let e := smoothBoundaryFrontierChart D x
  let V : Set (frontier D.carrier) := e.source ∩ e ⁻¹' Ioo (-δ) δ
  let Φ : frontier D.carrier × ℝ → X := fun p =>
    (extChartAt SurfaceRealModel (x : X)).symm (G (e p.1, p.2))
  have hVopen : IsOpen V := e.isOpen_inter_preimage isOpen_Ioo
  have hex : e x = 0 := by
    rw [smoothBoundaryFrontierChart_apply]
    simp only [(smoothBoundaryProductChartAt D x).point_coord]
  have hxV : x ∈ V := by
    refine ⟨smoothBoundaryFrontierChart_point_mem D x, ?_⟩
    change e x ∈ Ioo (-δ) δ
    rw [hex]
    constructor <;> linarith
  have hΦsmooth : ∀ q ∈ V, ∀ t ∈ Ioo (-δ) δ,
      ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod
          (modelWithCornersSelf ℝ ℝ)) SurfaceRealModel ∞ Φ (q, t) := by
    intro q hq t ht
    have he : ContMDiffAt (modelWithCornersSelf ℝ ℝ)
        (modelWithCornersSelf ℝ ℝ) ∞ e q := by
      simpa only [e, modelWithCornersSelf_coe, id_eq] using
        (contMDiffAt_extChartAt' (I := modelWithCornersSelf ℝ ℝ)
          (n := ∞) hq.1)
    have hpair : ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod
        (modelWithCornersSelf ℝ ℝ))
        ((modelWithCornersSelf ℝ ℝ).prod (modelWithCornersSelf ℝ ℝ)) ∞
        (fun z : frontier D.carrier × ℝ => (e z.1, z.2)) (q, t) :=
      (he.comp (q, t) contMDiffAt_fst).prodMk contMDiffAt_snd
    have hmodel : ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod
        (modelWithCornersSelf ℝ ℝ)) (modelWithCornersSelf ℝ (ℝ × ℝ)) ∞
        (fun z : ℝ × ℝ => z) (e q, t) := by
      rw [contMDiffAt_iff]
      refine ⟨continuousAt_id, ?_⟩
      simp only [mfld_simps]
      exact contDiffWithinAt_id
    have hpairSelf : ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod
        (modelWithCornersSelf ℝ ℝ)) (modelWithCornersSelf ℝ (ℝ × ℝ)) ∞
        (fun z : frontier D.carrier × ℝ => (e z.1, z.2)) (q, t) := by
      simpa only [Function.comp_def] using hmodel.comp (q, t) hpair
    have hz : (e q, t) ∈ Ioo (-δ) δ ×ˢ Ioo (-δ) δ := ⟨hq.2, ht⟩
    have hG : ContMDiffAt (modelWithCornersSelf ℝ (ℝ × ℝ))
        (modelWithCornersSelf ℝ ℂ) ∞ G (e q, t) :=
      (hregular (e q, t) hz).contMDiffAt
    have hGcomp : ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod
        (modelWithCornersSelf ℝ ℝ)) (modelWithCornersSelf ℝ ℂ) ∞
        (fun z : frontier D.carrier × ℝ => G (e z.1, z.2)) (q, t) := by
      simpa only [Function.comp_def] using hG.comp (q, t) hpairSelf
    have hInvWithin := contMDiffWithinAt_extChartAt_symm_target
      (I := SurfaceRealModel) (n := ∞) (x : X) (htarget (e q, t) hz)
    have hInv : ContMDiffAt (modelWithCornersSelf ℝ ℂ)
        SurfaceRealModel ∞ (extChartAt SurfaceRealModel (x : X)).symm
          (G (e q, t)) :=
      hInvWithin.contMDiffAt
        (isOpen_extChartAt_target (x : X) |>.mem_nhds
          (htarget (e q, t) hz))
    simpa only [Φ, e, Function.comp_def] using hInv.comp (q, t) hGcomp
  have hΦinjective : InjOn Φ (V ×ˢ Ioo (-δ) δ) := by
    intro z hz w hw hzw
    have hzrect : (e z.1, z.2) ∈ Ioo (-δ) δ ×ˢ Ioo (-δ) δ :=
      ⟨hz.1.2, hz.2⟩
    have hwrect : (e w.1, w.2) ∈ Ioo (-δ) δ ×ˢ Ioo (-δ) δ :=
      ⟨hw.1.2, hw.2⟩
    have hG : G (e z.1, z.2) = G (e w.1, w.2) := by
      have happ := congrArg (extChartAt SurfaceRealModel (x : X)) hzw
      change (extChartAt SurfaceRealModel (x : X))
          ((extChartAt SurfaceRealModel (x : X)).symm (G (e z.1, z.2))) =
        (extChartAt SurfaceRealModel (x : X))
          ((extChartAt SurfaceRealModel (x : X)).symm (G (e w.1, w.2))) at happ
      rw [(extChartAt SurfaceRealModel (x : X)).right_inv
          (htarget (e z.1, z.2) hzrect),
        (extChartAt SurfaceRealModel (x : X)).right_inv
          (htarget (e w.1, w.2) hwrect)] at happ
      exact happ
    have hpair : (e z.1, z.2) = (e w.1, w.2) := by
      apply P.injOn (hrect hzrect) (hrect hwrect)
      simpa only [hPcoe] using hG
    have hfirst : z.1 = w.1 :=
      e.injOn hz.1.1 hw.1.1 (congrArg Prod.fst hpair)
    have hsecond : z.2 = w.2 :=
      congrArg (fun a : ℝ × ℝ => a.2) hpair
    exact Prod.ext hfirst hsecond
  let Q : OpenPartialHomeomorph (frontier D.carrier × ℝ) X :=
    ((e.prod (OpenPartialHomeomorph.refl ℝ)).trans P).trans
      (chartAt ℂ (x : X)).symm
  have hQsource : V ×ˢ Ioo (-δ) δ ⊆ Q.source := by
    intro z hz
    change z ∈ (((e.prod (OpenPartialHomeomorph.refl ℝ)).trans P).trans
      (chartAt ℂ (x : X)).symm).source
    rw [OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.trans_source]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact ⟨hz.1.1, mem_univ z.2⟩
    · change (e z.1, z.2) ∈ P.source
      exact hrect ⟨hz.1.2, hz.2⟩
    · change P (e z.1, z.2) ∈ (chartAt ℂ (x : X)).target
      rw [hPcoe]
      have ht := htarget (e z.1, z.2) ⟨hz.1.2, hz.2⟩
      rw [extChartAt_target] at ht
      simpa only [modelWithCornersSelf_coe_symm, id_eq] using ht.1
  have hΦQ : EqOn Φ Q (V ×ˢ Ioo (-δ) δ) := by
    intro z hz
    simp only [Φ, Q, OpenPartialHomeomorph.trans_apply,
      OpenPartialHomeomorph.prod_apply, OpenPartialHomeomorph.refl_apply,
      hPcoe, extChartAt_coe_symm, modelWithCornersSelf_coe_symm,
      Function.comp_id, id_eq]
  have hΦopen : IsOpenMap ((V ×ˢ Ioo (-δ) δ).restrict Φ) :=
    isOpenMap_restrict_of_eqOn_openPartialHomeomorph
      (hVopen.prod isOpen_Ioo) Q hQsource hΦQ
  let Θ : X → frontier D.carrier × ℝ := fun y =>
    let st := P.symm (extChartAt SurfaceRealModel (x : X) y)
    (e.symm st.1, st.2)
  have hΘleft : LeftInvOn Θ Φ (V ×ˢ Ioo (-δ) δ) := by
    intro z hz
    have hp : (e z.1, z.2) ∈ Ioo (-δ) δ ×ˢ Ioo (-δ) δ :=
      ⟨hz.1.2, hz.2⟩
    have hchart : extChartAt SurfaceRealModel (x : X) (Φ z) =
        G (e z.1, z.2) := by
      exact (extChartAt SurfaceRealModel (x : X)).right_inv
        (htarget (e z.1, z.2) hp)
    have hPleft : P.symm (G (e z.1, z.2)) = (e z.1, z.2) := by
      rw [← hPcoe]
      exact P.left_inv (hrect hp)
    simp only [Θ, hchart, hPleft]
    exact Prod.ext (e.left_inv hz.1.1) rfl
  have hΘsmooth : ∀ z ∈ V ×ˢ Ioo (-δ) δ,
      ContMDiffAt SurfaceRealModel
        ((modelWithCornersSelf ℝ ℝ).prod
          (modelWithCornersSelf ℝ ℝ)) ∞ Θ (Φ z) := by
    intro z hz
    let pz : ℝ × ℝ := (e z.1, z.2)
    have hp : pz ∈ Ioo (-δ) δ ×ˢ Ioo (-δ) δ :=
      ⟨hz.1.2, hz.2⟩
    have hpSource : pz ∈ P.source := hrect hp
    have hchartValue : extChartAt SurfaceRealModel (x : X) (Φ z) = G pz :=
      (extChartAt SurfaceRealModel (x : X)).right_inv (htarget pz hp)
    have hΦsource : Φ z ∈ (extChartAt SurfaceRealModel (x : X)).source :=
      (extChartAt SurfaceRealModel (x : X)).symm.map_source (htarget pz hp)
    have hchartSmooth : ContMDiffAt SurfaceRealModel
        (modelWithCornersSelf ℝ ℂ) ∞
        (extChartAt SurfaceRealModel (x : X)) (Φ z) :=
      contMDiffAt_extChartAt' (by
        simpa only [extChartAt_source] using hΦsource)
    rcases hregularDeriv pz hp with ⟨Lp, hLp⟩
    have hPleft : P.symm (G pz) = pz := by
      rw [← hPcoe]
      exact P.left_inv hpSource
    have hPtarget : G pz ∈ P.target := by
      rw [← hPcoe]
      exact P.map_source hpSource
    have hPderiv : HasFDerivAt P
        (Lp : (ℝ × ℝ) →L[ℝ] ℂ) (P.symm (G pz)) := by
      rw [hPleft]
      simpa only [hPcoe] using hLp
    have hPsmooth : ContDiffAt ℝ ∞ P (P.symm (G pz)) := by
      rw [hPleft]
      simpa only [hPcoe] using hregular pz hp
    have hPinvSmooth : ContDiffAt ℝ ∞ P.symm (G pz) :=
      P.contDiffAt_symm hPtarget hPderiv hPsmooth
    have hPinvComp : ContMDiffAt SurfaceRealModel
        (modelWithCornersSelf ℝ (ℝ × ℝ)) ∞
        (fun y : X => P.symm (extChartAt SurfaceRealModel (x : X) y))
        (Φ z) := by
      have hPinvAt : ContDiffAt ℝ ∞ P.symm
          (extChartAt SurfaceRealModel (x : X) (Φ z)) := by
        rw [hchartValue]
        exact hPinvSmooth
      simpa only [Function.comp_def] using
        hPinvAt.comp_contMDiffAt hchartSmooth
    have heTarget : e z.1 ∈ e.target := e.map_source hz.1.1
    have heTarget' : e z.1 ∈
        (extChartAt (modelWithCornersSelf ℝ ℝ) x).target := by
      rw [extChartAt_target]
      refine ⟨?_, mem_range_self _⟩
      simpa only [e, modelWithCornersSelf_coe_symm, id_eq] using heTarget
    have heInvWithin := contMDiffWithinAt_extChartAt_symm_target
      (I := modelWithCornersSelf ℝ ℝ) (n := ∞) x heTarget'
    have heInv : ContMDiffAt (modelWithCornersSelf ℝ ℝ)
        (modelWithCornersSelf ℝ ℝ) ∞ e.symm (e z.1) := by
      simpa only [e, extChartAt_coe_symm, modelWithCornersSelf_coe_symm,
        Function.comp_id] using heInvWithin.contMDiffAt
          (isOpen_extChartAt_target x |>.mem_nhds heTarget')
    have hmodel : ContMDiffAt (modelWithCornersSelf ℝ (ℝ × ℝ))
        ((modelWithCornersSelf ℝ ℝ).prod
          (modelWithCornersSelf ℝ ℝ)) ∞
        (fun u : ℝ × ℝ => u)
        (P.symm (extChartAt SurfaceRealModel (x : X) (Φ z))) := by
      rw [contMDiffAt_iff]
      refine ⟨continuousAt_id, ?_⟩
      simp only [mfld_simps]
      exact contDiffWithinAt_id
    have hPinvCompProd : ContMDiffAt SurfaceRealModel
        ((modelWithCornersSelf ℝ ℝ).prod
          (modelWithCornersSelf ℝ ℝ)) ∞
        (fun y : X => P.symm (extChartAt SurfaceRealModel (x : X) y))
        (Φ z) := by
      simpa only [Function.comp_def] using hmodel.comp (Φ z) hPinvComp
    have hfirstCoord : ContMDiffAt SurfaceRealModel
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun y : X => (P.symm
          (extChartAt SurfaceRealModel (x : X) y)).1) (Φ z) :=
      contMDiffAt_fst.comp (Φ z) hPinvCompProd
    have hsecondCoord : ContMDiffAt SurfaceRealModel
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun y : X => (P.symm
          (extChartAt SurfaceRealModel (x : X) y)).2) (Φ z) :=
      contMDiffAt_snd.comp (Φ z) hPinvCompProd
    have hfirst : ContMDiffAt SurfaceRealModel
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun y : X => e.symm (P.symm
          (extChartAt SurfaceRealModel (x : X) y)).1) (Φ z) := by
      have hcoordEq : (P.symm
          (extChartAt SurfaceRealModel (x : X) (Φ z))).1 = e z.1 := by
        rw [hchartValue, hPleft]
      have heInv' : ContMDiffAt (modelWithCornersSelf ℝ ℝ)
          (modelWithCornersSelf ℝ ℝ) ∞ e.symm
          (P.symm (extChartAt SurfaceRealModel (x : X) (Φ z))).1 := by
        rw [hcoordEq]
        exact heInv
      exact heInv'.comp (Φ z) hfirstCoord
    simpa only [Θ] using hfirst.prodMk hsecondCoord
  refine ⟨V, hVopen, hxV, δ, hδ, Φ, hΦsmooth, hΦinjective,
    hΦopen, ⟨Θ, hΘsmooth, hΘleft⟩, ?_, ?_⟩
  · intro q hq
    have hqInitial := hinitial (e q) hq.2
    change (extChartAt SurfaceRealModel (x : X)).symm
      (G (e q, 0)) = (q : X)
    rw [hqInitial.2]
    exact congrArg (fun y : frontier D.carrier => (y : X))
      (e.left_inv hq.1)
  · intro q hq
    exact hcurves (e q) hq.2

/-- Local transverse-flow data over an open subset of the smooth frontier. -/
structure SmoothFrontierFlowPatch (D : SmoothBoundaryDomain X) where
  carrier : Set (frontier D.carrier)
  isOpen_carrier : IsOpen carrier
  timeRadius : ℝ
  timeRadius_pos : 0 < timeRadius
  flow : frontier D.carrier × ℝ → X
  smooth :
    letI := smoothBoundaryFrontierChartedSpace D
    ∀ q ∈ carrier, ∀ t ∈ Ioo (-timeRadius) timeRadius,
      ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod
          (modelWithCornersSelf ℝ ℝ)) SurfaceRealModel ∞ flow (q, t)
  injective : InjOn flow (carrier ×ˢ Ioo (-timeRadius) timeRadius)
  isOpenMap : IsOpenMap
    ((carrier ×ˢ Ioo (-timeRadius) timeRadius).restrict flow)
  inverse : X → frontier D.carrier × ℝ
  inverse_smooth :
    letI := smoothBoundaryFrontierChartedSpace D
    ∀ z ∈ carrier ×ˢ Ioo (-timeRadius) timeRadius,
      ContMDiffAt SurfaceRealModel
        ((modelWithCornersSelf ℝ ℝ).prod
          (modelWithCornersSelf ℝ ℝ)) ∞ inverse (flow z)
  inverse_left : LeftInvOn inverse flow
    (carrier ×ˢ Ioo (-timeRadius) timeRadius)
  initial : ∀ q ∈ carrier, flow (q, 0) = q
  integralCurve : ∀ q ∈ carrier,
    IsMIntegralCurveOn (fun t : ℝ => flow (q, t))
      (smoothFrontierTransverseVectorField D)
      (Ioo (-timeRadius) timeRadius)

/-- A local transverse-flow patch can be chosen around each frontier point. -/
theorem exists_smoothFrontierFlowPatch_through
    (D : SmoothBoundaryDomain X) (x : frontier D.carrier) :
    ∃ P : SmoothFrontierFlowPatch D, x ∈ P.carrier := by
  rcases exists_smoothFrontierFlowPatch D x with
    ⟨V, hVopen, hxV, δ, hδ, Φ, hsmooth, hinjective, hopen, hinverse,
      hinitial, hcurves⟩
  rcases hinverse with ⟨Θ, hΘsmooth, hΘleft⟩
  exact ⟨{
    carrier := V
    isOpen_carrier := hVopen
    timeRadius := δ
    timeRadius_pos := hδ
    flow := Φ
    smooth := hsmooth
    injective := hinjective
    isOpenMap := hopen
    inverse := Θ
    inverse_smooth := hΘsmooth
    inverse_left := hΘleft
    initial := hinitial
    integralCurve := hcurves
  }, hxV⟩

/--
%%handwave
name:
  Finite uniformly timed flow-patch cover
statement:
  Every connected frontier component \(C\) has a finite cover by transverse
  flow patches \(V_1,\ldots,V_N\), and there is \(\varepsilon>0\) no larger
  than any of their time radii.
proof:
  The component is compact and the flow patches centered at its points form
  an open cover, so choose a finite subcover.  The minimum of the finitely many
  positive time radii is a common positive radius.
-/
theorem exists_finite_smoothFrontierFlowPatch_cover
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) :
    ∃ patch :
        {q // q ∈ connectedComponent p} → SmoothFrontierFlowPatch D,
      ∃ centers : Finset {q // q ∈ connectedComponent p},
        connectedComponent p ⊆
          ⋃ q ∈ centers, (patch q).carrier ∧
        ∃ ε : ℝ, 0 < ε ∧
          ∀ q ∈ centers, ε ≤ (patch q).timeRadius := by
  classical
  letI : CompactSpace (frontier D.carrier) :=
    isCompact_iff_compactSpace.mp
      (D.compact_closure.of_isClosed_subset
        isClosed_frontier frontier_subset_closure)
  let C : Set (frontier D.carrier) := connectedComponent p
  let patch : {q // q ∈ C} → SmoothFrontierFlowPatch D := fun q =>
    Classical.choose (exists_smoothFrontierFlowPatch_through D q)
  have hpatch_mem : ∀ q : {q // q ∈ C},
      (q : frontier D.carrier) ∈ (patch q).carrier :=
    fun q => Classical.choose_spec
      (exists_smoothFrontierFlowPatch_through D q)
  have hCcompact : IsCompact C := isClosed_connectedComponent.isCompact
  have hcover : C ⊆ ⋃ q : {q // q ∈ C}, (patch q).carrier := by
    intro q hq
    let q' : {q // q ∈ C} := ⟨q, hq⟩
    exact mem_iUnion.mpr ⟨q', hpatch_mem q'⟩
  rcases hCcompact.elim_finite_subcover
      (fun q : {q // q ∈ C} => (patch q).carrier)
      (fun q => (patch q).isOpen_carrier) hcover with
    ⟨centers, hcenters⟩
  have hpC : p ∈ C := mem_connectedComponent
  have hcenters_nonempty : centers.Nonempty := by
    by_contra hnone
    have hempty : centers = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnone
    have hpcover := hcenters hpC
    rw [hempty] at hpcover
    simp at hpcover
  let radii : Finset ℝ := centers.image fun q => (patch q).timeRadius
  have hradii_nonempty : radii.Nonempty := hcenters_nonempty.image _
  let ε : ℝ := radii.min' hradii_nonempty
  have hεpos : 0 < ε := by
    have hεmem : ε ∈ radii := Finset.min'_mem radii hradii_nonempty
    rcases Finset.mem_image.mp hεmem with ⟨q, hq, hqeq⟩
    rw [← hqeq]
    exact (patch q).timeRadius_pos
  have hεle : ∀ q ∈ centers, ε ≤ (patch q).timeRadius := by
    intro q hq
    exact Finset.min'_le radii _ (Finset.mem_image.mpr ⟨q, hq, rfl⟩)
  exact ⟨patch, centers, hcenters, ε, hεpos, hεle⟩

/--
%%handwave
name:
  Uniqueness of transverse trajectories on a common interval
statement:
  If \(\gamma\) and \(\gamma'\) are integral curves of the same smooth
  transverse field on \(( -\varepsilon,\varepsilon)\) and
  \(( -\eta,\eta)\), respectively, and \(\gamma(0)=\gamma'(0)\), then
  \[
    \gamma(t)=\gamma'(t)
    \quad\text{for }|t|<\min\{\varepsilon,\eta\}.
  \]
proof:
  Restrict both curves to their common interval and apply uniqueness for
  integral curves of a smooth vector field with the same value at time zero.
-/
theorem smoothFrontierTransverseIntegralCurves_eqOn_commonInterval
    (D : SmoothBoundaryDomain X)
    {gamma gamma' : ℝ → X} {ε η : ℝ}
    (hε : 0 < ε) (hη : 0 < η)
    (hgamma : IsMIntegralCurveOn gamma
      (smoothFrontierTransverseVectorField D) (Ioo (-ε) ε))
    (hgamma' : IsMIntegralCurveOn gamma'
      (smoothFrontierTransverseVectorField D) (Ioo (-η) η))
    (hzero : gamma 0 = gamma' 0) :
    EqOn gamma gamma' (Ioo (-(min ε η)) (min ε η)) := by
  have hmin : 0 < min ε η := lt_min hε hη
  apply isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
    (t₀ := 0) (a := -(min ε η)) (b := min ε η)
    (show 0 ∈ Ioo (-(min ε η)) (min ε η) by
      constructor <;> linarith)
    ((smoothFrontierTransverseVectorField_contMDiff D).of_le (by norm_num))
  · exact hgamma.mono
      (Ioo_subset_Ioo (neg_le_neg (min_le_left ε η)) (min_le_left ε η))
  · exact hgamma'.mono
      (Ioo_subset_Ioo (neg_le_neg (min_le_right ε η)) (min_le_right ε η))
  · exact hzero

/-- A finite uniformly timed flow-patch cover glues to a flow family on the
whole connected frontier component.  The glued family agrees on the common
time interval with every local patch containing its initial point. -/
theorem exists_glued_smoothFrontierFlow_of_finite_cover
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier)
    (patch : {q // q ∈ connectedComponent p} →
      SmoothFrontierFlowPatch D)
    (centers : Finset {q // q ∈ connectedComponent p})
    (hcover : connectedComponent p ⊆
      ⋃ q ∈ centers, (patch q).carrier)
    {ε : ℝ} (hε : 0 < ε)
    (hεle : ∀ q ∈ centers, ε ≤ (patch q).timeRadius) :
    ∃ Φ : {q // q ∈ connectedComponent p} × ℝ → X,
      (∀ q, Φ (q, 0) = (q : frontier D.carrier)) ∧
      (∀ q, IsMIntegralCurveOn (fun t : ℝ => Φ (q, t))
        (smoothFrontierTransverseVectorField D) (Ioo (-ε) ε)) ∧
      ∀ i ∈ centers, ∀ q : {q // q ∈ connectedComponent p},
        (q : frontier D.carrier) ∈ (patch i).carrier →
        EqOn (fun t : ℝ => Φ (q, t))
          (fun t : ℝ => (patch i).flow (q, t)) (Ioo (-ε) ε) := by
  classical
  let C := {q // q ∈ connectedComponent p}
  have hcenter_exists : ∀ q : C,
      ∃ i ∈ centers, (q : frontier D.carrier) ∈ (patch i).carrier := by
    intro q
    have hqcover := hcover q.2
    rcases mem_iUnion.mp hqcover with ⟨i, hqi⟩
    rcases mem_iUnion.mp hqi with ⟨hi, hqmem⟩
    exact ⟨i, hi, hqmem⟩
  let center : C → C := fun q => Classical.choose (hcenter_exists q)
  have hcenter_mem : ∀ q : C, center q ∈ centers := fun q =>
    (Classical.choose_spec (hcenter_exists q)).1
  have hq_mem_center : ∀ q : C,
      (q : frontier D.carrier) ∈ (patch (center q)).carrier := fun q =>
    (Classical.choose_spec (hcenter_exists q)).2
  let Φ : C × ℝ → X := fun qt => (patch (center qt.1)).flow (qt.1, qt.2)
  have hinitial : ∀ q : C, Φ (q, 0) = (q : frontier D.carrier) := by
    intro q
    exact (patch (center q)).initial q (hq_mem_center q)
  have hintegral : ∀ q : C,
      IsMIntegralCurveOn (fun t : ℝ => Φ (q, t))
        (smoothFrontierTransverseVectorField D) (Ioo (-ε) ε) := by
    intro q
    exact ((patch (center q)).integralCurve q (hq_mem_center q)).mono
      (Ioo_subset_Ioo
        (neg_le_neg (hεle (center q) (hcenter_mem q)))
        (hεle (center q) (hcenter_mem q)))
  refine ⟨Φ, hinitial, hintegral, ?_⟩
  intro i hi q hqi
  have hagree := smoothFrontierTransverseIntegralCurves_eqOn_commonInterval
    D hε (patch i).timeRadius_pos (hintegral q)
      ((patch i).integralCurve q hqi)
      (by rw [hinitial q, (patch i).initial q hqi])
  simpa only [min_eq_left (hεle i hi)] using hagree

/-- The pointwise glued family extends arbitrarily away from the chosen
component to a map on the whole frontier product.  On the component it is
smooth, because near every point ODE uniqueness identifies it with any one
smooth local patch containing that point. -/
theorem exists_smooth_gluedFrontierFlow_of_finite_cover
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier)
    (patch : {q // q ∈ connectedComponent p} →
      SmoothFrontierFlowPatch D)
    (centers : Finset {q // q ∈ connectedComponent p})
    (hcover : connectedComponent p ⊆
      ⋃ q ∈ centers, (patch q).carrier)
    {ε : ℝ} (hε : 0 < ε)
    (hεle : ∀ q ∈ centers, ε ≤ (patch q).timeRadius) :
    ∃ Ψ : frontier D.carrier × ℝ → X,
      (∀ q ∈ connectedComponent p, Ψ (q, 0) = q) ∧
      (∀ q ∈ connectedComponent p,
        IsMIntegralCurveOn (fun t : ℝ => Ψ (q, t))
          (smoothFrontierTransverseVectorField D) (Ioo (-ε) ε)) ∧
      (letI := smoothBoundaryFrontierChartedSpace D
       ∀ q ∈ connectedComponent p, ∀ t ∈ Ioo (-ε) ε,
        ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod
            (modelWithCornersSelf ℝ ℝ))
          SurfaceRealModel ∞ Ψ (q, t)) ∧
      IsOpenMap ((connectedComponent p ×ˢ Ioo (-ε) ε).restrict Ψ) ∧
      ∀ q ∈ connectedComponent p,
        ∃ V : Set (frontier D.carrier),
          IsOpen V ∧ q ∈ V ∧ V ⊆ connectedComponent p ∧
          InjOn Ψ (V ×ˢ Ioo (-ε) ε) := by
  classical
  rcases exists_glued_smoothFrontierFlow_of_finite_cover
      D p patch centers hcover hε hεle with
    ⟨Φ, hinitial, hintegral, hagree⟩
  let Ψ : frontier D.carrier × ℝ → X := fun qt =>
    if hq : qt.1 ∈ connectedComponent p then Φ (⟨qt.1, hq⟩, qt.2)
    else (qt.1 : X)
  have hΨinitial : ∀ q ∈ connectedComponent p, Ψ (q, 0) = (q : X) := by
    intro q hq
    simp only [Ψ, dif_pos hq]
    exact hinitial ⟨q, hq⟩
  have hΨintegral : ∀ q ∈ connectedComponent p,
      IsMIntegralCurveOn (fun t : ℝ => Ψ (q, t))
        (smoothFrontierTransverseVectorField D) (Ioo (-ε) ε) := by
    intro q hq
    convert hintegral ⟨q, hq⟩ using 1
    funext t
    simp only [Ψ, dif_pos hq]
  letI := smoothBoundaryFrontierChartedSpace D
  letI : IsManifold (modelWithCornersSelf ℝ ℝ) ∞
      (frontier D.carrier) := smoothBoundaryDomain_frontier_isSmoothOneManifold D
  letI : LocallyConnectedSpace (frontier D.carrier) :=
    ChartedSpace.locallyConnectedSpace ℝ (frontier D.carrier)
  have hcomponentOpen : IsOpen (connectedComponent p) := isOpen_connectedComponent
  have hΨsmooth : ∀ q ∈ connectedComponent p, ∀ t ∈ Ioo (-ε) ε,
      ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod
          (modelWithCornersSelf ℝ ℝ)) SurfaceRealModel ∞ Ψ (q, t) := by
    intro q hq t ht
    have hqcover := hcover hq
    rcases mem_iUnion.mp hqcover with ⟨i, hqi⟩
    rcases mem_iUnion.mp hqi with ⟨hi, hqPatch⟩
    have hpatchSmooth := (patch i).smooth q hqPatch t
      (Ioo_subset_Ioo (neg_le_neg (hεle i hi)) (hεle i hi) ht)
    have hcomponentEventually : ∀ᶠ z : frontier D.carrier × ℝ in nhds (q, t),
        z.1 ∈ connectedComponent p :=
      (show Tendsto (fun z : frontier D.carrier × ℝ => z.1)
          (nhds (q, t)) (nhds q) from continuousAt_fst).eventually
        (hcomponentOpen.mem_nhds hq)
    have hpatchEventually : ∀ᶠ z : frontier D.carrier × ℝ in nhds (q, t),
        z.1 ∈ (patch i).carrier :=
      (show Tendsto (fun z : frontier D.carrier × ℝ => z.1)
          (nhds (q, t)) (nhds q) from continuousAt_fst).eventually
        ((patch i).isOpen_carrier.mem_nhds hqPatch)
    have htimeEventually : ∀ᶠ z : frontier D.carrier × ℝ in nhds (q, t),
        z.2 ∈ Ioo (-ε) ε :=
      (show Tendsto (fun z : frontier D.carrier × ℝ => z.2)
          (nhds (q, t)) (nhds t) from continuousAt_snd).eventually
        (isOpen_Ioo.mem_nhds ht)
    have heq : Ψ =ᶠ[nhds (q, t)] (patch i).flow := by
      filter_upwards [hcomponentEventually, hpatchEventually, htimeEventually]
        with z hzComponent hzPatch hzTime
      simp only [Ψ, dif_pos hzComponent]
      exact hagree i hi ⟨z.1, hzComponent⟩ hzPatch hzTime
    exact hpatchSmooth.congr_of_eventuallyEq heq
  have hΨopen : IsOpenMap
      ((connectedComponent p ×ˢ Ioo (-ε) ε).restrict Ψ) := by
    intro U hU
    refine isOpen_iff_forall_mem_open.2 ?_
    intro y hy
    rcases hy with ⟨z, hzU, rfl⟩
    have hqcover := hcover z.2.1
    rcases mem_iUnion.mp hqcover with ⟨i, hqi⟩
    rcases mem_iUnion.mp hqi with ⟨hi, hqPatch⟩
    let T : Set (frontier D.carrier × ℝ) :=
      (connectedComponent p ∩ (patch i).carrier) ×ˢ Ioo (-ε) ε
    have hTopen : IsOpen T :=
      (hcomponentOpen.inter (patch i).isOpen_carrier).prod isOpen_Ioo
    have hTsubPatch : T ⊆
        (patch i).carrier ×ˢ
          Ioo (-(patch i).timeRadius) (patch i).timeRadius := by
      intro w hw
      exact ⟨hw.1.2, Ioo_subset_Ioo
        (neg_le_neg (hεle i hi)) (hεle i hi) hw.2⟩
    have hpatchOpenT : IsOpenMap (T.restrict (patch i).flow) :=
      isOpenMap_restrict_mono (patch i).isOpenMap hTopen hTsubPatch
    have hTsubComponent : T ⊆ connectedComponent p ×ˢ Ioo (-ε) ε := by
      intro w hw
      exact ⟨hw.1.1, hw.2⟩
    let j : T → (connectedComponent p ×ˢ Ioo (-ε) ε) :=
      Set.inclusion hTsubComponent
    let O : Set T := j ⁻¹' U
    have hOopen : IsOpen O :=
      hU.preimage (continuous_inclusion hTsubComponent)
    let W : Set X := T.restrict (patch i).flow '' O
    refine ⟨W, ?_, hpatchOpenT O hOopen, ?_⟩
    · rintro v ⟨w, hwO, rfl⟩
      refine ⟨j w, hwO, ?_⟩
      change Ψ w = (patch i).flow (w : frontier D.carrier × ℝ)
      exact (show Ψ w = (patch i).flow w by
        simp only [Ψ, dif_pos w.2.1.1]
        exact hagree i hi ⟨w.1.1, w.2.1.1⟩ w.2.1.2 w.2.2)
    · let w : T := ⟨z, ⟨⟨z.2.1, hqPatch⟩, z.2.2⟩⟩
      refine ⟨w, ?_, ?_⟩
      · change j w ∈ U
        simpa only [j, w, Set.inclusion_mk] using hzU
      · change (patch i).flow (w : frontier D.carrier × ℝ) = Ψ z
        rw [show Ψ z = (patch i).flow z by
          simp only [Ψ, dif_pos z.2.1]
          exact hagree i hi ⟨z.1.1, z.2.1⟩ hqPatch z.2.2]
  have hΨlocallyInjective : ∀ q ∈ connectedComponent p,
      ∃ V : Set (frontier D.carrier),
        IsOpen V ∧ q ∈ V ∧ V ⊆ connectedComponent p ∧
        InjOn Ψ (V ×ˢ Ioo (-ε) ε) := by
    intro q hq
    have hqcover := hcover hq
    rcases mem_iUnion.mp hqcover with ⟨i, hqi⟩
    rcases mem_iUnion.mp hqi with ⟨hi, hqPatch⟩
    let V : Set (frontier D.carrier) :=
      connectedComponent p ∩ (patch i).carrier
    refine ⟨V, hcomponentOpen.inter (patch i).isOpen_carrier,
      ⟨hq, hqPatch⟩, inter_subset_left, ?_⟩
    intro z hz w hw hzw
    have hzRadius : z.2 ∈ Ioo (-(patch i).timeRadius) (patch i).timeRadius :=
      Ioo_subset_Ioo (neg_le_neg (hεle i hi)) (hεle i hi) hz.2
    have hwRadius : w.2 ∈ Ioo (-(patch i).timeRadius) (patch i).timeRadius :=
      Ioo_subset_Ioo (neg_le_neg (hεle i hi)) (hεle i hi) hw.2
    have hzEq : Ψ z = (patch i).flow z := by
      simp only [Ψ, dif_pos hz.1.1]
      exact hagree i hi ⟨z.1, hz.1.1⟩ hz.1.2 hz.2
    have hwEq : Ψ w = (patch i).flow w := by
      simp only [Ψ, dif_pos hw.1.1]
      exact hagree i hi ⟨w.1, hw.1.1⟩ hw.1.2 hw.2
    apply (patch i).injective ⟨hz.1.2, hzRadius⟩ ⟨hw.1.2, hwRadius⟩
    rw [← hzEq, ← hwEq, hzw]
  exact ⟨Ψ, hΨinitial, hΨintegral, hΨsmooth, hΨopen,
    hΨlocallyInjective⟩

/--
%%handwave
name:
  Glued transverse flow on a frontier component
statement:
  For each connected frontier component \(C\), there are
  \(\varepsilon>0\) and a map
  \(\Psi:C\times(-\varepsilon,\varepsilon)\to X\) such that
  \(\Psi(q,0)=q\), every time curve is an integral curve of the transverse
  field, \(\Psi\) is smooth and open, and it is injective on a neighborhood
  of each \(q\in C\) times the common interval.
proof:
  Choose a finite uniformly timed patch cover.  Select one patch at each
  initial point and define \(\Psi\) with its trajectory; uniqueness on common
  intervals makes this independent of the selection wherever patches overlap.
  Thus the local smoothness, openness, and injectivity of the patches descend
  to the glued family.
-/
theorem exists_glued_smoothFrontierFlow
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) :
    ∃ ε : ℝ, 0 < ε ∧
      ∃ Ψ : frontier D.carrier × ℝ → X,
        (∀ q ∈ connectedComponent p, Ψ (q, 0) = q) ∧
        (∀ q ∈ connectedComponent p,
          IsMIntegralCurveOn (fun t : ℝ => Ψ (q, t))
            (smoothFrontierTransverseVectorField D) (Ioo (-ε) ε)) ∧
        (letI := smoothBoundaryFrontierChartedSpace D
         ∀ q ∈ connectedComponent p, ∀ t ∈ Ioo (-ε) ε,
          ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod
              (modelWithCornersSelf ℝ ℝ))
            SurfaceRealModel ∞ Ψ (q, t)) ∧
        IsOpenMap ((connectedComponent p ×ˢ Ioo (-ε) ε).restrict Ψ) ∧
        ∀ q ∈ connectedComponent p,
          ∃ V : Set (frontier D.carrier),
            IsOpen V ∧ q ∈ V ∧ V ⊆ connectedComponent p ∧
            InjOn Ψ (V ×ˢ Ioo (-ε) ε) := by
  rcases exists_finite_smoothFrontierFlowPatch_cover D p with
    ⟨patch, centers, hcover, ε, hε, hεle⟩
  rcases exists_smooth_gluedFrontierFlow_of_finite_cover
      D p patch centers hcover hε hεle with
    ⟨Ψ, hinitial, hintegral, hsmooth, hopen, hinjective⟩
  exact ⟨ε, hε, Ψ, hinitial, hintegral, hsmooth, hopen, hinjective⟩

/--
%%handwave
name:
  Uniform monotonicity of the glued frontier flow
statement:
  The glued flow on a connected frontier component can be restricted to a
  common interval \(( -\delta,\delta)\) such that every trajectory remains in
  the signed-coordinate neighborhood and
  \[
    t\longmapsto s(\Psi(q,t))
  \]
  is strictly increasing there.
proof:
  Uniform transversality gives a neighborhood of the compact component on
  which \(ds(V)>c>0\).  Compactness permits one common time shrink keeping all
  trajectories in that neighborhood.  The chain rule gives
  \((s\circ\Psi_q)'(t)>c\), hence strict monotonicity.
-/
theorem exists_glued_smoothFrontierFlow_strictMono
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) :
    ∃ δ : ℝ, 0 < δ ∧
      ∃ Ψ : frontier D.carrier × ℝ → X,
        (∀ q ∈ connectedComponent p, Ψ (q, 0) = q) ∧
        (∀ q ∈ connectedComponent p,
          IsMIntegralCurveOn (fun t : ℝ => Ψ (q, t))
            (smoothFrontierTransverseVectorField D) (Ioo (-δ) δ)) ∧
        (letI := smoothBoundaryFrontierChartedSpace D
         ∀ q ∈ connectedComponent p, ∀ t ∈ Ioo (-δ) δ,
          ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod
              (modelWithCornersSelf ℝ ℝ))
            SurfaceRealModel ∞ Ψ (q, t)) ∧
        IsOpenMap ((connectedComponent p ×ˢ Ioo (-δ) δ).restrict Ψ) ∧
        (∀ q ∈ connectedComponent p, ∀ t ∈ Ioo (-δ) δ,
          Ψ (q, t) ∈ smoothBoundaryGlobalCoordinateNeighborhood D) ∧
        ∀ q ∈ connectedComponent p,
          StrictMonoOn (fun t : ℝ =>
            smoothBoundaryGlobalSignedCoordinate D (Ψ (q, t)))
            (Ioo (-δ) δ) := by
  classical
  rcases exists_glued_smoothFrontierFlow D p with
    ⟨ε, hε, Ψ, hinitial, hintegral, hsmooth, hopen, hlocalInjective⟩
  rcases exists_open_smoothFrontierTransverseDerivative_uniformly_pos D p with
    ⟨c, hc, U₀, hU₀open, hfrontierU₀, hU₀pos⟩
  let U : Set X :=
    U₀ ∩ smoothBoundaryGlobalCoordinateNeighborhood D
  have hUopen : IsOpen U :=
    hU₀open.inter (smoothBoundaryGlobalCoordinateNeighborhood_isOpen D)
  have hfrontierU : frontier D.carrier ⊆ U := by
    intro x hx
    exact ⟨hfrontierU₀ hx,
      frontier_subset_smoothBoundaryGlobalCoordinateNeighborhood D hx⟩
  have hUpos : ∀ x ∈ U, c < smoothFrontierTransverseDerivative D x := by
    intro x hx
    exact hU₀pos x hx.1
  letI := smoothBoundaryFrontierChartedSpace D
  letI : IsManifold (modelWithCornersSelf ℝ ℝ) ∞
      (frontier D.carrier) := smoothBoundaryDomain_frontier_isSmoothOneManifold D
  letI : LocallyConnectedSpace (frontier D.carrier) :=
    ChartedSpace.locallyConnectedSpace ℝ (frontier D.carrier)
  letI : CompactSpace (frontier D.carrier) :=
    isCompact_iff_compactSpace.mp
      (D.compact_closure.of_isClosed_subset
        isClosed_frontier frontier_subset_closure)
  let K : Set (frontier D.carrier) := connectedComponent p
  have hKcompact : IsCompact K := isClosed_connectedComponent.isCompact
  let S : Set (frontier D.carrier × ℝ) := Ψ ⁻¹' U
  have hSlocal : ∀ q ∈ K, S ∈ nhds q ×ˢ nhds (0 : ℝ) := by
    intro q hq
    have hzero : (0 : ℝ) ∈ Ioo (-ε) ε := by
      constructor <;> linarith
    have hcont : ContinuousAt Ψ (q, 0) :=
      (hsmooth q hq 0 hzero).continuousAt
    have hvalue : Ψ (q, 0) ∈ U := by
      rw [hinitial q hq]
      exact hfrontierU q.2
    have hpreimage : S ∈ nhds (q, (0 : ℝ)) :=
      hcont (hUopen.mem_nhds hvalue)
    simpa only [nhds_prod_eq] using hpreimage
  have hSuniform : S ∈ nhdsSet K ×ˢ nhds (0 : ℝ) :=
    hKcompact.mem_nhdsSet_prod_of_forall hSlocal
  rcases Filter.mem_prod_iff.mp hSuniform with
    ⟨A, hA, B, hB, hAB⟩
  rcases Metric.mem_nhds_iff.mp hB with ⟨r, hr, hballB⟩
  let δ : ℝ := min ε r / 2
  have hmin : 0 < min ε r := lt_min hε hr
  have hδ : 0 < δ := half_pos hmin
  have hδε : δ < ε :=
    (half_lt_self hmin).trans_le (min_le_left ε r)
  have hδr : δ < r :=
    (half_lt_self hmin).trans_le (min_le_right ε r)
  have hstay : ∀ q ∈ K, ∀ t ∈ Ioo (-δ) δ, Ψ (q, t) ∈ U := by
    intro q hq t ht
    apply hAB
    refine ⟨subset_of_mem_nhdsSet hA hq, hballB ?_⟩
    rw [Real.ball_zero_eq_Ioo]
    exact ⟨by linarith [ht.1, hδr], by linarith [ht.2, hδr]⟩
  have hcurve : ∀ q ∈ K,
      IsMIntegralCurveOn (fun t : ℝ => Ψ (q, t))
        (smoothFrontierTransverseVectorField D) (Ioo (-δ) δ) := by
    intro q hq
    exact (hintegral q hq).mono
      (Ioo_subset_Ioo (neg_le_neg hδε.le) hδε.le)
  have hδsmooth : ∀ q ∈ K, ∀ t ∈ Ioo (-δ) δ,
      ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod
          (modelWithCornersSelf ℝ ℝ)) SurfaceRealModel ∞ Ψ (q, t) := by
    intro q hq t ht
    exact hsmooth q hq t
      (Ioo_subset_Ioo (neg_le_neg hδε.le) hδε.le ht)
  have hδopen : IsOpenMap
      ((connectedComponent p ×ˢ Ioo (-δ) δ).restrict Ψ) := by
    apply isOpenMap_restrict_mono hopen
      (isOpen_connectedComponent.prod isOpen_Ioo)
    intro z hz
    exact ⟨hz.1, Ioo_subset_Ioo (neg_le_neg hδε.le) hδε.le hz.2⟩
  have hmono : ∀ q ∈ K,
      StrictMonoOn (fun t : ℝ =>
        smoothBoundaryGlobalSignedCoordinate D (Ψ (q, t)))
        (Ioo (-δ) δ) := by
    intro q hq
    have hcontinuous : ContinuousOn (fun t : ℝ =>
        smoothBoundaryGlobalSignedCoordinate D (Ψ (q, t)))
        (Ioo (-δ) δ) :=
      (smoothBoundaryGlobalSignedCoordinate_contMDiff D).continuous
        |>.comp_continuousOn (hcurve q hq).continuousOn
    apply strictMonoOn_of_deriv_pos (convex_Ioo (-δ) δ) hcontinuous
    intro t ht
    have ht' : t ∈ Ioo (-δ) δ := by simpa using ht
    rw [smoothBoundaryGlobalSignedCoordinate_deriv_along_transverseIntegralCurve
      D ((hcurve q hq).isMIntegralCurveAt (isOpen_Ioo.mem_nhds ht'))]
    exact hc.trans (hUpos (Ψ (q, t)) (hstay q hq t ht'))
  exact ⟨δ, hδ, Ψ, hinitial, hcurve, hδsmooth, hδopen,
    (fun q hq t ht => (hstay q hq t ht).2), hmono⟩

/--
%%handwave
name:
  An injective transverse flow collar
statement:
  For a connected frontier component \(C\), there are \(\rho>0\) and a
  smooth open map
  \(\Psi:C\times(-\rho,\rho)\to X\) that is injective, satisfies
  \(\Psi(q,0)=q\), and obeys
  \[
    \Psi(q,t)\in D\iff t<0,
    \qquad
    \Psi(q,t)\notin\overline D\iff t>0.
  \]
  Its restriction is therefore an open embedding.
proof:
  Shrink the uniformly monotone glued flow.  Equality of two images forces
  equality of their signed coordinates; strict monotonicity and uniqueness of
  trajectories reduce this to the same time and initial point, while compact
  local injectivity rules out distinct nearby trajectories.  The sign
  characterization of the global coordinate gives the two side identities,
  and an injective open map is an open embedding.
-/
theorem exists_injective_smoothFrontierComponentFlow
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∃ Ψ : frontier D.carrier × ℝ → X,
        (∀ q ∈ connectedComponent p, Ψ (q, 0) = q) ∧
        (∀ q ∈ connectedComponent p,
          IsMIntegralCurveOn (fun t : ℝ => Ψ (q, t))
            (smoothFrontierTransverseVectorField D) (Ioo (-ρ) ρ)) ∧
        (letI := smoothBoundaryFrontierChartedSpace D
         ∀ q ∈ connectedComponent p, ∀ t ∈ Ioo (-ρ) ρ,
          ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod
              (modelWithCornersSelf ℝ ℝ))
            SurfaceRealModel ∞ Ψ (q, t)) ∧
        IsOpenMap ((connectedComponent p ×ˢ Ioo (-ρ) ρ).restrict Ψ) ∧
        InjOn Ψ (connectedComponent p ×ˢ Ioo (-ρ) ρ) ∧
        (∀ q ∈ connectedComponent p, ∀ t ∈ Ioo (-ρ) ρ,
          Ψ (q, t) ∈ smoothBoundaryGlobalCoordinateNeighborhood D) ∧
        (∀ q ∈ connectedComponent p, ∀ t ∈ Ioo (-ρ) ρ,
          Ψ (q, t) ∈ D.carrier ↔ t < 0) ∧
        (∀ q ∈ connectedComponent p, ∀ t ∈ Ioo (-ρ) ρ,
          Ψ (q, t) ∉ closure D.carrier ↔ 0 < t) ∧
        Topology.IsOpenEmbedding
          ((connectedComponent p ×ˢ Ioo (-ρ) ρ).restrict Ψ) := by
  rcases exists_glued_smoothFrontierFlow_strictMono D p with
    ⟨δ, hδ, Ψ, hinitial, hcurve, hsmooth, hopen, hcoordinateNeighborhood,
      hmono⟩
  let ρ : ℝ := δ / 3
  have hρ : 0 < ρ := by positivity
  have hρδ : ρ < δ := by
    dsimp only [ρ]
    linarith
  have hcurveρ : ∀ q ∈ connectedComponent p,
      IsMIntegralCurveOn (fun t : ℝ => Ψ (q, t))
        (smoothFrontierTransverseVectorField D) (Ioo (-ρ) ρ) := by
    intro q hq
    exact (hcurve q hq).mono
      (Ioo_subset_Ioo (neg_le_neg hρδ.le) hρδ.le)
  have hsmoothρ :
      letI := smoothBoundaryFrontierChartedSpace D
      ∀ q ∈ connectedComponent p, ∀ t ∈ Ioo (-ρ) ρ,
        ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod
            (modelWithCornersSelf ℝ ℝ))
          SurfaceRealModel ∞ Ψ (q, t) := by
    letI := smoothBoundaryFrontierChartedSpace D
    intro q hq t ht
    exact hsmooth q hq t
      (Ioo_subset_Ioo (neg_le_neg hρδ.le) hρδ.le ht)
  have hopenρ : IsOpenMap
      ((connectedComponent p ×ˢ Ioo (-ρ) ρ).restrict Ψ) := by
    letI := smoothBoundaryFrontierChartedSpace D
    letI : IsManifold (modelWithCornersSelf ℝ ℝ) ∞
        (frontier D.carrier) := smoothBoundaryDomain_frontier_isSmoothOneManifold D
    letI : LocallyConnectedSpace (frontier D.carrier) :=
      ChartedSpace.locallyConnectedSpace ℝ (frontier D.carrier)
    apply isOpenMap_restrict_mono hopen
      (isOpen_connectedComponent.prod isOpen_Ioo)
    intro z hz
    exact ⟨hz.1, Ioo_subset_Ioo (neg_le_neg hρδ.le) hρδ.le hz.2⟩
  have hcoordinateNeighborhoodρ :
      ∀ q ∈ connectedComponent p, ∀ t ∈ Ioo (-ρ) ρ,
        Ψ (q, t) ∈ smoothBoundaryGlobalCoordinateNeighborhood D := by
    intro q hq t ht
    exact hcoordinateNeighborhood q hq t
      (Ioo_subset_Ioo (neg_le_neg hρδ.le) hρδ.le ht)
  have hsideρ : ∀ q ∈ connectedComponent p, ∀ t ∈ Ioo (-ρ) ρ,
      Ψ (q, t) ∈ D.carrier ↔ t < 0 := by
    intro q hq t ht
    have htδ : t ∈ Ioo (-δ) δ :=
      Ioo_subset_Ioo (neg_le_neg hρδ.le) hρδ.le ht
    have hzeroMem : (0 : ℝ) ∈ Ioo (-δ) δ := by
      constructor <;> linarith
    have hvalueZero :
        smoothBoundaryGlobalSignedCoordinate D (Ψ (q, 0)) = 0 := by
      rw [hinitial q hq]
      exact smoothBoundaryGlobalSignedCoordinate_eq_zero_of_mem_frontier D q.2
    have hcoordinateNeg :
        smoothBoundaryGlobalSignedCoordinate D (Ψ (q, t)) < 0 ↔ t < 0 := by
      constructor
      · intro hneg
        by_contra hnot
        have hle : 0 ≤ t := le_of_not_gt hnot
        rcases hle.eq_or_lt with rfl | hpos
        · linarith
        · have hlt := hmono q hq hzeroMem htδ hpos
          linarith
      · intro hneg
        have hlt := hmono q hq htδ hzeroMem hneg
        linarith
    rw [← hcoordinateNeg]
    exact (smoothBoundaryGlobalSignedCoordinate_lt_zero_iff_mem_carrier D
      (hcoordinateNeighborhoodρ q hq t ht)).symm
  have hexteriorSideρ : ∀ q ∈ connectedComponent p, ∀ t ∈ Ioo (-ρ) ρ,
      Ψ (q, t) ∉ closure D.carrier ↔ 0 < t := by
    intro q hq t ht
    have htδ : t ∈ Ioo (-δ) δ :=
      Ioo_subset_Ioo (neg_le_neg hρδ.le) hρδ.le ht
    have hzeroMem : (0 : ℝ) ∈ Ioo (-δ) δ := by
      constructor <;> linarith
    have hvalueZero :
        smoothBoundaryGlobalSignedCoordinate D (Ψ (q, 0)) = 0 := by
      rw [hinitial q hq]
      exact smoothBoundaryGlobalSignedCoordinate_eq_zero_of_mem_frontier D q.2
    have hcoordinatePos :
        0 < smoothBoundaryGlobalSignedCoordinate D (Ψ (q, t)) ↔ 0 < t := by
      constructor
      · intro hpos
        by_contra hnot
        have hle : t ≤ 0 := le_of_not_gt hnot
        rcases hle.eq_or_lt with hzero | hneg
        · subst t
          linarith
        · have hlt := hmono q hq htδ hzeroMem hneg
          linarith
      · intro hpos
        have hlt := hmono q hq hzeroMem htδ hpos
        linarith
    rw [← hcoordinatePos]
    exact (smoothBoundaryGlobalSignedCoordinate_pos_iff_not_mem_closure D
      (hcoordinateNeighborhoodρ q hq t ht)).symm
  have hinjective : InjOn Ψ
      (connectedComponent p ×ˢ Ioo (-ρ) ρ) := by
    intro z hz w hw hzw
    let Δ : ℝ := w.2 - z.2
    let gamma : ℝ → X := fun s => Ψ (z.1, s)
    let eta : ℝ → X := (fun s => Ψ (w.1, s)) ∘ (fun s => s + Δ)
    let a : ℝ := max (-δ) (-δ - Δ)
    let b : ℝ := min δ (δ - Δ)
    have hzδ : z.2 ∈ Ioo (-δ) δ :=
      Ioo_subset_Ioo (neg_le_neg hρδ.le) hρδ.le hz.2
    have hwδ : w.2 ∈ Ioo (-δ) δ :=
      Ioo_subset_Ioo (neg_le_neg hρδ.le) hρδ.le hw.2
    have hΔ : Δ ∈ Ioo (-δ) δ := by
      dsimp only [Δ, ρ] at hz hw ⊢
      constructor <;> linarith [hz.2.1, hz.2.2, hw.2.1, hw.2.2, hδ]
    have hzCommon : z.2 ∈ Ioo a b := by
      refine ⟨max_lt ?_ ?_, lt_min ?_ ?_⟩
      all_goals dsimp only [a, b, Δ]
      all_goals linarith [hzδ.1, hzδ.2, hwδ.1, hwδ.2]
    have hzeroCommon : (0 : ℝ) ∈ Ioo a b := by
      refine ⟨max_lt (by linarith) ?_, lt_min (by linarith) ?_⟩
      · dsimp only [Δ]
        linarith [hΔ.1]
      · dsimp only [Δ]
        linarith [hΔ.2]
    have hgamma : IsMIntegralCurveOn gamma
        (smoothFrontierTransverseVectorField D) (Ioo a b) :=
      (hcurve z.1 hz.1).mono (by
        intro s hs
        exact ⟨(lt_of_le_of_lt (le_max_left _ _) hs.1),
          (lt_of_lt_of_le hs.2 (min_le_left _ _))⟩)
    have hetaFull : IsMIntegralCurveOn eta
        (smoothFrontierTransverseVectorField D)
        {s | s + Δ ∈ Ioo (-δ) δ} := by
      simpa only [eta] using (hcurve w.1 hw.1).comp_add Δ
    have hetaCurve : IsMIntegralCurveOn eta
        (smoothFrontierTransverseVectorField D) (Ioo a b) :=
      hetaFull.mono (by
        intro s hs
        change s + Δ ∈ Ioo (-δ) δ
        constructor
        · have ha := lt_of_le_of_lt (le_max_right (-δ) (-δ - Δ)) hs.1
          linarith
        · have hb := lt_of_lt_of_le hs.2 (min_le_right δ (δ - Δ))
          linarith)
    have hmeet : gamma z.2 = eta z.2 := by
      change Ψ (z.1, z.2) = Ψ (w.1, z.2 + Δ)
      rw [show z.2 + Δ = w.2 by dsimp only [Δ]; ring]
      exact hzw
    have hagree : EqOn gamma eta (Ioo a b) :=
      isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
        hzCommon
        ((smoothFrontierTransverseVectorField_contMDiff D).of_le (by norm_num))
        hgamma hetaCurve hmeet
    have hbaseFlow : (z.1 : X) = Ψ (w.1, Δ) := by
      have hzeroEq := hagree hzeroCommon
      rw [show gamma 0 = Ψ (z.1, 0) by rfl,
        hinitial z.1 hz.1] at hzeroEq
      simpa only [eta, Function.comp_apply, zero_add] using hzeroEq
    have hvalueEq :
        smoothBoundaryGlobalSignedCoordinate D (Ψ (w.1, Δ)) =
          smoothBoundaryGlobalSignedCoordinate D (Ψ (w.1, 0)) := by
      rw [← hbaseFlow, hinitial w.1 hw.1,
        smoothBoundaryGlobalSignedCoordinate_eq_zero_of_mem_frontier D z.1.2,
        smoothBoundaryGlobalSignedCoordinate_eq_zero_of_mem_frontier D w.1.2]
    have hΔzero : Δ = 0 :=
      (hmono w.1 hw.1).injOn hΔ
        (show (0 : ℝ) ∈ Ioo (-δ) δ by constructor <;> linarith)
        hvalueEq
    have htime : z.2 = w.2 := by
      dsimp only [Δ] at hΔzero
      linarith
    have hbase : z.1 = w.1 := by
      apply Subtype.ext
      change (z.1 : X) = (w.1 : X)
      rw [hbaseFlow, hΔzero, hinitial w.1 hw.1]
    exact Prod.ext hbase htime
  letI := smoothBoundaryFrontierChartedSpace D
  have hcontinuous : Continuous
      ((connectedComponent p ×ˢ Ioo (-ρ) ρ).restrict Ψ) := by
    rw [continuous_iff_continuousAt]
    intro z
    have hΨcont : ContinuousAt Ψ z :=
      (hsmoothρ z.1.1 z.2.1 z.1.2 z.2.2).continuousAt
    simpa only [Set.restrict_eq, Function.comp_def] using
      hΨcont.comp continuousAt_subtype_val
  have hopenEmbedding : Topology.IsOpenEmbedding
      ((connectedComponent p ×ˢ Ioo (-ρ) ρ).restrict Ψ) :=
    Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
      hcontinuous hinjective.injective hopenρ
  exact ⟨ρ, hρ, Ψ, hinitial, hcurveρ, hsmoothρ, hopenρ, hinjective,
    hcoordinateNeighborhoodρ, hsideρ, hexteriorSideρ, hopenEmbedding⟩

/-- The product of a frontier component and a symmetric time interval,
packaged as an open submanifold of the frontier product. -/
noncomputable def smoothFrontierComponentCollarOpen
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) (ρ : ℝ) :
    TopologicalSpace.Opens (frontier D.carrier × ℝ) := by
  letI := smoothBoundaryFrontierChartedSpace D
  letI : LocallyConnectedSpace (frontier D.carrier) :=
    ChartedSpace.locallyConnectedSpace ℝ (frontier D.carrier)
  exact ⟨connectedComponent p ×ˢ Ioo (-ρ) ρ,
    isOpen_connectedComponent.prod isOpen_Ioo⟩

/--
%%handwave
name:
  Smooth product collar of a frontier component
statement:
  Every connected frontier component \(C\) admits \(\rho>0\) and a smooth
  diffeomorphism onto an open subset of the surface,
  \[
    E:C\times(-\rho,\rho)\longrightarrow E(C\times(-\rho,\rho)),
  \]
  with \(E(q,0)=q\), \(E(q,t)\in D\iff t<0\), and
  \(E(q,t)\notin\overline D\iff t>0\).  The inverse is smooth on the collar
  image.
proof:
  Restrict the injective open transverse flow to a time interval common to a
  finite patch cover.  It is an open embedding, hence gives the stated
  homeomorphism.  On each patch its inverse is the already constructed smooth
  local inverse; uniqueness makes these local inverses agree, proving global
  smoothness on the image.
-/
theorem exists_smoothFrontierComponentCollar
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∃ Ψ : frontier D.carrier × ℝ → X,
        ∃ E : OpenPartialHomeomorph
          (connectedComponent p ×ˢ Ioo (-ρ) ρ) X,
          E.source = univ ∧
          (E : (connectedComponent p ×ˢ Ioo (-ρ) ρ) → X) =
            (connectedComponent p ×ˢ Ioo (-ρ) ρ).restrict Ψ ∧
          (∀ q : frontier D.carrier, q ∈ connectedComponent p →
            Ψ (q, 0) = (q : X)) ∧
          (∀ q : frontier D.carrier, q ∈ connectedComponent p →
            ∀ t ∈ Ioo (-ρ) ρ,
              Ψ (q, t) ∈ smoothBoundaryGlobalCoordinateNeighborhood D) ∧
          (∀ q : frontier D.carrier, q ∈ connectedComponent p →
            ∀ t ∈ Ioo (-ρ) ρ,
              Ψ (q, t) ∈ D.carrier ↔ t < 0) ∧
          (∀ q : frontier D.carrier, q ∈ connectedComponent p →
            ∀ t ∈ Ioo (-ρ) ρ,
              Ψ (q, t) ∉ closure D.carrier ↔ 0 < t) ∧
          (letI := smoothBoundaryFrontierChartedSpace D
           ContMDiff
            ((modelWithCornersSelf ℝ ℝ).prod
              (modelWithCornersSelf ℝ ℝ)) SurfaceRealModel ∞
            (fun z : smoothFrontierComponentCollarOpen D p ρ => E z)) ∧
          (letI := smoothBoundaryFrontierChartedSpace D
           ContMDiffOn SurfaceRealModel
            ((modelWithCornersSelf ℝ ℝ).prod
              (modelWithCornersSelf ℝ ℝ)) ∞
            (fun y : X =>
              ((E.symm y : connectedComponent p ×ˢ Ioo (-ρ) ρ) :
                frontier D.carrier × ℝ)) E.target) := by
  classical
  rcases exists_injective_smoothFrontierComponentFlow D p with
    ⟨ρ₀, hρ₀, Ψ, hinitial, hcurve, hsmooth, hopen, hinjective,
      hcoordinateNeighborhood, hside, hexteriorSide, hopenEmbedding⟩
  rcases exists_finite_smoothFrontierFlowPatch_cover D p with
    ⟨patch, centers, hcover, ε, hε, hεle⟩
  let ρ : ℝ := min ρ₀ ε / 2
  have hρ : 0 < ρ := half_pos (lt_min hρ₀ hε)
  have hρρ₀ : ρ < ρ₀ :=
    (half_lt_self (lt_min hρ₀ hε)).trans_le (min_le_left ρ₀ ε)
  have hρε : ρ < ε :=
    (half_lt_self (lt_min hρ₀ hε)).trans_le (min_le_right ρ₀ ε)
  have hagree : ∀ i ∈ centers, ∀ q ∈ connectedComponent p,
      q ∈ (patch i).carrier →
      EqOn (fun t : ℝ => Ψ (q, t))
        (fun t : ℝ => (patch i).flow (q, t)) (Ioo (-ρ) ρ) := by
    intro i hi q hq hqPatch
    have hcommon := smoothFrontierTransverseIntegralCurves_eqOn_commonInterval
      D hρ₀ (patch i).timeRadius_pos (hcurve q hq)
        ((patch i).integralCurve q hqPatch)
        (by rw [hinitial q hq, (patch i).initial q hqPatch])
    intro t ht
    apply hcommon
    have hρPatch : ρ < (patch i).timeRadius :=
      hρε.trans_le (hεle i hi)
    have hρmin : ρ < min ρ₀ (patch i).timeRadius :=
      lt_min hρρ₀ hρPatch
    exact ⟨by linarith [ht.1, hρmin], by linarith [ht.2, hρmin]⟩
  letI := smoothBoundaryFrontierChartedSpace D
  letI : IsManifold (modelWithCornersSelf ℝ ℝ) ∞
      (frontier D.carrier) := smoothBoundaryDomain_frontier_isSmoothOneManifold D
  letI : LocallyConnectedSpace (frontier D.carrier) :=
    ChartedSpace.locallyConnectedSpace ℝ (frontier D.carrier)
  let S : Set (frontier D.carrier × ℝ) :=
    connectedComponent p ×ˢ Ioo (-ρ) ρ
  have hSopen : IsOpen S := isOpen_connectedComponent.prod isOpen_Ioo
  have hSsub : S ⊆ connectedComponent p ×ˢ Ioo (-ρ₀) ρ₀ := by
    intro z hz
    exact ⟨hz.1, Ioo_subset_Ioo (neg_le_neg hρρ₀.le) hρρ₀.le hz.2⟩
  have hopenρ : IsOpenMap (S.restrict Ψ) :=
    isOpenMap_restrict_mono hopen hSopen hSsub
  have hinjectiveρ : InjOn Ψ S := hinjective.mono hSsub
  have hsmoothρ : ∀ q ∈ connectedComponent p, ∀ t ∈ Ioo (-ρ) ρ,
      ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod
          (modelWithCornersSelf ℝ ℝ)) SurfaceRealModel ∞ Ψ (q, t) := by
    intro q hq t ht
    exact hsmooth q hq t
      (Ioo_subset_Ioo (neg_le_neg hρρ₀.le) hρρ₀.le ht)
  have hcontinuousρ : Continuous (S.restrict Ψ) := by
    rw [continuous_iff_continuousAt]
    intro z
    have hΨcont : ContinuousAt Ψ z :=
      (hsmoothρ z.1.1 z.2.1 z.1.2 z.2.2).continuousAt
    simpa only [Set.restrict_eq, Function.comp_def] using
      hΨcont.comp continuousAt_subtype_val
  have hopenEmbeddingρ : Topology.IsOpenEmbedding (S.restrict Ψ) :=
    Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
      hcontinuousρ hinjectiveρ.injective hopenρ
  have hpS : (p, (0 : ℝ)) ∈ S :=
    ⟨mem_connectedComponent, by constructor <;> linarith⟩
  letI : Nonempty S := ⟨⟨(p, 0), hpS⟩⟩
  let E : OpenPartialHomeomorph S X :=
    hopenEmbeddingρ.toOpenPartialHomeomorph (S.restrict Ψ)
  have hEsource : E.source = univ :=
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source _ _
  have hEcoe : (E : S → X) = S.restrict Ψ :=
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_apply _ _
  have hEinverseSmooth : ContMDiffOn SurfaceRealModel
      ((modelWithCornersSelf ℝ ℝ).prod
        (modelWithCornersSelf ℝ ℝ)) ∞
      (fun y : X => ((E.symm y : S) : frontier D.carrier × ℝ))
      E.target := by
    intro y hy
    let z : S := E.symm y
    have hzSource : z ∈ E.source := E.symm_mapsTo hy
    have hEzy : E z = y := E.right_inv hy
    have hqcover := hcover z.2.1
    rcases mem_iUnion.mp hqcover with ⟨i, hqi⟩
    rcases mem_iUnion.mp hqi with ⟨hi, hqPatch⟩
    have hρPatch : ρ < (patch i).timeRadius :=
      hρε.trans_le (hεle i hi)
    have hzPatch : (z : frontier D.carrier × ℝ) ∈
        (patch i).carrier ×ˢ
          Ioo (-(patch i).timeRadius) (patch i).timeRadius :=
      ⟨hqPatch, Ioo_subset_Ioo (neg_le_neg hρPatch.le) hρPatch.le z.2.2⟩
    have hflowz : Ψ z = (patch i).flow z :=
      hagree i hi z.1.1 z.2.1 hqPatch z.2.2
    have hΨzy : Ψ z = y := by
      rw [← hEzy, hEcoe]
      rfl
    have hlocalSmooth : ContMDiffAt SurfaceRealModel
        ((modelWithCornersSelf ℝ ℝ).prod
          (modelWithCornersSelf ℝ ℝ)) ∞ (patch i).inverse y := by
      rw [← hΨzy, hflowz]
      exact (patch i).inverse_smooth z hzPatch
    let T : Set (frontier D.carrier × ℝ) :=
      (connectedComponent p ∩ (patch i).carrier) ×ˢ Ioo (-ρ) ρ
    have hTopen : IsOpen T :=
      (isOpen_connectedComponent.inter (patch i).isOpen_carrier).prod isOpen_Ioo
    have hTsubPatch : T ⊆
        (patch i).carrier ×ˢ
          Ioo (-(patch i).timeRadius) (patch i).timeRadius := by
      intro w hw
      exact ⟨hw.1.2, Ioo_subset_Ioo
        (neg_le_neg hρPatch.le) hρPatch.le hw.2⟩
    have hpatchOpenT : IsOpenMap (T.restrict (patch i).flow) :=
      isOpenMap_restrict_mono (patch i).isOpenMap hTopen hTsubPatch
    let W : Set X := range (T.restrict (patch i).flow)
    have hWopen : IsOpen W := hpatchOpenT.isOpen_range
    let wz : T := ⟨z, ⟨⟨z.2.1, hqPatch⟩, z.2.2⟩⟩
    have hyW : y ∈ W := by
      refine ⟨wz, ?_⟩
      change (patch i).flow z = y
      rw [← hΨzy, hflowz]
    have hevent : (fun y' : X => ((E.symm y' : S) :
        frontier D.carrier × ℝ)) =ᶠ[nhds y] (patch i).inverse := by
      filter_upwards [hWopen.mem_nhds hyW] with y' hy'
      rcases hy' with ⟨w, rfl⟩
      let wS : S := ⟨w, ⟨w.2.1.1, w.2.2⟩⟩
      have hfloww : Ψ w = (patch i).flow w :=
        hagree i hi w.1.1 w.2.1.1 w.2.1.2 w.2.2
      have hEw : E wS = (patch i).flow w := by
        rw [hEcoe]
        exact hfloww
      have hEinv : E.symm ((patch i).flow w) = wS := by
        rw [← hEw]
        exact E.left_inv (by rw [hEsource]; exact mem_univ _)
      change ((E.symm ((patch i).flow (w : frontier D.carrier × ℝ)) : S) :
          frontier D.carrier × ℝ) =
        (patch i).inverse ((patch i).flow (w : frontier D.carrier × ℝ))
      rw [hEinv]
      exact ((patch i).inverse_left (hTsubPatch w.2)).symm
    exact (hlocalSmooth.congr_of_eventuallyEq hevent).contMDiffWithinAt
  have hEforwardSmooth : ContMDiff
      ((modelWithCornersSelf ℝ ℝ).prod
        (modelWithCornersSelf ℝ ℝ)) SurfaceRealModel ∞
      (fun z : smoothFrontierComponentCollarOpen D p ρ => E z) := by
    intro z
    have hPsi : ContMDiffAt
        ((modelWithCornersSelf ℝ ℝ).prod
          (modelWithCornersSelf ℝ ℝ)) SurfaceRealModel ∞
        (fun w : smoothFrontierComponentCollarOpen D p ρ => Ψ w) z := by
      rw [contMDiffAt_subtype_iff]
      exact hsmoothρ z.1.1 z.2.1 z.1.2 z.2.2
    apply hPsi.congr_of_eventuallyEq
    filter_upwards [] with w
    change E (⟨w, w.2⟩ : S) = Ψ w
    rw [hEcoe]
    rfl
  have hcoordinateNeighborhoodρ :
      ∀ q : frontier D.carrier, q ∈ connectedComponent p →
        ∀ t ∈ Ioo (-ρ) ρ,
          Ψ (q, t) ∈ smoothBoundaryGlobalCoordinateNeighborhood D := by
    intro q hq t ht
    exact hcoordinateNeighborhood q hq t
      (Ioo_subset_Ioo (neg_le_neg hρρ₀.le) hρρ₀.le ht)
  have hsideρ :
      ∀ q : frontier D.carrier, q ∈ connectedComponent p →
        ∀ t ∈ Ioo (-ρ) ρ,
          Ψ (q, t) ∈ D.carrier ↔ t < 0 := by
    intro q hq t ht
    exact hside q hq t
      (Ioo_subset_Ioo (neg_le_neg hρρ₀.le) hρρ₀.le ht)
  have hexteriorSideρ :
      ∀ q : frontier D.carrier, q ∈ connectedComponent p →
        ∀ t ∈ Ioo (-ρ) ρ,
          Ψ (q, t) ∉ closure D.carrier ↔ 0 < t := by
    intro q hq t ht
    exact hexteriorSide q hq t
      (Ioo_subset_Ioo (neg_le_neg hρρ₀.le) hρρ₀.le ht)
  exact ⟨ρ, hρ, Ψ, E, hEsource, hEcoe, hinitial,
    hcoordinateNeighborhoodρ, hsideρ, hexteriorSideρ,
    hEforwardSmooth, hEinverseSmooth⟩

end
end JJMath.Uniformization
