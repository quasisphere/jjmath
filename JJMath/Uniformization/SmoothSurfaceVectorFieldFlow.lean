import JJMath.Uniformization.SmoothFrontierFlow
import Mathlib.Geometry.Manifold.IntegralCurve.UniformTime

/-!
# Coordinate flows of smooth vector fields on a surface

This file extracts the coordinate-flow construction from the frontier collar
argument.  It applies to an arbitrary smooth vector field on a real surface
modelled on the complex plane.
-/

open Bundle Filter Function Set
open JJMath.Manifold
open scoped Manifold Topology ContDiff

namespace JJMath.Uniformization

noncomputable section

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
variable [IsManifold SurfaceRealModel ∞ X]

/-- A surface vector field written in the fixed tangent trivialization and
base chart centered at a point. -/
noncomputable def surfaceCoordinateVectorField
    (V : (x : X) → TangentSpace SurfaceRealModel x)
    (x : X) (z : ℂ) : ℂ :=
  let y := (extChartAt SurfaceRealModel x).symm z
  ((trivializationAt ℂ (TangentSpace SurfaceRealModel) x)
    (⟨y, V y⟩ : TangentBundle SurfaceRealModel X)).2

/--
%%handwave
name:
  A surface vector field in coordinates at the chart center
statement:
  Let \(V\) be a surface vector field and let \(v_x\) be its expression in
  the chart centered at \(x\).  Then
  \[
    v_x(\phi_x(x))=V_x,
  \]
  under the tangent-space identification supplied by that chart.
proof:
  Expanding the tangent trivialization applies the chart derivative to
  \(V_x\).  At the centered point, the chart and inverse-chart derivatives
  cancel.
-/
theorem surfaceCoordinateVectorField_apply_center
    (V : (x : X) → TangentSpace SurfaceRealModel x) (x : X) :
    surfaceCoordinateVectorField V x
        (extChartAt SurfaceRealModel x x) = V x := by
  simp [surfaceCoordinateVectorField,
    TangentBundle.trivializationAt_apply]
  rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
  have hround := fderivWithin_extChartAt_comp_extChartAt_symm_range
    (I := SurfaceRealModel) (x := x)
  have happ := congrArg (fun L : ℂ →L[ℝ] ℂ => L (V x)) hround
  simpa [SurfaceRealModel] using happ

/--
%%handwave
name:
  Coordinate-change formula for a surface vector field
statement:
  Fix \(x\in X\), write \(y=\phi_x^{-1}(z)\), and express \(V_y\) in the
  chart centered at \(x\).  Then
  \[
    v_x(z)=d(\phi_x\circ\phi_y^{-1})_{\phi_y(y)}(V_y).
  \]
proof:
  This is the tangent-coordinate-change formula encoded by the fixed
  tangent-bundle trivialization.
-/
theorem surfaceCoordinateVectorField_eq_tangentCoordChange
    (V : (x : X) → TangentSpace SurfaceRealModel x)
    (x : X) (z : ℂ) :
    surfaceCoordinateVectorField V x z =
      tangentCoordChange SurfaceRealModel
        ((extChartAt SurfaceRealModel x).symm z) x
        ((extChartAt SurfaceRealModel x).symm z)
        (V ((extChartAt SurfaceRealModel x).symm z)) := by
  rw [surfaceCoordinateVectorField]
  simp only [TangentBundle.trivializationAt_apply]
  rfl

/--
%%handwave
name:
  Coordinate ODE solutions give manifold integral curves
statement:
  Suppose \(z(t)\) remains in the target of the chart \(\phi_x\) and
  satisfies
  \[
    z'(t)=v_x(z(t)).
  \]
  Then \(\gamma(t)=\phi_x^{-1}(z(t))\) satisfies
  \[
    \gamma'(t)=V_{\gamma(t)}
  \]
  as a manifold derivative.
proof:
  Apply the manifold chain rule to the inverse chart.  Its derivative changes
  tangent coordinates back to the moving point, cancelling the coordinate
  change used to define \(v_x\).
-/
theorem hasMFDerivAt_extChartAt_symm_of_hasDerivAt_surfaceCoordinateVectorField
    (V : (x : X) → TangentSpace SurfaceRealModel x)
    (x : X) (z : ℝ → ℂ) (t : ℝ)
    (hz : z t ∈ (extChartAt SurfaceRealModel x).target)
    (hode : HasDerivAt z (surfaceCoordinateVectorField V x (z t)) t) :
    HasMFDerivAt 𝓘(ℝ) SurfaceRealModel
      (fun s => (extChartAt SurfaceRealModel x).symm (z s)) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (V ((extChartAt SurfaceRealModel x).symm (z t)))) := by
  let y : X := (extChartAt SurfaceRealModel x).symm (z t)
  have hmd := mdifferentiableWithinAt_extChartAt_symm
    (I := SurfaceRealModel) hz
  have hsymm : HasMFDerivAt 𝓘(ℝ, ℂ) SurfaceRealModel
      (extChartAt SurfaceRealModel x).symm (z t)
      (mfderivWithin 𝓘(ℝ, ℂ) SurfaceRealModel
        (extChartAt SurfaceRealModel x).symm (range 𝓘(ℝ, ℂ)) (z t)) :=
    hmd.hasMFDerivWithinAt.hasMFDerivAt (by simp [SurfaceRealModel])
  have hzM : HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ, ℂ) z t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (surfaceCoordinateVectorField V x (z t))) :=
    hode.hasFDerivAt.hasMFDerivAt
  have hcomp := hsymm.comp t hzM
  apply hcomp.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro a
  change ℝ at a
  change mfderivWithin 𝓘(ℝ, ℂ) SurfaceRealModel
      (extChartAt SurfaceRealModel x).symm (range 𝓘(ℝ, ℂ)) (z t)
        (a • surfaceCoordinateVectorField V x (z t)) =
      a • V ((extChartAt SurfaceRealModel x).symm (z t))
  rw [mfderivWithin_extChartAt_symm_eq_tangentCoordChange_surface x (z t) hz]
  have hmap := (tangentCoordChange SurfaceRealModel x y y).map_smul a
    (surfaceCoordinateVectorField V x (z t))
  have hcoord : surfaceCoordinateVectorField V x (z t) =
      tangentCoordChange SurfaceRealModel y x y (V y) :=
    surfaceCoordinateVectorField_eq_tangentCoordChange V x (z t)
  have hbase : tangentCoordChange SurfaceRealModel x y y
      (surfaceCoordinateVectorField V x (z t)) = V y := by
    rw [hcoord]
    rw [tangentCoordChange_comp (h := ⟨⟨mem_extChartAt_source y,
      (extChartAt SurfaceRealModel x).map_target hz⟩,
      mem_extChartAt_source y⟩)]
    rw [tangentCoordChange_self (mem_extChartAt_source y)]
  calc
    _ = a • tangentCoordChange SurfaceRealModel x y y
        (surfaceCoordinateVectorField V x (z t)) := hmap
    _ = a • V y := congrArg (a • ·) hbase
    _ = _ := rfl

/--
%%handwave
name:
  Smoothness of a surface vector field in fixed coordinates
statement:
  If \(V\) is a smooth surface vector field, then for every \(x\in X\) its
  coordinate expression
  \[
    z\longmapsto v_x(z)
  \]
  is smooth on the target of the chart centered at \(x\).
proof:
  Compose the smooth tangent-bundle section \(y\mapsto(y,V_y)\) with the
  smooth inverse chart and the tangent trivialization, then project to the
  fiber coordinate.
-/
theorem surfaceCoordinateVectorField_contDiffOn
    (V : (x : X) → TangentSpace SurfaceRealModel x)
    (hV : ContMDiff SurfaceRealModel SurfaceRealModel.tangent ∞
      (fun x => (⟨x, V x⟩ : TangentBundle SurfaceRealModel X)))
    (x : X) :
    ContDiffOn ℝ ∞ (surfaceCoordinateVectorField V x)
      (extChartAt SurfaceRealModel x).target := by
  let e := trivializationAt ℂ (TangentSpace SurfaceRealModel) x
  let s : X → TangentBundle SurfaceRealModel X := fun y => ⟨y, V y⟩
  have hs : ContMDiffOn SurfaceRealModel SurfaceRealModel.tangent ∞ s e.baseSet :=
    hV.contMDiffOn
  have hmaps : MapsTo s e.baseSet e.source := by
    intro y hy
    change y ∈ e.baseSet at hy
    change s y ∈ e.source
    simpa [e, s] using hy
  have hcoeff : ContMDiffOn SurfaceRealModel 𝓘(ℝ, ℂ) ∞
      (fun y => (e (s y)).2) e.baseSet :=
    ((e.contMDiffOn_iff hmaps).mp hs).2
  have hsymm : ContMDiffOn 𝓘(ℝ, ℂ) SurfaceRealModel ∞
      (extChartAt SurfaceRealModel x).symm
      (extChartAt SurfaceRealModel x).target :=
    contMDiffOn_extChartAt_symm x
  have hmaps' : MapsTo (extChartAt SurfaceRealModel x).symm
      (extChartAt SurfaceRealModel x).target e.baseSet := by
    intro z hz
    have hzsrc : (extChartAt SurfaceRealModel x).symm z ∈
        (extChartAt SurfaceRealModel x).source :=
      (extChartAt SurfaceRealModel x).map_target hz
    simpa [e] using hzsrc
  have hcomp := hcoeff.comp hsymm hmaps'
  simpa [surfaceCoordinateVectorField, e, s, Function.comp_def] using
    hcomp.contDiffOn

/--
%%handwave
name:
  Global smooth extension of a local coordinate vector field
statement:
  For every \(x\in X\), there is a globally smooth
  \(f:\mathbb C\to\mathbb C\) which agrees near \(\phi_x(x)\) with the
  coordinate expression \(v_x\) of \(V\).
proof:
  The coordinate field is smooth on the open chart target containing
  \(\phi_x(x)\).  Extend this local smooth map to a global Euclidean map
  after shrinking around the center.
-/
theorem exists_contDiff_surfaceCoordinateVectorField_eventuallyEq
    (V : (x : X) → TangentSpace SurfaceRealModel x)
    (hV : ContMDiff SurfaceRealModel SurfaceRealModel.tangent ∞
      (fun x => (⟨x, V x⟩ : TangentBundle SurfaceRealModel X)))
    (x : X) :
    ∃ f : ℂ → ℂ, ContDiff ℝ ∞ f ∧
      f =ᶠ[nhds (extChartAt SurfaceRealModel x x)]
        surfaceCoordinateVectorField V x := by
  apply JJMath.Manifold.exists_contDiff_eventuallyEq_of_contDiffOn
    (U := (extChartAt SurfaceRealModel x).target)
  · exact isOpen_extChartAt_target x
  · exact mem_extChartAt_target x
  · exact surfaceCoordinateVectorField_contDiffOn V hV x

/--
%%handwave
name:
  Jointly smooth local coordinate flow of a surface vector field
statement:
  At each \(x\in X\), there are \(\varepsilon>0\), a globally smooth
  extension \(f:\mathbb C\to\mathbb C\) of \(v_x\), and local curves
  \(\psi_y\) for \(y\) near \(\phi_x(x)\) satisfying
  \[
    \psi_y(0)=y,\qquad
    \psi_y(t)=y+\int_0^t f(\psi_y(s))\,ds,
  \]
  with \((y,t)\mapsto\psi_y(t)\) smooth for \(|t|<\varepsilon\).
proof:
  Extend the coordinate vector field globally and apply the Euclidean
  Picard theorem with smooth joint dependence on initial value and time.
-/
theorem exists_surfaceCoordinateLocalFlow
    (V : (x : X) → TangentSpace SurfaceRealModel x)
    (hV : ContMDiff SurfaceRealModel SurfaceRealModel.tangent ∞
      (fun x => (⟨x, V x⟩ : TangentBundle SurfaceRealModel X)))
    (x : X) :
    ∃ f : ℂ → ℂ, ∃ hf : ContDiff ℝ ∞ f,
      f =ᶠ[nhds (extChartAt SurfaceRealModel x x)]
        surfaceCoordinateVectorField V x ∧
      ∃ ε : ℝ, ∃ hε : 0 < ε, ∃ ψ : ℂ → LocalCurve ℂ ε,
        ψ (extChartAt SurfaceRealModel x x)
            ⟨0, by constructor <;> linarith [hε]⟩ =
          extChartAt SurfaceRealModel x x ∧
        (∀ᶠ y in nhds (extChartAt SurfaceRealModel x x),
          ψ y ⟨0, by constructor <;> linarith [hε]⟩ = y) ∧
        (∀ᶠ y in nhds (extChartAt SurfaceRealModel x x),
          ψ y = ContinuousMap.const (Icc (-ε) ε) y +
            localCurveIntegral ε hε.le
              (superposition f hf.continuous (ψ y))) ∧
        ∀ᶠ y in nhds (extChartAt SurfaceRealModel x x),
          ∀ t₀ ∈ Ioo (-ε) ε,
            ContDiffAt ℝ ∞
              (fun p : ℂ × ℝ =>
                extendLocalCurve ε hε.le (ψ p.1) p.2)
              (y, t₀) := by
  rcases exists_contDiff_surfaceCoordinateVectorField_eventuallyEq V hV x with
    ⟨f, hf, hfeq⟩
  rcases exists_jointlySmooth_localFlow f hf
      (extChartAt SurfaceRealModel x x) with
    ⟨ε, hε, ψ, hψ0, hinitψ, hfixedψ, hsmoothψ⟩
  exact ⟨f, hf, hfeq, ε, hε, ψ, hψ0, hinitψ, hfixedψ, hsmoothψ⟩

/--
%%handwave
name:
  Integral curves of a smooth surface vector field are smooth
statement:
  If \(V\) is smooth and \(\gamma:\mathbb R\to X\) satisfies
  \(\gamma'(t)=V_{\gamma(t)}\) for every \(t\), then \(\gamma\) is smooth.
proof:
  At each time \(t_0\), construct the jointly smooth Picard flow in a chart
  centered at \(\gamma(t_0)\).  Its curve through the same initial point
  solves the same ODE, so local uniqueness identifies it with \(\gamma\)
  near \(t_0\).  Hence \(\gamma\) is smooth at every time.
-/
theorem IsMIntegralCurve.contMDiff_of_surfaceVectorField
    (V : (x : X) → TangentSpace SurfaceRealModel x)
    (hV : ContMDiff SurfaceRealModel SurfaceRealModel.tangent ∞
      (fun x => (⟨x, V x⟩ : TangentBundle SurfaceRealModel X)))
    {gamma : ℝ → X} (hgamma : IsMIntegralCurve gamma V) :
    ContMDiff (modelWithCornersSelf ℝ ℝ) SurfaceRealModel ∞ gamma := by
  intro t₀
  let x : X := gamma t₀
  rcases exists_surfaceCoordinateLocalFlow V hV x with
    ⟨f, hf, hfeq, ε, hε, ψ, hψ0, hinit, hfixed, hsmooth⟩
  let z₀ : ℂ := extChartAt SurfaceRealModel x x
  let F : ℂ × ℝ → ℂ := fun p =>
    extendLocalCurve ε hε.le (ψ p.1) p.2
  let eta₀ : ℝ → X := fun t =>
    (extChartAt SurfaceRealModel x).symm (F (z₀, t))
  let eta : ℝ → X := eta₀ ∘ fun t => t - t₀
  have hzero_mem : (0 : ℝ) ∈ Ioo (-ε) ε := by
    constructor <;> linarith
  have hfixed₀ :
      ψ z₀ = ContinuousMap.const (Icc (-ε) ε) z₀ +
        localCurveIntegral ε hε.le
          (superposition f hf.continuous (ψ z₀)) :=
    by simpa [z₀] using hfixed.self_of_nhds
  have hinit₀ :
      ψ z₀ ⟨0, by constructor <;> linarith⟩ = z₀ :=
    by simpa [z₀] using hinit.self_of_nhds
  have hsmooth₀ : ∀ t ∈ Ioo (-ε) ε, ContDiffAt ℝ ∞ F (z₀, t) := by
    intro t ht
    simpa [F] using (mem_of_mem_nhds hsmooth) t ht
  have hFzero : F (z₀, 0) = z₀ := by
    rw [show F (z₀, 0) = extendLocalCurve ε hε.le (ψ z₀) 0 by rfl]
    rw [extendLocalCurve_apply_of_mem ε hε.le (ψ z₀)
      (show (0 : ℝ) ∈ Icc (-ε) ε by constructor <;> linarith)]
    exact hinit₀
  have hFtend : Tendsto (fun t : ℝ => F (z₀, t))
      (nhds 0) (nhds z₀) := by
    have hcomp : ContDiffAt ℝ ∞ (fun t : ℝ => F (z₀, t)) 0 :=
      (hsmooth₀ 0 hzero_mem).comp 0
        (contDiffAt_const.prodMk contDiffAt_id)
    have hcont := hcomp.continuousAt
    rw [continuousAt_def, hFzero] at hcont
    exact hcont
  have htarget : ∀ᶠ t in nhds (0 : ℝ),
      F (z₀, t) ∈ (extChartAt SurfaceRealModel x).target :=
    hFtend.eventually
      ((isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x))
  have hfield : ∀ᶠ t in nhds (0 : ℝ),
      f (F (z₀, t)) = surfaceCoordinateVectorField V x (F (z₀, t)) :=
    hFtend.eventually hfeq
  have htime : ∀ᶠ t in nhds (0 : ℝ), t ∈ Ioo (-ε) ε :=
    Ioo_mem_nhds (by linarith) (by linarith)
  have heta₀_curve : IsMIntegralCurveAt eta₀ V 0 := by
    rw [IsMIntegralCurveAt]
    filter_upwards [htarget, hfield, htime] with t htTarget htField htTime
    have hode : HasDerivAt (fun s : ℝ => F (z₀, s))
        (surfaceCoordinateVectorField V x (F (z₀, t))) t := by
      rw [← htField]
      exact hasDerivAt_extendLocalCurve_of_picardFixedPoint
        ε hε.le f hf.continuous z₀ (ψ z₀) hfixed₀ htTime
    simpa [eta₀] using
      (hasMFDerivAt_extChartAt_symm_of_hasDerivAt_surfaceCoordinateVectorField
        V x (fun s => F (z₀, s)) t htTarget hode)
  have heta₀_zero : eta₀ 0 = x := by
    dsimp [eta₀]
    rw [hFzero]
    exact (extChartAt SurfaceRealModel x).left_inv
      (mem_extChartAt_source x)
  have heta_curve : IsMIntegralCurveAt eta V t₀ := by
    simpa [eta] using heta₀_curve.comp_add (-t₀)
  have heta_at : eta t₀ = gamma t₀ := by
    simp only [eta, Function.comp_apply, sub_self, heta₀_zero, x]
  have heta₀_smooth : ContMDiffAt (modelWithCornersSelf ℝ ℝ)
      SurfaceRealModel ∞ eta₀ 0 := by
    have hFcurve : ContDiffAt ℝ ∞ (fun t : ℝ => F (z₀, t)) 0 :=
      (hsmooth₀ 0 hzero_mem).comp 0
        (contDiffAt_const.prodMk contDiffAt_id)
    have hsymm : ContMDiffAt (modelWithCornersSelf ℝ ℂ)
        SurfaceRealModel ∞
        (extChartAt SurfaceRealModel x).symm z₀ :=
      (contMDiffOn_extChartAt_symm x z₀ (mem_extChartAt_target x)).contMDiffAt
        ((isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x))
    have hsymmF : ContMDiffAt (modelWithCornersSelf ℝ ℂ)
        SurfaceRealModel ∞
        (extChartAt SurfaceRealModel x).symm (F (z₀, 0)) := by
      simpa only [hFzero] using hsymm
    have hcomp := hsymmF.comp 0 hFcurve.contMDiffAt
    change ContMDiffAt (modelWithCornersSelf ℝ ℝ)
      SurfaceRealModel ∞ eta₀ 0
    exact hcomp
  have heta_smooth : ContMDiffAt (modelWithCornersSelf ℝ ℝ)
      SurfaceRealModel ∞ eta t₀ := by
    have hshift : ContMDiffAt (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ ℝ) ∞
        (fun t : ℝ => t - t₀) t₀ :=
      (contDiffAt_id.sub contDiffAt_const).contMDiffAt
    have hcomp := heta₀_smooth.comp_of_eq hshift (by simp)
    change ContMDiffAt (modelWithCornersSelf ℝ ℝ)
      SurfaceRealModel ∞ eta t₀
    exact hcomp
  have heq : gamma =ᶠ[nhds t₀] eta :=
    isMIntegralCurveAt_eventuallyEq_of_contMDiffAt_boundaryless
      ((hV.of_le (by norm_num)) (gamma t₀))
      (hgamma.isMIntegralCurveAt t₀) heta_curve heta_at.symm
  exact heta_smooth.congr_of_eventuallyEq heq

/--
%%handwave
name:
  Uniform coordinate-time existence near one initial point
statement:
  For every \(x\in X\), there are \(\delta>0\) and a neighborhood \(U\) of
  \(\phi_x(x)\) such that every \(y\in U\) is the initial coordinate of a
  manifold integral curve of \(V\) on \((-\delta,\delta)\).
proof:
  Joint continuity of the Picard flow lets one choose a product neighborhood
  of \((\phi_x(x),0)\) on which the curves remain in the chart, satisfy the
  coordinate ODE, and retain their initial values.  Choose a symmetric time
  interval contained in its time factor and apply the inverse chart.
-/
theorem exists_surfaceIntegralCurvesOn_uniform_coordinateNeighborhood
    (V : (x : X) → TangentSpace SurfaceRealModel x)
    (hV : ContMDiff SurfaceRealModel SurfaceRealModel.tangent ∞
      (fun x => (⟨x, V x⟩ : TangentBundle SurfaceRealModel X)))
    (x : X) :
    ∃ δ : ℝ, 0 < δ ∧
      ∃ U : Set ℂ, U ∈ nhds (extChartAt SurfaceRealModel x x) ∧
        ∀ y ∈ U,
          ∃ gamma : ℝ → X,
            gamma 0 = (extChartAt SurfaceRealModel x).symm y ∧
            IsMIntegralCurveOn gamma V (Ioo (-δ) δ) := by
  rcases exists_surfaceCoordinateLocalFlow V hV x with
    ⟨f, hf, hfeq, ε, hε, ψ, hψ0, hinit, hfixed, hsmooth⟩
  let z₀ : ℂ := extChartAt SurfaceRealModel x x
  let F : ℂ × ℝ → ℂ := fun p =>
    extendLocalCurve ε hε.le (ψ p.1) p.2
  have hF0 : F (z₀, 0) = z₀ := by
    rw [show F (z₀, 0) = extendLocalCurve ε hε.le (ψ z₀) 0 by rfl]
    rw [extendLocalCurve_apply_of_mem ε hε.le (ψ z₀)
      (show (0 : ℝ) ∈ Icc (-ε) ε by constructor <;> linarith [hε])]
    simpa only [z₀] using hψ0
  have hFsmooth : ContDiffAt ℝ ∞ F (z₀, 0) := by
    simpa only [F, z₀] using (mem_of_mem_nhds hsmooth) 0
      (show (0 : ℝ) ∈ Ioo (-ε) ε by constructor <;> linarith [hε])
  have hFtend : Tendsto F (nhds (z₀, 0)) (nhds z₀) := by
    have hcont := hFsmooth.continuousAt
    rw [continuousAt_def, hF0] at hcont
    exact hcont
  have hfirst : Tendsto (fun p : ℂ × ℝ => p.1)
      (nhds (z₀, 0)) (nhds z₀) := continuousAt_fst
  have hsecond : Tendsto (fun p : ℂ × ℝ => p.2)
      (nhds (z₀, 0)) (nhds (0 : ℝ)) := continuousAt_snd
  have hfixed' : ∀ᶠ p : ℂ × ℝ in nhds (z₀, 0),
      ψ p.1 = ContinuousMap.const (Icc (-ε) ε) p.1 +
        localCurveIntegral ε hε.le
          (superposition f hf.continuous (ψ p.1)) :=
    hfirst.eventually hfixed
  have hinit' : ∀ᶠ p : ℂ × ℝ in nhds (z₀, 0),
      ψ p.1 ⟨0, by constructor <;> linarith [hε]⟩ = p.1 :=
    hfirst.eventually hinit
  have htime : ∀ᶠ p : ℂ × ℝ in nhds (z₀, 0),
      p.2 ∈ Ioo (-ε) ε :=
    hsecond.eventually (Ioo_mem_nhds (by linarith [hε]) (by linarith [hε]))
  have htarget : ∀ᶠ p : ℂ × ℝ in nhds (z₀, 0),
      F p ∈ (extChartAt SurfaceRealModel x).target :=
    hFtend.eventually (isOpen_extChartAt_target x |>.mem_nhds
      (mem_extChartAt_target x))
  have hfield : ∀ᶠ p : ℂ × ℝ in nhds (z₀, 0),
      f (F p) = surfaceCoordinateVectorField V x (F p) :=
    hFtend.eventually hfeq
  let Good : Set (ℂ × ℝ) := {p |
    ψ p.1 = ContinuousMap.const (Icc (-ε) ε) p.1 +
        localCurveIntegral ε hε.le
          (superposition f hf.continuous (ψ p.1)) ∧
    ψ p.1 ⟨0, by constructor <;> linarith [hε]⟩ = p.1 ∧
    p.2 ∈ Ioo (-ε) ε ∧
    F p ∈ (extChartAt SurfaceRealModel x).target ∧
    f (F p) = surfaceCoordinateVectorField V x (F p)}
  have hGood : Good ∈ nhds (z₀, 0) := by
    filter_upwards [hfixed', hinit', htime, htarget, hfield]
      with p hpfix hpinit hpt hptarget hpfield
    exact ⟨hpfix, hpinit, hpt, hptarget, hpfield⟩
  have hGoodProd : Good ∈ nhds z₀ ×ˢ nhds (0 : ℝ) := by
    simpa only [nhds_prod_eq] using hGood
  rcases Filter.mem_prod_iff.mp hGoodProd with
    ⟨A, hA, B, hB, hAB⟩
  rcases Metric.mem_nhds_iff.mp hB with ⟨r, hr, hballB⟩
  let δ : ℝ := min ε r / 2
  have hmin : 0 < min ε r := lt_min hε hr
  have hδ : 0 < δ := half_pos hmin
  have hδε : δ < ε :=
    (half_lt_self hmin).trans_le (min_le_left ε r)
  have hδr : δ < r :=
    (half_lt_self hmin).trans_le (min_le_right ε r)
  refine ⟨δ, hδ, A, hA, ?_⟩
  intro y hy
  let gamma : ℝ → X := fun t =>
    (extChartAt SurfaceRealModel x).symm (F (y, t))
  have hgood : ∀ t ∈ Ioo (-δ) δ, (y, t) ∈ Good := by
    intro t ht
    apply hAB
    refine ⟨hy, hballB ?_⟩
    rw [Real.ball_zero_eq_Ioo]
    exact ⟨by linarith [ht.1, hδr], by linarith [ht.2, hδr]⟩
  have hzero : (0 : ℝ) ∈ Ioo (-δ) δ := by
    constructor <;> linarith [hδ]
  have hgamma0 : gamma 0 =
      (extChartAt SurfaceRealModel x).symm y := by
    have hg := hgood 0 hzero
    change (extChartAt SurfaceRealModel x).symm (F (y, 0)) =
      (extChartAt SurfaceRealModel x).symm y
    have hFinit : F (y, 0) = y := by
      rw [show F (y, 0) = extendLocalCurve ε hε.le (ψ y) 0 by rfl]
      rw [extendLocalCurve_apply_of_mem ε hε.le (ψ y)
        (show (0 : ℝ) ∈ Icc (-ε) ε by
          constructor <;> linarith [hε])]
      exact hg.2.1
    rw [hFinit]
  refine ⟨gamma, hgamma0, ?_⟩
  intro t ht
  have hg := hgood t ht
  have htε : t ∈ Ioo (-ε) ε :=
    Ioo_subset_Ioo (neg_le_neg hδε.le) hδε.le ht
  have hode : HasDerivAt (fun s : ℝ => F (y, s))
      (surfaceCoordinateVectorField V x (F (y, t))) t := by
    rw [← hg.2.2.2.2]
    exact hasDerivAt_extendLocalCurve_of_picardFixedPoint
      ε hε.le f hf.continuous y (ψ y) hg.1 htε
  exact
    (hasMFDerivAt_extChartAt_symm_of_hasDerivAt_surfaceCoordinateVectorField
      V x (fun s => F (y, s)) t hg.2.2.2.1 hode).hasMFDerivWithinAt

/--
%%handwave
name:
  Uniform local existence on a surface neighborhood
statement:
  For every \(x\in X\), there are \(\delta>0\) and a neighborhood \(W\) of
  \(x\) such that each \(y\in W\) admits an integral curve of \(V\) through
  \(y\) on \((-\delta,\delta)\).
proof:
  Pull the uniform coordinate neighborhood back through the centered chart.
  The chart inverse sends each coordinate initial value to the corresponding
  surface point.
-/
theorem exists_surfaceIntegralCurvesOn_uniform_neighborhood
    (V : (x : X) → TangentSpace SurfaceRealModel x)
    (hV : ContMDiff SurfaceRealModel SurfaceRealModel.tangent ∞
      (fun x => (⟨x, V x⟩ : TangentBundle SurfaceRealModel X)))
    (x : X) :
    ∃ δ : ℝ, 0 < δ ∧
      ∃ W : Set X, W ∈ nhds x ∧
        ∀ y ∈ W,
          ∃ gamma : ℝ → X,
            gamma 0 = y ∧ IsMIntegralCurveOn gamma V (Ioo (-δ) δ) := by
  rcases exists_surfaceIntegralCurvesOn_uniform_coordinateNeighborhood V hV x with
    ⟨δ, hδ, U, hU, hcurves⟩
  let e := extChartAt SurfaceRealModel x
  let W : Set X := e.source ∩ e ⁻¹' U
  have hW : W ∈ nhds x := by
    apply Filter.inter_mem
    · exact extChartAt_source_mem_nhds x
    · exact (continuousAt_extChartAt x).preimage_mem_nhds hU
  refine ⟨δ, hδ, W, hW, ?_⟩
  intro y hy
  rcases hcurves (e y) hy.2 with ⟨gamma, hgamma0, hgamma⟩
  refine ⟨gamma, ?_, hgamma⟩
  rw [hgamma0]
  exact e.left_inv hy.1

/--
%%handwave
name:
  Uniform integral-curve time on a compact set
statement:
  If \(K\subseteq X\) is nonempty and compact, then there is
  \(\varepsilon>0\) such that every \(x\in K\) admits an integral curve of
  \(V\) through \(x\) on \((-\varepsilon,\varepsilon)\).
proof:
  Cover \(K\) by finitely many neighborhoods carrying local existence times.
  The minimum of those finitely many positive times is positive and works
  for every point of the cover.
-/
theorem exists_surfaceIntegralCurvesOn_uniform_time_of_isCompact
    (V : (x : X) → TangentSpace SurfaceRealModel x)
    (hV : ContMDiff SurfaceRealModel SurfaceRealModel.tangent ∞
      (fun x => (⟨x, V x⟩ : TangentBundle SurfaceRealModel X)))
    {K : Set X} (hK : IsCompact K) (hKne : K.Nonempty) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ x ∈ K, ∃ gamma : ℝ → X,
        gamma 0 = x ∧ IsMIntegralCurveOn gamma V (Ioo (-ε) ε) := by
  classical
  choose δ hδ W hW hcurves using
    fun x : X => exists_surfaceIntegralCurvesOn_uniform_neighborhood V hV x
  rcases hK.elim_nhds_subcover W (fun x _hx => hW x) with
    ⟨centers, hcentersK, hcover⟩
  have hcenters_nonempty : centers.Nonempty := by
    rcases hKne with ⟨x, hx⟩
    have hxcover := hcover hx
    rcases Set.mem_iUnion.mp hxcover with ⟨q, hxq⟩
    rcases Set.mem_iUnion.mp hxq with ⟨hq, _hxW⟩
    exact ⟨q, hq⟩
  let radii : Finset ℝ := centers.image δ
  have hradii_nonempty : radii.Nonempty := hcenters_nonempty.image δ
  let ε : ℝ := radii.min' hradii_nonempty
  have hεpos : 0 < ε := by
    have hεmem : ε ∈ radii := Finset.min'_mem radii hradii_nonempty
    rcases Finset.mem_image.mp hεmem with ⟨q, hq, hqeq⟩
    rw [← hqeq]
    exact hδ q
  have hεle : ∀ q ∈ centers, ε ≤ δ q := by
    intro q hq
    exact Finset.min'_le radii _
      (Finset.mem_image.mpr ⟨q, hq, rfl⟩)
  refine ⟨ε, hεpos, ?_⟩
  intro x hx
  have hxcover := hcover hx
  rcases Set.mem_iUnion.mp hxcover with ⟨q, hxq⟩
  rcases Set.mem_iUnion.mp hxq with ⟨hq, hxW⟩
  rcases hcurves q x hxW with ⟨gamma, hgamma0, hgamma⟩
  refine ⟨gamma, hgamma0, hgamma.mono ?_⟩
  exact Ioo_subset_Ioo (neg_le_neg (hεle q hq)) (hεle q hq)

/--
%%handwave
name:
  Completeness from uniform local existence on an invariant set
statement:
  Let \(K\subseteq X\) be invariant under integral-curve segments of a
  continuously differentiable vector field \(V\).  Suppose some
  \(\varepsilon>0\) works as a local existence time for every initial point
  of \(K\).  Then every \(x\in K\) lies on an integral curve
  \(\gamma:\mathbb R\to X\) of \(V\) with \(\gamma(0)=x\).
proof:
  If the symmetric existence intervals through \(x\) had a finite supremum,
  invariance would keep points near both ends inside \(K\).  Attach
  \(\varepsilon\)-length local solutions there and use uniqueness to glue
  them to the original curve, extending beyond the supremum.  This
  contradiction makes the available radii unbounded and yields a global
  integral curve.
-/
theorem exists_isMIntegralCurve_of_isMIntegralCurveOn_invariant
    [T2Space X]
    (V : (x : X) → TangentSpace SurfaceRealModel x)
    (hV : ContMDiff SurfaceRealModel SurfaceRealModel.tangent 1
      (fun x => (⟨x, V x⟩ : TangentBundle SurfaceRealModel X)))
    {K : Set X}
    (hK_invariant : ∀ {gamma : ℝ → X} {a b t₀ : ℝ},
      IsMIntegralCurveOn gamma V (Ioo a b) →
      t₀ ∈ Ioo a b → gamma t₀ ∈ K →
      ∀ t ∈ Ioo a b, gamma t ∈ K)
    {ε : ℝ} (hε : 0 < ε)
    (hlocal : ∀ x ∈ K, ∃ gamma : ℝ → X,
      gamma 0 = x ∧ IsMIntegralCurveOn gamma V (Ioo (-ε) ε))
    {x : X} (hx : x ∈ K) :
    ∃ gamma : ℝ → X, gamma 0 = x ∧ IsMIntegralCurve gamma V := by
  let s := {a | ∃ gamma, gamma 0 = x ∧
    IsMIntegralCurveOn gamma V (Ioo (-a) a)}
  suffices hbdd : ¬ BddAbove s by
    rw [not_bddAbove_iff] at hbdd
    rw [exists_isMIntegralCurve_iff_exists_isMIntegralCurveOn_Ioo hV]
    intro a
    obtain ⟨y, ⟨gamma, hgamma0, hgamma⟩, hay⟩ := hbdd a
    exact ⟨gamma, hgamma0,
      hgamma.mono (Ioo_subset_Ioo (neg_le_neg hay.le) hay.le)⟩
  intro hbdd
  set asup := sSup s with hasup
  obtain ⟨a, ha, hlt⟩ := Real.add_neg_lt_sSup
    (⟨ε, hlocal x hx⟩ : Set.Nonempty s) (ε := -(ε / 2))
    (by rw [neg_lt, neg_zero]; exact half_pos hε)
  rw [mem_setOf] at ha
  rw [← hasup, ← sub_eq_add_neg] at hlt
  obtain ⟨gamma, hgamma0, hgamma⟩ := ha
  have hεle : ε ≤ asup := le_csSup hbdd (hlocal x hx)
  have hzero_a : (0 : ℝ) ∈ Ioo (-a) a := by
    constructor <;> linarith
  have hleft_time : -(asup - ε / 2) ∈ Ioo (-a) a := by
    constructor <;> linarith
  have hright_time : asup - ε / 2 ∈ Ioo (-a) a := by
    constructor <;> linarith
  have hleft_mem : gamma (-(asup - ε / 2)) ∈ K :=
    hK_invariant hgamma hzero_a (hgamma0.symm ▸ hx)
      _ hleft_time
  have hright_mem : gamma (asup - ε / 2) ∈ K :=
    hK_invariant hgamma hzero_a (hgamma0.symm ▸ hx)
      _ hright_time
  obtain ⟨gamma1_aux, hgamma1_aux0, hgamma1⟩ :=
    hlocal (gamma (-(asup - ε / 2))) hleft_mem
  rw [← isMIntegralCurveOn_comp_add (dt := asup - ε / 2)] at hgamma1
  set gamma1 := gamma1_aux ∘ (· + (asup - ε / 2)) with hgamma1_def
  have heq1 : gamma1 (-(asup - ε / 2)) =
      gamma (-(asup - ε / 2)) := by
    simp [hgamma1_def, hgamma1_aux0]
  obtain ⟨gamma2_aux, hgamma2_aux0, hgamma2⟩ :=
    hlocal (gamma (asup - ε / 2)) hright_mem
  rw [← isMIntegralCurveOn_comp_sub (dt := asup - ε / 2)] at hgamma2
  set gamma2 := gamma2_aux ∘ (· - (asup - ε / 2)) with hgamma2_def
  have heq2 : gamma2 (asup - ε / 2) =
      gamma (asup - ε / 2) := by
    simp [hgamma2_def, hgamma2_aux0]
  simp_rw [Set.mem_Ioo, ← sub_lt_iff_lt_add, ← lt_sub_iff_add_lt,
    ← Set.mem_Ioo] at hgamma1
  simp_rw [Set.mem_Ioo, lt_sub_iff_add_lt, sub_lt_iff_lt_add,
    ← Set.mem_Ioo] at hgamma2
  set gamma_ext : ℝ → X := piecewise (Ioo (-(asup + ε / 2)) a)
    (piecewise (Ioo (-a) a) gamma gamma1) gamma2 with hgamma_ext_def
  have hgamma_ext0 : gamma_ext 0 = x := by
    rw [hgamma_ext_def, piecewise, if_pos ⟨by linarith, by linarith⟩,
      piecewise, if_pos ⟨by linarith, by linarith⟩, hgamma0]
  suffices hext : IsMIntegralCurveOn gamma_ext V
      (Ioo (-(asup + ε / 2)) (asup + ε / 2)) from
    (not_lt.mpr (le_csSup hbdd ⟨gamma_ext, hgamma_ext0, hext⟩))
      (lt_add_of_pos_right asup (half_pos hε))
  apply (isMIntegralCurveOn_piecewise (t₀ := asup - ε / 2) hV _ hgamma2
      ⟨⟨by linarith, hlt⟩, ⟨by linarith, by linarith⟩⟩
      (by rw [piecewise, if_pos ⟨by linarith, hlt⟩, ← heq2])).mono
    (Ioo_subset_Ioo_union_Ioo le_rfl (by linarith) (by linarith))
  exact (isMIntegralCurveOn_piecewise (t₀ := -(asup - ε / 2)) hV
      hgamma hgamma1
      ⟨⟨neg_lt_neg hlt, by linarith⟩, ⟨by linarith, by linarith⟩⟩
      heq1.symm).mono
    (union_comm _ _ ▸
      Ioo_subset_Ioo_union_Ioo (by linarith) (by linarith) le_rfl)

end

end JJMath.Uniformization
