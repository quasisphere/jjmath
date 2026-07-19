import JJMath.RiemannianGeometry.SurfaceAnalysis
import JJMath.Uniformization.CompactSupportTransfer

/-!
# Top-degree de Rham cohomology on Riemann surfaces

This file develops the surface-specific integration and Stokes facts needed
for the compact step of uniformization.  It deliberately does not attempt the
corresponding theorem in arbitrary dimension.
-/

open Set MeasureTheory
open scoped Manifold Topology ContDiff ENNReal

noncomputable section

namespace JJMath.Uniformization

open JJMath.Manifold

/--
%%handwave
name:
  Pullback of a planar top form multiplies by the determinant
statement:
  For a real alternating two-form \(\omega\) on \(\mathbb C\) and a real-linear
  map \(L:\mathbb C\to\mathbb C\),
  \[
    (L^*\omega)(1,i)=\det(L)\,\omega(1,i).
  \]
proof:
  Apply the determinant formula for an alternating form evaluated on the
  image under \(L\) of the oriented basis \((1,i)\).
-/
theorem complexTopDegree_comp_apply_orientedBasis_det
    (omega : ℂ [⋀^Fin 2]→L[ℝ] ℝ) (L : ℂ →L[ℝ] ℂ) :
    omega.compContinuousLinearMap L complexPlanarOrientedBasis =
      L.det * omega complexPlanarOrientedBasis := by
  classical
  let e : Module.Basis (Fin 2) ℝ ℂ := Complex.basisOneI
  have h :=
    congrFun (congrArg DFunLike.coe
      (alternatingMap_eq_smulRight_basis_det e omega.toAlternatingMap))
      (fun i : Fin 2 ↦ L (e i))
  have hdet :
      e.det (fun i : Fin 2 ↦ L (e i)) =
        LinearMap.det (L : ℂ →ₗ[ℝ] ℂ) := by
    simpa [Function.comp_def, Module.Basis.det_self] using
      (Module.Basis.det_comp e (L : ℂ →ₗ[ℝ] ℂ)
        (fun i : Fin 2 ↦ e i))
  have hbasis : (fun i : Fin 2 ↦ Complex.basisOneI i) =
      complexPlanarOrientedBasis := by
    funext i
    fin_cases i <;> simp [Complex.coe_basisOneI, complexPlanarOrientedBasis]
  dsimp [e] at h hdet
  rw [hdet] at h
  change omega (fun i ↦ L (complexPlanarOrientedBasis i)) =
    L.det * omega complexPlanarOrientedBasis
  rw [← hbasis]
  exact h

/-- The oriented coordinate coefficient of a smooth surface two-form. -/
noncomputable def surfaceTwoFormCoefficientInChart
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (omega : SmoothForms (I := SurfaceRealModel) (M := X) ℝ 2)
    (e : OpenPartialHomeomorph X ℂ) (z : ℂ) : ℝ :=
  coordinateExpression (I := SurfaceRealModel) (F := ℝ) (n := 2)
    omega.toFun e z complexPlanarOrientedBasis

/-- The two scalar coordinate components of a smooth surface one-form. -/
noncomputable def surfaceOneFormComponentInChart
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (eta : SmoothForms (I := SurfaceRealModel) (M := X) ℝ 1)
    (e : OpenPartialHomeomorph X ℂ) (i : Fin 2) (z : ℂ) : ℝ :=
  coordinateExpression (I := SurfaceRealModel) (F := ℝ) (n := 1)
    eta.toFun e z (fun _ : Fin 1 ↦ complexCoordinateVector i)

/-- The intrinsic scalar coefficient of a two-form relative to the positively
oriented Riemannian area density. -/
noncomputable def surfaceTwoFormDensityCoefficient
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : SmoothRiemannianMetricOnSurface X)
    (omega : SmoothForms (I := SurfaceRealModel) (M := X) ℝ 2)
    (x : X) : ℝ :=
  omega.toFun x complexPlanarOrientedBasis /
    surfaceMetricVolumeDensityAt g x

/--
%%handwave
name:
  Coordinate coefficient of a surface two-form
statement:
  In a real surface chart \(e\), the oriented coordinate coefficient of a
  two-form \(\omega\) at \(z\) is
  \[
    \det(de^{-1}_z)\,\omega_{e^{-1}(z)}(1,i).
  \]
proof:
  The coordinate expression is the pullback of \(\omega\) by the tangent map
  of the inverse chart.  Evaluate that pullback on the oriented basis and use
  the determinant formula for planar top forms.
-/
theorem surfaceTwoFormCoefficientInChart_eq_det_mul
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X]
    (omega : SmoothForms (I := SurfaceRealModel) (M := X) ℝ 2)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    (z : ℂ) (hz : z ∈ e.target) :
    surfaceTwoFormCoefficientInChart omega e z =
      (surfaceChartTangentMap e z).det *
        omega.toFun (e.symm z) complexPlanarOrientedBasis := by
  have hcoord :
      coordinateExpression (I := SurfaceRealModel) (F := ℝ) (n := 2)
          omega.toFun e z =
        (omega.toFun (e.symm z)).compContinuousLinearMap
          (surfaceChartTangentMap e z) := by
    have hmd : MDifferentiableWithinAt SurfaceRealModel SurfaceRealModel
        e.symm e.target z :=
      mdifferentiableOn_atlas_symm (I := SurfaceRealModel) he z hz
    simp [coordinateExpression, surfaceChartTangentMap, mfderivWithin,
      writtenInExtChartAt, SurfaceRealModel, hmd]
    congr 2
  rw [surfaceTwoFormCoefficientInChart, hcoord]
  exact complexTopDegree_comp_apply_orientedBasis_det
    (omega.toFun (e.symm z)) (surfaceChartTangentMap e z)

/--
%%handwave
name:
  Intrinsic and coordinate densities of a surface two-form
statement:
  In an oriented complex chart, if \(f\) is the intrinsic coefficient of a
  two-form \(\omega\) relative to the metric area form and \(\rho\) is the
  coordinate area density, then
  \[
    f(e^{-1}(z))\rho(z)=\omega_e(z)(1,i).
  \]
proof:
  Both the two-form coefficient and metric density acquire the same positive
  Jacobian determinant under the chart; cancel the positive intrinsic metric
  density.
-/
theorem surfaceTwoFormDensityCoefficient_mul_volumeDensityInChart
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X]
    (g : SmoothRiemannianMetricOnSurface X)
    (omega : SmoothForms (I := SurfaceRealModel) (M := X) ℝ 2)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    (z : ℂ) (hz : z ∈ e.target) :
    surfaceTwoFormDensityCoefficient g omega (e.symm z) *
        surfaceMetricVolumeDensityInChart g e z =
      surfaceTwoFormCoefficientInChart omega e z := by
  have hdetpos := surfaceChartTangentMap_det_pos g e he z hz
  have hdensity :=
    surfaceMetricVolumeDensityInChart_eq_abs_det_mul_at g e he z hz
  have hbasepos := surfaceMetricVolumeDensityAt_pos g (e.symm z)
  rw [surfaceTwoFormDensityCoefficient,
    surfaceTwoFormCoefficientInChart_eq_det_mul omega e he z hz,
    hdensity, abs_of_pos hdetpos]
  field_simp [hbasepos.ne']

/-- The positively oriented area form determined by a smooth surface metric. -/
noncomputable def surfaceMetricVolumeForm
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (g : SmoothRiemannianMetricOnSurface X) :
    SmoothForms (I := SurfaceRealModel) (M := X) ℝ 2 where
  toFun := fun x ↦ surfaceMetricVolumeDensityAt g x • complexPlanarAreaForm
  isContMDiff := by
    letI : IsManifold SurfaceRealModel ∞ X := g.isManifold_real
    intro e he
    have hρ := (surfaceMetricVolumeDensityInChart_smooth_positive X g e he).1
    have hexttarget : (e.extend SurfaceRealModel).target = e.target := by
      ext z
      simp [SurfaceRealModel]
    rw [hexttarget]
    have hcoord : ∀ z ∈ e.target,
        coordinateExpression (I := SurfaceRealModel) (F := ℝ) (n := 2)
            (fun x ↦ surfaceMetricVolumeDensityAt g x • complexPlanarAreaForm) e z =
          surfaceMetricVolumeDensityInChart g e z • complexPlanarAreaForm := by
      intro z hz
      have hmd : MDifferentiableWithinAt SurfaceRealModel SurfaceRealModel
          e.symm e.target z :=
        mdifferentiableOn_atlas_symm (I := SurfaceRealModel) he z hz
      have hraw :
          coordinateExpression (I := SurfaceRealModel) (F := ℝ) (n := 2)
              (fun x ↦ surfaceMetricVolumeDensityAt g x • complexPlanarAreaForm) e z =
            (surfaceMetricVolumeDensityAt g (e.symm z) •
                complexPlanarAreaForm).compContinuousLinearMap
              (surfaceChartTangentMap e z) := by
        simp [coordinateExpression, surfaceChartTangentMap, mfderivWithin,
          writtenInExtChartAt, SurfaceRealModel, hmd]
        congr 2
      rw [hraw]
      apply complexTopDegreeContinuousAlternatingMap_ext_basis
      rw [complexTopDegree_comp_apply_orientedBasis_det]
      simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul]
      have harea : complexPlanarAreaForm complexPlanarOrientedBasis = 1 := by
        have hb : complexPlanarOrientedBasis =
            (fun i : Fin 2 ↦ Complex.basisOneI i) := by
          funext i
          fin_cases i <;>
            simp [complexPlanarOrientedBasis, Complex.coe_basisOneI]
        rw [hb]
        exact complexPlanarAreaForm_basis
      rw [harea, mul_one, mul_one]
      rw [surfaceMetricVolumeDensityInChart_eq_abs_det_mul_at g e he z hz,
        abs_of_pos (surfaceChartTangentMap_det_pos g e he z hz)]
    have hsmooth : ContDiffOn ℝ ∞
        (fun z ↦ surfaceMetricVolumeDensityInChart g e z •
          complexPlanarAreaForm) e.target :=
      hρ.smul contDiffOn_const
    exact hsmooth.congr (fun z hz ↦ hcoord z hz)

/--
%%handwave
name:
  The metric area form has coefficient one
statement:
  Relative to itself, the positively oriented metric area form has intrinsic
  density coefficient \(1\) at every point.
proof:
  Its value on the oriented basis is the metric volume density, since the
  standard planar area form evaluates to one; divide by that positive density.
-/
@[simp]
theorem surfaceTwoFormDensityCoefficient_surfaceMetricVolumeForm
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (g : SmoothRiemannianMetricOnSurface X) (x : X) :
    surfaceTwoFormDensityCoefficient g (surfaceMetricVolumeForm g) x = 1 := by
  rw [surfaceTwoFormDensityCoefficient]
  change (surfaceMetricVolumeDensityAt g x *
      complexPlanarAreaForm complexPlanarOrientedBasis) /
        surfaceMetricVolumeDensityAt g x = 1
  have harea : complexPlanarAreaForm complexPlanarOrientedBasis = 1 := by
    have hb : complexPlanarOrientedBasis =
        (fun i : Fin 2 ↦ Complex.basisOneI i) := by
      funext i
      fin_cases i <;>
        simp [complexPlanarOrientedBasis, Complex.coe_basisOneI]
    rw [hb]
    exact complexPlanarAreaForm_basis
  rw [harea, mul_one]
  exact div_self (surfaceMetricVolumeDensityAt_pos g x).ne'

/--
%%handwave
name:
  Coefficient of a scalar multiple of the metric area form
statement:
  If \(\chi\) is smooth, then the intrinsic density coefficient of
  \(\chi\,dA_g\) is \(\chi\) pointwise.
proof:
  Evaluate \(\chi\,dA_g\) on the oriented basis and divide by the positive
  metric volume density; the density cancels.
-/
@[simp]
theorem surfaceTwoFormDensityCoefficient_pointwiseSMul_volumeForm
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X]
    (g : SmoothRiemannianMetricOnSurface X)
    (χ : C^∞⟮SurfaceRealModel, X; ℝ⟯) (x : X) :
    surfaceTwoFormDensityCoefficient g
        (smoothFormsPointwiseSMul
          (I := SurfaceRealModel) (M := X) (A := ℝ)
          χ (surfaceMetricVolumeForm g)) x = χ x := by
  rw [surfaceTwoFormDensityCoefficient]
  change (χ x * (surfaceMetricVolumeDensityAt g x *
      complexPlanarAreaForm complexPlanarOrientedBasis)) /
        surfaceMetricVolumeDensityAt g x = χ x
  have harea : complexPlanarAreaForm complexPlanarOrientedBasis = 1 := by
    have hb : complexPlanarOrientedBasis =
        (fun i : Fin 2 ↦ Complex.basisOneI i) := by
      funext i
      fin_cases i <;>
        simp [complexPlanarOrientedBasis, Complex.coe_basisOneI]
    rw [hb]
    exact complexPlanarAreaForm_basis
  rw [harea, mul_one]
  field_simp [(surfaceMetricVolumeDensityAt_pos g x).ne']

/--
%%handwave
name:
  Every two-form on a surface is closed
statement:
  On a real two-dimensional smooth manifold, the exterior derivative of
  every smooth two-form is zero.
proof:
  The derivative is an alternating three-form, and any three tangent vectors
  in a two-dimensional real vector space are linearly dependent.
-/
theorem surfaceTwoForm_deRhamDifferential_eq_zero
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X]
    (omega : SmoothForms (I := SurfaceRealModel) (M := X) ℝ 2) :
    deRhamDifferential
      (I := SurfaceRealModel) (M := X) (A := ℝ) 2 omega = 0 := by
  apply DifferentialForm.ext
  intro x
  ext v
  change Fin 3 → ℂ at v
  have hdep : ¬ LinearIndependent ℝ v := by
    intro hv
    have hcard := hv.fintype_card_le_finrank
    norm_num [Complex.finrank_real_complex] at hcard
  exact ((deRhamDifferential
    (I := SurfaceRealModel) (M := X) (A := ℝ) 2 omega).toFun x).toAlternatingMap.map_linearDependent
      v hdep

/--
%%handwave
name:
  Smoothness of two-form coordinate coefficients
statement:
  The coefficient obtained by evaluating the coordinate expression of a
  smooth surface two-form on the oriented basis \((1,i)\) is smooth throughout
  the chart target.
proof:
  The coordinate expression of a smooth form is smooth, and evaluation on a
  fixed ordered basis is continuous linear.
-/
theorem surfaceTwoFormCoefficientInChart_contDiffOn
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X]
    (omega : SmoothForms (I := SurfaceRealModel) (M := X) ℝ 2)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X) :
    ContDiffOn ℝ ∞ (surfaceTwoFormCoefficientInChart omega e) e.target := by
  have hform : ContDiffOn ℝ ∞
      (coordinateExpression (I := SurfaceRealModel) (F := ℝ) (n := 2)
        omega.toFun e) e.target := by
    simpa using omega.isContMDiff e he
  exact ((ContinuousAlternatingMap.apply ℝ ℂ ℝ
    complexPlanarOrientedBasis).contDiff.contDiffOn.comp hform
      (fun _ _ ↦ Set.mem_univ _))

/--
%%handwave
name:
  Smoothness of one-form coordinate components
statement:
  In a surface chart, each scalar component of a smooth one-form with respect
  to the coordinate basis \((1,i)\) is smooth on the chart target.
proof:
  Compose the smooth coordinate expression of the one-form with evaluation
  on the corresponding fixed coordinate vector.
-/
theorem surfaceOneFormComponentInChart_contDiffOn
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X]
    (eta : SmoothForms (I := SurfaceRealModel) (M := X) ℝ 1)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    (i : Fin 2) :
    ContDiffOn ℝ ∞ (surfaceOneFormComponentInChart eta e i) e.target := by
  have hform : ContDiffOn ℝ ∞
      (coordinateExpression (I := SurfaceRealModel) (F := ℝ) (n := 1)
        eta.toFun e) e.target := by
    simpa using eta.isContMDiff e he
  exact ((ContinuousAlternatingMap.apply ℝ ℂ ℝ
    (fun _ : Fin 1 ↦ complexCoordinateVector i)).contDiff.contDiffOn.comp hform
      (fun _ _ ↦ Set.mem_univ _))

set_option maxHeartbeats 800000 in
/--
%%handwave
name:
  Coordinate formula for the exterior derivative on a surface
statement:
  If a one-form in oriented coordinates is \(P\,dx+Q\,dy\), then the oriented
  coefficient of its exterior derivative is
  \[
    \partial_x Q-\partial_y P.
  \]
proof:
  Apply the coordinate formula for the exterior derivative to the ordered
  basis \((1,i)\).  The two alternating summands are the \(x\)-derivative of
  the second component and minus the \(y\)-derivative of the first.
-/
theorem surfaceTwoFormCoefficientInChart_deRhamDifferential
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X]
    (eta : SmoothForms (I := SurfaceRealModel) (M := X) ℝ 1)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    (z : ℂ) (hz : z ∈ e.target) :
    surfaceTwoFormCoefficientInChart
        (deRhamDifferential (I := SurfaceRealModel) (M := X) (A := ℝ) 1 eta) e z =
      fderiv ℝ (surfaceOneFormComponentInChart eta e 1) z (1 : ℂ) -
        fderiv ℝ (surfaceOneFormComponentInChart eta e 0) z Complex.I := by
  have hzext : z ∈ (e.extend SurfaceRealModel).target := by
    simpa [SurfaceRealModel] using hz
  have hdiff : DifferentiableWithinAt ℝ
      (coordinateExpression (I := SurfaceRealModel) (F := ℝ) (n := 1)
        eta.toFun e) (e.extend SurfaceRealModel).target z :=
    ((eta.isContMDiff e he z hzext).differentiableWithinAt (by simp))
  have hcoord := coordinateExpression_exteriorDerivativePoint
    (I := SurfaceRealModel) (F := ℝ) (r := ∞) eta he hzext
  rw [surfaceTwoFormCoefficientInChart]
  change (coordinateExpression (I := SurfaceRealModel) (F := ℝ) (n := 2)
      (exteriorDerivative (I := SurfaceRealModel) (r := ∞) eta).toFun e z)
        complexPlanarOrientedBasis = _
  change (coordinateExpression (I := SurfaceRealModel) (F := ℝ) (n := 2)
      (exteriorDerivativePoint (I := SurfaceRealModel) (r := ∞) eta) e z)
        complexPlanarOrientedBasis = _
  rw [hcoord]
  rw [extDerivWithin_apply_basis_eq_sum_directional_coefficients
    (eta := coordinateExpression (I := SurfaceRealModel) (F := ℝ) (n := 1)
      eta.toFun e)
    (s := (e.extend SurfaceRealModel).target) (x := z)
    (base := complexPlanarOrientedBasis)
    (hxs := (uniqueDiffOn_extend_target (I := SurfaceRealModel) e) z hzext)
    (heta := hdiff)]
  have hexttarget : (e.extend SurfaceRealModel).target = e.target := by
    ext w
    simp [SurfaceRealModel]
  rw [hexttarget]
  rw [Fin.sum_univ_two]
  simp [complexPlanarOrientedBasis,
    fderivWithin_of_isOpen e.open_target hz]
  have htail : Fin.tail complexPlanarOrientedBasis =
      (fun _ : Fin 1 ↦ complexCoordinateVector 1) := by
    funext i
    fin_cases i
    rfl
  have hremove : Fin.removeNth 1 complexPlanarOrientedBasis =
      (fun _ : Fin 1 ↦ complexCoordinateVector 0) := by
    funext i
    fin_cases i
    rfl
  rw [htail, hremove]
  rfl

/--
%%handwave
name:
  Coordinate Stokes formula for a compactly supported one-form
statement:
  Let \(P\,dx+Q\,dy\) be a smooth one-form whose coordinate components vanish
  outside a compact subset of a surface chart.  Then
  \[
    \int \bigl(\partial_xQ-\partial_yP\bigr)\,dx\,dy=0
  \]
  over the chart target.
proof:
  Choose a smooth cutoff equal to one on the support and compactly supported
  inside the chart.  Euclidean integration by parts transfers the derivatives
  to the cutoff; its derivative vanishes on the original support, while the
  form vanishes off that support, so every remaining term is zero.
-/
theorem surfaceTwoFormCoefficientInChart_deRhamDifferential_integral_eq_zero
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X]
    (eta : SmoothForms (I := SurfaceRealModel) (M := X) ℝ 1)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    (K : Set ℂ) (hKcompact : IsCompact K) (hKtarget : K ⊆ e.target)
    (hzero : ∀ i : Fin 2, ∀ z ∈ e.target, z ∉ K →
      surfaceOneFormComponentInChart eta e i z = 0) :
    ∫ z in e.target,
        surfaceTwoFormCoefficientInChart
          (deRhamDifferential (I := SurfaceRealModel) (M := X) (A := ℝ) 1 eta) e z = 0 := by
  classical
  obtain ⟨δ, hδpos, hδtarget⟩ :=
    hKcompact.exists_cthickening_subset_open e.open_target hKtarget
  let ε : ℝ := δ / 2
  have hεpos : 0 < ε := by
    dsimp [ε]
    linarith
  have hεδ : ε < δ := by
    dsimp [ε]
    linarith
  have hclosedε : IsClosed (Metric.cthickening ε K) :=
    Metric.isClosed_cthickening
  have hεsubset : Metric.cthickening ε K ⊆ Metric.thickening δ K :=
    Metric.cthickening_subset_thickening' hδpos hεδ K
  obtain ⟨ψ, hψsmooth, _hψrange, hψsupport, hψone⟩ :=
    exists_contMDiff_support_eq_eq_one_iff
      (I := modelWithCornersSelf ℝ ℂ) (n := ⊤)
      Metric.isOpen_thickening hclosedε hεsubset
  have hψtsupport : tsupport ψ ⊆ Metric.cthickening δ K := by
    rw [tsupport, hψsupport]
    exact Metric.closure_thickening_subset_cthickening δ K
  have hψtarget : tsupport ψ ⊆ e.target :=
    hψtsupport.trans hδtarget
  have hψcompact : IsCompact (tsupport ψ) :=
    hKcompact.cthickening.of_isClosed_subset
      (isClosed_tsupport ψ) hψtsupport
  have hψcontDiff : ContDiff ℝ ∞ ψ := by
    simpa using hψsmooth.contDiff
  have hψderivZero : ∀ z ∈ K, fderiv ℝ ψ z = 0 := by
    intro z hzK
    have hzthick : z ∈ Metric.thickening ε K :=
      Metric.self_subset_thickening hεpos K hzK
    have hnhds : Metric.thickening ε K ∈ nhds z :=
      Metric.isOpen_thickening.mem_nhds hzthick
    have heventually : ψ =ᶠ[nhds z] fun _ : ℂ ↦ (1 : ℝ) := by
      filter_upwards [hnhds] with w hw
      exact (hψone w).1 ((Metric.thickening_subset_cthickening ε K) hw)
    rw [Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) heventually]
    simp
  have hcomponentDerivZero : ∀ i : Fin 2, ∀ z ∈ e.target, z ∉ K →
      fderiv ℝ (surfaceOneFormComponentInChart eta e i) z = 0 := by
    intro i z hzTarget hzK
    have hnhds : e.target \ K ∈ nhds z :=
      (e.open_target.sdiff hKcompact.isClosed).mem_nhds ⟨hzTarget, hzK⟩
    have heventually : surfaceOneFormComponentInChart eta e i =ᶠ[nhds z]
        fun _ : ℂ ↦ (0 : ℝ) := by
      filter_upwards [hnhds] with w hw
      exact hzero i w hw.1 hw.2
    rw [Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) heventually]
    simp
  let F : Fin 2 → ℂ → ℝ
    | 0 => surfaceOneFormComponentInChart eta e 1
    | 1 => fun z ↦ -surfaceOneFormComponentInChart eta e 0 z
  have hFdiff : ∀ i : Fin 2, ∀ z ∈ e.target,
      DifferentiableAt ℝ (F i) z := by
    intro i z hz
    fin_cases i
    · exact ((surfaceOneFormComponentInChart_contDiffOn eta e he 1).differentiableOn
        (by simp) z hz).differentiableAt (e.open_target.mem_nhds hz)
    · exact (((surfaceOneFormComponentInChart_contDiffOn eta e he 0).neg).differentiableOn
        (by simp) z hz).differentiableAt (e.open_target.mem_nhds hz)
  have hFcont : ∀ i : Fin 2, ContinuousOn (F i) e.target := by
    intro i
    fin_cases i
    · exact (surfaceOneFormComponentInChart_contDiffOn eta e he 1).continuousOn
    · exact (surfaceOneFormComponentInChart_contDiffOn eta e he 0).neg.continuousOn
  have hDFcont : ∀ i : Fin 2,
      ContinuousOn
        (fun z : ℂ ↦ fderiv ℝ (F i) z (complexCoordinateVector i))
        e.target := by
    intro i
    have hi : ContDiffOn ℝ ∞ (F i) e.target := by
      fin_cases i
      · exact surfaceOneFormComponentInChart_contDiffOn eta e he 1
      · exact (surfaceOneFormComponentInChart_contDiffOn eta e he 0).neg
    have hDi : ContDiffOn ℝ ∞ (fderiv ℝ (F i)) e.target :=
      hi.fderiv_of_isOpen e.open_target (by simp)
    exact (hDi.clm_apply
      (contDiffOn_const (c := complexCoordinateVector i))).continuousOn
  have hψdiff : ∀ z ∈ e.target, DifferentiableAt ℝ ψ z := by
    intro z _hz
    exact (hψcontDiff.differentiable (by simp)).differentiableAt
  have hψcont : ContinuousOn ψ e.target :=
    hψcontDiff.continuous.continuousOn
  have hDψcont : ∀ i : Fin 2,
      ContinuousOn
        (fun z : ℂ ↦ fderiv ℝ ψ z (complexCoordinateVector i))
        e.target := by
    intro i
    exact ((hψcontDiff.continuous_fderiv (by simp)).clm_apply
      continuous_const).continuousOn
  have hparts := euclidean_divergence_integral_by_parts_on_open
    e.target e.open_target F ψ hψtarget hψcompact
    hFdiff hψdiff hFcont hDFcont hψcont hDψcont
  have hright :
      ∫ z in e.target,
          ∑ i : Fin 2, F i z * fderiv ℝ ψ z (complexCoordinateVector i) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem e.open_target.measurableSet] with z hzTarget
    by_cases hzK : z ∈ K
    · rw [hψderivZero z hzK]
      simp
    · have hFzero : ∀ i : Fin 2, F i z = 0 := by
        intro i
        fin_cases i
        · exact hzero 1 z hzTarget hzK
        · simp [F, hzero 0 z hzTarget hzK]
      simp [hFzero]
  have hleft :
      ∫ z in e.target,
          (fderiv ℝ (F 0) z (1 : ℂ) +
            fderiv ℝ (F 1) z Complex.I) * ψ z = 0 := by
    rw [hparts, hright, neg_zero]
  rw [← hleft]
  apply setIntegral_congr_fun e.open_target.measurableSet
  intro z hz
  rw [surfaceTwoFormCoefficientInChart_deRhamDifferential eta e he z hz]
  have hdiv :
      fderiv ℝ (F 0) z (1 : ℂ) + fderiv ℝ (F 1) z Complex.I =
        fderiv ℝ (surfaceOneFormComponentInChart eta e 1) z (1 : ℂ) -
          fderiv ℝ (surfaceOneFormComponentInChart eta e 0) z Complex.I := by
    dsimp [F]
    change _ + fderiv ℝ (-(surfaceOneFormComponentInChart eta e 0)) z Complex.I = _
    rw [fderiv_neg]
    rfl
  change _ =
    (fderiv ℝ (F 0) z (1 : ℂ) + fderiv ℝ (F 1) z Complex.I) * ψ z
  rw [hdiv]
  by_cases hzK : z ∈ K
  · have hzclosed : z ∈ Metric.cthickening ε K :=
      Metric.self_subset_cthickening K hzK
    rw [(hψone z).mp hzclosed, mul_one]
  · have hQ : fderiv ℝ (surfaceOneFormComponentInChart eta e 1) z = 0 :=
      hcomponentDerivZero 1 z hz hzK
    have hP : fderiv ℝ (surfaceOneFormComponentInChart eta e 0) z = 0 :=
      hcomponentDerivZero 0 z hz hzK
    rw [hQ, hP]
    simp

/--
%%handwave
name:
  Smoothness of the intrinsic coefficient of a surface two-form
statement:
  The scalar function \(f\) determined by \(\omega=f\,dA_g\) is smooth on the
  surface whenever \(\omega\) and the Riemannian metric \(g\) are smooth.
proof:
  In a complex chart, \(f\) is the quotient of the smooth coordinate
  coefficient of \(\omega\) by the smooth positive metric area density.
-/
theorem surfaceTwoFormDensityCoefficient_isSmoothOnSurface
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (g : SmoothRiemannianMetricOnSurface X)
    (omega : SmoothForms (I := SurfaceRealModel) (M := X) ℝ 2) :
    IsSmoothOnSurface (Set.univ : Set X)
      (surfaceTwoFormDensityCoefficient g omega) := by
  letI : IsManifold SurfaceRealModel ∞ X := g.isManifold_real
  intro e he
  have hcoeff := surfaceTwoFormCoefficientInChart_contDiffOn omega e he
  have hdensity :=
    (surfaceMetricVolumeDensityInChart_smooth_positive X g e he).1
  have hdensity_ne : ∀ z ∈ e.target,
      surfaceMetricVolumeDensityInChart g e z ≠ 0 := by
    intro z hz
    exact ne_of_gt
      ((surfaceMetricVolumeDensityInChart_smooth_positive X g e he).2 z hz)
  have hdiv : ContDiffOn ℝ ∞
      (fun z ↦ surfaceTwoFormCoefficientInChart omega e z /
        surfaceMetricVolumeDensityInChart g e z) e.target :=
    hcoeff.div hdensity hdensity_ne
  simpa using hdiv.congr (fun z hz ↦ by
    apply (eq_div_iff (hdensity_ne z hz)).mpr
    exact surfaceTwoFormDensityCoefficient_mul_volumeDensityInChart
      g omega e he z hz)

/--
%%handwave
name:
  Continuity of the intrinsic coefficient of a surface two-form
statement:
  The scalar coefficient \(f\) in \(\omega=f\,dA_g\) is continuous on the
  surface.
proof:
  The coefficient is smooth in every surface chart, hence defines a globally
  smooth and therefore continuous function.
-/
theorem surfaceTwoFormDensityCoefficient_continuous
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (g : SmoothRiemannianMetricOnSurface X)
    (omega : SmoothForms (I := SurfaceRealModel) (M := X) ℝ 2) :
    Continuous (surfaceTwoFormDensityCoefficient g omega) := by
  letI : IsManifold SurfaceRealModel ∞ X := g.isManifold_real
  exact (isSmoothOnSurface_univ_contMDiff
    (surfaceTwoFormDensityCoefficient_isSmoothOnSurface g omega)).continuous

/-- Integral of a smooth surface two-form against its oriented Riemannian
area density. -/
noncomputable def surfaceTwoFormIntegral
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X]
    (g : SmoothRiemannianMetricOnSurface X)
    (measureGeometry : SurfaceMetricMeasureGeometry X g)
    (omega : SmoothForms (I := SurfaceRealModel) (M := X) ℝ 2) : ℝ :=
  ∫ x, surfaceTwoFormDensityCoefficient g omega x
    ∂measureGeometry.volume

/--
%%handwave
name:
  Positivity of smooth Riemannian area on open sets
statement:
  A smooth positive Riemannian area measure on a surface assigns positive
  measure to every nonempty open set.
proof:
  Intersect the open set with a coordinate chart.  In that chart the measure
  has a smooth strictly positive density with respect to planar Lebesgue
  measure, and every nonempty planar open set has positive Lebesgue measure.
-/
theorem surfaceMetricMeasureGeometry_isOpenPosMeasure
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [ComplexOneManifold X]
    (g : SmoothRiemannianMetricOnSurface X)
    (measureGeometry : SurfaceMetricMeasureGeometry X g) :
    Measure.IsOpenPosMeasure measureGeometry.volume := by
  letI : OpensMeasurableSpace X := measureGeometry.opensMeasurable
  constructor
  intro O hO hOne
  rcases hOne with ⟨x, hxO⟩
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ x
  have he : e ∈ atlas ℂ X := chart_mem_atlas ℂ x
  have hxSource : x ∈ e.source := mem_chart_source ℂ x
  let S : Set ℂ := e '' (O ∩ e.source)
  have hSopen : IsOpen S :=
    e.isOpen_image_of_subset_source (hO.inter e.open_source) inter_subset_right
  have hSne : S.Nonempty := ⟨e x, ⟨x, ⟨hxO, hxSource⟩, rfl⟩⟩
  have hStarget : S ⊆ e.target := by
    rintro z ⟨y, ⟨_hyO, hySource⟩, rfl⟩
    exact e.map_source hySource
  obtain ⟨ρ, hρsmooth, hρpos, hchart⟩ :=
    (measureGeometry.smoothPositive).chart_density e he
  intro hOzero
  have heAEM : AEMeasurable e
      (measureGeometry.volume.restrict e.source) :=
    e.continuousOn.aemeasurable e.open_source.measurableSet
  have hmapzero :
      Measure.map e (measureGeometry.volume.restrict e.source) S = 0 := by
    rw [Measure.map_apply_of_aemeasurable heAEM hSopen.measurableSet]
    rw [Measure.restrict_apply' e.open_source.measurableSet]
    apply measure_mono_null _ hOzero
    intro y hy
    have hySource : y ∈ e.source := hy.2
    have hyImage : e y ∈ S := hy.1
    rcases hyImage with ⟨w, ⟨hwO, hwSource⟩, hwz⟩
    have hyw : y = w := e.injOn hySource hwSource hwz.symm
    simpa [hyw] using hwO
  rw [hchart] at hmapzero
  have hρaem : AEMeasurable (fun z : ℂ ↦ ENNReal.ofReal (ρ z))
      (MeasureTheory.volume.restrict e.target) :=
    (ENNReal.continuous_ofReal.comp_continuousOn hρsmooth.continuousOn).aemeasurable
      e.open_target.measurableSet
  have hbasezero :=
    (withDensity_apply_eq_zero' hρaem).mp hmapzero
  have hsupportInter :
      {z : ℂ | ENNReal.ofReal (ρ z) ≠ 0} ∩ S = S := by
    ext z
    constructor
    · exact fun hz ↦ hz.2
    · intro hzS
      refine ⟨?_, hzS⟩
      exact (ENNReal.ofReal_pos.mpr (hρpos z (hStarget hzS))).ne'
  rw [hsupportInter] at hbasezero
  rw [Measure.restrict_apply hSopen.measurableSet] at hbasezero
  rw [inter_eq_left.mpr hStarget] at hbasezero
  exact hSopen.measure_ne_zero MeasureTheory.volume hSne hbasezero

/--
%%handwave
name:
  Integrability of smooth two-form coefficients on compact surfaces
statement:
  On a compact surface, the intrinsic coefficient \(f\) of any smooth
  two-form \(\omega=f\,dA_g\) is integrable with respect to the metric area
  measure.
proof:
  The coefficient is continuous, hence integrable on the compact whole
  surface for a measure finite on compact sets.
-/
theorem surfaceTwoFormDensityCoefficient_integrable
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [ComplexOneManifold X] [CompactSpace X]
    (g : SmoothRiemannianMetricOnSurface X)
    (measureGeometry : SurfaceMetricMeasureGeometry X g)
    (omega : SmoothForms (I := SurfaceRealModel) (M := X) ℝ 2) :
    Integrable (surfaceTwoFormDensityCoefficient g omega)
      measureGeometry.volume := by
  letI : OpensMeasurableSpace X := measureGeometry.opensMeasurable
  letI : IsFiniteMeasureOnCompacts measureGeometry.volume :=
    measureGeometry.isFiniteMeasureOnCompacts
  simpa [IntegrableOn] using
    (surfaceTwoFormDensityCoefficient_continuous g omega).continuousOn.integrableOn_compact
      (μ := measureGeometry.volume)
      (isCompact_univ : IsCompact (Set.univ : Set X))

/--
%%handwave
name:
  A positive closed two-form supported in a prescribed compact set
statement:
  Let \(S\subseteq C\subseteq X\), where \(S\) is nonempty and open and \(C\)
  is compact.  There exists a closed smooth two-form \(\omega\), supported in
  \(C\), such that \(\int_X\omega>0\).
proof:
  Choose a nonnegative smooth bump function \(\chi\), supported in \(S\), that
  equals one at a chosen point of \(S\).  Set \(\omega=\chi\,dA_g\).  Every
  two-form on a surface is closed, its integral is positive because the area
  measure is positive on open sets, and its support lies in \(C\).
-/
theorem exists_closedSurfaceTwoForm_integral_pos_supported_in_compact
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [RiemannSurface X] [CompactSpace X]
    [IsManifold SurfaceRealModel ∞ X] [SigmaCompactSpace X]
    (g : SmoothRiemannianMetricOnSurface X)
    (measureGeometry : SurfaceMetricMeasureGeometry X g)
    (S C : Set X) (hSopen : IsOpen S) (hCcompact : IsCompact C)
    (hSC : S ⊆ C) (y : X) (hy : y ∈ S) :
    ∃ omega : DeRhamClosedForms
        (I := SurfaceRealModel) (M := X) (A := ℝ) 2,
      0 < surfaceTwoFormIntegral g measureGeometry omega.1 ∧
      ∀ x : X, x ∉ C → omega.1.toFun x = 0 := by
  classical
  obtain ⟨χ, hχsmooth, hχrange, hχsupport, hχone⟩ :=
    exists_contMDiff_support_eq_eq_one_iff
      (I := SurfaceRealModel) (n := ⊤)
      hSopen isClosed_singleton (singleton_subset_iff.mpr hy)
  let χSmooth : C^∞⟮SurfaceRealModel, X; ℝ⟯ :=
    { val := χ
      property := hχsmooth }
  let omegaForm : SmoothForms
      (I := SurfaceRealModel) (M := X) ℝ 2 :=
    smoothFormsPointwiseSMul
      (I := SurfaceRealModel) (M := X) (A := ℝ)
      χSmooth (surfaceMetricVolumeForm g)
  let omega : DeRhamClosedForms
      (I := SurfaceRealModel) (M := X) (A := ℝ) 2 :=
    ⟨omegaForm, surfaceTwoForm_deRhamDifferential_eq_zero omegaForm⟩
  refine ⟨omega, ?_, ?_⟩
  · rw [surfaceTwoFormIntegral]
    have hcoeff : surfaceTwoFormDensityCoefficient g omega.1 = χ := by
      funext x
      exact surfaceTwoFormDensityCoefficient_pointwiseSMul_volumeForm
        g χSmooth x
    rw [hcoeff]
    letI : Measure.IsOpenPosMeasure measureGeometry.volume :=
      surfaceMetricMeasureGeometry_isOpenPosMeasure g measureGeometry
    apply integral_pos_of_integrable_nonneg_nonzero hχsmooth.continuous
    · simpa [hcoeff] using
        surfaceTwoFormDensityCoefficient_integrable g measureGeometry omega.1
    · intro x
      exact (hχrange ⟨x, rfl⟩).1
    · have hyone : χ y = 1 := (hχone y).mp (Set.mem_singleton y)
      rw [hyone]
      norm_num
  · intro x hxC
    apply smoothFormsPointwiseSMul_eq_zero_of_notMem_tsupport
      (I := SurfaceRealModel) (A := ℝ) χSmooth (surfaceMetricVolumeForm g)
    have htsupport : tsupport χ ⊆ C := by
      rw [tsupport, hχsupport]
      exact closure_minimal hSC hCcompact.isClosed
    exact fun hx ↦ hxC (htsupport hx)

/--
%%handwave
name:
  A positive closed two-form supported in a coordinate disk
statement:
  Given a point \(y\) in the open interior of a closed coordinate disk, there
  exists a closed smooth two-form supported in that closed disk and having
  positive total integral.
proof:
  Apply the compact-support construction to the expanded open disk of the
  same radius, which is contained in the closed coordinate disk and contains
  \(y\).
-/
theorem exists_closedSurfaceTwoForm_integral_pos_supported_in_closedCoordinateDisk
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [RiemannSurface X] [CompactSpace X]
    [IsManifold SurfaceRealModel ∞ X] [SigmaCompactSpace X]
    (g : SmoothRiemannianMetricOnSurface X)
    (measureGeometry : SurfaceMetricMeasureGeometry X g)
    (D : ClosedCoordinateDisk X) (y : X)
    (hy : y ∈ D.expandedOpenDisk D.closedRadius) :
    ∃ omega : DeRhamClosedForms
        (I := SurfaceRealModel) (M := X) (A := ℝ) 2,
      0 < surfaceTwoFormIntegral g measureGeometry omega.1 ∧
      ∀ x : X, x ∉ D.carrier → omega.1.toFun x = 0 := by
  apply exists_closedSurfaceTwoForm_integral_pos_supported_in_compact
    g measureGeometry
    (D.expandedOpenDisk D.closedRadius) D.carrier
    (D.expandedOpenDisk_isOpen D.closedRadius) D.compact (y := y)
  · intro x hx
    rw [ClosedCoordinateDisk.expandedOpenDisk] at hx
    rw [D.carrier_eq]
    exact ⟨hx.1, Metric.ball_subset_closedBall hx.2⟩
  · exact hy

/--
%%handwave
name:
  Additivity of intrinsic two-form coefficients
statement:
  If \(\omega=f\,dA_g\) and \(\eta=h\,dA_g\), then
  \(\omega+\eta=(f+h)dA_g\) pointwise.
proof:
  Evaluation on the oriented basis is additive, and division by the common
  metric area density distributes over addition.
-/
theorem surfaceTwoFormDensityCoefficient_add
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : SmoothRiemannianMetricOnSurface X)
    (omega eta : SmoothForms (I := SurfaceRealModel) (M := X) ℝ 2)
    (x : X) :
    surfaceTwoFormDensityCoefficient g (omega + eta) x =
      surfaceTwoFormDensityCoefficient g omega x +
        surfaceTwoFormDensityCoefficient g eta x := by
  simp only [surfaceTwoFormDensityCoefficient]
  change (omega.toFun x complexPlanarOrientedBasis +
      eta.toFun x complexPlanarOrientedBasis) /
        surfaceMetricVolumeDensityAt g x = _
  ring

/--
%%handwave
name:
  Additivity of surface integration
statement:
  On a compact surface,
  \[
    \int_X(\omega+\eta)=\int_X\omega+\int_X\eta
  \]
  for smooth two-forms \(\omega,\eta\).
proof:
  Their intrinsic coefficients add pointwise and are integrable; apply
  additivity of the Lebesgue integral.
-/
theorem surfaceTwoFormIntegral_add
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [ComplexOneManifold X] [CompactSpace X]
    (g : SmoothRiemannianMetricOnSurface X)
    (measureGeometry : SurfaceMetricMeasureGeometry X g)
    (omega eta : SmoothForms (I := SurfaceRealModel) (M := X) ℝ 2) :
    surfaceTwoFormIntegral g measureGeometry (omega + eta) =
      surfaceTwoFormIntegral g measureGeometry omega +
        surfaceTwoFormIntegral g measureGeometry eta := by
  rw [surfaceTwoFormIntegral, surfaceTwoFormIntegral, surfaceTwoFormIntegral]
  rw [integral_congr_ae (Filter.Eventually.of_forall
    (surfaceTwoFormDensityCoefficient_add g omega eta))]
  exact integral_add
    (surfaceTwoFormDensityCoefficient_integrable g measureGeometry omega)
    (surfaceTwoFormDensityCoefficient_integrable g measureGeometry eta)

/--
%%handwave
name:
  Integral of the zero surface form
statement:
  The zero two-form has total integral zero.
proof:
  Its intrinsic density coefficient is identically zero, whose integral is
  zero.
-/
@[simp]
theorem surfaceTwoFormIntegral_zero
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [ComplexOneManifold X]
    (g : SmoothRiemannianMetricOnSurface X)
    (measureGeometry : SurfaceMetricMeasureGeometry X g) :
    surfaceTwoFormIntegral g measureGeometry
      (0 : SmoothForms (I := SurfaceRealModel) (M := X) ℝ 2) = 0 := by
  rw [surfaceTwoFormIntegral]
  apply integral_eq_zero_of_ae
  exact Filter.Eventually.of_forall (fun x ↦ by
    change (0 : ℝ) / surfaceMetricVolumeDensityAt g x = 0
    simp)

/--
%%handwave
name:
  Surface integration of a finite sum
statement:
  On a compact surface, integration commutes with every finite sum of smooth
  two-forms:
  \[
    \int_X\sum_{i\in F}\omega_i=\sum_{i\in F}\int_X\omega_i.
  \]
proof:
  Induct on the finite set, using additivity of integration and the zero-form
  case.
-/
theorem surfaceTwoFormIntegral_finset_sum
    {X ι : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [ComplexOneManifold X] [CompactSpace X]
    (g : SmoothRiemannianMetricOnSurface X)
    (measureGeometry : SurfaceMetricMeasureGeometry X g)
    (omega : ι → SmoothForms (I := SurfaceRealModel) (M := X) ℝ 2)
    (s : Finset ι) :
    surfaceTwoFormIntegral g measureGeometry (∑ i ∈ s, omega i) =
      ∑ i ∈ s, surfaceTwoFormIntegral g measureGeometry (omega i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        surfaceTwoFormIntegral_add, ih]

/--
%%handwave
name:
  Exterior differentiation preserves compact support
statement:
  If a smooth differential form vanishes outside a compact set \(C\), then
  its exterior derivative also vanishes outside \(C\).
proof:
  At a point of the open complement of \(C\), the form agrees locally with
  the zero form.  Locality of exterior differentiation therefore makes its
  derivative zero there.
-/
theorem deRhamDifferential_toFun_eq_zero_of_not_mem_compact_ambient
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [T2Space X] [IsManifold SurfaceRealModel ∞ X]
    (C : Set X) (hCcompact : IsCompact C) {n : ℕ}
    (eta : SmoothForms (I := SurfaceRealModel) (M := X) ℝ n)
    (hzero : ∀ x : X, x ∉ C → eta.toFun x = 0)
    (x : X) (hx : x ∉ C) :
    (deRhamDifferential (I := SurfaceRealModel) (M := X) (A := ℝ) n eta).toFun x = 0 := by
  have hlocal : ∀ᶠ y in nhds x,
      eta.toFun y = (0 : SmoothForms
        (I := SurfaceRealModel) (M := X) ℝ n).toFun y := by
    filter_upwards [hCcompact.isClosed.isOpen_compl.mem_nhds hx] with y hy
    simp [hzero y hy]
  rw [deRhamDifferential_toFun_eq_of_eventuallyEq
    (I := SurfaceRealModel) eta 0 hlocal]
  have hd0 : deRhamDifferential (I := SurfaceRealModel) (M := X) (A := ℝ) n
      (0 : SmoothForms (I := SurfaceRealModel) (M := X) ℝ n) = 0 :=
    LinearMap.map_zero _
  simpa using congrArg (fun theta ↦ theta.toFun x) hd0

/--
%%handwave
name:
  Chart formula for a compactly supported surface integral
statement:
  If a smooth two-form \(\omega\) is supported in a compact subset of one
  surface chart \(e\), then
  \[
    \int_X\omega=\int_{e(X)}\omega_e(z)(1,i)\,dz.
  \]
proof:
  Restrict the global integral to the chart source, transport the metric area
  measure through the chart, and write it using its coordinate density.  The
  product of this density with the intrinsic coefficient of \(\omega\) is
  exactly the oriented coordinate coefficient.
-/
theorem surfaceTwoFormIntegral_eq_chartCoefficientIntegral_of_compactSupport
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [ComplexOneManifold X]
    (g : SmoothRiemannianMetricOnSurface X)
    (measureGeometry : SurfaceMetricMeasureGeometry X g)
    (omega : SmoothForms (I := SurfaceRealModel) (M := X) ℝ 2)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    (C : Set X) (_hCcompact : IsCompact C) (hCsource : C ⊆ e.source)
    (hzero : ∀ x : X, x ∉ C → omega.toFun x = 0) :
    surfaceTwoFormIntegral g measureGeometry omega =
      ∫ z in e.target, surfaceTwoFormCoefficientInChart omega e z := by
  letI : IsManifold SurfaceRealModel ∞ X := g.isManifold_real
  letI : OpensMeasurableSpace X := measureGeometry.opensMeasurable
  let φ : X → ℝ := surfaceTwoFormDensityCoefficient g omega
  let ψ : ℂ → ℝ := fun z ↦ φ (e.symm z)
  have hφzero : ∀ x : X, x ∉ e.source → φ x = 0 := by
    intro x hxSource
    have hxC : x ∉ C := fun hxC ↦ hxSource (hCsource hxC)
    change omega.toFun x complexPlanarOrientedBasis /
      surfaceMetricVolumeDensityAt g x = 0
    rw [hzero x hxC]
    change (0 : ℝ) / surfaceMetricVolumeDensityAt g x = 0
    exact zero_div _
  have hrestrict :
      surfaceTwoFormIntegral g measureGeometry omega =
        ∫ x in e.source, φ x ∂measureGeometry.volume := by
    rw [surfaceTwoFormIntegral]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero
      (μ := measureGeometry.volume) (s := e.source) (f := φ) hφzero).symm
  have hac : riemannianVolumeChartMeasure g e ≪
      MeasureTheory.volume.restrict e.target := by
    rw [riemannianVolumeChartMeasure]
    exact withDensity_absolutelyContinuous _ _
  have hψcont : ContinuousOn ψ e.target := by
    exact (surfaceTwoFormDensityCoefficient_continuous g omega).comp_continuousOn
      e.symm.continuousOn
  have hψaemeas : AEStronglyMeasurable ψ
      (riemannianVolumeChartMeasure g e) :=
    AEStronglyMeasurable.mono_ac hac
      (hψcont.aestronglyMeasurable e.open_target.measurableSet)
  have hchange :
      ∫ x in e.source, φ x ∂measureGeometry.volume =
        ∫ z, ψ z ∂riemannianVolumeChartMeasure g e := by
    refine riemannianVolume_source_integral_eq_chartMeasure_of_pointwise
      g measureGeometry e he
      (surfaceChart_source_nullMeasurable_volume g measureGeometry e he)
      (surfaceChart_aemeasurable_restrict_volume g measureGeometry e he)
      hψaemeas ?_
    intro x hx
    simp [ψ, φ, e.left_inv hx]
  calc
    surfaceTwoFormIntegral g measureGeometry omega =
        ∫ x in e.source, φ x ∂measureGeometry.volume := hrestrict
    _ = ∫ z, ψ z ∂riemannianVolumeChartMeasure g e := hchange
    _ = ∫ z in e.target,
          ψ z * surfaceMetricVolumeDensityInChart g e z
          ∂MeasureTheory.volume :=
      riemannianVolumeChartMeasure_integral_eq_setIntegral_density g e he ψ
    _ = ∫ z in e.target, surfaceTwoFormCoefficientInChart omega e z := by
      apply setIntegral_congr_fun e.open_target.measurableSet
      intro z hz
      exact surfaceTwoFormDensityCoefficient_mul_volumeDensityInChart
        g omega e he z hz

/--
%%handwave
name:
  Stokes' theorem for support in one surface chart
statement:
  If a smooth one-form \(\eta\) is supported in a compact subset of a single
  surface chart, then
  \[
    \int_X d\eta=0.
  \]
proof:
  Its exterior derivative has the same compact support.  Use the chart
  integral formula, identify the coordinate coefficient with
  \(\partial_xQ-\partial_yP\), and apply the compactly supported Euclidean
  integration-by-parts identity.
-/
theorem surfaceTwoFormIntegral_deRhamDifferential_eq_zero_of_chartSupport
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [ComplexOneManifold X]
    [IsManifold SurfaceRealModel ∞ X]
    (g : SmoothRiemannianMetricOnSurface X)
    (measureGeometry : SurfaceMetricMeasureGeometry X g)
    (eta : SmoothForms (I := SurfaceRealModel) (M := X) ℝ 1)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    (C : Set X) (hCcompact : IsCompact C) (hCsource : C ⊆ e.source)
    (hzero : ∀ x : X, x ∉ C → eta.toFun x = 0) :
    surfaceTwoFormIntegral g measureGeometry
      (deRhamDifferential (I := SurfaceRealModel) (M := X) (A := ℝ) 1 eta) = 0 := by
  letI : IsManifold SurfaceRealModel ∞ X := g.isManifold_real
  let K : Set ℂ := e '' C
  have hKcompact : IsCompact K :=
    hCcompact.image_of_continuousOn (e.continuousOn.mono hCsource)
  have hKtarget : K ⊆ e.target := by
    rintro _ ⟨x, hxC, rfl⟩
    exact e.map_source (hCsource hxC)
  have hcomponentZero : ∀ i : Fin 2, ∀ z ∈ e.target, z ∉ K →
      surfaceOneFormComponentInChart eta e i z = 0 := by
    intro i z hzTarget hzK
    have hxC : e.symm z ∉ C := by
      intro hxC
      exact hzK ⟨e.symm z, hxC, e.right_inv hzTarget⟩
    simp [surfaceOneFormComponentInChart, coordinateExpression,
      SurfaceRealModel, hzero (e.symm z) hxC]
    rfl
  have hdzero : ∀ x : X, x ∉ C →
      (deRhamDifferential (I := SurfaceRealModel) (M := X) (A := ℝ) 1 eta).toFun x = 0 :=
    deRhamDifferential_toFun_eq_zero_of_not_mem_compact_ambient
      C hCcompact eta hzero
  rw [surfaceTwoFormIntegral_eq_chartCoefficientIntegral_of_compactSupport
    g measureGeometry
    (deRhamDifferential (I := SurfaceRealModel) (M := X) (A := ℝ) 1 eta)
    e he C hCcompact hCsource hdzero]
  exact surfaceTwoFormCoefficientInChart_deRhamDifferential_integral_eq_zero
    eta e he K hKcompact hKtarget hcomponentZero

/--
%%handwave
name:
  Stokes' theorem for one-forms on a compact surface
statement:
  For every smooth one-form \(\eta\) on a compact Riemann surface,
  \[
    \int_X d\eta=0.
  \]
proof:
  Choose a finite partition of unity subordinate to surface charts and
  decompose \(\eta\) into finitely many chart-supported one-forms.  The
  chart-supported Stokes formula annihilates the integral of each exterior
  derivative, and linearity finishes the sum.
-/
theorem surfaceTwoFormIntegral_deRhamDifferential_eq_zero
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [ComplexOneManifold X] [CompactSpace X]
    [T2Space X] [SigmaCompactSpace X]
    [IsManifold SurfaceRealModel ∞ X]
    (g : SmoothRiemannianMetricOnSurface X)
    (measureGeometry : SurfaceMetricMeasureGeometry X g)
    (eta : SmoothForms (I := SurfaceRealModel) (M := X) ℝ 1) :
    surfaceTwoFormIntegral g measureGeometry
      (deRhamDifferential (I := SurfaceRealModel) (M := X) (A := ℝ) 1 eta) = 0 := by
  classical
  obtain ⟨ι, hι, χ, e, he, hχsmooth, hχsupport, hχsum⟩ :=
    exists_finite_surface_chart_supported_partition_of_compactSet
      g (Set.univ : Set X) isCompact_univ
  letI : Fintype ι := hι
  let χSmooth : ι → C^∞⟮SurfaceRealModel, X; ℝ⟯ := fun i ↦
    { val := χ i
      property := isSmoothOnSurface_univ_contMDiff (hχsmooth i) }
  let etaPiece : ι → SmoothForms
      (I := SurfaceRealModel) (M := X) ℝ 1 := fun i ↦
    smoothFormsPointwiseSMul
      (I := SurfaceRealModel) (M := X) (A := ℝ) (χSmooth i) eta
  have hsum : ∑ i : ι, etaPiece i = eta := by
    apply smoothFormsPointwiseSMul_finset_sum_eq_self_of_sum_eq_one
      (I := SurfaceRealModel) Finset.univ χSmooth eta
    intro x
    simpa [χSmooth] using hχsum x (Set.mem_univ x)
  have hpiece : ∀ i : ι,
      surfaceTwoFormIntegral g measureGeometry
        (deRhamDifferential
          (I := SurfaceRealModel) (M := X) (A := ℝ) 1 (etaPiece i)) = 0 := by
    intro i
    let C : Set X := tsupport (χ i)
    have hCcompact : IsCompact C :=
      isCompact_univ.of_isClosed_subset (isClosed_tsupport (χ i))
        (Set.subset_univ C)
    apply surfaceTwoFormIntegral_deRhamDifferential_eq_zero_of_chartSupport
      g measureGeometry (etaPiece i) (e i) (he i) C hCcompact (hχsupport i)
    intro x hxC
    apply smoothFormsPointwiseSMul_eq_zero_of_notMem_tsupport
      (I := SurfaceRealModel) (A := ℝ) (χSmooth i) eta
    simpa [C, χSmooth] using hxC
  have hdSum :
      deRhamDifferential (I := SurfaceRealModel) (M := X) (A := ℝ) 1 eta =
        ∑ i : ι,
          deRhamDifferential
            (I := SurfaceRealModel) (M := X) (A := ℝ) 1 (etaPiece i) := by
    rw [← hsum]
    exact map_sum
      (deRhamDifferential (I := SurfaceRealModel) (M := X) (A := ℝ) 1)
      _ Finset.univ
  rw [hdSum, surfaceTwoFormIntegral_finset_sum]
  apply Finset.sum_eq_zero
  intro i _hi
  exact hpiece i

/--
%%handwave
name:
  Nonzero integral detects a nonzero top-degree de Rham class
statement:
  A closed two-form \(\omega\) on a compact Riemann surface with
  \(\int_X\omega\ne0\) represents a nonzero class in \(H^2_{\mathrm{dR}}(X)\).
proof:
  If its class vanished, then \(\omega=d\eta\) for some smooth one-form
  \(\eta\).  Stokes' theorem would give \(\int_X\omega=0\), a contradiction.
-/
theorem surfaceTwoForm_deRhamClass_ne_zero_of_integral_ne_zero
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [ComplexOneManifold X] [CompactSpace X]
    [T2Space X] [SigmaCompactSpace X]
    [IsManifold SurfaceRealModel ∞ X]
    (g : SmoothRiemannianMetricOnSurface X)
    (measureGeometry : SurfaceMetricMeasureGeometry X g)
    (omega : DeRhamClosedForms
      (I := SurfaceRealModel) (M := X) (A := ℝ) 2)
    (hintegral : surfaceTwoFormIntegral g measureGeometry omega.1 ≠ 0) :
    (DeRhamExactClosedForms
      (I := SurfaceRealModel) (M := X) (A := ℝ) 2).mkQ omega ≠ 0 := by
  intro hzero
  have hmem : omega ∈ DeRhamExactClosedForms
      (I := SurfaceRealModel) (M := X) (A := ℝ) 2 := by
    rw [← Submodule.Quotient.mk_eq_zero]
    simpa [Submodule.mkQ_apply] using hzero
  change omega.1 ∈ DeRhamExactForms
    (I := SurfaceRealModel) (M := X) (A := ℝ) 2 at hmem
  rw [DeRhamExactForms] at hmem
  rcases hmem with ⟨eta, heta⟩
  apply hintegral
  rw [← heta]
  exact surfaceTwoFormIntegral_deRhamDifferential_eq_zero
    g measureGeometry eta

end JJMath.Uniformization
