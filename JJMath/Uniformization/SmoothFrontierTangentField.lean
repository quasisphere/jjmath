import JJMath.Uniformization.SmoothFrontierLocalCollar
import JJMath.RiemannianGeometry.SurfaceAnalysis

open Bundle Filter Function Set
open JJMath.Manifold
open scoped Manifold Topology ContDiff

namespace JJMath.Uniformization

noncomputable section

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
variable [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]

noncomputable def surfaceTangentQuarterTurn
    (V : (x : X) → TangentSpace SurfaceRealModel x) (x : X) :
    TangentSpace SurfaceRealModel x :=
  show ℂ from Complex.I * (show ℂ from V x)

noncomputable def complexQuarterTurnCLM : ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.mulLeftRight ℝ ℂ Complex.I) 1

/--
%%handwave
name:
  The complex quarter-turn map is multiplication by \(i\)
statement:
  For every \(z\in\mathbb C\), the real-linear quarter-turn map satisfies
  \[
    J(z)=iz.
  \]
proof:
  This is the evaluation formula for the continuous linear map defined by
  left multiplication by \(i\).
-/
@[simp]
theorem complexQuarterTurnCLM_apply (z : ℂ) :
    complexQuarterTurnCLM z = Complex.I * z := by
  simp [complexQuarterTurnCLM, ContinuousLinearMap.mulLeftRight_apply]

/--
%%handwave
name:
  Smoothness of the quarter-turn of a surface vector field
statement:
  If \(V\) is a smooth vector field on a Riemann surface, then the field
  \[
    x\longmapsto J V_x=iV_x
  \]
  is smooth.
proof:
  In a complex-linear tangent trivialization, multiplication by \(i\)
  commutes with the coordinate change.  Thus the coordinate coefficients of
  \(JV\) are obtained by applying the fixed real-linear quarter-turn map to
  the smooth coefficients of \(V\).
-/
theorem surfaceTangentQuarterTurn_contMDiff
    (V : (x : X) → TangentSpace SurfaceRealModel x)
    (hV : ContMDiff SurfaceRealModel SurfaceRealModel.tangent ∞
      (fun x => (⟨x, V x⟩ : TangentBundle SurfaceRealModel X))) :
    ContMDiff SurfaceRealModel SurfaceRealModel.tangent ∞
      (fun x => (⟨x, surfaceTangentQuarterTurn V x⟩ :
        TangentBundle SurfaceRealModel X)) := by
  intro x₀
  let e := trivializationAt ℂ
    (TangentSpace SurfaceRealModel : X → Type) x₀
  have hx₀ : x₀ ∈ e.baseSet := by
    exact mem_chart_source ℂ x₀
  rw [e.contMDiffAt_section_iff hx₀]
  have hcoeff : ContMDiffAt SurfaceRealModel 𝓘(ℝ, ℂ) ∞
      (fun y => (e (⟨y, V y⟩ : TangentBundle SurfaceRealModel X)).2) x₀ := by
    exact (e.contMDiffAt_section_iff hx₀).mp (hV x₀)
  have hrot : ContMDiffAt SurfaceRealModel 𝓘(ℝ, ℂ) ∞
      (fun y => Complex.I *
        (e (⟨y, V y⟩ : TangentBundle SurfaceRealModel X)).2) x₀ :=
    by
      simpa [Function.comp_def] using
        complexQuarterTurnCLM.contDiff.comp_contMDiffAt hcoeff
  apply hrot.congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds hx₀] with y hy
  change (e (⟨y, show ℂ from Complex.I * (show ℂ from V y)⟩ :
      TangentBundle SurfaceRealModel X)).2 =
    Complex.I * (e (⟨y, V y⟩ : TangentBundle SurfaceRealModel X)).2
  rw [← congrFun (e.coe_linearMapAt_of_mem (R := ℝ) hy)
      (show ℂ from Complex.I * (show ℂ from V y)),
    ← congrFun (e.coe_linearMapAt_of_mem (R := ℝ) hy) (V y)]
  change e.continuousLinearMapAt ℝ y
      (show ℂ from Complex.I * (show ℂ from V y)) =
    Complex.I * e.continuousLinearMapAt ℝ y (V y)
  let L : ℂ →L[ℝ] ℂ := e.continuousLinearMapAt ℝ y
  have hI : L Complex.I = Complex.I * L 1 :=
    (tangentTrivializationAt_continuousLinearMapAt_complex_linear_nonzero
      x₀ y hy).1
  change L (Complex.I * (show ℂ from V y)) =
    Complex.I * L (show ℂ from V y)
  rw [complexLinearMap_apply_eq_mul L hI
      (Complex.I * (show ℂ from V y)),
    complexLinearMap_apply_eq_mul L hI (show ℂ from V y)]
  ring

/-- The transverse field rotated by the complex orientation. -/
noncomputable def smoothFrontierQuarterTurnVectorField
    (D : SmoothBoundaryDomain X) (x : X) :
    TangentSpace SurfaceRealModel x :=
  surfaceTangentQuarterTurn (smoothFrontierTransverseVectorField D) x

/--
%%handwave
name:
  Smoothness of the rotated transverse frontier field
statement:
  The quarter-turn \(JV\) of the chosen smooth transverse frontier field
  \(V\) is a smooth vector field on the surface.
proof:
  Apply smoothness of quarter-turning a vector field to the chosen smooth
  transverse field.
-/
theorem smoothFrontierQuarterTurnVectorField_contMDiff
    (D : SmoothBoundaryDomain X) :
    ContMDiff SurfaceRealModel SurfaceRealModel.tangent ∞
      (fun x => (⟨x, smoothFrontierQuarterTurnVectorField D x⟩ :
        TangentBundle SurfaceRealModel X)) :=
  surfaceTangentQuarterTurn_contMDiff _
    (smoothFrontierTransverseVectorField_contMDiff D)

/--
%%handwave
name:
  Smoothness of the transverse derivative to all orders
statement:
  If \(s\) is the global signed boundary coordinate and \(V\) the chosen
  transverse field, then
  \[
    x\longmapsto ds_x(V_x)
  \]
  is smooth.
proof:
  The tangent map of the smooth function \(s\) is smooth to all orders.
  Compose it with the smooth tangent section \(x\mapsto(x,V_x)\) and project
  to the scalar fiber coordinate.
-/
theorem smoothFrontierTransverseDerivative_contMDiff_top
    (D : SmoothBoundaryDomain X) :
    ContMDiff SurfaceRealModel 𝓘(ℝ) ∞
      (smoothFrontierTransverseDerivative D) := by
  have htan : ContMDiff SurfaceRealModel.tangent 𝓘(ℝ).tangent ∞
      (tangentMap SurfaceRealModel 𝓘(ℝ)
        (smoothBoundaryGlobalSignedCoordinate D)) :=
    (smoothBoundaryGlobalSignedCoordinate_contMDiff D).contMDiff_tangentMap
      (by simp)
  have hsection : ContMDiff SurfaceRealModel SurfaceRealModel.tangent ∞
      (fun x => (⟨x, smoothFrontierTransverseVectorField D x⟩ :
        TangentBundle SurfaceRealModel X)) :=
    smoothFrontierTransverseVectorField_contMDiff D
  exact (contMDiff_snd_tangentBundle_modelSpace ℝ 𝓘(ℝ)).comp
    (htan.comp hsection)

/-- The derivative of the signed boundary coordinate in the rotated
transverse direction. -/
noncomputable def smoothFrontierAngularDerivative
    (D : SmoothBoundaryDomain X) (x : X) : ℝ :=
  tangentMap SurfaceRealModel 𝓘(ℝ)
    (smoothBoundaryGlobalSignedCoordinate D)
    (⟨x, smoothFrontierQuarterTurnVectorField D x⟩ :
      TangentBundle SurfaceRealModel X) |>.2

/--
%%handwave
name:
  Smoothness of the angular derivative of the signed coordinate
statement:
  The function
  \[
    x\longmapsto ds_x(JV_x)
  \]
  is smooth on the surface.
proof:
  Compose the smooth tangent map of \(s\) with the smooth section
  \(x\mapsto(x,JV_x)\), then take the real fiber coordinate.
-/
theorem smoothFrontierAngularDerivative_contMDiff
    (D : SmoothBoundaryDomain X) :
    ContMDiff SurfaceRealModel 𝓘(ℝ) ∞
      (smoothFrontierAngularDerivative D) := by
  have htan : ContMDiff SurfaceRealModel.tangent 𝓘(ℝ).tangent ∞
      (tangentMap SurfaceRealModel 𝓘(ℝ)
        (smoothBoundaryGlobalSignedCoordinate D)) :=
    (smoothBoundaryGlobalSignedCoordinate_contMDiff D).contMDiff_tangentMap
      (by simp)
  have hsection : ContMDiff SurfaceRealModel SurfaceRealModel.tangent ∞
      (fun x => (⟨x, smoothFrontierQuarterTurnVectorField D x⟩ :
        TangentBundle SurfaceRealModel X)) :=
    smoothFrontierQuarterTurnVectorField_contMDiff D
  exact (contMDiff_snd_tangentBundle_modelSpace ℝ 𝓘(ℝ)).comp
    (htan.comp hsection)

/-- A globally smooth field tangent to every level of the signed boundary
coordinate.  The determinant-like formula avoids dividing by the transverse
derivative away from the frontier. -/
noncomputable def smoothFrontierTangentVectorField
    (D : SmoothBoundaryDomain X) (x : X) :
    TangentSpace SurfaceRealModel x :=
  smoothFrontierTransverseDerivative D x •
      smoothFrontierQuarterTurnVectorField D x -
    smoothFrontierAngularDerivative D x •
      smoothFrontierTransverseVectorField D x

/--
%%handwave
name:
  Smoothness of the oriented frontier tangent field
statement:
  The vector field
  \[
    T_x=ds_x(V_x)\,JV_x-ds_x(JV_x)\,V_x
  \]
  is smooth.
proof:
  Both scalar coefficient functions and both vector fields in the formula
  are smooth.  Smooth sections are closed under scalar multiplication and
  subtraction.
-/
theorem smoothFrontierTangentVectorField_contMDiff
    (D : SmoothBoundaryDomain X) :
    ContMDiff SurfaceRealModel SurfaceRealModel.tangent ∞
      (fun x => (⟨x, smoothFrontierTangentVectorField D x⟩ :
        TangentBundle SurfaceRealModel X)) := by
  apply ContMDiff.sub_section
  · exact (smoothFrontierTransverseDerivative_contMDiff_top D)
      |>.smul_section (smoothFrontierQuarterTurnVectorField_contMDiff D)
  · exact (smoothFrontierAngularDerivative_contMDiff D).smul_section
      (smoothFrontierTransverseVectorField_contMDiff D)

/--
%%handwave
name:
  Evaluation formula for the angular derivative
statement:
  For every \(x\in X\), the angular derivative is
  \[
    \alpha_D(x)=ds_x(JV_x).
  \]
proof:
  The scalar component of the tangent map of \(s\) at \((x,JV_x)\) is the
  manifold derivative \(ds_x\) applied to \(JV_x\).
-/
@[simp]
theorem smoothFrontierAngularDerivative_apply
    (D : SmoothBoundaryDomain X) (x : X) :
    smoothFrontierAngularDerivative D x =
      (show ℝ from mfderiv SurfaceRealModel 𝓘(ℝ)
        (smoothBoundaryGlobalSignedCoordinate D) x
        (smoothFrontierQuarterTurnVectorField D x)) := by
  simp [smoothFrontierAngularDerivative]

/--
%%handwave
name:
  The oriented frontier field is tangent to the signed-coordinate levels
statement:
  For every \(x\in X\),
  \[
    ds_x(T_x)=0.
  \]
proof:
  Substitute
  \(T_x=ds_x(V_x)JV_x-ds_x(JV_x)V_x\) and use linearity:
  the two resulting scalar products are equal and cancel.
-/
theorem smoothFrontierTangentVectorField_mfderiv_eq_zero
    (D : SmoothBoundaryDomain X) (x : X) :
    (show ℝ from mfderiv SurfaceRealModel 𝓘(ℝ)
      (smoothBoundaryGlobalSignedCoordinate D) x
      (smoothFrontierTangentVectorField D x)) = 0 := by
  rw [smoothFrontierTangentVectorField, map_sub, map_smul, map_smul,
    smoothFrontierTransverseDerivative_apply,
    smoothFrontierAngularDerivative_apply]
  change
    (show ℝ from mfderiv SurfaceRealModel 𝓘(ℝ)
      (smoothBoundaryGlobalSignedCoordinate D) x
      (smoothFrontierTransverseVectorField D x)) *
        (show ℝ from mfderiv SurfaceRealModel 𝓘(ℝ)
          (smoothBoundaryGlobalSignedCoordinate D) x
          (smoothFrontierQuarterTurnVectorField D x)) -
      (show ℝ from mfderiv SurfaceRealModel 𝓘(ℝ)
        (smoothBoundaryGlobalSignedCoordinate D) x
        (smoothFrontierQuarterTurnVectorField D x)) *
        (show ℝ from mfderiv SurfaceRealModel 𝓘(ℝ)
          (smoothBoundaryGlobalSignedCoordinate D) x
          (smoothFrontierTransverseVectorField D x)) = 0
  ring

/--
%%handwave
name:
  Nonvanishing of the oriented tangent field on the frontier
statement:
  If \(x\in\partial D\), then \(T_x\ne0\).
proof:
  Write \(a=ds_x(V_x)>0\) and \(b=ds_x(JV_x)\).  If
  \(T_x=aJV_x-bV_x\) vanished, then in the complex tangent line
  \((ai-b)V_x=0\).  Transversality implies \(V_x\ne0\), while \(a>0\)
  prevents \(ai-b\) from vanishing.
-/
theorem smoothFrontierTangentVectorField_ne_zero
    (D : SmoothBoundaryDomain X) {x : X}
    (hx : x ∈ frontier D.carrier) :
    smoothFrontierTangentVectorField D x ≠ 0 := by
  let V : ℂ := smoothFrontierTransverseVectorField D x
  let a : ℝ := smoothFrontierTransverseDerivative D x
  let b : ℝ := smoothFrontierAngularDerivative D x
  have ha : 0 < a := by
    change 0 < smoothFrontierTransverseDerivative D x
    rw [smoothFrontierTransverseDerivative_apply]
    exact smoothFrontierTransverseVectorField_mfderiv_pos D hx
  have hV : V ≠ 0 := by
    intro hzero
    have hpos := smoothFrontierTransverseVectorField_mfderiv_pos D hx
    rw [show smoothFrontierTransverseVectorField D x = 0 by exact hzero] at hpos
    simp at hpos
    exact (lt_irrefl 0 hpos)
  intro hzero
  have hcomplex : (a * Complex.I - b) * V = 0 := by
    have hzero' : a • (Complex.I * V) - b • V = 0 := by
      simpa [smoothFrontierTangentVectorField, a, b, V,
        smoothFrontierQuarterTurnVectorField, surfaceTangentQuarterTurn]
        using hzero
    simpa [Complex.real_smul, sub_mul, mul_assoc] using hzero'
  have hab : (a : ℂ) * Complex.I - (b : ℂ) = 0 :=
    (mul_eq_zero.mp hcomplex).resolve_right hV
  have him := congrArg Complex.im hab
  simp at him
  exact ha.ne' him

/--
%%handwave
name:
  Zero derivative of the signed coordinate along tangent flow
statement:
  If \(\gamma\) is an integral curve of \(T\) at time \(t\), then
  \[
    \frac{d}{du}\Big|_{u=t}s(\gamma(u))=0.
  \]
proof:
  The manifold chain rule gives
  \((s\circ\gamma)'(t)=ds_{\gamma(t)}(T_{\gamma(t)})\), and the tangent-field
  construction makes the latter zero.
-/
theorem smoothBoundaryGlobalSignedCoordinate_hasDerivAt_zero_along_tangentIntegralCurve
    (D : SmoothBoundaryDomain X) {gamma : ℝ → X} {t : ℝ}
    (hgamma : IsMIntegralCurveAt gamma
      (smoothFrontierTangentVectorField D) t) :
    HasDerivAt (fun s : ℝ =>
      smoothBoundaryGlobalSignedCoordinate D (gamma s)) 0 t := by
  let h : X → ℝ := smoothBoundaryGlobalSignedCoordinate D
  let c : ℝ := show ℝ from
    mfderiv SurfaceRealModel 𝓘(ℝ) h (gamma t)
      (smoothFrontierTangentVectorField D (gamma t))
  have hh : MDifferentiableAt SurfaceRealModel 𝓘(ℝ) h (gamma t) :=
    ((smoothBoundaryGlobalSignedCoordinate_contMDiff D).contMDiffAt
      |>.mdifferentiableAt (by norm_num))
  have hcomp := hh.hasMFDerivAt.comp t hgamma.hasMFDerivAt
  have hordinary : HasDerivAt (h ∘ gamma) c t := by
    rw [hasDerivAt_iff_hasFDerivAt]
    convert hcomp.hasFDerivAt using 1
    apply ContinuousLinearMap.ext
    intro a
    change a * (show ℝ from mfderiv SurfaceRealModel 𝓘(ℝ) h (gamma t)
      (smoothFrontierTangentVectorField D (gamma t))) =
        (show ℝ from mfderiv SurfaceRealModel 𝓘(ℝ) h (gamma t)
          (a • smoothFrontierTangentVectorField D (gamma t)))
    rw [map_smul]
    rfl
  have hc : c = 0 := by
    simpa [c, h] using
      smoothFrontierTangentVectorField_mfderiv_eq_zero D (gamma t)
  simpa only [Function.comp_apply, h, hc] using hordinary

/--
%%handwave
name:
  Constancy of the signed coordinate along a tangent integral curve
statement:
  If \(\gamma\) is an integral curve of \(T\) on an interval
  \((a,b)\), then for all \(s,t\in(a,b)\),
  \[
    s_D(\gamma(s))=s_D(\gamma(t)).
  \]
proof:
  The derivative of the composite signed coordinate is zero at every point
  of the interval.  A differentiable real function with zero derivative on
  a connected interval is constant.
-/
theorem smoothBoundaryGlobalSignedCoordinate_eq_along_tangentIntegralCurveOn_Ioo
    (D : SmoothBoundaryDomain X) {gamma : ℝ → X} {a b s t : ℝ}
    (hgamma : IsMIntegralCurveOn gamma
      (smoothFrontierTangentVectorField D) (Ioo a b))
    (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b) :
    smoothBoundaryGlobalSignedCoordinate D (gamma s) =
      smoothBoundaryGlobalSignedCoordinate D (gamma t) := by
  let f : ℝ → ℝ := fun u =>
    smoothBoundaryGlobalSignedCoordinate D (gamma u)
  have hdiff : DifferentiableOn ℝ f (Ioo a b) := by
    intro u hu
    exact (smoothBoundaryGlobalSignedCoordinate_hasDerivAt_zero_along_tangentIntegralCurve
      D (hgamma.isMIntegralCurveAt (isOpen_Ioo.mem_nhds hu))).differentiableAt
      |>.differentiableWithinAt
  have hderiv : (Ioo a b).EqOn (deriv f) 0 := by
    intro u hu
    exact (smoothBoundaryGlobalSignedCoordinate_hasDerivAt_zero_along_tangentIntegralCurve
      D (hgamma.isMIntegralCurveAt (isOpen_Ioo.mem_nhds hu))).deriv
  exact isOpen_Ioo.is_const_of_deriv_eq_zero
    (ordConnected_Ioo.isPreconnected) hdiff hderiv hs ht

/--
%%handwave
name:
  Tangent integral curves preserve the frontier
statement:
  Let \(\gamma\) be an integral curve of \(T\) on \((a,b)\).  If
  \(\gamma(t_0)\in\partial D\) for some \(t_0\in(a,b)\), then
  \[
    \gamma(t)\in\partial D\qquad(t\in(a,b)).
  \]
proof:
  The signed coordinate is constant along the curve and equals zero at
  \(t_0\).  Locally in the global boundary-coordinate neighborhood, its
  zero set is exactly the frontier.  Thus the set of times at which the
  curve lies in the frontier is both open and closed in the connected
  interval and is nonempty, hence is the whole interval.
-/
theorem tangentIntegralCurveOn_Ioo_mem_frontier
    (D : SmoothBoundaryDomain X) {gamma : ℝ → X} {a b t₀ : ℝ}
    (hgamma : IsMIntegralCurveOn gamma
      (smoothFrontierTangentVectorField D) (Ioo a b))
    (ht₀ : t₀ ∈ Ioo a b) (hgamma₀ : gamma t₀ ∈ frontier D.carrier) :
    ∀ t ∈ Ioo a b, gamma t ∈ frontier D.carrier := by
  let S : Set ℝ := Ioo a b
  let g : S → X := fun t => gamma t
  let A : Set S := g ⁻¹' frontier D.carrier
  have hg : Continuous g := by
    exact hgamma.continuousOn.restrict
  have hAclosed : IsClosed A := by
    exact isClosed_frontier.preimage hg
  have hAopen : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro u hu
    have hgu : g u ∈ frontier D.carrier := hu
    have hguN : g u ∈ smoothBoundaryGlobalCoordinateNeighborhood D :=
      frontier_subset_smoothBoundaryGlobalCoordinateNeighborhood D hgu
    have hpreN : g ⁻¹' smoothBoundaryGlobalCoordinateNeighborhood D ∈ nhds u :=
      hg.continuousAt.preimage_mem_nhds
        ((smoothBoundaryGlobalCoordinateNeighborhood_isOpen D).mem_nhds hguN)
    apply Filter.mem_of_superset hpreN
    intro v hv
    change gamma v ∈ frontier D.carrier
    apply (smoothBoundaryGlobalSignedCoordinate_eq_zero_iff_mem_frontier D hv).mp
    calc
      smoothBoundaryGlobalSignedCoordinate D (gamma v) =
          smoothBoundaryGlobalSignedCoordinate D (gamma u) :=
        smoothBoundaryGlobalSignedCoordinate_eq_along_tangentIntegralCurveOn_Ioo
          D hgamma v.2 u.2
      _ = 0 := smoothBoundaryGlobalSignedCoordinate_eq_zero_of_mem_frontier D hgu
  letI : PreconnectedSpace S :=
    Subtype.preconnectedSpace ordConnected_Ioo.isPreconnected
  have hAnonempty : A.Nonempty := by
    let u₀ : S := ⟨t₀, ht₀⟩
    exact ⟨u₀, hgamma₀⟩
  have hAuniv : A = Set.univ :=
    (show IsClopen A from ⟨hAclosed, hAopen⟩).eq_univ hAnonempty
  intro t ht
  let u : S := ⟨t, ht⟩
  have hu : u ∈ A := by rw [hAuniv]; exact Set.mem_univ u
  exact hu

end

end JJMath.Uniformization
