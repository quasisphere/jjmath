import JJMath.Uniformization.SmoothFrontierCollar
import JJMath.Manifold.SmoothLocalFlow
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# A smooth transverse field along a smooth frontier

The signed boundary coordinate constructed from the local defining functions
is only needed through its first derivative.  Its positive tangent half-spaces
along the frontier are convex.  Local smooth tangent frames provide sections
lying in those half-spaces, and a smooth partition of unity therefore gives a
globally smooth vector field transverse to the frontier.  In particular, the
vector field and the chosen signed coordinate are smooth to every finite
order.
-/

open Bundle Filter Function Set
open JJMath.Manifold
open scoped Manifold Topology ContDiff

namespace JJMath.Uniformization

noncomputable section

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
variable [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]

/-- The fiberwise positive half-space selected by the signed boundary
coordinate at frontier points.  Away from the frontier there is no
restriction. -/
def smoothFrontierPositiveTangentCone
    (D : SmoothBoundaryDomain X) (x : X) :
    Set (TangentSpace SurfaceRealModel x) :=
  {v | x ∈ frontier D.carrier →
    0 < (show ℝ from mfderiv SurfaceRealModel 𝓘(ℝ)
      (smoothBoundaryGlobalSignedCoordinate D) x v)}

/--
%%handwave
name:
  Convexity of the positive transverse tangent cone
statement:
  Let \(s\) be the global signed boundary coordinate of \(D\).  For every
  \(x\in X\), the set
  \[
    C_x=\{v\in T_xX:x\in\partial D\Rightarrow ds_x(v)>0\}
  \]
  is convex over \(\mathbb R\).
proof:
  At a frontier point this is the strict half-space cut out by the linear
  functional \(ds_x\), and positive convex combinations preserve strict
  positivity.  Away from the frontier the condition is vacuous, so the cone
  is the whole tangent space.
-/
theorem smoothFrontierPositiveTangentCone_convex
    (D : SmoothBoundaryDomain X) (x : X) :
    Convex ℝ (smoothFrontierPositiveTangentCone D x) := by
  by_cases hx : x ∈ frontier D.carrier
  · intro v hv w hw a b ha hb hab _hx
    have hv' := hv hx
    have hw' := hw hx
    rw [map_add, map_smul, map_smul]
    change 0 < a * (show ℝ from mfderiv SurfaceRealModel 𝓘(ℝ)
      (smoothBoundaryGlobalSignedCoordinate D) x v) +
        b * (show ℝ from mfderiv SurfaceRealModel 𝓘(ℝ)
          (smoothBoundaryGlobalSignedCoordinate D) x w)
    rcases ha.lt_or_eq with ha' | rfl
    · exact add_pos_of_pos_of_nonneg
        (mul_pos ha' hv') (mul_nonneg hb hw'.le)
    · have hb_one : b = 1 := by linarith
      simp [hb_one, hw']
  · simpa [smoothFrontierPositiveTangentCone, hx] using
      (convex_univ : Convex ℝ (Set.univ : Set (TangentSpace SurfaceRealModel x)))

/--
%%handwave
name:
  Local smooth sections of the positive transverse tangent cone
statement:
  For every \(x\in X\), there are a neighborhood \(U\) of \(x\) and a smooth
  tangent field \(V\) on \(U\) such that
  \[
    y\in U\cap\partial D\quad\Longrightarrow\quad ds_y(V_y)>0.
  \]
proof:
  At a frontier point, choose and normalize a tangent vector on which
  \(ds_x\) equals \(1\), extend it by a smooth local frame, and shrink the
  neighborhood so that continuity preserves positivity.  Away from the
  frontier, the zero field on the open complement satisfies the vacuous
  condition.
-/
theorem exists_smoothLocalSection_mem_smoothFrontierPositiveTangentCone
    (D : SmoothBoundaryDomain X) (x : X) :
    ∃ U ∈ 𝓝 x,
      ∃ s : (y : X) → TangentSpace SurfaceRealModel y,
        ContMDiffOn SurfaceRealModel SurfaceRealModel.tangent ∞
          (fun y => (⟨y, s y⟩ : TangentBundle SurfaceRealModel X)) U ∧
        ∀ y ∈ U, s y ∈ smoothFrontierPositiveTangentCone D y := by
  classical
  by_cases hx : x ∈ frontier D.carrier
  · let h : X → ℝ := smoothBoundaryGlobalSignedCoordinate D
    let L : TangentSpace SurfaceRealModel x →L[ℝ] ℝ :=
      mfderiv SurfaceRealModel 𝓘(ℝ) h x
    have hL : L ≠ 0 := by
      simpa [L, h] using
        smoothBoundaryGlobalSignedCoordinate_mfderiv_ne_zero D hx
    obtain ⟨w, hw⟩ : ∃ w : TangentSpace SurfaceRealModel x, L w ≠ 0 := by
      by_contra hnone
      push Not at hnone
      apply hL
      ext v
      simpa using hnone v
    let v : TangentSpace SurfaceRealModel x := (L w)⁻¹ • w
    have hLv : L v = 1 := by
      simp [v, map_smul, hw]
    let e := trivializationAt ℂ
      (TangentSpace SurfaceRealModel) x
    have hxe : x ∈ e.baseSet := by
      exact mem_chart_source ℂ x
    let B : Module.Basis (Fin 2) ℝ (TangentSpace SurfaceRealModel x) :=
      e.basisAt Complex.basisOneI hxe
    let c : Fin 2 → ℝ := fun i => B.repr v i
    let s : (y : X) → TangentSpace SurfaceRealModel y := fun y =>
      ∑ i : Fin 2, c i • e.localFrame Complex.basisOneI i y
    have hs_smooth : ContMDiffOn SurfaceRealModel SurfaceRealModel.tangent ∞
        (fun y => (⟨y, s y⟩ : TangentBundle SurfaceRealModel X)) e.baseSet := by
      apply ContMDiffOn.sum_section
      intro i _hi
      exact (e.contMDiffOn_localFrame_baseSet ∞ Complex.basisOneI i).const_smul_section
    have hsx : s x = v := by
      change (∑ i : Fin 2, c i • e.localFrame Complex.basisOneI i x) = v
      simp only [e.localFrame_apply_of_mem_baseSet Complex.basisOneI hxe]
      simp [c, B, B.sum_repr v]
    let H : X → ℝ := fun y =>
      (tangentMap SurfaceRealModel 𝓘(ℝ) h
        (⟨y, s y⟩ : TangentBundle SurfaceRealModel X)).2
    have hh_smooth : ContMDiff SurfaceRealModel 𝓘(ℝ) 2 h := by
      simpa [h] using (smoothBoundaryGlobalSignedCoordinate_contMDiff D).of_le
        (by exact WithTop.coe_le_coe.mpr le_top)
    have htan_smooth : ContMDiff SurfaceRealModel.tangent 𝓘(ℝ).tangent 1
        (tangentMap SurfaceRealModel 𝓘(ℝ) h) :=
      hh_smooth.contMDiff_tangentMap (by norm_num)
    have hs_at : ContMDiffAt SurfaceRealModel SurfaceRealModel.tangent ∞
        (fun y => (⟨y, s y⟩ : TangentBundle SurfaceRealModel X)) x :=
      hs_smooth.contMDiffAt (e.open_baseSet.mem_nhds hxe)
    have hH_at : ContMDiffAt SurfaceRealModel 𝓘(ℝ) 1 H x := by
      have hcomp : ContMDiffAt SurfaceRealModel 𝓘(ℝ).tangent 1
          (fun y => tangentMap SurfaceRealModel 𝓘(ℝ) h
            (⟨y, s y⟩ : TangentBundle SurfaceRealModel X)) x :=
        htan_smooth.contMDiffAt.comp x (hs_at.of_le (by norm_num))
      exact (contMDiff_snd_tangentBundle_modelSpace ℝ 𝓘(ℝ)).contMDiffAt.comp x hcomp
    have hHx : H x = 1 := by
      simp only [H, tangentMap_snd, hsx]
      exact hLv
    have hpositive : {y : X | 0 < H y} ∈ 𝓝 x := by
      have htend : Tendsto H (𝓝 x) (𝓝 (H x)) := hH_at.continuousAt
      apply htend (Ioi_mem_nhds (show 0 < H x by rw [hHx]; norm_num))
    let U : Set X := e.baseSet ∩ {y : X | 0 < H y}
    have hU : U ∈ 𝓝 x :=
      inter_mem (e.open_baseSet.mem_nhds hxe) hpositive
    refine ⟨U, hU, s, hs_smooth.mono inter_subset_left, ?_⟩
    intro y hy hyfrontier
    have hyH : 0 < H y := hy.2
    simpa only [H, tangentMap_snd, h] using hyH
  · let U : Set X := (frontier D.carrier)ᶜ
    let s : (y : X) → TangentSpace SurfaceRealModel y := fun _ => 0
    refine ⟨U, isOpen_compl_iff.mpr isClosed_frontier |>.mem_nhds hx,
      s, ?_, ?_⟩
    · exact (Bundle.contMDiff_zeroSection ℝ
        (TangentSpace SurfaceRealModel : X → Type _)).contMDiffOn
    · intro y hy hyfrontier
      exact (hy hyfrontier).elim

/--
%%handwave
name:
  Existence of a smooth transverse boundary field
statement:
  For a smooth domain \(D\) with global signed boundary coordinate \(s\),
  there is a smooth vector field \(V\) on the surface such that
  \[
    ds_x(V_x)>0\qquad(x\in\partial D).
  \]
proof:
  At each frontier point, nonvanishing of \(ds\) gives a local smooth vector
  field in the open half-space \(ds(V)>0\); away from the frontier use the
  zero field.  These pointwise admissible sets are convex, so a smooth
  partition of unity glues the local fields while preserving strict
  positivity on the frontier.
-/
theorem exists_smoothFrontierTransverseVectorField
    (D : SmoothBoundaryDomain X) :
    ∃ V : (x : X) → TangentSpace SurfaceRealModel x,
      ContMDiff SurfaceRealModel SurfaceRealModel.tangent ∞
        (fun x => (⟨x, V x⟩ : TangentBundle SurfaceRealModel X)) ∧
      ∀ x ∈ frontier D.carrier,
        0 < (show ℝ from mfderiv SurfaceRealModel 𝓘(ℝ)
          (smoothBoundaryGlobalSignedCoordinate D) x (V x)) := by
  letI : SecondCountableTopology X :=
    rado_secondCountableTopology_riemannSurface X
  letI : SigmaCompactSpace X := inferInstance
  rcases exists_contMDiffSection_forall_mem_convex_of_local
      (n := (⊤ : ℕ∞)) SurfaceRealModel
      (fun x : X => TangentSpace SurfaceRealModel x)
      (smoothFrontierPositiveTangentCone D)
      (smoothFrontierPositiveTangentCone_convex D)
      (exists_smoothLocalSection_mem_smoothFrontierPositiveTangentCone D) with
    ⟨V, hV⟩
  exact ⟨V, V.contMDiff, fun x hx => hV x hx⟩

/-- A fixed choice of smooth vector field transverse to the frontier. -/
noncomputable def smoothFrontierTransverseVectorField
    (D : SmoothBoundaryDomain X) (x : X) :
    TangentSpace SurfaceRealModel x :=
  Classical.choose (exists_smoothFrontierTransverseVectorField D) x
/--
%%handwave
name:
  Smoothness of the chosen transverse field
statement:
  The fixed transverse field \(V\) selected for \(D\) defines a smooth
  section \(x\mapsto(x,V_x)\) of the tangent bundle.
proof:
  [A smooth field satisfying the required transversality exists](lean:JJMath.Uniformization.exists_smoothFrontierTransverseVectorField), and the fixed field is chosen together with that smoothness property.
-/
theorem smoothFrontierTransverseVectorField_contMDiff
    (D : SmoothBoundaryDomain X) :
    ContMDiff SurfaceRealModel SurfaceRealModel.tangent ∞
      (fun x => (⟨x, smoothFrontierTransverseVectorField D x⟩ :
        TangentBundle SurfaceRealModel X)) :=
  (Classical.choose_spec (exists_smoothFrontierTransverseVectorField D)).1

/-- The chosen transverse vector field written in the fixed tangent
trivialization and base chart centered at `x`. -/
noncomputable def smoothFrontierCoordinateVectorField
    (D : SmoothBoundaryDomain X) (x : X) (z : ℂ) : ℂ :=
  let y := (extChartAt SurfaceRealModel x).symm z
  ((trivializationAt ℂ (TangentSpace SurfaceRealModel) x)
    (⟨y, smoothFrontierTransverseVectorField D y⟩ :
      TangentBundle SurfaceRealModel X)).2

/--
%%handwave
name:
  The coordinate transverse field at the chart center
statement:
  Let \(V\) be the chosen transverse field and let \(v_x\) be its expression
  in the surface chart centered at \(x\).  Then
  \[
    v_x(\phi_x(x))=V_x,
  \]
  under the canonical identification of \(T_xX\) with the model space
  supplied by the centered chart.
proof:
  Expanding the tangent-bundle trivialization gives the derivative of the
  chart applied to \(V_x\).  At the chart center the inverse-chart and chart
  derivatives cancel, leaving \(V_x\).
-/
theorem smoothFrontierCoordinateVectorField_apply_center
    (D : SmoothBoundaryDomain X) (x : X) :
    smoothFrontierCoordinateVectorField D x
        (extChartAt SurfaceRealModel x x) =
      smoothFrontierTransverseVectorField D x := by
  simp [smoothFrontierCoordinateVectorField,
    TangentBundle.trivializationAt_apply]
  rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
  have hround := fderivWithin_extChartAt_comp_extChartAt_symm_range
    (I := SurfaceRealModel) (x := x)
  have happ := congrArg
    (fun L : ℂ →L[ℝ] ℂ => L (smoothFrontierTransverseVectorField D x)) hround
  simpa [SurfaceRealModel] using happ

/--
%%handwave
name:
  Coordinate expression of the transverse field
statement:
  Fix \(x\in X\), put \(y=\phi_x^{-1}(z)\), and let \(V\) be the chosen
  transverse field.  Its expression in the chart centered at \(x\) is
  \[
    v_x(z)=d(\phi_x\circ\phi_y^{-1})_{\phi_y(y)}(V_y).
  \]
proof:
  This is the definition of the tangent-bundle trivialization associated to
  the fixed chart, written as the tangent coordinate change from the chart
  centered at \(y\) to the chart centered at \(x\).
-/
theorem smoothFrontierCoordinateVectorField_eq_tangentCoordChange
    (D : SmoothBoundaryDomain X) (x : X) (z : ℂ) :
    smoothFrontierCoordinateVectorField D x z =
      tangentCoordChange SurfaceRealModel
        ((extChartAt SurfaceRealModel x).symm z) x
        ((extChartAt SurfaceRealModel x).symm z)
        (smoothFrontierTransverseVectorField D
          ((extChartAt SurfaceRealModel x).symm z)) := by
  rw [smoothFrontierCoordinateVectorField]
  simp only [TangentBundle.trivializationAt_apply]
  rfl

omit [RiemannSurface X] in
/--
%%handwave
name:
  Derivative of an inverse surface chart
statement:
  Let \(\phi_x\) be a surface chart, let \(z\) lie in its target, and put
  \(y=\phi_x^{-1}(z)\).  The manifold derivative of \(\phi_x^{-1}\) at \(z\)
  is the tangent coordinate change from the chart centered at \(x\) to the
  chart centered at \(y\).
proof:
  The inverse chart is differentiable on its target.  Expressing its
  manifold derivative in extended charts reduces directly to the derivative
  defining the tangent coordinate change.
-/
theorem mfderivWithin_extChartAt_symm_eq_tangentCoordChange_surface
    (x : X) (z : ℂ)
    (hz : z ∈ (extChartAt SurfaceRealModel x).target) :
    mfderivWithin 𝓘(ℝ, ℂ) SurfaceRealModel
        (extChartAt SurfaceRealModel x).symm (range 𝓘(ℝ, ℂ)) z =
      tangentCoordChange SurfaceRealModel x
        ((extChartAt SurfaceRealModel x).symm z)
        ((extChartAt SurfaceRealModel x).symm z) := by
  have hmd := mdifferentiableWithinAt_extChartAt_symm
    (I := SurfaceRealModel) hz
  have hz_eq : (chartAt ℂ x) ((chartAt ℂ x).symm z) = z := by
    simpa [SurfaceRealModel] using
      (extChartAt SurfaceRealModel x).right_inv hz
  rw [hmd.mfderivWithin, tangentCoordChange_def]
  simp [writtenInExtChartAt, SurfaceRealModel, Function.comp_def, hz_eq]

/--
%%handwave
name:
  Coordinate integral curves give manifold integral curves
statement:
  Fix a surface chart \(\phi\) and write the transverse field \(V\) in this
  chart as \(v\).  If a differentiable curve \(z(t)\) remains in the chart
  target and satisfies
  \[
    z'(t)=v(z(t)),
  \]
  then \(\gamma(t)=\phi^{-1}(z(t))\) has manifold derivative
  \[
    \gamma'(t)=V_{\gamma(t)}.
  \]
proof:
  Apply the manifold chain rule to \(\phi^{-1}\circ z\).  The derivative of
  the inverse chart is the tangent-coordinate change back to the moving
  point, which cancels the coordinate change used to define \(v\).
-/
theorem hasMFDerivAt_extChartAt_symm_of_hasDerivAt_smoothFrontierCoordinateVectorField
    (D : SmoothBoundaryDomain X) (x : X) (z : ℝ → ℂ) (t : ℝ)
    (hz : z t ∈ (extChartAt SurfaceRealModel x).target)
    (hode : HasDerivAt z
      (smoothFrontierCoordinateVectorField D x (z t)) t) :
    HasMFDerivAt 𝓘(ℝ) SurfaceRealModel
      (fun s => (extChartAt SurfaceRealModel x).symm (z s)) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (smoothFrontierTransverseVectorField D
          ((extChartAt SurfaceRealModel x).symm (z t)))) := by
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
        (smoothFrontierCoordinateVectorField D x (z t))) :=
    hode.hasFDerivAt.hasMFDerivAt
  have hcomp := hsymm.comp t hzM
  apply hcomp.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro a
  change ℝ at a
  change mfderivWithin 𝓘(ℝ, ℂ) SurfaceRealModel
      (extChartAt SurfaceRealModel x).symm (range 𝓘(ℝ, ℂ)) (z t)
        (a • smoothFrontierCoordinateVectorField D x (z t)) =
      a • smoothFrontierTransverseVectorField D
        ((extChartAt SurfaceRealModel x).symm (z t))
  rw [mfderivWithin_extChartAt_symm_eq_tangentCoordChange_surface x (z t) hz]
  have hmap := (tangentCoordChange SurfaceRealModel x y y).map_smul a
    (smoothFrontierCoordinateVectorField D x (z t))
  have hcoord : smoothFrontierCoordinateVectorField D x (z t) =
      tangentCoordChange SurfaceRealModel y x y
        (smoothFrontierTransverseVectorField D y) :=
    smoothFrontierCoordinateVectorField_eq_tangentCoordChange D x (z t)
  have hbase : tangentCoordChange SurfaceRealModel x y y
      (smoothFrontierCoordinateVectorField D x (z t)) =
      smoothFrontierTransverseVectorField D y := by
    rw [hcoord]
    rw [tangentCoordChange_comp (h := ⟨⟨mem_extChartAt_source y,
      (extChartAt SurfaceRealModel x).map_target hz⟩,
      mem_extChartAt_source y⟩)]
    rw [tangentCoordChange_self (mem_extChartAt_source y)]
  calc
    _ = a • tangentCoordChange SurfaceRealModel x y y
        (smoothFrontierCoordinateVectorField D x (z t)) := hmap
    _ = a • smoothFrontierTransverseVectorField D y := congrArg (a • ·) hbase
    _ = _ := rfl

/--
%%handwave
name:
  Derivative of the signed coordinate in a centered chart
statement:
  Let \(s:X\to\mathbb R\) be the global signed boundary coordinate.  For
  every \(x\in X\) and \(v\in\mathbb C\),
  \[
    D(s\circ\phi_x^{-1})_{\phi_x(x)}(v)=ds_x(v),
  \]
  where the centered chart identifies the model vector \(v\) with a tangent
  vector at \(x\).
proof:
  Smoothness of \(s\) gives its manifold derivative at \(x\).  Unfolding
  that derivative in the centered extended chart yields precisely the
  ordinary derivative of \(s\circ\phi_x^{-1}\).
-/
theorem fderiv_smoothBoundaryGlobalSignedCoordinate_comp_extChartAt_symm
    (D : SmoothBoundaryDomain X) (x : X) (v : ℂ) :
    fderiv ℝ
        (fun z : ℂ => smoothBoundaryGlobalSignedCoordinate D
          ((extChartAt SurfaceRealModel x).symm z))
        (extChartAt SurfaceRealModel x x) v =
      mfderiv SurfaceRealModel 𝓘(ℝ)
        (smoothBoundaryGlobalSignedCoordinate D) x v := by
  have hd : MDifferentiableAt SurfaceRealModel 𝓘(ℝ)
      (smoothBoundaryGlobalSignedCoordinate D) x :=
    (smoothBoundaryGlobalSignedCoordinate_contMDiff D).contMDiffAt
      |>.mdifferentiableAt (by norm_num)
  rw [mfderiv, if_pos hd]
  simp [writtenInExtChartAt, SurfaceRealModel, Function.comp_def]
  rfl

/--
%%handwave
name:
  Smoothness of the transverse field in a fixed chart
statement:
  For a fixed surface chart \(\phi\), the coordinate expression
  \[
    z\longmapsto d\phi_{\phi^{-1}(z)}
      \bigl(V_{\phi^{-1}(z)}\bigr)
  \]
  is smooth throughout the target of \(\phi\).
proof:
  Compose the smooth tangent-bundle section \(x\mapsto(x,V_x)\) with the
  smooth tangent trivialization over the chart and with the smooth inverse
  chart.  Taking the fiber coordinate preserves smoothness.
-/
theorem smoothFrontierCoordinateVectorField_contDiffOn
    (D : SmoothBoundaryDomain X) (x : X) :
    ContDiffOn ℝ ∞ (smoothFrontierCoordinateVectorField D x)
      (extChartAt SurfaceRealModel x).target := by
  let e := trivializationAt ℂ (TangentSpace SurfaceRealModel) x
  let s : X → TangentBundle SurfaceRealModel X := fun y =>
    ⟨y, smoothFrontierTransverseVectorField D y⟩
  have hs : ContMDiffOn SurfaceRealModel SurfaceRealModel.tangent ∞ s e.baseSet :=
    (smoothFrontierTransverseVectorField_contMDiff D).contMDiffOn
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
  simpa [smoothFrontierCoordinateVectorField, e, s, Function.comp_def] using
    hcomp.contDiffOn

/--
%%handwave
name:
  Global smooth extension of a local coordinate vector field
statement:
  For every \(x\in X\), the coordinate expression of the transverse field in
  the chart centered at \(x\) agrees near \(\phi_x(x)\) with some globally
  smooth map \(f:\mathbb C\to\mathbb C\).
proof:
  The coordinate field is smooth on the open chart target containing
  \(\phi_x(x)\).  A smooth extension lemma produces a global Euclidean map
  equal to it on a smaller neighborhood of that point.
-/
theorem exists_contDiff_smoothFrontierCoordinateVectorField_eventuallyEq
    (D : SmoothBoundaryDomain X) (x : X) :
    ∃ f : ℂ → ℂ, ContDiff ℝ ∞ f ∧
      f =ᶠ[𝓝 (extChartAt SurfaceRealModel x x)]
        smoothFrontierCoordinateVectorField D x := by
  apply JJMath.Manifold.exists_contDiff_eventuallyEq_of_contDiffOn
    (U := (extChartAt SurfaceRealModel x).target)
  · exact isOpen_extChartAt_target x
  · exact mem_extChartAt_target x
  · exact smoothFrontierCoordinateVectorField_contDiffOn D x

/--
%%handwave
name:
  A jointly smooth coordinate flow near every point
statement:
  For every \(x\in X\), there are a globally smooth
  \(f:\mathbb C\to\mathbb C\), equal near \(z_0=\phi_x(x)\) to the
  coordinate expression of the transverse field, a number
  \(\varepsilon>0\), and curves \(\psi_y\) for \(y\) near \(z_0\) such that
  \[
    \psi_y(0)=y,\qquad
    \psi_y(t)=y+\int_0^t f(\psi_y(r))\,dr,
  \]
  and \((y,t)\mapsto\psi_y(t)\) is smooth for \(|t|<\varepsilon\).
proof:
  Extend the coordinate field to a global smooth Euclidean field and apply
  local existence with joint smooth dependence on initial value and time at
  the chart center.
-/
theorem exists_smoothFrontierCoordinateLocalFlow
    (D : SmoothBoundaryDomain X) (x : X) :
    ∃ f : ℂ → ℂ, ∃ hf : ContDiff ℝ ∞ f,
      f =ᶠ[𝓝 (extChartAt SurfaceRealModel x x)]
        smoothFrontierCoordinateVectorField D x ∧
      ∃ ε : ℝ, ∃ hε : 0 < ε, ∃ ψ : ℂ → LocalCurve ℂ ε,
        ψ (extChartAt SurfaceRealModel x x)
            ⟨0, by constructor <;> linarith [hε]⟩ =
          extChartAt SurfaceRealModel x x ∧
        (∀ᶠ y in 𝓝 (extChartAt SurfaceRealModel x x),
          ψ y ⟨0, by constructor <;> linarith [hε]⟩ = y) ∧
        (∀ᶠ y in 𝓝 (extChartAt SurfaceRealModel x x),
          ψ y = ContinuousMap.const (Icc (-ε) ε) y +
            localCurveIntegral ε hε.le
              (superposition f hf.continuous (ψ y))) ∧
        ∀ᶠ y in 𝓝 (extChartAt SurfaceRealModel x x),
          ∀ t₀ ∈ Ioo (-ε) ε,
            ContDiffAt ℝ ∞
              (fun p : ℂ × ℝ =>
                extendLocalCurve ε hε.le (ψ p.1) p.2)
              (y, t₀) := by
  rcases exists_contDiff_smoothFrontierCoordinateVectorField_eventuallyEq D x with
    ⟨f, hf, hfeq⟩
  rcases exists_jointlySmooth_localFlow f hf
      (extChartAt SurfaceRealModel x x) with
    ⟨ε, hε, ψ, hψ0, hinitψ, hfixedψ, hsmoothψ⟩
  exact ⟨f, hf, hfeq, ε, hε, ψ, hψ0, hinitψ, hfixedψ, hsmoothψ⟩

/--
%%handwave
name:
  Initial derivative of the coordinate flow
statement:
  The coordinate flow above may be chosen so that, for
  \(F(y,t)=\psi_y(t)\),
  \[
    DF_{(z_0,0)}(v,a)=v+a f(z_0)
    \qquad(v\in\mathbb C,\ a\in\mathbb R).
  \]
proof:
  Take the jointly smooth Picard family.  Its initial-value slice is the
  identity and its time slice solves \(z'=f(z)\), so the derivative formula
  follows from the corresponding two directional derivatives and linearity.
-/
theorem exists_smoothFrontierCoordinateLocalFlow_with_fderiv
    (D : SmoothBoundaryDomain X) (x : X) :
    ∃ f : ℂ → ℂ, ∃ hf : ContDiff ℝ ∞ f,
      f =ᶠ[𝓝 (extChartAt SurfaceRealModel x x)]
        smoothFrontierCoordinateVectorField D x ∧
      ∃ ε : ℝ, ∃ hε : 0 < ε, ∃ ψ : ℂ → LocalCurve ℂ ε,
        ψ (extChartAt SurfaceRealModel x x)
            ⟨0, by constructor <;> linarith [hε]⟩ =
          extChartAt SurfaceRealModel x x ∧
        (∀ᶠ y in 𝓝 (extChartAt SurfaceRealModel x x),
          ψ y ⟨0, by constructor <;> linarith [hε]⟩ = y) ∧
        (∀ᶠ y in 𝓝 (extChartAt SurfaceRealModel x x),
          ψ y = ContinuousMap.const (Icc (-ε) ε) y +
            localCurveIntegral ε hε.le
              (superposition f hf.continuous (ψ y))) ∧
        (∀ᶠ y in 𝓝 (extChartAt SurfaceRealModel x x),
          ∀ t₀ ∈ Ioo (-ε) ε,
            ContDiffAt ℝ ∞
              (fun p : ℂ × ℝ =>
                extendLocalCurve ε hε.le (ψ p.1) p.2)
              (y, t₀)) ∧
        ∀ v : ℂ, ∀ a : ℝ,
          fderiv ℝ
              (fun p : ℂ × ℝ =>
                extendLocalCurve ε hε.le (ψ p.1) p.2)
              (extChartAt SurfaceRealModel x x, 0) (v, a) =
            v + a • f (extChartAt SurfaceRealModel x x) := by
  rcases exists_smoothFrontierCoordinateLocalFlow D x with
    ⟨f, hf, hfeq, ε, hε, ψ, hψ0, hinitψ, hfixedψ, hsmoothψ⟩
  refine ⟨f, hf, hfeq, ε, hε, ψ, hψ0, hinitψ, hfixedψ,
    hsmoothψ, ?_⟩
  intro v a
  exact fderiv_uncurry_extendLocalCurve_apply_zero ε hε.le f hf
    (extChartAt SurfaceRealModel x x) ψ hε hinitψ hfixedψ
    ((mem_of_mem_nhds hsmoothψ) 0 (by constructor <;> linarith [hε])) v a

/--
%%handwave
name:
  The coordinate flow solves the original field equation near the center
statement:
  The coordinate flow can be chosen with a neighborhood of \((z_0,0)\) on
  which \(F(y,t)=\psi_y(t)\) remains in the chart target and satisfies
  \[
    \frac{d}{dt}F(y,t)=v_x(F(y,t)),
  \]
  where \(v_x\) is the coordinate expression of the original transverse
  field; it also retains the initial derivative
  \(DF_{(z_0,0)}(v,a)=v+a f(z_0)\).
proof:
  Continuity keeps the flow in the chart target after shrinking around
  \((z_0,0)\).  On a possibly smaller neighborhood the global extension
  \(f\) equals the original coordinate field, and differentiating the Picard
  equation gives the asserted ordinary differential equation.
-/
theorem exists_smoothFrontierCoordinateLocalFlow_with_fderiv_and_ode
    (D : SmoothBoundaryDomain X) (x : X) :
    ∃ f : ℂ → ℂ, ∃ hf : ContDiff ℝ ∞ f,
      f =ᶠ[𝓝 (extChartAt SurfaceRealModel x x)]
        smoothFrontierCoordinateVectorField D x ∧
      ∃ ε : ℝ, ∃ hε : 0 < ε, ∃ ψ : ℂ → LocalCurve ℂ ε,
        ψ (extChartAt SurfaceRealModel x x)
            ⟨0, by constructor <;> linarith [hε]⟩ =
          extChartAt SurfaceRealModel x x ∧
        (∀ᶠ y in 𝓝 (extChartAt SurfaceRealModel x x),
          ψ y ⟨0, by constructor <;> linarith [hε]⟩ = y) ∧
        (∀ᶠ y in 𝓝 (extChartAt SurfaceRealModel x x),
          ψ y = ContinuousMap.const (Icc (-ε) ε) y +
            localCurveIntegral ε hε.le
              (superposition f hf.continuous (ψ y))) ∧
        (∀ᶠ y in 𝓝 (extChartAt SurfaceRealModel x x),
          ∀ t₀ ∈ Ioo (-ε) ε,
            ContDiffAt ℝ ∞
              (fun p : ℂ × ℝ =>
                extendLocalCurve ε hε.le (ψ p.1) p.2)
              (y, t₀)) ∧
        (∀ v : ℂ, ∀ a : ℝ,
          fderiv ℝ
              (fun p : ℂ × ℝ =>
                extendLocalCurve ε hε.le (ψ p.1) p.2)
              (extChartAt SurfaceRealModel x x, 0) (v, a) =
            v + a • f (extChartAt SurfaceRealModel x x)) ∧
        ∀ᶠ p : ℂ × ℝ in 𝓝 (extChartAt SurfaceRealModel x x, 0),
          extendLocalCurve ε hε.le (ψ p.1) p.2 ∈
              (extChartAt SurfaceRealModel x).target ∧
            HasDerivAt
              (fun t : ℝ => extendLocalCurve ε hε.le (ψ p.1) t)
              (smoothFrontierCoordinateVectorField D x
                (extendLocalCurve ε hε.le (ψ p.1) p.2)) p.2 := by
  rcases exists_smoothFrontierCoordinateLocalFlow_with_fderiv D x with
    ⟨f, hf, hfeq, ε, hε, ψ, hψ0, hinit, hfixed, hsmooth, hflowDeriv⟩
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
  have hFtend : Tendsto F (𝓝 (z₀, 0)) (𝓝 z₀) := by
    have hcont := hFsmooth.continuousAt
    rw [continuousAt_def, hF0] at hcont
    exact hcont
  have hfirst : Tendsto (fun p : ℂ × ℝ => p.1)
      (𝓝 (z₀, 0)) (𝓝 z₀) := continuousAt_fst
  have hsecond : Tendsto (fun p : ℂ × ℝ => p.2)
      (𝓝 (z₀, 0)) (𝓝 (0 : ℝ)) := continuousAt_snd
  have hfixed' : ∀ᶠ p : ℂ × ℝ in 𝓝 (z₀, 0),
      ψ p.1 = ContinuousMap.const (Icc (-ε) ε) p.1 +
        localCurveIntegral ε hε.le
          (superposition f hf.continuous (ψ p.1)) := hfirst.eventually hfixed
  have htime : ∀ᶠ p : ℂ × ℝ in 𝓝 (z₀, 0), p.2 ∈ Ioo (-ε) ε :=
    hsecond.eventually (Ioo_mem_nhds (by linarith [hε]) (by linarith [hε]))
  have htarget : ∀ᶠ p : ℂ × ℝ in 𝓝 (z₀, 0),
      F p ∈ (extChartAt SurfaceRealModel x).target :=
    hFtend.eventually (isOpen_extChartAt_target x |>.mem_nhds
      (mem_extChartAt_target x))
  have hfield : ∀ᶠ p : ℂ × ℝ in 𝓝 (z₀, 0),
      f (F p) = smoothFrontierCoordinateVectorField D x (F p) :=
    hFtend.eventually hfeq
  refine ⟨f, hf, hfeq, ε, hε, ψ, hψ0, hinit, hfixed, hsmooth,
    hflowDeriv, ?_⟩
  filter_upwards [hfixed', htime, htarget, hfield] with p hpfix hpt hptarget hpfield
  refine ⟨hptarget, ?_⟩
  rw [← hpfield]
  exact hasDerivAt_extendLocalCurve_of_picardFixedPoint
    ε hε.le f hf.continuous p.1 (ψ p.1) hpfix hpt
/--
%%handwave
name:
  Positivity of the chosen transverse field
statement:
  For the fixed transverse field \(V\) and every \(x\in\partial D\),
  \[
    ds_x(V_x)>0,
  \]
  where \(s\) is the global signed boundary coordinate.
proof:
  The fixed field was selected from the existence theorem together with this
  pointwise positivity property.
-/
theorem smoothFrontierTransverseVectorField_mfderiv_pos
    (D : SmoothBoundaryDomain X) {x : X}
    (hx : x ∈ frontier D.carrier) :
    0 < (show ℝ from mfderiv SurfaceRealModel 𝓘(ℝ)
      (smoothBoundaryGlobalSignedCoordinate D) x
      (smoothFrontierTransverseVectorField D x)) :=
  (Classical.choose_spec (exists_smoothFrontierTransverseVectorField D)).2 x hx

/--
%%handwave
name:
  Positive coordinate derivative in the transverse direction
statement:
  For \(x\in\partial D\), let \(v_x\) be the coordinate expression of the
  chosen transverse field in the chart centered at \(x\).  Then
  \[
    D(s\circ\phi_x^{-1})_{\phi_x(x)}
      \bigl(v_x(\phi_x(x))\bigr)>0.
  \]
proof:
  At the chart center, the coordinate field represents \(V_x\), and the
  coordinate derivative of \(s\) is \(ds_x\).  The result is therefore the
  defining inequality \(ds_x(V_x)>0\).
-/
theorem fderiv_smoothBoundaryGlobalSignedCoordinate_comp_extChartAt_symm_pos
    (D : SmoothBoundaryDomain X) (x : frontier D.carrier) :
    0 < fderiv ℝ
        (fun z : ℂ => smoothBoundaryGlobalSignedCoordinate D
          ((extChartAt SurfaceRealModel (x : X)).symm z))
        (extChartAt SurfaceRealModel (x : X) x)
        (smoothFrontierCoordinateVectorField D x
          (extChartAt SurfaceRealModel (x : X) x)) := by
  rw [smoothFrontierCoordinateVectorField_apply_center]
  rw [fderiv_smoothBoundaryGlobalSignedCoordinate_comp_extChartAt_symm]
  exact smoothFrontierTransverseVectorField_mfderiv_pos D x.2

/-- The derivative of the signed boundary coordinate in the direction of the
chosen smooth transverse field. -/
noncomputable def smoothFrontierTransverseDerivative
    (D : SmoothBoundaryDomain X) (x : X) : ℝ :=
  tangentMap SurfaceRealModel 𝓘(ℝ)
    (smoothBoundaryGlobalSignedCoordinate D)
    (⟨x, smoothFrontierTransverseVectorField D x⟩ :
      TangentBundle SurfaceRealModel X) |>.2

/--
%%handwave
name:
  Smoothness of the transverse derivative
statement:
  The function
  \[
    x\longmapsto ds_x(V_x)
  \]
  is continuously differentiable on \(X\).
proof:
  The signed coordinate is twice continuously differentiable, so its tangent
  map is continuously differentiable.  Compose this tangent map with the
  smooth tangent-bundle section \(x\mapsto(x,V_x)\), then project to its
  scalar fiber coordinate.
-/
theorem smoothFrontierTransverseDerivative_contMDiff
    (D : SmoothBoundaryDomain X) :
    ContMDiff SurfaceRealModel 𝓘(ℝ) 1
      (smoothFrontierTransverseDerivative D) := by
  have hh : ContMDiff SurfaceRealModel 𝓘(ℝ) 2
      (smoothBoundaryGlobalSignedCoordinate D) :=
    (smoothBoundaryGlobalSignedCoordinate_contMDiff D).of_le
      (by exact WithTop.coe_le_coe.mpr le_top)
  have htan : ContMDiff SurfaceRealModel.tangent 𝓘(ℝ).tangent 1
      (tangentMap SurfaceRealModel 𝓘(ℝ)
        (smoothBoundaryGlobalSignedCoordinate D)) :=
    hh.contMDiff_tangentMap (by norm_num)
  have hsection : ContMDiff SurfaceRealModel SurfaceRealModel.tangent 1
      (fun x => (⟨x, smoothFrontierTransverseVectorField D x⟩ :
        TangentBundle SurfaceRealModel X)) :=
    (smoothFrontierTransverseVectorField_contMDiff D).of_le (by norm_num)
  exact (contMDiff_snd_tangentBundle_modelSpace ℝ 𝓘(ℝ)).comp
    (htan.comp hsection)

/--
%%handwave
name:
  Evaluation formula for the transverse derivative
statement:
  For every \(x\in X\), the transverse derivative is
  \[
    \delta_D(x)=ds_x(V_x).
  \]
proof:
  The second component of the tangent map of \(s\) at \((x,V_x)\) is, by
  definition, the manifold derivative \(ds_x\) applied to \(V_x\).
-/
@[simp]
theorem smoothFrontierTransverseDerivative_apply
    (D : SmoothBoundaryDomain X) (x : X) :
    smoothFrontierTransverseDerivative D x =
      (show ℝ from mfderiv SurfaceRealModel 𝓘(ℝ)
        (smoothBoundaryGlobalSignedCoordinate D) x
        (smoothFrontierTransverseVectorField D x)) := by
  simp [smoothFrontierTransverseDerivative]

/--
%%handwave
name:
  Uniform positive lower bound for the transverse derivative
statement:
  If \(\partial D\) is nonempty, there is a constant \(c>0\) such that
  \[
    c\le ds_x(V_x)\qquad\text{for every }x\in\partial D.
  \]
proof:
  The continuous function \(x\mapsto ds_x(V_x)\) attains its minimum on the
  compact frontier.  Pointwise transversality makes that minimum positive;
  half of it is a positive uniform lower bound.
-/
theorem exists_uniform_smoothFrontierTransverseDerivative_pos
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) :
    ∃ c : ℝ, 0 < c ∧
      ∀ x ∈ frontier D.carrier,
        c ≤ smoothFrontierTransverseDerivative D x := by
  have hcompact : IsCompact (frontier D.carrier) :=
    D.compact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hcontinuous : Continuous (smoothFrontierTransverseDerivative D) :=
    (smoothFrontierTransverseDerivative_contMDiff D).continuous
  obtain ⟨x, hx, hxmin⟩ := hcompact.exists_isMinOn
    ⟨(p : X), p.2⟩ hcontinuous.continuousOn
  have hxpos : 0 < smoothFrontierTransverseDerivative D x := by
    rw [smoothFrontierTransverseDerivative_apply]
    exact smoothFrontierTransverseVectorField_mfderiv_pos D hx
  refine ⟨smoothFrontierTransverseDerivative D x / 2, half_pos hxpos, ?_⟩
  intro y hy
  exact (half_le_self hxpos.le).trans (hxmin hy)

/--
%%handwave
name:
  Uniform transversality near the entire frontier
statement:
  If \(\partial D\neq\varnothing\), there are \(c>0\) and an open set
  \(U\supseteq\partial D\) such that
  \[
    ds_x(V_x)>c\qquad(x\in U).
  \]
proof:
  The continuous function \(x\mapsto ds_x(V_x)\) is positive on the compact
  frontier, hence has a positive lower bound there.  Taking half that bound,
  its strict superlevel set is an open neighborhood of the frontier with the
  required uniform inequality.
-/
theorem exists_open_smoothFrontierTransverseDerivative_uniformly_pos
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) :
    ∃ c : ℝ, 0 < c ∧
      ∃ U : Set X, IsOpen U ∧ frontier D.carrier ⊆ U ∧
        ∀ x ∈ U, c < smoothFrontierTransverseDerivative D x := by
  rcases exists_uniform_smoothFrontierTransverseDerivative_pos D p with
    ⟨c, hc, hfrontier⟩
  let d : ℝ := c / 2
  let U : Set X := {x | d < smoothFrontierTransverseDerivative D x}
  have hUopen : IsOpen U :=
    isOpen_lt continuous_const
      (smoothFrontierTransverseDerivative_contMDiff D).continuous
  refine ⟨d, half_pos hc, U, hUopen, ?_, ?_⟩
  · intro x hx
    exact (half_lt_self hc).trans_le (hfrontier x hx)
  · intro x hx
    exact hx

/--
%%handwave
name:
  Local transverse integral curve through a frontier point
statement:
  For every \(x\in\partial D\), there is a curve
  \(\gamma:\mathbb R\to X\) with \(\gamma(0)=x\) which is an integral curve
  of the chosen transverse field \(V\) at time \(0\).
proof:
  The vector field is continuously differentiable near \(x\).  Local
  existence for integral curves of a smooth vector field on a boundaryless
  manifold supplies the required curve through \(x\).
-/
theorem exists_smoothFrontierTransverseIntegralCurveAt
    (D : SmoothBoundaryDomain X) (x : frontier D.carrier) :
    ∃ gamma : ℝ → X, gamma 0 = x ∧
      IsMIntegralCurveAt gamma (smoothFrontierTransverseVectorField D) 0 := by
  have hV : ContMDiffAt SurfaceRealModel SurfaceRealModel.tangent 1
      (fun y => (⟨y, smoothFrontierTransverseVectorField D y⟩ :
        TangentBundle SurfaceRealModel X)) (x : X) :=
    (smoothFrontierTransverseVectorField_contMDiff D).contMDiffAt.of_le (by norm_num)
  exact exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless 0 hV

/--
%%handwave
name:
  Derivative of the signed coordinate along a transverse integral curve
statement:
  Let \(\gamma\) be an integral curve of \(V\) at time \(t\).  Then
  \[
    \frac{d}{du}\Big|_{u=t}s(\gamma(u))
      =ds_{\gamma(t)}(V_{\gamma(t)}).
  \]
proof:
  Apply the manifold chain rule to \(s\circ\gamma\).  The derivative of the
  integral curve at \(t\) is \(V_{\gamma(t)}\), so evaluating \(ds\) on it
  gives the stated ordinary derivative.
-/
theorem smoothBoundaryGlobalSignedCoordinate_deriv_along_transverseIntegralCurve
    (D : SmoothBoundaryDomain X) {gamma : ℝ → X} {t : ℝ}
    (hgamma : IsMIntegralCurveAt gamma
      (smoothFrontierTransverseVectorField D) t) :
    deriv (fun s : ℝ =>
      smoothBoundaryGlobalSignedCoordinate D (gamma s)) t =
      smoothFrontierTransverseDerivative D (gamma t) := by
  let h : X → ℝ := smoothBoundaryGlobalSignedCoordinate D
  let c : ℝ := show ℝ from
    mfderiv SurfaceRealModel 𝓘(ℝ) h (gamma t)
      (smoothFrontierTransverseVectorField D (gamma t))
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
      (smoothFrontierTransverseVectorField D (gamma t))) =
        (show ℝ from mfderiv SurfaceRealModel 𝓘(ℝ) h (gamma t)
          (a • smoothFrontierTransverseVectorField D (gamma t)))
    rw [map_smul]
    rfl
  change deriv (h ∘ gamma) t = _
  rw [hordinary.deriv]
  simp [c, h]

/--
%%handwave
name:
  Positive crossing derivative of a transverse integral curve
statement:
  Suppose \(x\in\partial D\), \(\gamma(0)=x\), and \(\gamma\) is an integral
  curve of \(V\) at time \(0\).  Then
  \[
    \frac{d}{dt}\Big|_{t=0}s(\gamma(t))>0.
  \]
proof:
  The chain rule identifies the derivative with \(ds_x(V_x)\), which is
  strictly positive by transversality along the frontier.
-/
theorem smoothBoundaryGlobalSignedCoordinate_deriv_pos_along_transverseIntegralCurve
    (D : SmoothBoundaryDomain X) {x : X} (hx : x ∈ frontier D.carrier)
    {gamma : ℝ → X} (hgamma0 : gamma 0 = x)
    (hgamma : IsMIntegralCurveAt gamma
      (smoothFrontierTransverseVectorField D) 0) :
    0 < deriv (fun t : ℝ =>
      smoothBoundaryGlobalSignedCoordinate D (gamma t)) 0 := by
  have hx0 : gamma 0 ∈ frontier D.carrier := by
    rw [hgamma0]
    exact hx
  rw [smoothBoundaryGlobalSignedCoordinate_deriv_along_transverseIntegralCurve
    D hgamma, smoothFrontierTransverseDerivative_apply]
  exact smoothFrontierTransverseVectorField_mfderiv_pos D hx0

/--
%%handwave
name:
  A transverse integral curve increases the signed coordinate
statement:
  For every \(x\in\partial D\), there is an integral curve \(\gamma\) of the
  transverse field with \(\gamma(0)=x\) and
  \[
    \frac{d}{dt}\Big|_{t=0}s(\gamma(t))>0.
  \]
proof:
  Take a local integral curve through \(x\).  The chain rule identifies the
  derivative of \(s\circ\gamma\) at zero with \(ds_x(V_x)\), which is
  positive by transversality.
-/
theorem exists_smoothFrontierTransverseIntegralCurveAt_with_deriv_pos
    (D : SmoothBoundaryDomain X) (x : frontier D.carrier) :
    ∃ gamma : ℝ → X,
      gamma 0 = x ∧
      IsMIntegralCurveAt gamma (smoothFrontierTransverseVectorField D) 0 ∧
      0 < deriv (fun t : ℝ =>
        smoothBoundaryGlobalSignedCoordinate D (gamma t)) 0 := by
  rcases exists_smoothFrontierTransverseIntegralCurveAt D x with
    ⟨gamma, hgamma0, hgamma⟩
  exact ⟨gamma, hgamma0, hgamma,
    smoothBoundaryGlobalSignedCoordinate_deriv_pos_along_transverseIntegralCurve
      D x.2 hgamma0 hgamma⟩

/--
%%handwave
name:
  Strict increase along a uniformly transverse integral-curve segment
statement:
  For every \(p\in\partial D\), there are \(c,\varepsilon>0\) and an
  integral curve \(\gamma:(-\varepsilon,\varepsilon)\to X\), with
  \(\gamma(0)=p\), such that
  \[
    (s\circ\gamma)'(t)>c
    \quad\text{for }|t|<\varepsilon,
  \]
  and \(s\circ\gamma\) is strictly increasing on that interval.
proof:
  Choose an open neighborhood on which \(ds(V)>c>0\), and shorten a local
  integral curve through \(p\) so that it remains there.  The chain rule gives
  the derivative bound throughout the interval, and the mean-value theorem
  yields strict monotonicity.
-/
theorem exists_smoothFrontierTransverseIntegralCurveOn_strictMono
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) :
    ∃ c : ℝ, 0 < c ∧
      ∃ epsilon : ℝ, 0 < epsilon ∧
        ∃ gamma : ℝ → X,
          gamma 0 = p ∧
          IsMIntegralCurveOn gamma (smoothFrontierTransverseVectorField D)
            (Ioo (-epsilon) epsilon) ∧
          (∀ t ∈ Ioo (-epsilon) epsilon,
            c < deriv (fun s : ℝ =>
              smoothBoundaryGlobalSignedCoordinate D (gamma s)) t) ∧
          StrictMonoOn (fun t : ℝ =>
            smoothBoundaryGlobalSignedCoordinate D (gamma t))
            (Ioo (-epsilon) epsilon) := by
  rcases exists_open_smoothFrontierTransverseDerivative_uniformly_pos D p with
    ⟨c, hc, U, hUopen, hfrontierU, hUpos⟩
  rcases exists_smoothFrontierTransverseIntegralCurveAt D p with
    ⟨gamma, hgamma0, hgamma⟩
  have hgammaU : ∀ᶠ t in 𝓝 (0 : ℝ), gamma t ∈ U := by
    have hgamma0U : gamma 0 ∈ U := by
      rw [hgamma0]
      exact hfrontierU p.2
    exact hgamma.continuousAt.preimage_mem_nhds
      (hUopen.mem_nhds hgamma0U)
  obtain ⟨epsilon, hepsilon, hball⟩ :=
    Metric.eventually_nhds_iff_ball.mp (hgamma.and hgammaU)
  have hcurve : IsMIntegralCurveOn gamma
      (smoothFrontierTransverseVectorField D) (Ioo (-epsilon) epsilon) := by
    intro t ht
    have htball : t ∈ Metric.ball 0 epsilon := by
      simpa [Real.ball_zero_eq_Ioo] using ht
    exact (hball t htball).1.hasMFDerivWithinAt
  have hstay : ∀ t ∈ Ioo (-epsilon) epsilon, gamma t ∈ U := by
    intro t ht
    have htball : t ∈ Metric.ball 0 epsilon := by
      simpa [Real.ball_zero_eq_Ioo] using ht
    exact (hball t htball).2
  have hderiv : ∀ t ∈ Ioo (-epsilon) epsilon,
      c < deriv (fun s : ℝ =>
        smoothBoundaryGlobalSignedCoordinate D (gamma s)) t := by
    intro t ht
    rw [smoothBoundaryGlobalSignedCoordinate_deriv_along_transverseIntegralCurve
      D (hcurve.isMIntegralCurveAt (isOpen_Ioo.mem_nhds ht))]
    exact hUpos (gamma t) (hstay t ht)
  have hcontinuous : ContinuousOn (fun t : ℝ =>
      smoothBoundaryGlobalSignedCoordinate D (gamma t))
      (Ioo (-epsilon) epsilon) :=
    (smoothBoundaryGlobalSignedCoordinate_contMDiff D).continuous.comp_continuousOn
      hcurve.continuousOn
  have hmono : StrictMonoOn (fun t : ℝ =>
      smoothBoundaryGlobalSignedCoordinate D (gamma t))
      (Ioo (-epsilon) epsilon) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo (-epsilon) epsilon) hcontinuous
    intro t ht
    exact hc.trans (hderiv t (by simpa using ht))
  exact ⟨c, hc, epsilon, hepsilon, gamma, hgamma0, hcurve,
    hderiv, hmono⟩

end

end JJMath.Uniformization
