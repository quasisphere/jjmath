import JJMath.Quasiconformal.CapacityGeometry
import JJMath.Quasiconformal.RiemannSphere
import JJMath.Quasiconformal.SphericalMetric

/-!
# Capacity separation for normalized planar continua

This file isolates the geometric theorem needed to pass from exact round-ring
capacity to equicontinuity of normalized quasiconformal sphere maps.  The
normalization is expressed in the finite chart: one compact continuum joins
the origin to a point a definite Euclidean distance away, while a second
closed continuum contains one and runs to infinity.

The quantitative lower bound is the planar Grötzsch--Loewner theorem.  It is
not a formal consequence of the concentric-ring computation: one must first
compare arbitrary continua with an extremal ring, or prove the corresponding
two-dimensional Loewner estimate by a length--area argument.
-/

namespace JJMath

open Set Filter
open MeasureTheory
open scoped ENNReal Topology

namespace Quasiconformal

noncomputable section

attribute [local instance] finrank_real_complex_fact'

/--
%%handwave
name:
  Real stereographic coordinate
statement:
  This is the canonical real-linear isometric equivalence
  $\iota:\mathbb R\simeq\mathbb R^{\{1\}}$ used as the one-dimensional
  Euclidean target of stereographic projection on a circle.
-/
def realStereographicCoordinate :
    ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).symm |>.trans
    (EuclideanSpace.equiv (Fin 1) ℝ).symm

/--
%%handwave
name:
  Angular--radial coordinate swap
statement:
  This is the real-linear isometric equivalence
  $$
    (t,r)\longmapsto(r,\iota(t))
  $$
  from $\mathbb R\times\mathbb R$ to
  $\mathbb R\times\mathbb R^{\{1\}}$.
-/
def stereographicPolarAngularCoordinates :
    (ℝ × ℝ) ≃L[ℝ] (ℝ × EuclideanSpace ℝ (Fin 1)) :=
  (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ).trans
    ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr
      realStereographicCoordinate)

/--
%%handwave
name:
  Norm of the real stereographic coordinate
statement:
  The canonical identification
  $\iota:\mathbb R\to\mathbb R^1$ used for the angular stereographic
  coordinate is an isometry:
  $$
    \|\iota(t)\|=|t|.
  $$
proof:
  In one-dimensional Euclidean space the $L^2$ norm of the constant
  one-coordinate vector $t$ is $|t|$.
-/
theorem norm_realStereographicCoordinate (t : ℝ) :
    ‖realStereographicCoordinate t‖ = |t| := by
  simp [realStereographicCoordinate, PiLp.norm_toLp_const,
    Real.norm_eq_abs]

/--
%%handwave
name:
  Linearity of the real stereographic coordinate
statement:
  For every $t\in\mathbb R$,
  $$
    \iota(t)=t\,\iota(1).
  $$
proof:
  This is linearity of the canonical identification
  $\mathbb R\cong\mathbb R^1$.
-/
theorem realStereographicCoordinate_eq_smul_one (t : ℝ) :
    realStereographicCoordinate t =
      t • realStereographicCoordinate 1 := by
  rw [← map_smul]
  simp

/--
%%handwave
name:
  Selected unit tangent at a stereographic pole
statement:
  For $v\in S^1$, this is the vector $e_v\in v^\perp$ corresponding to the
  positive unit vector in the canonical one-dimensional Euclidean coordinate
  on $v^\perp$.
-/
def stereographicOrthogonalUnit
    (v : Metric.sphere (0 : ℂ) 1) : ℂ :=
  let U : (ℝ ∙ (v : ℂ))ᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 1) :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton 1
      (ne_zero_of_mem_unit_sphere v)).repr
  ((U.symm (realStereographicCoordinate 1) :
    (ℝ ∙ (v : ℂ))ᗮ) : ℂ)

/--
%%handwave
name:
  The selected stereographic tangent vector has unit norm
statement:
  If $e_v$ is the unit tangent vector selected in $v^\perp$ by the
  one-dimensional stereographic coordinate, then $\|e_v\|=1$.
proof:
  Both the orthonormal coordinate map on $v^\perp$ and the canonical
  identification $\mathbb R\cong\mathbb R^1$ preserve the norm of $1$.
-/
theorem norm_stereographicOrthogonalUnit
    (v : Metric.sphere (0 : ℂ) 1) :
    ‖stereographicOrthogonalUnit v‖ = 1 := by
  let U : (ℝ ∙ (v : ℂ))ᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 1) :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton 1
      (ne_zero_of_mem_unit_sphere v)).repr
  let esub : (ℝ ∙ (v : ℂ))ᗮ :=
    U.symm (realStereographicCoordinate 1)
  have hsub : ‖esub‖ = 1 := by
    rw [U.symm.norm_map]
    have hrealnorm : ∀ s : ℝ,
        ‖realStereographicCoordinate s‖ = |s| :=
      norm_realStereographicCoordinate
    simpa using hrealnorm 1
  change ‖(esub : ℂ)‖ = 1
  simpa only using hsub

/--
%%handwave
name:
  The selected stereographic tangent vector is orthogonal to the pole
statement:
  If $e_v$ is the tangent vector selected in $v^\perp$, then
  $$
    \langle e_v,v\rangle_{\mathbb R}=0.
  $$
proof:
  By construction $e_v$ belongs to the orthogonal complement of the line
  spanned by $v$.
-/
theorem real_inner_stereographicOrthogonalUnit_pole
    (v : Metric.sphere (0 : ℂ) 1) :
    inner ℝ (stereographicOrthogonalUnit v) (v : ℂ) = 0 := by
  let U : (ℝ ∙ (v : ℂ))ᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 1) :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton 1
      (ne_zero_of_mem_unit_sphere v)).repr
  let esub : (ℝ ∙ (v : ℂ))ᗮ :=
    U.symm (realStereographicCoordinate 1)
  have hve :
      inner ℝ (v : ℂ) (esub : ℂ) = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp esub.2
  rw [real_inner_comm]
  simpa [stereographicOrthogonalUnit, U, esub] using hve

/--
%%handwave
name:
  Inverse-stereographic unit-circle parametrization
statement:
  For $v\in S^1$ and $t\in\mathbb R$, this is
  $$
    \sigma_v(t)=\operatorname{stereo}_{v}^{-1}(\iota(t))\in S^1,
  $$
  regarded as a point of $\mathbb C$.
-/
def stereographicUnitCircleParam
    (v : Metric.sphere (0 : ℂ) 1) (t : ℝ) : ℂ :=
  (((stereographic' 1 v).symm (realStereographicCoordinate t) :
    Metric.sphere (0 : ℂ) 1) : ℂ)

/--
%%handwave
name:
  Explicit inverse-stereographic parametrization of the unit circle
statement:
  Let $v\in S^1$ and let $e_v\in v^\perp$ be the selected unit tangent
  vector.  The inverse-stereographic parametrization is
  $$
    \sigma_v(t)
      =\frac{4t}{t^2+4}\,e_v
        +\frac{t^2-4}{t^2+4}\,v.
  $$
proof:
  Substitute $\iota(t)=t\iota(1)$ into the standard inverse-stereographic
  formula.  The orthonormal coordinate map sends $\iota(t)$ to $t e_v$,
  whose squared norm is $t^2$.
-/
theorem stereographicUnitCircleParam_apply_explicit
    (v : Metric.sphere (0 : ℂ) 1) (t : ℝ) :
    stereographicUnitCircleParam v t =
      (4 * t / (t ^ 2 + 4)) • stereographicOrthogonalUnit v +
        ((t ^ 2 - 4) / (t ^ 2 + 4)) • (v : ℂ) := by
  let U : (ℝ ∙ (v : ℂ))ᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 1) :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton 1
      (ne_zero_of_mem_unit_sphere v)).repr
  let e : ℂ := (U.symm (realStereographicCoordinate 1) :
    (ℝ ∙ (v : ℂ))ᗮ)
  rw [stereographicUnitCircleParam, stereographic'_symm_apply]
  dsimp only
  have hcoord :
      (U.symm (realStereographicCoordinate t) :
          (ℝ ∙ (v : ℂ))ᗮ) =
        t • U.symm (realStereographicCoordinate 1) := by
    rw [realStereographicCoordinate_eq_smul_one, map_smul]
  have hnorm :
      ‖(U.symm (realStereographicCoordinate t) :
          (ℝ ∙ (v : ℂ))ᗮ)‖ ^ 2 = t ^ 2 := by
    rw [U.symm.norm_map, norm_realStereographicCoordinate]
    exact sq_abs t
  have hnorm_coe :
      ‖((U.symm (realStereographicCoordinate t) :
          (ℝ ∙ (v : ℂ))ᗮ) : ℂ)‖ ^ 2 = t ^ 2 := by
    have h := hnorm
    rw [Submodule.coe_norm] at h
    exact h
  rw [hnorm_coe, hcoord]
  simp only [Submodule.coe_smul_of_tower]
  change
    (t ^ 2 + 4)⁻¹ • (4 : ℝ) • (t • e) +
        (t ^ 2 + 4)⁻¹ • (t ^ 2 - 4) • (v : ℂ) =
      (4 * t / (t ^ 2 + 4)) • e +
        ((t ^ 2 - 4) / (t ^ 2 + 4)) • (v : ℂ)
  simp only [smul_smul, div_eq_mul_inv]
  module

/--
%%handwave
name:
  The real stereographic line covers the circle away from its pole
statement:
  For $v,\theta\in S^1$, either $\theta=v$, or there is $t\in\mathbb R$
  such that $\sigma_v(t)=\theta$.
proof:
  A point distinct from $v$ lies in the source of stereographic projection.
  Apply the chart, identify its one-dimensional Euclidean coordinate with a
  real number, and use the inverse law for the chart.
-/
theorem eq_pole_or_exists_stereographicUnitCircleParam
    (v θ : Metric.sphere (0 : ℂ) 1) :
    θ = v ∨ ∃ t : ℝ, stereographicUnitCircleParam v t = (θ : ℂ) := by
  by_cases hθ : θ = v
  · exact Or.inl hθ
  right
  let t : ℝ :=
    realStereographicCoordinate.symm ((stereographic' 1 v) θ)
  refine ⟨t, ?_⟩
  rw [stereographicUnitCircleParam]
  have hsource : θ ∈ (stereographic' 1 v).source := by
    simpa [stereographic'_source] using hθ
  have hcoord :
      realStereographicCoordinate t = (stereographic' 1 v) θ := by
    simp [t]
  rw [hcoord]
  exact congrArg Subtype.val ((stereographic' 1 v).left_inv hsource)

/--
%%handwave
name:
  Inverse-stereographic circle coordinates converge to their pole
statement:
  For every $v\in S^1$,
  $$
    \sigma_v(t)\longrightarrow v\qquad(t\to+\infty).
  $$
proof:
  In the [explicit inverse-stereographic formula](lean:JJMath.Quasiconformal.stereographicUnitCircleParam_apply_explicit), divide both rational coefficients by $t^2$.  The coefficient of the tangent vector tends to zero and the coefficient of $v$ tends to one.
-/
theorem tendsto_stereographicUnitCircleParam_atTop
    (v : Metric.sphere (0 : ℂ) 1) :
    Tendsto (stereographicUnitCircleParam v) atTop (𝓝 (v : ℂ)) := by
  have hinv : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero
  have hinv_sq : Tendsto (fun t : ℝ => t⁻¹ ^ 2) atTop (𝓝 0) := by
    simpa using hinv.pow 2
  have hα : Tendsto (fun t : ℝ => 4 * t / (t ^ 2 + 4))
      atTop (𝓝 0) := by
    have hlim : Tendsto
        (fun t : ℝ => (4 * t⁻¹) / (1 + 4 * t⁻¹ ^ 2))
        atTop (𝓝 0) := by
      simpa using
        (((tendsto_const_nhds (x := (4 : ℝ))).mul hinv).div
          ((tendsto_const_nhds (x := (1 : ℝ))).add
            ((tendsto_const_nhds (x := (4 : ℝ))).mul hinv_sq))
          (by norm_num : (1 + 4 * (0 : ℝ)) ≠ 0))
    apply hlim.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    field_simp [ht.ne']
  have hβ : Tendsto (fun t : ℝ => (t ^ 2 - 4) / (t ^ 2 + 4))
      atTop (𝓝 1) := by
    have hlim : Tendsto
        (fun t : ℝ => (1 - 4 * t⁻¹ ^ 2) / (1 + 4 * t⁻¹ ^ 2))
        atTop (𝓝 1) := by
      simpa using
        (((tendsto_const_nhds (x := (1 : ℝ))).sub
            ((tendsto_const_nhds (x := (4 : ℝ))).mul hinv_sq)).div
          ((tendsto_const_nhds (x := (1 : ℝ))).add
            ((tendsto_const_nhds (x := (4 : ℝ))).mul hinv_sq))
          (by norm_num : (1 + 4 * (0 : ℝ)) ≠ 0))
    apply hlim.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    field_simp [ht.ne']
  rw [show stereographicUnitCircleParam v = fun t =>
      (4 * t / (t ^ 2 + 4)) • stereographicOrthogonalUnit v +
        ((t ^ 2 - 4) / (t ^ 2 + 4)) • (v : ℂ) by
    funext t
    exact stereographicUnitCircleParam_apply_explicit v t]
  simpa using (hα.smul_const (stereographicOrthogonalUnit v)).add
    (hβ.smul_const (v : ℂ))

/--
%%handwave
name:
  Stereographic polar curves converge to the omitted radial point
statement:
  For every $v\in S^1$ and $r\in\mathbb R$,
  $$
    \Phi_v(r,\iota(t))\longrightarrow rv\qquad(t\to+\infty).
  $$
proof:
  The polar curve is $r\sigma_v(t)$.  Multiply the [convergence $\sigma_v(t)\to v$](lean:JJMath.Quasiconformal.tendsto_stereographicUnitCircleParam_atTop) by the fixed scalar $r$.
-/
theorem tendsto_stereographicPolarPatchMap_angularCurve_atTop
    (v : Metric.sphere (0 : ℂ) 1) (r : ℝ) :
    Tendsto
      (fun t : ℝ => Uniformization.stereographicPolarPatchMap v
        (stereographicPolarAngularCoordinates (t, r)))
      atTop (𝓝 (r • (v : ℂ))) := by
  have hscale :=
    (tendsto_stereographicUnitCircleParam_atTop v).const_smul r
  simpa [Uniformization.stereographicPolarPatchMap,
    stereographicPolarAngularCoordinates, stereographicUnitCircleParam] using
      hscale

/--
%%handwave
name:
  A uniform angular endpoint bound extends to the stereographic pole
statement:
  Let $u$ be continuous on $B(0,1)$, let $0<r<1$, and suppose that
  $U(t)=u(r\sigma_v(t))$ satisfies
  $$
    |U(s)-U(t)|\leq C\qquad(s\leq t).
  $$
  Then for every $t\in\mathbb R$,
  $$
    |U(t)-u(rv)|\leq C.
  $$
proof:
  Let the second parameter tend to $+\infty$.  The [stereographic polar curve converges to $rv$](lean:JJMath.Quasiconformal.tendsto_stereographicPolarPatchMap_angularCurve_atTop), and continuity of $u$ at the interior point $rv$ passes the endpoint inequality to the limit.
-/
theorem angular_endpoint_bound_pole_of_continuousOn
    (v : Metric.sphere (0 : ℂ) 1)
    {u : ℂ → ℝ} (hu_cont : ContinuousOn u (Metric.ball (0 : ℂ) 1))
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) {C : ℝ≥0∞}
    (hendpoint : ∀ s t : ℝ, s ≤ t →
      ENNReal.ofReal
          ‖u (Uniformization.stereographicPolarPatchMap v
            (stereographicPolarAngularCoordinates (s, r))) -
            u (Uniformization.stereographicPolarPatchMap v
              (stereographicPolarAngularCoordinates (t, r)))‖ ≤ C) :
    ∀ t : ℝ,
      ENNReal.ofReal
          ‖u (Uniformization.stereographicPolarPatchMap v
            (stereographicPolarAngularCoordinates (t, r))) -
            u (r • (v : ℂ))‖ ≤ C := by
  have hrpole : r • (v : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos hr0]
    simpa using hr1
  have hulim : Tendsto
      (fun T : ℝ => u (Uniformization.stereographicPolarPatchMap v
        (stereographicPolarAngularCoordinates (T, r))))
      atTop (𝓝 (u (r • (v : ℂ)))) :=
    (hu_cont.continuousAt (Metric.isOpen_ball.mem_nhds hrpole)).tendsto.comp
      (tendsto_stereographicPolarPatchMap_angularCurve_atTop v r)
  intro t
  have hcont : Continuous (fun y : ℝ => ENNReal.ofReal
      ‖u (Uniformization.stereographicPolarPatchMap v
        (stereographicPolarAngularCoordinates (t, r))) - y‖) := by
    exact ENNReal.continuous_ofReal.comp (by fun_prop)
  have hlim := hcont.continuousAt.tendsto.comp hulim
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop t] with T hT
  exact hendpoint t T hT

/--
%%handwave
name:
  A stereographic endpoint bound controls the whole Euclidean circle
statement:
  Let $u$ be continuous on $B(0,1)$, let $0<r<1$, and suppose that
  $U(t)=u(r\sigma_v(t))$ satisfies
  $$
    |U(s)-U(t)|\leq C\qquad(s\leq t).
  $$
  Then for all $\theta,\eta\in S^1$,
  $$
    |u(r\theta)-u(r\eta)|\leq C.
  $$
proof:
  The [finite endpoint estimate extends to the omitted pole](lean:JJMath.Quasiconformal.angular_endpoint_bound_pole_of_continuousOn).  Represent every non-pole direction by a real stereographic parameter, order the two finite parameters when both directions are non-poles, and use symmetry of distance in the remaining cases.
-/
theorem angular_sphere_bound_of_continuousOn
    (v : Metric.sphere (0 : ℂ) 1)
    {u : ℂ → ℝ} (hu_cont : ContinuousOn u (Metric.ball (0 : ℂ) 1))
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) {C : ℝ≥0∞}
    (hendpoint : ∀ s t : ℝ, s ≤ t →
      ENNReal.ofReal
          ‖u (Uniformization.stereographicPolarPatchMap v
            (stereographicPolarAngularCoordinates (s, r))) -
            u (Uniformization.stereographicPolarPatchMap v
              (stereographicPolarAngularCoordinates (t, r)))‖ ≤ C) :
    ∀ θ η : Metric.sphere (0 : ℂ) 1,
      ENNReal.ofReal ‖u (r • (θ : ℂ)) - u (r • (η : ℂ))‖ ≤ C := by
  have hpole := angular_endpoint_bound_pole_of_continuousOn
    v hu_cont hr0 hr1 hendpoint
  intro θ η
  rcases eq_pole_or_exists_stereographicUnitCircleParam v θ with
      hθ | ⟨s, hs⟩
  · subst θ
    rcases eq_pole_or_exists_stereographicUnitCircleParam v η with
        hη | ⟨t, ht⟩
    · subst η
      simp
    · have h := hpole t
      rw [← ht]
      simpa [Uniformization.stereographicPolarPatchMap,
        stereographicPolarAngularCoordinates, norm_sub_rev] using h
  · rcases eq_pole_or_exists_stereographicUnitCircleParam v η with
      hη | ⟨t, ht⟩
    · subst η
      have h := hpole s
      rw [← hs]
      simpa [Uniformization.stereographicPolarPatchMap,
        stereographicPolarAngularCoordinates] using h
    · rcases le_total s t with hst | hts
      · have h := hendpoint s t hst
        rw [← hs, ← ht]
        simpa [Uniformization.stereographicPolarPatchMap,
          stereographicPolarAngularCoordinates] using h
      · have h := hendpoint t s hts
        rw [← hs, ← ht]
        simpa [Uniformization.stereographicPolarPatchMap,
          stereographicPolarAngularCoordinates, norm_sub_rev] using h

/--
%%handwave
name:
  Velocity of the inverse-stereographic circle parametrization
statement:
  For $v\in S^1$ and the selected $e_v\in v^\perp$, this is the vector
  $$
    \sigma_v'(t)=
      \frac{4(4-t^2)}{(t^2+4)^2}e_v
      +\frac{16t}{(t^2+4)^2}v.
  $$
-/
def stereographicUnitCircleParamDerivative
    (v : Metric.sphere (0 : ℂ) 1) (t : ℝ) : ℂ :=
  (4 * (4 - t ^ 2) / (t ^ 2 + 4) ^ 2) •
      stereographicOrthogonalUnit v +
    (16 * t / (t ^ 2 + 4) ^ 2) • (v : ℂ)

/--
%%handwave
name:
  Derivative of the inverse-stereographic circle parametrization
statement:
  For every $v\in S^1$ and $t\in\mathbb R$,
  $$
    \sigma_v'(t)
      =\frac{4(4-t^2)}{(t^2+4)^2}\,e_v
        +\frac{16t}{(t^2+4)^2}\,v.
  $$
proof:
  Differentiate the two rational coefficients in the explicit
  inverse-stereographic formula.
-/
theorem stereographicUnitCircleParam_hasDerivAt
    (v : Metric.sphere (0 : ℂ) 1) (t : ℝ) :
    HasDerivAt (stereographicUnitCircleParam v)
      (stereographicUnitCircleParamDerivative v t) t := by
  let α : ℝ → ℝ := fun s => 4 * s / (s ^ 2 + 4)
  let β : ℝ → ℝ := fun s => (s ^ 2 - 4) / (s ^ 2 + 4)
  have hden : t ^ 2 + 4 ≠ 0 := by positivity
  have hα : HasDerivAt α
      (4 * (4 - t ^ 2) / (t ^ 2 + 4) ^ 2) t := by
    have hnum : HasDerivAt (fun s : ℝ => 4 * s) 4 t := by
      simpa using (hasDerivAt_id t).const_mul 4
    have hden' : HasDerivAt (fun s : ℝ => s ^ 2 + 4) (2 * t) t := by
      simpa using ((hasDerivAt_id t).pow 2).add_const 4
    convert hnum.div hden' hden using 1
    field_simp [hden]
    ring
  have hβ : HasDerivAt β
      (16 * t / (t ^ 2 + 4) ^ 2) t := by
    have hnum : HasDerivAt (fun s : ℝ => s ^ 2 - 4) (2 * t) t := by
      simpa using ((hasDerivAt_id t).pow 2).sub_const 4
    have hden' : HasDerivAt (fun s : ℝ => s ^ 2 + 4) (2 * t) t := by
      simpa using ((hasDerivAt_id t).pow 2).add_const 4
    convert hnum.div hden' hden using 1
    field_simp [hden]
    ring
  have hfun :
      stereographicUnitCircleParam v =
        fun s => α s • stereographicOrthogonalUnit v +
          β s • (v : ℂ) := by
    funext s
    simpa [α, β] using
      stereographicUnitCircleParam_apply_explicit v s
  rw [hfun]
  exact (hα.smul_const (stereographicOrthogonalUnit v)).add
    (hβ.smul_const (v : ℂ))

/--
%%handwave
name:
  Speed of the inverse-stereographic unit-circle parametrization
statement:
  The speed of the inverse-stereographic parametrization is
  $$
    \|\sigma_v'(t)\|=\frac{4}{t^2+4}.
  $$
proof:
  The vectors $e_v$ and $v$ are orthonormal.  Expanding the squared norm of
  the derivative therefore gives
  $$
    \frac{16(4-t^2)^2+256t^2}{(t^2+4)^4}
      =\frac{16}{(t^2+4)^2}.
  $$
  Both sides of the desired identity are nonnegative.
-/
theorem norm_stereographicUnitCircleParamDerivative
    (v : Metric.sphere (0 : ℂ) 1) (t : ℝ) :
    ‖stereographicUnitCircleParamDerivative v t‖ =
      4 / (t ^ 2 + 4) := by
  let e : ℂ := stereographicOrthogonalUnit v
  let a : ℝ := 4 * (4 - t ^ 2) / (t ^ 2 + 4) ^ 2
  let b : ℝ := 16 * t / (t ^ 2 + 4) ^ 2
  have he_norm : ‖e‖ = 1 := norm_stereographicOrthogonalUnit v
  have hv_norm : ‖(v : ℂ)‖ = 1 :=
    norm_eq_of_mem_sphere v
  have hev : inner ℝ e (v : ℂ) = 0 :=
    real_inner_stereographicOrthogonalUnit_pole v
  have hve : inner ℝ (v : ℂ) e = 0 := by
    rw [real_inner_comm]
    exact hev
  change ‖a • e + b • (v : ℂ)‖ = 4 / (t ^ 2 + 4)
  have hsquares :
      ‖a • e + b • (v : ℂ)‖ ^ 2 =
        (4 / (t ^ 2 + 4)) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    calc
      inner ℝ (a • e + b • (v : ℂ)) (a • e + b • (v : ℂ)) =
          a * a * inner ℝ e e + a * b * inner ℝ e (v : ℂ) +
            (b * a * inner ℝ (v : ℂ) e +
              b * b * inner ℝ (v : ℂ) (v : ℂ)) := by
        simp only [inner_add_left, inner_add_right, real_inner_smul_left,
          real_inner_smul_right]
        ring
      _ = a ^ 2 + b ^ 2 := by
        rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
          he_norm, hv_norm, hev, hve]
        ring
      _ = (4 / (t ^ 2 + 4)) ^ 2 := by
        dsimp [a, b]
        have hden : t ^ 2 + 4 ≠ 0 := by positivity
        field_simp [hden]
        ring
  have hright : 0 ≤ 4 / (t ^ 2 + 4) := by positivity
  have hleft : 0 ≤ ‖a • e + b • (v : ℂ)‖ := norm_nonneg _
  nlinarith

/--
%%handwave
name:
  Norm of the inverse-stereographic circle parametrization
statement:
  For every pole $v\in S^1$ and coordinate $t\in\mathbb R$,
  $$
    \|\sigma_v(t)\|=1.
  $$
proof:
  The inverse-stereographic parametrization takes values in the unit sphere.
-/
theorem norm_stereographicUnitCircleParam
    (v : Metric.sphere (0 : ℂ) 1) (t : ℝ) :
    ‖stereographicUnitCircleParam v t‖ = 1 := by
  exact norm_eq_of_mem_sphere
    ((stereographic' 1 v).symm (realStereographicCoordinate t))

/--
%%handwave
name:
  Orthogonality of stereographic position and velocity
statement:
  For every pole $v\in S^1$ and coordinate $t\in\mathbb R$,
  $$
    \langle\sigma_v'(t),\sigma_v(t)\rangle_{\mathbb R}=0.
  $$
proof:
  Substitute the explicit formulas for $\sigma_v$ and $\sigma_v'$.  Their
  coefficients are taken in the orthonormal pair $(e_v,v)$, and the remaining
  rational expression vanishes identically.
-/
theorem real_inner_stereographicUnitCircleParamDerivative_param
    (v : Metric.sphere (0 : ℂ) 1) (t : ℝ) :
    inner ℝ (stereographicUnitCircleParamDerivative v t)
      (stereographicUnitCircleParam v t) = 0 := by
  let e : ℂ := stereographicOrthogonalUnit v
  let a : ℝ := 4 * (4 - t ^ 2) / (t ^ 2 + 4) ^ 2
  let b : ℝ := 16 * t / (t ^ 2 + 4) ^ 2
  let c : ℝ := 4 * t / (t ^ 2 + 4)
  let d : ℝ := (t ^ 2 - 4) / (t ^ 2 + 4)
  have he_norm : ‖e‖ = 1 := norm_stereographicOrthogonalUnit v
  have hv_norm : ‖(v : ℂ)‖ = 1 := norm_eq_of_mem_sphere v
  have hev : inner ℝ e (v : ℂ) = 0 :=
    real_inner_stereographicOrthogonalUnit_pole v
  have hve : inner ℝ (v : ℂ) e = 0 := by
    rw [real_inner_comm]
    exact hev
  rw [stereographicUnitCircleParam_apply_explicit]
  change inner ℝ (a • e + b • (v : ℂ))
    (c • e + d • (v : ℂ)) = 0
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right]
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    he_norm, hv_norm, hev, hve]
  dsimp [a, b, c, d]
  have hden : t ^ 2 + 4 ≠ 0 := by positivity
  field_simp [hden]
  ring

/--
%%handwave
name:
  Angular derivative of a stereographic polar curve
statement:
  Let $\Phi_v$ be the stereographic polar patch and let
  $C(t,r)=(r,\iota(t))$.  For fixed $r$, the curve
  $t\mapsto\Phi_v(C(t,r))$ has derivative
  $$
    \frac{d}{dt}\Phi_v(C(t,r))=r\,\sigma_v'(t).
  $$
proof:
  The curve is exactly $t\mapsto r\,\sigma_v(t)$, so the result follows by
  multiplying [the derivative of the inverse-stereographic circle
  parametrization](lean:JJMath.Quasiconformal.stereographicUnitCircleParam_hasDerivAt)
  by the constant $r$.
-/
theorem stereographicPolarPatchMap_angularCurve_hasDerivAt
    (v : Metric.sphere (0 : ℂ) 1) (r t : ℝ) :
    HasDerivAt
      (fun s : ℝ =>
        Uniformization.stereographicPolarPatchMap v
          (stereographicPolarAngularCoordinates (s, r)))
      (r • stereographicUnitCircleParamDerivative v t) t := by
  change HasDerivAt
    (fun s : ℝ => r • stereographicUnitCircleParam v s)
    (r • stereographicUnitCircleParamDerivative v t) t
  exact (stereographicUnitCircleParam_hasDerivAt v t).const_smul r

/--
%%handwave
name:
  Angular coordinate vector of the stereographic polar differential
statement:
  Let $\Phi_v$ be the stereographic polar patch and
  $C(t,r)=(r,\iota(t))$.  Then
  $$
    \bigl(D\Phi_v(C(t,r))\circ C\bigr)(1,0)
      =r\,\sigma_v'(t).
  $$
proof:
  [The polar patch is smooth](lean:JJMath.Uniformization.contDiff_stereographicPolarPatchMap),
  so the chain rule identifies the left side with the derivative of
  $s\mapsto\Phi_v(C(s,r))$ at $t$.  Compare this with [the explicit derivative
  of that curve](lean:JJMath.Quasiconformal.stereographicPolarPatchMap_angularCurve_hasDerivAt)
  and use uniqueness of the derivative.
-/
theorem stereographicPolarPatchMap_angular_fderiv
    (v : Metric.sphere (0 : ℂ) 1) (r t : ℝ) :
    ((fderiv ℝ (Uniformization.stereographicPolarPatchMap v)
        (stereographicPolarAngularCoordinates (t, r))).comp
      (stereographicPolarAngularCoordinates :
        (ℝ × ℝ) →L[ℝ] (ℝ × EuclideanSpace ℝ (Fin 1))))
      ((1 : ℝ), (0 : ℝ)) =
        r • stereographicUnitCircleParamDerivative v t := by
  change
    (fderiv ℝ (Uniformization.stereographicPolarPatchMap v)
        (stereographicPolarAngularCoordinates (t, r)))
      (stereographicPolarAngularCoordinates ((1 : ℝ), (0 : ℝ))) =
        r • stereographicUnitCircleParamDerivative v t
  let Φ : ℝ × EuclideanSpace ℝ (Fin 1) → ℂ :=
    Uniformization.stereographicPolarPatchMap v
  let C : (ℝ × ℝ) →L[ℝ]
      (ℝ × EuclideanSpace ℝ (Fin 1)) :=
    stereographicPolarAngularCoordinates
  have hline : HasDerivAt (fun s : ℝ => (s, r))
      ((1 : ℝ), (0 : ℝ)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t r)
  have hC : HasDerivAt (fun s : ℝ => C (s, r))
      (C ((1 : ℝ), (0 : ℝ))) t := by
    simpa using (C.hasFDerivAt.comp t hline.hasFDerivAt).hasDerivAt
  have hΦ : HasFDerivAt Φ (fderiv ℝ Φ (C (t, r))) (C (t, r)) :=
    (((Uniformization.contDiff_stereographicPolarPatchMap v).differentiable
      (by simp)).differentiableAt).hasFDerivAt
  have hchain : HasDerivAt (fun s : ℝ => Φ (C (s, r)))
      ((fderiv ℝ Φ (C (t, r)))
        (C ((1 : ℝ), (0 : ℝ)))) t := by
    simpa using (hΦ.comp t hC.hasFDerivAt).hasDerivAt
  have hexplicit : HasDerivAt (fun s : ℝ => Φ (C (s, r)))
      (r • stereographicUnitCircleParamDerivative v t) t := by
    simpa [Φ, C] using
      stereographicPolarPatchMap_angularCurve_hasDerivAt v r t
  exact hchain.unique hexplicit

/--
%%handwave
name:
  Angular value of a planar covector field
statement:
  Given a real covector field $A$ on $\mathbb C$, this is the scalar
  $$
    V_v(t,r)=A(r\sigma_v(t))\bigl(r\sigma_v'(t)\bigr).
  $$
-/
def stereographicPolarAngularWeakDerivativeValue
    (v : Metric.sphere (0 : ℂ) 1)
    (du : ℂ → ℂ →L[ℝ] ℝ) (t r : ℝ) : ℝ :=
  du (Uniformization.stereographicPolarPatchMap v
    (stereographicPolarAngularCoordinates (t, r)))
    (r • stereographicUnitCircleParamDerivative v t)

/--
%%handwave
name:
  Angular weak-differential value under a positive dilation
statement:
  Let $S,q,t\in\mathbb R$.  If a covector field $D$ is pulled back by
  $z\mapsto Sz$ to the field $D_S(z)=S D(Sz)$, then its angular value at
  scaled radius $q$ is the original angular value at physical radius $Sq$:
  $$
    (D_S)_{q\sigma_v(t)}\bigl(q\sigma_v'(t)\bigr)
      =D_{Sq\sigma_v(t)}\bigl(Sq\sigma_v'(t)\bigr).
  $$
proof:
  The dilation of the base point changes $q\sigma_v(t)$ to
  $Sq\sigma_v(t)$, while real linearity moves the remaining factor $S$
  from the covector to the angular tangent vector.
-/
theorem stereographicPolarAngularWeakDerivativeValue_const_smul_comp
    (v : Metric.sphere (0 : ℂ) 1)
    (du : ℂ → ℂ →L[ℝ] ℝ) (S q t : ℝ) :
    stereographicPolarAngularWeakDerivativeValue v
        (fun z ↦ S • du (S • z)) t q =
      stereographicPolarAngularWeakDerivativeValue v du t (S * q) := by
  simp [stereographicPolarAngularWeakDerivativeValue,
    Uniformization.stereographicPolarPatchMap,
    stereographicPolarAngularCoordinates, realStereographicCoordinate]
  change S • du _ _ = _
  rw [← map_smul]
  congr 2 <;> simp [mul_assoc]

/--
%%handwave
name:
  Stereographic circle energy under dilation
statement:
  Let $S,q>0$, let $D_S(z)=S D(Sz)$, and write
  $$
    E_v(D,r)=\int_{\mathbb R}
      \left|D(r\sigma_v(t))\bigl(r\sigma_v'(t)\bigr)\right|^2
      \frac{t^2+4}{4r}\,dt.
  $$
  Then
  $$
    E_v(D_S,q)=S E_v(D,Sq).
  $$
proof:
  Use the [scaling identity for the angular value](lean:JJMath.Quasiconformal.stereographicPolarAngularWeakDerivativeValue_const_smul_comp).  The angular value itself is unchanged, and the reciprocal radial weight contributes the factor $S$.
-/
theorem lintegral_stereographicPolarAngularWeakDerivativeValue_const_smul_comp
    (v : Metric.sphere (0 : ℂ) 1)
    (du : ℂ → ℂ →L[ℝ] ℝ) {S q : ℝ}
    (hS : 0 < S) (hq : 0 < q) :
    (∫⁻ t : ℝ, ENNReal.ofReal
      (‖stereographicPolarAngularWeakDerivativeValue v
          (fun z ↦ S • du (S • z)) t q‖ ^ 2 *
        ((t ^ 2 + 4) / (4 * q))) ∂volume) =
      ENNReal.ofReal S *
        ∫⁻ t : ℝ, ENNReal.ofReal
          (‖stereographicPolarAngularWeakDerivativeValue v du t (S * q)‖ ^ 2 *
            ((t ^ 2 + 4) / (4 * (S * q)))) ∂volume := by
  have hpoint (t : ℝ) : ENNReal.ofReal
      (‖stereographicPolarAngularWeakDerivativeValue v
          (fun z ↦ S • du (S • z)) t q‖ ^ 2 *
        ((t ^ 2 + 4) / (4 * q))) =
      ENNReal.ofReal S * ENNReal.ofReal
        (‖stereographicPolarAngularWeakDerivativeValue v du t (S * q)‖ ^ 2 *
          ((t ^ 2 + 4) / (4 * (S * q)))) := by
    rw [stereographicPolarAngularWeakDerivativeValue_const_smul_comp,
      ← ENNReal.ofReal_mul hS.le]
    congr 1
    field_simp [hS.ne', hq.ne']
  rw [lintegral_congr hpoint,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/--
%%handwave
name:
  Angular value of the pulled-back weak differential
statement:
  Let $Du(z):\mathbb C\to\mathbb R$ be a field of real covectors.  For the
  weak differential pulled back by the stereographic polar patch and the
  angular--radial coordinate map, its value on $(1,0)$ at $(t,r)$ is
  $$
    Du(r\sigma_v(t))\bigl(r\sigma_v'(t)\bigr).
  $$
proof:
  Evaluate the two compositions of continuous linear maps and substitute
  [the angular vector of the polar-patch differential](lean:JJMath.Quasiconformal.stereographicPolarPatchMap_angular_fderiv).
-/
theorem stereographicPolarAngularWeakDifferential_apply
    (v : Metric.sphere (0 : ℂ) 1)
    (du : ℂ → ℂ →L[ℝ] ℝ) (r t : ℝ) :
    (((du (Uniformization.stereographicPolarPatchMap v
          (stereographicPolarAngularCoordinates (t, r)))).comp
        (fderiv ℝ (Uniformization.stereographicPolarPatchMap v)
          (stereographicPolarAngularCoordinates (t, r)))).comp
        (stereographicPolarAngularCoordinates :
          (ℝ × ℝ) →L[ℝ] (ℝ × EuclideanSpace ℝ (Fin 1))))
      ((1 : ℝ), (0 : ℝ)) =
        du (Uniformization.stereographicPolarPatchMap v
          (stereographicPolarAngularCoordinates (t, r)))
          (r • stereographicUnitCircleParamDerivative v t) := by
  apply congrArg
    (du (Uniformization.stereographicPolarPatchMap v
      (stereographicPolarAngularCoordinates (t, r))))
  simpa only [ContinuousLinearMap.comp_apply] using
    stereographicPolarPatchMap_angular_fderiv v r t

/--
%%handwave
name:
  Weighted pointwise angular-energy bound
statement:
  Let
  $$
    V_v(t,r)=Du(r\sigma_v(t))\bigl(r\sigma_v'(t)\bigr).
  $$
  If $r>0$, then
  $$
    |V_v(t,r)|^2\frac{t^2+4}{4r}
      \leq \|Du(r\sigma_v(t))\|^2\frac{4r}{t^2+4}.
  $$
proof:
  The operator-norm inequality gives
  $|V_v(t,r)|\leq\|Du(r\sigma_v(t))\|4r/(t^2+4)$.
  Square this inequality and divide by the positive factor $4r/(t^2+4)$.
-/
theorem stereographicPolarAngularWeakDerivativeValue_weighted_sq_le
    (v : Metric.sphere (0 : ℂ) 1)
    (du : ℂ → ℂ →L[ℝ] ℝ) (t r : ℝ) (hr : 0 < r) :
    ‖stereographicPolarAngularWeakDerivativeValue v du t r‖ ^ 2 *
        ((t ^ 2 + 4) / (4 * r)) ≤
      ‖du (Uniformization.stereographicPolarPatchMap v
        (stereographicPolarAngularCoordinates (t, r)))‖ ^ 2 *
          (r * (4 / (t ^ 2 + 4))) := by
  let q : ℝ := 4 / (t ^ 2 + 4)
  let N : ℝ :=
    ‖du (Uniformization.stereographicPolarPatchMap v
      (stereographicPolarAngularCoordinates (t, r)))‖
  let D : ℝ :=
    ‖stereographicPolarAngularWeakDerivativeValue v du t r‖
  have hq : 0 < q := by positivity
  have hw : 0 < r * q := mul_pos hr hq
  have hbound : D ≤ N * (r * q) := by
    dsimp [D, N, stereographicPolarAngularWeakDerivativeValue]
    convert ContinuousLinearMap.le_opNorm
      (du (Uniformization.stereographicPolarPatchMap v
        (stereographicPolarAngularCoordinates (t, r))))
      (r • stereographicUnitCircleParamDerivative v t) using 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr,
      norm_stereographicUnitCircleParamDerivative]
  have hsq : D ^ 2 ≤ (N * (r * q)) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) hw.le)).2 hbound
  have hdiv : D ^ 2 / (r * q) ≤ N ^ 2 * (r * q) := by
    apply (div_le_iff₀ hw).2
    nlinarith
  change D ^ 2 * ((t ^ 2 + 4) / (4 * r)) ≤
    N ^ 2 * (r * q)
  rw [show (t ^ 2 + 4) / (4 * r) = 1 / (r * q) by
    dsimp [q]
    field_simp]
  simpa [div_eq_mul_inv] using hdiv

/--
%%handwave
name:
  Complex-coordinate stereographic polar map
statement:
  For $v\in S^1$, this is the map
  $$
    T_v(z)=\operatorname{im}(z)\,\sigma_v(\operatorname{re}(z))
  $$
  from the complex angular--radial coordinate plane to $\mathbb C$.
-/
def stereographicPolarAngularComplexMap
    (v : Metric.sphere (0 : ℂ) 1) (z : ℂ) : ℂ :=
  Uniformization.stereographicPolarPatchMap v
    (stereographicPolarAngularCoordinates
      (Complex.equivRealProdCLM z))

/--
%%handwave
name:
  Formula for the complex angular--radial polar map
statement:
  If $z=t+ir$, then
  $$
    T_v(z)=r\sigma_v(t).
  $$
proof:
  Unfold the real and imaginary coordinate identification, the coordinate
  swap, and the stereographic polar patch.
-/
theorem stereographicPolarAngularComplexMap_apply
    (v : Metric.sphere (0 : ℂ) 1) (z : ℂ) :
    stereographicPolarAngularComplexMap v z =
      z.im • stereographicUnitCircleParam v z.re := by
  rfl

/--
%%handwave
name:
  Injectivity of stereographic polar coordinates at positive radii
statement:
  For every pole $v\in S^1$, the map
  $T_v(t+ir)=r\sigma_v(t)$ is injective on
  $$
    \{t+ir:0<r<1\}.
  $$
proof:
  Equality of two images gives equality of their norms, hence equality of the
  two positive radii.  Cancel that common radius.  Injectivity of inverse
  stereographic projection and of the linear coordinate map then gives
  equality of the angular coordinates.
-/
theorem injOn_stereographicPolarAngularComplexMap_positiveUnitRadius
    (v : Metric.sphere (0 : ℂ) 1) :
    Set.InjOn (stereographicPolarAngularComplexMap v)
      {z : ℂ | 0 < z.im ∧ z.im < 1} := by
  intro z hz w hw hzw
  have hnorm_z : ‖stereographicPolarAngularComplexMap v z‖ = |z.im| := by
    rw [stereographicPolarAngularComplexMap_apply,
      norm_smul, norm_stereographicUnitCircleParam, mul_one,
      Real.norm_eq_abs]
  have hnorm_w : ‖stereographicPolarAngularComplexMap v w‖ = |w.im| := by
    rw [stereographicPolarAngularComplexMap_apply,
      norm_smul, norm_stereographicUnitCircleParam, mul_one,
      Real.norm_eq_abs]
  have him : z.im = w.im := by
    rw [← abs_of_pos hz.1, ← abs_of_pos hw.1,
      ← hnorm_z, ← hnorm_w, hzw]
  have hparam : stereographicUnitCircleParam v z.re =
      stereographicUnitCircleParam v w.re := by
    have hscaled : z.im • stereographicUnitCircleParam v z.re =
        z.im • stereographicUnitCircleParam v w.re := by
      change z.im • stereographicUnitCircleParam v z.re =
        w.im • stereographicUnitCircleParam v w.re at hzw
      rwa [← him] at hzw
    exact smul_right_injective ℂ hz.1.ne' hscaled
  have hsphere :
      (stereographic' 1 v).symm (realStereographicCoordinate z.re) =
        (stereographic' 1 v).symm (realStereographicCoordinate w.re) := by
    apply Subtype.ext
    exact hparam
  have hcoord : realStereographicCoordinate z.re =
      realStereographicCoordinate w.re :=
    (stereographic' 1 v).symm.injOn
      (by simp [stereographic'_target])
      (by simp [stereographic'_target]) hsphere
  have hre : z.re = w.re := realStereographicCoordinate.injective hcoord
  apply Complex.ext
  · exact hre
  · exact him

/--
%%handwave
name:
  Smoothness of the complex angular--radial polar map
statement:
  For every $v\in S^1$, the map
  $$
    T_v:\mathbb C\to\mathbb C,
    \qquad T_v(t+ir)=r\sigma_v(t),
  $$
  is smooth.
proof:
  Compose the [smooth stereographic polar patch](lean:JJMath.Uniformization.contDiff_stereographicPolarPatchMap)
  with the two real-linear coordinate identifications.
-/
theorem contDiff_stereographicPolarAngularComplexMap
    (v : Metric.sphere (0 : ℂ) 1) :
    ContDiff ℝ ⊤ (stereographicPolarAngularComplexMap v) := by
  exact (Uniformization.contDiff_stereographicPolarPatchMap v).comp
    (stereographicPolarAngularCoordinates.contDiff.comp
      Complex.equivRealProdCLM.contDiff)

/--
%%handwave
name:
  Angular coordinate derivative of the complex polar map
statement:
  For $T_v(t+ir)=r\sigma_v(t)$,
  $$
    DT_v(t+ir)(1)=r\sigma_v'(t).
  $$
proof:
  Apply the chain rule along the real line $s\mapsto s+ir$ and compare with
  [the explicit derivative of the fixed-radius polar curve](lean:JJMath.Quasiconformal.stereographicPolarPatchMap_angularCurve_hasDerivAt).
-/
theorem fderiv_stereographicPolarAngularComplexMap_one
    (v : Metric.sphere (0 : ℂ) 1) (r t : ℝ) :
    (fderiv ℝ (stereographicPolarAngularComplexMap v)
      (t + r * Complex.I)) 1 =
        r • stereographicUnitCircleParamDerivative v t := by
  let z : ℂ := t + r * Complex.I
  have hmap : HasFDerivAt (stereographicPolarAngularComplexMap v)
      (fderiv ℝ (stereographicPolarAngularComplexMap v) z) z :=
    (((contDiff_stereographicPolarAngularComplexMap v).differentiable
      (by simp)).differentiableAt).hasFDerivAt
  have hline : HasDerivAt
      (fun s : ℝ => (s : ℂ) + r * Complex.I) 1 t := by
    simpa using
      (Complex.ofRealCLM.hasFDerivAt.comp t
        (hasDerivAt_id t).hasFDerivAt).hasDerivAt.const_add
          (r * Complex.I)
  have hchain : HasDerivAt
      (fun s : ℝ =>
        stereographicPolarAngularComplexMap v
          ((s : ℂ) + r * Complex.I))
      ((fderiv ℝ (stereographicPolarAngularComplexMap v) z) 1) t := by
    simpa [z] using (hmap.comp t hline.hasFDerivAt).hasDerivAt
  have hexplicit : HasDerivAt
      (fun s : ℝ =>
        stereographicPolarAngularComplexMap v
          ((s : ℂ) + r * Complex.I))
      (r • stereographicUnitCircleParamDerivative v t) t := by
    simpa [stereographicPolarAngularComplexMap] using
      stereographicPolarPatchMap_angularCurve_hasDerivAt v r t
  exact hchain.unique hexplicit

/--
%%handwave
name:
  Radial coordinate derivative of the complex polar map
statement:
  For $T_v(t+ir)=r\sigma_v(t)$,
  $$
    DT_v(t+ir)(i)=\sigma_v(t).
  $$
proof:
  Apply the chain rule along $s\mapsto t+is$.  Along that line the map is
  $s\mapsto s\sigma_v(t)$, whose derivative is $\sigma_v(t)$.
-/
theorem fderiv_stereographicPolarAngularComplexMap_I
    (v : Metric.sphere (0 : ℂ) 1) (r t : ℝ) :
    (fderiv ℝ (stereographicPolarAngularComplexMap v)
      (t + r * Complex.I)) Complex.I =
        stereographicUnitCircleParam v t := by
  let z : ℂ := t + r * Complex.I
  have hmap : HasFDerivAt (stereographicPolarAngularComplexMap v)
      (fderiv ℝ (stereographicPolarAngularComplexMap v) z) z :=
    (((contDiff_stereographicPolarAngularComplexMap v).differentiable
      (by simp)).differentiableAt).hasFDerivAt
  have hline : HasDerivAt
      (fun s : ℝ => (t : ℂ) + s * Complex.I) Complex.I r := by
    have hofReal : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 r := by
      simpa using
        (Complex.ofRealCLM.hasFDerivAt.comp r
          (hasDerivAt_id r).hasFDerivAt).hasDerivAt
    simpa [add_comm] using
      (hofReal.smul_const Complex.I).const_add (t : ℂ)
  have hchain : HasDerivAt
      (fun s : ℝ =>
        stereographicPolarAngularComplexMap v
          ((t : ℂ) + s * Complex.I))
      ((fderiv ℝ (stereographicPolarAngularComplexMap v) z) Complex.I) r := by
    simpa [z] using (hmap.comp r hline.hasFDerivAt).hasDerivAt
  have hexplicit : HasDerivAt
      (fun s : ℝ =>
        stereographicPolarAngularComplexMap v
          ((t : ℂ) + s * Complex.I))
      (stereographicUnitCircleParam v t) r := by
    simpa [stereographicPolarAngularComplexMap,
      stereographicPolarAngularCoordinates,
      stereographicUnitCircleParam] using
        (hasDerivAt_id r).smul_const
          (stereographicUnitCircleParam v t)
  exact hchain.unique hexplicit

/--
%%handwave
name:
  Jacobian of stereographic angular--radial polar coordinates
statement:
  If $r\geq0$ and $T_v(t+ir)=r\sigma_v(t)$, then
  $$
    |\operatorname{Jac}T_v(t+ir)|=\frac{4r}{t^2+4}.
  $$
proof:
  The derivative sends $1$ to $r\sigma_v'(t)$ and $i$ to $\sigma_v(t)$.
  These vectors are orthogonal, with respective norms $4r/(t^2+4)$ and $1$.
  The square of the Cartesian determinant is the determinant of their Gram
  matrix, so its absolute value is $4r/(t^2+4)$.
-/
theorem abs_weakJacobian_fderiv_stereographicPolarAngularComplexMap
    (v : Metric.sphere (0 : ℂ) 1) (r t : ℝ) (hr : 0 ≤ r) :
    |weakJacobian
      (fderiv ℝ (stereographicPolarAngularComplexMap v)
        (t + r * Complex.I))| =
      r * (4 / (t ^ 2 + 4)) := by
  let L : ℂ →L[ℝ] ℂ :=
    fderiv ℝ (stereographicPolarAngularComplexMap v)
      (t + r * Complex.I)
  have hL_one : L 1 = r • stereographicUnitCircleParamDerivative v t :=
    fderiv_stereographicPolarAngularComplexMap_one v r t
  have hL_I : L Complex.I = stereographicUnitCircleParam v t :=
    fderiv_stereographicPolarAngularComplexMap_I v r t
  have hnorm_one : ‖L 1‖ = r * (4 / (t ^ 2 + 4)) := by
    rw [hL_one, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr,
      norm_stereographicUnitCircleParamDerivative]
  have hnorm_I : ‖L Complex.I‖ = 1 := by
    rw [hL_I, norm_stereographicUnitCircleParam]
  have hinner : inner ℝ (L 1) (L Complex.I) = 0 := by
    rw [hL_one, hL_I, real_inner_smul_left,
      real_inner_stereographicUnitCircleParamDerivative_param, mul_zero]
  have hdet_sq (a b : ℂ) :
      (a.re * b.im - b.re * a.im) ^ 2 =
        ‖a‖ ^ 2 * ‖b‖ ^ 2 - (inner ℝ a b) ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm]
    rw [real_inner_eq_re_inner, RCLike.inner_apply]
    rw [Complex.normSq_apply, Complex.normSq_apply]
    have hab : RCLike.re (b * (starRingEnd ℂ) a) =
        b.re * a.re + b.im * a.im := by
      change (b * (starRingEnd ℂ) a).re =
        b.re * a.re + b.im * a.im
      rw [Complex.mul_re]
      simp
    rw [hab]
    ring
  have hsquares : (weakJacobian L) ^ 2 =
      (r * (4 / (t ^ 2 + 4))) ^ 2 := by
    rw [weakJacobian_eq_cartesian_coordinates]
    calc
      ((L 1).re * (L Complex.I).im -
          (L Complex.I).re * (L 1).im) ^ 2 =
          ‖L 1‖ ^ 2 * ‖L Complex.I‖ ^ 2 -
            (inner ℝ (L 1) (L Complex.I)) ^ 2 :=
        hdet_sq (L 1) (L Complex.I)
      _ = (r * (4 / (t ^ 2 + 4))) ^ 2 := by
        rw [hnorm_one, hnorm_I, hinner]
        ring
  have hright : 0 ≤ r * (4 / (t ^ 2 + 4)) := by positivity
  have habs_sq : |weakJacobian L| ^ 2 =
      (r * (4 / (t ^ 2 + 4))) ^ 2 := by
    rwa [sq_abs]
  nlinarith [abs_nonneg (weakJacobian L)]

/--
%%handwave
name:
  Area formula in stereographic angular--radial coordinates
statement:
  Let $T_v(t+ir)=r\sigma_v(t)$ and let $g:\mathbb C\to[0,\infty]$.  Then
  $$
    \int_{0<\operatorname{im}z<1}
      \frac{4\operatorname{im}z}{(\operatorname{re}z)^2+4}
      g(T_v(z))\,dz
    =\int_{T_v(\{0<\operatorname{im}z<1\})}g(y)\,dy.
  $$
proof:
  The map is smooth and [injective at positive unit radii](lean:JJMath.Quasiconformal.injOn_stereographicPolarAngularComplexMap_positiveUnitRadius).
  Apply the [classical area formula](lean:JJMath.Quasiconformal.areaFormula_of_hasFDerivAt)
  and substitute [the absolute Jacobian
  $4r/(t^2+4)$](lean:JJMath.Quasiconformal.abs_weakJacobian_fderiv_stereographicPolarAngularComplexMap).
-/
theorem lintegral_image_stereographicPolarAngularComplexMap
    (v : Metric.sphere (0 : ℂ) 1) (g : ℂ → ℝ≥0∞) :
    ∫⁻ z in {z : ℂ | 0 < z.im ∧ z.im < 1},
        ENNReal.ofReal (z.im * (4 / (z.re ^ 2 + 4))) *
          g (stereographicPolarAngularComplexMap v z) ∂volume =
      ∫⁻ y in stereographicPolarAngularComplexMap v ''
          {z : ℂ | 0 < z.im ∧ z.im < 1}, g y ∂volume := by
  let S : Set ℂ := {z : ℂ | 0 < z.im ∧ z.im < 1}
  have hS : MeasurableSet S := by
    exact (measurableSet_lt measurable_const Complex.measurable_im).inter
      (measurableSet_lt Complex.measurable_im measurable_const)
  have hderiv : ∀ z ∈ S,
      HasFDerivAt (stereographicPolarAngularComplexMap v)
        (fderiv ℝ (stereographicPolarAngularComplexMap v) z) z := by
    intro z hz
    exact (((contDiff_stereographicPolarAngularComplexMap v).differentiable
      (by simp)).differentiableAt).hasFDerivAt
  have harea := areaFormula_of_hasFDerivAt
    (hinj :=
      injOn_stereographicPolarAngularComplexMap_positiveUnitRadius v)
    (hderiv := hderiv) hS Subset.rfl g
  rw [harea]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem hS] with z hzS
  have hzrepr : z.re + z.im * Complex.I = z := by
    apply Complex.ext <;> simp
  rw [← hzrepr,
    abs_weakJacobian_fderiv_stereographicPolarAngularComplexMap
      v z.im z.re hzS.1.le]
  simp

/--
%%handwave
name:
  Unit-disk weighted stereographic angular-energy bound
statement:
  Let
  $$
    V_v(t,r)=Du(r\sigma_v(t))\bigl(r\sigma_v'(t)\bigr).
  $$
  Then
  $$
    \int_{0<r<1}\int_{\mathbb R}
      |V_v(t,r)|^2\frac{t^2+4}{4r}\,dt\,dr
      \leq \int_{B(0,1)}\|Du(y)\|^2\,dy,
  $$
  where the left side is presently expressed as the equivalent integral over
  the complex strip $0<\operatorname{im}z<1$.
proof:
  Apply the weighted pointwise angular-energy inequality under the integral.
  Its right side is the planar energy density multiplied by the absolute
  Jacobian $4r/(t^2+4)$.  The [stereographic angular--radial area
  formula](lean:JJMath.Quasiconformal.lintegral_image_stereographicPolarAngularComplexMap)
  converts this to the energy on the chart image.  That image lies in the
  open unit disk, so monotonicity gives the unit-disk energy.
-/
theorem lintegral_stereographicPolarAngularWeakDerivativeValue_weighted_le
    (v : Metric.sphere (0 : ℂ) 1)
    (du : ℂ → ℂ →L[ℝ] ℝ) :
    ∫⁻ z in {z : ℂ | 0 < z.im ∧ z.im < 1},
        ENNReal.ofReal
          (‖stereographicPolarAngularWeakDerivativeValue
              v du z.re z.im‖ ^ 2 *
            ((z.re ^ 2 + 4) / (4 * z.im))) ∂volume ≤
      ∫⁻ y in Metric.ball (0 : ℂ) 1,
        ENNReal.ofReal (‖du y‖ ^ 2) ∂volume := by
  let S : Set ℂ := {z : ℂ | 0 < z.im ∧ z.im < 1}
  have hS : MeasurableSet S := by
    exact (measurableSet_lt measurable_const Complex.measurable_im).inter
      (measurableSet_lt Complex.measurable_im measurable_const)
  calc
    ∫⁻ z in S,
        ENNReal.ofReal
          (‖stereographicPolarAngularWeakDerivativeValue
              v du z.re z.im‖ ^ 2 *
            ((z.re ^ 2 + 4) / (4 * z.im))) ∂volume ≤
        ∫⁻ z in S,
          ENNReal.ofReal
            (‖du (stereographicPolarAngularComplexMap v z)‖ ^ 2 *
              (z.im * (4 / (z.re ^ 2 + 4)))) ∂volume := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hS] with z hz
      apply ENNReal.ofReal_le_ofReal
      simpa [stereographicPolarAngularComplexMap] using
        stereographicPolarAngularWeakDerivativeValue_weighted_sq_le
          v du z.re z.im hz.1
    _ = ∫⁻ z in S,
          ENNReal.ofReal (z.im * (4 / (z.re ^ 2 + 4))) *
            ENNReal.ofReal
              (‖du (stereographicPolarAngularComplexMap v z)‖ ^ 2)
          ∂volume := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hS] with z hz
      rw [ENNReal.ofReal_mul (sq_nonneg
        ‖du (stereographicPolarAngularComplexMap v z)‖)]
      ac_rfl
    _ = ∫⁻ y in stereographicPolarAngularComplexMap v '' S,
          ENNReal.ofReal (‖du y‖ ^ 2) ∂volume := by
      simpa only [S] using
        lintegral_image_stereographicPolarAngularComplexMap v
          (fun y => ENNReal.ofReal (‖du y‖ ^ 2))
    _ ≤ ∫⁻ y in Metric.ball (0 : ℂ) 1,
          ENNReal.ofReal (‖du y‖ ^ 2) ∂volume := by
      apply lintegral_mono_set
      rintro y ⟨z, hz, rfl⟩
      apply Uniformization.stereographicPolarPatchMap_mapsTo_cylinder_unitBall
        (n := 1) v
      exact hz

/--
%%handwave
name:
  Volume preservation of angular--radial stereographic coordinates
statement:
  The linear coordinate map
  $$
    (t,r)\longmapsto (r,\iota(t))
  $$
  from $\mathbb R^2$ to the product of the radial line and the
  one-dimensional Euclidean stereographic coordinate preserves Lebesgue
  measure.
proof:
  The map is the coordinate swap followed by the canonical isometric
  identification of $\mathbb R$ with one-dimensional Euclidean space.  Both
  factors preserve their canonical volume measures.
-/
theorem measurePreserving_stereographicPolarAngularCoordinates :
    MeasurePreserving stereographicPolarAngularCoordinates
      (MeasureTheory.volume : Measure (ℝ × ℝ))
      (MeasureTheory.volume :
        Measure (ℝ × EuclideanSpace ℝ (Fin 1))) := by
  have hswap : MeasurePreserving
      (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ)
      (MeasureTheory.volume : Measure (ℝ × ℝ))
      (MeasureTheory.volume : Measure (ℝ × ℝ)) := by
    rw [Measure.volume_eq_prod]
    exact Measure.measurePreserving_swap
  have hprod : MeasurePreserving
      ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr
        realStereographicCoordinate)
      (MeasureTheory.volume : Measure (ℝ × ℝ))
      (MeasureTheory.volume :
        Measure (ℝ × EuclideanSpace ℝ (Fin 1))) := by
    rw [Measure.volume_eq_prod, Measure.volume_eq_prod]
    exact MeasurePreserving.prod (MeasurePreserving.id MeasureTheory.volume)
      ((PiLp.volume_preserving_toLp (Fin 1)).comp
        (volume_preserving_funUnique (Fin 1) ℝ).symm)
  exact hprod.comp hswap

/--
%%handwave
name:
  The polar cylinder in angular--radial order
statement:
  Under $(t,r)\mapsto(r,\iota(t))$, the stereographic polar cylinder
  $0<r<1$ pulls back to
  $$
    \{(t,r)\in\mathbb R^2:0<r<1\}.
  $$
proof:
  The first coordinate after the swap is exactly $r$.
-/
theorem preimage_stereographicPolarPatchCylinder_one_angularCoordinates :
    stereographicPolarAngularCoordinates ⁻¹'
        Uniformization.stereographicPolarPatchCylinder 1 =
      {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < 1} := by
  ext p
  rfl

/--
%%handwave
name:
  Null-set preservation of complex stereographic polar coordinates
statement:
  For every $v\in S^1$, the map
  $$
    T_v(t+ir)=r\sigma_v(t)
  $$
  is quasi-measure-preserving from Lebesgue measure restricted to the strip
  $\{t+ir:0<r<1\}$ to Lebesgue measure restricted to $B(0,1)$.
proof:
  The identification $t+ir\mapsto(r,\iota(t))$ preserves volume and carries
  the strip onto the positive unit polar cylinder.  Compose it with the
  [stereographic polar chart, which preserves null sets into the unit
  ball](lean:JJMath.Uniformization.stereographicPolarPatchMap_quasiMeasurePreserving_cylinder_unitBall).
-/
theorem stereographicPolarAngularComplexMap_quasiMeasurePreserving
    (v : Metric.sphere (0 : ℂ) 1) :
    Measure.QuasiMeasurePreserving
      (stereographicPolarAngularComplexMap v)
      (volume.restrict {z : ℂ | 0 < z.im ∧ z.im < 1})
      (volume.restrict (Metric.ball (0 : ℂ) 1)) := by
  let C : ℂ ≃L[ℝ] (ℝ × EuclideanSpace ℝ (Fin 1)) :=
    Complex.equivRealProdCLM.trans stereographicPolarAngularCoordinates
  have hC_mp : MeasurePreserving C
      (volume : Measure ℂ)
      (volume : Measure (ℝ × EuclideanSpace ℝ (Fin 1))) := by
    exact measurePreserving_stereographicPolarAngularCoordinates.comp
      Complex.volume_preserving_equiv_real_prod
  have hC_emb : MeasurableEmbedding C :=
    C.toHomeomorph.measurableEmbedding
  have hC_restrict : MeasurePreserving C
      (volume.restrict {z : ℂ | 0 < z.im ∧ z.im < 1})
      (volume.restrict
        (Uniformization.stereographicPolarPatchCylinder 1)) := by
    simpa [C,
      preimage_stereographicPolarPatchCylinder_one_angularCoordinates] using
      hC_mp.restrict_preimage_emb hC_emb
        (Uniformization.stereographicPolarPatchCylinder 1)
  have hpolar :=
    Uniformization.stereographicPolarPatchMap_quasiMeasurePreserving_cylinder_unitBall
      (H := ℂ) (n := 1) v
  simpa [stereographicPolarAngularComplexMap, C, Function.comp_def] using
    hpolar.comp hC_restrict.quasiMeasurePreserving

/--
%%handwave
name:
  Radius-first measurability on a complex strip
statement:
  If $(t,r)\mapsto F(t,r)$ is almost everywhere measurable when represented
  on the complex strip $\{t+ir:0<r<1\}$, then
  $(r,t)\mapsto F(t,r)$ is almost everywhere measurable for the product
  measure on $(0,1)\times\mathbb R$.
proof:
  Transport almost everywhere measurability through the volume-preserving
  real-linear isometry
  $z\mapsto(\operatorname{im}z,\operatorname{re}z)$.  Its restriction maps
  the complex strip measure-preservingly onto product measure restricted to
  $(0,1)\times\mathbb R$.
-/
theorem aemeasurable_radiusFirst_of_complex_strip
    (F : ℝ → ℝ → ℝ≥0∞)
    (hF : AEMeasurable (fun z : ℂ => F z.re z.im)
      (volume.restrict {z : ℂ | 0 < z.im ∧ z.im < 1})) :
    AEMeasurable (fun p : ℝ × ℝ => F p.2 p.1)
      ((volume.restrict (Set.Ioo (0 : ℝ) 1)).prod volume) := by
  let R : ℂ ≃L[ℝ] (ℝ × ℝ) :=
    Complex.equivRealProdCLM.trans
      (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ)
  have hswap : MeasurePreserving
      (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ)
      (volume : Measure (ℝ × ℝ))
      (volume : Measure (ℝ × ℝ)) := by
    rw [Measure.volume_eq_prod]
    exact Measure.measurePreserving_swap
  have hR_mp : MeasurePreserving R
      (volume : Measure ℂ) (volume : Measure (ℝ × ℝ)) := by
    exact hswap.comp Complex.volume_preserving_equiv_real_prod
  have hR_emb : MeasurableEmbedding R := R.toHomeomorph.measurableEmbedding
  have hpre : R ⁻¹' (Set.Ioo (0 : ℝ) 1 ×ˢ Set.univ) =
      {z : ℂ | 0 < z.im ∧ z.im < 1} := by
    ext z
    simp [R]
  have hR_restrict : MeasurePreserving R
      (volume.restrict {z : ℂ | 0 < z.im ∧ z.im < 1})
      (volume.restrict (Set.Ioo (0 : ℝ) 1 ×ˢ Set.univ)) := by
    simpa [hpre] using hR_mp.restrict_preimage_emb hR_emb
      (Set.Ioo (0 : ℝ) 1 ×ˢ Set.univ)
  have htarget : AEMeasurable (fun p : ℝ × ℝ => F p.2 p.1)
      (volume.restrict (Set.Ioo (0 : ℝ) 1 ×ˢ Set.univ)) := by
    apply (hR_restrict.aemeasurable_comp_iff hR_emb).mp
    simpa [R, Function.comp_def] using hF
  have hmeasure :
      ((volume.restrict (Set.Ioo (0 : ℝ) 1)).prod volume) =
        (volume : Measure (ℝ × ℝ)).restrict
          (Set.Ioo (0 : ℝ) 1 ×ˢ (Set.univ : Set ℝ)) := by
    calc
      (volume.restrict (Set.Ioo (0 : ℝ) 1)).prod volume =
          (volume.restrict (Set.Ioo (0 : ℝ) 1)).prod
            (volume.restrict (Set.univ : Set ℝ)) := by simp
      _ = (volume.prod volume).restrict
          (Set.Ioo (0 : ℝ) 1 ×ˢ (Set.univ : Set ℝ)) :=
        Measure.prod_restrict _ _
      _ = (volume : Measure (ℝ × ℝ)).restrict
          (Set.Ioo (0 : ℝ) 1 ×ˢ (Set.univ : Set ℝ)) := by
        rw [← Measure.volume_eq_prod]
  rw [hmeasure]
  exact htarget

/--
%%handwave
name:
  Radius-first Tonelli formula for a complex strip
statement:
  Let $F:\mathbb R^2\to[0,\infty]$ be almost everywhere measurable on
  $\mathbb R\times(0,1)$.  Then
  $$
    \int_{0<\operatorname{im}z<1}F(\operatorname{re}z,\operatorname{im}z)\,dz
      =\int_0^1\int_{\mathbb R}F(t,r)\,dt\,dr.
  $$
proof:
  The real-linear isometry $z\mapsto(\operatorname{im}z,\operatorname{re}z)$
  preserves planar Lebesgue measure and carries the complex strip to
  $(0,1)\times\mathbb R$.  Transport the integral through this equivalence
  and apply Tonelli's theorem.
-/
theorem lintegral_complex_strip_eq_radius_first
    (F : ℝ → ℝ → ℝ≥0∞)
    (hF : AEMeasurable (fun z : ℂ => F z.re z.im)
      (volume.restrict {z : ℂ | 0 < z.im ∧ z.im < 1})) :
    (∫⁻ z in {z : ℂ | 0 < z.im ∧ z.im < 1},
        F z.re z.im ∂volume) =
      ∫⁻ r in Set.Ioo (0 : ℝ) 1,
        ∫⁻ t : ℝ, F t r ∂volume ∂volume := by
  let R : ℂ ≃L[ℝ] (ℝ × ℝ) :=
    Complex.equivRealProdCLM.trans
      (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ)
  have hswap : MeasurePreserving
      (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ)
      (volume : Measure (ℝ × ℝ))
      (volume : Measure (ℝ × ℝ)) := by
    rw [Measure.volume_eq_prod]
    exact Measure.measurePreserving_swap
  have hR_mp : MeasurePreserving R
      (volume : Measure ℂ) (volume : Measure (ℝ × ℝ)) := by
    exact hswap.comp Complex.volume_preserving_equiv_real_prod
  have hR_emb : MeasurableEmbedding R :=
    R.toHomeomorph.measurableEmbedding
  have hpre : R ⁻¹' (Set.Ioo (0 : ℝ) 1 ×ˢ Set.univ) =
      {z : ℂ | 0 < z.im ∧ z.im < 1} := by
    ext z
    simp [R]
  have hR_restrict : MeasurePreserving R
      (volume.restrict {z : ℂ | 0 < z.im ∧ z.im < 1})
      (volume.restrict (Set.Ioo (0 : ℝ) 1 ×ˢ Set.univ)) := by
    simpa [hpre] using hR_mp.restrict_preimage_emb hR_emb
      (Set.Ioo (0 : ℝ) 1 ×ˢ Set.univ)
  have htarget : AEMeasurable (fun p : ℝ × ℝ => F p.2 p.1)
      (volume.restrict (Set.Ioo (0 : ℝ) 1 ×ˢ Set.univ)) := by
    apply (hR_restrict.aemeasurable_comp_iff hR_emb).mp
    simpa [R, Function.comp_def] using hF
  calc
    (∫⁻ z in {z : ℂ | 0 < z.im ∧ z.im < 1},
        F z.re z.im ∂volume) =
        ∫⁻ p in Set.Ioo (0 : ℝ) 1 ×ˢ Set.univ,
          F p.2 p.1 ∂volume := by
      simpa [R] using hR_restrict.lintegral_comp_emb hR_emb
        (fun p : ℝ × ℝ => F p.2 p.1)
    _ = ∫⁻ r in Set.Ioo (0 : ℝ) 1,
          ∫⁻ t : ℝ, F t r ∂volume ∂volume := by
      rw [Measure.volume_eq_prod] at htarget ⊢
      simpa using MeasureTheory.setLIntegral_prod
        (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
        (s := Set.Ioo (0 : ℝ) 1) (t := Set.univ)
        (fun p : ℝ × ℝ => F p.2 p.1) htarget

/--
%%handwave
name:
  Measurability of the stereographic angular weak-derivative norm
statement:
  If $Du\in L^2(B(0,1))$, then for every $v\in S^1$ the function
  $$
    (t,r)\longmapsto
      \left|Du(r\sigma_v(t))\bigl(r\sigma_v'(t)\bigr)\right|
  $$
  is almost everywhere measurable on the strip
  $\mathbb R\times(0,1)$.
proof:
  Pull the measurable representative of $Du$ back through the
  null-set-preserving stereographic polar map.  The angular vector field is
  continuous, evaluation of a covector on a vector is continuous, and norm
  followed by the nonnegative extended embedding preserves measurability.
-/
theorem aemeasurable_stereographicPolarAngularWeakDerivativeNorm
    (v : Metric.sphere (0 : ℂ) 1)
    (du : ℂ → ℂ →L[ℝ] ℝ)
    (hdu : MemLp du 2
      (volume.restrict (Metric.ball (0 : ℂ) 1))) :
    AEMeasurable
      (fun z : ℂ => ENNReal.ofReal
        ‖stereographicPolarAngularWeakDerivativeValue
          v du z.re z.im‖)
      (volume.restrict {z : ℂ | 0 < z.im ∧ z.im < 1}) := by
  let μS : Measure ℂ :=
    volume.restrict {z : ℂ | 0 < z.im ∧ z.im < 1}
  have hdu_comp : AEStronglyMeasurable
      (fun z : ℂ => du (stereographicPolarAngularComplexMap v z)) μS := by
    simpa [μS, Function.comp_def] using
      hdu.aestronglyMeasurable.comp_quasiMeasurePreserving
        (stereographicPolarAngularComplexMap_quasiMeasurePreserving v)
  have hvec_meas : Measurable
      (fun z : ℂ =>
        z.im • stereographicUnitCircleParamDerivative v z.re) := by
    simp only [stereographicUnitCircleParamDerivative]
    fun_prop
  have hvalue : AEStronglyMeasurable
      (fun z : ℂ =>
        stereographicPolarAngularWeakDerivativeValue v du z.re z.im) μS := by
    have happly :=
      (ContinuousLinearMap.apply ℝ ℝ).flip.aestronglyMeasurable_comp₂
        hdu_comp hvec_meas.aestronglyMeasurable
    simpa [stereographicPolarAngularWeakDerivativeValue,
      stereographicPolarAngularComplexMap] using happly
  exact hvalue.norm.aemeasurable.ennreal_ofReal

/--
%%handwave
name:
  Almost-everywhere angular-fiber measurability
statement:
  If $Du\in L^2(B(0,1))$, then for every $v\in S^1$ and almost every
  $r\in(0,1)$, the function
  $$
    t\longmapsto
      \left|Du(r\sigma_v(t))\bigl(r\sigma_v'(t)\bigr)\right|
  $$
  is almost everywhere measurable on $\mathbb R$.
proof:
  Swap the strip coordinates to radius-first product measure and apply the
  fiberwise measurability consequence of Fubini's theorem.
-/
theorem ae_aemeasurable_stereographicPolarAngularWeakDerivativeNorm
    (v : Metric.sphere (0 : ℂ) 1)
    (du : ℂ → ℂ →L[ℝ] ℝ)
    (hdu : MemLp du 2
      (volume.restrict (Metric.ball (0 : ℂ) 1))) :
    ∀ᵐ r ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)),
      AEMeasurable
        (fun t : ℝ => ENNReal.ofReal
          ‖stereographicPolarAngularWeakDerivativeValue v du t r‖)
        volume := by
  let F : ℝ → ℝ → ℝ≥0∞ := fun t r => ENNReal.ofReal
    ‖stereographicPolarAngularWeakDerivativeValue v du t r‖
  have hF_strip : AEMeasurable (fun z : ℂ => F z.re z.im)
      (volume.restrict {z : ℂ | 0 < z.im ∧ z.im < 1}) := by
    simpa [F] using
      aemeasurable_stereographicPolarAngularWeakDerivativeNorm v du hdu
  have hF_prod : AEMeasurable (fun p : ℝ × ℝ => F p.2 p.1)
      ((volume.restrict (Set.Ioo (0 : ℝ) 1)).prod volume) :=
    aemeasurable_radiusFirst_of_complex_strip F hF_strip
  have hfiber := hF_prod.aestronglyMeasurable.prodMk_left
  filter_upwards [hfiber] with r hr
  simpa [F] using hr.aemeasurable

/--
%%handwave
name:
  Measurability of the weighted stereographic angular energy
statement:
  If $Du\in L^2(B(0,1))$, then for every $v\in S^1$ the function
  $$
    (t,r)\longmapsto
    \left|Du(r\sigma_v(t))\bigl(r\sigma_v'(t)\bigr)\right|^2
      \frac{t^2+4}{4r}
  $$
  is almost everywhere measurable on $\mathbb R\times(0,1)$.
proof:
  Pull the almost everywhere measurable representative of $Du$ back through
  the [null-set-preserving stereographic polar
  map](lean:JJMath.Quasiconformal.stereographicPolarAngularComplexMap_quasiMeasurePreserving).
  The angular vector $(t,r)\mapsto r\sigma_v'(t)$ and the scalar weight are
  continuous, and evaluation of a continuous linear functional on a vector
  is continuous in both variables.
-/
theorem aemeasurable_stereographicPolarAngularWeightedEnergy
    (v : Metric.sphere (0 : ℂ) 1)
    (du : ℂ → ℂ →L[ℝ] ℝ)
    (hdu : MemLp du 2
      (volume.restrict (Metric.ball (0 : ℂ) 1))) :
    AEMeasurable
      (fun z : ℂ => ENNReal.ofReal
        (‖stereographicPolarAngularWeakDerivativeValue
            v du z.re z.im‖ ^ 2 *
          ((z.re ^ 2 + 4) / (4 * z.im))))
      (volume.restrict {z : ℂ | 0 < z.im ∧ z.im < 1}) := by
  let μS : Measure ℂ :=
    volume.restrict {z : ℂ | 0 < z.im ∧ z.im < 1}
  have hdu_comp : AEStronglyMeasurable
      (fun z : ℂ => du (stereographicPolarAngularComplexMap v z)) μS := by
    simpa [μS, Function.comp_def] using
      hdu.aestronglyMeasurable.comp_quasiMeasurePreserving
        (stereographicPolarAngularComplexMap_quasiMeasurePreserving v)
  have hvec_meas : Measurable
      (fun z : ℂ =>
        z.im • stereographicUnitCircleParamDerivative v z.re) := by
    simp only [stereographicUnitCircleParamDerivative]
    fun_prop
  have hvalue : AEStronglyMeasurable
      (fun z : ℂ =>
        stereographicPolarAngularWeakDerivativeValue v du z.re z.im) μS := by
    have happly :=
      (ContinuousLinearMap.apply ℝ ℝ).flip.aestronglyMeasurable_comp₂
        hdu_comp hvec_meas.aestronglyMeasurable
    simpa [stereographicPolarAngularWeakDerivativeValue,
      stereographicPolarAngularComplexMap] using happly
  have hweight : Measurable
      (fun z : ℂ => ((z.re ^ 2 + 4) / (4 * z.im))) := by
    fun_prop
  exact ((hvalue.norm.aemeasurable.pow_const 2).mul
    hweight.aemeasurable).ennreal_ofReal

/--
%%handwave
name:
  Radius-fiber weighted stereographic angular-energy bound
statement:
  Let
  $$
    V_v(t,r)=Du(r\sigma_v(t))\bigl(r\sigma_v'(t)\bigr).
  $$
  If $Du\in L^2(B(0,1))$, then
  $$
    \int_0^1\int_{\mathbb R}
      |V_v(t,r)|^2\frac{t^2+4}{4r}\,dt\,dr
      \leq \int_{B(0,1)}\|Du(y)\|^2\,dy.
  $$
proof:
  The weighted energy density is almost everywhere measurable.  Apply the
  [radius-first Tonelli formula for the complex
  strip](lean:JJMath.Quasiconformal.lintegral_complex_strip_eq_radius_first)
  to the [unit-disk weighted strip
  estimate](lean:JJMath.Quasiconformal.lintegral_stereographicPolarAngularWeakDerivativeValue_weighted_le).
-/
theorem lintegral_radius_stereographicPolarAngularWeakDerivativeValue_weighted_le
    (v : Metric.sphere (0 : ℂ) 1)
    (du : ℂ → ℂ →L[ℝ] ℝ)
    (hdu : MemLp du 2
      (volume.restrict (Metric.ball (0 : ℂ) 1))) :
    (∫⁻ r in Set.Ioo (0 : ℝ) 1,
        ∫⁻ t : ℝ,
          ENNReal.ofReal
            (‖stereographicPolarAngularWeakDerivativeValue v du t r‖ ^ 2 *
              ((t ^ 2 + 4) / (4 * r))) ∂volume ∂volume) ≤
      ∫⁻ y in Metric.ball (0 : ℂ) 1,
        ENNReal.ofReal (‖du y‖ ^ 2) ∂volume := by
  rw [← lintegral_complex_strip_eq_radius_first
    (fun t r => ENNReal.ofReal
      (‖stereographicPolarAngularWeakDerivativeValue v du t r‖ ^ 2 *
        ((t ^ 2 + 4) / (4 * r))))
    (aemeasurable_stereographicPolarAngularWeightedEnergy v du hdu)]
  exact lintegral_stereographicPolarAngularWeakDerivativeValue_weighted_le
    v du

/--
%%handwave
name:
  Measurability of the weighted energy of a stereographic circle
statement:
  If $Du\in L^2(B(0,1))$, then for every $v\in S^1$ the function
  $$
    r\longmapsto\int_{\mathbb R}
      \left|Du(r\sigma_v(t))\bigl(r\sigma_v'(t)\bigr)\right|^2
      \frac{t^2+4}{4r}\,dt
  $$
  is almost everywhere measurable on $(0,1)$.
proof:
  The two-variable weighted density is almost everywhere measurable after
  swapping to radius-first product coordinates.  Integrating its angular
  fiber preserves almost-everywhere measurability by Tonelli's theorem.
-/
theorem aemeasurable_lintegral_stereographicPolarAngularWeakDerivativeValue_weighted
    (v : Metric.sphere (0 : ℂ) 1)
    (du : ℂ → ℂ →L[ℝ] ℝ)
    (hdu : MemLp du 2
      (volume.restrict (Metric.ball (0 : ℂ) 1))) :
    AEMeasurable
      (fun r : ℝ => ∫⁻ t : ℝ,
        ENNReal.ofReal
          (‖stereographicPolarAngularWeakDerivativeValue v du t r‖ ^ 2 *
            ((t ^ 2 + 4) / (4 * r))) ∂volume)
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
  let F : ℝ → ℝ → ℝ≥0∞ := fun t r =>
    ENNReal.ofReal
      (‖stereographicPolarAngularWeakDerivativeValue v du t r‖ ^ 2 *
        ((t ^ 2 + 4) / (4 * r)))
  have hF_strip : AEMeasurable (fun z : ℂ => F z.re z.im)
      (volume.restrict {z : ℂ | 0 < z.im ∧ z.im < 1}) := by
    simpa [F] using
      aemeasurable_stereographicPolarAngularWeightedEnergy v du hdu
  have hF_prod : AEMeasurable (fun p : ℝ × ℝ => F p.2 p.1)
      ((volume.restrict (Set.Ioo (0 : ℝ) 1)).prod volume) :=
    aemeasurable_radiusFirst_of_complex_strip F hF_strip
  have houter : AEMeasurable
      (fun r : ℝ => ∫⁻ t : ℝ, F t r ∂volume)
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
    simpa [Function.uncurry] using hF_prod.lintegral_prod_right
  simpa [F] using houter

/--
%%handwave
name:
  Selection of a good radius with at most average energy
statement:
  Let $a<b$, let $F:(a,b)\to[0,\infty]$ be almost everywhere measurable,
  and suppose a property $P(r)$ holds for almost every $r\in(a,b)$.  Then
  there is $r\in(a,b)$ satisfying $P(r)$ and
  $$
    F(r)\leq\frac1{b-a}\int_a^b F(s)\,ds.
  $$
proof:
  Apply the first-moment principle to Lebesgue measure restricted to
  $(a,b)$, while avoiding the null set where either membership in the
  interval or the property fails.  The measure of the interval is $b-a$.
-/
theorem exists_good_radius_le_average
    {F : ℝ → ℝ≥0∞} {a b : ℝ} (hab : a < b)
    (hF : AEMeasurable F (volume.restrict (Set.Ioo a b)))
    {P : ℝ → Prop}
    (hP : ∀ᵐ r ∂(volume.restrict (Set.Ioo a b)), P r) :
    ∃ r ∈ Set.Ioo a b, P r ∧
      F r ≤ (∫⁻ s in Set.Ioo a b, F s ∂volume) /
        ENNReal.ofReal (b - a) := by
  let μ : Measure ℝ := volume.restrict (Set.Ioo a b)
  have hμ : μ ≠ 0 := by
    change (volume : Measure ℝ).restrict (Set.Ioo a b) ≠ 0
    intro hzero
    have hvolzero := Measure.restrict_eq_zero.mp hzero
    rw [Real.volume_Ioo] at hvolzero
    exact (ENNReal.ofReal_ne_zero_iff.mpr (sub_pos.mpr hab)) hvolzero
  have hmem : ∀ᵐ r ∂μ, r ∈ Set.Ioo a b :=
    ae_restrict_mem measurableSet_Ioo
  have hgood : ∀ᵐ r ∂μ, r ∈ Set.Ioo a b ∧ P r := by
    filter_upwards [hmem, hP] with r hr hPr
    exact ⟨hr, hPr⟩
  let N : Set ℝ := {r | ¬(r ∈ Set.Ioo a b ∧ P r)}
  have hN : μ N = 0 := ae_iff.mp hgood
  obtain ⟨r, hrN, hravg⟩ :=
    exists_notMem_null_le_laverage hμ hF hN
  refine ⟨r, (not_not.mp hrN).1, (not_not.mp hrN).2, ?_⟩
  rw [laverage_eq] at hravg
  simpa [μ, Real.volume_Ioo] using hravg

/--
%%handwave
name:
  Almost every radius has finite weighted angular energy
statement:
  If $Du\in L^2(B(0,1))$, then for every $v\in S^1$ and almost every
  $r\in(0,1)$,
  $$
    \int_{\mathbb R}
      \left|Du(r\sigma_v(t))\bigl(r\sigma_v'(t)\bigr)\right|^2
      \frac{t^2+4}{4r}\,dt<\infty.
  $$
proof:
  The radius-first weighted energy is bounded by the finite $L^2$ energy of
  $Du$ on the unit disk.  The fiber integral is almost everywhere measurable
  by Tonelli, and a nonnegative measurable function with finite integral is
  finite almost everywhere.
-/
theorem ae_lintegral_stereographicPolarAngularWeakDerivativeValue_weighted_lt_top
    (v : Metric.sphere (0 : ℂ) 1)
    (du : ℂ → ℂ →L[ℝ] ℝ)
    (hdu : MemLp du 2
      (volume.restrict (Metric.ball (0 : ℂ) 1))) :
    ∀ᵐ r ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)),
      (∫⁻ t : ℝ,
        ENNReal.ofReal
          (‖stereographicPolarAngularWeakDerivativeValue v du t r‖ ^ 2 *
            ((t ^ 2 + 4) / (4 * r))) ∂volume) < ∞ := by
  let F : ℝ → ℝ → ℝ≥0∞ := fun t r =>
    ENNReal.ofReal
      (‖stereographicPolarAngularWeakDerivativeValue v du t r‖ ^ 2 *
        ((t ^ 2 + 4) / (4 * r)))
  have hF_strip : AEMeasurable (fun z : ℂ => F z.re z.im)
      (volume.restrict {z : ℂ | 0 < z.im ∧ z.im < 1}) := by
    simpa [F] using
      aemeasurable_stereographicPolarAngularWeightedEnergy v du hdu
  have hF_prod : AEMeasurable (fun p : ℝ × ℝ => F p.2 p.1)
      ((volume.restrict (Set.Ioo (0 : ℝ) 1)).prod volume) :=
    aemeasurable_radiusFirst_of_complex_strip F hF_strip
  have houter : AEMeasurable
      (fun r : ℝ => ∫⁻ t : ℝ, F t r ∂volume)
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
    simpa [Function.uncurry] using hF_prod.lintegral_prod_right
  have htotal_le :=
    lintegral_radius_stereographicPolarAngularWeakDerivativeValue_weighted_le
      v du hdu
  have henergy_lt :
      (∫⁻ y in Metric.ball (0 : ℂ) 1,
        ENNReal.ofReal (‖du y‖ ^ 2) ∂volume) < ∞ := by
    rw [← eLpNorm_two_pow_two_eq_lintegral_ofReal_norm_sq
      du (volume.restrict (Metric.ball (0 : ℂ) 1))]
    exact ENNReal.pow_lt_top hdu.eLpNorm_lt_top
  have htotal_ne :
      (∫⁻ r in Set.Ioo (0 : ℝ) 1,
        ∫⁻ t : ℝ, F t r ∂volume ∂volume) ≠ ∞ := by
    apply ne_of_lt
    exact lt_of_le_of_lt (by simpa [F] using htotal_le) henergy_lt
  simpa [F] using ae_lt_top' houter htotal_ne

/--
%%handwave
name:
  Scalar weak derivatives in angular--radial stereographic coordinates
statement:
  Let $u$ be a scalar $W^{1,2}$ function on the complex unit disk with weak
  differential $Du$, and let $v\in S^1$.  Pull back first by the
  stereographic polar map $(r,y)\mapsto r\sigma_v(y)$ and then reorder the
  coordinates as $(t,r)$.  The resulting scalar function has weak
  differential
  $$
    Du\bigl(r\sigma_v(\iota(t))\bigr)
      \circ D\Phi_v\bigl(r,\iota(t)\bigr)\circ D(t,r\mapsto(r,\iota(t)))
  $$
  on $\{(t,r):0<r<1\}$.
proof:
  Pull the weak differential through the smooth stereographic polar chart,
  then through the volume-preserving linear coordinate swap.  The two weak
  chain rules compose to the displayed differential.
-/
theorem scalarWeakSobolev_stereographic_polar_angularCoordinates_pullback_weakDerivative
    (v : Metric.sphere (0 : ℂ) 1)
    {u : ℂ → ℝ} {du : ℂ → ℂ →L[ℝ] ℝ}
    (hweak : Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : ℂ) 1) u du)
    (hu : MemLp u 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : ℂ) 1)))
    (hdu : MemLp du 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : ℂ) 1))) :
    Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues
      {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < 1}
      (fun p : ℝ × ℝ =>
        u (Uniformization.stereographicPolarPatchMap v
          (stereographicPolarAngularCoordinates p)))
      (fun p : ℝ × ℝ =>
        ((du (Uniformization.stereographicPolarPatchMap v
            (stereographicPolarAngularCoordinates p))).comp
          (fderiv ℝ (Uniformization.stereographicPolarPatchMap v)
            (stereographicPolarAngularCoordinates p))).comp
          (stereographicPolarAngularCoordinates :
            (ℝ × ℝ) →L[ℝ]
              (ℝ × EuclideanSpace ℝ (Fin 1)))) := by
  have hpull :=
    Uniformization.scalarWeakSobolev_stereographic_polar_patch_pullback_weakDerivative
      (n := 1) v hweak hu hdu
  have hcoord := weakDerivative_comp_volumePreservingContinuousLinearEquiv
    stereographicPolarAngularCoordinates
    measurePreserving_stereographicPolarAngularCoordinates hpull
  simpa only [preimage_stereographicPolarPatchCylinder_one_angularCoordinates]
    using hcoord

/--
%%handwave
name:
  Angular ACL on translated compact stereographic polar bands
statement:
  Under the hypotheses of angular ACL on a compact polar band, fix
  $c\in\mathbb R$.  For almost every radius $r$, every protected segment
  $[a+c,b+c]\times\{r\}$ with $0<a<b<1$ has an absolutely continuous
  parametrization
  $$
    t\longmapsto u\bigl(\Phi_v(r,\iota(t+c))\bigr),
    \qquad a\leq t\leq b,
  $$
  whose derivative is the polar weak differential at $(t+c,r)$ applied to
  the angular vector $(1,0)$ for almost every $t\in(a,b)$.
proof:
  Translate the angular source coordinate by $(c,0)$.  Translation preserves
  volume and the polar cylinder, so the weak differential, continuity, and
  local integrability pull back to the translated compact band.  Apply
  [continuous scalar Sobolev functions are locally ACL on protected vertical segments](lean:JJMath.Uniformization.scalarWeakSobolev_firstCoordinate_fiberwise_acl_on_compact_of_continuousOn).
-/
theorem scalarWeakSobolev_stereographic_polar_angularCoordinates_fiberwise_acl_on_translated_compact
    (v : Metric.sphere (0 : ℂ) 1)
    {u : ℂ → ℝ} {du : ℂ → ℂ →L[ℝ] ℝ}
    (hweak : Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : ℂ) 1) u du)
    (hu : MemLp u 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : ℂ) 1)))
    (hdu : MemLp du 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : ℂ) 1)))
    (hu_cont : ContinuousOn u (Metric.ball (0 : ℂ) 1))
    (c : ℝ)
    {Q : Set (ℝ × ℝ)} (hQ : IsCompact Q)
    (hQ_cylinder : Q ⊆ {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < 1}) :
    let U : ℝ × ℝ → ℝ := fun p =>
      u (Uniformization.stereographicPolarPatchMap v
        (stereographicPolarAngularCoordinates p))
    let DU : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ := fun p =>
      ((du (Uniformization.stereographicPolarPatchMap v
          (stereographicPolarAngularCoordinates p))).comp
        (fderiv ℝ (Uniformization.stereographicPolarPatchMap v)
          (stereographicPolarAngularCoordinates p))).comp
        (stereographicPolarAngularCoordinates :
          (ℝ × ℝ) →L[ℝ] (ℝ × EuclideanSpace ℝ (Fin 1)))
    ∀ᵐ r ∂(volume : Measure ℝ),
      ∀ a b : ℝ, 0 < a → a < b → b < 1 →
        (∀ t ∈ Set.Icc a b, (t + c, r) ∈ Q) →
          AbsolutelyContinuousOnInterval (fun t : ℝ => U (t + c, r)) a b ∧
            ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Ioo a b),
              HasDerivAt (fun s : ℝ => U (s + c, r))
                (DU (t + c, r) ((1 : ℝ), (0 : ℝ))) t := by
  dsimp only
  let Ω : Set (ℝ × ℝ) := {p | 0 < p.2 ∧ p.2 < 1}
  let U : ℝ × ℝ → ℝ := fun p =>
    u (Uniformization.stereographicPolarPatchMap v
      (stereographicPolarAngularCoordinates p))
  let DU : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ := fun p =>
    ((du (Uniformization.stereographicPolarPatchMap v
        (stereographicPolarAngularCoordinates p))).comp
      (fderiv ℝ (Uniformization.stereographicPolarPatchMap v)
        (stereographicPolarAngularCoordinates p))).comp
      (stereographicPolarAngularCoordinates :
        (ℝ × ℝ) →L[ℝ] (ℝ × EuclideanSpace ℝ (Fin 1)))
  let shift : ℝ × ℝ := (c, 0)
  let Qc : Set (ℝ × ℝ) := (fun p => p + shift) ⁻¹' Q
  have hΩ_open : IsOpen Ω := by
    exact (isOpen_lt continuous_const continuous_snd).inter
      (isOpen_lt continuous_snd continuous_const)
  have hmap : Set.MapsTo
      (fun p : ℝ × ℝ =>
        Uniformization.stereographicPolarPatchMap v
          (stereographicPolarAngularCoordinates p))
      Ω (Metric.ball (0 : ℂ) 1) := by
    intro p hp
    apply Uniformization.stereographicPolarPatchMap_mapsTo_cylinder_unitBall v
    exact hp
  have hU_cont : ContinuousOn U Ω := by
    exact hu_cont.comp
      ((Uniformization.continuous_stereographicPolarPatchMap v).comp
        stereographicPolarAngularCoordinates.continuous).continuousOn hmap
  have hweak_pull :
      Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues Ω U DU := by
    simpa [Ω, U, DU] using
      scalarWeakSobolev_stereographic_polar_angularCoordinates_pullback_weakDerivative
        v hweak hu hdu
  have hpreimage : (fun p : ℝ × ℝ => p + shift) ⁻¹' Ω = Ω := by
    ext p
    simp [Ω, shift]
  have hweak_shift :
      Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues Ω
        (fun p => U (p + shift)) (fun p => DU (p + shift)) := by
    simpa only [hpreimage] using hweak_pull.comp_add_right shift
  have hU_shift_cont : ContinuousOn (fun p => U (p + shift)) Ω := by
    apply hU_cont.comp
      (continuous_id.add continuous_const).continuousOn
    intro p hp
    simpa [Ω, shift] using hp
  have hU_shift_loc : LocallyIntegrableOn (fun p => U (p + shift)) Ω
      (volume : Measure (ℝ × ℝ)) :=
    hU_shift_cont.locallyIntegrableOn hΩ_open.measurableSet
  have hQc : IsCompact Qc := by
    exact (Homeomorph.addRight shift).isCompact_preimage.2 hQ
  have hQcΩ : Qc ⊆ Ω := by
    intro p hp
    have hpQ : p + shift ∈ Q := hp
    have hpΩ := hQ_cylinder hpQ
    simpa [Ω, shift] using hpΩ
  have hacl :=
    Uniformization.scalarWeakSobolev_firstCoordinate_fiberwise_acl_on_compact_of_continuousOn
      hQc hQcΩ hΩ_open hU_shift_cont hweak_shift hU_shift_loc
  simpa [U, DU, shift, Qc, Prod.fst_add, Prod.snd_add] using hacl

/--
%%handwave
name:
  Simultaneous angular ACL on a countable overlapping cover
statement:
  Let $0<\rho$ and $\sigma<1$.  Under the scalar polar Sobolev hypotheses,
  for almost every $r\in[\rho,\sigma]$ and every $n\in\mathbb Z$, the
  parametrized angular arc
  $$
    t\longmapsto
      u\bigl(\Phi_v(r,\iota(t+n/2-1/8))\bigr),
    \qquad \frac18\leq t\leq\frac78,
  $$
  is absolutely continuous and has the polar weak angular derivative almost
  everywhere.  In the original stereographic coordinate these arcs are
  $[n/2,n/2+3/4]$; they overlap and cover the whole real line.
proof:
  For each integer $n$, apply angular ACL after translation by
  $n/2-1/8$ to the compact product of the corresponding angular interval
  with $[\rho,\sigma]$.  Intersect the resulting full-measure sets of radii
  over the countable set $\mathbb Z$.
-/
theorem scalarWeakSobolev_stereographic_polar_angularCoordinates_fiberwise_acl_on_countable_cover
    (v : Metric.sphere (0 : ℂ) 1)
    {u : ℂ → ℝ} {du : ℂ → ℂ →L[ℝ] ℝ}
    (hweak : Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : ℂ) 1) u du)
    (hu : MemLp u 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : ℂ) 1)))
    (hdu : MemLp du 2
      (MeasureTheory.volume.restrict (Metric.ball (0 : ℂ) 1)))
    (hu_cont : ContinuousOn u (Metric.ball (0 : ℂ) 1))
    {ρ σ : ℝ} (hρ : 0 < ρ) (hσ : σ < 1) :
    let U : ℝ × ℝ → ℝ := fun p =>
      u (Uniformization.stereographicPolarPatchMap v
        (stereographicPolarAngularCoordinates p))
    let DU : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ := fun p =>
      ((du (Uniformization.stereographicPolarPatchMap v
          (stereographicPolarAngularCoordinates p))).comp
        (fderiv ℝ (Uniformization.stereographicPolarPatchMap v)
          (stereographicPolarAngularCoordinates p))).comp
        (stereographicPolarAngularCoordinates :
          (ℝ × ℝ) →L[ℝ] (ℝ × EuclideanSpace ℝ (Fin 1)))
    ∀ᵐ r ∂(volume : Measure ℝ),
      ∀ n : ℤ, r ∈ Set.Icc ρ σ →
        let c : ℝ := (n : ℝ) / 2 - 1 / 8
        AbsolutelyContinuousOnInterval
            (fun t : ℝ => U (t + c, r)) (1 / 8) (7 / 8) ∧
          ∀ᵐ t ∂(volume : Measure ℝ).restrict
              (Set.Ioo (1 / 8) (7 / 8)),
            HasDerivAt (fun s : ℝ => U (s + c, r))
              (DU (t + c, r) ((1 : ℝ), (0 : ℝ))) t := by
  dsimp only
  apply ae_all_iff.2
  intro n
  let c : ℝ := (n : ℝ) / 2 - 1 / 8
  let Q : Set (ℝ × ℝ) :=
    Set.Icc (1 / 8 + c) (7 / 8 + c) ×ˢ Set.Icc ρ σ
  have hQ : IsCompact Q :=
    isCompact_Icc.prod isCompact_Icc
  have hQ_cylinder : Q ⊆ {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < 1} := by
    intro p hp
    exact ⟨hρ.trans_le hp.2.1, hp.2.2.trans_lt hσ⟩
  have hn :=
    scalarWeakSobolev_stereographic_polar_angularCoordinates_fiberwise_acl_on_translated_compact
      v hweak hu hdu hu_cont c hQ hQ_cylinder
  filter_upwards [hn] with r hr
  intro hrband
  apply hr (1 / 8) (7 / 8) (by norm_num) (by norm_num) (by norm_num)
  intro t ht
  change t + c ∈ Set.Icc (1 / 8 + c) (7 / 8 + c) ∧
    r ∈ Set.Icc ρ σ
  exact ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, hrband⟩

/--
%%handwave
name:
  Endpoint bounds on the stereographic angular ACL cover
statement:
  Let $u\in W^{1,2}(B(0,1))$ be continuous with weak differential $Du$,
  and put $U(t,r)=u(r\sigma_v(t))$.  For almost every radius in a compact
  subinterval of $(0,1)$, every translated cover interval has the following
  property.  If $1/8\leq a<b\leq7/8$ and
  $c=n/2-1/8$, then
  $$
    |U(a+c,r)-U(b+c,r)|
      \leq\int_a^b
        \left|Du(r\sigma_v(t+c))\bigl(r\sigma_v'(t+c)\bigr)\right|\,dt.
  $$
proof:
  Restrict the simultaneous angular absolute-continuity statement to
  $[a,b]$.  Remove the two endpoints, which are Lebesgue-null, identify the
  pulled-back derivative with
  $Du(r\sigma_v(t+c))(r\sigma_v'(t+c))$, and apply the real fundamental
  theorem of calculus endpoint estimate.
-/
theorem scalarWeakSobolev_stereographic_polar_angularCoordinates_fiberwise_endpoint_bound_on_countable_cover
    (v : Metric.sphere (0 : ℂ) 1)
    {u : ℂ → ℝ} {du : ℂ → ℂ →L[ℝ] ℝ}
    (hweak : Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : ℂ) 1) u du)
    (hu : MemLp u 2
      (volume.restrict (Metric.ball (0 : ℂ) 1)))
    (hdu : MemLp du 2
      (volume.restrict (Metric.ball (0 : ℂ) 1)))
    (hu_cont : ContinuousOn u (Metric.ball (0 : ℂ) 1))
    {ρ σ : ℝ} (hρ : 0 < ρ) (hσ : σ < 1) :
    let U : ℝ × ℝ → ℝ := fun p =>
      u (Uniformization.stereographicPolarPatchMap v
        (stereographicPolarAngularCoordinates p))
    ∀ᵐ r ∂(volume : Measure ℝ),
      ∀ n : ℤ, r ∈ Set.Icc ρ σ →
        let c : ℝ := (n : ℝ) / 2 - 1 / 8
        ∀ a b : ℝ, 1 / 8 ≤ a → a < b → b ≤ 7 / 8 →
          ENNReal.ofReal ‖U (a + c, r) - U (b + c, r)‖ ≤
            ∫⁻ t in Set.Ioo a b,
              ENNReal.ofReal
                ‖stereographicPolarAngularWeakDerivativeValue
                  v du (t + c) r‖ ∂volume := by
  dsimp only
  let U : ℝ × ℝ → ℝ := fun p =>
    u (Uniformization.stereographicPolarPatchMap v
      (stereographicPolarAngularCoordinates p))
  let DU : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ := fun p =>
    ((du (Uniformization.stereographicPolarPatchMap v
        (stereographicPolarAngularCoordinates p))).comp
      (fderiv ℝ (Uniformization.stereographicPolarPatchMap v)
        (stereographicPolarAngularCoordinates p))).comp
      (stereographicPolarAngularCoordinates :
        (ℝ × ℝ) →L[ℝ] (ℝ × EuclideanSpace ℝ (Fin 1)))
  have hacl :=
    scalarWeakSobolev_stereographic_polar_angularCoordinates_fiberwise_acl_on_countable_cover
      v hweak hu hdu hu_cont hρ hσ
  filter_upwards [hacl] with r hr
  intro n hrband
  let c : ℝ := (n : ℝ) / 2 - 1 / 8
  rcases hr n hrband with ⟨hU_ac, hU_deriv⟩
  intro a b ha hab hb
  have hsub : Set.uIcc a b ⊆ Set.uIcc (1 / 8 : ℝ) (7 / 8) := by
    rw [Set.uIcc_of_le hab.le,
      Set.uIcc_of_le (by norm_num : (1 / 8 : ℝ) ≤ 7 / 8)]
    exact Set.Icc_subset_Icc ha hb
  have hU_ac_ab : AbsolutelyContinuousOnInterval
      (fun t : ℝ => U (t + c, r)) a b := hU_ac.mono hsub
  have hderiv_full :
      ∀ᵐ t ∂(volume : Measure ℝ),
        t ∈ Set.Ioo (1 / 8 : ℝ) (7 / 8) →
          HasDerivAt (fun s : ℝ => U (s + c, r))
            (DU (t + c, r) ((1 : ℝ), (0 : ℝ))) t :=
    (ae_restrict_iff' measurableSet_Ioo).1 hU_deriv
  have hderiv_imp :
      ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIcc a b →
        HasDerivAt (fun s : ℝ => U (s + c, r))
          (stereographicPolarAngularWeakDerivativeValue v du (t + c) r) t := by
    filter_upwards [hderiv_full,
      compl_mem_ae_iff.mpr (measure_singleton (a : ℝ)),
      compl_mem_ae_iff.mpr (measure_singleton (b : ℝ))] with
        t ht hta htb htmem
    have htIcc : t ∈ Set.Icc a b := by
      simpa [Set.uIcc_of_le hab.le] using htmem
    have htIoo_ab : t ∈ Set.Ioo a b := by
      have hta' : t ≠ a := by simpa using hta
      have htb' : t ≠ b := by simpa using htb
      exact ⟨lt_of_le_of_ne htIcc.1 hta'.symm,
        lt_of_le_of_ne htIcc.2 htb'⟩
    have htbig : t ∈ Set.Ioo (1 / 8 : ℝ) (7 / 8) :=
      ⟨lt_of_le_of_lt ha htIoo_ab.1,
        lt_of_lt_of_le htIoo_ab.2 hb⟩
    have htderiv := ht htbig
    have hvalue : DU (t + c, r) ((1 : ℝ), (0 : ℝ)) =
        stereographicPolarAngularWeakDerivativeValue v du (t + c) r := by
      simpa [DU, stereographicPolarAngularWeakDerivativeValue] using
        stereographicPolarAngularWeakDifferential_apply v du r (t + c)
    rwa [hvalue] at htderiv
  simpa [U, c] using Uniformization.real_acl_endpoint_lintegral_bound
    (f := fun t : ℝ => U (t + c, r))
    (g := fun t : ℝ =>
      stereographicPolarAngularWeakDerivativeValue v du (t + c) r)
    hab hU_ac_ab hderiv_imp

/--
%%handwave
name:
  Additivity of nonnegative integrals over adjacent open intervals
statement:
  If $a\leq b\leq c$ and $h:\mathbb R\to[0,\infty]$, then
  $$
    \int_{(a,b)}h(t)\,dt+\int_{(b,c)}h(t)\,dt
      =\int_{(a,c)}h(t)\,dt.
  $$
proof:
  Open and half-open intervals agree up to their null endpoints.  The
  half-open intervals $(a,b]$ and $(b,c]$ are disjoint and their union is
  $(a,c]$, so additivity of the Lebesgue integral applies.
-/
theorem lintegral_Ioo_add_lintegral_Ioo
    (f : ℝ → ℝ≥0∞) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    (∫⁻ t in Set.Ioo a b, f t ∂volume) +
        ∫⁻ t in Set.Ioo b c, f t ∂volume =
      ∫⁻ t in Set.Ioo a c, f t ∂volume := by
  rw [Measure.restrict_congr_set (Ioo_ae_eq_Ioc (μ := volume)),
    Measure.restrict_congr_set (Ioo_ae_eq_Ioc (μ := volume)),
    Measure.restrict_congr_set (Ioo_ae_eq_Ioc (μ := volume)),
    ← MeasureTheory.lintegral_union measurableSet_Ioc
      (Ioc_disjoint_Ioc_of_le (b := b) le_rfl),
    Ioc_union_Ioc_eq_Ioc hab hbc]

/--
%%handwave
name:
  Chaining adjacent half-step endpoint estimates
statement:
  Let $U:\mathbb R\to\mathbb R$ and $g:\mathbb R\to[0,\infty]$.  Suppose
  that for every $n\in\mathbb Z$,
  $$
    |U(n/2)-U((n+1)/2)|
      \leq\int_{n/2}^{(n+1)/2}g(t)\,dt.
  $$
  Then for every $m\in\mathbb Z$ and $N\in\mathbb N$,
  $$
    |U(m/2)-U((m+N)/2)|
      \leq\int_{m/2}^{(m+N)/2}g(t)\,dt.
  $$
proof:
  Induct on $N$.  At the successor step, use the triangle inequality and
  add the new edge estimate.  Additivity on adjacent open intervals merges
  the two integrals, so each half-step is counted exactly once.
-/
theorem halfIntegerGrid_endpoint_bound_of_edge_bound
    (U : ℝ → ℝ) (g : ℝ → ℝ≥0∞)
    (hedge : ∀ n : ℤ,
      ENNReal.ofReal ‖U ((n : ℝ) / 2) - U ((n : ℝ) / 2 + 1 / 2)‖ ≤
        ∫⁻ t in Set.Ioo ((n : ℝ) / 2) ((n : ℝ) / 2 + 1 / 2),
          g t ∂volume) :
    ∀ (m : ℤ) (N : ℕ),
      ENNReal.ofReal
          ‖U ((m : ℝ) / 2) - U (((m + (N : ℤ) : ℤ) : ℝ) / 2)‖ ≤
        ∫⁻ t in Set.Ioo ((m : ℝ) / 2)
            (((m + (N : ℤ) : ℤ) : ℝ) / 2), g t ∂volume := by
  intro m N
  induction N with
  | zero => simp
  | succ N ih =>
      let k : ℤ := m + (N : ℤ)
      have hk : ((k : ℝ) / 2 : ℝ) ≤ (k : ℝ) / 2 + 1 / 2 := by
        norm_num
      have hm : ((m : ℝ) / 2 : ℝ) ≤ (k : ℝ) / 2 := by
        apply (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).2
        exact_mod_cast (Int.le_add_of_nonneg_right (Int.natCast_nonneg N) :
          m ≤ m + (N : ℤ))
      have hedge_k := hedge k
      calc
        ENNReal.ofReal
            ‖U ((m : ℝ) / 2) -
              U (((m + ((N + 1 : ℕ) : ℤ) : ℤ) : ℝ) / 2)‖ ≤
            ENNReal.ofReal
              (‖U ((m : ℝ) / 2) - U ((k : ℝ) / 2)‖ +
                ‖U ((k : ℝ) / 2) -
                  U (((m + ((N + 1 : ℕ) : ℤ) : ℤ) : ℝ) / 2)‖) := by
          apply ENNReal.ofReal_le_ofReal
          simpa [dist_eq_norm] using
            dist_triangle (U ((m : ℝ) / 2)) (U ((k : ℝ) / 2))
              (U (((m + ((N + 1 : ℕ) : ℤ) : ℤ) : ℝ) / 2))
        _ = ENNReal.ofReal ‖U ((m : ℝ) / 2) - U ((k : ℝ) / 2)‖ +
              ENNReal.ofReal
                ‖U ((k : ℝ) / 2) -
                  U (((m + ((N + 1 : ℕ) : ℤ) : ℤ) : ℝ) / 2)‖ := by
          rw [ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
        _ ≤ (∫⁻ t in Set.Ioo ((m : ℝ) / 2) ((k : ℝ) / 2),
                g t ∂volume) +
              ∫⁻ t in Set.Ioo ((k : ℝ) / 2) ((k : ℝ) / 2 + 1 / 2),
                g t ∂volume := by
          apply add_le_add
          · simpa [k] using ih
          · convert hedge_k using 1 <;> simp [k] <;> push_cast <;> ring
        _ = ∫⁻ t in Set.Ioo ((m : ℝ) / 2)
              (((m + ((N + 1 : ℕ) : ℤ) : ℤ) : ℝ) / 2),
              g t ∂volume := by
          convert lintegral_Ioo_add_lintegral_Ioo g hm hk using 1 <;>
            simp [k] <;> push_cast <;> ring

/--
%%handwave
name:
  Gluing half-step local endpoint estimates on the real line
statement:
  Let $U:\mathbb R\to\mathbb R$ and $g:\mathbb R\to[0,\infty]$.  Suppose
  that whenever $n\in\mathbb Z$ and
  $n/2\leq s\leq t\leq(n+1)/2$,
  $$
    |U(s)-U(t)|\leq\int_s^t g(x)\,dx.
  $$
  Then the same estimate holds for every $s\leq t$ in $\mathbb R$.
proof:
  Place $s$ and $t$ in their half-step cells using
  $\lfloor2s\rfloor$ and $\lfloor2t\rfloor$.  If the cells agree, use the
  local estimate.  Otherwise, use the local estimate on the two end pieces
  and chain all intervening half-step edges.  The triangle inequality and
  exact additivity of the three adjacent integrals give the result without
  overlap.
-/
theorem endpoint_bound_of_halfInteger_local_endpoint_bound
    (U : ℝ → ℝ) (g : ℝ → ℝ≥0∞)
    (hlocal : ∀ (n : ℤ) (s t : ℝ),
      (n : ℝ) / 2 ≤ s → s ≤ t → t ≤ (n : ℝ) / 2 + 1 / 2 →
        ENNReal.ofReal ‖U s - U t‖ ≤
          ∫⁻ x in Set.Ioo s t, g x ∂volume) :
    ∀ s t : ℝ, s ≤ t →
      ENNReal.ofReal ‖U s - U t‖ ≤
        ∫⁻ x in Set.Ioo s t, g x ∂volume := by
  have hedge : ∀ n : ℤ,
      ENNReal.ofReal ‖U ((n : ℝ) / 2) - U ((n : ℝ) / 2 + 1 / 2)‖ ≤
        ∫⁻ x in Set.Ioo ((n : ℝ) / 2) ((n : ℝ) / 2 + 1 / 2),
          g x ∂volume := by
    intro n
    exact hlocal n ((n : ℝ) / 2) ((n : ℝ) / 2 + 1 / 2)
      le_rfl (by norm_num) le_rfl
  intro s t hst
  let m : ℤ := ⌊2 * s⌋
  let n : ℤ := ⌊2 * t⌋
  have hms : (m : ℝ) / 2 ≤ s := by
    have h := Int.floor_le (2 * s)
    change (m : ℝ) ≤ 2 * s at h
    linarith
  have hsm : s ≤ (m : ℝ) / 2 + 1 / 2 := by
    have h := Int.lt_floor_add_one (2 * s)
    change 2 * s < (m : ℝ) + 1 at h
    linarith
  have hnt : (n : ℝ) / 2 ≤ t := by
    have h := Int.floor_le (2 * t)
    change (n : ℝ) ≤ 2 * t at h
    linarith
  have htn : t ≤ (n : ℝ) / 2 + 1 / 2 := by
    have h := Int.lt_floor_add_one (2 * t)
    change 2 * t < (n : ℝ) + 1 at h
    linarith
  have hmn : m ≤ n := by
    exact Int.floor_mono (by linarith)
  rcases hmn.eq_or_lt with hmn_eq | hmn_lt
  · have htm : t ≤ (m : ℝ) / 2 + 1 / 2 := by
      simpa [hmn_eq] using htn
    exact hlocal m s t hms hst htm
  · have hm1n : m + 1 ≤ n := Int.add_one_le_iff.mpr hmn_lt
    have hm1n_real : (m : ℝ) / 2 + 1 / 2 ≤ (n : ℝ) / 2 := by
      have hm1n_cast : (m : ℝ) + 1 ≤ (n : ℝ) := by
        exact_mod_cast hm1n
      linarith
    let N : ℕ := (n - (m + 1)).toNat
    have hN : (N : ℤ) = n - (m + 1) := by
      exact Int.toNat_of_nonneg (sub_nonneg.mpr hm1n)
    have hleft := hlocal m s ((m : ℝ) / 2 + 1 / 2)
      hms hsm le_rfl
    have hright := hlocal n ((n : ℝ) / 2) t
      le_rfl hnt htn
    have hmiddle := halfIntegerGrid_endpoint_bound_of_edge_bound U g hedge
      (m + 1) N
    have hmiddle' :
        ENNReal.ofReal
            ‖U ((m : ℝ) / 2 + 1 / 2) - U ((n : ℝ) / 2)‖ ≤
          ∫⁻ x in Set.Ioo ((m : ℝ) / 2 + 1 / 2) ((n : ℝ) / 2),
            g x ∂volume := by
      convert hmiddle using 1 <;> simp [hN] <;> push_cast <;> ring
    calc
      ENNReal.ofReal ‖U s - U t‖ ≤
          ENNReal.ofReal
            (‖U s - U ((m : ℝ) / 2 + 1 / 2)‖ +
              ‖U ((m : ℝ) / 2 + 1 / 2) - U ((n : ℝ) / 2)‖ +
              ‖U ((n : ℝ) / 2) - U t‖) := by
        apply ENNReal.ofReal_le_ofReal
        calc
          ‖U s - U t‖ ≤
              ‖U s - U ((m : ℝ) / 2 + 1 / 2)‖ +
                ‖U ((m : ℝ) / 2 + 1 / 2) - U t‖ := by
            simpa [dist_eq_norm] using
              dist_triangle (U s) (U ((m : ℝ) / 2 + 1 / 2)) (U t)
          _ ≤ ‖U s - U ((m : ℝ) / 2 + 1 / 2)‖ +
                (‖U ((m : ℝ) / 2 + 1 / 2) - U ((n : ℝ) / 2)‖ +
                  ‖U ((n : ℝ) / 2) - U t‖) := by
            gcongr
            simpa [dist_eq_norm] using
              dist_triangle (U ((m : ℝ) / 2 + 1 / 2))
                (U ((n : ℝ) / 2)) (U t)
          _ = _ := by ring
      _ = ENNReal.ofReal ‖U s - U ((m : ℝ) / 2 + 1 / 2)‖ +
            ENNReal.ofReal
              ‖U ((m : ℝ) / 2 + 1 / 2) - U ((n : ℝ) / 2)‖ +
            ENNReal.ofReal ‖U ((n : ℝ) / 2) - U t‖ := by
        rw [ENNReal.ofReal_add
          (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _),
          ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
      _ ≤ (∫⁻ x in Set.Ioo s ((m : ℝ) / 2 + 1 / 2), g x ∂volume) +
            (∫⁻ x in Set.Ioo ((m : ℝ) / 2 + 1 / 2) ((n : ℝ) / 2),
              g x ∂volume) +
            ∫⁻ x in Set.Ioo ((n : ℝ) / 2) t, g x ∂volume := by
        exact add_le_add (add_le_add hleft hmiddle') hright
      _ = ∫⁻ x in Set.Ioo s t, g x ∂volume := by
        rw [lintegral_Ioo_add_lintegral_Ioo g hsm hm1n_real,
          lintegral_Ioo_add_lintegral_Ioo g
            (hsm.trans hm1n_real) hnt]

/--
%%handwave
name:
  Global endpoint estimate on almost every stereographic angular line
statement:
  Let $u\in W^{1,2}(B(0,1))$ be continuous with weak differential $Du$,
  and put $U(t,r)=u(r\sigma_v(t))$.  For almost every radius in a compact
  subinterval of $(0,1)$ and every $s\leq t$ in $\mathbb R$,
  $$
    |U(s,r)-U(t,r)|
      \leq\int_s^t
        \left|Du(r\sigma_v(x))\bigl(r\sigma_v'(x)\bigr)\right|\,dx.
  $$
proof:
  On each half-step cell, translate the endpoint estimate from the
  simultaneous overlapping ACL cover and move its integral back by
  translation invariance of Lebesgue measure.  The abstract half-step gluing
  theorem then joins the two partial end cells and all intervening full cells
  without double-counting any derivative interval.
-/
theorem scalarWeakSobolev_stereographic_polar_angularCoordinates_fiberwise_global_endpoint_bound
    (v : Metric.sphere (0 : ℂ) 1)
    {u : ℂ → ℝ} {du : ℂ → ℂ →L[ℝ] ℝ}
    (hweak : Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : ℂ) 1) u du)
    (hu : MemLp u 2
      (volume.restrict (Metric.ball (0 : ℂ) 1)))
    (hdu : MemLp du 2
      (volume.restrict (Metric.ball (0 : ℂ) 1)))
    (hu_cont : ContinuousOn u (Metric.ball (0 : ℂ) 1))
    {ρ σ : ℝ} (hρ : 0 < ρ) (hσ : σ < 1) :
    let U : ℝ × ℝ → ℝ := fun p =>
      u (Uniformization.stereographicPolarPatchMap v
        (stereographicPolarAngularCoordinates p))
    ∀ᵐ r ∂(volume : Measure ℝ),
      r ∈ Set.Icc ρ σ → ∀ s t : ℝ, s ≤ t →
        ENNReal.ofReal ‖U (s, r) - U (t, r)‖ ≤
          ∫⁻ x in Set.Ioo s t,
            ENNReal.ofReal
              ‖stereographicPolarAngularWeakDerivativeValue v du x r‖
              ∂volume := by
  dsimp only
  let U : ℝ × ℝ → ℝ := fun p =>
    u (Uniformization.stereographicPolarPatchMap v
      (stereographicPolarAngularCoordinates p))
  have hendpoint :=
    scalarWeakSobolev_stereographic_polar_angularCoordinates_fiberwise_endpoint_bound_on_countable_cover
      v hweak hu hdu hu_cont hρ hσ
  filter_upwards [hendpoint] with r hr
  intro hrband
  apply endpoint_bound_of_halfInteger_local_endpoint_bound
    (fun t : ℝ => U (t, r))
    (fun t : ℝ => ENNReal.ofReal
      ‖stereographicPolarAngularWeakDerivativeValue v du t r‖)
  intro n s t hns hst htn
  by_cases heq : s = t
  · subst t
    simp
  have hstlt : s < t := lt_of_le_of_ne hst heq
  let c : ℝ := (n : ℝ) / 2 - 1 / 8
  have hlocal := hr n hrband (s - c) (t - c)
    (by dsimp [c]; linarith)
    (by linarith)
    (by dsimp [c]; linarith)
  let T : ℝ → ℝ := fun x => x + c
  have hT_emb : MeasurableEmbedding T := by
    simpa [T] using Uniformization.measurableEmbedding_add_right
      (H := ℝ) c
  have hT_mp : MeasurePreserving T
      (volume.restrict (Set.Ioo (s - c) (t - c)))
      (volume.restrict (Set.Ioo s t)) := by
    have h :=
      (Uniformization.measurePreserving_add_right_volume (H := ℝ) c).restrict_image_emb
        hT_emb (Set.Ioo (s - c) (t - c))
    convert h using 1 <;> simp [T, Set.image_add_const_Ioo] <;> ring
  calc
    ENNReal.ofReal ‖U (s, r) - U (t, r)‖ ≤
        ∫⁻ x in Set.Ioo (s - c) (t - c),
          ENNReal.ofReal
            ‖stereographicPolarAngularWeakDerivativeValue v du (x + c) r‖
            ∂volume := by
      convert hlocal using 1 <;> simp [U, c] <;> ring
    _ = ∫⁻ x in Set.Ioo s t,
          ENNReal.ofReal
            ‖stereographicPolarAngularWeakDerivativeValue v du x r‖
            ∂volume := by
      simpa [T] using hT_mp.lintegral_comp_emb hT_emb
        (fun x : ℝ => ENNReal.ofReal
          ‖stereographicPolarAngularWeakDerivativeValue v du x r‖)

/--
%%handwave
name:
  Integral of the reciprocal stereographic angular weight
statement:
  For every $r\geq0$,
  $$
    \int_{\mathbb R}\frac{4r}{t^2+4}\,dt=2\pi r,
  $$
  as an equality in $[0,\infty]$ after the canonical nonnegative embedding.
proof:
  Write $4r/(t^2+4)=r/(1+(t/2)^2)$.  Dilation by $1/2$ contributes the
  factor $2$, and the classical integral
  $\int_{\mathbb R}(1+x^2)^{-1}\,dx=\pi$ gives the formula.  Integrability
  and nonnegativity identify the real integral with the nonnegative extended
  integral.
-/
theorem lintegral_stereographicAngularReciprocalWeight
    (r : ℝ) (hr : 0 ≤ r) :
    (∫⁻ t : ℝ, ENNReal.ofReal (4 * r / (t ^ 2 + 4)) ∂volume) =
      ENNReal.ofReal (2 * Real.pi * r) := by
  let g : ℝ → ℝ := fun x => (1 + x ^ 2)⁻¹
  have hgint : Integrable g := integrable_inv_one_add_sq
  have hgscale : Integrable (fun t : ℝ => g ((1 / 2 : ℝ) * t)) :=
    hgint.comp_mul_left' (by norm_num)
  have hfint : Integrable (fun t : ℝ => 4 * r / (t ^ 2 + 4)) := by
    have hmul := hgscale.const_mul r
    apply hmul.congr
    filter_upwards [] with t
    dsimp [g]
    field_simp
    ring
  have hfnonneg : ∀ᵐ t : ℝ, 0 ≤ 4 * r / (t ^ 2 + 4) := by
    filter_upwards [] with t
    positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hfint hfnonneg]
  congr 1
  calc
    (∫ t : ℝ, 4 * r / (t ^ 2 + 4) ∂volume) =
        ∫ t : ℝ, r * g ((1 / 2 : ℝ) * t) ∂volume := by
      apply integral_congr_ae
      filter_upwards [] with t
      dsimp [g]
      field_simp
      ring
    _ = r * ∫ t : ℝ, g ((1 / 2 : ℝ) * t) ∂volume := by
      rw [MeasureTheory.integral_const_mul]
    _ = r * (2 * Real.pi) := by
      rw [Measure.integral_comp_mul_left g (1 / 2 : ℝ)]
      simp [g, integral_univ_inv_one_add_sq]
    _ = 2 * Real.pi * r := by ring

/--
%%handwave
name:
  Weighted Cauchy--Schwarz inequality for a positive extended weight
statement:
  Let $h,w:\mathbb R\to[0,\infty]$ be almost everywhere measurable, with
  $0<w(t)<\infty$ almost everywhere.  Then
  $$
    \int_{\mathbb R}h(t)\,dt
      \leq
    \left(\int_{\mathbb R}w(t)h(t)^2\,dt\right)^{1/2}
    \left(\int_{\mathbb R}w(t)^{-1}\,dt\right)^{1/2}.
  $$
proof:
  Apply Hölder's inequality with exponents $2$ and $2$ to
  $w^{1/2}h$ and $w^{-1/2}$.  Positivity and finiteness of $w$ identify
  their product with $h$; the laws of real powers identify their squares
  with $wh^2$ and $w^{-1}$.
-/
theorem lintegral_le_weighted_rpow_two_mul_inv
    {h w : ℝ → ℝ≥0∞}
    (hh : AEMeasurable h volume) (hw : AEMeasurable w volume)
    (hw0 : ∀ᵐ t ∂(volume : Measure ℝ), w t ≠ 0)
    (hwtop : ∀ᵐ t ∂(volume : Measure ℝ), w t ≠ ⊤) :
    (∫⁻ t : ℝ, h t ∂volume) ≤
      (∫⁻ t : ℝ, w t * h t ^ (2 : ℝ) ∂volume) ^ ((2 : ℝ)⁻¹) *
        (∫⁻ t : ℝ, (w t)⁻¹ ∂volume) ^ ((2 : ℝ)⁻¹) := by
  let f : ℝ → ℝ≥0∞ := fun t => w t ^ ((2 : ℝ)⁻¹) * h t
  let g : ℝ → ℝ≥0∞ := fun t => w t ^ (-(2 : ℝ)⁻¹)
  have hf : AEMeasurable f volume :=
    (hw.pow_const ((2 : ℝ)⁻¹)).mul hh
  have hg : AEMeasurable g volume :=
    hw.pow_const (-(2 : ℝ)⁻¹)
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq
    (μ := (volume : Measure ℝ)) (p := (2 : ℝ)) (q := (2 : ℝ))
    (f := f) (g := g) Real.HolderConjugate.two_two hf hg
  have hfg : (fun t => f t * g t) =ᵐ[volume] h := by
    filter_upwards [hw0, hwtop] with t hzero htop
    dsimp [f, g]
    calc
      w t ^ ((2 : ℝ)⁻¹) * h t * w t ^ (-(2 : ℝ)⁻¹) =
          (w t ^ ((2 : ℝ)⁻¹) * w t ^ (-(2 : ℝ)⁻¹)) * h t := by
        ac_rfl
      _ = h t := by
        rw [← ENNReal.rpow_add
          ((2 : ℝ)⁻¹) (-(2 : ℝ)⁻¹) hzero htop]
        norm_num
  have hf_sq : (fun t => f t ^ (2 : ℝ)) =ᵐ[volume]
      fun t => w t * h t ^ (2 : ℝ) := by
    filter_upwards with t
    dsimp [f]
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
      ← ENNReal.rpow_mul]
    norm_num
  have hg_sq : (fun t => g t ^ (2 : ℝ)) =ᵐ[volume]
      fun t => (w t)⁻¹ := by
    filter_upwards with t
    dsimp [g]
    rw [← ENNReal.rpow_mul]
    norm_num [ENNReal.rpow_neg_one]
  have hholder' :
      (∫⁻ t, f t * g t ∂volume) ≤
        (∫⁻ t, f t ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ)) *
          (∫⁻ t, g t ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ)) := by
    simpa only [Pi.mul_apply] using hholder
  rw [lintegral_congr_ae hfg,
    lintegral_congr_ae hf_sq, lintegral_congr_ae hg_sq] at hholder'
  simpa [one_div] using hholder'

/--
%%handwave
name:
  Weighted angular variation estimate on a stereographic circle
statement:
  Let $r>0$, let $Du$ be a measurable covector field, and write
  $$
    V(t,r)=Du(r\sigma_v(t))\bigl(r\sigma_v'(t)\bigr).
  $$
  If $t\mapsto |V(t,r)|$ is almost everywhere measurable, then
  $$
    \int_{\mathbb R}|V(t,r)|\,dt
      \leq
    \left(\int_{\mathbb R}|V(t,r)|^2
      \frac{t^2+4}{4r}\,dt\right)^{1/2}(2\pi r)^{1/2}.
  $$
proof:
  Apply the [weighted Cauchy--Schwarz
  inequality](lean:JJMath.Quasiconformal.lintegral_le_weighted_rpow_two_mul_inv)
  with weight $(t^2+4)/(4r)$.  Its reciprocal has integral $2\pi r$ by
  the [reciprocal stereographic-weight
  formula](lean:JJMath.Quasiconformal.lintegral_stereographicAngularReciprocalWeight).
-/
theorem lintegral_stereographicPolarAngularWeakDerivativeNorm_le_weightedEnergy
    (v : Metric.sphere (0 : ℂ) 1)
    (du : ℂ → ℂ →L[ℝ] ℝ)
    {r : ℝ} (hr : 0 < r)
    (hmeas : AEMeasurable
      (fun t : ℝ => ENNReal.ofReal
        ‖stereographicPolarAngularWeakDerivativeValue v du t r‖)
      volume) :
    (∫⁻ t : ℝ, ENNReal.ofReal
        ‖stereographicPolarAngularWeakDerivativeValue v du t r‖
        ∂volume) ≤
      (∫⁻ t : ℝ, ENNReal.ofReal
        (‖stereographicPolarAngularWeakDerivativeValue v du t r‖ ^ 2 *
          ((t ^ 2 + 4) / (4 * r))) ∂volume) ^ ((2 : ℝ)⁻¹) *
        ENNReal.ofReal (2 * Real.pi * r) ^ ((2 : ℝ)⁻¹) := by
  let h : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal
    ‖stereographicPolarAngularWeakDerivativeValue v du t r‖
  let w : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal
    ((t ^ 2 + 4) / (4 * r))
  have hw : AEMeasurable w volume := by
    dsimp [w]
    fun_prop
  have hw0 : ∀ᵐ t ∂(volume : Measure ℝ), w t ≠ 0 := by
    filter_upwards [] with t
    exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hwtop : ∀ᵐ t ∂(volume : Measure ℝ), w t ≠ ⊤ := by
    filter_upwards [] with t
    exact ENNReal.ofReal_ne_top
  have hweighted : (fun t => w t * h t ^ (2 : ℝ)) =
      fun t => ENNReal.ofReal
        (‖stereographicPolarAngularWeakDerivativeValue v du t r‖ ^ 2 *
          ((t ^ 2 + 4) / (4 * r))) := by
    funext t
    dsimp [h, w]
    rw [ENNReal.rpow_two,
      ← ENNReal.ofReal_pow (by positivity) 2]
    rw [← ENNReal.ofReal_mul (by positivity)]
    ring
  have hinv : (fun t => (w t)⁻¹) =
      fun t => ENNReal.ofReal (4 * r / (t ^ 2 + 4)) := by
    funext t
    dsimp [w]
    rw [← ENNReal.ofReal_inv_of_pos (by positivity)]
    congr 1
    field_simp
  have hcs := lintegral_le_weighted_rpow_two_mul_inv
    (h := h) (w := w) (by simpa [h] using hmeas) hw hw0 hwtop
  rw [hweighted, hinv,
    lintegral_stereographicAngularReciprocalWeight r hr.le] at hcs
  simpa [h] using hcs

/--
%%handwave
name:
  Weighted global endpoint estimate on almost every stereographic circle
statement:
  Let $u\in W^{1,2}(B(0,1))$ be continuous with weak differential $Du$,
  fix $v\in S^1$, and put $U(t,r)=u(r\sigma_v(t))$.  For almost every
  $r$ in any compact interval $[\rho,\sigma]\subset(0,1)$, the weighted
  angular energy
  $$
    E_v(r)=\int_{\mathbb R}
      \left|Du(r\sigma_v(x))\bigl(r\sigma_v'(x)\bigr)\right|^2
      \frac{x^2+4}{4r}\,dx
  $$
  is finite and, for every $s\leq t$,
  $$
    |U(s,r)-U(t,r)|\leq E_v(r)^{1/2}(2\pi r)^{1/2}.
  $$
proof:
  The [global endpoint estimate bounds each difference by the angular variation integral](lean:JJMath.Quasiconformal.scalarWeakSobolev_stereographic_polar_angularCoordinates_fiberwise_global_endpoint_bound).  Enlarge the interval of integration to the real line and apply the [weighted angular variation estimate](lean:JJMath.Quasiconformal.lintegral_stereographicPolarAngularWeakDerivativeNorm_le_weightedEnergy).  Almost-everywhere angular-fiber measurability and finiteness of the weighted energy hold simultaneously after restricting to $(0,1)$.
-/
theorem scalarWeakSobolev_stereographic_polar_angularCoordinates_fiberwise_global_endpoint_bound_weightedEnergy
    (v : Metric.sphere (0 : ℂ) 1)
    {u : ℂ → ℝ} {du : ℂ → ℂ →L[ℝ] ℝ}
    (hweak : Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : ℂ) 1) u du)
    (hu : MemLp u 2
      (volume.restrict (Metric.ball (0 : ℂ) 1)))
    (hdu : MemLp du 2
      (volume.restrict (Metric.ball (0 : ℂ) 1)))
    (hu_cont : ContinuousOn u (Metric.ball (0 : ℂ) 1))
    {ρ σ : ℝ} (hρ : 0 < ρ) (hσ : σ < 1) :
    let U : ℝ × ℝ → ℝ := fun p =>
      u (Uniformization.stereographicPolarPatchMap v
        (stereographicPolarAngularCoordinates p))
    ∀ᵐ r ∂(volume : Measure ℝ),
      r ∈ Set.Icc ρ σ →
        (∫⁻ t : ℝ,
          ENNReal.ofReal
            (‖stereographicPolarAngularWeakDerivativeValue v du t r‖ ^ 2 *
              ((t ^ 2 + 4) / (4 * r))) ∂volume) < ∞ ∧
        ∀ s t : ℝ, s ≤ t →
          ENNReal.ofReal ‖U (s, r) - U (t, r)‖ ≤
            (∫⁻ x : ℝ, ENNReal.ofReal
              (‖stereographicPolarAngularWeakDerivativeValue v du x r‖ ^ 2 *
                ((x ^ 2 + 4) / (4 * r))) ∂volume) ^ ((2 : ℝ)⁻¹) *
              ENNReal.ofReal (2 * Real.pi * r) ^ ((2 : ℝ)⁻¹) := by
  dsimp only
  let U : ℝ × ℝ → ℝ := fun p =>
    u (Uniformization.stereographicPolarPatchMap v
      (stereographicPolarAngularCoordinates p))
  have hendpoint :=
    scalarWeakSobolev_stereographic_polar_angularCoordinates_fiberwise_global_endpoint_bound
      v hweak hu hdu hu_cont hρ hσ
  have hmeas_restrict :=
    ae_aemeasurable_stereographicPolarAngularWeakDerivativeNorm v du hdu
  have hmeas : ∀ᵐ r ∂(volume : Measure ℝ), r ∈ Set.Ioo (0 : ℝ) 1 →
      AEMeasurable
        (fun t : ℝ => ENNReal.ofReal
          ‖stereographicPolarAngularWeakDerivativeValue v du t r‖)
        volume :=
    (ae_restrict_iff' measurableSet_Ioo).1 hmeas_restrict
  have hfinite_restrict :=
    ae_lintegral_stereographicPolarAngularWeakDerivativeValue_weighted_lt_top
      v du hdu
  have hfinite : ∀ᵐ r ∂(volume : Measure ℝ), r ∈ Set.Ioo (0 : ℝ) 1 →
      (∫⁻ t : ℝ,
        ENNReal.ofReal
          (‖stereographicPolarAngularWeakDerivativeValue v du t r‖ ^ 2 *
            ((t ^ 2 + 4) / (4 * r))) ∂volume) < ∞ :=
    (ae_restrict_iff' measurableSet_Ioo).1 hfinite_restrict
  filter_upwards [hendpoint, hmeas, hfinite] with r hrendpoint hrmeas hrfinite
  intro hrband
  have hrIoo : r ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨hρ.trans_le hrband.1, hrband.2.trans_lt hσ⟩
  refine ⟨hrfinite hrIoo, ?_⟩
  intro s t hst
  calc
    ENNReal.ofReal ‖U (s, r) - U (t, r)‖ ≤
        ∫⁻ x in Set.Ioo s t,
          ENNReal.ofReal
            ‖stereographicPolarAngularWeakDerivativeValue v du x r‖
            ∂volume := hrendpoint hrband s t hst
    _ ≤ ∫⁻ x : ℝ, ENNReal.ofReal
          ‖stereographicPolarAngularWeakDerivativeValue v du x r‖
          ∂volume := setLIntegral_le_lintegral _ _
    _ ≤ (∫⁻ x : ℝ, ENNReal.ofReal
          (‖stereographicPolarAngularWeakDerivativeValue v du x r‖ ^ 2 *
            ((x ^ 2 + 4) / (4 * r))) ∂volume) ^ ((2 : ℝ)⁻¹) *
          ENNReal.ofReal (2 * Real.pi * r) ^ ((2 : ℝ)⁻¹) :=
      lintegral_stereographicPolarAngularWeakDerivativeNorm_le_weightedEnergy
        v du (hρ.trans_le hrband.1) (hrmeas hrIoo)

/--
%%handwave
name:
  Weighted oscillation estimate on almost every Euclidean circle
statement:
  Let $u\in W^{1,2}(B(0,1))$ be continuous with weak differential $Du$,
  fix $v\in S^1$, and define
  $$
    E_v(r)=\int_{\mathbb R}
      \left|Du(r\sigma_v(x))\bigl(r\sigma_v'(x)\bigr)\right|^2
      \frac{x^2+4}{4r}\,dx.
  $$
  For almost every $r$ in any compact interval
  $[\rho,\sigma]\subset(0,1)$, $E_v(r)<\infty$ and, for every
  $\theta,\eta\in S^1$,
  $$
    |u(r\theta)-u(r\eta)|\leq E_v(r)^{1/2}(2\pi r)^{1/2}.
  $$
proof:
  Apply the [weighted endpoint estimate on the finite stereographic line](lean:JJMath.Quasiconformal.scalarWeakSobolev_stereographic_polar_angularCoordinates_fiberwise_global_endpoint_bound_weightedEnergy), then use [continuity to extend the same bound to every pair of points on the circle](lean:JJMath.Quasiconformal.angular_sphere_bound_of_continuousOn).
-/
theorem scalarWeakSobolev_ae_stereographic_circle_oscillation_le_weightedEnergy
    (v : Metric.sphere (0 : ℂ) 1)
    {u : ℂ → ℝ} {du : ℂ → ℂ →L[ℝ] ℝ}
    (hweak : Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : ℂ) 1) u du)
    (hu : MemLp u 2
      (volume.restrict (Metric.ball (0 : ℂ) 1)))
    (hdu : MemLp du 2
      (volume.restrict (Metric.ball (0 : ℂ) 1)))
    (hu_cont : ContinuousOn u (Metric.ball (0 : ℂ) 1))
    {ρ σ : ℝ} (hρ : 0 < ρ) (hσ : σ < 1) :
    ∀ᵐ r ∂(volume : Measure ℝ),
      r ∈ Set.Icc ρ σ →
        (∫⁻ t : ℝ,
          ENNReal.ofReal
            (‖stereographicPolarAngularWeakDerivativeValue v du t r‖ ^ 2 *
              ((t ^ 2 + 4) / (4 * r))) ∂volume) < ∞ ∧
        ∀ θ η : Metric.sphere (0 : ℂ) 1,
          ENNReal.ofReal ‖u (r • (θ : ℂ)) - u (r • (η : ℂ))‖ ≤
            (∫⁻ x : ℝ, ENNReal.ofReal
              (‖stereographicPolarAngularWeakDerivativeValue v du x r‖ ^ 2 *
                ((x ^ 2 + 4) / (4 * r))) ∂volume) ^ ((2 : ℝ)⁻¹) *
              ENNReal.ofReal (2 * Real.pi * r) ^ ((2 : ℝ)⁻¹) := by
  have hendpoint :=
    scalarWeakSobolev_stereographic_polar_angularCoordinates_fiberwise_global_endpoint_bound_weightedEnergy
      v hweak hu hdu hu_cont hρ hσ
  filter_upwards [hendpoint] with r hr
  intro hrband
  rcases hr hrband with ⟨hfinite, hbound⟩
  refine ⟨hfinite, ?_⟩
  exact angular_sphere_bound_of_continuousOn v hu_cont
    (hρ.trans_le hrband.1) (hrband.2.trans_lt hσ) hbound

/--
%%handwave
name:
  A good Euclidean circle with quantitatively controlled angular energy
statement:
  Let $u\in W^{1,2}(B(0,1))$ be continuous with weak differential $Du$,
  fix $v\in S^1$, and let $0<a<b<1$.  There is $r\in(a,b)$ such that
  $$
    E_v(r)\leq\frac1{b-a}\int_{B(0,1)}\|Du(y)\|^2\,dy<\infty,
  $$
  where
  $$
    E_v(r)=\int_{\mathbb R}
      \left|Du(r\sigma_v(t))\bigl(r\sigma_v'(t)\bigr)\right|^2
      \frac{t^2+4}{4r}\,dt,
  $$
  and for every $\theta,\eta\in S^1$,
  $$
    |u(r\theta)-u(r\eta)|\leq E_v(r)^{1/2}(2\pi r)^{1/2}.
  $$
proof:
  The circle energy is almost everywhere measurable, its integral over
  $(0,1)$ is bounded by the disk energy, and the full-circle oscillation
  property holds almost everywhere.  Apply the [good-radius first-moment selection](lean:JJMath.Quasiconformal.exists_good_radius_le_average) on $(a,b)$ while avoiding the exceptional radii, then use monotonicity of the nonnegative integral.
-/
theorem exists_stereographic_circle_energy_le_average
    (v : Metric.sphere (0 : ℂ) 1)
    {u : ℂ → ℝ} {du : ℂ → ℂ →L[ℝ] ℝ}
    (hweak : Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : ℂ) 1) u du)
    (hu : MemLp u 2
      (volume.restrict (Metric.ball (0 : ℂ) 1)))
    (hdu : MemLp du 2
      (volume.restrict (Metric.ball (0 : ℂ) 1)))
    (hu_cont : ContinuousOn u (Metric.ball (0 : ℂ) 1))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    ∃ r ∈ Set.Ioo a b,
      (∫⁻ t : ℝ, ENNReal.ofReal
        (‖stereographicPolarAngularWeakDerivativeValue v du t r‖ ^ 2 *
          ((t ^ 2 + 4) / (4 * r))) ∂volume) < ∞ ∧
      (∫⁻ t : ℝ, ENNReal.ofReal
        (‖stereographicPolarAngularWeakDerivativeValue v du t r‖ ^ 2 *
          ((t ^ 2 + 4) / (4 * r))) ∂volume) ≤
        (∫⁻ y in Metric.ball (0 : ℂ) 1,
          ENNReal.ofReal (‖du y‖ ^ 2) ∂volume) /
            ENNReal.ofReal (b - a) ∧
      ∀ θ η : Metric.sphere (0 : ℂ) 1,
        ENNReal.ofReal ‖u (r • (θ : ℂ)) - u (r • (η : ℂ))‖ ≤
          (∫⁻ x : ℝ, ENNReal.ofReal
            (‖stereographicPolarAngularWeakDerivativeValue v du x r‖ ^ 2 *
              ((x ^ 2 + 4) / (4 * r))) ∂volume) ^ ((2 : ℝ)⁻¹) *
            ENNReal.ofReal (2 * Real.pi * r) ^ ((2 : ℝ)⁻¹) := by
  let F : ℝ → ℝ≥0∞ := fun r => ∫⁻ t : ℝ, ENNReal.ofReal
    (‖stereographicPolarAngularWeakDerivativeValue v du t r‖ ^ 2 *
      ((t ^ 2 + 4) / (4 * r))) ∂volume
  have hab_subset : Set.Ioo a b ⊆ Set.Ioo (0 : ℝ) 1 := by
    intro r hr
    exact ⟨ha.trans hr.1, hr.2.trans hb⟩
  have hF : AEMeasurable F (volume.restrict (Set.Ioo a b)) :=
    (aemeasurable_lintegral_stereographicPolarAngularWeakDerivativeValue_weighted
      v du hdu).mono_measure
        (Measure.restrict_mono hab_subset le_rfl)
  let P : ℝ → Prop := fun r => F r < ∞ ∧
    ∀ θ η : Metric.sphere (0 : ℂ) 1,
      ENNReal.ofReal ‖u (r • (θ : ℂ)) - u (r • (η : ℂ))‖ ≤
        F r ^ ((2 : ℝ)⁻¹) *
          ENNReal.ofReal (2 * Real.pi * r) ^ ((2 : ℝ)⁻¹)
  have hcircle :=
    scalarWeakSobolev_ae_stereographic_circle_oscillation_le_weightedEnergy
      v hweak hu hdu hu_cont ha hb
  have hP : ∀ᵐ r ∂(volume.restrict (Set.Ioo a b)), P r := by
    apply (ae_restrict_iff' measurableSet_Ioo).2
    filter_upwards [hcircle] with r hr
    intro hrIoo
    exact hr ⟨hrIoo.1.le, hrIoo.2.le⟩
  obtain ⟨r, hr, hrP, hravg⟩ :=
    exists_good_radius_le_average hab hF hP
  have hband_le : (∫⁻ s in Set.Ioo a b, F s ∂volume) ≤
      ∫⁻ s in Set.Ioo (0 : ℝ) 1, F s ∂volume :=
    lintegral_mono' (Measure.restrict_mono hab_subset le_rfl) le_rfl
  have htotal :=
    lintegral_radius_stereographicPolarAngularWeakDerivativeValue_weighted_le
      v du hdu
  have hband_energy : (∫⁻ s in Set.Ioo a b, F s ∂volume) ≤
      ∫⁻ y in Metric.ball (0 : ℂ) 1,
        ENNReal.ofReal (‖du y‖ ^ 2) ∂volume :=
    hband_le.trans (by simpa [F] using htotal)
  refine ⟨r, hr, hrP.1, ?_, hrP.2⟩
  exact hravg.trans
    (ENNReal.div_le_div_right hband_energy (ENNReal.ofReal (b - a)))

/--
%%handwave
name:
  A good physical Euclidean circle in an arbitrary ball
statement:
  Let $S>0$, let $u\in W^{1,2}(B(0,S))$ be continuous with weak
  differential $Du$, fix $v\in S^1$, and let $0<a<b<S$. There is a
  physical radius $r\in(a,b)$ such that
  $$
    E_v(r)\leq\frac1{b-a}\int_{B(0,S)}\|Du(y)\|^2\,dy<\infty,
  $$
  where
  $$
    E_v(r)=\int_{\mathbb R}
      \left|Du(r\sigma_v(t))\bigl(r\sigma_v'(t)\bigr)\right|^2
      \frac{t^2+4}{4r}\,dt,
  $$
  and for every $\theta,\eta\in S^1$,
  $$
    |u(r\theta)-u(r\eta)|\leq E_v(r)^{1/2}(2\pi r)^{1/2}.
  $$
proof:
  Dilate $B(0,S)$ to the unit disk and apply the [unit-disk good-circle selector](lean:JJMath.Quasiconformal.exists_stereographic_circle_energy_le_average) on $(a/S,b/S)$. The [circle energy gains the factor $S$](lean:JJMath.Quasiconformal.lintegral_stereographicPolarAngularWeakDerivativeValue_const_smul_comp), the interval length loses the same factor, and [planar Dirichlet energy is dilation invariant](lean:JJMath.Quasiconformal.lintegral_norm_const_smul_comp_sq_restrict_ball_one), so the physical estimate has exactly the stated constant.
-/
theorem exists_stereographic_circle_energy_le_average_on_ball
    (v : Metric.sphere (0 : ℂ) 1)
    {u : ℂ → ℝ} {du : ℂ → ℂ →L[ℝ] ℝ}
    {S a b : ℝ} (hS : 0 < S) (ha : 0 < a) (hab : a < b)
    (hb : b < S)
    (hweak : Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : ℂ) S) u du)
    (hu : MemLp u 2
      (volume.restrict (Metric.ball (0 : ℂ) S)))
    (hdu : MemLp du 2
      (volume.restrict (Metric.ball (0 : ℂ) S)))
    (hu_cont : ContinuousOn u (Metric.ball (0 : ℂ) S)) :
    ∃ r ∈ Set.Ioo a b,
      (∫⁻ t : ℝ, ENNReal.ofReal
        (‖stereographicPolarAngularWeakDerivativeValue v du t r‖ ^ 2 *
          ((t ^ 2 + 4) / (4 * r))) ∂volume) < ∞ ∧
      (∫⁻ t : ℝ, ENNReal.ofReal
        (‖stereographicPolarAngularWeakDerivativeValue v du t r‖ ^ 2 *
          ((t ^ 2 + 4) / (4 * r))) ∂volume) ≤
        (∫⁻ y in Metric.ball (0 : ℂ) S,
          ENNReal.ofReal (‖du y‖ ^ 2) ∂volume) /
            ENNReal.ofReal (b - a) ∧
      ∀ θ η : Metric.sphere (0 : ℂ) 1,
        ENNReal.ofReal ‖u (r • (θ : ℂ)) - u (r • (η : ℂ))‖ ≤
          (∫⁻ x : ℝ, ENNReal.ofReal
            (‖stereographicPolarAngularWeakDerivativeValue v du x r‖ ^ 2 *
              ((x ^ 2 + 4) / (4 * r))) ∂volume) ^ ((2 : ℝ)⁻¹) *
            ENNReal.ofReal (2 * Real.pi * r) ^ ((2 : ℝ)⁻¹) := by
  let w : ℂ → ℝ := fun z ↦ u (S • z)
  let dw : ℂ → ℂ →L[ℝ] ℝ := fun z ↦ S • du (S • z)
  have hweakS :
      Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues
        (Metric.ball (0 : ℂ) (S * 1)) u du := by
    simpa using hweak
  have hweak_raw := hweakS.comp_smul hS.ne'
  rw [Uniformization.preimage_const_smul_ball_zero_of_pos
    (a := S) (R := (1 : ℝ)) hS] at hweak_raw
  have hwweak : Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : ℂ) 1) w dw := by
    simpa [w, dw] using hweak_raw
  have hw : MemLp w 2
      (volume.restrict (Metric.ball (0 : ℂ) 1)) := by
    simpa [w] using
      Uniformization.memLp_comp_const_smul_of_memLp_restrict_ball_zero
        (a := S) (R := (1 : ℝ)) hS (by simpa using hu)
  have hdw : MemLp dw 2
      (volume.restrict (Metric.ball (0 : ℂ) 1)) := by
    have hcomp :=
      Uniformization.memLp_comp_const_smul_of_memLp_restrict_ball_zero
        (a := S) (R := (1 : ℝ)) hS (by simpa using hdu)
    simpa [dw] using hcomp.const_smul S
  have hmaps : Set.MapsTo (fun z : ℂ ↦ S • z)
      (Metric.ball 0 1) (Metric.ball 0 S) := by
    intro z hz
    simp only [Metric.mem_ball, dist_zero_right] at hz ⊢
    simpa [norm_smul, Real.norm_eq_abs, abs_of_pos hS] using
      (mul_lt_mul_of_pos_left hz hS)
  have hw_cont : ContinuousOn w (Metric.ball (0 : ℂ) 1) := by
    exact hu_cont.comp (continuous_const_smul S).continuousOn hmaps
  have haS : 0 < a / S := div_pos ha hS
  have habS : a / S < b / S :=
    (div_lt_div_iff_of_pos_right hS).2 hab
  have hbS : b / S < 1 := (div_lt_one hS).2 hb
  obtain ⟨q, hq, hqfinite, hqenergy, hqosc⟩ :=
    exists_stereographic_circle_energy_le_average v hwweak hw hdw hw_cont
      haS habS hbS
  have hqpos : 0 < q := haS.trans hq.1
  have hscale :=
    lintegral_stereographicPolarAngularWeakDerivativeValue_const_smul_comp
      v du hS hqpos
  have hrmem : S * q ∈ Set.Ioo a b := by
    constructor
    · simpa [mul_comm] using (div_lt_iff₀ hS).1 hq.1
    · simpa [mul_comm] using (lt_div_iff₀ hS).1 hq.2
  refine ⟨S * q, hrmem, ?_, ?_, ?_⟩
  · rw [hscale] at hqfinite
    exact ENNReal.lt_top_of_mul_ne_top_right hqfinite.ne
      (ENNReal.ofReal_pos.2 hS).ne'
  · have hdisk :
        (∫⁻ y in Metric.ball (0 : ℂ) 1,
            ENNReal.ofReal (‖dw y‖ ^ 2) ∂volume) =
          ∫⁻ y in Metric.ball (0 : ℂ) S,
            ENNReal.ofReal (‖du y‖ ^ 2) ∂volume := by
      simpa [dw] using
        lintegral_norm_const_smul_comp_sq_restrict_ball_one hS du
          hdu.1.aemeasurable
    rw [hscale] at hqenergy
    rw [hdisk] at hqenergy
    rw [show b / S - a / S = (b - a) / S by
      field_simp [hS.ne']] at hqenergy
    rw [ENNReal.ofReal_div_of_pos hS] at hqenergy
    apply (ENNReal.mul_le_mul_iff_right
      (ENNReal.ofReal_pos.2 hS).ne' ENNReal.ofReal_ne_top).1
    calc
      ENNReal.ofReal S *
          (∫⁻ t : ℝ, ENNReal.ofReal
            (‖stereographicPolarAngularWeakDerivativeValue v du t (S * q)‖ ^ 2 *
              ((t ^ 2 + 4) / (4 * (S * q)))) ∂volume) ≤
          (∫⁻ y in Metric.ball (0 : ℂ) S,
            ENNReal.ofReal (‖du y‖ ^ 2) ∂volume) /
              (ENNReal.ofReal (b - a) / ENNReal.ofReal S) := hqenergy
      _ = ENNReal.ofReal S *
          ((∫⁻ y in Metric.ball (0 : ℂ) S,
            ENNReal.ofReal (‖du y‖ ^ 2) ∂volume) /
              ENNReal.ofReal (b - a)) := by
        rw [div_eq_mul_inv,
          ENNReal.inv_div (Or.inl ENNReal.ofReal_ne_top)
            (Or.inl (ENNReal.ofReal_pos.2 hS).ne')]
        simp only [div_eq_mul_inv]
        ac_rfl
  · intro θ η
    have hosc := hqosc θ η
    rw [hscale] at hosc
    simpa [w, mul_smul, ENNReal.mul_rpow_of_nonneg,
      ENNReal.ofReal_mul hS.le, mul_assoc, mul_left_comm, mul_comm] using hosc

/--
%%handwave
name:
  Dyadic-circle square-root cancellation
statement:
  Let $d>0$, $r\leq2d$, and $F,E\in[0,\infty]$. If
  $$
    F\leq \frac{E}{d},
  $$
  then
  $$
    F^{1/2}(2\pi r)^{1/2}
      \leq E^{1/2}(4\pi)^{1/2}.
  $$
proof:
  Before taking square roots, bound $2\pi r\leq4\pi d$.  The factor $d$
  then cancels the denominator in $E/d$; positivity and finiteness of $d$
  make this cancellation valid in $[0,\infty]$ even when $E=\infty$.
-/
theorem circle_oscillation_factor_le_of_radius_le_two_mul
    {F E : ℝ≥0∞} {d r : ℝ}
    (hd : 0 < d) (hr : r ≤ 2 * d)
    (hF : F ≤ E / ENNReal.ofReal d) :
    F ^ ((2 : ℝ)⁻¹) *
        ENNReal.ofReal (2 * Real.pi * r) ^ ((2 : ℝ)⁻¹) ≤
      E ^ ((2 : ℝ)⁻¹) *
        ENNReal.ofReal (4 * Real.pi) ^ ((2 : ℝ)⁻¹) := by
  rw [← ENNReal.mul_rpow_of_nonneg, ← ENNReal.mul_rpow_of_nonneg]
  · apply ENNReal.rpow_le_rpow
    calc
      F * ENNReal.ofReal (2 * Real.pi * r) ≤
          (E / ENNReal.ofReal d) *
            ENNReal.ofReal (2 * Real.pi * r) :=
        mul_le_mul_left hF _
      _ ≤ (E / ENNReal.ofReal d) *
            ENNReal.ofReal (4 * Real.pi * d) := by
        apply mul_le_mul_right
        exact ENNReal.ofReal_mono (by nlinarith [Real.pi_pos])
      _ = E * ENNReal.ofReal (4 * Real.pi) := by
        rw [show ENNReal.ofReal (4 * Real.pi * d) =
            ENNReal.ofReal (4 * Real.pi) * ENNReal.ofReal d by
          rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 4 * Real.pi)]]
        rw [div_eq_mul_inv]
        calc
          (E * (ENNReal.ofReal d)⁻¹) *
              (ENNReal.ofReal (4 * Real.pi) * ENNReal.ofReal d) =
            E * (((ENNReal.ofReal d)⁻¹ * ENNReal.ofReal d) *
              ENNReal.ofReal (4 * Real.pi)) := by ac_rfl
          _ = E * ENNReal.ofReal (4 * Real.pi) := by
            rw [ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 hd).ne'
              ENNReal.ofReal_ne_top, one_mul]
    positivity
  · positivity
  · positivity

/--
%%handwave
name:
  Good circles in the inner and outer dyadic annuli
statement:
  Let $0<d\leq1/4$, and let $u\in W^{1,2}(B(0,3))$ be continuous with
  weak differential $Du$.  For each $v\in S^1$ there are radii
  $a\in(d,2d)$ and $b\in(1,2)$ such that, for all
  $\theta,\eta\in S^1$,
  $$
    |u(a\theta)-u(a\eta)|,
    |u(b\theta)-u(b\eta)|
      \leq
    \left(\int_{B(0,3)}\|Du\|^2\right)^{1/2}(4\pi)^{1/2}.
  $$
proof:
  Apply the [physical good-circle theorem](lean:JJMath.Quasiconformal.exists_stereographic_circle_energy_le_average_on_ball) first on $(d,2d)$ and then on $(1,2)$. In each interval, the [dyadic square-root cancellation](lean:JJMath.Quasiconformal.circle_oscillation_factor_le_of_radius_le_two_mul) removes the interval length and the selected radius from the oscillation estimate.
-/
theorem exists_inner_outer_good_circles
    (v : Metric.sphere (0 : ℂ) 1)
    {u : ℂ → ℝ} {du : ℂ → ℂ →L[ℝ] ℝ}
    {d : ℝ} (hd : 0 < d) (hdle : d ≤ 1 / 4)
    (hweak : Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : ℂ) 3) u du)
    (hu : MemLp u 2
      (volume.restrict (Metric.ball (0 : ℂ) 3)))
    (hdu : MemLp du 2
      (volume.restrict (Metric.ball (0 : ℂ) 3)))
    (hu_cont : ContinuousOn u (Metric.ball (0 : ℂ) 3)) :
    ∃ a ∈ Set.Ioo d (2 * d), ∃ b ∈ Set.Ioo (1 : ℝ) 2,
      (∀ θ η : Metric.sphere (0 : ℂ) 1,
        ENNReal.ofReal ‖u (a • (θ : ℂ)) - u (a • (η : ℂ))‖ ≤
          (∫⁻ y in Metric.ball (0 : ℂ) 3,
            ENNReal.ofReal (‖du y‖ ^ 2) ∂volume) ^ ((2 : ℝ)⁻¹) *
              ENNReal.ofReal (4 * Real.pi) ^ ((2 : ℝ)⁻¹)) ∧
      ∀ θ η : Metric.sphere (0 : ℂ) 1,
        ENNReal.ofReal ‖u (b • (θ : ℂ)) - u (b • (η : ℂ))‖ ≤
          (∫⁻ y in Metric.ball (0 : ℂ) 3,
            ENNReal.ofReal (‖du y‖ ^ 2) ∂volume) ^ ((2 : ℝ)⁻¹) *
              ENNReal.ofReal (4 * Real.pi) ^ ((2 : ℝ)⁻¹) := by
  obtain ⟨a, ha, _hafinite, haenergy, haosc⟩ :=
    exists_stereographic_circle_energy_le_average_on_ball
      (S := (3 : ℝ)) (a := d) (b := 2 * d) v (by norm_num) hd
        (by linarith) (by linarith) hweak hu hdu hu_cont
  obtain ⟨b, hb, _hbfinite, hbenergy, hbosc⟩ :=
    exists_stereographic_circle_energy_le_average_on_ball
      (S := (3 : ℝ)) (a := (1 : ℝ)) (b := 2) v (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) hweak hu hdu hu_cont
  refine ⟨a, ha, b, hb, ?_, ?_⟩
  · intro θ η
    exact (haosc θ η).trans
      (circle_oscillation_factor_le_of_radius_le_two_mul
        hd ha.2.le (by simpa [two_mul] using haenergy))
  · intro θ η
    exact (hbosc θ η).trans
      (circle_oscillation_factor_le_of_radius_le_two_mul
        (d := (1 : ℝ)) (by norm_num) (by simpa using hb.2.le)
          (by convert hbenergy using 1 <;> norm_num))

/--
%%handwave
name:
  A radial segment with at most average logarithmic energy
statement:
  Let $0<a<b<3$, and let $u\in W^{1,2}(B(0,3))$ be continuous with weak
  differential $Du$. There is a direction $\theta\in S^1$ such that
  $$
    |u(a\theta)-u(b\theta)|
      \leq
    \left(\frac1{2\pi}\int_{B(0,3)}\|Du\|^2\right)^{1/2}
      (\log b-\log a)^{1/2}.
  $$
proof:
  Dilate the ball of radius three to the unit disk and choose a measurable
  representative of the pulled-back weak differential with radial ACL.
  Polar integration and the fact that the angular measure of $S^1$ is
  $2\pi$ select a ray whose squared radial energy is at most the angular
  average. Apply [weighted radial Cauchy--Schwarz](lean:JJMath.Quasiconformal.lintegral_le_weighted_rpow_two_mul_log); dilation cancels from the logarithmic factor, while [planar Dirichlet energy is dilation invariant](lean:JJMath.Quasiconformal.lintegral_norm_const_smul_comp_sq_restrict_ball_one).
-/
theorem exists_radial_segment_oscillation_le_average_energy
    {u : ℂ → ℝ} {du : ℂ → ℂ →L[ℝ] ℝ}
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 3)
    (hweak : Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : ℂ) 3) u du)
    (hu : MemLp u 2
      (volume.restrict (Metric.ball (0 : ℂ) 3)))
    (hdu : MemLp du 2
      (volume.restrict (Metric.ball (0 : ℂ) 3)))
    (hu_cont : ContinuousOn u (Metric.ball (0 : ℂ) 3)) :
    ∃ θ : Metric.sphere (0 : ℂ) 1,
      ENNReal.ofReal ‖u (a • (θ : ℂ)) - u (b • (θ : ℂ))‖ ≤
        ((∫⁻ y in Metric.ball (0 : ℂ) 3,
          ENNReal.ofReal (‖du y‖ ^ 2) ∂volume) /
            ENNReal.ofReal (2 * Real.pi)) ^ ((2 : ℝ)⁻¹) *
          ENNReal.ofReal (Real.log b - Real.log a) ^ ((2 : ℝ)⁻¹) := by
  let w : ℂ → ℝ := fun z ↦ u ((3 : ℝ) • z)
  let dw : ℂ → ℂ →L[ℝ] ℝ :=
    fun z ↦ (3 : ℝ) • du ((3 : ℝ) • z)
  have hweak3 :
      Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues
        (Metric.ball (0 : ℂ) ((3 : ℝ) * 1)) u du := by
    simpa using hweak
  have hweak_raw := hweak3.comp_smul (by norm_num : (3 : ℝ) ≠ 0)
  rw [Uniformization.preimage_const_smul_ball_zero_of_pos
    (a := (3 : ℝ)) (R := (1 : ℝ)) (by norm_num)] at hweak_raw
  have hwweak : Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : ℂ) 1) w dw := by
    simpa [w, dw] using hweak_raw
  have hw : MemLp w 2
      (volume.restrict (Metric.ball (0 : ℂ) 1)) := by
    simpa [w] using
      Uniformization.memLp_comp_const_smul_of_memLp_restrict_ball_zero
        (a := (3 : ℝ)) (R := (1 : ℝ)) (by norm_num)
          (by simpa using hu)
  have hdw : MemLp dw 2
      (volume.restrict (Metric.ball (0 : ℂ) 1)) := by
    have hcomp :=
      Uniformization.memLp_comp_const_smul_of_memLp_restrict_ball_zero
        (a := (3 : ℝ)) (R := (1 : ℝ)) (by norm_num)
          (by simpa using hdu)
    simpa [dw] using hcomp.const_smul (3 : ℝ)
  have hmaps : Set.MapsTo (fun z : ℂ ↦ (3 : ℝ) • z)
      (Metric.ball 0 1) (Metric.ball 0 3) := by
    intro z hz
    simp only [Metric.mem_ball, dist_zero_right] at hz ⊢
    simpa using
      (mul_lt_mul_of_pos_left hz (by norm_num : (0 : ℝ) < 3))
  have hw_cont : ContinuousOn w (Metric.ball (0 : ℂ) 1) := by
    exact hu_cont.comp
      (continuous_const_smul (3 : ℝ)).continuousOn hmaps
  obtain ⟨G, hG, hG_eq, hG_acl⟩ :=
    Uniformization.scalarWeakSobolev_unit_ball_exists_measurable_weakDifferential_radial_acl_all_segments_of_continuousOn
      hw_cont hwweak hw hdw
  let q := a / 3
  let s := b / 3
  have hq : 0 < q := div_pos ha (by norm_num)
  have hqs : q < s :=
    (div_lt_div_iff_of_pos_right (by norm_num)).2 hab
  have hs : s < 1 := (div_lt_one (by norm_num)).2 hb
  let H : ℂ → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (‖G z‖ ^ 2)
  let F : Metric.sphere (0 : ℂ) 1 → ℝ≥0∞ := fun θ ↦
    ∫⁻ t in Set.Ioo q s,
      ENNReal.ofReal t * H (t • (θ : ℂ)) ∂volume
  have hH : Measurable H := (hG.norm.pow_const 2).ennreal_ofReal
  have hF : AEMeasurable F
      ((volume : Measure ℂ).toSphere) := by
    have hjoint : Measurable (fun p : Metric.sphere (0 : ℂ) 1 × ℝ ↦
        (Set.Ioo q s).indicator
          (fun t ↦ ENNReal.ofReal t * H (t • (p.1 : ℂ))) p.2) := by
      apply Measurable.indicator
      · fun_prop
      · exact measurableSet_Ioo.preimage measurable_snd
    have hjoint' : Measurable (Function.uncurry
        (fun θ : Metric.sphere (0 : ℂ) 1 ↦ fun t : ℝ ↦
          (Set.Ioo q s).indicator
            (fun x ↦ ENNReal.ofReal x * H (x • (θ : ℂ))) t)) := by
      simpa [Function.uncurry] using hjoint
    have hFi : AEMeasurable
        (fun θ : Metric.sphere (0 : ℂ) 1 ↦
          ∫⁻ t : ℝ, (Set.Ioo q s).indicator
            (fun x ↦ ENNReal.ofReal x * H (x • (θ : ℂ))) t ∂volume)
        ((volume : Measure ℂ).toSphere) :=
      (hjoint'.lintegral_prod_right
        (ν := (volume : Measure ℝ))).aemeasurable
    convert hFi using 1
    funext θ
    rw [lintegral_indicator measurableSet_Ioo]
  let μS : Measure (Metric.sphere (0 : ℂ) 1) :=
    (volume : Measure ℂ).toSphere
  have hmass : μS Set.univ = ENNReal.ofReal (2 * Real.pi) := by
    simpa [μS] using complex_toSphere_apply_univ
  have hμ : μS ≠ 0 := by
    intro hzero
    have hz : μS Set.univ = 0 := by rw [hzero]; simp
    rw [hmass] at hz
    exact (ENNReal.ofReal_pos.2
      (mul_pos (by norm_num) Real.pi_pos)).ne' hz
  let N : Set (Metric.sphere (0 : ℂ) 1) :=
    {θ | ¬ ∀ r t : ℝ, 0 < r → r < t → t < 1 →
      ENNReal.ofReal ‖w (r • (θ : ℂ)) - w (t • (θ : ℂ))‖ ≤
        ∫⁻ x in {x : ℝ | r < x ∧ x < t},
          ENNReal.ofReal ‖G (x • (θ : ℂ)) (θ : ℂ)‖ ∂volume}
  have hN : μS N = 0 := by
    exact ae_iff.mp (by simpa [μS, N] using hG_acl)
  obtain ⟨θ, hθN, hθavg⟩ :=
    exists_notMem_null_le_laverage hμ hF hN
  have htotal : (∫⁻ η : Metric.sphere (0 : ℂ) 1, F η ∂μS) ≤
      ∫⁻ z in Metric.ball (0 : ℂ) 1, H z ∂volume := by
    let Hball : ℂ → ℝ≥0∞ := (Metric.ball (0 : ℂ) 1).indicator H
    have hHball : Measurable Hball := hH.indicator measurableSet_ball
    have hp := lintegral_toSphere_weighted_Ioo_le_lintegral_complex
      (b := s) hq Hball hHball
    have heq : (∫⁻ η : Metric.sphere (0 : ℂ) 1,
          ∫⁻ t in Set.Ioo q s,
            ENNReal.ofReal t * H (t • (η : ℂ)) ∂volume ∂μS) =
        ∫⁻ η : Metric.sphere (0 : ℂ) 1,
          ∫⁻ t in Set.Ioo q s,
            ENNReal.ofReal t * Hball (t • (η : ℂ)) ∂volume ∂μS := by
      refine lintegral_congr fun η ↦ ?_
      refine setLIntegral_congr_fun measurableSet_Ioo fun t ht ↦ ?_
      have htpos : 0 < t := hq.trans ht.1
      have htball : t • (η : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
        simp [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs,
          abs_of_pos htpos, norm_eq_of_mem_sphere η, ht.2.trans hs]
      rw [show Hball (t • (η : ℂ)) = H (t • (η : ℂ)) by
        exact Set.indicator_of_mem htball H]
    calc
      (∫⁻ η : Metric.sphere (0 : ℂ) 1, F η ∂μS) =
          ∫⁻ η : Metric.sphere (0 : ℂ) 1,
            ∫⁻ t in Set.Ioo q s,
              ENNReal.ofReal t * H (t • (η : ℂ)) ∂volume ∂μS := by rfl
      _ = _ := heq
      _ ≤ ∫⁻ z : ℂ, Hball z ∂volume := hp
      _ = ∫⁻ z in Metric.ball (0 : ℂ) 1, H z ∂volume := by
        simpa [Hball] using lintegral_indicator measurableSet_ball H
  have hGenergy : (∫⁻ z in Metric.ball (0 : ℂ) 1, H z ∂volume) =
      ∫⁻ y in Metric.ball (0 : ℂ) 3,
        ENNReal.ofReal (‖du y‖ ^ 2) ∂volume := by
    calc
      (∫⁻ z in Metric.ball (0 : ℂ) 1, H z ∂volume) =
          ∫⁻ z in Metric.ball (0 : ℂ) 1,
            ENNReal.ofReal (‖dw z‖ ^ 2) ∂volume := by
        apply lintegral_congr_ae
        filter_upwards [hG_eq] with z hz
        simp [H, hz]
      _ = _ := by
        simpa [dw] using
          lintegral_norm_const_smul_comp_sq_restrict_ball_one
            (by norm_num : (0 : ℝ) < 3) du hdu.1.aemeasurable
  have hθenergy : F θ ≤
      (∫⁻ y in Metric.ball (0 : ℂ) 3,
        ENNReal.ofReal (‖du y‖ ^ 2) ∂volume) /
          ENNReal.ofReal (2 * Real.pi) := by
    rw [laverage_eq, hmass] at hθavg
    exact hθavg.trans
      (ENNReal.div_le_div_right (htotal.trans_eq hGenergy) _)
  have hθacl := (not_not.mp hθN) q s hq hqs hs
  have hdir :
      (∫⁻ t in Set.Ioo q s,
          ENNReal.ofReal ‖G (t • (θ : ℂ)) (θ : ℂ)‖ ∂volume) ≤
        ∫⁻ t in Set.Ioo q s,
          ENNReal.ofReal ‖G (t • (θ : ℂ))‖ ∂volume := by
    apply setLIntegral_mono' measurableSet_Ioo
    intro t _ht
    apply ENNReal.ofReal_mono
    simpa [norm_eq_of_mem_sphere θ] using
      (G (t • (θ : ℂ))).le_opNorm (θ : ℂ)
  have hmeas : AEMeasurable
      (fun t : ℝ ↦ ENNReal.ofReal ‖G (t • (θ : ℂ))‖)
      (volume.restrict (Set.Ioo q s)) := by
    exact ((hG.comp (by fun_prop)).norm.ennreal_ofReal).aemeasurable
  have hcs := lintegral_le_weighted_rpow_two_mul_log hq hqs hmeas
  have hcs' :
      (∫⁻ t in Set.Ioo q s,
          ENNReal.ofReal ‖G (t • (θ : ℂ))‖ ∂volume) ≤
        F θ ^ ((2 : ℝ)⁻¹) *
          ENNReal.ofReal (Real.log s - Real.log q) ^ ((2 : ℝ)⁻¹) := by
    simpa [F, H, ENNReal.rpow_two,
      ENNReal.ofReal_pow (norm_nonneg _) 2] using hcs
  refine ⟨θ, ?_⟩
  have hchain := hθacl.trans (hdir.trans hcs')
  have hscale_a : (3 : ℝ) • (q • (θ : ℂ)) = a • (θ : ℂ) := by
    rw [smul_smul]
    congr 1
    dsimp [q]
    ring
  have hscale_b : (3 : ℝ) • (s • (θ : ℂ)) = b • (θ : ℂ) := by
    rw [smul_smul]
    congr 1
    dsimp [s]
    ring
  change ENNReal.ofReal
      ‖u ((3 : ℝ) • (q • (θ : ℂ))) -
        u ((3 : ℝ) • (s • (θ : ℂ)))‖ ≤ _ at hchain
  rw [hscale_a, hscale_b] at hchain
  have hlog : Real.log s - Real.log q = Real.log b - Real.log a := by
    dsimp [q, s]
    rw [Real.log_div (ha.trans hab).ne' (by norm_num : (3 : ℝ) ≠ 0),
      Real.log_div ha.ne' (by norm_num : (3 : ℝ) ≠ 0)]
    ring
  rw [hlog] at hchain
  refine hchain.trans ?_
  exact mul_le_mul_left
    (ENNReal.rpow_le_rpow hθenergy (by positivity)) _

/--
%%handwave
name:
  Removing the square root from a linear energy estimate
statement:
  Let $E,C\in[0,\infty]$ with $0<C<\infty$. If
  $$
    1\leq E^{1/2}C,
  $$
  then
  $$
    C^{-2}\leq E.
  $$
proof:
  Write $C=(C^2)^{1/2}$ and apply the [weighted square-root cancellation](lean:JJMath.Quasiconformal.inv_le_of_one_le_rpow_half_mul_rpow_half) with weight $C^2$.
-/
theorem inv_sq_le_of_one_le_rpow_half_mul
    {E C : ℝ≥0∞} (hC : 0 < C) (hCtop : C ≠ ∞)
    (h : 1 ≤ E ^ ((2 : ℝ)⁻¹) * C) :
    (C ^ (2 : ℕ))⁻¹ ≤ E := by
  apply inv_le_of_one_le_rpow_half_mul_rpow_half
    (by positivity) (by simp [pow_two, ENNReal.mul_eq_top, hCtop])
  have hroot : (C ^ (2 : ℕ)) ^ ((2 : ℝ)⁻¹) = C := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  rw [hroot]
  exact h

/--
%%handwave
name:
  Normalized positive real ray
statement:
  This is the closed set
  $[1,\infty)\subset\mathbb R\subset\mathbb C$.
-/
def planarUnitRay : Set ℂ :=
  ((↑) : ℝ → ℂ) '' Set.Ici 1

/--
%%handwave
name:
  Geometry of the normalized positive ray
statement:
  The set $[1,\infty)\subset\mathbb R\subset\mathbb C$ is closed and
  connected, contains $1$, and contains points of arbitrarily large complex
  modulus.
proof:
  The real half-line $[1,\infty)$ is closed and connected.  Its standard
  inclusion into $\mathbb C$ is a closed embedding, so these properties pass
  to its image.  The real point $\max\{R,1\}$ has modulus at least $R$.
-/
theorem planarUnitRay_properties :
    IsClosed planarUnitRay ∧
      IsConnected planarUnitRay ∧
      (1 : ℂ) ∈ planarUnitRay ∧
      ∀ R : ℝ, ∃ z ∈ planarUnitRay, R ≤ ‖z‖ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Complex.isUniformEmbedding_ofReal.isClosedEmbedding.isClosedMap
      _ isClosed_Ici
  · exact isConnected_Ici.image ((↑) : ℝ → ℂ)
      Complex.continuous_ofReal.continuousOn
  · exact ⟨1, Set.mem_Ici.mpr le_rfl, by simp⟩
  · intro R
    let T := max R 1
    refine ⟨(T : ℂ), ⟨T, Set.mem_Ici.mpr (le_max_right _ _), rfl⟩, ?_⟩
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    · exact le_max_left _ _
    · exact zero_le_one.trans (le_max_right _ _)

/--
%%handwave
name:
  Whole-plane homeomorphisms preserve unboundedness
statement:
  Let $f:\mathbb C\to\mathbb C$ be a homeomorphism and suppose
  $E\subset\mathbb C$ contains points of arbitrarily large modulus.  Then
  $f(E)$ also contains points of arbitrarily large modulus.
proof:
  The inverse image of every closed target disk is compact and hence bounded.
  Choose a point of $E$ outside that bounded inverse image.  Its image lies
  outside the target disk.
-/
theorem Homeomorph.image_unbounded
    (f : ℂ ≃ₜ ℂ) {E : Set ℂ}
    (hE : ∀ R : ℝ, ∃ z ∈ E, R ≤ ‖z‖) :
    ∀ S : ℝ, ∃ z ∈ f '' E, S ≤ ‖z‖ := by
  intro S
  obtain ⟨B, hB⟩ :=
    ((isCompact_closedBall (0 : ℂ) S).image
      f.symm.continuous).isBounded.subset_closedBall 0
  obtain ⟨x, hxE, hxnorm⟩ := hE (|B| + 1)
  have hBlt : B < ‖x‖ := by
    linarith [le_abs_self B]
  refine ⟨f x, ⟨x, hxE, rfl⟩, ?_⟩
  by_contra hnot
  have hfxball : f x ∈ Metric.closedBall (0 : ℂ) S := by
    simpa [Metric.mem_closedBall, dist_zero_right] using le_of_not_ge hnot
  have hximage : x ∈ f.symm '' Metric.closedBall (0 : ℂ) S := by
    exact ⟨f x, hfxball, f.symm_apply_apply x⟩
  have hxball := hB hximage
  have hxnorm_le : ‖x‖ ≤ B := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hxball
  linarith

/--
%%handwave
name:
  Normalized outer continuum under a whole-plane homeomorphism
statement:
  If $f:\mathbb C\to\mathbb C$ is a homeomorphism fixing $1$, then
  $f([1,\infty))$ is closed and connected, contains $1$, and is unbounded.
proof:
  A homeomorphism preserves closedness and connectedness, the fixed-point
  identity supplies $1$, and [whole-plane homeomorphisms preserve unboundedness](lean:JJMath.Quasiconformal.Homeomorph.image_unbounded).
-/
theorem Homeomorph.image_planarUnitRay_properties
    (f : ℂ ≃ₜ ℂ) (hone : f 1 = 1) :
    IsClosed (f '' planarUnitRay) ∧
      IsConnected (f '' planarUnitRay) ∧
      (1 : ℂ) ∈ f '' planarUnitRay ∧
      ∀ R : ℝ, ∃ z ∈ f '' planarUnitRay, R ≤ ‖z‖ := by
  refine ⟨f.isClosedMap _ planarUnitRay_properties.1,
    planarUnitRay_properties.2.1.image f f.continuous.continuousOn,
    ⟨1, planarUnitRay_properties.2.2.1, hone⟩, ?_⟩
  exact Homeomorph.image_unbounded f planarUnitRay_properties.2.2.2

/--
%%handwave
name:
  Normalized inner disk under a whole-plane homeomorphism
statement:
  If $f:\mathbb C\to\mathbb C$ is a homeomorphism fixing $0$ and $r\geq0$,
  then $f(\overline B(0,r))$ is compact and connected and contains $0$.
proof:
  A closed disk is compact and connected, homeomorphisms preserve both
  properties, and the fixed-point identity supplies $0$.
-/
theorem Homeomorph.image_closedBall_zero_properties
    (f : ℂ ≃ₜ ℂ) (hzero : f 0 = 0) {r : ℝ} (hr : 0 ≤ r) :
    IsCompact (f '' Metric.closedBall 0 r) ∧
      IsConnected (f '' Metric.closedBall 0 r) ∧
      (0 : ℂ) ∈ f '' Metric.closedBall 0 r := by
  refine ⟨(isCompact_closedBall (0 : ℂ) r).image f.continuous,
    (Metric.isConnected_closedBall hr).image f f.continuous.continuousOn,
    ⟨0, ?_, hzero⟩⟩
  simpa [Metric.mem_closedBall]

/--
%%handwave
name:
  Outer normalized continuum in the finite chart
statement:
  Let $F:\widehat{\mathbb C}\to\widehat{\mathbb C}$ fix $0$, $1$, and
  $\infty$, and let $f:\mathbb C\to\mathbb C$ be its finite-chart
  homeomorphism.  Then $f([1,\infty))$ is closed and connected, contains
  $1$, and contains points of arbitrarily large modulus.
proof:
  The source ray has all four properties.  A homeomorphism preserves closed
  and connected sets, normalization preserves the marked point $1$, and
  [whole-plane homeomorphisms preserve unboundedness](lean:JJMath.Quasiconformal.Homeomorph.image_unbounded).
-/
theorem IsNormalizedRiemannSphereHomeomorph.finiteChart_image_planarUnitRay_properties
    {F : RiemannSphere ≃ₜ RiemannSphere}
    (hF : IsNormalizedRiemannSphereHomeomorph F) :
    IsClosed (riemannSphereFiniteChartHomeomorph F hF.2.2 '' planarUnitRay) ∧
      IsConnected
        (riemannSphereFiniteChartHomeomorph F hF.2.2 '' planarUnitRay) ∧
      (1 : ℂ) ∈
        riemannSphereFiniteChartHomeomorph F hF.2.2 '' planarUnitRay ∧
      ∀ R : ℝ, ∃ z ∈
        riemannSphereFiniteChartHomeomorph F hF.2.2 '' planarUnitRay,
        R ≤ ‖z‖ := by
  let f := riemannSphereFiniteChartHomeomorph F hF.2.2
  have hfix := hF.finiteChart_fixes_zero_one
  refine ⟨f.isClosedMap _ planarUnitRay_properties.1, ?_, ?_, ?_⟩
  · exact planarUnitRay_properties.2.1.image f f.continuous.continuousOn
  · exact ⟨1, planarUnitRay_properties.2.2.1, hfix.2⟩
  · exact Homeomorph.image_unbounded f planarUnitRay_properties.2.2.2

/--
%%handwave
name:
  Inner normalized continuum in the finite chart
statement:
  Let $F:\widehat{\mathbb C}\to\widehat{\mathbb C}$ fix $0$, $1$, and
  $\infty$, and let $f$ be its finite-chart homeomorphism.  If $r\geq0$,
  then $f(\overline B(0,r))$ is a compact connected set containing $0$.
proof:
  The closed disk is compact and connected.  Its image under the
  whole-plane homeomorphism remains compact and connected, and it contains
  $f(0)=0$ by normalization.
-/
theorem IsNormalizedRiemannSphereHomeomorph.finiteChart_image_closedBall_properties
    {F : RiemannSphere ≃ₜ RiemannSphere}
    (hF : IsNormalizedRiemannSphereHomeomorph F)
    {r : ℝ} (hr : 0 ≤ r) :
    IsCompact
        (riemannSphereFiniteChartHomeomorph F hF.2.2 ''
          Metric.closedBall 0 r) ∧
      IsConnected
        (riemannSphereFiniteChartHomeomorph F hF.2.2 ''
          Metric.closedBall 0 r) ∧
      (0 : ℂ) ∈
        riemannSphereFiniteChartHomeomorph F hF.2.2 ''
          Metric.closedBall 0 r := by
  let f := riemannSphereFiniteChartHomeomorph F hF.2.2
  have hfix := hF.finiteChart_fixes_zero_one
  refine ⟨(isCompact_closedBall (0 : ℂ) r).image f.continuous, ?_, ?_⟩
  · exact (Metric.isConnected_closedBall hr).image f f.continuous.continuousOn
  · refine ⟨0, ?_, hfix.1⟩
    simpa [Metric.mem_closedBall]

/--
%%handwave
name:
  The normalized ray condenser is bounded by the round ring
statement:
  For every $r\in\mathbb R$,
  $$
    \operatorname{cap}_{\mathbb C}
      \bigl(\overline B(0,r),[1,\infty)\bigr)
      \leq \operatorname{cap}(r,1).
  $$
proof:
  The positive ray $[1,\infty)$ lies in the exterior
  $\mathbb C\setminus B(0,1)$.  Enlarge the outer plate and apply monotonicity
  of condenser capacity in the plates.
-/
theorem planarCondenserCapacity_closedBall_planarUnitRay_le_planarRingCapacity
    (r : ℝ) :
    planarCondenserCapacity Set.univ (Metric.closedBall (0 : ℂ) r)
        planarUnitRay ≤ planarRingCapacity r 1 := by
  apply planarCondenserCapacity_mono_plates subset_rfl
  rintro z ⟨t, ht, rfl⟩
  simp only [Set.mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  · exact ht
  · exact zero_le_one.trans ht

/--
%%handwave
name:
  Round-ring capacity tends to zero at exponentially small radii
statement:
  As $n\to\infty$ through the natural numbers,
  $$
    \operatorname{cap}(e^{-n},1)\longrightarrow0.
  $$
proof:
  For every $n\geq1$, the exact round-ring formula gives
  $$
    \operatorname{cap}(e^{-n},1)=\frac{2\pi}{n}.
  $$
  The real sequence on the right tends to zero, and the embedding into the
  extended nonnegative reals is continuous at zero.
-/
theorem tendsto_planarRingCapacity_exp_neg_nat : Filter.Tendsto
    (fun n : ℕ ↦ planarRingCapacity (Real.exp (-(n : ℝ))) 1)
    Filter.atTop (nhds 0) := by
  have heq : ∀ᶠ n : ℕ in Filter.atTop,
      planarRingCapacity (Real.exp (-(n : ℝ))) 1 =
        ENNReal.ofReal (2 * Real.pi / (n : ℝ)) := by
    filter_upwards [Filter.eventually_atTop.2 ⟨1, fun n hn ↦ hn⟩] with n hn
    have hnpos : 0 < (n : ℝ) := by
      exact_mod_cast hn
    have hr : 0 < Real.exp (-(n : ℝ)) := Real.exp_pos _
    have hr1 : Real.exp (-(n : ℝ)) < 1 := by
      rw [Real.exp_lt_one_iff]
      linarith
    rw [planarRingCapacity_eq_logarithmicEnergy hr hr1]
    congr 2
    rw [Real.log_one, Real.log_exp]
    ring
  have hreal : Filter.Tendsto
      (fun n : ℕ ↦ 2 * Real.pi / (n : ℝ))
      Filter.atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (2 * Real.pi)
  have henn := ENNReal.tendsto_ofReal hreal
  have hcongr := henn.congr' (heq.mono fun _ hn ↦ hn.symm)
  simpa using hcongr

/--
%%handwave
name:
  A fixed finite factor preserves vanishing ring capacity
statement:
  For every real $K$,
  $$
    K_+\operatorname{cap}(e^{-n},1)\longrightarrow0
    \qquad(n\to\infty),
  $$
  where $K_+=\max\{K,0\}$ is represented in the extended nonnegative
  reals.
proof:
  The ring capacities tend to zero.  Multiplication by the finite extended
  nonnegative number associated to $K$ is continuous at zero.
-/
theorem tendsto_ofReal_mul_planarRingCapacity_exp_neg_nat (K : ℝ) :
    Filter.Tendsto
      (fun n : ℕ ↦
        ENNReal.ofReal K * planarRingCapacity (Real.exp (-(n : ℝ))) 1)
      Filter.atTop (nhds 0) := by
  have h := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal K)
    tendsto_planarRingCapacity_exp_neg_nat (Or.inr ENNReal.ofReal_ne_top)
  simpa using h

/--
%%handwave
name:
  An exponentially small ring has arbitrarily small distorted capacity
statement:
  If $c>0$ is an extended nonnegative number and $K\in\mathbb R$, then there
  is an integer $n\geq1$ such that
  $$
    K_+\operatorname{cap}(e^{-n},1)<c.
  $$
proof:
  Apply convergence of $K_+\operatorname{cap}(e^{-n},1)$ to zero to the
  neighborhood $[0,c)$ and then increase the resulting index to at least
  one.
-/
theorem exists_nat_ofReal_mul_planarRingCapacity_exp_neg_lt
    (K : ℝ) {c : ℝ≥0∞} (hc : 0 < c) :
    ∃ n : ℕ, 1 ≤ n ∧
      ENNReal.ofReal K * planarRingCapacity (Real.exp (-(n : ℝ))) 1 < c := by
  have hev : ∀ᶠ n : ℕ in Filter.atTop,
      ENNReal.ofReal K * planarRingCapacity (Real.exp (-(n : ℝ))) 1 < c :=
    tendsto_ofReal_mul_planarRingCapacity_exp_neg_nat K (Iio_mem_nhds hc)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  let n := max N 1
  exact ⟨n, le_max_right _ _, hN n (le_max_left _ _)⟩

/--
%%handwave
name:
  Capacity upper bound for arbitrary finite-chart image plates
statement:
  Let $F:\widehat{\mathbb C}\to\widehat{\mathbb C}$ be normalized and
  $K$-quasiconformal, and let $f:\mathbb C\to\mathbb C$ be its finite-chart
  homeomorphism. For all $E_0,E_1\subseteq\mathbb C$,
  $$
    \operatorname{cap}_{\mathbb C}(f(E_0),f(E_1))
      \leq K\operatorname{cap}_{\mathbb C}(E_0,E_1).
  $$
proof:
  The finite source and target charts are both the whole plane because
  $F(\infty)=\infty$. Apply planar quasiconformal capacity distortion and
  identify the ambient chart map with $f$.
-/
theorem IsKQuasiconformalRiemannSphere.finiteChart_image_condenser_capacity_le
    {K : ℝ} {F : RiemannSphere ≃ₜ RiemannSphere}
    (hqc : IsKQuasiconformalRiemannSphere K F)
    (hF : IsNormalizedRiemannSphereHomeomorph F)
    (E₀ E₁ : Set ℂ) :
    planarCondenserCapacity Set.univ
        (riemannSphereFiniteChartHomeomorph F hF.2.2 '' E₀)
        (riemannSphereFiniteChartHomeomorph F hF.2.2 '' E₁) ≤
      ENNReal.ofReal K * planarCondenserCapacity Set.univ E₀ E₁ := by
  have hsource :=
    riemannSphere_finiteChartRepresentation_source_eq_univ_of_map_infty
      F hF.2.2
  have htarget :=
    riemannSphere_finiteChartRepresentation_target_eq_univ_of_map_infty
      F hF.2.2
  have hE₀ : E₀ ⊆
      (riemannSphereChartRepresentation F .finite .finite).source := by
    rw [hsource]
    exact Set.subset_univ _
  have hE₁ : E₁ ⊆
      (riemannSphereChartRepresentation F .finite .finite).source := by
    rw [hsource]
    exact Set.subset_univ _
  have hd := (hqc .finite .finite).planarCondenserCapacity_distortion hE₀ hE₁
  have hd1 : planarCondenserCapacity Set.univ
        (ambientMap (riemannSphereChartHomeomorph F .finite .finite) '' E₀)
        (ambientMap (riemannSphereChartHomeomorph F .finite .finite) '' E₁) ≤
      ENNReal.ofReal K * planarCondenserCapacity Set.univ E₀ E₁ := by
    simpa only [hsource, htarget] using hd.1
  simp_rw [ambientMap_finiteChartHomeomorph_apply F hF.2.2] at hd1
  exact hd1

/--
%%handwave
name:
  Capacity upper bound for arbitrary reciprocal-chart image plates
statement:
  Let $F:\widehat{\mathbb C}\to\widehat{\mathbb C}$ be normalized and
  $K$-quasiconformal, and let $g:\mathbb C\to\mathbb C$ be its
  reciprocal-chart homeomorphism. For all $E_0,E_1\subseteq\mathbb C$,
  $$
    \operatorname{cap}_{\mathbb C}(g(E_0),g(E_1))
      \leq K\operatorname{cap}_{\mathbb C}(E_0,E_1).
  $$
proof:
  Because $F(0)=0$, the reciprocal source and target chart domains are both
  the whole plane. Apply planar capacity distortion to the
  reciprocal-to-reciprocal representation and identify its ambient map with
  $g$.
-/
theorem IsKQuasiconformalRiemannSphere.infinityChart_image_condenser_capacity_le
    {K : ℝ} {F : RiemannSphere ≃ₜ RiemannSphere}
    (hqc : IsKQuasiconformalRiemannSphere K F)
    (hF : IsNormalizedRiemannSphereHomeomorph F)
    (E₀ E₁ : Set ℂ) :
    planarCondenserCapacity Set.univ
        (riemannSphereInfinityChartHomeomorph F hF.1 '' E₀)
        (riemannSphereInfinityChartHomeomorph F hF.1 '' E₁) ≤
      ENNReal.ofReal K * planarCondenserCapacity Set.univ E₀ E₁ := by
  have hsource :=
    riemannSphere_infinityChartRepresentation_source_eq_univ_of_map_zero
      F hF.1
  have htarget :=
    riemannSphere_infinityChartRepresentation_target_eq_univ_of_map_zero
      F hF.1
  have hE₀ : E₀ ⊆
      (riemannSphereChartRepresentation F .infinity .infinity).source := by
    rw [hsource]
    exact Set.subset_univ _
  have hE₁ : E₁ ⊆
      (riemannSphereChartRepresentation F .infinity .infinity).source := by
    rw [hsource]
    exact Set.subset_univ _
  have hd := (hqc .infinity .infinity).planarCondenserCapacity_distortion
    hE₀ hE₁
  have hd1 : planarCondenserCapacity Set.univ
        (ambientMap (riemannSphereChartHomeomorph F .infinity .infinity) '' E₀)
        (ambientMap (riemannSphereChartHomeomorph F .infinity .infinity) '' E₁) ≤
      ENNReal.ofReal K * planarCondenserCapacity Set.univ E₀ E₁ := by
    simpa only [hsource, htarget] using hd.1
  simp_rw [ambientMap_infinityChartHomeomorph_apply F hF.1] at hd1
  exact hd1

/--
%%handwave
name:
  Capacity upper bound for a normalized quasiconformal image disk
statement:
  Let $F:\widehat{\mathbb C}\to\widehat{\mathbb C}$ be a normalized
  $K$-quasiconformal homeomorphism and let $f$ be its finite-chart
  homeomorphism.  For every $r\in\mathbb R$,
  $$
    \operatorname{cap}_{\mathbb C}
      \bigl(f(\overline B(0,r)),f([1,\infty))\bigr)
      \leq K\operatorname{cap}(r,1).
  $$
proof:
  Since $F(\infty)=\infty$, the finite-to-finite chart has source and target
  equal to all of $\mathbb C$.  Apply the
  [quasiconformal capacity-distortion inequality](lean:JJMath.Quasiconformal.IsKQuasiconformalBetween.planarCondenserCapacity_distortion),
  identify its ambient chart representative with $f$, and use that the ray
  condenser has capacity at most the concentric ring capacity.
-/
theorem IsKQuasiconformalRiemannSphere.finiteChart_image_closedBall_planarUnitRay_capacity_le
    {K : ℝ} {F : RiemannSphere ≃ₜ RiemannSphere}
    (hqc : IsKQuasiconformalRiemannSphere K F)
    (hF : IsNormalizedRiemannSphereHomeomorph F) (r : ℝ) :
    planarCondenserCapacity Set.univ
        (riemannSphereFiniteChartHomeomorph F hF.2.2 ''
          Metric.closedBall 0 r)
        (riemannSphereFiniteChartHomeomorph F hF.2.2 '' planarUnitRay) ≤
      ENNReal.ofReal K * planarRingCapacity r 1 := by
  have hsource :=
    riemannSphere_finiteChartRepresentation_source_eq_univ_of_map_infty
      F hF.2.2
  have htarget :=
    riemannSphere_finiteChartRepresentation_target_eq_univ_of_map_infty
      F hF.2.2
  have hball_source : Metric.closedBall (0 : ℂ) r ⊆
      (riemannSphereChartRepresentation F .finite .finite).source := by
    rw [hsource]
    exact Set.subset_univ _
  have hray_source : planarUnitRay ⊆
      (riemannSphereChartRepresentation F .finite .finite).source := by
    rw [hsource]
    exact Set.subset_univ _
  have hd := (hqc .finite .finite).planarCondenserCapacity_distortion
    (E₀ := Metric.closedBall (0 : ℂ) r) (E₁ := planarUnitRay)
    hball_source hray_source
  have hd1 : planarCondenserCapacity Set.univ
        (ambientMap (riemannSphereChartHomeomorph F .finite .finite) ''
          Metric.closedBall (0 : ℂ) r)
        (ambientMap (riemannSphereChartHomeomorph F .finite .finite) ''
          planarUnitRay) ≤
      ENNReal.ofReal K * planarCondenserCapacity Set.univ
        (Metric.closedBall (0 : ℂ) r) planarUnitRay := by
    simpa only [hsource, htarget] using hd.1
  simp_rw [ambientMap_finiteChartHomeomorph_apply F hF.2.2] at hd1
  exact hd1.trans (mul_le_mul_right
    (planarCondenserCapacity_closedBall_planarUnitRay_le_planarRingCapacity r)
    (ENNReal.ofReal K))

/--
%%handwave
name:
  A connected planar set meets every intermediate circle
statement:
  Let $E\subset\mathbb C$ be connected and let $x,y\in E$.  If
  $|x|\leq r\leq |y|$, then there is $z\in E$ with $|z|=r$.
proof:
  The modulus is continuous, so its image on the connected set $E$ is an
  interval.  This interval contains $|x|$ and $|y|$, hence also $r$.
-/
theorem IsConnected.exists_mem_norm_eq_of_norm_le
    {E : Set ℂ} (hE : IsConnected E)
    {x y : ℂ} (hx : x ∈ E) (hy : y ∈ E)
    {r : ℝ} (hxr : ‖x‖ ≤ r) (hry : r ≤ ‖y‖) :
    ∃ z ∈ E, ‖z‖ = r := by
  exact hE.isPreconnected.intermediate_value hx hy
    continuous_norm.continuousOn ⟨hxr, hry⟩

/--
%%handwave
name:
  The inner normalized continuum meets its intermediate circles
statement:
  Let $E\subset\mathbb C$ be connected, contain $0$, and contain a point of
  modulus at least $\delta$.  For every $r\in[0,\delta]$ there is $z\in E$
  with $|z|=r$.
proof:
  Choose $y\in E$ with $|y|\geq\delta$.  Then
  $|0|=0\leq r\leq\delta\leq|y|$, and apply the intermediate-circle
  property for connected sets.
-/
theorem IsConnected.exists_mem_norm_eq_of_zero_mem_of_reaches
    {E : Set ℂ} (hE : IsConnected E)
    (hzero : 0 ∈ E) {δ : ℝ}
    (hreaches : ∃ z ∈ E, δ ≤ ‖z‖)
    {r : ℝ} (hr0 : 0 ≤ r) (hrδ : r ≤ δ) :
    ∃ z ∈ E, ‖z‖ = r := by
  obtain ⟨y, hyE, hδy⟩ := hreaches
  exact IsConnected.exists_mem_norm_eq_of_norm_le hE hzero hyE
    (by simpa) (hrδ.trans hδy)

/--
%%handwave
name:
  The outer normalized continuum meets every circle of radius at least one
statement:
  Let $E\subset\mathbb C$ be connected, contain $1$, and contain points of
  arbitrarily large modulus.  For every $r\geq1$ there is $z\in E$ with
  $|z|=r$.
proof:
  Choose $y\in E$ with $|y|\geq r$.  Since $|1|=1\leq r$, the
  intermediate-circle property for connected sets gives the required point.
-/
theorem IsConnected.exists_mem_norm_eq_of_one_mem_of_unbounded
    {E : Set ℂ} (hE : IsConnected E)
    (hone : (1 : ℂ) ∈ E)
    (hunbounded : ∀ R : ℝ, ∃ z ∈ E, R ≤ ‖z‖)
    {r : ℝ} (h1r : 1 ≤ r) :
    ∃ z ∈ E, ‖z‖ = r := by
  obtain ⟨y, hyE, hry⟩ := hunbounded r
  exact IsConnected.exists_mem_norm_eq_of_norm_le hE hone hyE (by simpa) hry

/--
%%handwave
name:
  Inner dyadic scale for normalized continuum separation
statement:
  For $\delta\in\mathbb R$, define
  $$
    d(\delta)=\min\{\delta/2,1/4\}.
  $$
  The cap by $1/4$ keeps the doubled circle inside radius $1/2$.
-/
def normalizedContinuumInnerRadius (δ : ℝ) : ℝ :=
  min (δ / 2) (1 / 4)

/--
%%handwave
name:
  Bounds for the normalized-continuum inner radius
statement:
  If $\delta>0$ and $d=\min\{\delta/2,1/4\}$, then
  $$
    d>0,\qquad 2d\leq\delta,\qquad 2d\leq\frac12.
  $$
proof:
  Both entries in the minimum are positive.  The other two inequalities
  follow by comparing the minimum with each entry and multiplying by two.
-/
theorem normalizedContinuumInnerRadius_bounds
    {δ : ℝ} (hδ : 0 < δ) :
    0 < normalizedContinuumInnerRadius δ ∧
      2 * normalizedContinuumInnerRadius δ ≤ δ ∧
      2 * normalizedContinuumInnerRadius δ ≤ 1 / 2 := by
  dsimp [normalizedContinuumInnerRadius]
  refine ⟨lt_min (by linarith) (by norm_num), ?_, ?_⟩
  · linarith [min_le_left (δ / 2) (1 / 4)]
  · linarith [min_le_right (δ / 2) (1 / 4)]

/--
%%handwave
name:
  Uniform capacity separation for normalized planar continua
statement:
  For every $\delta>0$ there is a constant $c(\delta)>0$ with the following
  property.  Let $E_0\subset\mathbb C$ be a compact connected set containing
  $0$ and some $z$ with $|z|\geq\delta$.  Let $E_1\subset\mathbb C$ be a
  closed connected set containing $1$ and points of arbitrarily large
  modulus.  Then
  $$
    c(\delta)\leq
      \operatorname{cap}_{\mathbb C}(E_0,E_1).
  $$
proof:
  Put $d=\min(\delta/2,1/4)$.  For an arbitrary admissible potential of
  energy $E$, the [two dyadic annuli contain circles whose full oscillations are at most $E^{1/2}(4\pi)^{1/2}$](lean:JJMath.Quasiconformal.exists_inner_outer_good_circles).  Connectedness forces the inner plate to meet the first circle and the outer plate to meet the second.  The [radial averaging estimate supplies a ray whose change between the two circles is bounded by the square root of its logarithmic energy average](lean:JJMath.Quasiconformal.exists_radial_segment_oscillation_le_average_energy).  The triangle inequality therefore gives $1\leq E^{1/2}C(d)$ for an explicit finite positive $C(d)$, whence $C(d)^{-2}\leq E$.  Taking the infimum over all admissible potentials proves the claim.
-/
theorem exists_pos_le_planarCondenserCapacity_of_normalized_continua
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ≥0∞, 0 < c ∧
      ∀ (E₀ E₁ : Set ℂ),
        IsCompact E₀ →
        IsConnected E₀ →
        0 ∈ E₀ →
        (∃ z ∈ E₀, δ ≤ ‖z‖) →
        IsClosed E₁ →
        IsConnected E₁ →
        1 ∈ E₁ →
        (∀ R : ℝ, ∃ z ∈ E₁, R ≤ ‖z‖) →
        c ≤ planarCondenserCapacity Set.univ E₀ E₁ := by
  let d : ℝ := normalizedContinuumInnerRadius δ
  obtain ⟨hd, hdδ, hdhalf⟩ := normalizedContinuumInnerRadius_bounds hδ
  have hdle : d ≤ 1 / 4 := by
    dsimp [d, normalizedContinuumInnerRadius]
    exact min_le_right _ _
  let P : ℝ≥0∞ := ENNReal.ofReal (2 * Real.pi)
  let A : ℝ≥0∞ := ENNReal.ofReal (4 * Real.pi) ^ ((2 : ℝ)⁻¹)
  let L : ℝ≥0∞ := ENNReal.ofReal (Real.log 2 - Real.log d)
  let C : ℝ≥0∞ :=
    2 * A + P⁻¹ ^ ((2 : ℝ)⁻¹) * L ^ ((2 : ℝ)⁻¹)
  let c : ℝ≥0∞ := (C ^ (2 : ℕ))⁻¹
  have hC : 0 < C := by
    dsimp [C, A]
    positivity
  have hCtop : C ≠ ∞ := by
    dsimp [C, A, P, L]
    finiteness
  have hc : 0 < c := by
    dsimp [c]
    rw [ENNReal.inv_pos]
    exact ENNReal.pow_ne_top hCtop
  refine ⟨c, hc, ?_⟩
  intro E₀ E₁ hE₀compact hE₀connected hzero hreaches
    hE₁closed hE₁connected hone hunbounded
  rw [planarCondenserCapacity, sInf_range]
  refine le_iInf fun u ↦ ?_
  let E₃ : ℝ≥0∞ := ∫⁻ z in Metric.ball (0 : ℂ) 3,
    ENNReal.ofReal (‖u.weakDifferential z‖ ^ 2) ∂volume
  let E : ℝ≥0∞ := u.dirichletEnergy
  have hweak₃ : Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues
      (Metric.ball (0 : ℂ) 3) u u.weakDifferential :=
    Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues.mono_set
      u.isLocalW12.2.1 (Set.subset_univ _)
  have hlocal := u.isLocalW12.2.2
    (Metric.closedBall (0 : ℂ) 3) (isCompact_closedBall (0 : ℂ) 3)
    (Set.subset_univ _)
  have hu₃ : MemLp u 2
      (volume.restrict (Metric.ball (0 : ℂ) 3)) :=
    hlocal.1.mono_measure
      (Measure.restrict_mono Metric.ball_subset_closedBall le_rfl)
  have hdu₃ : MemLp u.weakDifferential 2
      (volume.restrict (Metric.ball (0 : ℂ) 3)) :=
    hlocal.2.mono_measure
      (Measure.restrict_mono Metric.ball_subset_closedBall le_rfl)
  have hucont₃ : ContinuousOn u (Metric.ball (0 : ℂ) 3) :=
    u.continuousOn.mono (Set.subset_univ _)
  let v : Metric.sphere (0 : ℂ) 1 := ⟨1, by simp⟩
  obtain ⟨a, ha, b, hb, hacircle, hbcircle⟩ :=
    exists_inner_outer_good_circles v hd hdle hweak₃ hu₃ hdu₃ hucont₃
  have ha0 : 0 < a := hd.trans ha.1
  have hb0 : 0 < b := by linarith [hb.1]
  have hab : a < b := by linarith [ha.2, hdhalf, hb.1]
  have hb3 : b < 3 := hb.2.trans (by norm_num)
  have hE₃E : E₃ ≤ E := by
    dsimp [E₃, E, PlanarCondenserCompetitor.dirichletEnergy]
    exact lintegral_mono' (Measure.restrict_mono (Set.subset_univ _) le_rfl) le_rfl
  obtain ⟨z₀, hz₀E, hz₀norm⟩ :=
    IsConnected.exists_mem_norm_eq_of_zero_mem_of_reaches
      hE₀connected hzero hreaches ha0.le
        (ha.2.le.trans hdδ)
  obtain ⟨z₁, hz₁E, hz₁norm⟩ :=
    IsConnected.exists_mem_norm_eq_of_one_mem_of_unbounded
      hE₁connected hone hunbounded hb.1.le
  let θ₀ : Metric.sphere (0 : ℂ) 1 :=
    ⟨a⁻¹ • z₀, by
      simp only [Metric.mem_sphere, dist_zero_right, norm_smul,
        Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha0), hz₀norm]
      field_simp⟩
  let θ₁ : Metric.sphere (0 : ℂ) 1 :=
    ⟨b⁻¹ • z₁, by
      simp only [Metric.mem_sphere, dist_zero_right, norm_smul,
        Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hb0), hz₁norm]
      field_simp⟩
  have haθ₀ : a • (θ₀ : ℂ) = z₀ := by
    dsimp [θ₀]
    change a • (a⁻¹ • z₀) = z₀
    rw [smul_smul, mul_inv_cancel₀ ha0.ne', one_smul]
  have hbθ₁ : b • (θ₁ : ℂ) = z₁ := by
    dsimp [θ₁]
    change b • (b⁻¹ • z₁) = z₁
    rw [smul_smul, mul_inv_cancel₀ hb0.ne', one_smul]
  have hinner (θ : Metric.sphere (0 : ℂ) 1) :
      ENNReal.ofReal ‖u (a • (θ : ℂ))‖ ≤ E ^ ((2 : ℝ)⁻¹) * A := by
    calc
      ENNReal.ofReal ‖u (a • (θ : ℂ))‖ =
          ENNReal.ofReal ‖u (a • (θ : ℂ)) - u (a • (θ₀ : ℂ))‖ := by
        rw [haθ₀, u.eq_zero_on z₀ hz₀E, sub_zero]
      _ ≤ E₃ ^ ((2 : ℝ)⁻¹) * A := by
        simpa [E₃, A] using hacircle θ θ₀
      _ ≤ E ^ ((2 : ℝ)⁻¹) * A :=
        mul_le_mul_left
          (ENNReal.rpow_le_rpow hE₃E (by positivity)) _
  have houter (θ : Metric.sphere (0 : ℂ) 1) :
      ENNReal.ofReal ‖(1 : ℝ) - u (b • (θ : ℂ))‖ ≤
        E ^ ((2 : ℝ)⁻¹) * A := by
    calc
      ENNReal.ofReal ‖(1 : ℝ) - u (b • (θ : ℂ))‖ =
          ENNReal.ofReal ‖u (b • (θ : ℂ)) - u (b • (θ₁ : ℂ))‖ := by
        rw [hbθ₁, u.eq_one_on z₁ hz₁E]
        simp [norm_sub_rev]
      _ ≤ E₃ ^ ((2 : ℝ)⁻¹) * A := by
        simpa [E₃, A] using hbcircle θ θ₁
      _ ≤ E ^ ((2 : ℝ)⁻¹) * A :=
        mul_le_mul_left
          (ENNReal.rpow_le_rpow hE₃E (by positivity)) _
  obtain ⟨θ, hradial⟩ :=
    exists_radial_segment_oscillation_le_average_energy
      ha0 hab hb3 hweak₃ hu₃ hdu₃ hucont₃
  have hlog : Real.log b - Real.log a ≤ Real.log 2 - Real.log d := by
    exact sub_le_sub
      (Real.log_le_log hb0 hb.2.le)
      (Real.log_le_log hd ha.1.le)
  have hradial' :
      ENNReal.ofReal ‖u (a • (θ : ℂ)) - u (b • (θ : ℂ))‖ ≤
        E ^ ((2 : ℝ)⁻¹) *
          (P⁻¹ ^ ((2 : ℝ)⁻¹) * L ^ ((2 : ℝ)⁻¹)) := by
    calc
      ENNReal.ofReal ‖u (a • (θ : ℂ)) - u (b • (θ : ℂ))‖ ≤
          (E₃ / P) ^ ((2 : ℝ)⁻¹) *
            ENNReal.ofReal (Real.log b - Real.log a) ^ ((2 : ℝ)⁻¹) := by
        simpa [E₃, P] using hradial
      _ ≤ (E / P) ^ ((2 : ℝ)⁻¹) * L ^ ((2 : ℝ)⁻¹) := by
        have henergyroot :
            (E₃ / P) ^ ((2 : ℝ)⁻¹) ≤
              (E / P) ^ ((2 : ℝ)⁻¹) := by
          refine ENNReal.rpow_le_rpow ?_ (by norm_num)
          exact ENNReal.div_le_div_right hE₃E P
        have hlogroot :
            ENNReal.ofReal (Real.log b - Real.log a) ^ ((2 : ℝ)⁻¹) ≤
              L ^ ((2 : ℝ)⁻¹) := by
          refine ENNReal.rpow_le_rpow ?_ (by norm_num)
          simpa [L] using ENNReal.ofReal_mono hlog
        exact (mul_le_mul_left henergyroot _).trans
          (mul_le_mul_right hlogroot _)
      _ = E ^ ((2 : ℝ)⁻¹) *
          (P⁻¹ ^ ((2 : ℝ)⁻¹) * L ^ ((2 : ℝ)⁻¹)) := by
        calc
          (E / P) ^ ((2 : ℝ)⁻¹) * L ^ ((2 : ℝ)⁻¹) =
              (E * P⁻¹) ^ ((2 : ℝ)⁻¹) * L ^ ((2 : ℝ)⁻¹) := by
            rw [div_eq_mul_inv]
          _ = (E ^ ((2 : ℝ)⁻¹) * P⁻¹ ^ ((2 : ℝ)⁻¹)) *
              L ^ ((2 : ℝ)⁻¹) := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
          _ = _ := by ac_rfl
  have hone_real : (1 : ℝ) ≤
      ‖u (a • (θ : ℂ))‖ +
      ‖u (a • (θ : ℂ)) - u (b • (θ : ℂ))‖ +
      ‖(1 : ℝ) - u (b • (θ : ℂ))‖ := by
    calc
      (1 : ℝ) = ‖u (a • (θ : ℂ)) +
          (u (b • (θ : ℂ)) - u (a • (θ : ℂ))) +
          ((1 : ℝ) - u (b • (θ : ℂ)))‖ := by ring_nf; norm_num
      _ ≤ ‖u (a • (θ : ℂ))‖ +
          ‖u (b • (θ : ℂ)) - u (a • (θ : ℂ))‖ +
          ‖(1 : ℝ) - u (b • (θ : ℂ))‖ := by
        exact (norm_add_le
          (u (a • (θ : ℂ)) +
            (u (b • (θ : ℂ)) - u (a • (θ : ℂ))))
          ((1 : ℝ) - u (b • (θ : ℂ)))).trans
            (add_le_add_left
              (norm_add_le (u (a • (θ : ℂ)))
                (u (b • (θ : ℂ)) - u (a • (θ : ℂ)))) _)
      _ = _ := by rw [norm_sub_rev]
  have hone : (1 : ℝ≥0∞) ≤
      ENNReal.ofReal ‖u (a • (θ : ℂ))‖ +
      ENNReal.ofReal ‖u (a • (θ : ℂ)) - u (b • (θ : ℂ))‖ +
      ENNReal.ofReal ‖(1 : ℝ) - u (b • (θ : ℂ))‖ := by
    calc
      (1 : ℝ≥0∞) = ENNReal.ofReal (1 : ℝ) := by norm_num
      _ ≤ ENNReal.ofReal
          (‖u (a • (θ : ℂ))‖ +
            ‖u (a • (θ : ℂ)) - u (b • (θ : ℂ))‖ +
            ‖(1 : ℝ) - u (b • (θ : ℂ))‖) :=
        ENNReal.ofReal_mono hone_real
      _ = _ := by
        rw [ENNReal.ofReal_add
            (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _),
          ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
  have honeC : (1 : ℝ≥0∞) ≤ E ^ ((2 : ℝ)⁻¹) * C := by
    calc
      (1 : ℝ≥0∞) ≤
          ENNReal.ofReal ‖u (a • (θ : ℂ))‖ +
          ENNReal.ofReal ‖u (a • (θ : ℂ)) - u (b • (θ : ℂ))‖ +
          ENNReal.ofReal ‖(1 : ℝ) - u (b • (θ : ℂ))‖ := hone
      _ ≤ (E ^ ((2 : ℝ)⁻¹) * A) +
          (E ^ ((2 : ℝ)⁻¹) *
            (P⁻¹ ^ ((2 : ℝ)⁻¹) * L ^ ((2 : ℝ)⁻¹))) +
          (E ^ ((2 : ℝ)⁻¹) * A) := by
        exact add_le_add (add_le_add (hinner θ) hradial') (houter θ)
      _ = E ^ ((2 : ℝ)⁻¹) * C := by
        dsimp [C]
        rw [two_mul, mul_add, mul_add]
        ac_rfl
  have hcE : c ≤ E := by
    dsimp [c]
    exact inv_sq_le_of_one_le_rpow_half_mul hC hCtop honeC
  simpa [E] using hcE

/--
%%handwave
name:
  Uniform origin modulus from normalized capacity distortion
statement:
  Let $K\in\mathbb R$ and $\delta>0$. There is $r>0$ such that every
  homeomorphism $f:\mathbb C\to\mathbb C$ fixing $0$ and $1$ and satisfying
  $$
    \operatorname{cap}_{\mathbb C}
      \bigl(f(\overline B(0,s)),f([1,\infty))\bigr)
      \leq K\operatorname{cap}(s,1)
  $$
  for every $s$ obeys $|z|\leq r\Rightarrow|f(z)|<\delta$.
proof:
  Choose the normalized continuum-separation constant $c(\delta)>0$ and an
  exponentially small $r$ with $K\operatorname{cap}(r,1)<c(\delta)$. If an
  image point reached modulus $\delta$, the image disk and image ray would
  satisfy the normalized continuum hypotheses, contradicting the assumed
  capacity upper bound.
-/
theorem exists_radius_norm_lt_of_norm_le_of_normalized_capacity_le
    (K : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ r : ℝ, 0 < r ∧
      ∀ (f : ℂ ≃ₜ ℂ), f 0 = 0 → f 1 = 1 →
        (∀ s : ℝ,
          planarCondenserCapacity Set.univ
              (f '' Metric.closedBall 0 s) (f '' planarUnitRay) ≤
            ENNReal.ofReal K * planarRingCapacity s 1) →
        ∀ z : ℂ, ‖z‖ ≤ r → ‖f z‖ < δ := by
  obtain ⟨c, hc, hsep⟩ :=
    exists_pos_le_planarCondenserCapacity_of_normalized_continua hδ
  obtain ⟨n, _hn, hnsmall⟩ :=
    exists_nat_ofReal_mul_planarRingCapacity_exp_neg_lt K hc
  let r : ℝ := Real.exp (-(n : ℝ))
  have hr : 0 < r := Real.exp_pos _
  refine ⟨r, hr, ?_⟩
  intro f hzero hone hupper z hz
  by_contra hnot
  have hδz : δ ≤ ‖f z‖ := le_of_not_gt hnot
  let E₀ : Set ℂ := f '' Metric.closedBall 0 r
  let E₁ : Set ℂ := f '' planarUnitRay
  have hinner := Homeomorph.image_closedBall_zero_properties f hzero hr.le
  have houter := Homeomorph.image_planarUnitRay_properties f hone
  have hreaches : ∃ w ∈ E₀, δ ≤ ‖w‖ := by
    exact ⟨f z, ⟨z, by simpa [Metric.mem_closedBall, dist_zero_right], rfl⟩,
      hδz⟩
  have hcle : c ≤ planarCondenserCapacity Set.univ E₀ E₁ :=
    hsep E₀ E₁ hinner.1 hinner.2.1 hinner.2.2 hreaches
      houter.1 houter.2.1 houter.2.2.1 houter.2.2.2
  have hu := hupper r
  have hcontr : c ≤ ENNReal.ofReal K * planarRingCapacity r 1 := by
    exact hcle.trans (by simpa [E₀, E₁] using hu)
  exact (not_lt_of_ge hcontr) hnsmall

/--
%%handwave
name:
  Uniform reciprocal-chart equicontinuity at infinity
statement:
  Let $K\in\mathbb R$ and $\delta>0$. There is $r>0$ such that every
  normalized $K$-quasiconformal sphere homeomorphism has reciprocal-chart
  representative $g$ satisfying
  $$
    |z|\leq r\quad\Longrightarrow\quad |g(z)|<\delta.
  $$
proof:
  The reciprocal-chart representative is a whole-plane homeomorphism fixing
  $0$ and $1$. Its image condensers satisfy the required capacity upper bound
  by [reciprocal-chart capacity distortion](lean:JJMath.Quasiconformal.IsKQuasiconformalRiemannSphere.infinityChart_image_condenser_capacity_le) and the round-ring comparison. Apply the uniform normalized-capacity modulus theorem.
-/
theorem exists_radius_infinityChart_norm_lt_of_norm_le
    (K : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ r : ℝ, 0 < r ∧
      ∀ (F : RiemannSphere ≃ₜ RiemannSphere)
        (_hqc : IsKQuasiconformalRiemannSphere K F)
        (hF : IsNormalizedRiemannSphereHomeomorph F) (z : ℂ),
        ‖z‖ ≤ r →
          ‖riemannSphereInfinityChartHomeomorph F hF.1 z‖ < δ := by
  obtain ⟨r, hr, hmod⟩ :=
    exists_radius_norm_lt_of_norm_le_of_normalized_capacity_le K hδ
  refine ⟨r, hr, ?_⟩
  intro F hqc hF z hz
  let g := riemannSphereInfinityChartHomeomorph F hF.1
  have hfix := hF.infinityChart_fixes_zero_one
  exact hmod g hfix.1 hfix.2 (fun s ↦
    (hqc.infinityChart_image_condenser_capacity_le hF
        (Metric.closedBall 0 s) planarUnitRay).trans
      (mul_le_mul_right
        (planarCondenserCapacity_closedBall_planarUnitRay_le_planarRingCapacity s)
        (ENNReal.ofReal K))) z hz

/--
%%handwave
name:
  Capacity lower bound for a normalized image disk
statement:
  For every $\delta>0$ there is $c(\delta)>0$ such that the following holds.
  Let $F:\widehat{\mathbb C}\to\widehat{\mathbb C}$ fix $0$, $1$, and
  $\infty$, let $f$ be its finite-chart homeomorphism, and let $r\geq0$.
  If $f(\overline B(0,r))$ contains a point of modulus at least $\delta$,
  then
  $$
    c(\delta)\leq
      \operatorname{cap}_{\mathbb C}
        \bigl(f(\overline B(0,r)),f([1,\infty))\bigr).
  $$
proof:
  The image disk is a compact connected set containing $0$, while the image
  ray is a closed connected unbounded set containing $1$.  Apply the
  [uniform capacity separation theorem](lean:JJMath.Quasiconformal.exists_pos_le_planarCondenserCapacity_of_normalized_continua).
-/
theorem exists_pos_le_finiteChart_image_closedBall_planarUnitRay_capacity
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ≥0∞, 0 < c ∧
      ∀ (F : RiemannSphere ≃ₜ RiemannSphere)
        (hF : IsNormalizedRiemannSphereHomeomorph F)
        {r : ℝ}, 0 ≤ r →
        (∃ z ∈
          riemannSphereFiniteChartHomeomorph F hF.2.2 ''
            Metric.closedBall 0 r,
          δ ≤ ‖z‖) →
        c ≤ planarCondenserCapacity Set.univ
          (riemannSphereFiniteChartHomeomorph F hF.2.2 ''
            Metric.closedBall 0 r)
          (riemannSphereFiniteChartHomeomorph F hF.2.2 '' planarUnitRay) := by
  obtain ⟨c, hc, hcap⟩ :=
    exists_pos_le_planarCondenserCapacity_of_normalized_continua hδ
  refine ⟨c, hc, ?_⟩
  intro F hF r hr hreaches
  have hinner := hF.finiteChart_image_closedBall_properties hr
  have houter := hF.finiteChart_image_planarUnitRay_properties
  exact hcap _ _ hinner.1 hinner.2.1 hinner.2.2 hreaches
    houter.1 houter.2.1 houter.2.2.1 houter.2.2.2

/--
%%handwave
name:
  Capacity squeeze for a normalized quasiconformal image disk
statement:
  For every $\delta>0$ there is $c(\delta)>0$ such that, whenever a
  normalized $K$-quasiconformal sphere homeomorphism has finite-chart image
  $f(\overline B(0,r))$ reaching modulus $\delta$ with $r\geq0$, one has
  $$
    c(\delta)\leq K\operatorname{cap}(r,1).
  $$
proof:
  The normalized-continuum separation theorem bounds the image condenser
  from below by $c(\delta)$.  The quasiconformal distortion theorem and the
  round-ring comparison bound the same image condenser from above by
  $K\operatorname{cap}(r,1)$.
-/
theorem exists_pos_le_ofReal_mul_planarRingCapacity_of_finiteChart_image_closedBall_reaches
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ≥0∞, 0 < c ∧
      ∀ (K : ℝ) (F : RiemannSphere ≃ₜ RiemannSphere)
        (_hqc : IsKQuasiconformalRiemannSphere K F)
        (hF : IsNormalizedRiemannSphereHomeomorph F)
        {r : ℝ}, 0 ≤ r →
        (∃ z ∈
          riemannSphereFiniteChartHomeomorph F hF.2.2 ''
            Metric.closedBall 0 r,
          δ ≤ ‖z‖) →
        c ≤ ENNReal.ofReal K * planarRingCapacity r 1 := by
  obtain ⟨c, hc, hlower⟩ :=
    exists_pos_le_finiteChart_image_closedBall_planarUnitRay_capacity hδ
  refine ⟨c, hc, ?_⟩
  intro K F hqc hF r hr hreaches
  exact (hlower F hF hr hreaches).trans
    (hqc.finiteChart_image_closedBall_planarUnitRay_capacity_le hF r)

/--
%%handwave
name:
  Uniform finite-chart equicontinuity at zero
statement:
  Let $K\in\mathbb R$ and $\delta>0$.  There is $r>0$, depending only on
  $K$ and $\delta$, such that every normalized $K$-quasiconformal
  self-homeomorphism $F$ of the Riemann sphere has finite-chart
  representative $f$ satisfying
  $$
    |z|\leq r\quad\Longrightarrow\quad |f(z)|<\delta.
  $$
proof:
  Let $c(\delta)>0$ be the continuum-separation constant.  Choose
  $n\geq1$ with
  $K_+\operatorname{cap}(e^{-n},1)<c(\delta)$ and put $r=e^{-n}$.
  If some point of the closed $r$-disk had image modulus at least $\delta$,
  the [capacity squeeze](lean:JJMath.Quasiconformal.exists_pos_le_ofReal_mul_planarRingCapacity_of_finiteChart_image_closedBall_reaches)
  would give the contradictory reverse inequality.
-/
theorem exists_radius_finiteChart_norm_lt_of_norm_le
    (K : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ r : ℝ, 0 < r ∧
      ∀ (F : RiemannSphere ≃ₜ RiemannSphere)
        (_hqc : IsKQuasiconformalRiemannSphere K F)
        (hF : IsNormalizedRiemannSphereHomeomorph F) (z : ℂ),
        ‖z‖ ≤ r →
          ‖riemannSphereFiniteChartHomeomorph F hF.2.2 z‖ < δ := by
  obtain ⟨c, hc, hsqueeze⟩ :=
    exists_pos_le_ofReal_mul_planarRingCapacity_of_finiteChart_image_closedBall_reaches hδ
  obtain ⟨n, _hn, hnsmall⟩ :=
    exists_nat_ofReal_mul_planarRingCapacity_exp_neg_lt K hc
  let r : ℝ := Real.exp (-(n : ℝ))
  have hr : 0 < r := Real.exp_pos _
  refine ⟨r, hr, ?_⟩
  intro F hqc hF z hz
  by_contra hnot
  have hδz : δ ≤
      ‖riemannSphereFiniteChartHomeomorph F hF.2.2 z‖ :=
    le_of_not_gt hnot
  have hreaches : ∃ w ∈
      riemannSphereFiniteChartHomeomorph F hF.2.2 ''
        Metric.closedBall 0 r,
      δ ≤ ‖w‖ := by
    refine ⟨riemannSphereFiniteChartHomeomorph F hF.2.2 z, ?_, hδz⟩
    refine ⟨z, ?_, rfl⟩
    simpa [Metric.mem_closedBall, dist_zero_right] using hz
  have hcle := hsqueeze K F hqc hF hr.le hreaches
  exact (not_lt_of_ge hcle) hnsmall

/--
%%handwave
name:
  Spherical equicontinuity at the normalized origin
statement:
  Let $\{F_i\}_{i\in I}$ be any family of normalized
  $K$-quasiconformal self-homeomorphisms of
  $\widehat{\mathbb C}$.  Then the family is equicontinuous at $0$ for the
  compatible spherical metric.
proof:
  Continuity of the inclusion $\mathbb C\hookrightarrow\widehat{\mathbb C}$
  converts a sufficiently small Euclidean target norm into any prescribed
  spherical distance.  Apply the [uniform finite-chart estimate at zero](lean:JJMath.Quasiconformal.exists_radius_finiteChart_norm_lt_of_norm_le), use the image of the corresponding Euclidean disk as a spherical neighborhood of zero, and return from the finite chart.
-/
theorem equicontinuousAt_zero_normalizedKQuasiconformalRiemannSphere
    {ι : Type*} (K : ℝ)
    (F : ι → RiemannSphere ≃ₜ RiemannSphere)
    (hqc : ∀ i, IsKQuasiconformalRiemannSphere K (F i))
    (hnorm : ∀ i, IsNormalizedRiemannSphereHomeomorph (F i)) :
    EquicontinuousAt (fun i z ↦ F i z)
      ((0 : ℂ) : RiemannSphere) := by
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  have hcoe : Continuous ((↑) : ℂ → RiemannSphere) :=
    OnePoint.continuous_coe
  obtain ⟨δ, hδ, hδmap⟩ :=
    (Metric.continuousAt_iff.mp hcoe.continuousAt) ε hε
  obtain ⟨r, hr, hrmap⟩ :=
    exists_radius_finiteChart_norm_lt_of_norm_le K hδ
  have hopen : IsOpen (((↑) : ℂ → RiemannSphere) '' Metric.ball 0 r) :=
    OnePoint.isOpenMap_coe _ Metric.isOpen_ball
  have hzero_mem : ((0 : ℂ) : RiemannSphere) ∈
      ((↑) : ℂ → RiemannSphere) '' Metric.ball 0 r := by
    exact ⟨0, by simpa [Metric.mem_ball], rfl⟩
  filter_upwards [hopen.mem_nhds hzero_mem] with x hx
  intro i
  rcases hx with ⟨z, hz, rfl⟩
  have hzle : ‖z‖ ≤ r := by
    exact (by simpa [Metric.mem_ball, dist_zero_right] using
      (Metric.mem_ball.mp hz) : ‖z‖ < r).le
  let w : ℂ :=
    riemannSphereFiniteChartHomeomorph (F i) (hnorm i).2.2 z
  have hw : ‖w‖ < δ := hrmap (F i) (hqc i) (hnorm i) z hzle
  have hroundtrip : (w : RiemannSphere) = F i (z : RiemannSphere) := by
    exact coe_riemannSphereFiniteChartHomeomorph_apply
      (F i) (hnorm i).2.2 z
  rw [(hnorm i).1, ← hroundtrip, dist_comm]
  apply hδmap
  simpa [w, dist_zero_right] using hw

/--
%%handwave
name:
  Spherical equicontinuity of normalized inverse maps at the origin
statement:
  Let $\{F_i\}_{i\in I}$ be any family of normalized
  $K$-quasiconformal self-homeomorphisms of
  $\widehat{\mathbb C}$. Then the family $\{F_i^{-1}\}_{i\in I}$ is
  equicontinuous at $0$ for the compatible spherical metric.
proof:
  Each inverse is [normalized](lean:JJMath.Quasiconformal.IsNormalizedRiemannSphereHomeomorph.symm) and [$K$-quasiconformal](lean:JJMath.Quasiconformal.IsKQuasiconformalRiemannSphere.symm). Apply [spherical equicontinuity at the normalized origin](lean:JJMath.Quasiconformal.equicontinuousAt_zero_normalizedKQuasiconformalRiemannSphere) to the inverse family.
-/
theorem equicontinuousAt_zero_symm_normalizedKQuasiconformalRiemannSphere
    {ι : Type*} (K : ℝ)
    (F : ι → RiemannSphere ≃ₜ RiemannSphere)
    (hqc : ∀ i, IsKQuasiconformalRiemannSphere K (F i))
    (hnorm : ∀ i, IsNormalizedRiemannSphereHomeomorph (F i)) :
    EquicontinuousAt (fun i z ↦ (F i).symm z)
      ((0 : ℂ) : RiemannSphere) := by
  exact equicontinuousAt_zero_normalizedKQuasiconformalRiemannSphere K
    (fun i ↦ (F i).symm) (fun i ↦ (hqc i).symm) (fun i ↦ (hnorm i).symm)

/--
%%handwave
name:
  Spherical equicontinuity at the normalized point infinity
statement:
  Let $\{F_i\}_{i\in I}$ be any family of normalized
  $K$-quasiconformal self-homeomorphisms of
  $\widehat{\mathbb C}$. Then the family is equicontinuous at $\infty$ for
  the compatible spherical metric.
proof:
  Reciprocal coordinates send $\infty$ to $0$. Pull an arbitrary spherical
  entourage back through the continuous inverse reciprocal chart, choose a
  Euclidean disk inside that neighborhood of $0$, and apply the [uniform reciprocal-chart estimate](lean:JJMath.Quasiconformal.exists_radius_infinityChart_norm_lt_of_norm_le). The inverse-chart image of the corresponding source disk is a spherical neighborhood of $\infty$ on which every map has image pair in the prescribed entourage.
-/
theorem equicontinuousAt_infty_normalizedKQuasiconformalRiemannSphere
    {ι : Type*} (K : ℝ)
    (F : ι → RiemannSphere ≃ₜ RiemannSphere)
    (hqc : ∀ i, IsKQuasiconformalRiemannSphere K (F i))
    (hnorm : ∀ i, IsNormalizedRiemannSphereHomeomorph (F i)) :
    EquicontinuousAt (fun i z ↦ F i z)
      (OnePoint.infty : RiemannSphere) := by
  intro U hU
  let S : Set RiemannSphere :=
    {y | ((OnePoint.infty : RiemannSphere), y) ∈ U}
  have hS : S ∈ 𝓝 (OnePoint.infty : RiemannSphere) :=
    mem_nhds_left _ hU
  have hS0 : S ∈ 𝓝 (riemannSphereInfinityChart.symm 0) := by
    simpa using hS
  have hpre : riemannSphereInfinityChart.symm ⁻¹' S ∈ 𝓝 (0 : ℂ) :=
    continuous_riemannSphereInfinityChart_symm.continuousAt.preimage_mem_nhds
      hS0
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hpre
  obtain ⟨r, hr, hrmap⟩ :=
    exists_radius_infinityChart_norm_lt_of_norm_le K hδ
  filter_upwards
    [riemannSphereInfinityChart_symm_image_ball_mem_nhds_infty hr]
    with x hx
  intro i
  rcases hx with ⟨z, hz, rfl⟩
  have hzle : ‖z‖ ≤ r := by
    exact (by simpa [Metric.mem_ball, dist_zero_right] using
      (Metric.mem_ball.mp hz) : ‖z‖ < r).le
  let w : ℂ :=
    riemannSphereInfinityChartHomeomorph (F i) (hnorm i).1 z
  have hw : ‖w‖ < δ := hrmap (F i) (hqc i) (hnorm i) z hzle
  have hwball : w ∈ Metric.ball (0 : ℂ) δ := by
    simpa [Metric.mem_ball, dist_zero_right] using hw
  have hwU :
      ((OnePoint.infty : RiemannSphere),
        riemannSphereInfinityChart.symm w) ∈ U :=
    hδsub hwball
  have hroundtrip :
      riemannSphereInfinityChart.symm w =
        F i (riemannSphereInfinityChart.symm z) := by
    exact
      riemannSphereInfinityChart_symm_riemannSphereInfinityChartHomeomorph_apply
        (F i) (hnorm i).1 z
  rw [(hnorm i).2.2, ← hroundtrip]
  exact hwU

/--
%%handwave
name:
  Spherical equicontinuity of normalized inverse maps at infinity
statement:
  Let $\{F_i\}_{i\in I}$ be any family of normalized
  $K$-quasiconformal self-homeomorphisms of
  $\widehat{\mathbb C}$. Then the inverse family $\{F_i^{-1}\}_{i\in I}$
  is equicontinuous at $\infty$ for the compatible spherical metric.
proof:
  Each inverse remains normalized and $K$-quasiconformal. Apply [spherical equicontinuity at infinity](lean:JJMath.Quasiconformal.equicontinuousAt_infty_normalizedKQuasiconformalRiemannSphere) to the inverse family.
-/
theorem equicontinuousAt_infty_symm_normalizedKQuasiconformalRiemannSphere
    {ι : Type*} (K : ℝ)
    (F : ι → RiemannSphere ≃ₜ RiemannSphere)
    (hqc : ∀ i, IsKQuasiconformalRiemannSphere K (F i))
    (hnorm : ∀ i, IsNormalizedRiemannSphereHomeomorph (F i)) :
    EquicontinuousAt (fun i z ↦ (F i).symm z)
      (OnePoint.infty : RiemannSphere) := by
  exact equicontinuousAt_infty_normalizedKQuasiconformalRiemannSphere K
    (fun i ↦ (F i).symm) (fun i ↦ (hqc i).symm) (fun i ↦ (hnorm i).symm)

/--
%%handwave
name:
  Uniform finite-coordinate bound at a fixed nonzero point
statement:
  Let $K\in\mathbb R$ and $x\in\mathbb C\setminus\{0\}$. There is $M>0$
  such that every normalized $K$-quasiconformal sphere homeomorphism with
  finite-chart representative $f$ satisfies
  $$
    |f(x)|<M.
  $$
proof:
  Apply the reciprocal-coordinate modulus at $\infty$ to the inverse maps
  with target threshold $|x^{-1}|$. The identity
  $g_{F^{-1}}(f(x)^{-1})=x^{-1}$ forces $|f(x)^{-1}|$ to stay outside a fixed
  disk about $0$, hence $|f(x)|$ is uniformly bounded.
-/
theorem exists_uniform_finiteChart_norm_bound_at
    (K : ℝ) {x : ℂ} (hx : x ≠ 0) :
    ∃ M : ℝ, 0 < M ∧
      ∀ (F : RiemannSphere ≃ₜ RiemannSphere)
        (_hqc : IsKQuasiconformalRiemannSphere K F)
        (hF : IsNormalizedRiemannSphereHomeomorph F),
        ‖riemannSphereFiniteChartHomeomorph F hF.2.2 x‖ < M := by
  have hδ : 0 < ‖x⁻¹‖ := norm_pos_iff.mpr (inv_ne_zero hx)
  obtain ⟨r, hr, hrmap⟩ :=
    exists_radius_infinityChart_norm_lt_of_norm_le K hδ
  refine ⟨r⁻¹, inv_pos.mpr hr, ?_⟩
  intro F hqc hF
  let y := riemannSphereFiniteChartHomeomorph F hF.2.2 x
  have hy : y ≠ 0 := by
    intro hy
    have hy' : riemannSphereFiniteChartHomeomorph F hF.2.2 x = 0 := by
      simpa [y] using hy
    have hcoe := coe_riemannSphereFiniteChartHomeomorph_apply F hF.2.2 x
    have heq : F (x : RiemannSphere) =
        F ((0 : ℂ) : RiemannSphere) := by
      rw [← hcoe, hy', hF.1]
    have hxeq := F.injective heq
    exact hx (by simpa using hxeq)
  have hinvchart :
      riemannSphereInfinityChartHomeomorph F.symm hF.symm.1 y⁻¹ =
        x⁻¹ := by
    exact infinityChartHomeomorph_symm_apply_inv_finiteChartHomeomorph hF hx
  have hnot : ¬ ‖y⁻¹‖ ≤ r := by
    intro hle
    have hsmall := hrmap F.symm hqc.symm hF.symm y⁻¹ hle
    rw [hinvchart] at hsmall
    exact lt_irrefl _ hsmall
  have hrinv : r < ‖y‖⁻¹ := by
    simpa [norm_inv] using lt_of_not_ge hnot
  exact (lt_inv_comm₀ hr (norm_pos_iff.mpr hy)).mp hrinv

/--
%%handwave
name:
  Uniform finite-coordinate bound on a fixed source disk
statement:
  Let $K,R\in\mathbb R$. There is $M>0$ such that every normalized
  $K$-quasiconformal sphere homeomorphism with finite-chart representative
  $f$ satisfies
  $$
    |z|\leq R\quad\Longrightarrow\quad |f(z)|<M.
  $$
proof:
  Choose a positive reciprocal threshold smaller than
  $(\max\{R,0\}+1)^{-1}$. Apply the reciprocal-coordinate modulus at
  $\infty$ to the inverse family. If $f(z)$ had arbitrarily large modulus,
  then $f(z)^{-1}$ would enter the corresponding reciprocal source disk,
  while the identity
  $g_{F^{-1}}(f(z)^{-1})=z^{-1}$ and $|z|\leq R$ keep its image outside the
  target disk. The point $z=0$ is fixed separately.
-/
theorem exists_uniform_finiteChart_norm_bound_on_closedBall
    (K R : ℝ) :
    ∃ M : ℝ, 0 < M ∧
      ∀ (F : RiemannSphere ≃ₜ RiemannSphere)
        (_hqc : IsKQuasiconformalRiemannSphere K F)
        (hF : IsNormalizedRiemannSphereHomeomorph F) (z : ℂ),
        ‖z‖ ≤ R →
          ‖riemannSphereFiniteChartHomeomorph F hF.2.2 z‖ < M := by
  let A : ℝ := max R 0 + 1
  have hA : 0 < A := by dsimp [A]; linarith [le_max_right R 0]
  let δ : ℝ := A⁻¹
  have hδ : 0 < δ := inv_pos.mpr hA
  obtain ⟨r, hr, hrmap⟩ :=
    exists_radius_infinityChart_norm_lt_of_norm_le K hδ
  refine ⟨r⁻¹, inv_pos.mpr hr, ?_⟩
  intro F hqc hF z hzR
  by_cases hz : z = 0
  · subst z
    rw [hF.finiteChart_fixes_zero_one.1, norm_zero]
    exact inv_pos.mpr hr
  let y := riemannSphereFiniteChartHomeomorph F hF.2.2 z
  have hy : y ≠ 0 := by
    intro hy
    have hy' : riemannSphereFiniteChartHomeomorph F hF.2.2 z = 0 := by
      simpa [y] using hy
    have hcoe := coe_riemannSphereFiniteChartHomeomorph_apply F hF.2.2 z
    have heq : F (z : RiemannSphere) =
        F ((0 : ℂ) : RiemannSphere) := by
      rw [← hcoe, hy', hF.1]
    exact hz (by simpa using F.injective heq)
  have hδz : δ ≤ ‖z⁻¹‖ := by
    have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hzltA : ‖z‖ < A := by
      exact (hzR.trans (le_max_left R 0)).trans_lt (lt_add_one _)
    have hinv : A⁻¹ < ‖z‖⁻¹ := (inv_lt_inv₀ hA hzpos).2 hzltA
    simpa [δ, norm_inv] using hinv.le
  have hinvchart :
      riemannSphereInfinityChartHomeomorph F.symm hF.symm.1 y⁻¹ =
        z⁻¹ := by
    exact infinityChartHomeomorph_symm_apply_inv_finiteChartHomeomorph hF hz
  have hnot : ¬ ‖y⁻¹‖ ≤ r := by
    intro hle
    have hsmall := hrmap F.symm hqc.symm hF.symm y⁻¹ hle
    rw [hinvchart] at hsmall
    exact (not_lt_of_ge hδz) hsmall
  have hrinv : r < ‖y‖⁻¹ := by
    simpa [norm_inv] using lt_of_not_ge hnot
  exact (lt_inv_comm₀ hr (norm_pos_iff.mpr hy)).mp hrinv

/--
%%handwave
name:
  Affine coordinates centered at a nonzero point and the origin
statement:
  For $x\in\mathbb C\setminus\{0\}$, this is the complex-affine
  homeomorphism
  $$
    B_x(z)=x(1-z).
  $$
  It sends $0$ to $x$ and $1$ to $0$.
-/
def pointZeroHomeomorph (x : ℂ) (hx : x ≠ 0) : ℂ ≃ₜ ℂ :=
  (Homeomorph.mulLeft₀ (-x) (neg_ne_zero.mpr hx)).trans
    (Homeomorph.addRight x)

/--
%%handwave
name:
  Formula for the point-origin affine coordinates
statement:
  For $x\neq0$ and $z\in\mathbb C$,
  $$
    B_x(z)=x(1-z).
  $$
proof:
  Expand multiplication by $-x$ followed by translation by $x$.
-/
@[simp]
theorem pointZeroHomeomorph_apply (x : ℂ) (hx : x ≠ 0) (z : ℂ) :
    pointZeroHomeomorph x hx z = x * (1 - z) := by
  simp [pointZeroHomeomorph]
  ring

/--
%%handwave
name:
  Affine-map expression for point-origin coordinates
statement:
  The map $B_x(z)=x(1-z)$ is the complex-affine map with linear
  coefficient $-x$ and translation $x$.
proof:
  Expand both formulas.
-/
theorem pointZeroHomeomorph_eq_affineMap (x : ℂ) (hx : x ≠ 0) :
    (pointZeroHomeomorph x hx : ℂ → ℂ) = affineMap (-x) 0 x := by
  funext z
  simp [pointZeroHomeomorph, affineMap, realLinearMapOfWirtinger]

/--
%%handwave
name:
  Formula for the inverse point-origin coordinates
statement:
  For $x\neq0$ and $z\in\mathbb C$,
  $$
    B_x^{-1}(z)=1-x^{-1}z.
  $$
proof:
  Substitute the proposed inverse into $B_x$ and use $x\neq0$.
-/
@[simp]
theorem pointZeroHomeomorph_symm_apply (x : ℂ) (hx : x ≠ 0) (z : ℂ) :
    (pointZeroHomeomorph x hx).symm z = 1 - x⁻¹ * z := by
  apply (pointZeroHomeomorph x hx).injective
  simp [pointZeroHomeomorph_apply]
  field_simp

/--
%%handwave
name:
  Affine-map expression for inverse point-origin coordinates
statement:
  The inverse map $B_x^{-1}(z)=1-x^{-1}z$ is the complex-affine map with
  linear coefficient $-x^{-1}$ and translation $1$.
proof:
  Expand both formulas.
-/
theorem pointZeroHomeomorph_symm_eq_affineMap (x : ℂ) (hx : x ≠ 0) :
    ((pointZeroHomeomorph x hx).symm : ℂ → ℂ) =
      affineMap (-x⁻¹) 0 1 := by
  funext z
  simp [affineMap, realLinearMapOfWirtinger]
  ring

/--
%%handwave
name:
  A normalized finite-chart map has no additional zero
statement:
  If a sphere homeomorphism fixes $0$ and $\infty$, its finite-chart
  representative $f$ satisfies
  $$
    x\neq0\quad\Longrightarrow\quad f(x)\neq0.
  $$
proof:
  Otherwise $f(x)=f(0)$, and injectivity gives $x=0$.
-/
theorem IsNormalizedRiemannSphereHomeomorph.finiteChartHomeomorph_ne_zero
    {F : RiemannSphere ≃ₜ RiemannSphere}
    (hF : IsNormalizedRiemannSphereHomeomorph F)
    {x : ℂ} (hx : x ≠ 0) :
    riemannSphereFiniteChartHomeomorph F hF.2.2 x ≠ 0 := by
  intro hzero
  let f := riemannSphereFiniteChartHomeomorph F hF.2.2
  have heq : f x = f 0 := by
    rw [hzero]
    exact hF.finiteChart_fixes_zero_one.1.symm
  exact hx (f.injective heq)

/--
%%handwave
name:
  Finite-chart recentering at a nonzero point
statement:
  Let $f:\mathbb C\to\mathbb C$ be the finite-chart representative of a
  normalized sphere homeomorphism and let $x\neq0$. The recentered
  homeomorphism is
  $$
    G_{f,x}=B_{f(x)}^{-1}\circ f\circ B_x,
    \qquad B_x(z)=x(1-z).
  $$
  Thus the marked pair $(x,0)$ in the source and $(f(x),0)$ in the target
  both become $(0,1)$.
-/
def recenteredFiniteChartHomeomorph
    (F : RiemannSphere ≃ₜ RiemannSphere)
    (hF : IsNormalizedRiemannSphereHomeomorph F)
    (x : ℂ) (hx : x ≠ 0) : ℂ ≃ₜ ℂ :=
  (pointZeroHomeomorph x hx).trans
    (riemannSphereFiniteChartHomeomorph F hF.2.2) |>.trans
      (pointZeroHomeomorph
        (riemannSphereFiniteChartHomeomorph F hF.2.2 x)
        (hF.finiteChartHomeomorph_ne_zero hx)).symm

/--
%%handwave
name:
  Formula for the recentered finite-chart map
statement:
  With $f$ and $G_{f,x}$ as above,
  $$
    G_{f,x}(z)=1-f(x)^{-1}f\bigl(x(1-z)\bigr).
  $$
proof:
  Substitute the formulas for $B_x$ and $B_{f(x)}^{-1}$ into the defining
  conjugation.
-/
@[simp]
theorem recenteredFiniteChartHomeomorph_apply
    (F : RiemannSphere ≃ₜ RiemannSphere)
    (hF : IsNormalizedRiemannSphereHomeomorph F)
    (x : ℂ) (hx : x ≠ 0) (z : ℂ) :
    recenteredFiniteChartHomeomorph F hF x hx z =
      1 - (riemannSphereFiniteChartHomeomorph F hF.2.2 x)⁻¹ *
        riemannSphereFiniteChartHomeomorph F hF.2.2 (x * (1 - z)) := by
  simp [recenteredFiniteChartHomeomorph]

/--
%%handwave
name:
  The recentered finite-chart map fixes zero
statement:
  For every nonzero $x$, the recentered map satisfies
  $$
    G_{f,x}(0)=0.
  $$
proof:
  The source change sends $0$ to $x$, and the target change sends $f(x)$
  back to $0$.
-/
@[simp]
theorem recenteredFiniteChartHomeomorph_zero
    (F : RiemannSphere ≃ₜ RiemannSphere)
    (hF : IsNormalizedRiemannSphereHomeomorph F)
    (x : ℂ) (hx : x ≠ 0) :
    recenteredFiniteChartHomeomorph F hF x hx 0 = 0 := by
  rw [recenteredFiniteChartHomeomorph_apply]
  simp only [sub_zero, mul_one]
  rw [inv_mul_cancel₀ (hF.finiteChartHomeomorph_ne_zero hx)]
  norm_num

/--
%%handwave
name:
  The recentered finite-chart map fixes one
statement:
  For every nonzero $x$, the recentered map satisfies
  $$
    G_{f,x}(1)=1.
  $$
proof:
  The source change sends $1$ to $0$, normalization gives $f(0)=0$, and
  the target change sends $0$ to $1$.
-/
@[simp]
theorem recenteredFiniteChartHomeomorph_one
    (F : RiemannSphere ≃ₜ RiemannSphere)
    (hF : IsNormalizedRiemannSphereHomeomorph F)
    (x : ℂ) (hx : x ≠ 0) :
    recenteredFiniteChartHomeomorph F hF x hx 1 = 1 := by
  simp [recenteredFiniteChartHomeomorph_apply,
    hF.finiteChart_fixes_zero_one.1]

/--
%%handwave
name:
  Capacity bound after recentering at a finite point
statement:
  Let $F$ be a normalized $K$-quasiconformal sphere homeomorphism, let
  $x\neq0$, and let $G_{F,x}$ be its recentered finite-chart map. Then for
  every real $s$,
  $$
    \operatorname{cap}_{\mathbb C}
      \bigl(G_{F,x}(\overline B(0,s)),G_{F,x}([1,\infty))\bigr)
      \leq K\operatorname{cap}(s,1).
  $$
proof:
  The source affine map sends the normalized disk-ray condenser to the disk
  centered at $x$ and the ray from $x$ through $0$. Apply finite-chart
  quasiconformal capacity distortion, then use exact complex-affine
  invariance for both the source and target coordinate changes and the
  round-ring comparison.
-/
theorem IsKQuasiconformalRiemannSphere.recenteredFiniteChart_image_capacity_le
    {K : ℝ} {F : RiemannSphere ≃ₜ RiemannSphere}
    (hqc : IsKQuasiconformalRiemannSphere K F)
    (hF : IsNormalizedRiemannSphereHomeomorph F)
    {x : ℂ} (hx : x ≠ 0) (s : ℝ) :
    planarCondenserCapacity Set.univ
        (recenteredFiniteChartHomeomorph F hF x hx '' Metric.closedBall 0 s)
        (recenteredFiniteChartHomeomorph F hF x hx '' planarUnitRay) ≤
      ENNReal.ofReal K * planarRingCapacity s 1 := by
  let f := riemannSphereFiniteChartHomeomorph F hF.2.2
  let T := pointZeroHomeomorph x hx
  let y := f x
  let hy : y ≠ 0 := hF.finiteChartHomeomorph_ne_zero hx
  let S := pointZeroHomeomorph y hy
  have hmap := hqc.finiteChart_image_condenser_capacity_le hF
    (T '' Metric.closedBall 0 s) (T '' planarUnitRay)
  have htarget := planarCondenserCapacity_affineMap_image (-y⁻¹) 1
    (neg_ne_zero.mpr (inv_ne_zero hy))
    (f '' (T '' Metric.closedBall 0 s))
    (f '' (T '' planarUnitRay))
  have hsource := planarCondenserCapacity_affineMap_image (-x) x
    (neg_ne_zero.mpr hx) (Metric.closedBall 0 s) planarUnitRay
  have himage (E : Set ℂ) :
      recenteredFiniteChartHomeomorph F hF x hx '' E =
        S.symm '' (f '' (T '' E)) := by
    rw [Set.image_image, Set.image_image]
    apply Set.image_congr
    intro z hz
    rfl
  calc
    planarCondenserCapacity Set.univ
        (recenteredFiniteChartHomeomorph F hF x hx '' Metric.closedBall 0 s)
        (recenteredFiniteChartHomeomorph F hF x hx '' planarUnitRay) =
      planarCondenserCapacity Set.univ
        (S.symm '' (f '' (T '' Metric.closedBall 0 s)))
        (S.symm '' (f '' (T '' planarUnitRay))) := by
          rw [himage, himage]
    _ = planarCondenserCapacity Set.univ
        (f '' (T '' Metric.closedBall 0 s))
        (f '' (T '' planarUnitRay)) := by
          rw [pointZeroHomeomorph_symm_eq_affineMap]
          exact htarget
    _ ≤ ENNReal.ofReal K * planarCondenserCapacity Set.univ
        (T '' Metric.closedBall 0 s) (T '' planarUnitRay) := hmap
    _ = ENNReal.ofReal K * planarCondenserCapacity Set.univ
        (Metric.closedBall 0 s) planarUnitRay := by
          congr 1
          rw [pointZeroHomeomorph_eq_affineMap]
          exact hsource
    _ ≤ ENNReal.ofReal K * planarRingCapacity s 1 :=
      mul_le_mul_right
        (planarCondenserCapacity_closedBall_planarUnitRay_le_planarRingCapacity s)
        (ENNReal.ofReal K)

/--
%%handwave
name:
  Uniform finite-chart equicontinuity at a fixed nonzero point
statement:
  Let $K\in\mathbb R$, $x\in\mathbb C\setminus\{0\}$, and $\delta>0$.
  There is $r>0$ such that every normalized $K$-quasiconformal sphere
  homeomorphism with finite-chart representative $f$ satisfies
  $$
    |z-x|\leq r\quad\Longrightarrow\quad |f(z)-f(x)|<\delta.
  $$
proof:
  The values $f(x)$ have a common finite bound $M$. Conjugate by
  $B_x(z)=x(1-z)$ in the source and $B_{f(x)}^{-1}$ in the target. The
  resulting homeomorphism fixes $0$ and $1$ and satisfies the standard
  normalized capacity bound. Apply the origin modulus with threshold
  $\delta/M$, then undo the two affine changes.
-/
theorem exists_radius_finiteChart_norm_sub_lt_at
    (K : ℝ) {x : ℂ} (hx : x ≠ 0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ r : ℝ, 0 < r ∧
      ∀ (F : RiemannSphere ≃ₜ RiemannSphere)
        (_hqc : IsKQuasiconformalRiemannSphere K F)
        (hF : IsNormalizedRiemannSphereHomeomorph F) (z : ℂ),
        ‖z - x‖ ≤ r →
          ‖riemannSphereFiniteChartHomeomorph F hF.2.2 z -
            riemannSphereFiniteChartHomeomorph F hF.2.2 x‖ < δ := by
  obtain ⟨M, hM, hbound⟩ :=
    exists_uniform_finiteChart_norm_bound_at K hx
  have hδM : 0 < δ / M := div_pos hδ hM
  obtain ⟨s, hs, hmod⟩ :=
    exists_radius_norm_lt_of_norm_le_of_normalized_capacity_le K hδM
  refine ⟨‖x‖ * s, mul_pos (norm_pos_iff.mpr hx) hs, ?_⟩
  intro F hqc hF z hz
  let f := riemannSphereFiniteChartHomeomorph F hF.2.2
  let T := pointZeroHomeomorph x hx
  let y := f x
  have hy : y ≠ 0 := hF.finiteChartHomeomorph_ne_zero hx
  let S := pointZeroHomeomorph y hy
  let g := recenteredFiniteChartHomeomorph F hF x hx
  let u := T.symm z
  have hu_formula : u = x⁻¹ * (x - z) := by
    dsimp [u, T]
    rw [pointZeroHomeomorph_symm_apply]
    field_simp
  have hu : ‖u‖ ≤ s := by
    rw [hu_formula, norm_mul, norm_inv, norm_sub_rev]
    exact (inv_mul_le_iff₀ (norm_pos_iff.mpr hx)).2 hz
  have hgsmall : ‖g u‖ < δ / M := by
    exact hmod g
      (recenteredFiniteChartHomeomorph_zero F hF x hx)
      (recenteredFiniteChartHomeomorph_one F hF x hx)
      (fun t ↦ hqc.recenteredFiniteChart_image_capacity_le hF hx t)
      u hu
  have hS : S (g u) = f z := by
    dsimp only [g, u, recenteredFiniteChartHomeomorph]
    change S (S.symm (f (T (T.symm z)))) = f z
    simp
  have hrelation : f z - y = -y * g u := by
    calc
      f z - y = S (g u) - y := by rw [hS]
      _ = -y * g u := by
        rw [pointZeroHomeomorph_apply]
        ring
  have hybound : ‖y‖ < M := hbound F hqc hF
  calc
    ‖f z - f x‖ = ‖y‖ * ‖g u‖ := by
      rw [show f x = y by rfl, hrelation, norm_mul, norm_neg]
    _ ≤ M * ‖g u‖ :=
      mul_le_mul_of_nonneg_right hybound.le (norm_nonneg _)
    _ < M * (δ / M) := mul_lt_mul_of_pos_left hgsmall hM
    _ = δ := by field_simp

/--
%%handwave
name:
  Spherical equicontinuity at a fixed nonzero finite point
statement:
  Let $\{F_i\}_{i\in I}$ be any family of normalized
  $K$-quasiconformal self-homeomorphisms of $\widehat{\mathbb C}$. For
  every $x\in\mathbb C\setminus\{0\}$, the family is equicontinuous at the
  spherical point represented by $x$.
proof:
  The finite coordinates $f_i(x)$ lie in one compact disk. The finite-chart
  modulus keeps nearby $f_i(z)$ in a slightly larger compact disk. On that
  disk, the continuous inclusion into the sphere is uniformly continuous by
  Heine--Cantor, so the Euclidean estimate gives the required spherical
  estimate uniformly in $i$.
-/
theorem equicontinuousAt_finite_normalizedKQuasiconformalRiemannSphere
    {ι : Type*} (K : ℝ)
    (F : ι → RiemannSphere ≃ₜ RiemannSphere)
    (hqc : ∀ i, IsKQuasiconformalRiemannSphere K (F i))
    (hnorm : ∀ i, IsNormalizedRiemannSphereHomeomorph (F i))
    {x : ℂ} (hx : x ≠ 0) :
    EquicontinuousAt (fun i z ↦ F i z) (x : RiemannSphere) := by
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  obtain ⟨M, hM, hbound⟩ :=
    exists_uniform_finiteChart_norm_bound_at K hx
  let C : Set ℂ := Metric.closedBall 0 (M + 1)
  have hCcompact : IsCompact C := isCompact_closedBall 0 (M + 1)
  have hcoe : Continuous ((↑) : ℂ → RiemannSphere) :=
    OnePoint.continuous_coe
  have huc : UniformContinuousOn ((↑) : ℂ → RiemannSphere) C :=
    hCcompact.uniformContinuousOn_of_continuous hcoe.continuousOn
  obtain ⟨η, hη, hηmap⟩ :=
    (Metric.uniformContinuousOn_iff.mp huc) ε hε
  let δ : ℝ := min η 1
  have hδ : 0 < δ := lt_min hη zero_lt_one
  obtain ⟨r, hr, hrmap⟩ :=
    exists_radius_finiteChart_norm_sub_lt_at K hx hδ
  have hopen : IsOpen (((↑) : ℂ → RiemannSphere) '' Metric.ball x r) :=
    OnePoint.isOpenMap_coe _ Metric.isOpen_ball
  have hxmem : (x : RiemannSphere) ∈
      ((↑) : ℂ → RiemannSphere) '' Metric.ball x r := by
    exact ⟨x, Metric.mem_ball_self hr, rfl⟩
  filter_upwards [hopen.mem_nhds hxmem] with q hq
  intro i
  rcases hq with ⟨z, hz, rfl⟩
  let f := riemannSphereFiniteChartHomeomorph (F i) (hnorm i).2.2
  have hzle : ‖z - x‖ ≤ r := by
    exact (by simpa [Metric.mem_ball, dist_eq_norm] using
      (Metric.mem_ball.mp hz) : ‖z - x‖ < r).le
  have hclose : ‖f z - f x‖ < δ :=
    hrmap (F i) (hqc i) (hnorm i) z hzle
  have hfx : ‖f x‖ < M := hbound (F i) (hqc i) (hnorm i)
  have hfxC : f x ∈ C := by
    simp only [C, Metric.mem_closedBall, dist_zero_right]
    linarith
  have hfzC : f z ∈ C := by
    simp only [C, Metric.mem_closedBall, dist_zero_right]
    exact (calc
      ‖f z‖ ≤ ‖f x‖ + ‖f z - f x‖ := by
        have := norm_add_le (f x) (f z - f x)
        simpa [add_sub_cancel] using this
      _ < M + 1 := by
        exact add_lt_add hfx (hclose.trans_le (min_le_right _ _))).le
  have hdist : dist (f x) (f z) < η := by
    simpa [dist_eq_norm, norm_sub_rev] using
      hclose.trans_le (min_le_left _ _)
  have hsphere : dist ((f x : ℂ) : RiemannSphere)
      ((f z : ℂ) : RiemannSphere) < ε :=
    hηmap (f x) hfxC (f z) hfzC hdist
  have hroundtrip_x : ((f x : ℂ) : RiemannSphere) =
      F i (x : RiemannSphere) :=
    coe_riemannSphereFiniteChartHomeomorph_apply
      (F i) (hnorm i).2.2 x
  have hroundtrip_z : ((f z : ℂ) : RiemannSphere) =
      F i (z : RiemannSphere) :=
    coe_riemannSphereFiniteChartHomeomorph_apply
      (F i) (hnorm i).2.2 z
  simpa [hroundtrip_x, hroundtrip_z] using hsphere

/--
%%handwave
name:
  Equicontinuity of normalized quasiconformal sphere maps
statement:
  Every family of normalized $K$-quasiconformal self-homeomorphisms of
  $\widehat{\mathbb C}$ is equicontinuous at every point of the sphere.
proof:
  At $\infty$, use reciprocal coordinates. At the finite point $0$, use the
  normalized origin estimate. Every other finite point is covered by the
  recentered finite-chart estimate.
-/
theorem equicontinuous_normalizedKQuasiconformalRiemannSphere
    {ι : Type*} (K : ℝ)
    (F : ι → RiemannSphere ≃ₜ RiemannSphere)
    (hqc : ∀ i, IsKQuasiconformalRiemannSphere K (F i))
    (hnorm : ∀ i, IsNormalizedRiemannSphereHomeomorph (F i)) :
    Equicontinuous (fun i z ↦ F i z) := by
  intro x
  induction x using OnePoint.rec with
  | infty =>
      exact equicontinuousAt_infty_normalizedKQuasiconformalRiemannSphere
        K F hqc hnorm
  | coe x =>
      by_cases hx : x = 0
      · subst x
        exact equicontinuousAt_zero_normalizedKQuasiconformalRiemannSphere
          K F hqc hnorm
      · exact equicontinuousAt_finite_normalizedKQuasiconformalRiemannSphere
          K F hqc hnorm hx

/--
%%handwave
name:
  Equicontinuity of normalized quasiconformal inverse maps
statement:
  If $\{F_i\}_{i\in I}$ is a family of normalized
  $K$-quasiconformal self-homeomorphisms of $\widehat{\mathbb C}$, then the
  inverse family $\{F_i^{-1}\}_{i\in I}$ is equicontinuous on the sphere.
proof:
  Every inverse remains normalized and $K$-quasiconformal. Apply
  [equicontinuity of the normalized family](lean:JJMath.Quasiconformal.equicontinuous_normalizedKQuasiconformalRiemannSphere).
-/
theorem equicontinuous_symm_normalizedKQuasiconformalRiemannSphere
    {ι : Type*} (K : ℝ)
    (F : ι → RiemannSphere ≃ₜ RiemannSphere)
    (hqc : ∀ i, IsKQuasiconformalRiemannSphere K (F i))
    (hnorm : ∀ i, IsNormalizedRiemannSphereHomeomorph (F i)) :
    Equicontinuous (fun i z ↦ (F i).symm z) := by
  exact equicontinuous_normalizedKQuasiconformalRiemannSphere K
    (fun i ↦ (F i).symm) (fun i ↦ (hqc i).symm) (fun i ↦ (hnorm i).symm)

/--
%%handwave
name:
  Uniform equicontinuity of normalized quasiconformal sphere maps
statement:
  Every family of normalized $K$-quasiconformal self-homeomorphisms of the
  Riemann sphere is uniformly equicontinuous.
proof:
  The family is equicontinuous at every point, and the Riemann sphere is
  compact. Apply the equicontinuous Heine--Cantor theorem.
-/
theorem uniformEquicontinuous_normalizedKQuasiconformalRiemannSphere
    {ι : Type*} (K : ℝ)
    (F : ι → RiemannSphere ≃ₜ RiemannSphere)
    (hqc : ∀ i, IsKQuasiconformalRiemannSphere K (F i))
    (hnorm : ∀ i, IsNormalizedRiemannSphereHomeomorph (F i)) :
    UniformEquicontinuous (fun i z ↦ F i z) := by
  exact CompactSpace.uniformEquicontinuous_of_equicontinuous
    (equicontinuous_normalizedKQuasiconformalRiemannSphere K F hqc hnorm)

/--
%%handwave
name:
  Uniform equicontinuity of normalized quasiconformal inverse maps
statement:
  For every family $\{F_i\}_{i\in I}$ of normalized
  $K$-quasiconformal sphere homeomorphisms, the inverse family
  $\{F_i^{-1}\}_{i\in I}$ is uniformly equicontinuous.
proof:
  The inverse family is equicontinuous on the compact Riemann sphere. Apply
  the equicontinuous Heine--Cantor theorem.
-/
theorem uniformEquicontinuous_symm_normalizedKQuasiconformalRiemannSphere
    {ι : Type*} (K : ℝ)
    (F : ι → RiemannSphere ≃ₜ RiemannSphere)
    (hqc : ∀ i, IsKQuasiconformalRiemannSphere K (F i))
    (hnorm : ∀ i, IsNormalizedRiemannSphereHomeomorph (F i)) :
    UniformEquicontinuous (fun i z ↦ (F i).symm z) := by
  exact CompactSpace.uniformEquicontinuous_of_equicontinuous
    (equicontinuous_symm_normalizedKQuasiconformalRiemannSphere K F hqc hnorm)

/--
%%handwave
name:
  Positive capacity of a normalized pair of planar continua
statement:
  Suppose $E_0\subset\mathbb C$ is compact and connected, contains $0$, and
  reaches Euclidean distance $\delta>0$ from the origin.  Suppose
  $E_1\subset\mathbb C$ is closed and connected, contains $1$, and is
  unbounded.  Then
  $$
    0<\operatorname{cap}_{\mathbb C}(E_0,E_1).
  $$
proof:
  Apply the [uniform capacity separation theorem](lean:JJMath.Quasiconformal.exists_pos_le_planarCondenserCapacity_of_normalized_continua)
  and compare its positive constant with the capacity.
-/
theorem planarCondenserCapacity_pos_of_normalized_continua
    {δ : ℝ} (hδ : 0 < δ)
    {E₀ E₁ : Set ℂ}
    (hE₀compact : IsCompact E₀)
    (hE₀connected : IsConnected E₀)
    (hzero : 0 ∈ E₀)
    (hreaches : ∃ z ∈ E₀, δ ≤ ‖z‖)
    (hE₁closed : IsClosed E₁)
    (hE₁connected : IsConnected E₁)
    (hone : 1 ∈ E₁)
    (hunbounded : ∀ R : ℝ, ∃ z ∈ E₁, R ≤ ‖z‖) :
    0 < planarCondenserCapacity Set.univ E₀ E₁ := by
  obtain ⟨c, hc, hcap⟩ :=
    exists_pos_le_planarCondenserCapacity_of_normalized_continua hδ
  exact hc.trans_le
    (hcap E₀ E₁ hE₀compact hE₀connected hzero hreaches
      hE₁closed hE₁connected hone hunbounded)

/--
%%handwave
name:
  Positive capacity of a compact continuum against an unbounded continuum
statement:
  Let $E_0,E_1\subset\mathbb C$ be disjoint. If $E_0$ is a compact
  nontrivial continuum and $E_1$ is a closed connected unbounded set, then
  $$
    0<\operatorname{cap}_{\mathbb C}(E_0,E_1).
  $$
proof:
  Choose distinct points $x_0,x_1\in E_0$ and a point $y_0\in E_1$.
  The complex-affine map
  $T(z)=(z-x_0)/(y_0-x_0)$ sends $x_0$ to $0$ and $y_0$ to $1$, while the
  image of $x_1$ remains a positive distance from $0$. It preserves
  compactness, connectedness, closedness, unboundedness, and [planar condenser capacity](lean:JJMath.Quasiconformal.planarCondenserCapacity_affineMap_image). Apply [positivity for normalized continua](lean:JJMath.Quasiconformal.planarCondenserCapacity_pos_of_normalized_continua) to the two image plates.
-/
theorem planarCondenserCapacity_pos_of_compact_nontrivial_continuum_of_unbounded_continuum
    {E₀ E₁ : Set ℂ}
    (hE₀compact : IsCompact E₀)
    (hE₀connected : IsConnected E₀)
    (hE₀nontrivial : E₀.Nontrivial)
    (hE₁closed : IsClosed E₁)
    (hE₁connected : IsConnected E₁)
    (hE₁unbounded : ∀ R : ℝ, ∃ z ∈ E₁, R ≤ ‖z‖)
    (hdisjoint : Disjoint E₀ E₁) :
    0 < planarCondenserCapacity Set.univ E₀ E₁ := by
  obtain ⟨x₀, hx₀, x₁, hx₁, hxne⟩ := hE₀nontrivial
  obtain ⟨y₀, hy₀, _hy₀norm⟩ := hE₁unbounded 0
  have hyx : y₀ - x₀ ≠ 0 := by
    rw [sub_ne_zero]
    intro hyx
    exact Set.disjoint_left.1 hdisjoint hx₀ (hyx ▸ hy₀)
  let a : ℂ := (y₀ - x₀)⁻¹
  let c : ℂ := -a * x₀
  have ha : a ≠ 0 := by
    exact inv_ne_zero hyx
  let T : ℂ ≃ₜ ℂ :=
    (Homeomorph.mulLeft₀ a ha).trans (Homeomorph.addRight c)
  have hT_apply (z : ℂ) : T z = a * z + c := by
    simp [T]
  have hT₀ : T x₀ = 0 := by
    rw [hT_apply]
    dsimp [c]
    ring
  have hTy : T y₀ = 1 := by
    rw [hT_apply]
    dsimp [a, c]
    calc
      (y₀ - x₀)⁻¹ * y₀ + -(y₀ - x₀)⁻¹ * x₀ =
          (y₀ - x₀)⁻¹ * (y₀ - x₀) := by ring
      _ = 1 := inv_mul_cancel₀ hyx
  let δ : ℝ := ‖T x₁‖
  have hδ : 0 < δ := by
    rw [norm_pos_iff]
    intro hzero
    have hTx : T x₁ = T x₀ := by
      rw [hzero, hT₀]
    exact hxne (T.injective hTx).symm
  let A₀ : Set ℂ := T '' E₀
  let A₁ : Set ℂ := T '' E₁
  have hA₀compact : IsCompact A₀ :=
    hE₀compact.image T.continuous
  have hA₀connected : IsConnected A₀ :=
    hE₀connected.image T T.continuous.continuousOn
  have hzero : (0 : ℂ) ∈ A₀ :=
    ⟨x₀, hx₀, hT₀⟩
  have hreaches : ∃ z ∈ A₀, δ ≤ ‖z‖ :=
    ⟨T x₁, ⟨x₁, hx₁, rfl⟩, le_rfl⟩
  have hA₁closed : IsClosed A₁ :=
    T.isClosedMap E₁ hE₁closed
  have hA₁connected : IsConnected A₁ :=
    hE₁connected.image T T.continuous.continuousOn
  have hone : (1 : ℂ) ∈ A₁ :=
    ⟨y₀, hy₀, hTy⟩
  have hA₁unbounded : ∀ R : ℝ, ∃ z ∈ A₁, R ≤ ‖z‖ :=
    Homeomorph.image_unbounded T hE₁unbounded
  have hTaffine : (T : ℂ → ℂ) = affineMap a 0 c := by
    funext z
    rw [hT_apply]
    simp [affineMap, realLinearMapOfWirtinger]
  have hpositive :
      0 < planarCondenserCapacity Set.univ A₀ A₁ :=
    planarCondenserCapacity_pos_of_normalized_continua
      hδ hA₀compact hA₀connected hzero hreaches
      hA₁closed hA₁connected hone hA₁unbounded
  have hA₀affine :
      A₀ = affineMap a 0 c '' E₀ := by
    change T '' E₀ = affineMap a 0 c '' E₀
    rw [hTaffine]
  have hA₁affine :
      A₁ = affineMap a 0 c '' E₁ := by
    change T '' E₁ = affineMap a 0 c '' E₁
    rw [hTaffine]
  rw [hA₀affine, hA₁affine,
    planarCondenserCapacity_affineMap_image a c ha E₀ E₁] at hpositive
  exact hpositive

end

end Quasiconformal

end JJMath
