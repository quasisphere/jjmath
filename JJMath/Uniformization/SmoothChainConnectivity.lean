import JJMath.Manifold.OneFormPeriod
import JJMath.RiemannianGeometry.SurfaceMetric
import Mathlib.Analysis.Convex.MetricSpace

/-!
# Smooth singular chains on connected surfaces

This file proves that any two points of a connected smooth surface are the
boundary of a finite smooth singular one-chain.  The proof first joins nearby
points by an affine segment in a convex coordinate ball and then uses
connectedness to show that the resulting equivalence class is the whole
surface.
-/

open Set
open scoped Manifold ContDiff Topology

namespace JJMath
namespace Manifold

noncomputable section

universe v w m

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type w} [TopologicalSpace H]
variable {M : Type m} [TopologicalSpace M] [ChartedSpace H M]
variable (I : ModelWithCorners ℝ E H)

/-- The constant smooth singular zero-simplex at a point. -/
noncomputable def ContMDiffSingularSimplex.point
    (x : M) {r : WithTop ℕ∞} :
    ContMDiffSingularSimplex (I := I) (M := M) 0 r where
  toContinuousMap := ⟨fun _ => x, continuous_const⟩
  contMDiff := ⟨fun _ => x, contMDiff_const.contMDiffOn, fun _ => rfl⟩

@[simp]
theorem ContMDiffSingularSimplex.point_apply
    (x : M) {r : WithTop ℕ∞} (q : StandardSimplex 0) :
    ContMDiffSingularSimplex.point (I := I) (r := r) x q = x :=
  rfl

/-- Two smooth singular simplices are equal when they agree pointwise. -/
theorem ContMDiffSingularSimplex.ext_apply
    {k : ℕ} {r : WithTop ℕ∞}
    {sigma tau : ContMDiffSingularSimplex (I := I) (M := M) k r}
    (h : ∀ q, sigma q = tau q) : sigma = tau := by
  rcases sigma with ⟨sigma, hsigma⟩
  rcases tau with ⟨tau, htau⟩
  have hmaps : sigma = tau := by
    apply ContinuousMap.ext
    exact h
  subst tau
  rfl

@[simp]
theorem ContMDiffSingularSimplex.point_openInclusion
    {U : TopologicalSpace.Opens M} (x : U) {r : WithTop ℕ∞} :
    (ContMDiffSingularSimplex.point (I := I) (r := r) x).openInclusion I U =
      ContMDiffSingularSimplex.point (I := I) (r := r) (x : M) := by
  apply ContMDiffSingularSimplex.ext_apply
  intro q
  rfl

@[simp]
theorem ContMDiffSingularSimplex.point_nestedOpenInclusion
    {U V : TopologicalSpace.Opens M} (hUV : U ≤ V)
    (x : U) {r : WithTop ℕ∞} :
    (ContMDiffSingularSimplex.point (I := I) (r := r) x).nestedOpenInclusion
        I hUV =
      ContMDiffSingularSimplex.point (I := I) (r := r)
        (TopologicalSpace.Opens.inclusion hUV x) := by
  apply ContMDiffSingularSimplex.ext_apply
  intro q
  rfl

end

namespace SmoothChainConnectivity

open JJMath.Uniformization

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
variable [IsManifold SurfaceRealModel ∞ X]

/-- A smooth one-simplex obtained by mapping an affine coordinate segment
back through a surface chart. -/
noncomputable def chartAffineSimplex
    (x : X) (a b : ℂ)
    (hsegment : ∀ q ∈ stdSimplex ℝ (Fin 2),
      q 0 • a + q 1 • b ∈ (chartAt ℂ x).target) :
    ContMDiffSingularSimplex (I := SurfaceRealModel) (M := X) 1 ∞ := by
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ x
  let L : SimplexAmbient 1 → ℂ := fun q => q 0 • a + q 1 • b
  have hL : ContDiff ℝ ∞ L := by fun_prop
  have hmaps : ∀ q : StandardSimplex 1, L q ∈ e.target := by
    intro q
    exact hsegment q q.2
  have hmaps_ext : stdSimplex ℝ (Fin 2) ⊆
      L ⁻¹' (extChartAt SurfaceRealModel x).target := by
    intro q hq
    simpa [L, SurfaceRealModel] using hsegment q hq
  exact
    { toContinuousMap :=
        ⟨fun q => e.symm (L q),
          e.continuousOn_symm.comp_continuous
            (hL.continuous.comp continuous_subtype_val) hmaps⟩
      contMDiff := by
        refine ⟨fun q => e.symm (L q), ?_, fun _ => rfl⟩
        simpa [e, SurfaceRealModel, Function.comp_def] using
          (contMDiffOn_extChartAt_symm (I := SurfaceRealModel) x).comp
            hL.contMDiff.contMDiffOn hmaps_ext }

@[simp]
theorem chartAffineSimplex_apply
    (x : X) (a b : ℂ)
    (hsegment : ∀ q ∈ stdSimplex ℝ (Fin 2),
      q 0 • a + q 1 • b ∈ (chartAt ℂ x).target)
    (q : StandardSimplex 1) :
    chartAffineSimplex x a b hsegment q =
      (chartAt ℂ x).symm (q 0 • a + q 1 • b) :=
  rfl

theorem chartAffineSimplex_face_zero
    (x y : X) (hy : y ∈ (chartAt ℂ x).source)
    (hsegment : ∀ q ∈ stdSimplex ℝ (Fin 2),
      q 0 • (chartAt ℂ x x) + q 1 • (chartAt ℂ x y) ∈
        (chartAt ℂ x).target) :
    (chartAffineSimplex x (chartAt ℂ x x) (chartAt ℂ x y) hsegment).face 0 =
      ContMDiffSingularSimplex.point (I := SurfaceRealModel) y := by
  apply ContMDiffSingularSimplex.ext_apply
  intro q
  change (chartAt ℂ x).symm
      ((simplexFaceMap 0 q : SimplexAmbient 1) 0 • (chartAt ℂ x x) +
        (simplexFaceMap 0 q : SimplexAmbient 1) 1 • (chartAt ℂ x y)) = y
  have hq : (q : SimplexAmbient 0) 0 = 1 := by simpa using q.2.2
  rw [show (simplexFaceMap 0 q : SimplexAmbient 1) 0 = 0 by
      exact simplexAmbientMap_succAbove_apply_omitted 0 q]
  rw [show (simplexFaceMap 0 q : SimplexAmbient 1) 1 =
      (q : SimplexAmbient 0) 0 by
      exact simplexAmbientMap_succAbove_apply_succAbove 0 q 0]
  simp [hq, (chartAt ℂ x).left_inv hy]

theorem chartAffineSimplex_face_one
    (x y : X) (_hy : y ∈ (chartAt ℂ x).source)
    (hsegment : ∀ q ∈ stdSimplex ℝ (Fin 2),
      q 0 • (chartAt ℂ x x) + q 1 • (chartAt ℂ x y) ∈
        (chartAt ℂ x).target) :
    (chartAffineSimplex x (chartAt ℂ x x) (chartAt ℂ x y) hsegment).face 1 =
      ContMDiffSingularSimplex.point (I := SurfaceRealModel) x := by
  apply ContMDiffSingularSimplex.ext_apply
  intro q
  change (chartAt ℂ x).symm
      ((simplexFaceMap 1 q : SimplexAmbient 1) 0 • (chartAt ℂ x x) +
        (simplexFaceMap 1 q : SimplexAmbient 1) 1 • (chartAt ℂ x y)) = x
  have hq : (q : SimplexAmbient 0) 0 = 1 := by simpa using q.2.2
  rw [show (simplexFaceMap 1 q : SimplexAmbient 1) 1 = 0 by
      exact simplexAmbientMap_succAbove_apply_omitted 1 q]
  rw [show (simplexFaceMap 1 q : SimplexAmbient 1) 0 =
      (q : SimplexAmbient 0) 0 by
      exact simplexAmbientMap_succAbove_apply_succAbove 1 q 0]
  simp [hq]

/-- Two surface points are smoothly chain joined when their formal difference
is the boundary of a smooth singular one-chain. -/
def SmoothChainJoined (x y : X) : Prop :=
  ∃ c : SingularChain (I := SurfaceRealModel) (M := X) 1 ∞,
    boundary (I := SurfaceRealModel) c =
      Finsupp.single (ContMDiffSingularSimplex.point
        (I := SurfaceRealModel) y) (1 : ℤ) -
      Finsupp.single (ContMDiffSingularSimplex.point
        (I := SurfaceRealModel) x) (1 : ℤ)

theorem smoothChainJoined_refl (x : X) : SmoothChainJoined x x := by
  refine ⟨0, ?_⟩
  simp

theorem smoothChainJoined_symm {x y : X} :
    SmoothChainJoined x y → SmoothChainJoined y x := by
  rintro ⟨c, hc⟩
  refine ⟨-c, ?_⟩
  rw [map_neg, hc]
  abel

theorem smoothChainJoined_trans {x y z : X} :
    SmoothChainJoined x y → SmoothChainJoined y z → SmoothChainJoined x z := by
  rintro ⟨c, hc⟩ ⟨d, hd⟩
  refine ⟨c + d, ?_⟩
  rw [map_add, hc, hd]
  abel

theorem boundary_chartAffineSimplex_single
    (x y : X) (hy : y ∈ (chartAt ℂ x).source)
    (hsegment : ∀ q ∈ stdSimplex ℝ (Fin 2),
      q 0 • (chartAt ℂ x x) + q 1 • (chartAt ℂ x y) ∈
        (chartAt ℂ x).target) :
    boundary (I := SurfaceRealModel)
      (Finsupp.single
        (chartAffineSimplex x (chartAt ℂ x x) (chartAt ℂ x y) hsegment)
        (1 : ℤ)) =
      Finsupp.single (ContMDiffSingularSimplex.point
        (I := SurfaceRealModel) y) (1 : ℤ) -
      Finsupp.single (ContMDiffSingularSimplex.point
        (I := SurfaceRealModel) x) (1 : ℤ) := by
  simp [boundary, Finsupp.linearCombination_single, Fin.sum_univ_two,
    chartAffineSimplex_face_zero x y hy hsegment,
    chartAffineSimplex_face_one x y hy hsegment, sub_eq_add_neg]

theorem exists_open_smoothChainJoined_from
    (x : X) : ∃ W : Set X, IsOpen W ∧ x ∈ W ∧
      ∀ y ∈ W, SmoothChainJoined x y := by
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ x
  have hex_target : e x ∈ e.target := by simp [e]
  have htarget_nhds : e.target ∈ nhds (e x) :=
    e.open_target.mem_nhds hex_target
  rcases Metric.nhds_basis_ball.mem_iff.mp htarget_nhds with
    ⟨r, hr, hball_target⟩
  let B : Set ℂ := Metric.ball (e x) r
  let W : Set X := e.symm '' B
  have hB_open : IsOpen B := Metric.isOpen_ball
  have hW_open : IsOpen W :=
    e.isOpen_image_symm_of_subset_target hB_open hball_target
  have hxW : x ∈ W := by
    refine ⟨e x, Metric.mem_ball_self hr, ?_⟩
    exact e.left_inv (by simp [e])
  refine ⟨W, hW_open, hxW, ?_⟩
  intro y hyW
  rcases hyW with ⟨b, hbB, rfl⟩
  have hb_target : b ∈ e.target := hball_target hbB
  have hy_source : e.symm b ∈ e.source := e.map_target hb_target
  have hcoord_y : e (e.symm b) = b := e.right_inv hb_target
  have hsegment : ∀ q ∈ stdSimplex ℝ (Fin 2),
      q 0 • (chartAt ℂ x x) + q 1 • (chartAt ℂ x (e.symm b)) ∈
        (chartAt ℂ x).target := by
    intro q hq
    apply hball_target
    change q 0 • e x + q 1 • e (e.symm b) ∈ B
    rw [hcoord_y]
    exact (convex_ball (e x) r) (Metric.mem_ball_self hr) hbB
      (hq.1 0) (hq.1 1) (by simpa [Fin.sum_univ_two] using hq.2)
  refine ⟨Finsupp.single
      (chartAffineSimplex x (chartAt ℂ x x) (chartAt ℂ x (e.symm b)) hsegment)
      (1 : ℤ), ?_⟩
  exact boundary_chartAffineSimplex_single x (e.symm b) hy_source hsegment

/--
%%handwave
name:
  Smooth-chain connectivity of a connected surface
statement:
  If \(X\) is a connected smooth surface, then for every \(x,y\in X\) there
  is a finite smooth singular one-chain \(c\) with
  \[
    \partial c=y-x.
  \]
proof:
  Points sufficiently close in a convex coordinate ball are joined by one
  affine smooth simplex.  For fixed \(x\), the set of points smoothly
  chain-joined to \(x\) and its complement are therefore both open.  It is
  nonempty, so connectedness makes it all of \(X\).
-/
theorem smoothChainJoined_all [ConnectedSpace X] (x y : X) :
    SmoothChainJoined x y := by
  let S : Set X := {z | SmoothChainJoined x z}
  have hS_open : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    rcases exists_open_smoothChainJoined_from z with ⟨W, hWopen, hzW, hW⟩
    refine Filter.mem_of_superset (hWopen.mem_nhds hzW) ?_
    intro w hw
    exact smoothChainJoined_trans hz (hW w hw)
  have hS_compl_open : IsOpen Sᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    rcases exists_open_smoothChainJoined_from z with ⟨W, hWopen, hzW, hW⟩
    refine Filter.mem_of_superset (hWopen.mem_nhds hzW) ?_
    intro w hw hS_w
    exact hz (smoothChainJoined_trans hS_w (smoothChainJoined_symm (hW w hw)))
  have hS_clopen : IsClopen S :=
    ⟨isOpen_compl_iff.mp hS_compl_open, hS_open⟩
  have hS_nonempty : S.Nonempty := ⟨x, smoothChainJoined_refl x⟩
  have hS_univ : S = univ := hS_clopen.eq_univ hS_nonempty
  change y ∈ S
  rw [hS_univ]
  exact mem_univ y

/--
%%handwave
name:
  Closed zero-forms are determined at one point
statement:
  Two smooth zero-forms on a connected surface with equal exterior
  derivatives and equal values at one point are equal everywhere.
proof:
  Join the chosen point to an arbitrary point by a finite smooth singular
  one-chain.  Stokes' theorem expresses the change of each zero-form as the
  integral of its exterior derivative along that chain, so the two changes
  agree.
-/
theorem smoothZeroForm_eq_of_differential_eq_of_eq_at
    [ConnectedSpace X]
    (theta eta : SmoothForms
      (I := SurfaceRealModel) (M := X) ℝ 0)
    (x₀ : X)
    (hd :
      deRhamDifferential
          (I := SurfaceRealModel) (M := X) (A := ℝ) 0 theta =
        deRhamDifferential
          (I := SurfaceRealModel) (M := X) (A := ℝ) 0 eta)
    (hbase :
      theta.toFun x₀ (fun i : Fin 0 => nomatch i) =
        eta.toFun x₀ (fun i : Fin 0 => nomatch i)) :
    theta = eta := by
  apply DifferentialForm.ext
  intro x
  ext v
  rw [show v = (fun i : Fin 0 => nomatch i) from Subsingleton.elim _ _]
  rcases smoothChainJoined_all x₀ x with ⟨c, hc⟩
  have htheta :=
    integrateSmoothChain_deRhamDifferential_zero_eq_boundary
      (I := SurfaceRealModel) theta c
  have heta :=
    integrateSmoothChain_deRhamDifferential_zero_eq_boundary
      (I := SurfaceRealModel) eta c
  have hleft :
      integrateSmoothChain (I := SurfaceRealModel)
          (deRhamDifferential
            (I := SurfaceRealModel) (M := X) (A := ℝ) 0 theta) c =
        integrateSmoothChain (I := SurfaceRealModel)
          (deRhamDifferential
            (I := SurfaceRealModel) (M := X) (A := ℝ) 0 eta) c := by
    rw [hd]
  rw [htheta, heta, hc] at hleft
  simp [integrateChain, integrateChainHom, integrateSimplex,
    pullbackSimplexIntegrationTheory,
    integrateSimplexByPullback_zeroForm_zero, sub_eq_add_neg] at hleft
  calc
    theta.toFun x (fun i : Fin 0 => nomatch i) =
        (theta.toFun x (fun i : Fin 0 => nomatch i) -
          theta.toFun x₀ (fun i : Fin 0 => nomatch i)) +
            theta.toFun x₀ (fun i : Fin 0 => nomatch i) := by ring
    _ =
        (eta.toFun x (fun i : Fin 0 => nomatch i) -
          eta.toFun x₀ (fun i : Fin 0 => nomatch i)) +
            theta.toFun x₀ (fun i : Fin 0 => nomatch i) := by
      rw [show
        theta.toFun x (fun i : Fin 0 => nomatch i) -
            theta.toFun x₀ (fun i : Fin 0 => nomatch i) =
          eta.toFun x (fun i : Fin 0 => nomatch i) -
            eta.toFun x₀ (fun i : Fin 0 => nomatch i) by
          simpa [sub_eq_add_neg] using hleft]
    _ = eta.toFun x (fun i : Fin 0 => nomatch i) := by
      rw [hbase]
      ring

end SmoothChainConnectivity
end Manifold
end JJMath
