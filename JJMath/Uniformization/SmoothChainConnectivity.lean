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

/--
%%handwave
name:
  Evaluation of a constant smooth zero-simplex
statement:
  For a point \(x\in M\), the constant smooth singular zero-simplex at
  \(x\) takes its unique simplex point to \(x\).
proof:
  The underlying map of the zero-simplex is, by construction, the constant
  map with value \(x\).
-/
@[simp]
theorem ContMDiffSingularSimplex.point_apply
    (x : M) {r : WithTop ℕ∞} (q : StandardSimplex 0) :
    ContMDiffSingularSimplex.point (I := I) (r := r) x q = x :=
  rfl

/--
%%handwave
name:
  Extensionality for smooth singular simplices
statement:
  If two smooth singular \(k\)-simplices \(\sigma\) and \(\tau\) satisfy
  \(\sigma(q)=\tau(q)\) for every \(q\in\Delta^k\), then
  \(\sigma=\tau\).
proof:
  Pointwise equality identifies the underlying continuous maps.  The
  smoothness witnesses are propositions, so the two structured simplices
  are equal.
-/
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

/--
%%handwave
name:
  Inclusion of a constant zero-simplex into the ambient manifold
statement:
  Let \(U\subseteq M\) be open and \(x\in U\).  Including the constant
  zero-simplex at \(x\) from \(U\) into \(M\) gives the constant
  zero-simplex at the ambient point \(x\in M\).
proof:
  Both simplices have the same constant value at every point of
  \(\Delta^0\), so simplex extensionality applies.
-/
@[simp]
theorem ContMDiffSingularSimplex.point_openInclusion
    {U : TopologicalSpace.Opens M} (x : U) {r : WithTop ℕ∞} :
    (ContMDiffSingularSimplex.point (I := I) (r := r) x).openInclusion I U =
      ContMDiffSingularSimplex.point (I := I) (r := r) (x : M) := by
  apply ContMDiffSingularSimplex.ext_apply
  intro q
  rfl

/--
%%handwave
name:
  Nested inclusion of a constant zero-simplex
statement:
  If \(U\subseteq V\) are open subsets of \(M\) and \(x\in U\), then
  including the constant zero-simplex at \(x\) from \(U\) into \(V\) gives
  the constant zero-simplex at the image of \(x\) in \(V\).
proof:
  Both sides are pointwise the same constant map into \(V\).
-/
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

/--
%%handwave
name:
  Evaluation of an affine simplex in a surface chart
statement:
  Suppose the affine segment from \(a\) to \(b\) lies in a surface-chart
  target.  The corresponding smooth singular one-simplex satisfies
  \[
    \sigma(q)=\phi^{-1}\bigl(q_0a+q_1b\bigr)
    \qquad(q\in\Delta^1).
  \]
proof:
  This is the defining formula for the affine coordinate simplex.
-/
@[simp]
theorem chartAffineSimplex_apply
    (x : X) (a b : ℂ)
    (hsegment : ∀ q ∈ stdSimplex ℝ (Fin 2),
      q 0 • a + q 1 • b ∈ (chartAt ℂ x).target)
    (q : StandardSimplex 1) :
    chartAffineSimplex x a b hsegment q =
      (chartAt ℂ x).symm (q 0 • a + q 1 • b) :=
  rfl

/--
%%handwave
name:
  Terminal face of an affine chart simplex
statement:
  Let \(\sigma\) be the affine chart simplex from \(x\) to \(y\).  Its
  zeroth face is the constant zero-simplex at \(y\).
proof:
  On the zeroth face of \(\Delta^1\), the barycentric coordinates are
  \((0,1)\).  Thus the affine combination is \(\phi_x(y)\), whose
  inverse-chart image is \(y\).
-/
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

/--
%%handwave
name:
  Initial face of an affine chart simplex
statement:
  Let \(\sigma\) be the affine chart simplex from \(x\) to \(y\).  Its
  first face is the constant zero-simplex at \(x\).
proof:
  On the first face of \(\Delta^1\), the barycentric coordinates are
  \((1,0)\).  The affine combination is therefore \(\phi_x(x)\), and the
  inverse chart returns \(x\).
-/
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

/--
%%handwave
name:
  Reflexivity of smooth-chain joining
statement:
  Every point \(x\in X\) is smoothly chain joined to itself.
proof:
  The zero one-chain has boundary \(0=x-x\).
-/
theorem smoothChainJoined_refl (x : X) : SmoothChainJoined x x := by
  refine ⟨0, ?_⟩
  simp

/--
%%handwave
name:
  Symmetry of smooth-chain joining
statement:
  If a smooth singular one-chain has boundary \(y-x\), then some smooth
  singular one-chain has boundary \(x-y\).
proof:
  Negating the original chain negates its boundary.
-/
theorem smoothChainJoined_symm {x y : X} :
    SmoothChainJoined x y → SmoothChainJoined y x := by
  rintro ⟨c, hc⟩
  refine ⟨-c, ?_⟩
  rw [map_neg, hc]
  abel

/--
%%handwave
name:
  Transitivity of smooth-chain joining
statement:
  If \(x\) is smoothly chain joined to \(y\) and \(y\) is smoothly chain
  joined to \(z\), then \(x\) is smoothly chain joined to \(z\).
proof:
  Add chains with boundaries \(y-x\) and \(z-y\); linearity of the boundary
  operator gives the telescoping boundary \(z-x\).
-/
theorem smoothChainJoined_trans {x y z : X} :
    SmoothChainJoined x y → SmoothChainJoined y z → SmoothChainJoined x z := by
  rintro ⟨c, hc⟩ ⟨d, hd⟩
  refine ⟨c + d, ?_⟩
  rw [map_add, hc, hd]
  abel

/--
%%handwave
name:
  Boundary of an affine chart simplex
statement:
  Let \(\sigma\) be the affine chart one-simplex from \(x\) to \(y\).
  As a singular one-chain with coefficient \(1\), its boundary is
  \[
    \partial\sigma=[y]-[x].
  \]
proof:
  The alternating boundary of a one-simplex is its zeroth face minus its
  first face.  These faces are respectively the constant zero-simplices at
  \(y\) and \(x\).
-/
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

/--
%%handwave
name:
  Nearby points are smoothly chain joined
statement:
  For every \(x\in X\), there is an open neighborhood \(W\) of \(x\) such
  that every \(y\in W\) is smoothly chain joined to \(x\).
proof:
  Choose a metric ball about \(\phi_x(x)\) contained in the chart target and
  pull it back to \(X\).  Convexity keeps the affine segment from
  \(\phi_x(x)\) to \(\phi_x(y)\) inside the ball, so its inverse-chart image
  is a smooth one-simplex with boundary \(y-x\).
-/
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
