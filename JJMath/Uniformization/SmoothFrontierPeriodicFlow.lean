import JJMath.Uniformization.SmoothFrontierTangentField
import JJMath.Uniformization.SmoothSurfaceVectorFieldFlow
import JJMath.Manifold.AnnularPeriod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Complete tangent flows on compact smooth frontiers

The oriented tangent field on a compact smooth frontier is complete.  The
point of using the invariant-subset uniform-time lemma is that the ambient
field need not be complete away from the frontier.
-/

open Bundle Filter Function Set
open Complex
open scoped Manifold Topology ContDiff ComplexConjugate

namespace JJMath.Uniformization

noncomputable section

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
variable [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]

/--
%%handwave
name:
  Smooth restriction to an open codomain
statement:
  Let \(f:M\to N\) be a \(C^n\) map between smooth manifolds, and let
  \(U\subseteq N\) be open.  If \(f(M)\subseteq U\), then the same function,
  regarded as a map \(M\to U\), is \(C^n\).
proof:
  Near each value \(f(x)\), the inclusion into \(U\) has a smooth local
  retraction equal to the identity on \(U\).  Compose this retraction with
  \(f\) and use local equality.
-/
theorem ContMDiff.codRestrict_open
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H G M N : Type*}
    [TopologicalSpace H] [TopologicalSpace G]
    [TopologicalSpace M] [TopologicalSpace N]
    {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ F G}
    [ChartedSpace H M] [ChartedSpace G N]
    {n : WithTop ℕ∞} {f : M → N}
    (hf : ContMDiff I J n f) (U : TopologicalSpace.Opens N)
    (hmem : ∀ x, f x ∈ U) :
    ContMDiff I J n (fun x => (⟨f x, hmem x⟩ : U)) := by
  classical
  intro x
  let qU : U := ⟨f x, hmem x⟩
  let retract : N → U := fun y =>
    if hy : y ∈ U then ⟨y, hy⟩ else qU
  have hretract : ContMDiffAt J J n retract (f x) := by
    rw [← contMDiffAt_subtype_iff (U := U) (x := qU)]
    have heq : (fun y : U => retract y) = id := by
      funext y
      simp [retract]
    rw [heq]
    exact contMDiffAt_id
  have hcomp := hretract.comp x (hf x)
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [] with y
  simp [retract, hmem]

/-- A symmetric open interval, regarded as an open real submanifold. -/
def symmetricOpenInterval (rho : ℝ) : TopologicalSpace.Opens ℝ :=
  ⟨Ioo (-rho) rho, isOpen_Ioo⟩

/-- Every nonempty symmetric open interval is smoothly diffeomorphic to the
real line. -/
noncomputable def symmetricOpenIntervalDiffeomorphReal
    (rho : ℝ) (hrho : 0 < rho) :
    symmetricOpenInterval rho ≃ₘ⟮
      modelWithCornersSelf ℝ ℝ, modelWithCornersSelf ℝ ℝ⟯ ℝ := by
  classical
  let k : ℝ := Real.pi / (2 * rho)
  let kinv : ℝ := 2 * rho / Real.pi
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hrho_ne : rho ≠ 0 := ne_of_gt hrho
  have hkpos : 0 < k := div_pos Real.pi_pos (mul_pos (by norm_num) hrho)
  have hkinvpos : 0 < kinv := div_pos (mul_pos (by norm_num) hrho) Real.pi_pos
  have hk_left : k * (-rho) = -(Real.pi / 2) := by
    dsimp [k]
    field_simp
  have hk_right : k * rho = Real.pi / 2 := by
    dsimp [k]
    field_simp
  have hkinv_left : kinv * (-(Real.pi / 2)) = -rho := by
    dsimp [kinv]
    field_simp
  have hkinv_right : kinv * (Real.pi / 2) = rho := by
    dsimp [kinv]
    field_simp
  have hk_mem : ∀ x : symmetricOpenInterval rho,
      k * (x : ℝ) ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    intro x
    constructor
    · rw [← hk_left]
      exact mul_lt_mul_of_pos_left x.2.1 hkpos
    · rw [← hk_right]
      exact mul_lt_mul_of_pos_left x.2.2 hkpos
  have hinv_mem : ∀ y : ℝ,
      kinv * Real.arctan y ∈ Ioo (-rho) rho := by
    intro y
    constructor
    · rw [← hkinv_left]
      exact mul_lt_mul_of_pos_left (Real.neg_pi_div_two_lt_arctan y) hkinvpos
    · rw [← hkinv_right]
      exact mul_lt_mul_of_pos_left (Real.arctan_lt_pi_div_two y) hkinvpos
  let equiv : symmetricOpenInterval rho ≃ ℝ :=
    { toFun := fun x => Real.tan (k * (x : ℝ))
      invFun := fun y => ⟨kinv * Real.arctan y, hinv_mem y⟩
      left_inv := by
        intro x
        apply Subtype.ext
        change kinv * Real.arctan (Real.tan (k * (x : ℝ))) = (x : ℝ)
        rw [Real.arctan_tan (hk_mem x).1 (hk_mem x).2]
        dsimp [k, kinv]
        field_simp
      right_inv := by
        intro y
        change Real.tan (k * (kinv * Real.arctan y)) = y
        have hscale : k * (kinv * Real.arctan y) = Real.arctan y := by
          dsimp [k, kinv]
          field_simp
        rw [hscale, Real.tan_arctan] }
  have hto : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ ℝ) ∞ equiv := by
    intro x
    change ContMDiffAt (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun x : symmetricOpenInterval rho => Real.tan (k * (x : ℝ))) x
    have hlin : ContDiffAt ℝ ∞ (fun y : ℝ => k * y) (x : ℝ) :=
      contDiffAt_const.mul contDiffAt_id
    have htan : ContDiffAt ℝ ∞ Real.tan (k * (x : ℝ)) :=
      Real.contDiffAt_tan.mpr
        (Real.cos_pos_of_mem_Ioo (hk_mem x)).ne'
    have hamb : ContMDiffAt (modelWithCornersSelf ℝ ℝ)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun y : ℝ => Real.tan (k * y)) (x : ℝ) :=
      (htan.comp (x : ℝ) hlin).contMDiffAt
    exact hamb.comp x (contMDiff_subtype_val x)
  have hinvRaw : ContDiff ℝ ∞
      (fun y : ℝ => kinv * Real.arctan y) :=
    contDiff_const.mul Real.contDiff_arctan
  have hinv : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ ℝ) ∞ equiv.symm := by
    change ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun y : ℝ =>
        (⟨kinv * Real.arctan y, hinv_mem y⟩ : symmetricOpenInterval rho))
    exact ContMDiff.codRestrict_open hinvRaw.contMDiff
      (symmetricOpenInterval rho) hinv_mem
  exact
    { toEquiv := equiv
      contMDiff_toFun := hto
      contMDiff_invFun := hinv }

/--
%%handwave
name:
  The tangent coordinate preserves negativity
statement:
  For \(\rho>0\) and \(x\in(-\rho,\rho)\),
  \[
    \tan\!\left(\frac{\pi x}{2\rho}\right)<0
    \quad\Longleftrightarrow\quad x<0.
  \]
proof:
  The scaled argument lies in \((-\pi/2,\pi/2)\), where the tangent function
  has the same sign as its argument; the scaling factor is positive.
-/
theorem symmetricOpenIntervalDiffeomorphReal_lt_zero_iff
    (rho : ℝ) (hrho : 0 < rho) (x : symmetricOpenInterval rho) :
    symmetricOpenIntervalDiffeomorphReal rho hrho x < 0 ↔ (x : ℝ) < 0 := by
  let k : ℝ := Real.pi / (2 * rho)
  have hkpos : 0 < k := div_pos Real.pi_pos (mul_pos (by norm_num) hrho)
  have hleft : -(Real.pi / 2) < k * (x : ℝ) := by
    have hscale : k * (-rho) = -(Real.pi / 2) := by
      dsimp [k]
      field_simp
    rw [← hscale]
    exact mul_lt_mul_of_pos_left x.2.1 hkpos
  have hright : k * (x : ℝ) < Real.pi / 2 := by
    have hscale : k * rho = Real.pi / 2 := by
      dsimp [k]
      field_simp
    rw [← hscale]
    exact mul_lt_mul_of_pos_left x.2.2 hkpos
  change Real.tan (k * (x : ℝ)) < 0 ↔ (x : ℝ) < 0
  constructor
  · intro htan
    by_contra hx
    have hxnonneg : 0 ≤ (x : ℝ) := le_of_not_gt hx
    have hargnonneg : 0 ≤ k * (x : ℝ) := mul_nonneg hkpos.le hxnonneg
    have := Real.tan_nonneg_of_nonneg_of_le_pi_div_two hargnonneg hright.le
    linarith
  · intro hx
    exact Real.tan_neg_of_neg_of_pi_div_two_lt
      (mul_neg_of_pos_of_neg hkpos hx) hleft

/--
%%handwave
name:
  The tangent coordinate preserves positivity
statement:
  For \(\rho>0\) and \(x\in(-\rho,\rho)\),
  \[
    0<\tan\!\left(\frac{\pi x}{2\rho}\right)
    \quad\Longleftrightarrow\quad 0<x.
  \]
proof:
  The scaled argument lies in \((-\pi/2,\pi/2)\), where tangent preserves
  strict sign, and the scaling factor is positive.
-/
theorem symmetricOpenIntervalDiffeomorphReal_pos_iff
    (rho : ℝ) (hrho : 0 < rho) (x : symmetricOpenInterval rho) :
    0 < symmetricOpenIntervalDiffeomorphReal rho hrho x ↔ 0 < (x : ℝ) := by
  let k : ℝ := Real.pi / (2 * rho)
  have hkpos : 0 < k := div_pos Real.pi_pos (mul_pos (by norm_num) hrho)
  have hleft : -(Real.pi / 2) < k * (x : ℝ) := by
    have hscale : k * (-rho) = -(Real.pi / 2) := by
      dsimp [k]
      field_simp
    rw [← hscale]
    exact mul_lt_mul_of_pos_left x.2.1 hkpos
  have hright : k * (x : ℝ) < Real.pi / 2 := by
    have hscale : k * rho = Real.pi / 2 := by
      dsimp [k]
      field_simp
    rw [← hscale]
    exact mul_lt_mul_of_pos_left x.2.2 hkpos
  change 0 < Real.tan (k * (x : ℝ)) ↔ 0 < (x : ℝ)
  constructor
  · intro htan
    by_contra hx
    have hxnonpos : (x : ℝ) ≤ 0 := le_of_not_gt hx
    have hargnonpos : k * (x : ℝ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hkpos.le hxnonpos
    have := Real.tan_nonpos_of_nonpos_of_neg_pi_div_two_le hargnonpos hleft.le
    linarith
  · intro hx
    exact Real.tan_pos_of_pos_of_lt_pi_div_two
      (mul_pos hkpos hx) hright

/-- The negative real axis as an open one-dimensional manifold. -/
def negativeRealOpen : TopologicalSpace.Opens ℝ :=
  ⟨Iio 0, isOpen_Iio⟩

/-- The negative real axis is smoothly diffeomorphic to the real line via
the real logarithm. -/
noncomputable def negativeRealDiffeomorphReal :
    negativeRealOpen ≃ₘ⟮modelWithCornersSelf ℝ ℝ,
      modelWithCornersSelf ℝ ℝ⟯ ℝ := by
  let equiv : negativeRealOpen ≃ ℝ :=
    { toFun := fun x => Real.log (x : ℝ)
      invFun := fun y => ⟨-Real.exp y, neg_lt_zero.mpr (Real.exp_pos y)⟩
      left_inv := by
        intro x
        apply Subtype.ext
        simpa using congrArg Neg.neg (Real.exp_log_of_neg x.2)
      right_inv := by
        intro y
        simp [Real.log_neg_eq_log] }
  have hto : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ ℝ) ∞ equiv := by
    intro x
    have hlog : ContDiffAt ℝ ∞ Real.log (x : ℝ) :=
      Real.contDiffAt_log.mpr x.2.ne
    exact hlog.contMDiffAt.comp x (contMDiff_subtype_val x)
  have hinvRaw : ContDiff ℝ ∞ (fun y : ℝ => -Real.exp y) :=
    Real.contDiff_exp.neg
  have hinv : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ ℝ) ∞ equiv.symm :=
    ContMDiff.codRestrict_open hinvRaw.contMDiff negativeRealOpen
      (fun y => neg_lt_zero.mpr (Real.exp_pos y))
  exact
    { toEquiv := equiv
      contMDiff_toFun := hto
      contMDiff_invFun := hinv }

/-- The negative half of the standard annular cylinder. -/
def negativeAnnularCylinderOpen :
    TopologicalSpace.Opens (Circle × ℝ) :=
  ⟨univ ×ˢ Iio 0, isOpen_univ.prod isOpen_Iio⟩

/-- Reassociate the subtype defining the negative half-cylinder with the
product of the circle and the negative real axis. -/
noncomputable def negativeAnnularCylinderOpenDiffeomorphProduct :
    negativeAnnularCylinderOpen ≃ₘ⟮
      JJMath.Manifold.AnnularCylinderModel,
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))).prod
        (modelWithCornersSelf ℝ ℝ)⟯ Circle × negativeRealOpen := by
  let equiv : negativeAnnularCylinderOpen ≃ Circle × negativeRealOpen :=
    { toFun := fun z => (z.1.1, ⟨z.1.2, z.2.2⟩)
      invFun := fun z => ⟨(z.1, z.2.1), ⟨mem_univ _, z.2.2⟩⟩
      left_inv := by intro z; rfl
      right_inv := by intro z; rfl }
  have hval : ContMDiff JJMath.Manifold.AnnularCylinderModel
      JJMath.Manifold.AnnularCylinderModel ∞
      (fun z : negativeAnnularCylinderOpen => (z : Circle × ℝ)) :=
    contMDiff_subtype_val
  have htoSecond : ContMDiff JJMath.Manifold.AnnularCylinderModel
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun z : negativeAnnularCylinderOpen =>
        (⟨z.1.2, z.2.2⟩ : negativeRealOpen)) :=
    ContMDiff.codRestrict_open hval.snd negativeRealOpen
      (fun z => z.2.2)
  have hto : ContMDiff JJMath.Manifold.AnnularCylinderModel
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))).prod
        (modelWithCornersSelf ℝ ℝ)) ∞ equiv :=
    hval.fst.prodMk htoSecond
  have hinvRaw : ContMDiff
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))).prod
        (modelWithCornersSelf ℝ ℝ))
      JJMath.Manifold.AnnularCylinderModel ∞
      (fun z : Circle × negativeRealOpen => (z.1, (z.2 : ℝ))) := by
    exact contMDiff_fst.prodMk
      ((contMDiff_subtype_val (I := modelWithCornersSelf ℝ ℝ)).comp
        contMDiff_snd)
  have hinv : ContMDiff
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))).prod
        (modelWithCornersSelf ℝ ℝ))
      JJMath.Manifold.AnnularCylinderModel ∞ equiv.symm :=
    ContMDiff.codRestrict_open hinvRaw negativeAnnularCylinderOpen
      (fun z => ⟨mem_univ _, z.2.2⟩)
  exact
    { toEquiv := equiv
      contMDiff_toFun := hto
      contMDiff_invFun := hinv }

/-- The negative half of the annular cylinder is itself an annular
cylinder. -/
noncomputable def negativeAnnularCylinderOpenDiffeomorphAnnularCylinder :
    negativeAnnularCylinderOpen ≃ₘ⟮
      JJMath.Manifold.AnnularCylinderModel,
      JJMath.Manifold.AnnularCylinderModel⟯ Circle × ℝ :=
  negativeAnnularCylinderOpenDiffeomorphProduct.trans
    ((Diffeomorph.refl
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) Circle ∞).prodCongr
        negativeRealDiffeomorphReal)

/-- The sine of the short signed angle from `z` to `w`. -/
noncomputable def circleLocalSine (z w : Circle) : ℝ :=
  (conj (z : ℂ) * (w : ℂ)).im

/-- The short signed angle from `z`, defined on the semicircle where the
arcsine branch is valid.  Only its germ at `z` is used. -/
noncomputable def circleLocalAngle (z w : Circle) : ℝ :=
  Real.arcsin (circleLocalSine z w)

/--
%%handwave
name:
  Smoothness of the centered local angle on the circle
statement:
  For \(z\in S^1\), the function
  \[
    w\longmapsto \arcsin\!\bigl(\operatorname{Im}(\overline z w)\bigr)
  \]
  is smooth at \(w=z\).
proof:
  The imaginary part of \(\overline z w\) is smooth in \(w\) and vanishes at
  \(w=z\).  The arcsine function is smooth in a neighborhood of zero.
-/
theorem circleLocalAngle_contMDiffAt (z : Circle) :
    ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ ℝ) ∞
      (circleLocalAngle z) z := by
  letI : Fact (Module.finrank ℝ ℂ = 1 + 1) :=
    finrank_real_complex_fact'
  let coeCircle : Circle → ℂ := fun w => (w : ℂ)
  have hcoe : ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ ℂ) ∞
      coeCircle := contMDiff_coe_sphere
  have hmul : ContDiff ℝ ∞ (fun w : ℂ => conj (z : ℂ) * w) :=
    contDiff_const.mul contDiff_id
  have him : ContDiff ℝ ∞ (fun w : ℂ => w.im) :=
    Complex.imCLM.contDiff
  have hsine : ContMDiffAt
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ ℝ) ∞
      (circleLocalSine z) z := by
    simpa only [circleLocalSine, coeCircle, Function.comp_def] using
      him.contMDiff.comp (hmul.contMDiff.comp hcoe) z
  have hsine_zero : circleLocalSine z z = 0 := by
    simp [circleLocalSine, ← Circle.coe_inv_eq_conj]
  have harcsin : ContDiffAt ℝ ∞ Real.arcsin (circleLocalSine z z) := by
    rw [hsine_zero]
    exact Real.contDiffAt_arcsin (by norm_num) (by norm_num)
  exact harcsin.contMDiffAt.comp z hsine

/--
%%handwave
name:
  Local circle sine along exponential coordinates
statement:
  For all \(a,b\in\mathbb R\),
  \[
    \operatorname{Im}\!\left(\overline{e^{ia}}e^{ib}\right)
      =\sin(b-a).
  \]
proof:
  The product is \(e^{i(b-a)}\); taking its imaginary part gives the sine.
-/
theorem circleLocalSine_exp (a b : ℝ) :
    circleLocalSine (Circle.exp a) (Circle.exp b) = Real.sin (b - a) := by
  rw [circleLocalSine, ← Circle.coe_inv_eq_conj, ← Circle.coe_mul]
  have hcircle : (Circle.exp a)⁻¹ * Circle.exp b = Circle.exp (b - a) := by
    rw [← Circle.exp_neg, ← Circle.exp_add]
    congr 1
    ring
  rw [hcircle, Circle.coe_exp]
  exact Complex.exp_ofReal_mul_I_im (b - a)

/--
%%handwave
name:
  A centered angle is a local inverse to the circle exponential
statement:
  For \(t_0\in\mathbb R\), the map
  \[
    z\longmapsto
    \exp\!\left(i\left[t_0+
      \arcsin\operatorname{Im}(e^{-it_0}z)\right]\right)
  \]
  agrees with \(z\) in a neighborhood of \(e^{it_0}\in S^1\).
proof:
  For \(t\) near \(t_0\), the difference \(t-t_0\) lies in
  \([-\pi/2,\pi/2]\), so arcsine inverts sine.  The circle exponential is a
  local homeomorphism and transfers this identity to a neighborhood of
  \(e^{it_0}\).
-/
theorem circleExp_add_circleLocalAngle_eventuallyEq (t₀ : ℝ) :
    (fun z : Circle =>
      Circle.exp (t₀ + circleLocalAngle (Circle.exp t₀) z)) =ᶠ[
        nhds (Circle.exp t₀)] id := by
  have hphase : ∀ᶠ t in nhds t₀,
      t₀ + circleLocalAngle (Circle.exp t₀) (Circle.exp t) = t := by
    have hinterval : ∀ᶠ t in nhds t₀,
        t - t₀ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      have hpi : 0 < Real.pi / 2 := by positivity
      have hIcc : Icc (-(Real.pi / 2)) (Real.pi / 2) ∈ nhds (0 : ℝ) :=
        Icc_mem_nhds (by linarith) (by linarith)
      have hcont : ContinuousAt (fun t : ℝ => t - t₀) t₀ :=
        continuousAt_id.sub continuousAt_const
      have hIcc' : Icc (-(Real.pi / 2)) (Real.pi / 2) ∈
          nhds (t₀ - t₀) := by
        simpa only [sub_self] using hIcc
      have hpre := hcont.preimage_mem_nhds hIcc'
      change {t : ℝ | t - t₀ ∈
        Icc (-(Real.pi / 2)) (Real.pi / 2)} ∈ nhds t₀
      exact hpre
    filter_upwards [hinterval] with t ht
    rw [circleLocalAngle, circleLocalSine_exp,
      Real.arcsin_sin ht.1 ht.2]
    ring
  have himage : Circle.exp '' {t | t₀ +
      circleLocalAngle (Circle.exp t₀) (Circle.exp t) = t} ∈
      nhds (Circle.exp t₀) := by
    rw [← (isLocalHomeomorph_circleExp.map_nhds_eq t₀),
      Filter.mem_map]
    exact Filter.mem_of_superset hphase
      (fun t ht => ⟨t, ht, rfl⟩)
  filter_upwards [himage] with z hz
  rcases hz with ⟨t, ht, rfl⟩
  simp only [id_eq]
  rw [ht]

/--
%%handwave
name:
  Exponential coordinates on an additive circle
statement:
  For \(P\ne0\) and \(t\in\mathbb R\), the standard homeomorphism
  \(\mathbb R/P\mathbb Z\cong S^1\) sends the class of
  \(Pt/(2\pi)\) to \(e^{it}\).
proof:
  Substitute the class \(Pt/(2\pi)\) into the defining exponential of the
  homeomorphism and cancel the nonzero constants.
-/
theorem addCircle_homeomorphCircle_symm_exp
    (P : ℝ) (hP : P ≠ 0) (t : ℝ) :
    (AddCircle.homeomorphCircle hP).symm (Circle.exp t) =
      ((P / (2 * Real.pi) * t : ℝ) : AddCircle P) := by
  apply (AddCircle.homeomorphCircle hP).injective
  rw [(AddCircle.homeomorphCircle hP).apply_symm_apply]
  rw [AddCircle.homeomorphCircle_apply,
    AddCircle.toCircle_apply_mk]
  congr 1
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp

/-- The derivative, in a centered product chart, of the oriented tangent
field.  We use the within-derivative because the partial coordinate is only
specified to be smooth on its source. -/
noncomputable def smoothFrontierProductCoordinateVelocity
    (D : SmoothBoundaryDomain X) (q : frontier D.carrier) (x : X) :
    ℝ × ℝ :=
  (tangentMapWithin SurfaceRealModel 𝓘(ℝ, ℝ × ℝ)
    (smoothBoundaryProductChartAt D q).coordinate
    (smoothBoundaryProductChartAt D q).coordinate.source
    (⟨x, smoothFrontierTangentVectorField D x⟩ :
      TangentBundle SurfaceRealModel X)).2

/--
%%handwave
name:
  Continuity of the boundary-flow velocity in product coordinates
statement:
  At a frontier point \(q\), express the oriented tangent vector field in a
  centered boundary product chart.  Its coordinate velocity is continuous
  at \(q\).
proof:
  The tangent-vector section is continuous, and the tangent map of the
  smooth product chart is continuous on its source.  Compose these maps and
  project to the vector component.
-/
theorem smoothFrontierProductCoordinateVelocity_continuousAt
    (D : SmoothBoundaryDomain X) (q : frontier D.carrier) :
    ContinuousAt (smoothFrontierProductCoordinateVelocity D q) (q : X) := by
  let C := smoothBoundaryProductChartAt D q
  let tangentSection : X → TangentBundle SurfaceRealModel X := fun x =>
    ⟨x, smoothFrontierTangentVectorField D x⟩
  have hsection : Continuous tangentSection :=
    (smoothFrontierTangentVectorField_contMDiff D).continuous
  have htangent : ContinuousOn
      (tangentMapWithin SurfaceRealModel 𝓘(ℝ, ℝ × ℝ)
        C.coordinate C.coordinate.source)
      (π ℂ (TangentSpace SurfaceRealModel) ⁻¹' C.coordinate.source) :=
    C.coordinate.contMDiffOn_toFun.continuousOn_tangentMapWithin
      (by simp) C.coordinate.open_source.uniqueMDiffOn
  have hsection_mem : tangentSection (q : X) ∈
      π ℂ (TangentSpace SurfaceRealModel) ⁻¹' C.coordinate.source := by
    exact C.point_mem
  have hopen : IsOpen
      (π ℂ (TangentSpace SurfaceRealModel) ⁻¹' C.coordinate.source) :=
    C.coordinate.open_source.preimage
      (FiberBundle.continuous_proj ℂ (TangentSpace SurfaceRealModel))
  have hmap : ContinuousAt
      (tangentMapWithin SurfaceRealModel 𝓘(ℝ, ℝ × ℝ)
        C.coordinate C.coordinate.source) (tangentSection (q : X)) :=
    (htangent (tangentSection (q : X)) hsection_mem).continuousAt
      (hopen.mem_nhds hsection_mem)
  have hcomp := hmap.comp hsection.continuousAt
  have hsnd : Continuous
      (fun p : TangentBundle 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) => p.2) :=
    (contMDiff_snd_tangentBundle_modelSpace (n := 0) (ℝ × ℝ)
      𝓘(ℝ, ℝ × ℝ)).continuous
  simpa [smoothFrontierProductCoordinateVelocity, C, tangentSection,
    Function.comp_def] using hsnd.continuousAt.comp hcomp

/--
%%handwave
name:
  Derivative of a frontier trajectory in product coordinates
statement:
  Let \(\gamma\) be an integral curve of the oriented frontier tangent field
  with \(\gamma(t_0)=q\).  For all \(t\) sufficiently near \(t_0\),
  \[
    \frac{d}{ds}\bigg|_{s=t} C(\gamma(s))
      = dC_{\gamma(t)}\bigl(V(\gamma(t))\bigr),
  \]
  where \(C\) is the centered product chart and \(V\) is the tangent field.
proof:
  Near \(t_0\) the trajectory lies in the chart source.  Apply the chain
  rule to \(C\circ\gamma\), use the integral-curve equation
  \(\gamma'=V\circ\gamma\), and identify the derivative with the coordinate
  velocity.
-/
theorem smoothFrontierProductCoordinate_eventually_hasDerivAt
    (D : SmoothBoundaryDomain X) (q : frontier D.carrier)
    {gamma : ℝ → X} {t₀ : ℝ}
    (hgamma0 : gamma t₀ = q)
    (hgamma : IsMIntegralCurve gamma
      (smoothFrontierTangentVectorField D)) :
    ∀ᶠ t in nhds t₀,
      HasDerivAt
        (fun s : ℝ =>
          (smoothBoundaryProductChartAt D q).coordinate (gamma s))
        (smoothFrontierProductCoordinateVelocity D q (gamma t)) t := by
  let C := smoothBoundaryProductChartAt D q
  have hsource : ∀ᶠ t in nhds t₀, gamma t ∈ C.coordinate.source := by
    apply hgamma.continuous.continuousAt.preimage_mem_nhds
    rw [hgamma0]
    exact C.coordinate.open_source.mem_nhds C.point_mem
  filter_upwards [hsource] with t ht
  have hcoordWithin :
      ContMDiffWithinAt SurfaceRealModel 𝓘(ℝ, ℝ × ℝ) ∞
        C.coordinate C.coordinate.source (gamma t) :=
    C.coordinate.contMDiffOn_toFun (gamma t) ht
  have hcoordAt :
      MDifferentiableAt SurfaceRealModel 𝓘(ℝ, ℝ × ℝ)
        C.coordinate (gamma t) :=
    (hcoordWithin.mdifferentiableWithinAt (by simp)).mdifferentiableAt
      (C.coordinate.open_source.mem_nhds ht)
  have hcomp := hcoordAt.hasMFDerivAt.comp t
    (hgamma.isMIntegralCurveAt t).hasMFDerivAt
  let w : ℝ × ℝ :=
    mfderiv SurfaceRealModel 𝓘(ℝ, ℝ × ℝ)
      C.coordinate (gamma t)
        (smoothFrontierTangentVectorField D (gamma t))
  have hordinary : HasDerivAt (fun s : ℝ => C.coordinate (gamma s)) w t := by
    rw [hasDerivAt_iff_hasFDerivAt]
    convert hcomp.hasFDerivAt using 1
    apply ContinuousLinearMap.ext
    intro a
    change a • w =
      mfderiv SurfaceRealModel 𝓘(ℝ, ℝ × ℝ)
        C.coordinate (gamma t)
          (a • smoothFrontierTangentVectorField D (gamma t))
    rw [map_smul]
    rfl
  have hvelocity :
      smoothFrontierProductCoordinateVelocity D q (gamma t) = w := by
    rw [smoothFrontierProductCoordinateVelocity, tangentMapWithin_snd,
      mfderivWithin_eq_mfderiv
        (C.coordinate.open_source.uniqueMDiffOn (gamma t) ht) hcoordAt]
  simpa [C, hvelocity] using hordinary

/--
%%handwave
name:
  Derivative of the angular product coordinate
statement:
  Under the hypotheses above, for \(t\) near \(t_0\) the angular component
  \(\theta(s)=C(\gamma(s))_2\) satisfies
  \[
    \theta'(t)=\bigl(dC_{\gamma(t)}V(\gamma(t))\bigr)_2.
  \]
proof:
  Project the product-coordinate derivative formula onto its second
  component.
-/
theorem smoothFrontierProductAngularCoordinate_eventually_hasDerivAt
    (D : SmoothBoundaryDomain X) (q : frontier D.carrier)
    {gamma : ℝ → X} {t₀ : ℝ}
    (hgamma0 : gamma t₀ = q)
    (hgamma : IsMIntegralCurve gamma
      (smoothFrontierTangentVectorField D)) :
    ∀ᶠ t in nhds t₀,
      HasDerivAt
        (fun s : ℝ =>
          ((smoothBoundaryProductChartAt D q).coordinate (gamma s)).2)
        (smoothFrontierProductCoordinateVelocity D q (gamma t)).2 t := by
  filter_upwards
    [smoothFrontierProductCoordinate_eventually_hasDerivAt
      D q hgamma0 hgamma] with t ht
  rw [hasDerivAt_iff_hasFDerivAt]
  convert ht.hasFDerivAt.snd using 1

/--
%%handwave
name:
  Complete tangent trajectories through frontier points
statement:
  For every \(p\in\partial D\), there is an integral curve
  \(\gamma:\mathbb R\to X\) of the oriented tangent field such that
  \(\gamma(0)=p\).
proof:
  The frontier is compact, so local integral curves through its points have
  a uniform positive existence time.  Tangency makes the frontier invariant;
  iterating the uniform local solutions gives a complete curve.
-/
theorem exists_smoothFrontierTangentIntegralCurve
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) :
    ∃ gamma : ℝ → X, gamma 0 = p ∧
      IsMIntegralCurve gamma (smoothFrontierTangentVectorField D) := by
  have hcompact : IsCompact (frontier D.carrier) :=
    D.compact_closure.of_isClosed_subset
      isClosed_frontier frontier_subset_closure
  rcases exists_surfaceIntegralCurvesOn_uniform_time_of_isCompact
      (smoothFrontierTangentVectorField D)
      (smoothFrontierTangentVectorField_contMDiff D)
      hcompact ⟨(p : X), p.2⟩ with
    ⟨ε, hε, hlocal⟩
  apply exists_isMIntegralCurve_of_isMIntegralCurveOn_invariant
    (smoothFrontierTangentVectorField D)
    ((smoothFrontierTangentVectorField_contMDiff D).of_le (by norm_num))
    (K := frontier D.carrier)
    (fun hgamma ht₀ hfrontier =>
      tangentIntegralCurveOn_Ioo_mem_frontier D hgamma ht₀ hfrontier)
    hε hlocal p.2

/--
%%handwave
name:
  Vanishing of the transverse frontier velocity
statement:
  At the center \(q\in\partial D\) of a boundary product chart, the first,
  transverse component of the coordinate velocity of the oriented tangent
  field is zero.
proof:
  Take a complete integral curve through \(q\).  It remains on the frontier,
  where the transverse product coordinate is locally identically zero.
  Uniqueness of derivatives then forces its transverse velocity at \(q\) to
  vanish.
-/
theorem smoothFrontierProductCoordinateVelocity_fst_eq_zero
    (D : SmoothBoundaryDomain X) (q : frontier D.carrier) :
    (smoothFrontierProductCoordinateVelocity D q (q : X)).1 = 0 := by
  rcases exists_smoothFrontierTangentIntegralCurve D q with
    ⟨gamma, hgamma0, hgamma⟩
  let C := smoothBoundaryProductChartAt D q
  have hfrontier : ∀ t, gamma t ∈ frontier D.carrier := by
    intro t
    let a : ℝ := min 0 t - 1
    let b : ℝ := max 0 t + 1
    have hzero : (0 : ℝ) ∈ Ioo a b := by
      constructor
      · dsimp [a]
        linarith [min_le_left (0 : ℝ) t]
      · dsimp [b]
        linarith [le_max_left (0 : ℝ) t]
    have ht : t ∈ Ioo a b := by
      constructor
      · dsimp [a]
        linarith [min_le_right (0 : ℝ) t]
      · dsimp [b]
        linarith [le_max_right (0 : ℝ) t]
    exact tangentIntegralCurveOn_Ioo_mem_frontier D
      (hgamma.isMIntegralCurveOn (Ioo a b)) hzero
      (hgamma0.symm ▸ q.2) t ht
  have hsource : ∀ᶠ t in nhds (0 : ℝ), gamma t ∈ C.coordinate.source := by
    apply hgamma.continuous.continuousAt.preimage_mem_nhds
    rw [hgamma0]
    exact C.coordinate.open_source.mem_nhds C.point_mem
  have hfirst : (fun t : ℝ => (C.coordinate (gamma t)).1) =ᶠ[
      nhds (0 : ℝ)] fun _ => 0 := by
    filter_upwards [hsource] with t ht
    exact (C.frontier_iff_zero (gamma t) ht).mp (hfrontier t)
  have hpair :=
    (smoothFrontierProductCoordinate_eventually_hasDerivAt
      D q hgamma0 hgamma).self_of_nhds
  have hfst : HasDerivAt (fun t : ℝ => (C.coordinate (gamma t)).1)
      (smoothFrontierProductCoordinateVelocity D q (gamma 0)).1 0 := by
    rw [hasDerivAt_iff_hasFDerivAt]
    convert hpair.hasFDerivAt.fst using 1
  have hzero : HasDerivAt (fun t : ℝ => (C.coordinate (gamma t)).1)
      0 0 :=
    (hasDerivAt_const (x := (0 : ℝ)) (c := (0 : ℝ)))
      |>.congr_of_eventuallyEq hfirst
  rw [hgamma0] at hfst
  exact hfst.unique hzero

/--
%%handwave
name:
  Nonvanishing of the frontier velocity in product coordinates
statement:
  At every frontier point \(q\), the full coordinate velocity of the
  oriented tangent field in a centered boundary product chart is nonzero.
proof:
  The differential of a local diffeomorphism is injective.  If the
  coordinate velocity vanished, injectivity would make the original tangent
  vector vanish, contradicting nonvanishing of the oriented frontier field.
-/
theorem smoothFrontierProductCoordinateVelocity_ne_zero
    (D : SmoothBoundaryDomain X) (q : frontier D.carrier) :
    smoothFrontierProductCoordinateVelocity D q (q : X) ≠ 0 := by
  let C := smoothBoundaryProductChartAt D q
  have hcoordWithin :
      ContMDiffWithinAt SurfaceRealModel 𝓘(ℝ, ℝ × ℝ) ∞
        C.coordinate C.coordinate.source (q : X) :=
    C.coordinate.contMDiffOn_toFun (q : X) C.point_mem
  have hcoordAt :
      MDifferentiableAt SurfaceRealModel 𝓘(ℝ, ℝ × ℝ)
        C.coordinate (q : X) :=
    (hcoordWithin.mdifferentiableWithinAt (by simp)).mdifferentiableAt
      (C.coordinate.open_source.mem_nhds C.point_mem)
  have hvelocity :
      smoothFrontierProductCoordinateVelocity D q (q : X) =
        mfderiv SurfaceRealModel 𝓘(ℝ, ℝ × ℝ)
          C.coordinate (q : X)
            (smoothFrontierTangentVectorField D (q : X)) := by
    rw [smoothFrontierProductCoordinateVelocity, tangentMapWithin_snd,
      mfderivWithin_eq_mfderiv
        (C.coordinate.open_source.uniqueMDiffOn (q : X) C.point_mem)
        hcoordAt]
  have hlocal :
      IsLocalDiffeomorphAt SurfaceRealModel 𝓘(ℝ, ℝ × ℝ) ∞
        C.coordinate (q : X) :=
    PartialDiffeomorph.isLocalDiffeomorphAt
      SurfaceRealModel 𝓘(ℝ, ℝ × ℝ) ∞ C.coordinate C.point_mem
  have hinjective :
      Function.Injective
        (mfderiv SurfaceRealModel 𝓘(ℝ, ℝ × ℝ)
          C.coordinate (q : X)) :=
    (hlocal.mfderivToContinuousLinearEquiv (by simp)).injective
  intro hzero
  have hTzero : smoothFrontierTangentVectorField D (q : X) = 0 := by
    apply hinjective
    rw [map_zero, ← hvelocity, hzero]
    rfl
  exact smoothFrontierTangentVectorField_ne_zero D q.2 hTzero

/--
%%handwave
name:
  Nonvanishing of the angular frontier velocity
statement:
  At the center of a boundary product chart, the angular component of the
  oriented tangent-field velocity is nonzero.
proof:
  The transverse component is zero, while the full coordinate velocity is
  nonzero; therefore its angular component cannot vanish.
-/
theorem smoothFrontierProductCoordinateVelocity_snd_ne_zero
    (D : SmoothBoundaryDomain X) (q : frontier D.carrier) :
    (smoothFrontierProductCoordinateVelocity D q (q : X)).2 ≠ 0 := by
  intro hsecond
  apply smoothFrontierProductCoordinateVelocity_ne_zero D q
  apply Prod.ext
  · exact smoothFrontierProductCoordinateVelocity_fst_eq_zero D q
  · exact hsecond

/--
%%handwave
name:
  Strict derivative of the angular coordinate along the frontier flow
statement:
  If \(\gamma(t_0)=q\) is an integral curve of the oriented frontier field,
  then the angular product coordinate \(\theta(t)=C(\gamma(t))_2\) has a
  strict derivative at \(t_0\), equal to the nonzero angular coordinate
  velocity at \(q\).
proof:
  Near \(t_0\), the ordinary derivative of \(\theta\) is the angular velocity.
  That velocity varies continuously along \(\gamma\), so the derivative is
  strict and evaluates at \(q\).
-/
theorem smoothFrontierProductAngularCoordinate_hasStrictDerivAt
    (D : SmoothBoundaryDomain X) (q : frontier D.carrier)
    {gamma : ℝ → X} {t₀ : ℝ}
    (hgamma0 : gamma t₀ = q)
    (hgamma : IsMIntegralCurve gamma
      (smoothFrontierTangentVectorField D)) :
    HasStrictDerivAt
      (fun s : ℝ =>
        ((smoothBoundaryProductChartAt D q).coordinate (gamma s)).2)
      (smoothFrontierProductCoordinateVelocity D q (q : X)).2 t₀ := by
  have hder :=
    smoothFrontierProductAngularCoordinate_eventually_hasDerivAt
      D q hgamma0 hgamma
  have hvelocityAt : ContinuousAt
      (smoothFrontierProductCoordinateVelocity D q) (gamma t₀) := by
    simpa only [hgamma0] using
      smoothFrontierProductCoordinateVelocity_continuousAt D q
  have hvelocityCurve : ContinuousAt
      (fun t : ℝ => smoothFrontierProductCoordinateVelocity D q (gamma t))
      t₀ :=
    hvelocityAt.comp hgamma.continuous.continuousAt
  have hang : ContinuousAt
      (fun t : ℝ =>
        (smoothFrontierProductCoordinateVelocity D q (gamma t)).2) t₀ :=
    hvelocityCurve.snd
  have hstrict :=
    hasStrictDerivAt_of_hasDerivAt_of_continuousAt hder hang
  simpa only [hgamma0] using hstrict

/--
%%handwave
name:
  Complete tangent trajectories remain on the frontier
statement:
  If a complete integral curve \(\gamma:\mathbb R\to X\) of the oriented
  frontier field starts on \(\partial D\), then
  \(\gamma(t)\in\partial D\) for every \(t\in\mathbb R\).
proof:
  For a fixed \(t\), restrict the complete curve to a bounded open interval
  containing both \(0\) and \(t\).  Invariance of the frontier for local
  tangent integral curves gives the conclusion at \(t\).
-/
theorem smoothFrontierTangentIntegralCurve_mem_frontier
    (D : SmoothBoundaryDomain X) {gamma : ℝ → X}
    (hgamma : IsMIntegralCurve gamma
      (smoothFrontierTangentVectorField D))
    (hgamma0 : gamma 0 ∈ frontier D.carrier) :
    ∀ t, gamma t ∈ frontier D.carrier := by
  intro t
  let a : ℝ := min 0 t - 1
  let b : ℝ := max 0 t + 1
  have hzero : (0 : ℝ) ∈ Ioo a b := by
    constructor
    · dsimp [a]
      linarith [min_le_left (0 : ℝ) t]
    · dsimp [b]
      linarith [le_max_left (0 : ℝ) t]
  have ht : t ∈ Ioo a b := by
    constructor
    · dsimp [a]
      linarith [min_le_right (0 : ℝ) t]
    · dsimp [b]
      linarith [le_max_right (0 : ℝ) t]
  exact tangentIntegralCurveOn_Ioo_mem_frontier D
    (hgamma.isMIntegralCurveOn (Ioo a b)) hzero hgamma0 t ht

/--
%%handwave
name:
  Smoothness of a tangent trajectory in the frontier manifold
statement:
  A complete integral curve of the oriented frontier field that remains in
  \(\partial D\) is smooth as a map
  \(\mathbb R\to\partial D\), where the frontier carries its natural smooth
  one-manifold structure.
proof:
  The ambient integral curve is smooth.  In a frontier chart, its coordinate
  is the angular component of a boundary product chart, hence is smooth by
  composition with the ambient curve.
-/
theorem smoothFrontierTangentIntegralCurve_contMDiff_frontier
    (D : SmoothBoundaryDomain X) {gamma : ℝ → X}
    (hgamma : IsMIntegralCurve gamma
      (smoothFrontierTangentVectorField D))
    (hfrontier : ∀ t, gamma t ∈ frontier D.carrier) :
    letI := smoothBoundaryFrontierChartedSpace D
    ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun t => (⟨gamma t, hfrontier t⟩ : frontier D.carrier)) := by
  letI := smoothBoundaryFrontierChartedSpace D
  letI : IsManifold (modelWithCornersSelf ℝ ℝ) ∞
      (frontier D.carrier) :=
    smoothBoundaryDomain_frontier_isSmoothOneManifold D
  let gammaF : ℝ → frontier D.carrier := fun t =>
    ⟨gamma t, hfrontier t⟩
  have hgammaSmooth : ContMDiff (modelWithCornersSelf ℝ ℝ)
      SurfaceRealModel ∞ gamma :=
    IsMIntegralCurve.contMDiff_of_surfaceVectorField
      (smoothFrontierTangentVectorField D)
      (smoothFrontierTangentVectorField_contMDiff D) hgamma
  intro t₀
  let q : frontier D.carrier := gammaF t₀
  have hqsource : gammaF t₀ ∈
      (chartAt ℝ q).source := by
    change q ∈ (smoothBoundaryFrontierChart D q).source
    exact smoothBoundaryFrontierChart_point_mem D q
  rw [contMDiffAt_iff_target_of_mem_source hqsource]
  constructor
  · exact Continuous.subtype_mk hgamma.continuous hfrontier |>.continuousAt
  · let C := smoothBoundaryProductChartAt D q
    have hcoordAt : ContMDiffAt SurfaceRealModel
        (modelWithCornersSelf ℝ (ℝ × ℝ)) ∞ C.coordinate (gamma t₀) := by
      have hmem : gamma t₀ ∈ C.coordinate.source := by
        exact C.point_mem
      exact (C.coordinate.contMDiffOn_toFun (gamma t₀) hmem).contMDiffAt
        (C.coordinate.open_source.mem_nhds hmem)
    have hang : ContMDiffAt (modelWithCornersSelf ℝ ℝ)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun t : ℝ => (C.coordinate (gamma t)).2) t₀ := by
      have hcomp := hcoordAt.comp t₀ (hgammaSmooth t₀)
      exact hcomp.contDiffAt.snd.contMDiffAt
    have heq :
        (extChartAt (modelWithCornersSelf ℝ ℝ) q ∘ gammaF) =
          (fun t : ℝ => (C.coordinate (gamma t)).2) := by
      funext t
      change smoothBoundaryFrontierChart D q (gammaF t) = _
      simp only [smoothBoundaryFrontierChart_apply, gammaF, C]
    rw [heq]
    exact hang

/--
%%handwave
name:
  A tangent trajectory stays in its frontier component
statement:
  If an integral curve \(\gamma\) of the oriented frontier field satisfies
  \(\gamma(0)=p\in\partial D\), then
  \[
    \gamma(t)\in\operatorname{Comp}_{\partial D}(p)
    \qquad(t\in\mathbb R).
  \]
proof:
  The image of the connected line under the continuous curve is connected,
  lies in the frontier, and contains \(p\); it is therefore contained in the
  connected component of \(p\).
-/
theorem smoothFrontierTangentIntegralCurve_mem_connectedComponentIn
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier)
    {gamma : ℝ → X} (hgamma0 : gamma 0 = p)
    (hgamma : IsMIntegralCurve gamma
      (smoothFrontierTangentVectorField D)) :
    ∀ t, gamma t ∈
      connectedComponentIn (frontier D.carrier) (p : X) := by
  have hfrontier : range gamma ⊆ frontier D.carrier := by
    rw [range_subset_iff]
    exact smoothFrontierTangentIntegralCurve_mem_frontier D hgamma
      (hgamma0.symm ▸ p.2)
  have hp_range : (p : X) ∈ range gamma := ⟨0, hgamma0⟩
  have hrange : range gamma ⊆
      connectedComponentIn (frontier D.carrier) (p : X) :=
    (isPreconnected_range hgamma.continuous)
      |>.subset_connectedComponentIn hp_range hfrontier
  exact fun t => hrange (mem_range_self t)

/--
%%handwave
name:
  Tangent trajectories are open maps onto the frontier
statement:
  A complete integral curve of the nonvanishing oriented frontier field,
  regarded as a map \(\mathbb R\to\partial D\), is an open map.
proof:
  At every time, the angular boundary coordinate has nonzero strict
  derivative, so it maps a neighborhood of that time onto a neighborhood of
  the corresponding angular coordinate.  The boundary product chart then
  transfers this neighborhood back to the frontier.
-/
theorem smoothFrontierTangentIntegralCurve_isOpenMap
    (D : SmoothBoundaryDomain X) {gamma : ℝ → X}
    (hgamma : IsMIntegralCurve gamma
      (smoothFrontierTangentVectorField D))
    (hfrontier : ∀ t, gamma t ∈ frontier D.carrier) :
    IsOpenMap (fun t : ℝ =>
      (⟨gamma t, hfrontier t⟩ : frontier D.carrier)) := by
  intro G hGopen
  rw [isOpen_iff_mem_nhds]
  intro q hq
  rcases hq with ⟨t₀, ht₀G, hq⟩
  have hgamma0 : gamma t₀ = (q : X) := by
    exact congrArg Subtype.val hq
  let C := smoothBoundaryProductChartAt D q
  let e := smoothBoundaryFrontierChart D q
  let theta : ℝ → ℝ := fun t => (C.coordinate (gamma t)).2
  have hstrict : HasStrictDerivAt theta
      (smoothFrontierProductCoordinateVelocity D q (q : X)).2 t₀ := by
    simpa [theta, C] using
      smoothFrontierProductAngularCoordinate_hasStrictDerivAt
        D q hgamma0 hgamma
  have hangular_ne :
      (smoothFrontierProductCoordinateVelocity D q (q : X)).2 ≠ 0 :=
    smoothFrontierProductCoordinateVelocity_snd_ne_zero D q
  have htheta0 : theta t₀ = 0 := by
    simp only [theta, hgamma0]
    exact congrArg Prod.snd C.point_coord
  have hmap : Filter.map theta (nhds t₀) = nhds (0 : ℝ) := by
    simpa only [htheta0] using hstrict.map_nhds_eq hangular_ne
  let A : Set ℝ :=
    G ∩ gamma ⁻¹' smoothBoundaryProductBallSource D q
  have hA : A ∈ nhds t₀ := by
    apply Filter.inter_mem (hGopen.mem_nhds ht₀G)
    apply hgamma.continuous.continuousAt.preimage_mem_nhds
    rw [hgamma0]
    exact (smoothBoundaryProductBallSource_isOpen D q).mem_nhds
      (smoothBoundaryProductBallSource_point_mem D q)
  have himage : theta '' A ∈ nhds (0 : ℝ) := by
    rw [← hmap, Filter.mem_map]
    exact Filter.mem_of_superset hA (fun t ht => ⟨t, ht, rfl⟩)
  have htarget0 : (0 : ℝ) ∈ e.target := by
    simpa [e, smoothBoundaryFrontierChart_target] using
      Metric.mem_ball_self (x := (0 : ℝ))
        (smoothBoundaryProductChartRadius_pos D q)
  rcases mem_nhds_iff.mp
      (Filter.inter_mem himage (e.open_target.mem_nhds htarget0)) with
    ⟨B, hBsub, hBopen, hB0⟩
  let S : Set (frontier D.carrier) := e.source ∩ e ⁻¹' B
  have hSopen : IsOpen S := e.isOpen_inter_preimage hBopen
  have heq0 : e q = 0 := by
    simpa [e, C] using congrArg Prod.snd C.point_coord
  have hqS : q ∈ S := by
    refine ⟨smoothBoundaryFrontierChart_point_mem D q, ?_⟩
    show e q ∈ B
    rw [heq0]
    exact hB0
  have hSsubset : S ⊆
      (fun t : ℝ =>
        (⟨gamma t, hfrontier t⟩ : frontier D.carrier)) '' G := by
    intro x hx
    have hxB : e x ∈ theta '' A := (hBsub hx.2).1
    rcases hxB with ⟨s, hsA, hs⟩
    have hxBall : (x : X) ∈ smoothBoundaryProductBallSource D q := by
      simpa [e] using hx.1
    have hcoordEq : C.coordinate (x : X) = C.coordinate (gamma s) := by
      apply Prod.ext
      · rw [(C.frontier_iff_zero (x : X) hxBall.1).mp x.2,
          (C.frontier_iff_zero (gamma s) hsA.2.1).mp (hfrontier s)]
      · have hs' : (C.coordinate (gamma s)).2 =
            (C.coordinate (x : X)).2 := by
          simpa [theta, e, C] using hs
        exact hs'.symm
    have hxEq : (x : X) = gamma s :=
      C.coordinate.injOn hxBall.1 hsA.2.1 hcoordEq
    refine ⟨s, hsA.1, ?_⟩
    exact Subtype.ext hxEq.symm
  exact Filter.mem_of_superset (hSopen.mem_nhds hqS) hSsubset

/--
%%handwave
name:
  Openness of a complete tangent orbit in the frontier
statement:
  The image of a complete integral curve of the nonvanishing oriented
  frontier field is open relative to \(\partial D\).
proof:
  At each point of the orbit, the angular coordinate along the trajectory
  has nonzero strict derivative and hence covers an interval.  Injectivity of
  the local product chart shows that the corresponding frontier neighborhood
  lies in the orbit.
-/
theorem smoothFrontierTangentIntegralCurve_range_isOpen
    (D : SmoothBoundaryDomain X) {gamma : ℝ → X}
    (hgamma : IsMIntegralCurve gamma
      (smoothFrontierTangentVectorField D))
    (hfrontier : ∀ t, gamma t ∈ frontier D.carrier) :
    IsOpen ((fun x : frontier D.carrier => (x : X)) ⁻¹' range gamma) := by
  rw [isOpen_iff_mem_nhds]
  intro q hq
  rcases hq with ⟨t₀, hgamma0'⟩
  have hgamma0 : gamma t₀ = (q : X) := hgamma0'
  let C := smoothBoundaryProductChartAt D q
  let e := smoothBoundaryFrontierChart D q
  let theta : ℝ → ℝ := fun t => (C.coordinate (gamma t)).2
  have hstrict : HasStrictDerivAt theta
      (smoothFrontierProductCoordinateVelocity D q (q : X)).2 t₀ := by
    simpa [theta, C] using
      smoothFrontierProductAngularCoordinate_hasStrictDerivAt
        D q hgamma0 hgamma
  have hangular_ne :
      (smoothFrontierProductCoordinateVelocity D q (q : X)).2 ≠ 0 :=
    smoothFrontierProductCoordinateVelocity_snd_ne_zero D q
  have htheta0 : theta t₀ = 0 := by
    simp only [theta, hgamma0]
    exact congrArg Prod.snd C.point_coord
  have hmap : Filter.map theta (nhds t₀) = nhds (0 : ℝ) := by
    simpa only [htheta0] using hstrict.map_nhds_eq hangular_ne
  let A : Set ℝ := gamma ⁻¹' smoothBoundaryProductBallSource D q
  have hA : A ∈ nhds t₀ := by
    apply hgamma.continuous.continuousAt.preimage_mem_nhds
    rw [hgamma0]
    exact (smoothBoundaryProductBallSource_isOpen D q).mem_nhds
      (smoothBoundaryProductBallSource_point_mem D q)
  have himage : theta '' A ∈ nhds (0 : ℝ) := by
    rw [← hmap, Filter.mem_map]
    exact Filter.mem_of_superset hA (fun t ht => ⟨t, ht, rfl⟩)
  have htarget0 : (0 : ℝ) ∈ e.target := by
    simpa [e, smoothBoundaryFrontierChart_target] using
      Metric.mem_ball_self (x := (0 : ℝ))
        (smoothBoundaryProductChartRadius_pos D q)
  rcases mem_nhds_iff.mp
      (Filter.inter_mem himage (e.open_target.mem_nhds htarget0)) with
    ⟨B, hBsub, hBopen, hB0⟩
  let S : Set (frontier D.carrier) := e.source ∩ e ⁻¹' B
  have hSopen : IsOpen S := by
    exact e.isOpen_inter_preimage hBopen
  have heq0 : e q = 0 := by
    simpa [e, C] using congrArg Prod.snd C.point_coord
  have hqS : q ∈ S := by
    refine ⟨smoothBoundaryFrontierChart_point_mem D q, ?_⟩
    show e q ∈ B
    rw [heq0]
    exact hB0
  have hSsubset : S ⊆
      (fun x : frontier D.carrier => (x : X)) ⁻¹' range gamma := by
    intro x hx
    have hxB : e x ∈ theta '' A := (hBsub hx.2).1
    rcases hxB with ⟨s, hsA, hs⟩
    have hxBall : (x : X) ∈ smoothBoundaryProductBallSource D q := by
      simpa [e] using hx.1
    have hcoordEq : C.coordinate (x : X) = C.coordinate (gamma s) := by
      apply Prod.ext
      · rw [(C.frontier_iff_zero (x : X) hxBall.1).mp x.2,
          (C.frontier_iff_zero (gamma s) hsA.1).mp (hfrontier s)]
      · have hs' : (C.coordinate (gamma s)).2 =
            (C.coordinate (x : X)).2 := by
          simpa [theta, e, C] using hs
        exact hs'.symm
    have hxEq : (x : X) = gamma s :=
      C.coordinate.injOn hxBall.1 hsA.1 hcoordEq
    exact ⟨s, hxEq.symm⟩
  exact Filter.mem_of_superset (hSopen.mem_nhds hqS) hSsubset

/--
%%handwave
name:
  Complete tangent orbits are clopen in the frontier
statement:
  The image of a complete integral curve of the oriented frontier field is
  both open and closed relative to \(\partial D\).
proof:
  The orbit is open.  Through any point outside it, take another complete
  orbit, which is open as well.  If the two orbits met, uniqueness of integral
  curves after translating time would make the second point lie on the first
  orbit.  Thus these exterior orbits form an open complement.
-/
theorem smoothFrontierTangentIntegralCurve_range_isClopen
    (D : SmoothBoundaryDomain X) {gamma : ℝ → X}
    (hgamma : IsMIntegralCurve gamma
      (smoothFrontierTangentVectorField D))
    (hfrontier : ∀ t, gamma t ∈ frontier D.carrier) :
    IsClopen ((fun x : frontier D.carrier => (x : X)) ⁻¹' range gamma) := by
  let O : Set (frontier D.carrier) :=
    (fun x : frontier D.carrier => (x : X)) ⁻¹' range gamma
  have hOopen : IsOpen O :=
    smoothFrontierTangentIntegralCurve_range_isOpen D hgamma hfrontier
  have hOcompl_open : IsOpen Oᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro q hq
    have hq_not : (q : X) ∉ range gamma := hq
    rcases exists_smoothFrontierTangentIntegralCurve D q with
      ⟨eta, heta0, heta⟩
    have heta_frontier : ∀ t, eta t ∈ frontier D.carrier :=
      smoothFrontierTangentIntegralCurve_mem_frontier D heta
        (heta0.symm ▸ q.2)
    let Oeta : Set (frontier D.carrier) :=
      (fun x : frontier D.carrier => (x : X)) ⁻¹' range eta
    have hOeta_open : IsOpen Oeta :=
      smoothFrontierTangentIntegralCurve_range_isOpen D heta heta_frontier
    have hqOeta : q ∈ Oeta := ⟨0, heta0⟩
    have hOeta_subset : Oeta ⊆ Oᶜ := by
      intro x hxeta hxgamma
      rcases hxeta with ⟨b, hb⟩
      rcases hxgamma with ⟨a, ha⟩
      have hab : gamma a = eta b := ha.trans hb.symm
      have hshift : (fun t : ℝ => gamma (t + a)) =
          (fun t : ℝ => eta (t + b)) := by
        apply isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless
          (t₀ := (0 : ℝ))
          ((smoothFrontierTangentVectorField_contMDiff D).of_le
            (by norm_num))
          (hgamma.comp_add a) (heta.comp_add b)
        simpa using hab
      have heval := congrFun hshift (-b)
      have hq_range : (q : X) ∈ range gamma := by
        refine ⟨-b + a, ?_⟩
        simpa [heta0] using heval
      exact hq_not hq_range
    exact Filter.mem_of_superset
      (hOeta_open.mem_nhds hqOeta) hOeta_subset
  exact ⟨(isOpen_compl_iff.mp hOcompl_open), hOopen⟩

/--
%%handwave
name:
  A complete tangent orbit is the whole frontier component
statement:
  If \(\gamma(0)=p\in\partial D\), then the range of the complete oriented
  tangent trajectory is exactly
  \(\operatorname{Comp}_{\partial D}(p)\).
proof:
  The range lies in the component.  As a subset of the frontier it is clopen
  and contains \(p\), so connectedness of the component forces the reverse
  inclusion.
-/
theorem smoothFrontierTangentIntegralCurve_range_eq_frontierComponent
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier)
    {gamma : ℝ → X} (hgamma0 : gamma 0 = p)
    (hgamma : IsMIntegralCurve gamma
      (smoothFrontierTangentVectorField D)) :
    range gamma = connectedComponentIn (frontier D.carrier) (p : X) := by
  have hfrontier : ∀ t, gamma t ∈ frontier D.carrier :=
    smoothFrontierTangentIntegralCurve_mem_frontier D hgamma
      (hgamma0.symm ▸ p.2)
  let O : Set (frontier D.carrier) :=
    (fun x : frontier D.carrier => (x : X)) ⁻¹' range gamma
  have hOclopen : IsClopen O :=
    smoothFrontierTangentIntegralCurve_range_isClopen D hgamma hfrontier
  have hpO : p ∈ O := ⟨0, hgamma0⟩
  have hcomponent_subset_O : connectedComponent p ⊆ O :=
    isPreconnected_connectedComponent.subset_isClopen hOclopen
      ⟨p, mem_connectedComponent, hpO⟩
  apply Set.Subset.antisymm
  · rintro x ⟨t, rfl⟩
    exact smoothFrontierTangentIntegralCurve_mem_connectedComponentIn
      D p hgamma0 hgamma t
  · rw [connectedComponentIn_eq_image p.2]
    rintro x ⟨q, hq, rfl⟩
    exact hcomponent_subset_O hq

/--
%%handwave
name:
  A complete frontier trajectory is not injective
statement:
  A complete oriented tangent trajectory through a point of the compact
  smooth frontier cannot be injective as a map \(\mathbb R\to X\).
proof:
  Its range is the compact connected frontier component, and the trajectory
  is continuous, open, and surjective onto that component.  If it were also
  injective it would be a homeomorphism from \(\mathbb R\) onto a compact
  space, contradicting noncompactness of the real line.
-/
theorem smoothFrontierTangentIntegralCurve_not_injective
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier)
    {gamma : ℝ → X} (hgamma0 : gamma 0 = p)
    (hgamma : IsMIntegralCurve gamma
      (smoothFrontierTangentVectorField D)) :
    ¬ Function.Injective gamma := by
  intro hgamma_injective
  let C : Set X := connectedComponentIn (frontier D.carrier) (p : X)
  have hmem : ∀ t, gamma t ∈ C :=
    smoothFrontierTangentIntegralCurve_mem_connectedComponentIn
      D p hgamma0 hgamma
  let gammaC : ℝ → C := fun t => ⟨gamma t, hmem t⟩
  have hgammaC_injective : Function.Injective gammaC := by
    intro a b hab
    apply hgamma_injective
    exact congrArg Subtype.val hab
  have hrange : range gamma = C := by
    simpa [C] using
      smoothFrontierTangentIntegralCurve_range_eq_frontierComponent
        D p hgamma0 hgamma
  have hgammaC_surjective : Function.Surjective gammaC := by
    intro x
    have hxrange : (x : X) ∈ range gamma := by
      rw [hrange]
      exact x.2
    rcases hxrange with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    exact Subtype.ext ht
  have hfrontier : ∀ t, gamma t ∈ frontier D.carrier :=
    smoothFrontierTangentIntegralCurve_mem_frontier D hgamma
      (hgamma0.symm ▸ p.2)
  let gammaF : ℝ → frontier D.carrier := fun t =>
    ⟨gamma t, hfrontier t⟩
  have hgammaF_open : IsOpenMap gammaF :=
    smoothFrontierTangentIntegralCurve_isOpenMap D hgamma hfrontier
  let toFrontier : C → frontier D.carrier := fun x =>
    ⟨(x : X), connectedComponentIn_subset
      (frontier D.carrier) (p : X) x.2⟩
  have htoFrontier : Continuous toFrontier :=
    Continuous.subtype_mk continuous_subtype_val
      (fun x => connectedComponentIn_subset
        (frontier D.carrier) (p : X) x.2)
  have hgammaC_open : IsOpenMap gammaC := by
    intro G hG
    have hopenF : IsOpen (gammaF '' G) := hgammaF_open G hG
    have hopenPre : IsOpen (toFrontier ⁻¹' (gammaF '' G)) :=
      hopenF.preimage htoFrontier
    have heq : gammaC '' G = toFrontier ⁻¹' (gammaF '' G) := by
      ext x
      constructor
      · rintro ⟨t, htG, htx⟩
        refine ⟨t, htG, ?_⟩
        have hval : gamma t = (x : X) :=
          congrArg (fun y : C => (y : X)) htx
        exact Subtype.ext hval
      · rintro ⟨t, htG, htx⟩
        refine ⟨t, htG, ?_⟩
        have hval : gamma t = (x : X) :=
          congrArg (fun y : frontier D.carrier => (y : X)) htx
        exact Subtype.ext hval
    rw [heq]
    exact hopenPre
  let equiv : ℝ ≃ C := Equiv.ofBijective gammaC
    ⟨hgammaC_injective, hgammaC_surjective⟩
  have hgammaC_continuous : Continuous gammaC :=
    Continuous.subtype_mk hgamma.continuous hmem
  let homeo : ℝ ≃ₜ C :=
    equiv.toHomeomorphOfContinuousOpen hgammaC_continuous hgammaC_open
  letI : CompactSpace C :=
    isCompact_iff_compactSpace.mp
      (smoothBoundaryDomain_frontier_connectedComponentIn_isCompact D p)
  have hcompactReal : CompactSpace ℝ := homeo.symm.compactSpace
  exact (not_compactSpace_iff.mpr inferInstance) hcompactReal

/--
%%handwave
name:
  Periodicity of the tangent flow on a frontier component
statement:
  For every \(p\in\partial D\), there are an integral curve
  \(\gamma:\mathbb R\to X\) and a period \(T>0\) such that
  \(\gamma(0)=p\) and \(\gamma(t+T)=\gamma(t)\) for every \(t\).
proof:
  A complete integral curve through \(p\) exists.  The uniqueness theorem
  gives the dichotomy that such a curve is periodic or injective; compactness
  of its frontier component excludes injectivity.
-/
theorem exists_periodic_smoothFrontierTangentIntegralCurve
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) :
    ∃ gamma : ℝ → X, ∃ T : ℝ,
      gamma 0 = p ∧ 0 < T ∧
        IsMIntegralCurve gamma (smoothFrontierTangentVectorField D) ∧
        Periodic gamma T := by
  rcases exists_smoothFrontierTangentIntegralCurve D p with
    ⟨gamma, hgamma0, hgamma⟩
  rcases hgamma.periodic_xor_injective
      ((smoothFrontierTangentVectorField_contMDiff D).of_le
        (by norm_num)) with
    hperiodic | hinjective
  · rcases hperiodic.1 with ⟨T, hT, hperiodic⟩
    exact ⟨gamma, T, hgamma0, hT, hgamma, hperiodic⟩
  · exact (smoothFrontierTangentIntegralCurve_not_injective
      D p hgamma0 hgamma hinjective.1).elim

/--
%%handwave
name:
  Existence of a fundamental period for the frontier flow
statement:
  For every \(p\in\partial D\), there are an integral curve \(\gamma\) through
  \(p\) and \(P>0\) such that \(P\) is a period of \(\gamma\) and
  \(P\le d\) for every positive period \(d\) of \(\gamma\).
proof:
  A nonzero angular derivative makes the curve locally injective near time
  zero, so there are no sufficiently small positive returns.  Starting from
  any positive period \(T\), minimize the return time on a compact interval
  bounded away from zero.  Uniqueness of integral curves turns the minimizing
  return into a period, and a smaller positive period would contradict its
  minimality or local injectivity.
-/
theorem exists_fundamentalPeriod_smoothFrontierTangentIntegralCurve
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) :
    ∃ gamma : ℝ → X, ∃ P : ℝ,
      gamma 0 = p ∧ 0 < P ∧
        IsMIntegralCurve gamma (smoothFrontierTangentVectorField D) ∧
        Periodic gamma P ∧
        ∀ d : ℝ, 0 < d → Periodic gamma d → P ≤ d := by
  rcases exists_periodic_smoothFrontierTangentIntegralCurve D p with
    ⟨gamma, T, hgamma0, hT, hgamma, hTperiodic⟩
  let theta : ℝ → ℝ := fun t =>
    ((smoothBoundaryProductChartAt D p).coordinate (gamma t)).2
  let c : ℝ :=
    (smoothFrontierProductCoordinateVelocity D p (p : X)).2
  have hstrict : HasStrictDerivAt theta c 0 := by
    simpa [theta, c] using
      smoothFrontierProductAngularCoordinate_hasStrictDerivAt
        D p hgamma0 hgamma
  have hc : c ≠ 0 := by
    simpa [c] using smoothFrontierProductCoordinateVelocity_snd_ne_zero D p
  have hleft := hstrict.eventually_left_inverse hc
  rcases Metric.mem_nhds_iff.mp hleft with ⟨δ, hδ, hδleft⟩
  have htheta_inj : Set.InjOn theta (Metric.ball (0 : ℝ) δ) := by
    intro a ha b hb hab
    calc
      a = hstrict.localInverse theta c 0 hc (theta a) :=
        (hδleft ha).symm
      _ = hstrict.localInverse theta c 0 hc (theta b) :=
        congrArg _ hab
      _ = b := hδleft hb
  let ε : ℝ := min δ (T / 2)
  have hε : 0 < ε := lt_min hδ (half_pos hT)
  have hεδ : ε ≤ δ := min_le_left δ (T / 2)
  have hεT : ε < T :=
    (min_le_right δ (T / 2)).trans_lt (half_lt_self hT)
  have hno_return : ∀ {t : ℝ}, t ∈ Ioo (-ε) ε →
      gamma t = gamma 0 → t = 0 := by
    intro t ht hreturn
    have htball : t ∈ Metric.ball (0 : ℝ) δ := by
      rw [Real.ball_zero_eq_Ioo]
      exact Ioo_subset_Ioo (neg_le_neg hεδ) hεδ ht
    have hzeroball : (0 : ℝ) ∈ Metric.ball (0 : ℝ) δ :=
      Metric.mem_ball_self hδ
    apply htheta_inj htball hzeroball
    exact congrArg
      (fun x : X =>
        ((smoothBoundaryProductChartAt D p).coordinate x).2) hreturn
  let S : Set ℝ := Icc ε T ∩ {t | gamma t = gamma 0}
  have hScompact : IsCompact S := by
    exact isCompact_Icc.inter_right
      (isClosed_eq hgamma.continuous continuous_const)
  have hTmem : T ∈ S := by
    refine ⟨⟨hεT.le, le_rfl⟩, ?_⟩
    exact hTperiodic.eq
  rcases hScompact.exists_isMinOn ⟨T, hTmem⟩ continuous_id.continuousOn with
    ⟨P, hPS, hPmin⟩
  have hPpos : 0 < P := hε.trans_le hPS.1.1
  have hPperiodic : Periodic gamma P := by
    have hreturn : gamma P = gamma 0 := hPS.2
    simpa using hgamma.periodic_of_eq
      ((smoothFrontierTangentVectorField_contMDiff D).of_le
        (by norm_num)) hreturn
  have hminimal : ∀ d : ℝ, 0 < d → Periodic gamma d → P ≤ d := by
    intro d hd hdperiodic
    by_cases hdT : d ≤ T
    · have hεd : ε ≤ d := by
        by_contra hnot
        have hdε : d < ε := lt_of_not_ge hnot
        have hdIoo : d ∈ Ioo (-ε) ε := ⟨by linarith, hdε⟩
        have hd0 : d = 0 := hno_return hdIoo hdperiodic.eq
        linarith
      exact hPmin ⟨⟨hεd, hdT⟩, hdperiodic.eq⟩
    · exact hPS.1.2.trans (le_of_not_ge hdT)
  exact ⟨gamma, P, hgamma0, hPpos, hgamma, hPperiodic, hminimal⟩

/--
%%handwave
name:
  Equal points differ by an integral multiple of the fundamental period
statement:
  Let \(\gamma\) be an integral curve with least positive period \(P\).  If
  \(\gamma(a)=\gamma(b)\), then \(a-b\in P\mathbb Z\).
proof:
  The return equality makes \(a-b\) a period.  Subtract an integral multiple
  of \(P\) to obtain a representative \(r\in[0,P\)).  This remainder is also
  a period; minimality of \(P\) forces \(r=0\).
-/
theorem sub_mem_zmultiples_of_eq_of_fundamentalPeriod
    (D : SmoothBoundaryDomain X) {gamma : ℝ → X} {P : ℝ}
    (hgamma : IsMIntegralCurve gamma
      (smoothFrontierTangentVectorField D))
    (hPpos : 0 < P) (hPperiodic : Periodic gamma P)
    (hminimal : ∀ d : ℝ, 0 < d → Periodic gamma d → P ≤ d)
    {a b : ℝ} (heq : gamma a = gamma b) :
    a - b ∈ AddSubgroup.zmultiples P := by
  have hdperiodic : Periodic gamma (a - b) :=
    hgamma.periodic_of_eq
      ((smoothFrontierTangentVectorField_contMDiff D).of_le
        (by norm_num)) heq
  rcases existsUnique_sub_zsmul_mem_Ico hPpos (a - b) 0 with
    ⟨k, hk, _hunique⟩
  simp only [zero_add] at hk
  let r : ℝ := (a - b) - k • P
  have hr : r ∈ Ico 0 P := by simpa [r] using hk
  have hrperiodic : Periodic gamma r := by
    exact hdperiodic.sub_period (hPperiodic.zsmul k)
  have hrle : r ≤ 0 := by
    by_contra hnot
    have hrpos : 0 < r := lt_of_not_ge hnot
    exact (not_le_of_gt hr.2) (hminimal r hrpos hrperiodic)
  have hrzero : r = 0 := le_antisymm hrle hr.1
  apply AddSubgroup.mem_zmultiples_iff.mpr
  refine ⟨k, ?_⟩
  dsimp [r] at hrzero
  linarith

/--
%%handwave
name:
  A frontier component is an additive circle
statement:
  For every \(p\in\partial D\), there is a number \(P>0\) and a homeomorphism
  \[
    \mathbb R/P\mathbb Z\ \cong\
    \operatorname{Comp}_{\partial D}(p).
  \]
proof:
  Lift a fundamental-period trajectory to the additive circle.  Equality of
  two lifted values implies that their parameters differ by an integral
  multiple of \(P\), giving injectivity, while the orbit-component theorem
  gives surjectivity.  Compactness of the additive circle upgrades the
  continuous bijection to a homeomorphism.
-/
theorem exists_homeomorph_addCircle_frontierComponent
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) :
    ∃ P : ℝ, 0 < P ∧
      Nonempty (AddCircle P ≃ₜ
        {x : X // x ∈
          connectedComponentIn (frontier D.carrier) (p : X)}) := by
  rcases exists_fundamentalPeriod_smoothFrontierTangentIntegralCurve D p with
    ⟨gamma, P, hgamma0, hPpos, hgamma, hPperiodic, hminimal⟩
  let C : Set X := connectedComponentIn (frontier D.carrier) (p : X)
  have hmem : ∀ t, gamma t ∈ C :=
    smoothFrontierTangentIntegralCurve_mem_connectedComponentIn
      D p hgamma0 hgamma
  let liftX : AddCircle P → X := hPperiodic.lift
  have hlift_mem : ∀ z : AddCircle P, liftX z ∈ C := by
    intro z
    refine Quotient.inductionOn' z ?_
    intro t
    simpa [liftX] using hmem t
  let liftC : AddCircle P → C := fun z => ⟨liftX z, hlift_mem z⟩
  have hliftX_continuous : Continuous liftX := by
    rw [isQuotientMap_quotient_mk'.continuous_iff]
    simpa [liftX, Function.comp_def] using hgamma.continuous
  have hliftC_continuous : Continuous liftC :=
    Continuous.subtype_mk hliftX_continuous hlift_mem
  have hliftC_injective : Function.Injective liftC := by
    intro z w
    refine Quotient.inductionOn₂' z w ?_
    intro a b hab
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    apply sub_mem_zmultiples_of_eq_of_fundamentalPeriod
      D hgamma hPpos hPperiodic hminimal
    have hab' := congrArg Subtype.val hab
    simpa [liftC, liftX] using hab'
  have hrange : range gamma = C := by
    simpa [C] using
      smoothFrontierTangentIntegralCurve_range_eq_frontierComponent
        D p hgamma0 hgamma
  have hliftC_surjective : Function.Surjective liftC := by
    intro x
    have hxrange : (x : X) ∈ range gamma := by
      rw [hrange]
      exact x.2
    rcases hxrange with ⟨t, ht⟩
    refine ⟨(t : AddCircle P), ?_⟩
    apply Subtype.ext
    simpa [liftC, liftX] using ht
  let equiv : AddCircle P ≃ C := Equiv.ofBijective liftC
    ⟨hliftC_injective, hliftC_surjective⟩
  letI : Fact (0 < P) := ⟨hPpos⟩
  have hliftC_closed : IsClosedMap liftC :=
    hliftC_continuous.isClosedMap
  have hinverse_continuous : Continuous equiv.symm := by
    rw [continuous_iff_isClosed]
    intro S hS
    have hpreimage : equiv.symm ⁻¹' S = liftC '' S := by
      ext y
      constructor
      · intro hy
        refine ⟨equiv.symm y, hy, ?_⟩
        exact equiv.apply_symm_apply y
      · rintro ⟨x, hx, hxy⟩
        have : equiv.symm y = x := by
          rw [← hxy]
          exact equiv.symm_apply_apply x
        change equiv.symm y ∈ S
        rw [this]
        exact hx
    rw [hpreimage]
    exact hliftC_closed S hS
  let homeo : AddCircle P ≃ₜ C :=
    { toEquiv := equiv
      continuous_toFun := hliftC_continuous
      continuous_invFun := hinverse_continuous }
  exact ⟨P, hPpos, ⟨homeo⟩⟩

/--
%%handwave
name:
  Smooth circle parametrization of a frontier component
statement:
  Every connected component \(C\) of a smooth compact frontier admits a
  smooth injective parametrization \(\phi:S^1\to\partial D\) with range \(C\).
  Moreover, at every \(z\in S^1\), \(\phi\) has a smooth local left inverse
  near \(\phi(z)\).
proof:
  Rescale a fundamental-period tangent trajectory and descend it from
  \(\mathbb R/P\mathbb Z\) to \(S^1\).  Centered angle branches prove local
  smoothness on the circle, while the fundamental-period property gives
  injectivity and the orbit-component theorem gives the range.  A boundary
  product coordinate has nonzero derivative along the trajectory, so the
  inverse function theorem supplies the local left inverses.
-/
theorem exists_smooth_circle_frontierComponent_parametrization
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) :
    letI := smoothBoundaryFrontierChartedSpace D
    ∃ phi : Circle → frontier D.carrier,
      ContMDiff
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
        (modelWithCornersSelf ℝ ℝ) ∞ phi ∧
      Function.Injective phi ∧
      range phi = connectedComponent p ∧
      ∀ z : Circle, ∃ g : frontier D.carrier → Circle,
        ContMDiffAt (modelWithCornersSelf ℝ ℝ)
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
          ∞ g (phi z) ∧
        (g ∘ phi) =ᶠ[nhds z] id := by
  classical
  letI := smoothBoundaryFrontierChartedSpace D
  letI : IsManifold (modelWithCornersSelf ℝ ℝ) ∞
      (frontier D.carrier) :=
    smoothBoundaryDomain_frontier_isSmoothOneManifold D
  rcases exists_fundamentalPeriod_smoothFrontierTangentIntegralCurve D p with
    ⟨gamma, P, hgamma0, hPpos, hgamma, hPperiodic, hminimal⟩
  have hPne : P ≠ 0 := ne_of_gt hPpos
  have hfrontier : ∀ t, gamma t ∈ frontier D.carrier :=
    smoothFrontierTangentIntegralCurve_mem_frontier D hgamma
      (hgamma0.symm ▸ p.2)
  let gammaF : ℝ → frontier D.carrier := fun t =>
    ⟨gamma t, hfrontier t⟩
  have hgammaFSmooth : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ ℝ) ∞ gammaF := by
    simpa [gammaF] using
      smoothFrontierTangentIntegralCurve_contMDiff_frontier
        D hgamma hfrontier
  have hgammaSmooth : ContMDiff (modelWithCornersSelf ℝ ℝ)
      SurfaceRealModel ∞ gamma :=
    IsMIntegralCurve.contMDiff_of_surfaceVectorField
      (smoothFrontierTangentVectorField D)
      (smoothFrontierTangentVectorField_contMDiff D) hgamma
  let liftF : AddCircle P → frontier D.carrier := fun z =>
    ⟨hPperiodic.lift z, by
      refine Quotient.inductionOn' z ?_
      exact fun t => hfrontier t⟩
  let phi : Circle → frontier D.carrier := fun z =>
    liftF ((AddCircle.homeomorphCircle hPne).symm z)
  let scale : ℝ := P / (2 * Real.pi)
  have hphi_exp : ∀ t : ℝ, phi (Circle.exp t) = gammaF (scale * t) := by
    intro t
    apply Subtype.ext
    change hPperiodic.lift
      ((AddCircle.homeomorphCircle hPne).symm (Circle.exp t)) =
        gamma (scale * t)
    rw [show (AddCircle.homeomorphCircle hPne).symm (Circle.exp t) =
        ((scale * t : ℝ) : AddCircle P) by
      simpa [scale] using addCircle_homeomorphCircle_symm_exp P hPne t]
    rfl
  have hphiSmooth : ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ ℝ) ∞ phi := by
    intro z
    let t : ℝ := Complex.arg (z : ℂ)
    have hzt : Circle.exp t = z := by
      simpa [t] using Circle.exp_arg z
    let tau : Circle → ℝ := fun w =>
      scale * (t + circleLocalAngle z w)
    have htau : ContMDiffAt
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
        (modelWithCornersSelf ℝ ℝ) ∞ tau z := by
      have hreal : ContDiff ℝ ∞ (fun r : ℝ => scale * (t + r)) :=
        contDiff_const.mul (contDiff_const.add contDiff_id)
      simpa [tau] using hreal.contDiffAt.contMDiffAt.comp z
        (circleLocalAngle_contMDiffAt z)
    have hlocal : ContMDiffAt
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
        (modelWithCornersSelf ℝ ℝ) ∞ (gammaF ∘ tau) z :=
      (hgammaFSmooth (tau z)).comp z htau
    have hexp : (fun w : Circle =>
        Circle.exp (t + circleLocalAngle z w)) =ᶠ[nhds z] id := by
      simpa only [hzt] using
        circleExp_add_circleLocalAngle_eventuallyEq t
    have heq : phi =ᶠ[nhds z] gammaF ∘ tau := by
      filter_upwards [hexp] with w hw
      change phi w = gammaF (scale * (t + circleLocalAngle z w))
      calc
        phi w = phi (Circle.exp
            (t + circleLocalAngle z w)) := congrArg phi hw.symm
        _ = gammaF (scale * (t + circleLocalAngle z w)) :=
          hphi_exp (t + circleLocalAngle z w)
    exact hlocal.congr_of_eventuallyEq heq
  have hliftF_injective : Function.Injective liftF := by
    intro z w
    refine Quotient.inductionOn₂' z w ?_
    intro a b hab
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    apply sub_mem_zmultiples_of_eq_of_fundamentalPeriod
      D hgamma hPpos hPperiodic hminimal
    exact congrArg Subtype.val hab
  have hphi_injective : Function.Injective phi :=
    hliftF_injective.comp (AddCircle.homeomorphCircle hPne).symm.injective
  have hlocalInverse : ∀ z : Circle,
      ∃ g : frontier D.carrier → Circle,
        ContMDiffAt (modelWithCornersSelf ℝ ℝ)
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
          ∞ g (phi z) ∧
        (g ∘ phi) =ᶠ[nhds z] id := by
    intro z
    let s : ℝ := Complex.arg (z : ℂ)
    have hzs : Circle.exp s = z := by
      simpa [s] using Circle.exp_arg z
    let base : ℝ := scale * s
    let q : frontier D.carrier := phi z
    have hgammaBase : gamma base = (q : X) := by
      have h := congrArg Subtype.val (hphi_exp s)
      rw [hzs] at h
      simpa [base, q] using h.symm
    let C := smoothBoundaryProductChartAt D q
    let affine : ℝ → ℝ := fun r => base + scale * r
    let theta : ℝ → ℝ := fun r =>
      (C.coordinate (gamma (affine r))).2
    have haffineSmooth : ContDiffAt ℝ ∞ affine 0 := by
      exact (contDiffAt_const.add (contDiffAt_const.mul contDiffAt_id))
    have hcoordAt : ContMDiffAt SurfaceRealModel
        (modelWithCornersSelf ℝ (ℝ × ℝ)) ∞
        C.coordinate (gamma base) := by
      have hmem : gamma base ∈ C.coordinate.source := by
        rw [hgammaBase]
        exact C.point_mem
      exact (C.coordinate.contMDiffOn_toFun (gamma base) hmem).contMDiffAt
        (C.coordinate.open_source.mem_nhds hmem)
    have hthetaSmooth : ContDiffAt ℝ ∞ theta 0 := by
      have hcurve : ContMDiffAt (modelWithCornersSelf ℝ ℝ)
          SurfaceRealModel ∞ (gamma ∘ affine) 0 :=
        (hgammaSmooth (affine 0)).comp 0 haffineSmooth.contMDiffAt
      have hcoord : ContMDiffAt (modelWithCornersSelf ℝ ℝ)
          (modelWithCornersSelf ℝ (ℝ × ℝ)) ∞
          (C.coordinate ∘ gamma ∘ affine) 0 := by
        have hbase : affine 0 = base := by simp [affine]
        have hcoordAt' : ContMDiffAt SurfaceRealModel
            (modelWithCornersSelf ℝ (ℝ × ℝ)) ∞
            C.coordinate (gamma (affine 0)) := by
          simpa only [hbase] using hcoordAt
        exact hcoordAt'.comp 0 hcurve
      simpa [theta, Function.comp_def] using hcoord.contDiffAt.snd
    have hstrictBase :=
      smoothFrontierProductAngularCoordinate_hasStrictDerivAt
        D q hgammaBase hgamma
    have haffineStrict : HasStrictDerivAt affine scale 0 := by
      simpa [affine] using
        (HasStrictDerivAt.const_mul scale
          (hasStrictDerivAt_id (x := (0 : ℝ)))).const_add base
    have hthetaStrict : HasStrictDerivAt theta
        ((smoothFrontierProductCoordinateVelocity D q (q : X)).2 * scale) 0 := by
      have hstrictBase' : HasStrictDerivAt
          (fun u : ℝ => (C.coordinate (gamma u)).2)
          (smoothFrontierProductCoordinateVelocity D q (q : X)).2
          (affine 0) := by
        simpa [affine, C] using hstrictBase
      simpa [theta, affine, C, Function.comp_def] using
        hstrictBase'.comp 0 haffineStrict
    have hscale : scale ≠ 0 := by
      dsimp [scale]
      exact div_ne_zero hPne
        (mul_ne_zero (by norm_num) (ne_of_gt Real.pi_pos))
    have hderiv_ne :
        (smoothFrontierProductCoordinateVelocity D q (q : X)).2 * scale ≠ 0 :=
      mul_ne_zero
        (smoothFrontierProductCoordinateVelocity_snd_ne_zero D q) hscale
    let e : ℝ ≃L[ℝ] ℝ :=
      ContinuousLinearEquiv.unitsEquivAut ℝ
        (Units.mk0
          ((smoothFrontierProductCoordinateVelocity D q (q : X)).2 * scale)
          hderiv_ne)
    have hthetaF : HasFDerivAt theta (e : ℝ →L[ℝ] ℝ) 0 := by
      simpa [e] using hthetaStrict.hasDerivAt.hasFDerivAt_equiv hderiv_ne
    let rinv : ℝ → ℝ :=
      hthetaSmooth.localInverse hthetaF (by norm_num)
    have htheta0 : theta 0 = 0 := by
      simp only [theta, affine, mul_zero, add_zero, hgammaBase]
      exact congrArg Prod.snd C.point_coord
    have hrinvSmooth : ContDiffAt ℝ ∞ rinv 0 := by
      have h := hthetaSmooth.to_localInverse hthetaF (by norm_num)
      simpa only [htheta0, rinv] using h
    have hleft : ∀ᶠ r in nhds (0 : ℝ), rinv (theta r) = r := by
      exact (hthetaSmooth.hasStrictFDerivAt' hthetaF (by norm_num))
        |>.eventually_left_inverse
    let g : frontier D.carrier → Circle := fun r =>
      Circle.exp (s + rinv (smoothBoundaryFrontierChart D q r))
    have hchart : ContMDiffAt (modelWithCornersSelf ℝ ℝ)
        (modelWithCornersSelf ℝ ℝ) ∞
        (smoothBoundaryFrontierChart D q) q := by
      change ContMDiffAt (modelWithCornersSelf ℝ ℝ)
        (modelWithCornersSelf ℝ ℝ) ∞
        (extChartAt (modelWithCornersSelf ℝ ℝ) q) q
      exact contMDiffAt_extChartAt
    have hchart0 : smoothBoundaryFrontierChart D q q = 0 := by
      exact congrArg Prod.snd C.point_coord
    have hgSmooth : ContMDiffAt (modelWithCornersSelf ℝ ℝ)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) ∞
        g q := by
      have hrinvChart : ContMDiffAt (modelWithCornersSelf ℝ ℝ)
          (modelWithCornersSelf ℝ ℝ) ∞
          (rinv ∘ smoothBoundaryFrontierChart D q) q := by
        have hrinvAt : ContMDiffAt (modelWithCornersSelf ℝ ℝ)
            (modelWithCornersSelf ℝ ℝ) ∞ rinv
            (smoothBoundaryFrontierChart D q q) := by
          simpa only [hchart0] using hrinvSmooth.contMDiffAt
        exact hrinvAt.comp q hchart
      have hphase : ContMDiffAt (modelWithCornersSelf ℝ ℝ)
          (modelWithCornersSelf ℝ ℝ) ∞
          (fun r : frontier D.carrier =>
            s + rinv (smoothBoundaryFrontierChart D q r)) q := by
        have hadd : ContDiffAt ℝ ∞ (fun u : ℝ => s + u)
            (rinv (smoothBoundaryFrontierChart D q q)) :=
          contDiffAt_const.add contDiffAt_id
        simpa only [Function.comp_def] using
          hadd.contMDiffAt.comp q hrinvChart
      have hcomp := (contMDiff_circleExp
        (s + rinv (smoothBoundaryFrontierChart D q q))).comp q hphase
      change ContMDiffAt (modelWithCornersSelf ℝ ℝ)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) ∞ g q
      exact hcomp
    have hangle0 : circleLocalAngle z z = 0 := by
      simp [circleLocalAngle, circleLocalSine, ← Circle.coe_inv_eq_conj]
    have hleftAngle : ∀ᶠ w in nhds z,
        rinv (theta (circleLocalAngle z w)) = circleLocalAngle z w := by
      have htend : Tendsto (circleLocalAngle z) (nhds z) (nhds 0) := by
        have hcont := (circleLocalAngle_contMDiffAt z).continuousAt
        rw [continuousAt_def, hangle0] at hcont
        exact hcont
      exact htend.eventually hleft
    have hexp : (fun w : Circle =>
        Circle.exp (s + circleLocalAngle z w)) =ᶠ[nhds z] id := by
      simpa only [hzs] using circleExp_add_circleLocalAngle_eventuallyEq s
    have hginv : (g ∘ phi) =ᶠ[nhds z] id := by
      filter_upwards [hleftAngle, hexp] with w hwleft hwexp
      have hphiAngle : phi w =
          gammaF (affine (circleLocalAngle z w)) := by
        calc
          phi w = phi (Circle.exp
              (s + circleLocalAngle z w)) := congrArg phi hwexp.symm
          _ = gammaF (scale * (s + circleLocalAngle z w)) :=
            hphi_exp (s + circleLocalAngle z w)
          _ = gammaF (affine (circleLocalAngle z w)) := by
            congr 2
            simp [affine, base]
            ring
      have hchartPhi : smoothBoundaryFrontierChart D q (phi w) =
          theta (circleLocalAngle z w) := by
        rw [hphiAngle]
        simp only [smoothBoundaryFrontierChart_apply, theta, gammaF, C]
      change g (phi w) = w
      rw [show g (phi w) = Circle.exp
          (s + rinv (smoothBoundaryFrontierChart D q (phi w))) by rfl,
        hchartPhi, hwleft]
      exact hwexp
    exact ⟨g, by simpa [q] using hgSmooth, hginv⟩
  have hrangeAmbient : range gamma =
      connectedComponentIn (frontier D.carrier) (p : X) :=
    smoothFrontierTangentIntegralCurve_range_eq_frontierComponent
      D p hgamma0 hgamma
  have hphi_range : range phi = connectedComponent p := by
    ext q
    constructor
    · rintro ⟨z, rfl⟩
      change liftF ((AddCircle.homeomorphCircle hPne).symm z) ∈
        connectedComponent p
      generalize ha : (AddCircle.homeomorphCircle hPne).symm z = a
      refine Quotient.inductionOn' a ?_
      intro t
      change (⟨gamma t, hfrontier t⟩ : frontier D.carrier) ∈
        connectedComponent p
      have ht := smoothFrontierTangentIntegralCurve_mem_connectedComponentIn
        D p hgamma0 hgamma t
      rw [connectedComponentIn_eq_image p.2] at ht
      rcases ht with ⟨q, hq, hqt⟩
      have heq : (⟨gamma t, hfrontier t⟩ : frontier D.carrier) = q :=
        Subtype.ext hqt.symm
      rw [heq]
      exact hq
    · intro hq
      have hqAmbient : (q : X) ∈
          connectedComponentIn (frontier D.carrier) (p : X) := by
        rw [connectedComponentIn_eq_image p.2]
        exact ⟨q, hq, rfl⟩
      rw [← hrangeAmbient] at hqAmbient
      rcases hqAmbient with ⟨t, ht⟩
      refine ⟨AddCircle.homeomorphCircle hPne (t : AddCircle P), ?_⟩
      apply Subtype.ext
      simpa [phi, liftF] using ht
  exact ⟨phi, hphiSmooth,
    ⟨hphi_injective, hphi_range, hlocalInverse⟩⟩

/-- A connected component of the smooth frontier, packaged as an open
submanifold of the frontier. -/
noncomputable def smoothFrontierComponentOpen
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) :
    TopologicalSpace.Opens (frontier D.carrier) where
  carrier := connectedComponent p
  is_open' := by
    letI := smoothBoundaryFrontierChartedSpace D
    letI : LocallyConnectedSpace (frontier D.carrier) :=
      ChartedSpace.locallyConnectedSpace ℝ (frontier D.carrier)
    exact isOpen_connectedComponent

/--
%%handwave
name:
  A connected smooth frontier component is a circle
statement:
  Every connected component of the smooth compact frontier is smoothly
  diffeomorphic to \(S^1\).
proof:
  Use the smooth injective circle parametrization whose image is the
  component.  Compactness makes it a homeomorphism.  Smooth local left
  inverses of the parametrization agree locally with the inverse
  homeomorphism, proving that the inverse is smooth.
-/
theorem exists_diffeomorph_circle_smoothFrontierComponent
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) :
    letI := smoothBoundaryFrontierChartedSpace D
    Nonempty (Circle ≃ₘ⟮
      modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)),
      modelWithCornersSelf ℝ ℝ⟯ smoothFrontierComponentOpen D p) := by
  classical
  letI := smoothBoundaryFrontierChartedSpace D
  letI : IsManifold (modelWithCornersSelf ℝ ℝ) ∞
      (frontier D.carrier) :=
    smoothBoundaryDomain_frontier_isSmoothOneManifold D
  letI : LocallyConnectedSpace (frontier D.carrier) :=
    ChartedSpace.locallyConnectedSpace ℝ (frontier D.carrier)
  let U := smoothFrontierComponentOpen D p
  rcases exists_smooth_circle_frontierComponent_parametrization D p with
    ⟨phi, hphiSmooth, hphiInjective, hphiRange, hlocalInverse⟩
  have hphiMem : ∀ z, phi z ∈ U := by
    intro z
    change phi z ∈ connectedComponent p
    rw [← hphiRange]
    exact mem_range_self z
  let phiU : Circle → U := fun z => ⟨phi z, hphiMem z⟩
  have hphiUSurjective : Function.Surjective phiU := by
    intro q
    have hq : (q : frontier D.carrier) ∈ range phi := by
      rw [hphiRange]
      exact q.2
    rcases hq with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    exact Subtype.ext hz
  have hphiUInjective : Function.Injective phiU := by
    intro z w hzw
    apply hphiInjective
    exact congrArg Subtype.val hzw
  let equiv : Circle ≃ U := Equiv.ofBijective phiU
    ⟨hphiUInjective, hphiUSurjective⟩
  have hphiUContinuous : Continuous phiU :=
    Continuous.subtype_mk hphiSmooth.continuous hphiMem
  have hphiUClosed : IsClosedMap phiU :=
    hphiUContinuous.isClosedMap
  let homeo : Circle ≃ₜ U :=
    equiv.toHomeomorphOfContinuousClosed hphiUContinuous hphiUClosed
  have hphiUSmooth : ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ ℝ) ∞ phiU := by
    intro z
    let qU : U := phiU z
    let retract : frontier D.carrier → U := fun q =>
      if hq : q ∈ U then ⟨q, hq⟩ else qU
    have hretractAt : ContMDiffAt (modelWithCornersSelf ℝ ℝ)
        (modelWithCornersSelf ℝ ℝ) ∞ retract (phi z) := by
      rw [← contMDiffAt_subtype_iff (U := U) (x := qU)]
      have heq : (fun q : U => retract q) = id := by
        funext q
        simp [retract]
      rw [heq]
      exact contMDiffAt_id
    have heq : phiU = retract ∘ phi := by
      funext w
      simp [phiU, retract, hphiMem]
    rw [heq]
    exact hretractAt.comp z (hphiSmooth z)
  have hhomeoInvSmooth : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) ∞
      homeo.symm := by
    intro q
    let z : Circle := homeo.symm q
    have hhomeo_z : homeo z = q := homeo.apply_symm_apply q
    have hphi_z : phi z = (q : frontier D.carrier) := by
      have hval := congrArg Subtype.val hhomeo_z
      change phi z = (q : frontier D.carrier) at hval
      exact hval
    rcases hlocalInverse z with ⟨g, hgSmooth, hginv⟩
    have hgq : ContMDiffAt (modelWithCornersSelf ℝ ℝ)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) ∞
        g (q : frontier D.carrier) := by
      simpa only [hphi_z] using hgSmooth
    have hgSubtype : ContMDiffAt (modelWithCornersSelf ℝ ℝ)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) ∞
        (g ∘ (Subtype.val : U → frontier D.carrier)) q :=
      hgq.comp q (contMDiff_subtype_val q)
    have hevent : homeo.symm =ᶠ[nhds q]
        g ∘ (Subtype.val : U → frontier D.carrier) := by
      have hpull := homeo.symm.continuous.continuousAt.eventually hginv
      filter_upwards [hpull] with r hr
      change homeo.symm r = g (r : frontier D.carrier)
      have hphiInv : phi (homeo.symm r) = (r : frontier D.carrier) := by
        have hval := congrArg Subtype.val (homeo.apply_symm_apply r)
        change phi (homeo.symm r) = (r : frontier D.carrier) at hval
        exact hval
      have hr' : g (phi (homeo.symm r)) = homeo.symm r := by
        simpa only [Function.comp_apply, id_eq] using hr
      rw [hphiInv] at hr'
      exact hr'.symm
    exact hgSubtype.congr_of_eventuallyEq hevent
  let diffeo : Circle ≃ₘ⟮
      modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)),
      modelWithCornersSelf ℝ ℝ⟯ U :=
    { toEquiv := homeo.toEquiv
      contMDiff_toFun := by
        simpa [homeo, equiv] using hphiUSmooth
      contMDiff_invFun := hhomeoInvSmooth }
  exact ⟨diffeo⟩

/--
%%handwave
name:
  Side-preserving annular collar of a frontier component
statement:
  Let \(C\) be the frontier component through \(p\).  There is an open
  neighborhood \(W\subseteq X\) containing \(C\) and a diffeomorphism
  \(\Phi:W\to S^1\times\mathbb R\) such that
  \[
    y\in D\iff \Phi(y)_2<0,
    \qquad
    y\notin\overline D\iff \Phi(y)_2>0.
  \]
proof:
  Start with the smooth product collar \(C\times(-\rho,\rho)\to X\).  Identify
  \(C\) smoothly with \(S^1\), and identify the transverse interval with
  \(\mathbb R\) by the sign-preserving tangent coordinate.  Their product,
  composed with the collar, is the desired diffeomorphism; the collar side
  formulas and sign preservation give the two equivalences.
-/
theorem exists_sidePreservingDiffeomorph_annularCylinder_smoothFrontierComponentCollar
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) :
    ∃ W : TopologicalSpace.Opens X,
      (p : X) ∈ W ∧
      Subtype.val '' connectedComponent p ⊆ (W : Set X) ∧
      ∃ phi : W ≃ₘ⟮SurfaceRealModel,
        JJMath.Manifold.AnnularCylinderModel⟯ (Circle × ℝ),
        (∀ y : W, ((y : X) ∈ D.carrier ↔ (phi y).2 < 0)) ∧
        ∀ y : W, ((y : X) ∉ closure D.carrier ↔ 0 < (phi y).2) := by
  classical
  rcases exists_smoothFrontierComponentCollar D p with
    ⟨rho, hrho, Psi, E, hEsource, hEcoe, hinitial,
      hcoordinateNeighborhood, hside, hexteriorSide,
      hEforwardSmooth, hEinverseSmooth⟩
  letI := smoothBoundaryFrontierChartedSpace D
  letI : IsManifold (modelWithCornersSelf ℝ ℝ) ∞
      (frontier D.carrier) :=
    smoothBoundaryDomain_frontier_isSmoothOneManifold D
  letI : LocallyConnectedSpace (frontier D.carrier) :=
    ChartedSpace.locallyConnectedSpace ℝ (frontier D.carrier)
  rcases exists_diffeomorph_circle_smoothFrontierComponent D p with
    ⟨chi⟩
  let eta := symmetricOpenIntervalDiffeomorphReal rho hrho
  let C := smoothFrontierComponentOpen D p
  let J := symmetricOpenInterval rho
  let S := smoothFrontierComponentCollarOpen D p rho
  let W : TopologicalSpace.Opens X := ⟨E.target, E.open_target⟩
  let coord : W → S := fun y => E.symm (y : X)
  let toCylinder : W → Circle × ℝ := fun y =>
    (chi.symm ⟨(coord y).1.1, (coord y).2.1⟩,
      eta ⟨(coord y).1.2, (coord y).2.2⟩)
  let fromCylinderRaw : Circle × ℝ → frontier D.carrier × ℝ := fun z =>
    ((chi z.1 : C), (eta.symm z.2 : J))
  have hfromMem : ∀ z, fromCylinderRaw z ∈ S := by
    intro z
    exact ⟨(chi z.1).2, (eta.symm z.2).2⟩
  let fromCylinderS : Circle × ℝ → S := fun z =>
    ⟨fromCylinderRaw z, hfromMem z⟩
  have hfromSource : ∀ z, fromCylinderS z ∈ E.source := by
    intro z
    rw [hEsource]
    exact mem_univ _
  let fromCylinder : Circle × ℝ → W := fun z =>
    ⟨E (fromCylinderS z), E.map_source (hfromSource z)⟩
  have hleft : Function.LeftInverse fromCylinder toCylinder := by
    intro y
    apply Subtype.ext
    let u : connectedComponent p ×ˢ Ioo (-rho) rho := E.symm (y : X)
    have huSource : u ∈ E.source := E.symm_mapsTo y.2
    have hfirst :
        (chi (chi.symm ⟨u.1.1, u.2.1⟩) : C) = u.1.1 := by
      exact congrArg Subtype.val (chi.apply_symm_apply ⟨u.1.1, u.2.1⟩)
    have hsecond :
        (eta.symm (eta ⟨u.1.2, u.2.2⟩) : J) = u.1.2 := by
      exact congrArg Subtype.val (eta.symm_apply_apply ⟨u.1.2, u.2.2⟩)
    have hsourcePoint : fromCylinderS (toCylinder y) = u := by
      apply Subtype.ext
      apply Prod.ext
      · exact hfirst
      · exact hsecond
    change E (fromCylinderS (toCylinder y)) = (y : X)
    rw [hsourcePoint]
    exact E.right_inv y.2
  have hright : Function.RightInverse fromCylinder toCylinder := by
    intro z
    let u : S := fromCylinderS z
    have huSource : u ∈ E.source := hfromSource z
    have hEinv : E.symm (E u) = u := E.left_inv huSource
    apply Prod.ext
    · change chi.symm
          ⟨(E.symm (E u)).1.1, (E.symm (E u)).2.1⟩ = z.1
      rw [hEinv]
      exact chi.symm_apply_apply z.1
    · change eta
          ⟨(E.symm (E u)).1.2, (E.symm (E u)).2.2⟩ = z.2
      rw [hEinv]
      exact eta.apply_symm_apply z.2
  let equiv : W ≃ Circle × ℝ :=
    { toFun := toCylinder
      invFun := fromCylinder
      left_inv := hleft
      right_inv := hright }
  have hcoordSmooth : ContMDiff SurfaceRealModel
      ((modelWithCornersSelf ℝ ℝ).prod
        (modelWithCornersSelf ℝ ℝ)) ∞
      (fun y : W => ((E.symm (y : X) :
        connectedComponent p ×ˢ Ioo (-rho) rho) :
          frontier D.carrier × ℝ)) := by
    intro y
    have hamb : ContMDiffAt SurfaceRealModel
        ((modelWithCornersSelf ℝ ℝ).prod
          (modelWithCornersSelf ℝ ℝ)) ∞
        (fun x : X => ((E.symm x : connectedComponent p ×ˢ
          Ioo (-rho) rho) : frontier D.carrier × ℝ)) (y : X) :=
      (hEinverseSmooth (y : X) y.2).contMDiffAt
        (E.open_target.mem_nhds y.2)
    exact hamb.comp y (contMDiff_subtype_val y)
  have hfirstMem : ∀ y : W,
      (coord y).1.1 ∈ C := fun y => (coord y).2.1
  have hsecondMem : ∀ y : W,
      (coord y).1.2 ∈ J := fun y => (coord y).2.2
  have hfirstSmooth : ContMDiff SurfaceRealModel
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun y : W =>
        (⟨(coord y).1.1, hfirstMem y⟩ : C)) :=
    ContMDiff.codRestrict_open hcoordSmooth.fst C hfirstMem
  have hsecondSmooth : ContMDiff SurfaceRealModel
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun y : W =>
        (⟨(coord y).1.2, hsecondMem y⟩ : J)) :=
    ContMDiff.codRestrict_open hcoordSmooth.snd J hsecondMem
  have htoSmooth : ContMDiff SurfaceRealModel
      JJMath.Manifold.AnnularCylinderModel ∞
      toCylinder := by
    have hcircle := chi.symm.contMDiff.comp hfirstSmooth
    have hreal := eta.contMDiff.comp hsecondSmooth
    simpa [toCylinder] using hcircle.prodMk hreal
  have hchiVal : ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun z : Circle => (chi z : frontier D.carrier)) :=
    (contMDiff_subtype_val (I := modelWithCornersSelf ℝ ℝ))
      |>.comp chi.contMDiff
  have hetaVal : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun t : ℝ => (eta.symm t : ℝ)) :=
    (contMDiff_subtype_val (I := modelWithCornersSelf ℝ ℝ))
      |>.comp eta.symm.contMDiff
  have hrawSmooth : ContMDiff JJMath.Manifold.AnnularCylinderModel
      ((modelWithCornersSelf ℝ ℝ).prod
        (modelWithCornersSelf ℝ ℝ)) ∞ fromCylinderRaw := by
    simpa [fromCylinderRaw] using hchiVal.prodMap hetaVal
  have hsourceSmooth : ContMDiff JJMath.Manifold.AnnularCylinderModel
      ((modelWithCornersSelf ℝ ℝ).prod
        (modelWithCornersSelf ℝ ℝ)) ∞ fromCylinderS := by
    exact ContMDiff.codRestrict_open hrawSmooth S hfromMem
  have hfromAmbient : ContMDiff JJMath.Manifold.AnnularCylinderModel
      SurfaceRealModel ∞
      (fun z => E (fromCylinderS z)) :=
    hEforwardSmooth.comp hsourceSmooth
  have hfromSmooth : ContMDiff JJMath.Manifold.AnnularCylinderModel
      SurfaceRealModel ∞
      fromCylinder := by
    exact ContMDiff.codRestrict_open hfromAmbient W
      (fun z => E.map_source (hfromSource z))
  let diffeo : W ≃ₘ⟮SurfaceRealModel,
      JJMath.Manifold.AnnularCylinderModel⟯ Circle × ℝ :=
    { toEquiv := equiv
      contMDiff_toFun := by simpa [equiv] using htoSmooth
      contMDiff_invFun := by simpa [equiv] using hfromSmooth }
  have hpW : (p : X) ∈ W := by
    let u : connectedComponent p ×ˢ Ioo (-rho) rho :=
      ⟨(p, 0), mem_connectedComponent, by constructor <;> linarith⟩
    have huSource : u ∈ E.source := by
      rw [hEsource]
      exact mem_univ _
    have hEu : E u = (p : X) := by
      rw [hEcoe]
      exact hinitial p mem_connectedComponent
    rw [← hEu]
    exact E.map_source huSource
  have hcomponentW :
      Subtype.val '' connectedComponent p ⊆ (W : Set X) := by
    rintro _q ⟨q, hq, rfl⟩
    let u : connectedComponent p ×ˢ Ioo (-rho) rho :=
      ⟨(q, 0), hq, by constructor <;> linarith⟩
    have huSource : u ∈ E.source := by
      rw [hEsource]
      exact mem_univ _
    have hEu : E u = (q : X) := by
      rw [hEcoe]
      exact hinitial q hq
    rw [← hEu]
    exact E.map_source huSource
  have hdiffeoSide : ∀ y : W,
      ((y : X) ∈ D.carrier ↔ (diffeo y).2 < 0) := by
    intro y
    let u : S := E.symm (y : X)
    have huTarget : (y : X) ∈ E.target := y.2
    have huSource : u ∈ E.source := E.symm_mapsTo huTarget
    have hEu : E u = (y : X) := E.right_inv huTarget
    have hPsi : Psi (u : frontier D.carrier × ℝ) = (y : X) := by
      rw [← hEu, hEcoe]
      rfl
    have hsideu := hside u.1.1 u.2.1 u.1.2 u.2.2
    rw [hPsi] at hsideu
    change ((y : X) ∈ D.carrier ↔
      eta ⟨u.1.2, u.2.2⟩ < 0)
    rw [hsideu]
    exact symmetricOpenIntervalDiffeomorphReal_lt_zero_iff
      rho hrho ⟨u.1.2, u.2.2⟩ |>.symm
  have hdiffeoExteriorSide : ∀ y : W,
      ((y : X) ∉ closure D.carrier ↔ 0 < (diffeo y).2) := by
    intro y
    let u : S := E.symm (y : X)
    have huTarget : (y : X) ∈ E.target := y.2
    have huSource : u ∈ E.source := E.symm_mapsTo huTarget
    have hEu : E u = (y : X) := E.right_inv huTarget
    have hPsi : Psi (u : frontier D.carrier × ℝ) = (y : X) := by
      rw [← hEu, hEcoe]
      rfl
    have hsideu := hexteriorSide u.1.1 u.2.1 u.1.2 u.2.2
    rw [hPsi] at hsideu
    change ((y : X) ∉ closure D.carrier ↔
      0 < eta ⟨u.1.2, u.2.2⟩)
    rw [hsideu]
    exact symmetricOpenIntervalDiffeomorphReal_pos_iff
      rho hrho ⟨u.1.2, u.2.2⟩ |>.symm
  exact ⟨W, hpW, hcomponentW, diffeo,
    hdiffeoSide, hdiffeoExteriorSide⟩

/--
%%handwave
name:
  Annular collar of a smooth frontier component
statement:
  Every point \(p\) of a smooth compact frontier has an open neighborhood
  \(W\subseteq X\) smoothly diffeomorphic to the annular cylinder
  \(S^1\times\mathbb R\).
proof:
  Forget the side-preserving conclusions of the annular collar
  diffeomorphism constructed for the frontier component through \(p\).
-/
theorem exists_diffeomorph_annularCylinder_smoothFrontierComponentCollar
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) :
    ∃ W : TopologicalSpace.Opens X,
      (p : X) ∈ W ∧
      Nonempty (W ≃ₘ⟮SurfaceRealModel,
        JJMath.Manifold.AnnularCylinderModel⟯ (Circle × ℝ)) := by
  rcases
      exists_sidePreservingDiffeomorph_annularCylinder_smoothFrontierComponentCollar
        D p with
    ⟨W, hpW, _hcomponentW, phi, _hside, _hexteriorSide⟩
  exact ⟨W, hpW, ⟨phi⟩⟩

/--
%%handwave
name:
  Preconnectedness of the exterior half of an annular collar
statement:
  Suppose a diffeomorphism \(\Phi:W\to S^1\times\mathbb R\) identifies
  \(W\setminus\overline D\) with \(S^1\times(0,\infty)\).  Then
  \(W\setminus\overline D\) is preconnected.
proof:
  The circle is the continuous image of the connected real line, hence is
  preconnected, and so is its product with \((0,\infty)\).  The inverse collar
  map sends that product continuously and surjectively onto the exterior
  half, preserving preconnectedness.
-/
theorem sidePreservingAnnularCollar_exteriorSide_isPreconnected
    (D : SmoothBoundaryDomain X) (W : TopologicalSpace.Opens X)
    (phi : W ≃ₘ⟮SurfaceRealModel,
      JJMath.Manifold.AnnularCylinderModel⟯ (Circle × ℝ))
    (hexteriorSide :
      ∀ y : W, ((y : X) ∉ closure D.carrier ↔ 0 < (phi y).2)) :
    IsPreconnected ((W : Set X) ∩ (closure D.carrier)ᶜ) := by
  let T : Set (Circle × ℝ) := univ ×ˢ Ioi 0
  have hexpSurjective : Function.Surjective Circle.exp := by
    intro z
    refine ⟨Complex.arg z, ?_⟩
    simpa using Circle.exp_arg z
  have hCirclePre : IsPreconnected (univ : Set Circle) := by
    rw [← Set.image_univ_of_surjective hexpSurjective]
    exact isPreconnected_univ.image Circle.exp Circle.exp.continuous.continuousOn
  have hTpre : IsPreconnected T :=
    hCirclePre.prod isPreconnected_Ioi
  let f : Circle × ℝ → X := fun z => ((phi.symm z : W) : X)
  have hf : Continuous f :=
    continuous_subtype_val.comp phi.symm.continuous
  have himage : f '' T =
      (W : Set X) ∩ (closure D.carrier)ᶜ := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨(phi.symm z).2, ?_⟩
      apply (hexteriorSide (phi.symm z)).mpr
      simpa [T] using hz.2
    · rintro ⟨hxW, hxExterior⟩
      let y : W := ⟨x, hxW⟩
      have hpositive : 0 < (phi y).2 := (hexteriorSide y).mp hxExterior
      refine ⟨phi y, ⟨mem_univ _, hpositive⟩, ?_⟩
      change ((phi.symm (phi y) : W) : X) = x
      simp [y]
  rw [← himage]
  exact hTpre.image f hf.continuousOn

/-- Restrict a side-preserving annular collar to its domain half. -/
noncomputable def sidePreservingAnnularCollarDomainRestriction
    (D : SmoothBoundaryDomain X) (W : TopologicalSpace.Opens X)
    (phi : W ≃ₘ⟮SurfaceRealModel,
      JJMath.Manifold.AnnularCylinderModel⟯ (Circle × ℝ))
    (hside : ∀ y : W, ((y : X) ∈ D.carrier ↔ (phi y).2 < 0)) :
    (W ⊓ ⟨D.carrier, D.isOpen⟩ : TopologicalSpace.Opens X) ≃ₘ⟮
      SurfaceRealModel, JJMath.Manifold.AnnularCylinderModel⟯
      negativeAnnularCylinderOpen := by
  let WD : TopologicalSpace.Opens X := W ⊓ ⟨D.carrier, D.isOpen⟩
  let toW : WD → W := fun y => ⟨(y : X), y.2.1⟩
  have htoW : ContMDiff SurfaceRealModel SurfaceRealModel ∞ toW :=
    ContMDiff.codRestrict_open
      (contMDiff_subtype_val (I := SurfaceRealModel)) W
      (fun y : WD => y.2.1)
  let toRaw : WD → Circle × ℝ := fun y => phi (toW y)
  have htoRaw : ContMDiff SurfaceRealModel
      JJMath.Manifold.AnnularCylinderModel ∞ toRaw :=
    phi.contMDiff.comp htoW
  have htoMem : ∀ y : WD, toRaw y ∈ negativeAnnularCylinderOpen := by
    intro y
    exact ⟨mem_univ _, (hside (toW y)).mp y.2.2⟩
  let toNeg : WD → negativeAnnularCylinderOpen := fun y =>
    ⟨toRaw y, htoMem y⟩
  have htoNeg : ContMDiff SurfaceRealModel
      JJMath.Manifold.AnnularCylinderModel ∞ toNeg :=
    ContMDiff.codRestrict_open htoRaw negativeAnnularCylinderOpen htoMem
  let fromRaw : negativeAnnularCylinderOpen → X := fun z =>
    (phi.symm (z : Circle × ℝ) : W)
  have hfromRaw : ContMDiff JJMath.Manifold.AnnularCylinderModel
      SurfaceRealModel ∞ fromRaw :=
    (contMDiff_subtype_val (I := SurfaceRealModel)).comp
      (phi.symm.contMDiff.comp
        (contMDiff_subtype_val
          (I := JJMath.Manifold.AnnularCylinderModel)))
  have hfromMem : ∀ z : negativeAnnularCylinderOpen, fromRaw z ∈ WD := by
    intro z
    have hzD : ((phi.symm (z : Circle × ℝ) : W) : X) ∈ D.carrier := by
      apply (hside (phi.symm (z : Circle × ℝ))).mpr
      simpa using z.2.2
    exact ⟨(phi.symm (z : Circle × ℝ)).2, hzD⟩
  let fromNeg : negativeAnnularCylinderOpen → WD := fun z =>
    ⟨fromRaw z, hfromMem z⟩
  have hfromNeg : ContMDiff JJMath.Manifold.AnnularCylinderModel
      SurfaceRealModel ∞ fromNeg :=
    ContMDiff.codRestrict_open hfromRaw WD hfromMem
  let equiv : WD ≃ negativeAnnularCylinderOpen :=
    { toFun := toNeg
      invFun := fromNeg
      left_inv := by
        intro y
        apply Subtype.ext
        change ((phi.symm (phi (toW y)) : W) : X) = (y : X)
        rw [phi.symm_apply_apply]
      right_inv := by
        intro z
        apply Subtype.ext
        change phi (phi.symm (z : Circle × ℝ)) = (z : Circle × ℝ)
        exact phi.apply_symm_apply z }
  exact
    { toEquiv := equiv
      contMDiff_toFun := htoNeg
      contMDiff_invFun := hfromNeg }

/-- The domain half of a side-preserving frontier collar is itself an
annular cylinder. -/
noncomputable def sidePreservingAnnularCollarDomainDiffeomorph
    (D : SmoothBoundaryDomain X) (W : TopologicalSpace.Opens X)
    (phi : W ≃ₘ⟮SurfaceRealModel,
      JJMath.Manifold.AnnularCylinderModel⟯ (Circle × ℝ))
    (hside : ∀ y : W, ((y : X) ∈ D.carrier ↔ (phi y).2 < 0)) :
    (W ⊓ ⟨D.carrier, D.isOpen⟩ : TopologicalSpace.Opens X) ≃ₘ⟮
      SurfaceRealModel, JJMath.Manifold.AnnularCylinderModel⟯
      (Circle × ℝ) :=
  (sidePreservingAnnularCollarDomainRestriction D W phi hside).trans
    negativeAnnularCylinderOpenDiffeomorphAnnularCylinder

/--
%%handwave
name:
  An interior annular collar of every smooth frontier component
statement:
  For every \(p\in\partial D\), there is an open set \(W\subseteq D\) smoothly
  diffeomorphic to \(S^1\times\mathbb R\).
proof:
  Take a side-preserving annular collar of the frontier component through
  \(p\), restrict it to its negative-coordinate half inside \(D\), and use
  the logarithmic diffeomorphism from that half-cylinder to the full annular
  cylinder.
-/
theorem exists_diffeomorph_annularCylinder_smoothFrontierComponent_domainCollar
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) :
    ∃ W : TopologicalSpace.Opens X,
      W ≤ ⟨D.carrier, D.isOpen⟩ ∧
      Nonempty (W ≃ₘ⟮SurfaceRealModel,
        JJMath.Manifold.AnnularCylinderModel⟯ (Circle × ℝ)) := by
  rcases
      exists_sidePreservingDiffeomorph_annularCylinder_smoothFrontierComponentCollar
        D p with
    ⟨C, _hpC, _hcomponentC, phi, hside, _hexteriorSide⟩
  let W : TopologicalSpace.Opens X := C ⊓ ⟨D.carrier, D.isOpen⟩
  refine ⟨W, inf_le_right, ?_⟩
  exact ⟨sidePreservingAnnularCollarDomainDiffeomorph D C phi hside⟩

end

end JJMath.Uniformization
