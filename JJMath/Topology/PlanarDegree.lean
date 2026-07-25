import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Complex.Tietze
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Separation.Profinite

/-!
# Local orientation for planar homeomorphisms

This file gives a topological, componentwise definition of orientation for a
homeomorphism between planar domains. Around each point, map a small positive
circle, translate its image center to zero, and normalize its base point to
one. The homeomorphism preserves orientation when this loop is homotopic in
the punctured plane to the positive unit circle.
-/

namespace JJMath

open Set
open scoped Topology ContDiff

namespace Quasiconformal

noncomputable section

/-- The punctured complex plane. -/
abbrev PuncturedComplex := {z : ℂ // z ≠ 0}

/--
%%handwave
name:
  Gluing continuous maps over a finite closed cover
statement:
  Let $X=\bigcup_{i\in I}S_i$, where $I$ is finite and every $S_i$ is
  closed. Suppose continuous maps $f_i:S_i\to Y$ agree at every point of
  every overlap $S_i\cap S_j$. Then there is a continuous map $F:X\to Y$
  whose restriction to each $S_i$ is $f_i$.
proof:
  At each point of the union choose one member of the cover and evaluate its
  map. Compatibility makes the result independent of the choice. On each
  closed member it agrees with the corresponding continuous map, and the
  finite closed-cover pasting lemma gives continuity.
-/
theorem exists_continuousMap_iUnion_of_finite_closed
    {X Y ι : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [Finite ι] [Nonempty ι]
    (s : ι → Set X) (hs : ∀ i, IsClosed (s i))
    (f : ∀ i, C(s i, Y))
    (hcompat : ∀ i j x (hxi : x ∈ s i)
      (hxj : x ∈ s j),
      f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩) :
    ∃ F : C(⋃ i, s i, Y),
      ∀ i x (hxi : x ∈ s i),
        F ⟨x, Set.mem_iUnion.mpr ⟨i, hxi⟩⟩ =
          f i ⟨x, hxi⟩ := by
  let U : Set X := ⋃ i, s i
  let pick (x : U) : ι :=
    Classical.choose (Set.mem_iUnion.mp x.2)
  have hpick (x : U) : (x : X) ∈ s (pick x) :=
    Classical.choose_spec (Set.mem_iUnion.mp x.2)
  let G : U → Y := fun x ↦
    f (pick x) ⟨x, hpick x⟩
  have hG (i : ι) (x : U)
      (hxi : (x : X) ∈ s i) :
      G x = f i ⟨x, hxi⟩ :=
    hcompat (pick x) i x (hpick x) hxi
  let t : ι → Set U := fun i ↦
    Subtype.val ⁻¹' s i
  have htclosed (i : ι) : IsClosed (t i) :=
    (hs i).preimage continuous_subtype_val
  have hGcont (i : ι) : ContinuousOn G (t i) := by
    rw [continuousOn_iff_continuous_restrict]
    change Continuous (fun x : t i ↦ G x)
    let e : C(t i, s i) :=
      ⟨fun x ↦ ⟨(x : U), x.2⟩, by
        fun_prop⟩
    have heq :
        (fun x : t i ↦ G x) = f i ∘ e := by
      funext x
      exact hG i x x.2
    rw [heq]
    exact (f i).continuous.comp e.continuous
  have htcover : ⋃ i, t i = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    change x ∈ ⋃ i, t i
    rw [Set.mem_iUnion]
    change ∃ i, (x : X) ∈ s i
    exact Set.mem_iUnion.mp x.2
  have hGcontinuous : Continuous G := by
    rw [← continuousOn_univ, ← htcover]
    exact (locallyFinite_of_finite t).continuousOn_iUnion
      htclosed hGcont
  let F : C(U, Y) := ⟨G, hGcontinuous⟩
  refine ⟨F, ?_⟩
  intro i x hxi
  exact hG i
    ⟨x, Set.mem_iUnion.mpr ⟨i, hxi⟩⟩ hxi

/--
%%handwave
name:
  Logarithmic lift of a punctured-plane path
statement:
  For a path $\gamma:[0,1]\to\mathbb C\setminus\{0\}$ starting at $a$, its
  logarithmic lift is the unique continuous path $L_\gamma$ satisfying
  $$
    L_\gamma(0)=\log a,
    \qquad e^{L_\gamma(t)}=\gamma(t).
  $$
-/
noncomputable def puncturedPathLogLift
    {a b : PuncturedComplex} (γ : Path a b) : C(unitInterval, ℂ) :=
  Complex.isCoveringMap_exp.liftPath γ (Complex.log (a : ℂ)) (by
    apply Subtype.ext
    exact (congrArg Subtype.val γ.source).trans
      (Complex.exp_log a.2).symm)

/--
%%handwave
name:
  Exponential of a punctured-path logarithmic lift
statement:
  If $L_\gamma$ is the logarithmic lift of a path $\gamma$ in the punctured
  plane, then $e^{L_\gamma(t)}=\gamma(t)$ for every $t\in[0,1]$.
proof:
  This is the lifting identity for the exponential covering map.
-/
theorem exp_puncturedPathLogLift
    {a b : PuncturedComplex} (γ : Path a b) (t : unitInterval) :
    Complex.exp (puncturedPathLogLift γ t) = γ t := by
  have h := congr_fun
    (Complex.isCoveringMap_exp.liftPath_lifts γ (Complex.log (a : ℂ)) (by
      apply Subtype.ext
      exact (congrArg Subtype.val γ.source).trans
        (Complex.exp_log a.2).symm)) t
  exact congrArg Subtype.val h

/--
%%handwave
name:
  Initial value of a punctured-path logarithmic lift
statement:
  If a punctured-plane path $\gamma$ starts at $a$, then its logarithmic lift
  satisfies $L_\gamma(0)=\log a$.
proof:
  This is the prescribed initial value in path lifting.
-/
@[simp]
theorem puncturedPathLogLift_zero
    {a b : PuncturedComplex} (γ : Path a b) :
    puncturedPathLogLift γ 0 = Complex.log (a : ℂ) := by
  exact Complex.isCoveringMap_exp.liftPath_zero γ _ _

/--
%%handwave
name:
  Logarithmic increment of a punctured-plane path
statement:
  The logarithmic increment of a path $\gamma$ in
  $\mathbb C\setminus\{0\}$ is
  $$
    \Delta\log(\gamma)=L_\gamma(1)-L_\gamma(0),
  $$
  where $L_\gamma$ is its logarithmic lift.
-/
noncomputable def puncturedPathLogIncrement
    {a b : PuncturedComplex} (γ : Path a b) : ℂ :=
  puncturedPathLogLift γ 1 - puncturedPathLogLift γ 0

/--
%%handwave
name:
  Additivity of logarithmic path increments
statement:
  If $\gamma_0$ ends where $\gamma_1$ begins, then
  $$
    \Delta\log(\gamma_0*\gamma_1)
      =\Delta\log(\gamma_0)+\Delta\log(\gamma_1).
  $$
proof:
  Shift the logarithmic lift of $\gamma_1$ so that it starts at the endpoint
  of the lift of $\gamma_0$. Uniqueness of path lifting identifies the
  concatenation with the lift of $\gamma_0*\gamma_1$.
-/
theorem puncturedPathLogIncrement_trans
    {a b c : PuncturedComplex} (γ₀ : Path a b) (γ₁ : Path b c) :
    puncturedPathLogIncrement (γ₀.trans γ₁) =
      puncturedPathLogIncrement γ₀ +
        puncturedPathLogIncrement γ₁ := by
  let cov := Complex.isCoveringMap_exp
  let L₀ : C(unitInterval, ℂ) := puncturedPathLogLift γ₀
  let L₁ : C(unitInterval, ℂ) := puncturedPathLogLift γ₁
  have hbLift : b =
      (⟨Complex.exp (L₀ 1), Complex.exp_ne_zero _⟩ :
        PuncturedComplex) := by
    apply Subtype.ext
    exact (congrArg Subtype.val γ₀.target).symm.trans
      (exp_puncturedPathLogLift γ₀ 1).symm
  have hγ₁liftStart : γ₁ 0 =
      (⟨Complex.exp (L₀ 1), Complex.exp_ne_zero _⟩ :
        PuncturedComplex) :=
    γ₁.source.trans hbLift
  let shifted : C(unitInterval, ℂ) :=
    ⟨fun t ↦ L₀ 1 - Complex.log (b : ℂ) + L₁ t, by fun_prop⟩
  have hshifted :
      shifted = cov.liftPath γ₁ (L₀ 1) hγ₁liftStart := by
    apply (cov.eq_liftPath_iff'
      (γ := γ₁) (e := L₀ 1) (γ_0 := hγ₁liftStart)).mpr
    constructor
    · funext t
      apply Subtype.ext
      simp only [shifted, ContinuousMap.coe_mk, Function.comp_apply,
        Complex.exp_add, Complex.exp_sub]
      rw [show Complex.exp (L₀ 1) = (b : ℂ) by
          exact (exp_puncturedPathLogLift γ₀ 1).trans
            (congrArg Subtype.val γ₀.target),
        Complex.exp_log b.2, div_self b.2, one_mul]
      simpa [L₁] using exp_puncturedPathLogLift γ₁ t
    · simp [shifted, L₁]
  have ha :
      a =
        (⟨Complex.exp (Complex.log (a : ℂ)),
          Complex.exp_ne_zero _⟩ : PuncturedComplex) := by
    apply Subtype.ext
    exact (Complex.exp_log a.2).symm
  have htrans := cov.liftPath_trans ha γ₀ γ₁
  have hendpoint := DFunLike.congr_fun htrans (1 : unitInterval)
  simp at hendpoint
  change puncturedPathLogLift (γ₀.trans γ₁) 1 =
    cov.liftPath γ₁ (L₀ 1) hγ₁liftStart 1 at hendpoint
  rw [← hshifted] at hendpoint
  unfold puncturedPathLogIncrement
  rw [puncturedPathLogLift_zero,
    puncturedPathLogLift_zero, puncturedPathLogLift_zero,
    hendpoint]
  dsimp [shifted, L₀, L₁]
  ring

/--
%%handwave
name:
  Homotopy invariance of logarithmic path increments
statement:
  Endpoint-fixed homotopic paths $\gamma_0,\gamma_1$ in the punctured plane
  have equal logarithmic increments:
  $$
    \gamma_0\simeq\gamma_1
      \quad\Longrightarrow\quad
    \Delta\log(\gamma_0)=\Delta\log(\gamma_1).
  $$
proof:
  Homotopic lifts through the exponential covering that start at the same
  logarithm have equal endpoints. Their initial values also agree, so their
  endpoint increments are equal.
-/
theorem puncturedPathLogIncrement_eq_of_homotopic
    {a b : PuncturedComplex} {γ₀ γ₁ : Path a b}
    (h : Path.Homotopic γ₀ γ₁) :
    puncturedPathLogIncrement γ₀ =
      puncturedPathLogIncrement γ₁ := by
  have hstart₀ : γ₀ 0 =
      (⟨Complex.exp (Complex.log (a : ℂ)),
        Complex.exp_ne_zero _⟩ : PuncturedComplex) := by
    apply Subtype.ext
    exact (congrArg Subtype.val γ₀.source).trans
      (Complex.exp_log a.2).symm
  have hstart₁ : γ₁ 0 =
      (⟨Complex.exp (Complex.log (a : ℂ)),
        Complex.exp_ne_zero _⟩ : PuncturedComplex) := by
    apply Subtype.ext
    exact (congrArg Subtype.val γ₁.source).trans
      (Complex.exp_log a.2).symm
  have hend :=
    Complex.isCoveringMap_exp.liftPath_apply_one_eq_of_homotopicRel
      h (Complex.log (a : ℂ)) hstart₀ hstart₁
  unfold puncturedPathLogIncrement
  rw [puncturedPathLogLift_zero,
    puncturedPathLogLift_zero]
  exact congrArg (fun z : ℂ ↦ z - Complex.log (a : ℂ)) hend

/--
%%handwave
name:
  Pointwise product of punctured-plane paths
statement:
  If $\gamma$ is a path from $a$ to $b$ and $\delta$ is a path from $c$ to
  $d$ in $\mathbb C\setminus\{0\}$, their pointwise product is the path
  $$
    (\gamma\delta)(t)=\gamma(t)\delta(t)
  $$
  from $ac$ to $bd$ in $\mathbb C\setminus\{0\}$.
-/
def puncturedPathPointwiseMul
    {a b c d : PuncturedComplex}
    (γ : Path a b) (δ : Path c d) :
    Path (⟨(a : ℂ) * (c : ℂ), mul_ne_zero a.2 c.2⟩ :
      PuncturedComplex)
      (⟨(b : ℂ) * (d : ℂ), mul_ne_zero b.2 d.2⟩ :
        PuncturedComplex) :=
  Path.mk
    (⟨fun t ↦
      (⟨(γ t : ℂ) * (δ t : ℂ),
        mul_ne_zero (γ t).2 (δ t).2⟩ : PuncturedComplex),
      by fun_prop⟩ : C(unitInterval, PuncturedComplex))
    (by
      apply Subtype.ext
      change (γ 0 : ℂ) * (δ 0 : ℂ) = (a : ℂ) * (c : ℂ)
      rw [congrArg Subtype.val γ.source,
        congrArg Subtype.val δ.source])
    (by
      apply Subtype.ext
      change (γ 1 : ℂ) * (δ 1 : ℂ) = (b : ℂ) * (d : ℂ)
      rw [congrArg Subtype.val γ.target,
        congrArg Subtype.val δ.target])

/--
%%handwave
name:
  Logarithmic increment of a pointwise product
statement:
  For paths $\gamma,\delta$ in $\mathbb C\setminus\{0\}$,
  $$
    \Delta\log(\gamma\delta)
      =\Delta\log(\gamma)+\Delta\log(\delta).
  $$
proof:
  The sum of logarithmic lifts, translated to start at the principal
  logarithm of the product of the initial values, is a logarithmic lift of
  the pointwise product. Its endpoint difference is the sum of the two
  endpoint differences.
-/
theorem puncturedPathLogIncrement_pointwiseMul
    {a b c d : PuncturedComplex}
    (γ : Path a b) (δ : Path c d) :
    puncturedPathLogIncrement
        (puncturedPathPointwiseMul γ δ) =
      puncturedPathLogIncrement γ +
        puncturedPathLogIncrement δ := by
  let η := puncturedPathPointwiseMul γ δ
  let e : ℂ := Complex.log ((a : ℂ) * (c : ℂ))
  have hη0 : η 0 =
      (⟨Complex.exp e, Complex.exp_ne_zero _⟩ :
        PuncturedComplex) := by
    apply Subtype.ext
    simp [η, puncturedPathPointwiseMul, e,
      Complex.exp_log (mul_ne_zero a.2 c.2)]
  let Lγ := puncturedPathLogLift γ
  let Lδ := puncturedPathLogLift δ
  let M : C(unitInterval, ℂ) :=
    ⟨fun t ↦ e - Complex.log (a : ℂ) -
        Complex.log (c : ℂ) + Lγ t + Lδ t, by
      fun_prop⟩
  have hM :
      M = Complex.isCoveringMap_exp.liftPath η e hη0 := by
    apply (Complex.isCoveringMap_exp.eq_liftPath_iff'
      (γ := η) (e := e) (γ_0 := hη0)).mpr
    constructor
    · funext t
      apply Subtype.ext
      change Complex.exp
        (e - Complex.log (a : ℂ) -
          Complex.log (c : ℂ) + Lγ t + Lδ t) =
        (γ t : ℂ) * (δ t : ℂ)
      rw [Complex.exp_add, Complex.exp_add,
        Complex.exp_sub, Complex.exp_sub,
        show Complex.exp e = (a : ℂ) * (c : ℂ) by
          exact Complex.exp_log (mul_ne_zero a.2 c.2),
        Complex.exp_log a.2, Complex.exp_log c.2,
        exp_puncturedPathLogLift γ t,
        exp_puncturedPathLogLift δ t]
      field_simp [a.2, c.2]
    · simp only [M, ContinuousMap.coe_mk, Lγ, Lδ,
        puncturedPathLogLift_zero]
      ring
  unfold puncturedPathLogIncrement
  change
    Complex.isCoveringMap_exp.liftPath η e hη0 1 -
        Complex.isCoveringMap_exp.liftPath η e hη0 0 =
      (Lγ 1 - Lγ 0) + (Lδ 1 - Lδ 0)
  rw [← hM]
  dsimp [M]
  ring

/--
%%handwave
name:
  Integer power of a punctured-plane path
statement:
  If $\gamma$ is a path from $a$ to $b$ in
  $\mathbb C\setminus\{0\}$ and $n\in\mathbb Z$, then
  $$
    t\longmapsto\gamma(t)^n
  $$
  is a path from $a^n$ to $b^n$ in the punctured plane.
-/
noncomputable def puncturedPathZPow
    {a b : PuncturedComplex} (γ : Path a b) (n : ℤ) :
    Path (⟨(a : ℂ) ^ n, zpow_ne_zero n a.2⟩ :
      PuncturedComplex)
      (⟨(b : ℂ) ^ n, zpow_ne_zero n b.2⟩ :
        PuncturedComplex) :=
  Path.mk
    (⟨fun t ↦
      (⟨(γ t : ℂ) ^ n, zpow_ne_zero n (γ t).2⟩ :
        PuncturedComplex),
      Continuous.subtype_mk
        ((continuous_subtype_val.comp γ.continuous).zpow₀ n
          (fun t ↦ Or.inl (γ t).2)) _⟩ :
      C(unitInterval, PuncturedComplex))
    (by
      apply Subtype.ext
      change (γ 0 : ℂ) ^ n = (a : ℂ) ^ n
      rw [congrArg Subtype.val γ.source])
    (by
      apply Subtype.ext
      change (γ 1 : ℂ) ^ n = (b : ℂ) ^ n
      rw [congrArg Subtype.val γ.target])

/--
%%handwave
name:
  Logarithmic increment of an integer power
statement:
  For a path $\gamma$ in $\mathbb C\setminus\{0\}$ and
  $n\in\mathbb Z$,
  $$
    \Delta\log(\gamma^n)=n\,\Delta\log(\gamma).
  $$
proof:
  Multiply a logarithmic lift by $n$ and translate it to start at the
  principal logarithm of the powered initial value. Exponentiation shows
  that this is a lift of $\gamma^n$, and taking its endpoint difference
  gives the formula.
-/
theorem puncturedPathLogIncrement_zpow
    {a b : PuncturedComplex} (γ : Path a b) (n : ℤ) :
    puncturedPathLogIncrement (puncturedPathZPow γ n) =
      (n : ℂ) * puncturedPathLogIncrement γ := by
  let η := puncturedPathZPow γ n
  let e : ℂ := Complex.log ((a : ℂ) ^ n)
  have hη0 : η 0 =
      (⟨Complex.exp e, Complex.exp_ne_zero _⟩ :
        PuncturedComplex) := by
    apply Subtype.ext
    simp [η, puncturedPathZPow, e,
      Complex.exp_log (zpow_ne_zero n a.2)]
  let L := puncturedPathLogLift γ
  let M : C(unitInterval, ℂ) :=
    ⟨fun t ↦ e - (n : ℂ) * Complex.log (a : ℂ) +
        (n : ℂ) * L t, by
      fun_prop⟩
  have hM :
      M = Complex.isCoveringMap_exp.liftPath η e hη0 := by
    apply (Complex.isCoveringMap_exp.eq_liftPath_iff'
      (γ := η) (e := e) (γ_0 := hη0)).mpr
    constructor
    · funext t
      apply Subtype.ext
      change Complex.exp
        (e - (n : ℂ) * Complex.log (a : ℂ) +
          (n : ℂ) * L t) = (γ t : ℂ) ^ n
      rw [Complex.exp_add, Complex.exp_sub,
        show Complex.exp e = (a : ℂ) ^ n by
          exact Complex.exp_log (zpow_ne_zero n a.2),
        Complex.exp_int_mul, Complex.exp_int_mul,
        Complex.exp_log a.2,
        exp_puncturedPathLogLift γ t]
      field_simp [zpow_ne_zero n a.2]
    · simp only [M, ContinuousMap.coe_mk, L,
        puncturedPathLogLift_zero]
      ring
  unfold puncturedPathLogIncrement
  change
    Complex.isCoveringMap_exp.liftPath η e hη0 1 -
        Complex.isCoveringMap_exp.liftPath η e hη0 0 =
      (n : ℂ) * (L 1 - L 0)
  rw [← hM]
  dsimp [M]
  ring

/--
%%handwave
name:
  Finite pointwise product of punctured-plane loops
statement:
  Let $S$ be finite and, for each $i\in S$, let $\gamma_i$ be a closed path
  in $\mathbb C\setminus\{0\}$ based at $a_i$. Their pointwise product is
  the closed path
  $$
    t\longmapsto\prod_{i\in S}\gamma_i(t)
  $$
  based at $\prod_{i\in S}a_i$.
-/
noncomputable def puncturedPathFinsetProd
    {ι : Type*} (s : Finset ι)
    (a : ι → PuncturedComplex)
    (γ : ∀ i, Path (a i) (a i)) :
    Path
      (⟨∏ i ∈ s, (a i : ℂ),
        Finset.prod_ne_zero_iff.mpr
          (fun i _hi ↦ (a i).2)⟩ : PuncturedComplex)
      (⟨∏ i ∈ s, (a i : ℂ),
        Finset.prod_ne_zero_iff.mpr
          (fun i _hi ↦ (a i).2)⟩ : PuncturedComplex) :=
  Path.mk
    (⟨fun t ↦
      (⟨∏ i ∈ s, (γ i t : ℂ),
        Finset.prod_ne_zero_iff.mpr
          (fun i _hi ↦ (γ i t).2)⟩ : PuncturedComplex),
      Continuous.subtype_mk
        (continuous_finsetProd _ fun i _hi ↦
          continuous_subtype_val.comp
            (γ i).continuous) _⟩ :
      C(unitInterval, PuncturedComplex))
    (by
      apply Subtype.ext
      apply Finset.prod_congr rfl
      intro i _hi
      exact congrArg Subtype.val (γ i).source)
    (by
      apply Subtype.ext
      apply Finset.prod_congr rfl
      intro i _hi
      exact congrArg Subtype.val (γ i).target)

/--
%%handwave
name:
  Logarithmic increment of a finite pointwise product
statement:
  For a finite family of closed paths $\gamma_i$ in
  $\mathbb C\setminus\{0\}$,
  $$
    \Delta\log\left(\prod_{i\in S}\gamma_i\right)
      =\sum_{i\in S}\Delta\log(\gamma_i).
  $$
proof:
  The sum of the logarithmic lifts, translated to begin at the principal
  logarithm of the product of the base points, is a logarithmic lift of the
  pointwise product. Taking endpoint differences turns its two finite sums
  into the displayed sum.
-/
theorem puncturedPathLogIncrement_finsetProd
    {ι : Type*} (s : Finset ι)
    (a : ι → PuncturedComplex)
    (γ : ∀ i, Path (a i) (a i)) :
    puncturedPathLogIncrement
        (puncturedPathFinsetProd s a γ) =
      ∑ i ∈ s, puncturedPathLogIncrement (γ i) := by
  let A : ℂ := ∏ i ∈ s, (a i : ℂ)
  have hA : A ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr
      (fun i _hi ↦ (a i).2)
  let η := puncturedPathFinsetProd s a γ
  let e : ℂ := Complex.log A
  have hη0 : η 0 =
      (⟨Complex.exp e, Complex.exp_ne_zero _⟩ :
        PuncturedComplex) := by
    apply Subtype.ext
    simp [η, puncturedPathFinsetProd, e, A,
      Complex.exp_log hA]
  let L : ι → C(unitInterval, ℂ) :=
    fun i ↦ puncturedPathLogLift (γ i)
  let M : C(unitInterval, ℂ) :=
    ⟨fun t ↦ e -
        ∑ i ∈ s, Complex.log (a i : ℂ) +
        ∑ i ∈ s, L i t, by
      fun_prop⟩
  have hM :
      M = Complex.isCoveringMap_exp.liftPath η e hη0 := by
    apply (Complex.isCoveringMap_exp.eq_liftPath_iff'
      (γ := η) (e := e) (γ_0 := hη0)).mpr
    constructor
    · funext t
      apply Subtype.ext
      change Complex.exp
        (e - (∑ i ∈ s, Complex.log (a i : ℂ)) +
          ∑ i ∈ s, L i t) =
        ∏ i ∈ s, (γ i t : ℂ)
      rw [Complex.exp_add, Complex.exp_sub,
        show Complex.exp e = A by
          exact Complex.exp_log hA,
        Complex.exp_sum, Complex.exp_sum]
      simp_rw [Complex.exp_log (a _).2]
      simp_rw [show ∀ i,
          Complex.exp (L i t) = (γ i t : ℂ) by
        intro i
        exact exp_puncturedPathLogLift (γ i) t]
      change (A / A) *
          (∏ i ∈ s, (γ i t : ℂ)) =
        ∏ i ∈ s, (γ i t : ℂ)
      rw [div_self hA, one_mul]
    · simp only [M, ContinuousMap.coe_mk, L,
        puncturedPathLogLift_zero]
      ring
  unfold puncturedPathLogIncrement
  change
    Complex.isCoveringMap_exp.liftPath η e hη0 1 -
        Complex.isCoveringMap_exp.liftPath η e hη0 0 =
      ∑ i ∈ s, (L i 1 - L i 0)
  rw [← hM]
  dsimp [M]
  rw [Finset.sum_sub_distrib]
  ring

/--
%%handwave
name:
  Closed logarithmic lift on the additive circle
statement:
  Let $\gamma:[0,1]\to\mathbb C\setminus\{0\}$ be a closed path with
  $\Delta\log(\gamma)=0$. Its logarithmic lift has equal endpoint values and
  therefore descends to a continuous function
  $$
    \ell_\gamma:\mathbb R/\mathbb Z\to\mathbb C.
  $$
-/
noncomputable def closedPuncturedPathLogOnAddCircle
    {a : PuncturedComplex} (γ : Path a a)
    (hzero : puncturedPathLogIncrement γ = 0) :
    C(AddCircle (1 : ℝ), ℂ) := by
  let L := puncturedPathLogLift γ
  let f : ℝ → ℂ := fun t ↦ L (Set.projIcc 0 1 zero_le_one t)
  have hf0 : f 0 = f 1 := by
    have hL : L 1 - L 0 = 0 := hzero
    have : L 1 = L 0 := sub_eq_zero.mp hL
    simpa [f] using this.symm
  exact ⟨AddCircle.liftIco 1 0 f,
    AddCircle.liftIco_zero_continuous hf0
      ((L.continuous.comp continuous_projIcc).continuousOn)⟩

/--
%%handwave
name:
  Values of the descended logarithm
statement:
  If $\gamma$ is a closed path in $\mathbb C\setminus\{0\}$ with
  $\Delta\log(\gamma)=0$, then its descended logarithm on
  $\mathbb R/\mathbb Z$ satisfies
  $$
    \ell_\gamma([t])=L_\gamma(t)
    \qquad (0\leq t\leq 1).
  $$
proof:
  On $[0,1)$ this is the defining property of the quotient lift. At $t=1$,
  identify $[1]=[0]$ and use $L_\gamma(1)=L_\gamma(0)$.
-/
theorem closedPuncturedPathLogOnAddCircle_coe
    {a : PuncturedComplex} (γ : Path a a)
    (hzero : puncturedPathLogIncrement γ = 0)
    (t : unitInterval) :
    closedPuncturedPathLogOnAddCircle γ hzero
        (t : AddCircle (1 : ℝ)) =
      puncturedPathLogLift γ t := by
  by_cases ht : (t : ℝ) < 1
  · change AddCircle.liftIco 1 0
        (fun s : ℝ ↦ puncturedPathLogLift γ
          (Set.projIcc 0 1 zero_le_one s))
        ((t : ℝ) : AddCircle (1 : ℝ)) =
      puncturedPathLogLift γ t
    rw [AddCircle.liftIco_zero_coe_apply ⟨t.2.1, ht⟩,
      Set.projIcc_val]
  · have ht1 : t = 1 := by
      apply Subtype.ext
      exact le_antisymm t.2.2 (not_lt.mp ht)
    have hL :
        puncturedPathLogLift γ 1 =
          puncturedPathLogLift γ 0 := by
      exact sub_eq_zero.mp hzero
    rw [ht1, hL]
    change closedPuncturedPathLogOnAddCircle γ hzero
      ((1 : ℝ) : AddCircle (1 : ℝ)) =
        puncturedPathLogLift γ 0
    rw [show ((1 : ℝ) : AddCircle (1 : ℝ)) = 0 by simp]
    change AddCircle.liftIco 1 0
        (fun s : ℝ ↦ puncturedPathLogLift γ
          (Set.projIcc 0 1 zero_le_one s))
        (0 : AddCircle (1 : ℝ)) =
      puncturedPathLogLift γ 0
    rw [← show ((0 : ℝ) : AddCircle (1 : ℝ)) = 0 by simp,
      AddCircle.liftIco_zero_coe_apply
        (show (0 : ℝ) ∈ Set.Ico 0 1 by simp),
      Set.projIcc_left]
    congr

/--
%%handwave
name:
  Closed logarithmic lift on the unit circle
statement:
  Let $\gamma:[0,1]\to\mathbb C\setminus\{0\}$ be closed and satisfy
  $\Delta\log(\gamma)=0$. Under the standard homeomorphism
  $\mathbb R/\mathbb Z\simeq S^1$, its descended logarithm defines a
  continuous function $\ell_\gamma:S^1\to\mathbb C$.
-/
noncomputable def closedPuncturedPathLogOnCircle
    {a : PuncturedComplex} (γ : Path a a)
    (hzero : puncturedPathLogIncrement γ = 0) :
    C(Circle, ℂ) :=
  (closedPuncturedPathLogOnAddCircle γ hzero).comp
    (AddCircle.homeomorphCircle
      (T := (1 : ℝ)) one_ne_zero).symm

/--
%%handwave
name:
  Unit-circle logarithm in angular coordinates
statement:
  If $\gamma$ is a closed punctured-plane path with zero logarithmic
  increment, then its logarithm on the unit circle satisfies
  $$
    \ell_\gamma(e^{2\pi i t})=L_\gamma(t)
    \qquad (0\leq t\leq 1).
  $$
proof:
  The standard homeomorphism
  $\mathbb R/\mathbb Z\simeq S^1$ sends $[t]$ to $e^{2\pi i t}$, so the
  conclusion follows from the value formula for the descended logarithm.
-/
theorem closedPuncturedPathLogOnCircle_param
    {a : PuncturedComplex} (γ : Path a a)
    (hzero : puncturedPathLogIncrement γ = 0)
    (t : unitInterval) :
    closedPuncturedPathLogOnCircle γ hzero
        (Circle.exp (2 * Real.pi * (t : ℝ))) =
      puncturedPathLogLift γ t := by
  rw [closedPuncturedPathLogOnCircle]
  change closedPuncturedPathLogOnAddCircle γ hzero
    ((AddCircle.homeomorphCircle
      (T := (1 : ℝ)) one_ne_zero).symm
      (Circle.exp (2 * Real.pi * (t : ℝ)))) = _
  rw [← closedPuncturedPathLogOnAddCircle_coe γ hzero t]
  congr 1
  apply (AddCircle.homeomorphCircle
    (T := (1 : ℝ)) one_ne_zero).injective
  rw [Homeomorph.apply_symm_apply,
    AddCircle.homeomorphCircle_apply]
  apply Subtype.ext
  rw [AddCircle.toCircle_apply_mk, Circle.coe_exp]
  simp

/--
%%handwave
name:
  Filling a zero-winding punctured-plane loop
statement:
  Let $\gamma:[0,1]\to\mathbb C\setminus\{0\}$ be a closed path. If
  $\Delta\log(\gamma)=0$, then there is a continuous nowhere-zero map
  $F:\mathbb C\to\mathbb C\setminus\{0\}$ such that
  $$
    F(e^{2\pi i t})=\gamma(t)
    \qquad (0\leq t\leq 1).
  $$
proof:
  The closed logarithmic lift defines a continuous logarithm on the unit
  circle. Extend this complex-valued logarithm to the plane by the Tietze
  extension theorem and exponentiate the extension.
-/
theorem exists_punctured_extension_of_logIncrement_eq_zero
    {a : PuncturedComplex} (γ : Path a a)
    (hzero : puncturedPathLogIncrement γ = 0) :
    ∃ F : C(ℂ, PuncturedComplex),
      ∀ t : unitInterval,
        F (Complex.exp
          (((2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I)) =
          γ t := by
  obtain ⟨G, hG⟩ :=
    (closedPuncturedPathLogOnCircle γ hzero).exists_extension
      Metric.isClosed_sphere.isClosedEmbedding_subtypeVal
  let F : C(ℂ, PuncturedComplex) :=
    ⟨fun q ↦ ⟨Complex.exp (G q), Complex.exp_ne_zero _⟩, by
      fun_prop⟩
  refine ⟨F, ?_⟩
  intro t
  let u : Circle := Circle.exp (2 * Real.pi * (t : ℝ))
  have hu :
      (u : ℂ) =
        Complex.exp
          (((2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I) := by
    simp [u, Circle.coe_exp]
  apply Subtype.ext
  change Complex.exp (G _) = (γ t : ℂ)
  rw [← hu, ← exp_puncturedPathLogLift γ t]
  congr 1
  have hGfun := DFunLike.congr_fun hG u
  change G _ = closedPuncturedPathLogOnCircle γ hzero _ at hGfun
  rw [closedPuncturedPathLogOnCircle_param] at hGfun
  exact hGfun

/--
%%handwave
name:
  Horizontal path across a punctured-plane square
statement:
  For a continuous map
  $H:[0,1]^2\to\mathbb C\setminus\{0\}$ and $y\in[0,1]$, the horizontal
  path at height $y$ is $t\mapsto H(t,y)$.
-/
def puncturedSquareHorizontalPath
    (H : C(unitInterval × unitInterval, PuncturedComplex))
    (y : unitInterval) :
    Path (H (0, y)) (H (1, y)) :=
  Path.mk ⟨fun t ↦ H (t, y), by fun_prop⟩ rfl rfl

/--
%%handwave
name:
  Vertical path across a punctured-plane square
statement:
  For a continuous map
  $H:[0,1]^2\to\mathbb C\setminus\{0\}$ and $x\in[0,1]$, the vertical
  path at horizontal coordinate $x$ is $t\mapsto H(x,t)$.
-/
def puncturedSquareVerticalPath
    (H : C(unitInterval × unitInterval, PuncturedComplex))
    (x : unitInterval) :
    Path (H (x, 0)) (H (x, 1)) :=
  Path.mk ⟨fun t ↦ H (x, t), by fun_prop⟩ rfl rfl

/--
%%handwave
name:
  Logarithmic increments cancel around a square
statement:
  For a continuous map
  $H:[0,1]^2\to\mathbb C\setminus\{0\}$, let $B,R,T,L$ be its bottom,
  right, top, and left side paths, each parameterized in the increasing
  coordinate direction. Then
  $$
    \Delta\log(B)+\Delta\log(R)
      =\Delta\log(L)+\Delta\log(T).
  $$
proof:
  The bottom-then-right and left-then-top routes have the same endpoints and
  are homotopic by pointwise convex interpolation of their parameter-square
  paths. Apply homotopy invariance and additivity of logarithmic increments.
-/
theorem puncturedPathLogIncrement_square_boundary
    (H : C(unitInterval × unitInterval, PuncturedComplex)) :
    puncturedPathLogIncrement (puncturedSquareHorizontalPath H 0) +
        puncturedPathLogIncrement (puncturedSquareVerticalPath H 1) =
      puncturedPathLogIncrement (puncturedSquareVerticalPath H 0) +
        puncturedPathLogIncrement (puncturedSquareHorizontalPath H 1) := by
  let idPath : Path (0 : unitInterval) 1 :=
    Path.mk ⟨id, continuous_id⟩ rfl rfl
  let bottomParam :
      Path ((0, 0) : unitInterval × unitInterval) (1, 0) :=
    idPath.prod (Path.refl 0)
  let rightParam :
      Path ((1, 0) : unitInterval × unitInterval) (1, 1) :=
    (Path.refl 1).prod idPath
  let leftParam :
      Path ((0, 0) : unitInterval × unitInterval) (0, 1) :=
    (Path.refl 0).prod idPath
  let topParam :
      Path ((0, 1) : unitInterval × unitInterval) (1, 1) :=
    idPath.prod (Path.refl 1)
  let bottomRight := bottomParam.trans rightParam
  let leftTop := leftParam.trans topParam
  let K : Path.Homotopy bottomRight leftTop :=
    { toFun := fun st ↦
        (Set.Icc.convexComb
            (bottomRight st.2).1 (leftTop st.2).1 st.1,
          Set.Icc.convexComb
            (bottomRight st.2).2 (leftTop st.2).2 st.1)
      continuous_toFun := by
        fun_prop
      map_zero_left := by
        intro t
        simp
      map_one_left := by
        intro t
        simp
      prop' := by
        intro s t ht
        rcases ht with rfl | rfl
        · simp
        · simp }
  have hroute :
      Path.Homotopic
        ((puncturedSquareHorizontalPath H 0).trans
          (puncturedSquareVerticalPath H 1))
        ((puncturedSquareVerticalPath H 0).trans
          (puncturedSquareHorizontalPath H 1)) := by
    have hmapped := K.map H
    refine ⟨hmapped.cast ?_ ?_⟩
    · rw [Path.map_trans]
      rfl
    · rw [Path.map_trans]
      rfl
  rw [← puncturedPathLogIncrement_trans,
    ← puncturedPathLogIncrement_trans]
  exact puncturedPathLogIncrement_eq_of_homotopic hroute

/--
%%handwave
name:
  Logarithmic lift of a based punctured-plane loop
statement:
  Every loop $\gamma$ in $\mathbb C\setminus\{0\}$ based at $1$ has a unique
  continuous lift $L_\gamma:[0,1]\to\mathbb C$ satisfying
  $$
    L_\gamma(0)=0,
    \qquad e^{L_\gamma(t)}=\gamma(t).
  $$
-/
noncomputable def puncturedLoopLogLift
    (γ : Path (⟨1, one_ne_zero⟩ : PuncturedComplex)
      ⟨1, one_ne_zero⟩) : C(unitInterval, ℂ) :=
  Complex.isCoveringMap_exp.liftPath γ 0 (by simp)

/--
%%handwave
name:
  Exponential of the logarithmic loop lift
statement:
  If $L_\gamma$ is the logarithmic lift of a based loop $\gamma$ in the
  punctured plane, then $e^{L_\gamma(t)}=\gamma(t)$ for every $t$.
proof:
  This is the defining lifting identity for the exponential covering.
-/
theorem exp_puncturedLoopLogLift
    (γ : Path (⟨1, one_ne_zero⟩ : PuncturedComplex)
      ⟨1, one_ne_zero⟩) (t : unitInterval) :
    Complex.exp (puncturedLoopLogLift γ t) = γ t := by
  have h := congr_fun
    (Complex.isCoveringMap_exp.liftPath_lifts γ 0 (by simp)) t
  exact congrArg Subtype.val h

/--
%%handwave
name:
  Logarithmic loop lift starts at zero
statement:
  The logarithmic lift $L_\gamma$ normalized above satisfies
  $L_\gamma(0)=0$.
proof:
  This is the prescribed initial value in path lifting.
-/
@[simp]
theorem puncturedLoopLogLift_zero
    (γ : Path (⟨1, one_ne_zero⟩ : PuncturedComplex)
      ⟨1, one_ne_zero⟩) :
    puncturedLoopLogLift γ 0 = 0 :=
  Complex.isCoveringMap_exp.liftPath_zero γ 0 (by simp)

/--
%%handwave
name:
  Endpoint of a logarithmic loop lift exponentiates to one
statement:
  The endpoint of the logarithmic lift of a loop based at $1$ satisfies
  $e^{L_\gamma(1)}=1$.
proof:
  Apply the lifting identity at the closing endpoint of the loop.
-/
theorem exp_puncturedLoopLogLift_one
    (γ : Path (⟨1, one_ne_zero⟩ : PuncturedComplex)
      ⟨1, one_ne_zero⟩) :
    Complex.exp (puncturedLoopLogLift γ 1) = 1 := by
  simpa using exp_puncturedLoopLogLift γ 1

/--
%%handwave
name:
  Integer winding number of a based punctured-plane loop
statement:
  The winding number of a loop $\gamma$ in
  $\mathbb C\setminus\{0\}$ based at $1$ is the integer $n$ determined by
  $$
    L_\gamma(1)=2\pi i n,
  $$
  where $L_\gamma$ is its logarithmic lift starting at zero.
-/
noncomputable def puncturedLoopWindingNumber
    (γ : Path (⟨1, one_ne_zero⟩ : PuncturedComplex)
      ⟨1, one_ne_zero⟩) : ℤ :=
  Classical.choose
    (Complex.exp_eq_one_iff.mp (exp_puncturedLoopLogLift_one γ))

/--
%%handwave
name:
  Endpoint formula for winding number
statement:
  For every based loop $\gamma$ in the punctured plane,
  $$
    L_\gamma(1)=n(2\pi i),
  $$
  where $n$ is its integer winding number.
proof:
  This is the defining property of the integer selected from
  $e^{L_\gamma(1)}=1$.
-/
theorem puncturedLoopLogLift_one_eq_windingNumber_mul
    (γ : Path (⟨1, one_ne_zero⟩ : PuncturedComplex)
      ⟨1, one_ne_zero⟩) :
    puncturedLoopLogLift γ 1 =
      puncturedLoopWindingNumber γ * (2 * Real.pi * Complex.I) :=
  Classical.choose_spec
    (Complex.exp_eq_one_iff.mp (exp_puncturedLoopLogLift_one γ))

/--
%%handwave
name:
  Winding number of a constant punctured-plane loop
statement:
  The constant loop at $1$ in $\mathbb C\setminus\{0\}$ has winding number
  zero.
proof:
  Its logarithmic lift starting at zero is the constant path at zero.
  Comparing its endpoint with the winding-number endpoint formula and
  cancelling $2\pi i\ne0$ gives the result.
-/
@[simp]
theorem puncturedLoopWindingNumber_refl :
    puncturedLoopWindingNumber
      (Path.refl
        (⟨1, one_ne_zero⟩ : PuncturedComplex)) = 0 := by
  have hbase :
      (⟨1, one_ne_zero⟩ : PuncturedComplex) =
        (⟨Complex.exp 0, Complex.exp_ne_zero 0⟩ :
          PuncturedComplex) := by
    simp
  have hlift :=
    Complex.isCoveringMap_exp.liftPath_const
      (e := (0 : ℂ)) hbase
  have hone :
      puncturedLoopLogLift
          (Path.refl
            (⟨1, one_ne_zero⟩ : PuncturedComplex)) 1 =
        0 := by
    have h := DFunLike.congr_fun hlift (1 : unitInterval)
    simpa [puncturedLoopLogLift, Path.refl] using h
  have hmul :
      (puncturedLoopWindingNumber
          (Path.refl
            (⟨1, one_ne_zero⟩ : PuncturedComplex)) : ℂ) *
          (2 * Real.pi * Complex.I) = 0 := by
    rw [← puncturedLoopLogLift_one_eq_windingNumber_mul]
    exact hone
  have hcast :
      (puncturedLoopWindingNumber
        (Path.refl
          (⟨1, one_ne_zero⟩ : PuncturedComplex)) : ℂ) = 0 :=
    (mul_eq_zero.mp hmul).resolve_right
      Complex.two_pi_I_ne_zero
  exact_mod_cast hcast

/--
%%handwave
name:
  Normalization of a closed punctured-plane path
statement:
  If $\gamma$ is a closed path in $\mathbb C\setminus\{0\}$ based at $a$,
  then
  $$
    t\longmapsto\frac{\gamma(t)}{a}
  $$
  is a loop in the punctured plane based at $1$.
-/
noncomputable def normalizedPuncturedPathLoop
    {a : PuncturedComplex} (γ : Path a a) :
    Path (⟨1, one_ne_zero⟩ : PuncturedComplex)
      ⟨1, one_ne_zero⟩ := by
  let loop : unitInterval → PuncturedComplex := fun t ↦
    ⟨(γ t : ℂ) / (a : ℂ), div_ne_zero (γ t).2 a.2⟩
  refine Path.mk ⟨loop, ?_⟩ ?_ ?_
  · apply Continuous.subtype_mk
    exact continuous_subtype_val.comp γ.continuous |>.div_const _
  · apply Subtype.ext
    simp [loop, a.2]
  · apply Subtype.ext
    simp [loop, a.2]

/--
%%handwave
name:
  Logarithmic increment of a closed path is its winding period
statement:
  For a closed path $\gamma$ in $\mathbb C\setminus\{0\}$,
  $$
    \Delta\log(\gamma)
      =\operatorname{wind}(\gamma,0)\,2\pi i,
  $$
  where the winding number is computed after dividing $\gamma$ by its base
  point.
proof:
  Subtracting the principal logarithm of the base point from the logarithmic
  lift of $\gamma$ gives the lift of the normalized loop starting at zero.
  The result follows from the endpoint formula for winding number.
-/
theorem puncturedPathLogIncrement_eq_windingNumber_mul
    {a : PuncturedComplex} (γ : Path a a) :
    puncturedPathLogIncrement γ =
      puncturedLoopWindingNumber (normalizedPuncturedPathLoop γ) *
        (2 * Real.pi * Complex.I) := by
  let L : C(unitInterval, ℂ) := puncturedPathLogLift γ
  let shifted : C(unitInterval, ℂ) :=
    ⟨fun t ↦ L t - Complex.log (a : ℂ), by fun_prop⟩
  have hshifted :
      shifted =
        puncturedLoopLogLift (normalizedPuncturedPathLoop γ) := by
    unfold puncturedLoopLogLift
    apply (Complex.isCoveringMap_exp.eq_liftPath_iff'
      (γ := normalizedPuncturedPathLoop γ) (e := 0)
        (γ_0 := by simp)).mpr
    constructor
    · funext t
      apply Subtype.ext
      simp only [shifted, ContinuousMap.coe_mk, Function.comp_apply,
        Complex.exp_sub, Complex.exp_log a.2]
      change Complex.exp (L t) / (a : ℂ) = (γ t : ℂ) / (a : ℂ)
      rw [show Complex.exp (L t) = (γ t : ℂ) by
        exact exp_puncturedPathLogLift γ t]
    · simp [shifted, L]
  rw [← puncturedLoopLogLift_one_eq_windingNumber_mul]
  rw [← hshifted]
  unfold puncturedPathLogIncrement
  simp only [shifted, ContinuousMap.coe_mk]
  rw [puncturedPathLogLift_zero]

/--
%%handwave
name:
  Winding number is invariant under based homotopy
statement:
  If two loops in $\mathbb C\setminus\{0\}$ based at $1$ are homotopic while
  keeping their base point fixed, then they have the same integer winding
  number.
proof:
  Lifts through the exponential covering that begin at the same point have
  equal endpoints under a based homotopy. Comparing the two endpoint formulas
  and cancelling $2\pi i\ne0$ identifies the winding numbers.
-/
theorem puncturedLoopWindingNumber_eq_of_homotopic
    {γ₀ γ₁ : Path (⟨1, one_ne_zero⟩ : PuncturedComplex)
      ⟨1, one_ne_zero⟩} (h : Path.Homotopic γ₀ γ₁) :
    puncturedLoopWindingNumber γ₀ = puncturedLoopWindingNumber γ₁ := by
  have hlift : puncturedLoopLogLift γ₀ 1 = puncturedLoopLogLift γ₁ 1 :=
    Complex.isCoveringMap_exp.liftPath_apply_one_eq_of_homotopicRel
      h 0 (by simp) (by simp)
  have hmul :
      (puncturedLoopWindingNumber γ₀ : ℂ) *
          (2 * Real.pi * Complex.I) =
        (puncturedLoopWindingNumber γ₁ : ℂ) *
          (2 * Real.pi * Complex.I) := by
    rw [← puncturedLoopLogLift_one_eq_windingNumber_mul,
      ← puncturedLoopLogLift_one_eq_windingNumber_mul]
    exact hlift
  have hcast :
      (puncturedLoopWindingNumber γ₀ : ℂ) =
        (puncturedLoopWindingNumber γ₁ : ℂ) :=
    mul_right_cancel₀ Complex.two_pi_I_ne_zero hmul
  exact_mod_cast hcast

/--
%%handwave
name:
  Equal winding numbers give a based homotopy
statement:
  Two loops in $\mathbb C\setminus\{0\}$ based at $1$ with the same integer
  winding number are homotopic through loops based at $1$.
proof:
  Their logarithmic lifts begin at zero and, by the endpoint formula, end at
  the same integral multiple of $2\pi i$. Linearly interpolate the two lifts
  while keeping both endpoints fixed, then exponentiate the interpolation.
-/
theorem puncturedLoop_homotopic_of_windingNumber_eq
    {γ₀ γ₁ : Path (⟨1, one_ne_zero⟩ : PuncturedComplex)
      ⟨1, one_ne_zero⟩}
    (hwind : puncturedLoopWindingNumber γ₀ =
      puncturedLoopWindingNumber γ₁) :
    Path.Homotopic γ₀ γ₁ := by
  let L₀ : C(unitInterval, ℂ) := puncturedLoopLogLift γ₀
  let L₁ : C(unitInterval, ℂ) := puncturedLoopLogLift γ₁
  have hend : L₀ 1 = L₁ 1 := by
    dsimp [L₀, L₁]
    rw [puncturedLoopLogLift_one_eq_windingNumber_mul,
      puncturedLoopLogLift_one_eq_windingNumber_mul, hwind]
  let H : C(unitInterval × unitInterval, PuncturedComplex) :=
    ⟨fun x ↦
      ⟨Complex.exp
        (L₀ x.2 + (x.1 : ℝ) • (L₁ x.2 - L₀ x.2)),
        Complex.exp_ne_zero _⟩, by
      apply Continuous.subtype_mk
      fun_prop⟩
  refine ⟨{
    toFun := H
    continuous_toFun := H.continuous
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro t
    apply Subtype.ext
    simpa [H, L₀] using exp_puncturedLoopLogLift γ₀ t
  · intro t
    apply Subtype.ext
    simpa [H, L₁] using exp_puncturedLoopLogLift γ₁ t
  · intro s t ht
    apply Subtype.ext
    rcases ht with rfl | rfl
    · simp [H, L₀, L₁]
    · simp only [H, ContinuousMap.coe_mk, Subtype.coe_mk]
      rw [hend]
      simp only [sub_self, smul_zero, add_zero]
      simpa [L₁] using exp_puncturedLoopLogLift_one γ₁

/--
%%handwave
name:
  Positive unit-circle loop
statement:
  The positive unit-circle loop in $\mathbb C\setminus\{0\}$ is
  $t\mapsto e^{2\pi i t}$, based at $1$.
-/
def positiveCircleLoop :
    Path (⟨1, one_ne_zero⟩ : PuncturedComplex) ⟨1, one_ne_zero⟩ :=
  Path.mk
    ⟨fun t ↦ ⟨Complex.exp ((2 * Real.pi * (t : ℝ)) * Complex.I),
        Complex.exp_ne_zero _⟩, by
          apply Continuous.subtype_mk
          exact Complex.continuous_exp.comp (by fun_prop)⟩
    (by simp)
    (by
      apply Subtype.ext
      change Complex.exp ((2 : ℂ) * Real.pi * (1 : ℝ) * Complex.I) = 1
      rw [show (2 : ℂ) * Real.pi * (1 : ℝ) * Complex.I =
          (2 * Real.pi : ℝ) * Complex.I by norm_num]
      simp [Complex.exp_mul_I])

/--
%%handwave
name:
  Winding number of the positive unit circle
statement:
  The loop $t\mapsto e^{2\pi i t}$ has winding number $1$ around the origin.
proof:
  Its logarithmic lift starting at zero is explicitly
  $L(t)=2\pi i t$, whose endpoint is $2\pi i$.
-/
@[simp]
theorem puncturedLoopWindingNumber_positiveCircleLoop :
    puncturedLoopWindingNumber positiveCircleLoop = 1 := by
  let L : C(unitInterval, ℂ) :=
    ⟨fun t ↦ (2 * Real.pi * (t : ℝ)) * Complex.I, by fun_prop⟩
  have hL : L = puncturedLoopLogLift positiveCircleLoop := by
    apply (Complex.isCoveringMap_exp.eq_liftPath_iff'
      (γ := positiveCircleLoop) (e := 0) (γ_0 := by simp)).mpr
    constructor
    · funext t
      apply Subtype.ext
      rfl
    · simp [L]
  have hendpoint :
      puncturedLoopLogLift positiveCircleLoop 1 =
        2 * Real.pi * Complex.I := by
    rw [← hL]
    simp [L]
  have hmul :
      (puncturedLoopWindingNumber positiveCircleLoop : ℂ) *
          (2 * Real.pi * Complex.I) =
        (1 : ℂ) * (2 * Real.pi * Complex.I) := by
    rw [← puncturedLoopLogLift_one_eq_windingNumber_mul, hendpoint]
    simp
  have hcast :
      (puncturedLoopWindingNumber positiveCircleLoop : ℂ) = (1 : ℂ) :=
    mul_right_cancel₀ Complex.two_pi_I_ne_zero hmul
  exact_mod_cast hcast

/--
%%handwave
name:
  Negative unit-circle loop
statement:
  The negative unit-circle loop in $\mathbb C\setminus\{0\}$ is
  $t\mapsto e^{-2\pi i t}$, based at $1$.
-/
def negativeCircleLoop :
    Path (⟨1, one_ne_zero⟩ : PuncturedComplex) ⟨1, one_ne_zero⟩ :=
  Path.mk
    ⟨fun t ↦
      ⟨Complex.exp ((-(2 * Real.pi * (t : ℝ))) * Complex.I),
        Complex.exp_ne_zero _⟩, by
          apply Continuous.subtype_mk
          exact Complex.continuous_exp.comp (by fun_prop)⟩
    (by simp)
    (by
      apply Subtype.ext
      change
        Complex.exp
            (-((2 : ℂ) * Real.pi * (1 : ℂ)) * Complex.I) =
          1
      rw [show
          -((2 : ℂ) * Real.pi * (1 : ℂ)) * Complex.I =
            -(((2 * Real.pi : ℝ) : ℂ) * Complex.I) by
        norm_num]
      rw [Complex.exp_neg]
      simp [Complex.exp_mul_I])

/--
%%handwave
name:
  Winding number of the negative unit circle
statement:
  The loop $t\mapsto e^{-2\pi i t}$ has winding number $-1$ around the
  origin.
proof:
  Its logarithmic lift starting at zero is
  $L(t)=-2\pi i t$, whose endpoint is $-2\pi i$.
-/
@[simp]
theorem puncturedLoopWindingNumber_negativeCircleLoop :
    puncturedLoopWindingNumber negativeCircleLoop = -1 := by
  let L : C(unitInterval, ℂ) :=
    ⟨fun t ↦ (-(2 * Real.pi * (t : ℝ))) * Complex.I, by
      fun_prop⟩
  have hL : L = puncturedLoopLogLift negativeCircleLoop := by
    apply (Complex.isCoveringMap_exp.eq_liftPath_iff'
      (γ := negativeCircleLoop) (e := 0) (γ_0 := by simp)).mpr
    constructor
    · funext t
      apply Subtype.ext
      rfl
    · simp [L]
  have hendpoint :
      puncturedLoopLogLift negativeCircleLoop 1 =
        -(2 * Real.pi * Complex.I) := by
    rw [← hL]
    simp [L]
  have hmul :
      (puncturedLoopWindingNumber negativeCircleLoop : ℂ) *
          (2 * Real.pi * Complex.I) =
        (-1 : ℂ) * (2 * Real.pi * Complex.I) := by
    rw [← puncturedLoopLogLift_one_eq_windingNumber_mul, hendpoint]
    ring
  have hcast :
      (puncturedLoopWindingNumber negativeCircleLoop : ℂ) =
        (-1 : ℂ) :=
    mul_right_cancel₀ Complex.two_pi_I_ne_zero hmul
  exact_mod_cast hcast

/--
%%handwave
name:
  Positive loop class has winding number one
statement:
  Every based loop in $\mathbb C\setminus\{0\}$ homotopic to the positive
  unit circle has integer winding number $1$.
proof:
  Winding number is invariant under based homotopy, and the positive unit
  circle has winding number $1$.
-/
theorem puncturedLoopWindingNumber_eq_one_of_homotopic_positive
    {γ : Path (⟨1, one_ne_zero⟩ : PuncturedComplex)
      ⟨1, one_ne_zero⟩}
    (h : Path.Homotopic γ positiveCircleLoop) :
    puncturedLoopWindingNumber γ = 1 := by
  rw [puncturedLoopWindingNumber_eq_of_homotopic h]
  exact puncturedLoopWindingNumber_positiveCircleLoop

/--
%%handwave
name:
  Winding number one characterizes the positive loop class
statement:
  A based loop in $\mathbb C\setminus\{0\}$ is homotopic to the positive unit
  circle if and only if its winding number is $1$.
proof:
  One implication is homotopy invariance. Conversely, winding number
  classifies based punctured-plane loops, and the positive circle has winding
  number one.
-/
theorem puncturedLoop_homotopic_positive_iff_windingNumber_eq_one
    {γ : Path (⟨1, one_ne_zero⟩ : PuncturedComplex)
      ⟨1, one_ne_zero⟩} :
    Path.Homotopic γ positiveCircleLoop ↔
      puncturedLoopWindingNumber γ = 1 := by
  constructor
  · exact puncturedLoopWindingNumber_eq_one_of_homotopic_positive
  · intro h
    apply puncturedLoop_homotopic_of_windingNumber_eq
    rw [h, puncturedLoopWindingNumber_positiveCircleLoop]

/--
%%handwave
name:
  Point on a positively oriented circle
statement:
  For $z\in\mathbb C$, $r\in\mathbb R$, and $t\in[0,1]$, define
  $$
    c_{z,r}(t)=z+r e^{2\pi i t}.
  $$
-/
def circlePoint (z : ℂ) (r : ℝ) (t : unitInterval) : ℂ :=
  z + (r : ℂ) * Complex.exp (((2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I)

/--
%%handwave
name:
  Positive circle starts at the rightmost point
statement:
  The positive circle of radius $r$ centered at $z$ takes the value $z+r$ at
  parameter $0$.
proof:
  Substitute $e^0=1$.
-/
theorem circlePoint_zero (z : ℂ) (r : ℝ) : circlePoint z r 0 = z + r := by
  simp [circlePoint]

/--
%%handwave
name:
  Positive circle closes
statement:
  The positive circle of radius $r$ centered at $z$ takes the value $z+r$ at
  parameter $1$.
proof:
  Substitute $e^{2\pi i}=1$.
-/
theorem circlePoint_one (z : ℂ) (r : ℝ) : circlePoint z r 1 = z + r := by
  rw [circlePoint]
  simp only [Set.Icc.coe_one, mul_one]
  simp [Complex.exp_mul_I]

/--
%%handwave
name:
  A positive-radius circle avoids its center
statement:
  If $r>0$, then every point of the circle of radius $r$ centered at $z$ is
  different from $z$.
proof:
  Both $r$ and the complex exponential are nonzero.
-/
theorem circlePoint_ne_center (z : ℂ) {r : ℝ} (hr : 0 < r)
    (t : unitInterval) : circlePoint z r t ≠ z := by
  rw [circlePoint, add_ne_left]
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hr)) (Complex.exp_ne_zero _)

/--
%%handwave
name:
  Distance from a positive circle to its center
statement:
  Every point of the positive circle of radius $r>0$ centered at $z$ has
  distance exactly $r$ from $z$.
proof:
  The complex exponential on the imaginary axis has norm one.
-/
theorem dist_circlePoint_center (z : ℂ) {r : ℝ} (hr : 0 < r)
    (t : unitInterval) : dist (circlePoint z r t) z = r := by
  rw [Complex.dist_eq, circlePoint, add_sub_cancel_left, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg hr.le,
    Complex.norm_exp_ofReal_mul_I, mul_one]

/--
%%handwave
name:
  Positive-circle parameterization is onto
statement:
  Let $r>0$. Every point $q$ with $|q-c|=r$ has the form
  $$
    q=c+r e^{2\pi i t}
  $$
  for some $t\in[0,1]$.
proof:
  Normalize $(q-c)/r$ to a point of the unit circle. Use the standard
  homeomorphism $\mathbb R/\mathbb Z\simeq S^1$ and represent its additive
  circle coordinate by an element of $[0,1]$.
-/
theorem exists_circlePoint_eq_of_dist_eq
    (c q : ℂ) {r : ℝ} (hr : 0 < r)
    (hq : dist q c = r) :
    ∃ t : unitInterval, circlePoint c r t = q := by
  have hnorm : ‖(q - c) / (r : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real,
      Real.norm_of_nonneg hr.le,
      ← Complex.dist_eq, hq,
      div_self (ne_of_gt hr)]
  let u : Circle :=
    ⟨(q - c) / (r : ℂ),
      mem_sphere_zero_iff_norm.mpr hnorm⟩
  let x : AddCircle (1 : ℝ) :=
    (AddCircle.homeomorphCircle
      (T := (1 : ℝ)) one_ne_zero).symm u
  have hx' : x ∈
      ((↑) : ℝ → AddCircle (1 : ℝ)) ''
        Set.Icc 0 (0 + 1) := by
    rw [AddCircle.coe_image_Icc_eq]
    exact Set.mem_univ x
  have hx : x ∈
      ((↑) : ℝ → AddCircle (1 : ℝ)) ''
        Set.Icc 0 1 := by
    simpa using hx'
  obtain ⟨s, hs, hsx⟩ := hx
  let t : unitInterval := ⟨s, hs⟩
  refine ⟨t, ?_⟩
  have hcircle :
      Circle.exp (2 * Real.pi * (t : ℝ)) = u := by
    have happ :
        AddCircle.homeomorphCircle
            (T := (1 : ℝ)) one_ne_zero
            (t : AddCircle (1 : ℝ)) = u := by
      rw [hsx]
      exact Homeomorph.apply_symm_apply _ u
    rw [AddCircle.homeomorphCircle_apply] at happ
    apply Subtype.ext
    have hval := congrArg Subtype.val happ
    rw [AddCircle.toCircle_apply_mk,
      Circle.coe_exp] at hval
    simpa using hval
  have hval := congrArg Subtype.val hcircle
  change Complex.exp
      (((2 * Real.pi * (t : ℝ) : ℝ) : ℂ) *
        Complex.I) =
    (q - c) / (r : ℂ) at hval
  rw [circlePoint, hval]
  field_simp [Complex.ofReal_ne_zero.mpr
    (ne_of_gt hr)]
  ring

/--
%%handwave
name:
  A contained closed disk contains its boundary circle
statement:
  If the closed disk of positive radius $r$ centered at $z$ lies in $\Omega$,
  then every point of its positive boundary circle lies in $\Omega$.
proof:
  Each boundary point has distance $r$ from the center.
-/
theorem circlePoint_mem_of_closedBall_subset {Ω : Set ℂ} (z : Ω)
    {r : ℝ} (hr : 0 < r) (hball : Metric.closedBall (z : ℂ) r ⊆ Ω)
    (t : unitInterval) : circlePoint z r t ∈ Ω := by
  apply hball
  rw [Metric.mem_closedBall, dist_circlePoint_center z hr t]

/--
%%handwave
name:
  Normalized image of a positive boundary circle
statement:
  Let $F:\Omega\to\Omega'$ be a homeomorphism, let $z\in\Omega$, and suppose
  the circle $c_{z,r}$ lies in $\Omega$. Define the based punctured-plane loop
  $$
    t\longmapsto
      \frac{F(c_{z,r}(t))-F(z)}
           {F(c_{z,r}(0))-F(z)}.
  $$
-/
def normalizedBoundaryLoop {Ω Ω' : Set ℂ} (F : Ω ≃ₜ Ω')
    (z : Ω) (r : ℝ) (hr : 0 < r)
    (hcircle : ∀ t : unitInterval, circlePoint z r t ∈ Ω) :
    Path (⟨1, one_ne_zero⟩ : PuncturedComplex) ⟨1, one_ne_zero⟩ := by
  let source : unitInterval → Ω := fun t ↦ ⟨circlePoint z r t, hcircle t⟩
  have hsource_ne (t : unitInterval) : source t ≠ z := by
    apply Subtype.coe_ne_coe.mp
    exact circlePoint_ne_center z hr t
  have hnum_ne (t : unitInterval) : (F (source t) : ℂ) - F z ≠ 0 :=
    sub_ne_zero.mpr (Subtype.coe_ne_coe.mpr (F.injective.ne (hsource_ne t)))
  have hden_ne : (F (source 0) : ℂ) - F z ≠ 0 := hnum_ne 0
  let loop : unitInterval → PuncturedComplex := fun t ↦
    ⟨((F (source t) : ℂ) - F z) / ((F (source 0) : ℂ) - F z),
      div_ne_zero (hnum_ne t) hden_ne⟩
  refine Path.mk ⟨loop, ?_⟩ ?_ ?_
  · apply Continuous.subtype_mk
    dsimp [loop]
    apply Continuous.div_const
    apply Continuous.sub
    · apply Continuous.subtype_val
      apply F.continuous.comp
      apply Continuous.subtype_mk
      dsimp [source, circlePoint]
      exact continuous_const.add
        (continuous_const.mul (Complex.continuous_exp.comp (by fun_prop)))
    · exact continuous_const
  · apply Subtype.ext
    simp [loop, hden_ne]
  · apply Subtype.ext
    change ((F (source 1) : ℂ) - F z) / ((F (source 0) : ℂ) - F z) = 1
    have hs : source 1 = source 0 := by
      apply Subtype.ext
      exact (circlePoint_one z r).trans (circlePoint_zero z r).symm
    rw [hs]
    exact div_self hden_ne

/--
%%handwave
name:
  Normalized image of a target-avoiding closed loop
statement:
  Let $F:\Omega\to\Omega'$ be a homeomorphism, $z\in\Omega$, and let
  $\gamma:[0,1]\to\Omega\setminus\{z\}$ be a closed loop. Define the based
  punctured-plane loop
  $$
    t\longmapsto
      \frac{F(\gamma(t))-F(z)}
           {F(\gamma(0))-F(z)}.
  $$
-/
def normalizedImageLoop {Ω Ω' : Set ℂ} (F : Ω ≃ₜ Ω')
    (z : Ω) (γ : C(unitInterval, Ω))
    (hne : ∀ t, γ t ≠ z) (hclosed : γ 1 = γ 0) :
    Path (⟨1, one_ne_zero⟩ : PuncturedComplex) ⟨1, one_ne_zero⟩ := by
  have hnum (t : unitInterval) : (F (γ t) : ℂ) - F z ≠ 0 :=
    sub_ne_zero.mpr (Subtype.coe_ne_coe.mpr (F.injective.ne (hne t)))
  have hden : (F (γ 0) : ℂ) - F z ≠ 0 := hnum 0
  let loop : unitInterval → PuncturedComplex := fun t ↦
    ⟨((F (γ t) : ℂ) - F z) / ((F (γ 0) : ℂ) - F z),
      div_ne_zero (hnum t) hden⟩
  refine Path.mk ⟨loop, ?_⟩ ?_ ?_
  · apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp (F.continuous.comp γ.continuous)).sub
      continuous_const |>.div_const _
  · apply Subtype.ext
    simp [loop, hden]
  · apply Subtype.ext
    simp [loop, hclosed, hden]

/--
%%handwave
name:
  Homotopy of normalized images of target-avoiding loops
statement:
  Let $H:[0,1]^2\to\Omega\setminus\{z\}$ be a continuous family of closed
  loops. Normalizing the $s$th loop by
  $$
    (s,t)\longmapsto
      \frac{F(H(s,t))-F(z)}
           {F(H(s,0))-F(z)}
  $$
  defines a based homotopy in $\mathbb C\setminus\{0\}$ between the
  normalized loops at $s=0$ and $s=1$.
-/
def normalizedImageLoopHomotopy {Ω Ω' : Set ℂ} (F : Ω ≃ₜ Ω')
    (z : Ω) (H : C(unitInterval × unitInterval, Ω))
    (hne : ∀ x, H x ≠ z) (hclosed : ∀ s, H (s, 1) = H (s, 0)) :
    Path.Homotopy
      (normalizedImageLoop F z
        (H.comp ⟨fun t ↦ (0, t), by fun_prop⟩)
        (fun t ↦ hne (0, t)) (hclosed 0))
      (normalizedImageLoop F z
        (H.comp ⟨fun t ↦ (1, t), by fun_prop⟩)
        (fun t ↦ hne (1, t)) (hclosed 1)) := by
  have hnum (x : unitInterval × unitInterval) :
      (F (H x) : ℂ) - F z ≠ 0 :=
    sub_ne_zero.mpr (Subtype.coe_ne_coe.mpr (F.injective.ne (hne x)))
  have hden (s : unitInterval) : (F (H (s, 0)) : ℂ) - F z ≠ 0 :=
    hnum (s, 0)
  let hom : unitInterval × unitInterval → PuncturedComplex := fun x ↦
    ⟨((F (H x) : ℂ) - F z) / ((F (H (x.1, 0)) : ℂ) - F z),
      div_ne_zero (hnum x) (hden x.1)⟩
  refine
    { toFun := hom
      continuous_toFun := ?_
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }
  · apply Continuous.subtype_mk
    apply Continuous.div
    · exact (continuous_subtype_val.comp (F.continuous.comp H.continuous)).sub
        continuous_const
    · exact (continuous_subtype_val.comp
        (F.continuous.comp (H.continuous.comp (by fun_prop)))).sub continuous_const
    · exact fun x ↦ hden x.1
  · intro t
    rfl
  · intro t
    rfl
  · intro s t ht
    apply Subtype.ext
    rcases ht with rfl | rfl
    · simp [hom, hden]
    · simp [hom, hclosed, hden]

/--
%%handwave
name:
  Normalized loop around a point
statement:
  Let $\gamma$ be a closed loop in $\mathbb C$ avoiding $w$. Translating by
  $-w$ and dividing by the initial displacement gives the based loop
  $$
    t\longmapsto\frac{\gamma(t)-w}{\gamma(0)-w}
  $$
  in $\mathbb C\setminus\{0\}$.
-/
def normalizedLoopAround (γ : C(unitInterval, ℂ)) (w : ℂ)
    (hne : ∀ t, γ t ≠ w) (hclosed : γ 1 = γ 0) :
    Path (⟨1, one_ne_zero⟩ : PuncturedComplex) ⟨1, one_ne_zero⟩ := by
  have hnum (t : unitInterval) : γ t - w ≠ 0 := sub_ne_zero.mpr (hne t)
  have hden : γ 0 - w ≠ 0 := hnum 0
  let loop : unitInterval → PuncturedComplex := fun t ↦
    ⟨(γ t - w) / (γ 0 - w), div_ne_zero (hnum t) hden⟩
  refine Path.mk ⟨loop, ?_⟩ ?_ ?_
  · apply Continuous.subtype_mk
    exact (γ.continuous.sub continuous_const).div_const _
  · apply Subtype.ext
    simp [loop, hden]
  · apply Subtype.ext
    simp [loop, hclosed, hden]

/--
%%handwave
name:
  Punctured path associated with a loop around a point
statement:
  If a closed planar loop $\gamma$ avoids $w$, then
  $$
    t\longmapsto\gamma(t)-w
  $$
  is a closed path in $\mathbb C\setminus\{0\}$ based at
  $\gamma(0)-w$.
-/
def puncturedPathAround
    (γ : C(unitInterval, ℂ)) (w : ℂ)
    (hne : ∀ t, γ t ≠ w) (hclosed : γ 1 = γ 0) :
    Path
      (⟨γ 0 - w, sub_ne_zero.mpr (hne 0)⟩ :
        PuncturedComplex)
      (⟨γ 0 - w, sub_ne_zero.mpr (hne 0)⟩ :
        PuncturedComplex) :=
  Path.mk
    (⟨fun t ↦
      (⟨γ t - w, sub_ne_zero.mpr (hne t)⟩ :
        PuncturedComplex),
      Continuous.subtype_mk
        (γ.continuous.sub continuous_const) _⟩ :
      C(unitInterval, PuncturedComplex))
    (by rfl)
    (by
      apply Subtype.ext
      simp only [hclosed])

/--
%%handwave
name:
  Normalizing a translated planar loop
statement:
  Let $\gamma$ be a closed planar loop avoiding $w$. Normalizing the
  punctured path $\gamma-w$ by its initial value gives exactly
  $$
    t\longmapsto
      \frac{\gamma(t)-w}{\gamma(0)-w}.
  $$
proof:
  Both paths have the displayed value at every parameter.
-/
theorem normalizedPuncturedPathLoop_puncturedPathAround
    (γ : C(unitInterval, ℂ)) (w : ℂ)
    (hne : ∀ t, γ t ≠ w) (hclosed : γ 1 = γ 0) :
    normalizedPuncturedPathLoop
        (puncturedPathAround γ w hne hclosed) =
      normalizedLoopAround γ w hne hclosed := by
  apply Path.ext
  funext t
  apply Subtype.ext
  rfl

/--
%%handwave
name:
  Logarithmic increment of a translated planar loop
statement:
  If a closed planar loop $\gamma$ avoids $w$, then
  $$
    \Delta\log(\gamma-w)
      =\operatorname{wind}(\gamma,w)\,2\pi i,
  $$
  where the winding number is computed from
  $(\gamma(t)-w)/(\gamma(0)-w)$.
proof:
  Apply the logarithmic-increment formula for a closed punctured-plane path
  and identify its normalized path with the normalized loop around $w$.
-/
theorem puncturedPathAround_logIncrement_eq_windingNumber_mul
    (γ : C(unitInterval, ℂ)) (w : ℂ)
    (hne : ∀ t, γ t ≠ w) (hclosed : γ 1 = γ 0) :
    puncturedPathLogIncrement
        (puncturedPathAround γ w hne hclosed) =
      (puncturedLoopWindingNumber
          (normalizedLoopAround γ w hne hclosed) : ℂ) *
        (2 * Real.pi * Complex.I) := by
  rw [puncturedPathLogIncrement_eq_windingNumber_mul,
    normalizedPuncturedPathLoop_puncturedPathAround]

/--
%%handwave
name:
  Normalized loops vary homotopically in an avoiding family
statement:
  Let $H(s,t)$ be a continuous family of closed planar loops, all avoiding a
  fixed point $w$. After translation by $-w$ and normalization at $t=0$, the
  loops at $s=0$ and $s=1$ are homotopic in
  $\mathbb C\setminus\{0\}$.
proof:
  Normalize the entire two-parameter family by
  $$
    (s,t)\longmapsto\frac{H(s,t)-w}{H(s,0)-w}.
  $$
  The avoidance hypothesis makes every denominator and numerator nonzero.
-/
theorem normalizedLoopAround_homotopic_of_homotopy
    (H : C(unitInterval × unitInterval, ℂ)) (w : ℂ)
    (hne : ∀ x, H x ≠ w) (hclosed : ∀ s, H (s, 1) = H (s, 0)) :
    Path.Homotopic
      (normalizedLoopAround
        (H.comp ⟨fun t ↦ (0, t), by fun_prop⟩) w
        (fun t ↦ hne (0, t)) (hclosed 0))
      (normalizedLoopAround
        (H.comp ⟨fun t ↦ (1, t), by fun_prop⟩) w
        (fun t ↦ hne (1, t)) (hclosed 1)) := by
  have hnum (x : unitInterval × unitInterval) : H x - w ≠ 0 :=
    sub_ne_zero.mpr (hne x)
  have hden (s : unitInterval) : H (s, 0) - w ≠ 0 := hnum (s, 0)
  let hom : unitInterval × unitInterval → PuncturedComplex := fun x ↦
    ⟨(H x - w) / (H (x.1, 0) - w),
      div_ne_zero (hnum x) (hden x.1)⟩
  refine ⟨{
    toFun := hom
    continuous_toFun := ?_
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · apply Continuous.subtype_mk
    exact (H.continuous.sub continuous_const).div
      ((H.continuous.comp (by fun_prop)).sub continuous_const)
      (fun x ↦ hden x.1)
  · intro t
    rfl
  · intro t
    rfl
  · intro s t ht
    apply Subtype.ext
    rcases ht with rfl | rfl
    · simp [hom, hden]
    · simp [hom, hclosed, hden]

/--
%%handwave
name:
  Normalized loops with a moving avoided point
statement:
  Let $H(s,t)$ be a continuous family of closed planar loops and let $c(s)$
  be a continuous path such that $H(s,t)\ne c(s)$ for all $s,t$. Then the
  normalized loop $H(0,\cdot)$ around $c(0)$ is homotopic in the punctured
  plane to the normalized loop $H(1,\cdot)$ around $c(1)$.
proof:
  Normalize the two-parameter family by
  $$
    (s,t)\longmapsto
      \frac{H(s,t)-c(s)}{H(s,0)-c(s)}.
  $$
-/
theorem normalizedLoopAround_homotopic_of_homotopy_moving_center
    (H : C(unitInterval × unitInterval, ℂ)) (c : C(unitInterval, ℂ))
    (hne : ∀ x, H x ≠ c x.1) (hclosed : ∀ s, H (s, 1) = H (s, 0)) :
    Path.Homotopic
      (normalizedLoopAround
        (H.comp ⟨fun t ↦ (0, t), by fun_prop⟩) (c 0)
        (fun t ↦ hne (0, t)) (hclosed 0))
      (normalizedLoopAround
        (H.comp ⟨fun t ↦ (1, t), by fun_prop⟩) (c 1)
        (fun t ↦ hne (1, t)) (hclosed 1)) := by
  have hnum (x : unitInterval × unitInterval) : H x - c x.1 ≠ 0 :=
    sub_ne_zero.mpr (hne x)
  have hden (s : unitInterval) : H (s, 0) - c s ≠ 0 := hnum (s, 0)
  let hom : unitInterval × unitInterval → PuncturedComplex := fun x ↦
    ⟨(H x - c x.1) / (H (x.1, 0) - c x.1),
      div_ne_zero (hnum x) (hden x.1)⟩
  refine ⟨{
    toFun := hom
    continuous_toFun := ?_
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · apply Continuous.subtype_mk
    exact (H.continuous.sub (c.continuous.comp (by fun_prop))).div
      ((H.continuous.comp (by fun_prop)).sub (c.continuous.comp (by fun_prop)))
      (fun x ↦ hden x.1)
  · intro t
    rfl
  · intro t
    rfl
  · intro s t ht
    apply Subtype.ext
    rcases ht with rfl | rfl
    · simp [hom, hden]
    · simp [hom, hclosed, hden]

/--
%%handwave
name:
  Straight-line stability of normalized loop class
statement:
  Let $\gamma_0$ and $\gamma_1$ be closed loops avoiding $w$. If
  $$
    |\gamma_1(t)-\gamma_0(t)|<|\gamma_0(t)-w|
  $$
  for every $t$, then their normalized loops around $w$ are homotopic in
  $\mathbb C\setminus\{0\}$.
proof:
  Join the two loops pointwise by straight line segments. Every point of a
  segment lies strictly closer to $\gamma_0(t)$ than $w$ does, so the
  two-parameter family avoids $w$. Normalize this family at its initial
  point.
-/
theorem normalizedLoopAround_homotopic_of_norm_sub_lt
    (γ₀ γ₁ : C(unitInterval, ℂ)) (w : ℂ)
    (h₀ne : ∀ t, γ₀ t ≠ w) (h₁ne : ∀ t, γ₁ t ≠ w)
    (h₀closed : γ₀ 1 = γ₀ 0) (h₁closed : γ₁ 1 = γ₁ 0)
    (hclose : ∀ t, ‖γ₁ t - γ₀ t‖ < ‖γ₀ t - w‖) :
    Path.Homotopic
      (normalizedLoopAround γ₀ w h₀ne h₀closed)
      (normalizedLoopAround γ₁ w h₁ne h₁closed) := by
  let H : C(unitInterval × unitInterval, ℂ) :=
    ⟨fun x ↦ γ₀ x.2 + (x.1 : ℝ) • (γ₁ x.2 - γ₀ x.2), by fun_prop⟩
  have hHne (x : unitInterval × unitInterval) : H x ≠ w := by
    intro hxw
    have hs0 : 0 ≤ (x.1 : ℝ) := x.1.2.1
    have hs1 : (x.1 : ℝ) ≤ 1 := x.1.2.2
    have heq : γ₀ x.2 - w = -(x.1 : ℝ) • (γ₁ x.2 - γ₀ x.2) := by
      calc
        γ₀ x.2 - w = γ₀ x.2 - H x := by rw [hxw]
        _ = -(x.1 : ℝ) • (γ₁ x.2 - γ₀ x.2) := by
          simp only [H, ContinuousMap.coe_mk, neg_smul, sub_eq_add_neg]
          module
    have hbaseLe : ‖γ₀ x.2 - w‖ ≤ ‖γ₁ x.2 - γ₀ x.2‖ := by
      rw [heq, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hs0]
      exact mul_le_of_le_one_left (norm_nonneg _) hs1
    exact (not_lt_of_ge hbaseLe) (hclose x.2)
  have hHclosed (s : unitInterval) : H (s, 1) = H (s, 0) := by
    simp only [H, ContinuousMap.coe_mk, h₀closed, h₁closed]
  have hhom := normalizedLoopAround_homotopic_of_homotopy H w hHne hHclosed
  convert hhom using 1 <;>
    apply Path.ext <;>
    funext t <;>
    apply Subtype.ext <;>
    simp [H, normalizedLoopAround]

/--
%%handwave
name:
  Positive circle as a path in a containing planar set
statement:
  If the circle $c_{z,r}(t)=z+r e^{2\pi i t}$ lies in
  $\Omega\subseteq\mathbb C$, define its lift as the continuous path
  $$
    [0,1]\longrightarrow\Omega,\qquad t\longmapsto c_{z,r}(t).
  $$
-/
def circlePath {Ω : Set ℂ} (z : Ω) (r : ℝ)
    (hcircle : ∀ t : unitInterval, circlePoint z r t ∈ Ω) :
    C(unitInterval, Ω) :=
  ⟨fun t ↦ ⟨circlePoint z r t, hcircle t⟩, by
    apply Continuous.subtype_mk
    dsimp [circlePoint]
    exact continuous_const.add
      (continuous_const.mul (Complex.continuous_exp.comp (by fun_prop)))⟩

/--
%%handwave
name:
  Planar positive circle loop
statement:
  The planar positive circle loop of radius $r$ centered at $z$ is
  $$
    t\longmapsto z+r e^{2\pi i t}.
  $$
-/
def complexCircleLoop (z : ℂ) (r : ℝ) : C(unitInterval, ℂ) :=
  ⟨fun t ↦ circlePoint z r t, by
    dsimp [circlePoint]
    exact continuous_const.add
      (continuous_const.mul (Complex.continuous_exp.comp (by fun_prop)))⟩

/--
%%handwave
name:
  A planar positive circle loop closes
statement:
  The planar positive circle of radius $r$ centered at $z$ has the same value
  at parameters $0$ and $1$.
proof:
  Both endpoint values are $z+r$.
-/
theorem complexCircleLoop_one_eq_zero (z : ℂ) (r : ℝ) :
    complexCircleLoop z r 1 = complexCircleLoop z r 0 := by
  exact (circlePoint_one z r).trans (circlePoint_zero z r).symm

/--
%%handwave
name:
  A positive planar circle avoids its center
statement:
  If $r>0$, then the positive circle of radius $r$ centered at $z$ never
  passes through $z$.
proof:
  Every point of the circle has distance $r>0$ from its center.
-/
theorem complexCircleLoop_ne_center (z : ℂ) {r : ℝ} (hr : 0 < r) :
    ∀ t, complexCircleLoop z r t ≠ z := by
  exact circlePoint_ne_center z hr

/--
%%handwave
name:
  Normalized positive circle has the standard positive class
statement:
  Translating a positive circle of radius $r>0$ by its center and normalizing
  at the initial point gives exactly the standard loop
  $t\mapsto e^{2\pi i t}$ in $\mathbb C\setminus\{0\}$.
proof:
  Translation removes the center, and division by the positive radius
  cancels its scale.
-/
theorem normalizedLoopAround_complexCircleLoop_center
    (z : ℂ) {r : ℝ} (hr : 0 < r) :
    normalizedLoopAround (complexCircleLoop z r) z
      (complexCircleLoop_ne_center z hr)
      (complexCircleLoop_one_eq_zero z r) = positiveCircleLoop := by
  apply Path.ext
  funext t
  apply Subtype.ext
  change ((circlePoint z r t - z) / (circlePoint z r 0 - z)) =
    Complex.exp ((2 * Real.pi * (t : ℝ)) * Complex.I)
  rw [circlePoint_zero]
  simp only [add_sub_cancel_left]
  rw [circlePoint]
  simp only [add_sub_cancel_left]
  change ((r : ℂ) *
      Complex.exp (((2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I)) /
        (r : ℂ) = Complex.exp ((2 * Real.pi * (t : ℝ)) * Complex.I)
  field_simp [Complex.ofReal_ne_zero.mpr (ne_of_gt hr)]
  congr 1
  push_cast
  ring

/--
%%handwave
name:
  A positive circle avoids every point in its interior
statement:
  If $|w-z|<r$, then the positive circle of radius $r$ centered at $z$ does
  not pass through $w$.
proof:
  Every point on the circle has distance exactly $r$ from $z$, whereas $w$
  has smaller distance from $z$.
-/
theorem complexCircleLoop_ne_of_dist_lt_radius
    (z w : ℂ) {r : ℝ} (hr : 0 < r) (hw : dist w z < r) :
    ∀ t, complexCircleLoop z r t ≠ w := by
  intro t htw
  have := dist_circlePoint_center z hr t
  change circlePoint z r t = w at htw
  rw [htw] at this
  linarith

/--
%%handwave
name:
  Every interior point sees a positive circle with degree one
statement:
  Let $r>0$ and $|w-z|<r$. The positive circle of radius $r$ centered at $z$,
  normalized as a loop around $w$, is homotopic in
  $\mathbb C\setminus\{0\}$ to the standard positive unit circle.
proof:
  Move the avoided point linearly from $w$ to $z$. The entire segment remains
  strictly inside the circle, so the normalized loop class does not change.
  At the center the normalized loop is exactly the standard positive circle.
-/
theorem normalizedLoopAround_complexCircleLoop_homotopic_positive
    (z w : ℂ) {r : ℝ} (hr : 0 < r) (hw : dist w z < r) :
    Path.Homotopic
      (normalizedLoopAround (complexCircleLoop z r) w
        (complexCircleLoop_ne_of_dist_lt_radius z w hr hw)
        (complexCircleLoop_one_eq_zero z r))
      positiveCircleLoop := by
  let H : C(unitInterval × unitInterval, ℂ) :=
    ⟨fun x ↦ complexCircleLoop z r x.2, by fun_prop⟩
  let c : C(unitInterval, ℂ) :=
    ⟨fun s ↦ z + (s : ℝ) • (w - z), by fun_prop⟩
  have hHne (x : unitInterval × unitInterval) : H x ≠ c x.1 := by
    intro heq
    have hs0 : 0 ≤ (x.1 : ℝ) := x.1.2.1
    have hs1 : (x.1 : ℝ) ≤ 1 := x.1.2.2
    have hcircle : dist (H x) z = r :=
      dist_circlePoint_center z hr x.2
    have hcenter : dist (c x.1) z ≤ dist w z := by
      rw [Complex.dist_eq]
      simp only [c, ContinuousMap.coe_mk, add_sub_cancel_left, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg hs0, Complex.dist_eq]
      exact mul_le_of_le_one_left (norm_nonneg _) hs1
    rw [heq] at hcircle
    linarith
  have hHclosed (s : unitInterval) : H (s, 1) = H (s, 0) := by
    exact complexCircleLoop_one_eq_zero z r
  have hhom :=
    normalizedLoopAround_homotopic_of_homotopy_moving_center
      H c hHne hHclosed
  have hhom' :
      Path.Homotopic
        (normalizedLoopAround (complexCircleLoop z r) w
          (complexCircleLoop_ne_of_dist_lt_radius z w hr hw)
          (complexCircleLoop_one_eq_zero z r))
        (normalizedLoopAround (complexCircleLoop z r) z
          (complexCircleLoop_ne_center z hr)
          (complexCircleLoop_one_eq_zero z r)) := by
    convert hhom.symm using 1 <;>
      apply Path.ext <;>
      funext t <;>
      apply Subtype.ext <;>
      simp [H, c, normalizedLoopAround]
  rw [normalizedLoopAround_complexCircleLoop_center z hr] at hhom'
  exact hhom'

/--
%%handwave
name:
  A circle avoids every point strictly outside its disk
statement:
  If $r>0$ and $r<|w-z|$, then the positive circle
  $\partial B(z,r)$ does not pass through $w$.
proof:
  Every point on the circle has distance $r$ from $z$, whereas $w$ has
  strictly larger distance from $z$.
-/
theorem complexCircleLoop_ne_of_radius_lt_dist
    (z w : ℂ) {r : ℝ} (hr : 0 < r)
    (hout : r < dist w z) :
    ∀ t, complexCircleLoop z r t ≠ w := by
  intro t h
  have hc := dist_circlePoint_center z hr t
  change circlePoint z r t = w at h
  rw [h] at hc
  linarith

/--
%%handwave
name:
  Logarithmic increment around an interior point
statement:
  If $r>0$ and $|w-z|<r$, then the translated positive circle
  $\gamma(t)=z+r e^{2\pi i t}-w$ satisfies
  $$
    \Delta\log(\gamma)=2\pi i.
  $$
proof:
  The normalized circle around an interior point is homotopic to the
  positive unit circle, whose winding number is one. Apply the
  logarithmic-increment formula for translated planar loops.
-/
theorem puncturedPathAround_complexCircleLoop_logIncrement_of_dist_lt_radius
    (z w : ℂ) {r : ℝ} (hr : 0 < r)
    (hin : dist w z < r) :
    puncturedPathLogIncrement
      (puncturedPathAround (complexCircleLoop z r) w
        (complexCircleLoop_ne_of_dist_lt_radius z w hr hin)
        (complexCircleLoop_one_eq_zero z r)) =
      2 * Real.pi * Complex.I := by
  rw [puncturedPathAround_logIncrement_eq_windingNumber_mul]
  have hhom :=
    normalizedLoopAround_complexCircleLoop_homotopic_positive
      z w hr hin
  rw [puncturedLoopWindingNumber_eq_of_homotopic hhom,
    puncturedLoopWindingNumber_positiveCircleLoop]
  norm_num

/--
%%handwave
name:
  A positive circle has zero winding around an exterior point
statement:
  If $r>0$ and $r<|w-z|$, then
  $$
    \operatorname{wind}(\partial B(z,r),w)=0.
  $$
proof:
  Shrink the circle radially to its center. Every intermediate circle stays
  inside $\overline B(z,r)$ and therefore avoids $w$. The normalized loop is
  thus homotopic to the constant loop at $1$, whose winding number is zero.
-/
theorem
    puncturedLoopWindingNumber_normalizedLoopAround_complexCircleLoop_eq_zero_of_radius_lt_dist
    (z w : ℂ) {r : ℝ} (hr : 0 < r)
    (hout : r < dist w z) :
    puncturedLoopWindingNumber
      (normalizedLoopAround (complexCircleLoop z r) w
        (complexCircleLoop_ne_of_radius_lt_dist z w hr hout)
        (complexCircleLoop_one_eq_zero z r)) = 0 := by
  let radius : unitInterval → ℝ :=
    fun s ↦ (1 - (s : ℝ)) * r
  let H : C(unitInterval × unitInterval, ℂ) :=
    ⟨fun x ↦ circlePoint z (radius x.1) x.2, by
      dsimp [circlePoint, radius]
      fun_prop⟩
  have hHne (x : unitInterval × unitInterval) :
      H x ≠ w := by
    intro hx
    have hs0 : 0 ≤ 1 - (x.1 : ℝ) :=
      sub_nonneg.mpr x.1.2.2
    have hs1 : 1 - (x.1 : ℝ) ≤ 1 := by
      linarith [x.1.2.1]
    have hradius : 0 ≤ radius x.1 :=
      mul_nonneg hs0 hr.le
    have hdist : dist (H x) z = radius x.1 := by
      change dist (circlePoint z (radius x.1) x.2) z =
        radius x.1
      rw [Complex.dist_eq, circlePoint, add_sub_cancel_left]
      change ‖(radius x.1 : ℂ) *
        Complex.exp
          (((2 * Real.pi * (x.2 : ℝ) : ℝ) : ℂ) *
            Complex.I)‖ = radius x.1
      rw [norm_mul, Complex.norm_real,
        Complex.norm_exp_ofReal_mul_I, mul_one,
        Real.norm_of_nonneg hradius]
    have hle : radius x.1 ≤ r :=
      mul_le_of_le_one_left hr.le hs1
    rw [hx] at hdist
    linarith
  have hclosed (s : unitInterval) :
      H (s, 1) = H (s, 0) := by
    exact complexCircleLoop_one_eq_zero z (radius s)
  have hhom :=
    normalizedLoopAround_homotopic_of_homotopy
      H w hHne hclosed
  have hstart :
      normalizedLoopAround
        (H.comp ⟨fun t ↦ (0, t), by fun_prop⟩) w
          (fun t ↦ hHne (0, t)) (hclosed 0) =
      normalizedLoopAround (complexCircleLoop z r) w
        (complexCircleLoop_ne_of_radius_lt_dist z w hr hout)
        (complexCircleLoop_one_eq_zero z r) := by
    apply Path.ext
    funext t
    apply Subtype.ext
    simp [H, radius, normalizedLoopAround,
      complexCircleLoop]
  have hend :
      normalizedLoopAround
        (H.comp ⟨fun t ↦ (1, t), by fun_prop⟩) w
          (fun t ↦ hHne (1, t)) (hclosed 1) =
      Path.refl
        (⟨1, one_ne_zero⟩ : PuncturedComplex) := by
    have hzw : z - w ≠ 0 := by
      apply sub_ne_zero.mpr
      intro h
      rw [h, dist_self] at hout
      exact (lt_irrefl 0) (hr.trans hout)
    apply Path.ext
    funext t
    apply Subtype.ext
    simp [H, radius, circlePoint, normalizedLoopAround,
      hzw]
  rw [← hstart]
  rw [puncturedLoopWindingNumber_eq_of_homotopic hhom]
  rw [hend]
  exact puncturedLoopWindingNumber_refl

/--
%%handwave
name:
  Logarithmic increment around an exterior point
statement:
  If $r>0$ and $r<|w-z|$, then the translated positive circle
  $\gamma(t)=z+r e^{2\pi i t}-w$ satisfies
  $$
    \Delta\log(\gamma)=0.
  $$
proof:
  Its normalized loop has winding number zero around the exterior point, so
  the logarithmic-increment formula gives a zero period.
-/
theorem
    puncturedPathAround_complexCircleLoop_logIncrement_eq_zero_of_radius_lt_dist
    (z w : ℂ) {r : ℝ} (hr : 0 < r)
    (hout : r < dist w z) :
    puncturedPathLogIncrement
      (puncturedPathAround (complexCircleLoop z r) w
        (complexCircleLoop_ne_of_radius_lt_dist z w hr hout)
        (complexCircleLoop_one_eq_zero z r)) = 0 := by
  rw [puncturedPathAround_logIncrement_eq_windingNumber_mul,
    puncturedLoopWindingNumber_normalizedLoopAround_complexCircleLoop_eq_zero_of_radius_lt_dist
      z w hr hout]
  norm_num

/--
%%handwave
name:
  Image loop of a positive circle
statement:
  If $f:\mathbb C\to\mathbb C$ is continuous, its image on the positive
  circle of radius $r$ centered at $z$ is the continuous loop
  $t\mapsto f(z+r e^{2\pi i t})$.
-/
def imageCircleLoop (f : ℂ → ℂ) (hf : Continuous f) (z : ℂ) (r : ℝ) :
    C(unitInterval, ℂ) :=
  ⟨fun t ↦ f (complexCircleLoop z r t),
    hf.comp (complexCircleLoop z r).continuous⟩

/--
%%handwave
name:
  Image of a positive circle is a closed loop
statement:
  The image under a continuous planar map of a positive circle has the same
  value at parameters $0$ and $1$.
proof:
  The original circle has the same endpoint values.
-/
theorem imageCircleLoop_one_eq_zero
    (f : ℂ → ℂ) (hf : Continuous f) (z : ℂ) (r : ℝ) :
    imageCircleLoop f hf z r 1 = imageCircleLoop f hf z r 0 := by
  simp only [imageCircleLoop, ContinuousMap.coe_mk]
  rw [complexCircleLoop_one_eq_zero]

/--
%%handwave
name:
  Planar index on a boundary circle
statement:
  Let $f:\mathbb C\to\mathbb C$ be continuous, let $r>0$, and suppose the
  image of the circle $|\zeta-z|=r$ avoids $w$. The index of $f$ on this
  circle about $w$ is the integer winding number of the normalized image loop
  around $w$.
-/
noncomputable def planarCircleIndex
    (f : ℂ → ℂ) (hf : Continuous f) (z w : ℂ) (r : ℝ) (_hr : 0 < r)
    (havoid : ∀ t, imageCircleLoop f hf z r t ≠ w) : ℤ :=
  puncturedLoopWindingNumber
    (normalizedLoopAround (imageCircleLoop f hf z r) w havoid
      (imageCircleLoop_one_eq_zero f hf z r))

/--
%%handwave
name:
  Planar circle index is stable under a close perturbation
statement:
  Let $f$ and $g$ be continuous maps and suppose that both image loops on
  $\partial B(z,r)$ avoid $w$. If
  $$
    |g(\zeta)-f(\zeta)|<|f(\zeta)-w|
    \qquad (\zeta\in\partial B(z,r)),
  $$
  then the two image loops have the same integer index about $w$.
proof:
  The pointwise straight-line homotopy from $f$ to $g$ stays away from $w$.
  Normalize its endpoint loops and apply homotopy invariance of the
  logarithmic-lift winding number.
-/
theorem planarCircleIndex_eq_of_norm_sub_lt
    (f g : ℂ → ℂ) (hf : Continuous f) (hg : Continuous g)
    (z w : ℂ) {r : ℝ} (hr : 0 < r)
    (hfavoid : ∀ t, imageCircleLoop f hf z r t ≠ w)
    (hgavoid : ∀ t, imageCircleLoop g hg z r t ≠ w)
    (hclose : ∀ t,
      ‖imageCircleLoop g hg z r t - imageCircleLoop f hf z r t‖ <
        ‖imageCircleLoop f hf z r t - w‖) :
    planarCircleIndex f hf z w r hr hfavoid =
      planarCircleIndex g hg z w r hr hgavoid := by
  apply puncturedLoopWindingNumber_eq_of_homotopic
  exact normalizedLoopAround_homotopic_of_norm_sub_lt
    (imageCircleLoop f hf z r) (imageCircleLoop g hg z r) w
    hfavoid hgavoid (imageCircleLoop_one_eq_zero f hf z r)
    (imageCircleLoop_one_eq_zero g hg z r) hclose

/--
%%handwave
name:
  Planar circle index is locally constant in the target
statement:
  Let the image under $f$ of $\partial B(z,r)$ avoid $w$. If
  $$
    |y-w|<|f(\zeta)-w|
    \qquad(\zeta\in\partial B(z,r)),
  $$
  then the image circle also avoids $y$ and its indices about $w$ and $y$
  are equal.
proof:
  Translate the image map by $w-y$. Its loop about $w$ is the original loop
  about $y$, while its distance from the original image loop is the constant
  $|y-w|$. Apply straight-line stability of the circle index.
-/
theorem exists_planarCircleIndex_eq_of_target_norm_sub_lt
    (f : ℂ → ℂ) (hf : Continuous f) (z w y : ℂ)
    {r : ℝ} (hr : 0 < r)
    (hwavoid : ∀ t, imageCircleLoop f hf z r t ≠ w)
    (hclose : ∀ t,
      ‖y - w‖ < ‖imageCircleLoop f hf z r t - w‖) :
    ∃ hyavoid : ∀ t, imageCircleLoop f hf z r t ≠ y,
      planarCircleIndex f hf z w r hr hwavoid =
        planarCircleIndex f hf z y r hr hyavoid := by
  have hyavoid : ∀ t, imageCircleLoop f hf z r t ≠ y := by
    intro t ht
    have hlt := hclose t
    rw [ht] at hlt
    exact (lt_irrefl _) hlt
  let g : ℂ → ℂ := fun x ↦ f x + (w - y)
  have hg : Continuous g := by fun_prop
  have hgavoid : ∀ t, imageCircleLoop g hg z r t ≠ w := by
    intro t ht
    apply hyavoid t
    have heq := congrArg (fun u : ℂ ↦ u - (w - y)) ht
    simpa [imageCircleLoop, g] using heq
  refine ⟨hyavoid, ?_⟩
  have hindex :
      planarCircleIndex f hf z w r hr hwavoid =
        planarCircleIndex g hg z w r hr hgavoid := by
    apply planarCircleIndex_eq_of_norm_sub_lt
      f g hf hg z w hr hwavoid hgavoid
    intro t
    rw [show
        imageCircleLoop g hg z r t - imageCircleLoop f hf z r t =
          w - y by
      simp [imageCircleLoop, g]]
    simpa [norm_sub_rev] using hclose t
  rw [hindex]
  unfold planarCircleIndex
  congr 1
  apply Path.ext
  funext t
  apply Subtype.ext
  simp [normalizedLoopAround, imageCircleLoop, g]
  ring

/--
%%handwave
name:
  Planar disk degree
statement:
  Let $f:\mathbb C\to\mathbb C$ be continuous and let $r>0$. The degree of
  $f$ on $B(z,r)$ at $w$ is the winding number of
  $f|_{\partial B(z,r)}$ about $w$ when the boundary image avoids $w$, and
  is extended by zero on the boundary image.
-/
noncomputable def planarDiskDegree
    (f : ℂ → ℂ) (hf : Continuous f) (z : ℂ) (r : ℝ)
    (hr : 0 < r) (w : ℂ) : ℤ := by
  classical
  exact
    if havoid : ∀ t, imageCircleLoop f hf z r t ≠ w then
      planarCircleIndex f hf z w r hr havoid
    else
      0

/--
%%handwave
name:
  Disk degree away from the boundary image
statement:
  If $f(\partial B(z,r))$ avoids $w$, then
  $\deg(f,B(z,r),w)$ is the circle index of the boundary image about $w$.
proof:
  This is the avoiding branch in the definition of disk degree.
-/
theorem planarDiskDegree_eq_planarCircleIndex
    (f : ℂ → ℂ) (hf : Continuous f) (z w : ℂ)
    {r : ℝ} (hr : 0 < r)
    (havoid : ∀ t, imageCircleLoop f hf z r t ≠ w) :
    planarDiskDegree f hf z r hr w =
      planarCircleIndex f hf z w r hr havoid := by
  simp [planarDiskDegree, havoid]

/--
%%handwave
name:
  Planar circle index is invariant through an avoiding annulus
statement:
  Let $r_0,r_1>0$. Suppose that for every radius
  $$
    r_s=(1-s)r_0+s r_1,
    \qquad 0\leq s\leq1,
  $$
  the image under a continuous map $f$ of the circle
  $|\zeta-z|=r_s$ avoids $w$. Then the indices of the two boundary circles
  about $w$ are equal.
proof:
  The concentric circles give a continuous family of closed image loops
  avoiding $w$. Normalize this family and use homotopy invariance of winding
  number.
-/
theorem planarCircleIndex_eq_of_radial_homotopy
    (f : ℂ → ℂ) (hf : Continuous f) (z w : ℂ)
    (r₀ r₁ : ℝ) (hr₀ : 0 < r₀) (hr₁ : 0 < r₁)
    (havoid : ∀ s t : unitInterval,
      f (circlePoint z ((1 - (s : ℝ)) * r₀ + (s : ℝ) * r₁) t) ≠ w) :
    planarCircleIndex f hf z w r₀ hr₀
        (fun t ↦ by simpa [imageCircleLoop] using havoid 0 t) =
      planarCircleIndex f hf z w r₁ hr₁
        (fun t ↦ by simpa [imageCircleLoop] using havoid 1 t) := by
  let radius : unitInterval → ℝ := fun s ↦
    (1 - (s : ℝ)) * r₀ + (s : ℝ) * r₁
  let H : C(unitInterval × unitInterval, ℂ) :=
    ⟨fun x ↦ f (circlePoint z (radius x.1) x.2), by
      apply hf.comp
      dsimp [circlePoint, radius]
      fun_prop⟩
  have hHne (x : unitInterval × unitInterval) : H x ≠ w :=
    havoid x.1 x.2
  have hHclosed (s : unitInterval) : H (s, 1) = H (s, 0) := by
    dsimp [H]
    rw [circlePoint_one, circlePoint_zero]
  have hhom := normalizedLoopAround_homotopic_of_homotopy H w hHne hHclosed
  apply puncturedLoopWindingNumber_eq_of_homotopic
  convert hhom using 1 <;>
    apply Path.ext <;>
    funext t <;>
    apply Subtype.ext <;>
    simp [normalizedLoopAround, imageCircleLoop, complexCircleLoop, H, radius]

/--
%%handwave
name:
  Isolating radius for a planar fiber point
statement:
  A radius $r$ isolates $z$ in the fiber $f^{-1}(w)$ if $r>0$ and
  $$
    |x-z|\leq r,\quad f(x)=w
    \quad\Longrightarrow\quad x=z.
  $$
-/
def IsFiberIsolatingRadius (f : ℂ → ℂ) (z w : ℂ) (r : ℝ) : Prop :=
  0 < r ∧ ∀ x, dist x z ≤ r → f x = w → x = z

/--
%%handwave
name:
  A discrete fiber supplies an isolating radius
statement:
  Suppose $f(z)=w$ and the fiber $f^{-1}(w)$ is discrete. Then there exists
  a positive radius $r$ which isolates $z$ in that fiber.
proof:
  Discreteness gives an open neighborhood of $z$ meeting the fiber only at
  $z$. Choose a sufficiently small closed disk inside that neighborhood.
-/
theorem exists_isFiberIsolatingRadius_of_isDiscrete_fiber
    (f : ℂ → ℂ) (z w : ℂ) (hzw : f z = w)
    (hdiscrete : IsDiscrete {x : ℂ | f x = w}) :
    ∃ r : ℝ, IsFiberIsolatingRadius f z w r := by
  have hzmem : z ∈ {x : ℂ | f x = w} := hzw
  obtain ⟨U, hUopen, hUfiber⟩ :=
    isOpen_inter_eq_singleton_of_mem_discrete hdiscrete hzmem
  have hzU : z ∈ U := by
    have : z ∈ U ∩ {x : ℂ | f x = w} := by
      rw [hUfiber]
      exact Set.mem_singleton z
    exact this.1
  obtain ⟨ε, hε, hεU⟩ := (Metric.isOpen_iff.mp hUopen) z hzU
  refine ⟨ε / 2, by
    constructor
    · positivity
    · intro x hx hfx
      have hxU : x ∈ U := by
        apply hεU
        rw [Metric.mem_ball]
        linarith
      have hxinter : x ∈ U ∩ {y : ℂ | f y = w} := ⟨hxU, hfx⟩
      rw [hUfiber] at hxinter
      simpa using hxinter⟩

/--
%%handwave
name:
  Smaller positive radii remain fiber-isolating
statement:
  If $r$ isolates $z$ in the fiber $f^{-1}(w)$ and $0<s\le r$, then $s$
  also isolates $z$ in that fiber.
proof:
  The closed disk of radius $s$ is contained in the closed disk of radius
  $r$, so the isolation implication for $r$ applies.
-/
theorem IsFiberIsolatingRadius.mono
    {f : ℂ → ℂ} {z w : ℂ} {r s : ℝ}
    (hr : IsFiberIsolatingRadius f z w r) (hs : 0 < s) (hsr : s ≤ r) :
    IsFiberIsolatingRadius f z w s := by
  refine ⟨hs, fun x hx hfx ↦ hr.2 x (hx.trans hsr) hfx⟩

/--
%%handwave
name:
  Pairwise disjoint isolating disks for a finite fiber
statement:
  Let $f^{-1}(w)$ be finite and discrete and contained in the open disk
  $B(z,r)$. There are positive radii $\rho_x$, one for every
  $x\in f^{-1}(w)$, such that each $\rho_x$ isolates $x$ in the fiber, the
  closed disks $\overline B(x,\rho_x)$ are pairwise disjoint, and all these
  closed disks lie in $B(z,r)$.
proof:
  Choose an isolating radius $s_x$ at every fiber point. Shrink it to one
  third of the minimum of $s_x$ and the distance from $x$ to the outer
  boundary. For distinct fiber points, isolation at both centers bounds each
  new radius by one third of their mutual distance, which makes the two
  closed disks disjoint. The boundary-distance bound keeps every disk inside
  the outer disk.
-/
theorem exists_pairwiseDisjoint_isolatingRadii_of_finite_fiber_subset_ball
    (f : ℂ → ℂ) (z w : ℂ) {r : ℝ}
    (hdiscrete : IsDiscrete {x : ℂ | f x = w})
    (_hfinite : {x : ℂ | f x = w}.Finite)
    (hfiber : {x : ℂ | f x = w} ⊆ Metric.ball z r) :
    ∃ ρ : {x : ℂ // f x = w} → ℝ,
      (∀ x : {x : ℂ // f x = w},
        IsFiberIsolatingRadius f x w (ρ x)) ∧
      (∀ x y : {x : ℂ // f x = w}, x ≠ y →
        Disjoint (Metric.closedBall (x : ℂ) (ρ x))
          (Metric.closedBall (y : ℂ) (ρ y))) ∧
      (∀ x : {x : ℂ // f x = w},
        Metric.closedBall (x : ℂ) (ρ x) ⊆ Metric.ball z r) := by
  have hex (x : {x : ℂ // f x = w}) :
      ∃ s : ℝ, IsFiberIsolatingRadius f x w s :=
    exists_isFiberIsolatingRadius_of_isDiscrete_fiber f x w x.2 hdiscrete
  choose s hs using hex
  let ρ : {x : ℂ // f x = w} → ℝ := fun x ↦
    min (s x) (r - dist (x : ℂ) z) / 3
  have hmargin (x : {x : ℂ // f x = w}) :
      0 < r - dist (x : ℂ) z := by
    have hx := Metric.mem_ball.mp (hfiber x.2)
    linarith
  have hρpos (x : {x : ℂ // f x = w}) : 0 < ρ x := by
    have hmin : 0 < min (s x) (r - dist (x : ℂ) z) :=
      lt_min (hs x).1 (hmargin x)
    dsimp [ρ]
    positivity
  have hρle_s (x : {x : ℂ // f x = w}) : ρ x ≤ s x := by
    have hspos := (hs x).1
    have hmin := min_le_left (s x) (r - dist (x : ℂ) z)
    dsimp [ρ]
    nlinarith [lt_min hspos (hmargin x)]
  have hρle_margin_third (x : {x : ℂ // f x = w}) :
      ρ x ≤ (r - dist (x : ℂ) z) / 3 := by
    exact div_le_div_of_nonneg_right
      (min_le_right (s x) (r - dist (x : ℂ) z)) (by norm_num)
  refine ⟨ρ, fun x ↦ (hs x).mono (hρpos x) (hρle_s x), ?_, ?_⟩
  · intro x y hxy
    have hsx_lt : s x < dist (y : ℂ) x := by
      by_contra h
      have hyx : (y : ℂ) = x := (hs x).2 y (le_of_not_gt h) y.2
      exact hxy (Subtype.ext hyx).symm
    have hsy_lt : s y < dist (x : ℂ) y := by
      by_contra h
      have hxy' : (x : ℂ) = y := (hs y).2 x (le_of_not_gt h) x.2
      exact hxy (Subtype.ext hxy')
    apply Metric.closedBall_disjoint_closedBall
    have hxthird : ρ x ≤ s x / 3 := by
      exact div_le_div_of_nonneg_right
        (min_le_left (s x) (r - dist (x : ℂ) z)) (by norm_num)
    have hythird : ρ y ≤ s y / 3 := by
      exact div_le_div_of_nonneg_right
        (min_le_left (s y) (r - dist (y : ℂ) z)) (by norm_num)
    rw [dist_comm (y : ℂ) x] at hsx_lt
    nlinarith [dist_pos.mpr (Subtype.coe_ne_coe.mpr hxy)]
  · intro x q hq
    rw [Metric.mem_ball]
    have hqx : dist q (x : ℂ) ≤ ρ x := by
      simpa [Metric.mem_closedBall] using hq
    have htriangle : dist q z ≤ dist q (x : ℂ) + dist (x : ℂ) z :=
      dist_triangle _ _ _
    have hρmargin : ρ x < r - dist (x : ℂ) z := by
      nlinarith [hρle_margin_third x, hmargin x]
    linarith

/--
%%handwave
name:
  Smooth uniform approximation on a compact planar set
statement:
  Let $f:\mathbb C\to\mathbb C$ be continuous, let $C\subseteq\mathbb C$ be
  compact, and let $\varepsilon>0$. There is a smooth map
  $g:\mathbb C\to\mathbb C$ such that
  $$
    |g(x)-f(x)|<\varepsilon
    \qquad (x\in C).
  $$
proof:
  Uniform continuity on a compact thickening of $C$ supplies a single input
  scale for the prescribed error. Convolution with a smooth bump function at
  a smaller scale gives a globally smooth approximation satisfying the
  desired bound on $C$.
-/
theorem exists_contDiff_dist_lt_on_compact
    {f : ℂ → ℂ} (hf : Continuous f) {C : Set ℂ} (hC : IsCompact C)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ → ℂ, ContDiff ℝ ∞ g ∧
      ∀ x ∈ C, dist (g x) (f x) < ε := by
  have huc : UniformContinuousOn f (Metric.cthickening 1 C) :=
    hC.cthickening.uniformContinuousOn_of_continuous hf.continuousOn
  rcases Metric.uniformContinuousOn_iff.mp huc (ε / 2) (half_pos hε) with
    ⟨δ, hδ, hfδ⟩
  rcases hf.exists_contDiff_dist_le_of_forall_mem_ball_dist_le
      (lt_min one_pos hδ) with ⟨g, hgc, hg⟩
  refine ⟨g, hgc, fun x hx ↦
    (hg _ _ fun y hy ↦ ?_).trans_lt (half_lt_self hε)⟩
  rw [Metric.mem_ball, lt_min_iff] at hy
  exact hfδ _ (Metric.mem_cthickening_of_dist_le _ x _ _ hx hy.1.le) _
    (Metric.self_subset_cthickening _ hx) hy.2 |>.le

/--
%%handwave
name:
  Closed disk with a family of open disks removed
statement:
  For centers $c_i\in\mathbb C$ and radii $\rho_i\in\mathbb R$, the
  associated perforated closed disk is
  $$
    \overline B(z,r)\setminus\bigcup_i B(c_i,\rho_i).
  $$
-/
def perforatedClosedDisk {ι : Type*} (z : ℂ) (r : ℝ)
    (c : ι → ℂ) (ρ : ι → ℝ) : Set ℂ :=
  Metric.closedBall z r \ ⋃ i, Metric.ball (c i) (ρ i)

/--
%%handwave
name:
  Compactness of a perforated closed disk
statement:
  A closed planar disk with any union of open disks removed is compact.
proof:
  The outer closed disk is compact and the union of the removed open disks
  is open.
-/
theorem isCompact_perforatedClosedDisk {ι : Type*} (z : ℂ) (r : ℝ)
    (c : ι → ℂ) (ρ : ι → ℝ) :
    IsCompact (perforatedClosedDisk z r c ρ) := by
  exact (isCompact_closedBall z r).diff
    (isOpen_iUnion fun _ ↦ Metric.isOpen_ball)

/--
%%handwave
name:
  The outer circle belongs to a strictly nested perforated disk
statement:
  Suppose every closed inner disk $\overline B(c_i,\rho_i)$ lies in the open
  outer disk $B(z,r)$ and $r>0$. Then every point of the circle
  $\partial B(z,r)$ belongs to the associated perforated closed disk.
proof:
  An outer-circle point belongs to the outer closed disk. If it lay in an
  inner open disk, it would lie in the corresponding closed disk and hence
  strictly inside the outer disk, contradicting its distance $r$ from $z$.
-/
theorem circlePoint_mem_perforatedClosedDisk_outer
    {ι : Type*} (z : ℂ) {r : ℝ} (hr : 0 < r)
    (c : ι → ℂ) (ρ : ι → ℝ)
    (hinside : ∀ i, Metric.closedBall (c i) (ρ i) ⊆ Metric.ball z r)
    (t : unitInterval) :
    circlePoint z r t ∈ perforatedClosedDisk z r c ρ := by
  constructor
  · rw [Metric.mem_closedBall, dist_circlePoint_center z hr t]
  · rw [mem_iUnion]
    rintro ⟨i, hi⟩
    have hiclosed : circlePoint z r t ∈ Metric.closedBall (c i) (ρ i) :=
      Metric.ball_subset_closedBall hi
    have hiouter := hinside i hiclosed
    rw [Metric.mem_ball, dist_circlePoint_center z hr t] at hiouter
    exact (lt_irrefl r) hiouter

/--
%%handwave
name:
  Inner circles belong to a disjoint perforated disk
statement:
  Suppose the positive-radius closed disks
  $\overline B(c_i,\rho_i)$ are pairwise disjoint and each lies in
  $B(z,r)$. Then every point of every inner boundary circle belongs to
  $$
    \overline B(z,r)\setminus\bigcup_j B(c_j,\rho_j).
  $$
proof:
  An inner boundary point lies in its own closed disk and hence in the outer
  disk. It is not in its own open disk because its distance from the center
  equals the radius, and pairwise disjointness excludes every other open
  disk.
-/
theorem circlePoint_mem_perforatedClosedDisk_inner
    {ι : Type*} (z : ℂ) (r : ℝ) (c : ι → ℂ) (ρ : ι → ℝ)
    (hρpos : ∀ i, 0 < ρ i)
    (hpair : ∀ i j, i ≠ j →
      Disjoint (Metric.closedBall (c i) (ρ i))
        (Metric.closedBall (c j) (ρ j)))
    (hinside : ∀ i, Metric.closedBall (c i) (ρ i) ⊆ Metric.ball z r)
    (i : ι) (t : unitInterval) :
    circlePoint (c i) (ρ i) t ∈ perforatedClosedDisk z r c ρ := by
  constructor
  · exact Metric.ball_subset_closedBall
      (hinside i (by
        rw [Metric.mem_closedBall,
          dist_circlePoint_center (c i) (hρpos i) t]))
  · rw [mem_iUnion]
    rintro ⟨j, hj⟩
    by_cases hij : i = j
    · subst j
      rw [Metric.mem_ball,
        dist_circlePoint_center (c i) (hρpos i) t] at hj
      exact (lt_irrefl (ρ i)) hj
    · have hiClosed :
          circlePoint (c i) (ρ i) t ∈ Metric.closedBall (c i) (ρ i) := by
        rw [Metric.mem_closedBall,
          dist_circlePoint_center (c i) (hρpos i) t]
      have hjClosed :
          circlePoint (c i) (ρ i) t ∈ Metric.closedBall (c j) (ρ j) :=
        Metric.ball_subset_closedBall hj
      exact Set.disjoint_left.mp (hpair i j hij) hiClosed hjClosed

/--
%%handwave
name:
  Smooth target-avoiding approximation on a perforated disk
statement:
  Let $f:\mathbb C\to\mathbb C$ be continuous and let the points of
  $f^{-1}(w)$ be the centers of positive-radius closed disks contained in
  $B(z,r)$. Put
  $$
    P=\overline B(z,r)\setminus
      \bigcup_{x\in f^{-1}(w)}B(x,\rho_x).
  $$
  If $r>0$, there is a smooth map $g:\mathbb C\to\mathbb C$ such that $g$
  avoids $w$ on $P$ and
  $$
    |g(q)-f(q)|<|f(q)-w|\qquad(q\in P).
  $$
proof:
  The perforated set $P$ is compact, because it is a closed disk minus an
  open union of balls. It is nonempty: the outer circle belongs to $P$ since
  every closed inner disk lies strictly inside the outer disk. The continuous
  positive function $|f-w|$ therefore has a positive minimum on $P$.
  Approximate $f$ smoothly within half that minimum. The strict relative
  error both prevents $g=w$ and gives the displayed estimate.
-/
theorem exists_contDiff_avoiding_approximationOn_perforatedClosedDisk
    (f : ℂ → ℂ) (hf : Continuous f) (z w : ℂ) {r : ℝ} (hr : 0 < r)
    (ρ : {x : ℂ // f x = w} → ℝ)
    (hρpos : ∀ x : {x : ℂ // f x = w}, 0 < ρ x)
    (hinside : ∀ x : {x : ℂ // f x = w},
      Metric.closedBall (x : ℂ) (ρ x) ⊆ Metric.ball z r) :
    ∃ g : ℂ → ℂ, ContDiff ℝ ∞ g ∧
      (∀ q ∈ perforatedClosedDisk z r
          (fun x : {x : ℂ // f x = w} ↦ (x : ℂ)) ρ,
        g q ≠ w) ∧
      (∀ q ∈ perforatedClosedDisk z r
          (fun x : {x : ℂ // f x = w} ↦ (x : ℂ)) ρ,
        ‖g q - f q‖ < ‖f q - w‖) := by
  let P : Set ℂ := perforatedClosedDisk z r
    (fun x : {x : ℂ // f x = w} ↦ (x : ℂ)) ρ
  have hPcompact : IsCompact P := by
    exact isCompact_perforatedClosedDisk z r
      (fun x : {x : ℂ // f x = w} ↦ (x : ℂ)) ρ
  have houter (t : unitInterval) : circlePoint z r t ∈ P := by
    exact circlePoint_mem_perforatedClosedDisk_outer z hr
      (fun x : {x : ℂ // f x = w} ↦ (x : ℂ)) ρ hinside t
  have hPnonempty : P.Nonempty := ⟨circlePoint z r 0, houter 0⟩
  have hfavoid (q : ℂ) (hq : q ∈ P) : f q ≠ w := by
    intro hqw
    let x : {x : ℂ // f x = w} := ⟨q, hqw⟩
    have hqball : q ∈ Metric.ball (x : ℂ) (ρ x) := by
      rw [Metric.mem_ball]
      simpa [x] using hρpos x
    exact hq.2 (mem_iUnion.mpr ⟨x, hqball⟩)
  let d : ℂ → ℝ := fun q ↦ ‖f q - w‖
  have hdcont : Continuous d := by
    dsimp [d]
    fun_prop
  obtain ⟨q₀, hq₀, hq₀min⟩ :=
    hPcompact.exists_isMinOn hPnonempty hdcont.continuousOn
  have hdpos : 0 < d q₀ := by
    change 0 < ‖f q₀ - w‖
    rw [norm_pos_iff]
    exact sub_ne_zero.mpr (hfavoid q₀ hq₀)
  obtain ⟨g, hgdiff, hgclose⟩ :=
    exists_contDiff_dist_lt_on_compact hf hPcompact (half_pos hdpos)
  have hclose (q : ℂ) (hq : q ∈ P) :
      ‖g q - f q‖ < ‖f q - w‖ := by
    have hdist := hgclose q hq
    rw [Complex.dist_eq] at hdist
    have hmin : d q₀ ≤ d q := hq₀min hq
    dsimp [d] at hmin
    linarith
  refine ⟨g, hgdiff, ?_, hclose⟩
  intro q hq hgw
  have hbase : ‖f q - w‖ ≤ ‖g q - f q‖ := by
    rw [hgw]
    simp [norm_sub_rev]
  exact (not_lt_of_ge hbase) (hclose q hq)

/--
%%handwave
name:
  Boundary of an isolating disk avoids the target
statement:
  If $r$ isolates $z$ in the fiber $f^{-1}(w)$, then the image under $f$ of
  the circle $|\zeta-z|=r$ avoids $w$.
proof:
  A boundary point mapped to $w$ would equal $z$ by isolation, but a positive
  radius circle never passes through its center.
-/
theorem imageCircleLoop_ne_of_isFiberIsolatingRadius
    (f : ℂ → ℂ) (hf : Continuous f) (z w : ℂ) {r : ℝ}
    (hr : IsFiberIsolatingRadius f z w r) :
    ∀ t, imageCircleLoop f hf z r t ≠ w := by
  intro t htw
  have hcenter : circlePoint z r t = z :=
    hr.2 _ (by rw [dist_circlePoint_center z hr.1 t]) htw
  exact circlePoint_ne_center z hr.1 t hcenter

/--
%%handwave
name:
  Circle index is independent of isolating radius
statement:
  If $r_0$ and $r_1$ both isolate $z$ in the fiber $f^{-1}(w)$, then the
  indices of the two image circles around $w$ are equal.
proof:
  Every intermediate concentric circle lies inside the larger isolating disk
  and avoids the fiber. Radius-homotopy invariance of the circle index then
  applies.
-/
theorem planarCircleIndex_eq_of_isFiberIsolatingRadius
    (f : ℂ → ℂ) (hf : Continuous f) (z w : ℂ)
    {r₀ r₁ : ℝ} (hr₀ : IsFiberIsolatingRadius f z w r₀)
    (hr₁ : IsFiberIsolatingRadius f z w r₁) :
    planarCircleIndex f hf z w r₀ hr₀.1
        (imageCircleLoop_ne_of_isFiberIsolatingRadius f hf z w hr₀) =
      planarCircleIndex f hf z w r₁ hr₁.1
        (imageCircleLoop_ne_of_isFiberIsolatingRadius f hf z w hr₁) := by
  apply planarCircleIndex_eq_of_radial_homotopy
  intro s t htarget
  let rs : ℝ := (1 - (s : ℝ)) * r₀ + (s : ℝ) * r₁
  have hs0 : 0 ≤ (s : ℝ) := s.2.1
  have hs1 : (s : ℝ) ≤ 1 := s.2.2
  have hrs : 0 < rs := by
    by_cases hs : (s : ℝ) = 0
    · simp [rs, hs, hr₀.1]
    · have hspos : 0 < (s : ℝ) := lt_of_le_of_ne hs0 (Ne.symm hs)
      have hfirst : 0 ≤ (1 - (s : ℝ)) * r₀ :=
        mul_nonneg (sub_nonneg.mpr hs1) hr₀.1.le
      have hsecond : 0 < (s : ℝ) * r₁ := mul_pos hspos hr₁.1
      dsimp [rs]
      linarith
  have hpointNe : circlePoint z rs t ≠ z :=
    circlePoint_ne_center z hrs t
  apply hpointNe
  by_cases hle : r₀ ≤ r₁
  · apply hr₁.2 _ ?_ htarget
    rw [dist_circlePoint_center z hrs t]
    dsimp [rs]
    nlinarith
  · have hle' : r₁ ≤ r₀ := le_of_not_ge hle
    apply hr₀.2 _ ?_ htarget
    rw [dist_circlePoint_center z hrs t]
    dsimp [rs]
    nlinarith

/--
%%handwave
name:
  Local index at a point of a discrete fiber
statement:
  Let $f:\mathbb C\to\mathbb C$ be continuous, suppose $f(z)=w$, and suppose
  $f^{-1}(w)$ is discrete. The local index of $f$ at $z$ over $w$ is the
  winding number of the image of any sufficiently small positive circle
  isolating $z$ in that fiber.
-/
noncomputable def planarLocalIndex
    (f : ℂ → ℂ) (hf : Continuous f) (z w : ℂ) (hzw : f z = w)
    (hdiscrete : IsDiscrete {x : ℂ | f x = w}) : ℤ :=
  let hex := exists_isFiberIsolatingRadius_of_isDiscrete_fiber
    f z w hzw hdiscrete
  let r := Classical.choose hex
  let hr := Classical.choose_spec hex
  planarCircleIndex f hf z w r hr.1
    (imageCircleLoop_ne_of_isFiberIsolatingRadius f hf z w hr)

/--
%%handwave
name:
  Local index equals the index on every isolating circle
statement:
  For a continuous map with discrete fiber $f^{-1}(w)$ and $f(z)=w$, the
  local index at $z$ equals the winding number on every circle whose radius
  isolates $z$ in that fiber.
proof:
  Compare the chosen isolating radius in the definition with the given one;
  circle index is independent of the isolating radius.
-/
theorem planarLocalIndex_eq_planarCircleIndex
    (f : ℂ → ℂ) (hf : Continuous f) (z w : ℂ) (hzw : f z = w)
    (hdiscrete : IsDiscrete {x : ℂ | f x = w})
    {r : ℝ} (hr : IsFiberIsolatingRadius f z w r) :
    planarLocalIndex f hf z w hzw hdiscrete =
      planarCircleIndex f hf z w r hr.1
        (imageCircleLoop_ne_of_isFiberIsolatingRadius f hf z w hr) := by
  let hex := exists_isFiberIsolatingRadius_of_isDiscrete_fiber
    f z w hzw hdiscrete
  let r₀ := Classical.choose hex
  let hr₀ : IsFiberIsolatingRadius f z w r₀ := Classical.choose_spec hex
  change planarCircleIndex f hf z w r₀ hr₀.1
      (imageCircleLoop_ne_of_isFiberIsolatingRadius f hf z w hr₀) = _
  exact planarCircleIndex_eq_of_isFiberIsolatingRadius f hf z w hr₀ hr

/--
%%handwave
name:
  Sum of local indices over a finite planar fiber
statement:
  Let $f:\mathbb C\to\mathbb C$ be continuous and suppose the fiber
  $f^{-1}(w)$ is finite and discrete. Its total fiber index is
  $$
    \sum_{z\in f^{-1}(w)} i(f,z;w),
  $$
  the finite sum of the integer local indices over all preimages of $w$.
-/
noncomputable def planarFiberIndexSum
    (f : ℂ → ℂ) (hf : Continuous f) (w : ℂ)
    (hdiscrete : IsDiscrete {z : ℂ | f z = w})
    (hfinite : {z : ℂ | f z = w}.Finite) : ℤ := by
  letI : Fintype {z : ℂ | f z = w} := hfinite.fintype
  exact ∑ z : {z : ℂ | f z = w},
    planarLocalIndex f hf z w z.2 hdiscrete

/--
%%handwave
name:
  A circle enclosing a fiber avoids the target
statement:
  Let $r>0$. If every point of $f^{-1}(w)$ lies in the open disk
  $B(z,r)$, then the image of the boundary circle $|\zeta-z|=r$ avoids $w$.
proof:
  A boundary point mapped to $w$ would belong to the fiber and hence have
  distance strictly less than $r$ from $z$, whereas every boundary point has
  distance exactly $r$.
-/
theorem imageCircleLoop_ne_of_fiber_subset_ball
    (f : ℂ → ℂ) (hf : Continuous f) (z w : ℂ) {r : ℝ} (hr : 0 < r)
    (hfiber : {x : ℂ | f x = w} ⊆ Metric.ball z r) :
    ∀ t, imageCircleLoop f hf z r t ≠ w := by
  intro t htarget
  have hmem : circlePoint z r t ∈ Metric.ball z r := hfiber htarget
  rw [Metric.mem_ball, dist_circlePoint_center z hr t] at hmem
  exact (lt_irrefl r) hmem

/--
%%handwave
name:
  Target avoidance on the outer boundary of a perforated disk
statement:
  Let $g:\mathbb C\to\mathbb C$ avoid $w$ on a perforated disk whose inner
  closed disks lie strictly inside $B(z,r)$, with $r>0$. Then the image under
  $g$ of the outer circle $\partial B(z,r)$ avoids $w$.
proof:
  Every outer-circle point belongs to the perforated disk, where the assumed
  target avoidance applies.
-/
theorem imageCircleLoop_ne_of_avoids_perforatedClosedDisk_outer
    {ι : Type*} (g : ℂ → ℂ) (hg : Continuous g) (z w : ℂ)
    {r : ℝ} (hr : 0 < r) (c : ι → ℂ) (ρ : ι → ℝ)
    (hinside : ∀ i, Metric.closedBall (c i) (ρ i) ⊆ Metric.ball z r)
    (havoid : ∀ q ∈ perforatedClosedDisk z r c ρ, g q ≠ w) :
    ∀ t, imageCircleLoop g hg z r t ≠ w := by
  intro t
  exact havoid _
    (circlePoint_mem_perforatedClosedDisk_outer z hr c ρ hinside t)

/--
%%handwave
name:
  Target avoidance on the inner boundaries of a perforated disk
statement:
  Let $g:\mathbb C\to\mathbb C$ avoid $w$ on a perforated disk with
  positive-radius, pairwise disjoint inner closed disks contained in the
  outer open disk. Then the image of every positively oriented inner boundary
  circle avoids $w$.
proof:
  Each inner boundary circle belongs to the perforated disk, so target
  avoidance there applies.
-/
theorem imageCircleLoop_ne_of_avoids_perforatedClosedDisk_inner
    {ι : Type*} (g : ℂ → ℂ) (hg : Continuous g) (z w : ℂ) (r : ℝ)
    (c : ι → ℂ) (ρ : ι → ℝ) (hρpos : ∀ i, 0 < ρ i)
    (hpair : ∀ i j, i ≠ j →
      Disjoint (Metric.closedBall (c i) (ρ i))
        (Metric.closedBall (c j) (ρ j)))
    (hinside : ∀ i, Metric.closedBall (c i) (ρ i) ⊆ Metric.ball z r)
    (havoid : ∀ q ∈ perforatedClosedDisk z r c ρ, g q ≠ w)
    (i : ι) :
    ∀ t, imageCircleLoop g hg (c i) (ρ i) t ≠ w := by
  intro t
  exact havoid _
    (circlePoint_mem_perforatedClosedDisk_inner z r c ρ
      hρpos hpair hinside i t)

/--
%%handwave
name:
  Nowhere-zero filling of a vortex-corrected inner boundary
statement:
  Let $g$ avoid $w$ on a disk with finitely many disjoint circular holes.
  Write $n_i$ for the index of $g-w$ on the $i$th positive inner boundary.
  For every hole $j$, the corrected boundary loop
  $$
    t\longmapsto
      \bigl(g(c_j+\rho_j e^{2\pi i t})-w\bigr)
      \prod_i
        \bigl(c_j+\rho_j e^{2\pi i t}-c_i\bigr)^{-n_i}
  $$
  extends from the unit circle to a continuous map
  $\mathbb C\to\mathbb C\setminus\{0\}$.
proof:
  The coordinate factor centered at $c_j$ has logarithmic increment
  $2\pi i$ on the $j$th boundary, while every other coordinate factor has
  increment zero there because its center lies outside the $j$th disk.
  The product and integer-power laws therefore make the corrected loop have
  zero logarithmic increment. Apply the nowhere-zero filling theorem for
  zero-increment loops.
-/
theorem exists_punctured_extension_of_corrected_inner_boundary
    {ι : Type*} [Fintype ι]
    (g : ℂ → ℂ) (hg : Continuous g) (z w : ℂ)
    (r : ℝ) (c : ι → ℂ) (ρ : ι → ℝ)
    (hρpos : ∀ i, 0 < ρ i)
    (hpair : ∀ i j, i ≠ j →
      Disjoint (Metric.closedBall (c i) (ρ i))
        (Metric.closedBall (c j) (ρ j)))
    (hinside : ∀ i, Metric.closedBall (c i) (ρ i) ⊆
      Metric.ball z r)
    (havoid : ∀ q ∈ perforatedClosedDisk z r c ρ,
      g q ≠ w)
    (j : ι) :
    ∃ F : C(ℂ, PuncturedComplex),
      ∀ t : unitInterval,
        F (Complex.exp
          (((2 * Real.pi * (t : ℝ) : ℝ) : ℂ) *
            Complex.I)) =
          (⟨(g (circlePoint (c j) (ρ j) t) - w) *
              ∏ i : ι,
                (circlePoint (c j) (ρ j) t - c i) ^
                  (-(planarCircleIndex g hg (c i) w (ρ i)
                    (hρpos i)
                    (imageCircleLoop_ne_of_avoids_perforatedClosedDisk_inner
                      g hg z w r c ρ hρpos hpair hinside
                        havoid i))),
            mul_ne_zero
              (sub_ne_zero.mpr
                (imageCircleLoop_ne_of_avoids_perforatedClosedDisk_inner
                  g hg z w r c ρ hρpos hpair hinside
                    havoid j t))
              (Finset.prod_ne_zero_iff.mpr
                (fun i _hi ↦ zpow_ne_zero _
                  (by
                    by_cases hij : i = j
                    · subst i
                      exact sub_ne_zero.mpr
                        (circlePoint_ne_center (c j)
                          (hρpos j) t)
                    · have hsum :
                          ρ j + ρ i <
                            dist (c j) (c i) :=
                        (disjoint_closedBall_closedBall_iff
                          (hρpos j).le (hρpos i).le).mp
                            (hpair j i
                              (fun hji ↦ hij hji.symm))
                      have hfar :
                          ρ j < dist (c i) (c j) := by
                        rw [dist_comm]
                        linarith [hρpos i]
                      exact sub_ne_zero.mpr
                        (complexCircleLoop_ne_of_radius_lt_dist
                          (c j) (c i) (hρpos j)
                            hfar t))))⟩ :
            PuncturedComplex) := by
  classical
  let hinner (i : ι) :=
    imageCircleLoop_ne_of_avoids_perforatedClosedDisk_inner
      g hg z w r c ρ hρpos hpair hinside havoid i
  let n : ι → ℤ := fun i ↦
    planarCircleIndex g hg (c i) w (ρ i)
      (hρpos i) (hinner i)
  have hfar (i : ι) (hij : i ≠ j) :
      ρ j < dist (c i) (c j) := by
    have hsum :
        ρ j + ρ i < dist (c j) (c i) :=
      (disjoint_closedBall_closedBall_iff
        (hρpos j).le (hρpos i).le).mp
          (hpair j i (fun hji ↦ hij hji.symm))
    rw [dist_comm]
    linarith [hρpos i]
  have hcoord (i : ι) :
      ∀ t, complexCircleLoop (c j) (ρ j) t ≠
        c i := by
    by_cases hij : i = j
    · subst i
      exact complexCircleLoop_ne_center
        (c j) (hρpos j)
    · exact complexCircleLoop_ne_of_radius_lt_dist
        (c j) (c i) (hρpos j) (hfar i hij)
  let coordStart : ι → PuncturedComplex := fun i ↦
    ⟨complexCircleLoop (c j) (ρ j) 0 - c i,
      sub_ne_zero.mpr (hcoord i 0)⟩
  let coord : ∀ i, Path (coordStart i) (coordStart i) :=
    fun i ↦ puncturedPathAround
      (complexCircleLoop (c j) (ρ j)) (c i)
        (hcoord i) (complexCircleLoop_one_eq_zero _ _)
  have hcoordInc (i : ι) :
      puncturedPathLogIncrement (coord i) =
        if i = j then
          2 * Real.pi * Complex.I else 0 := by
    by_cases hij : i = j
    · subst i
      rw [if_pos rfl]
      simpa [coord] using
        puncturedPathAround_complexCircleLoop_logIncrement_of_dist_lt_radius
          (c j) (c j) (hρpos j)
            (by simpa using hρpos j)
    · rw [if_neg hij]
      simpa [coord] using
        puncturedPathAround_complexCircleLoop_logIncrement_eq_zero_of_radius_lt_dist
          (c j) (c i) (hρpos j) (hfar i hij)
  let factorStart : ι → PuncturedComplex := fun i ↦
    ⟨(coordStart i : ℂ) ^ (-(n i)),
      zpow_ne_zero _ (coordStart i).2⟩
  let factor :
      ∀ i, Path (factorStart i) (factorStart i) :=
    fun i ↦ puncturedPathZPow (coord i) (-(n i))
  have hfactorInc (i : ι) :
      puncturedPathLogIncrement (factor i) =
        (-(n i) : ℂ) *
          (if i = j then
            2 * Real.pi * Complex.I else 0) := by
    change puncturedPathLogIncrement
      (puncturedPathZPow (coord i) (-(n i))) = _
    rw [puncturedPathLogIncrement_zpow,
      hcoordInc]
    push_cast
    rfl
  let factors :=
    puncturedPathFinsetProd
      Finset.univ factorStart factor
  have hfactorsInc :
      puncturedPathLogIncrement factors =
        (-(n j) : ℂ) *
          (2 * Real.pi * Complex.I) := by
    change puncturedPathLogIncrement
      (puncturedPathFinsetProd Finset.univ
        factorStart factor) = _
    rw [puncturedPathLogIncrement_finsetProd]
    simp_rw [hfactorInc]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i hi hij
      simp [hij]
    · simp
  let baseStart : PuncturedComplex :=
    ⟨imageCircleLoop g hg (c j) (ρ j) 0 - w,
      sub_ne_zero.mpr (hinner j 0)⟩
  let base : Path baseStart baseStart :=
    puncturedPathAround
      (imageCircleLoop g hg (c j) (ρ j)) w
        (hinner j)
        (imageCircleLoop_one_eq_zero
          g hg (c j) (ρ j))
  have hbaseInc :
      puncturedPathLogIncrement base =
        (n j : ℂ) *
          (2 * Real.pi * Complex.I) := by
    change puncturedPathLogIncrement
      (puncturedPathAround
        (imageCircleLoop g hg (c j) (ρ j)) w
          (hinner j)
          (imageCircleLoop_one_eq_zero
            g hg (c j) (ρ j))) = _
    rw [puncturedPathAround_logIncrement_eq_windingNumber_mul]
    rfl
  let corrected :=
    puncturedPathPointwiseMul base factors
  have hcorrected :
      puncturedPathLogIncrement corrected = 0 := by
    change puncturedPathLogIncrement
      (puncturedPathPointwiseMul base factors) = 0
    rw [puncturedPathLogIncrement_pointwiseMul,
      hbaseInc, hfactorsInc]
    ring
  obtain ⟨F, hF⟩ :=
    exists_punctured_extension_of_logIncrement_eq_zero
      corrected hcorrected
  refine ⟨F, ?_⟩
  intro t
  rw [hF t]
  apply Subtype.ext
  change
    (g (circlePoint (c j) (ρ j) t) - w) *
        (∏ i : ι,
          (circlePoint (c j) (ρ j) t - c i) ^
            (-(n i))) =
      (g (circlePoint (c j) (ρ j) t) - w) *
        ∏ i : ι,
          (circlePoint (c j) (ρ j) t - c i) ^
            (-(planarCircleIndex g hg
              (c i) w (ρ i) (hρpos i) (hinner i)))
  rfl

/--
%%handwave
name:
  Filling all holes after vortex correction
statement:
  Let $g$ avoid $w$ on the perforated closed disk
  $$
    P=\overline B(z,r)\setminus
      \bigcup_i B(c_i,\rho_i),
  $$
  where the positive-radius closed inner disks are pairwise disjoint and
  contained in the outer disk. If $n_i$ is the index of $g-w$ on the $i$th
  positive inner boundary, then
  $$
    q\longmapsto
      (g(q)-w)\prod_i(q-c_i)^{-n_i}
  $$
  extends from $P$ to a continuous map
  $\overline B(z,r)\to\mathbb C\setminus\{0\}$.
proof:
  Each corrected inner boundary has a nowhere-zero filling. Rescale that
  filling from the unit disk to the corresponding closed inner disk. These
  maps agree with the corrected map on the boundary circles, and different
  closed inner disks are disjoint. Glue the corrected map and all rescaled
  fillings over this finite closed cover of the outer closed disk.
-/
theorem
    exists_punctured_extension_of_vortexCorrected_perforatedClosedDisk
    {ι : Type*} [Fintype ι]
    (g : ℂ → ℂ) (hg : Continuous g) (z w : ℂ)
    (r : ℝ) (c : ι → ℂ) (ρ : ι → ℝ)
    (hρpos : ∀ i, 0 < ρ i)
    (hpair : ∀ i j, i ≠ j →
      Disjoint (Metric.closedBall (c i) (ρ i))
        (Metric.closedBall (c j) (ρ j)))
    (hinside : ∀ i, Metric.closedBall (c i) (ρ i) ⊆
      Metric.ball z r)
    (havoid : ∀ q ∈ perforatedClosedDisk z r c ρ,
      g q ≠ w) :
    let P := perforatedClosedDisk z r c ρ
    let hinner (i : ι) :=
      imageCircleLoop_ne_of_avoids_perforatedClosedDisk_inner
        g hg z w r c ρ hρpos hpair hinside havoid i
    let n : ι → ℤ := fun i ↦
      planarCircleIndex g hg (c i) w (ρ i)
        (hρpos i) (hinner i)
    ∃ F : C(Metric.closedBall z r,
        PuncturedComplex),
      ∀ q : P,
        F ⟨q, q.2.1⟩ =
          (⟨(g q - w) *
              ∏ i : ι, ((q : ℂ) - c i) ^ (-(n i)),
            mul_ne_zero
              (sub_ne_zero.mpr (havoid q q.2))
              (Finset.prod_ne_zero_iff.mpr
                (fun i _hi ↦ zpow_ne_zero _
                  (by
                    apply sub_ne_zero.mpr
                    intro hqi
                    have hcenter :
                        (q : ℂ) ∈
                          Metric.ball (c i) (ρ i) := by
                      rw [hqi, Metric.mem_ball, dist_self]
                      exact hρpos i
                    exact q.2.2
                      (Set.mem_iUnion.mpr
                        ⟨i, hcenter⟩))))⟩ :
            PuncturedComplex) := by
  classical
  let P := perforatedClosedDisk z r c ρ
  let hinner (i : ι) :=
    imageCircleLoop_ne_of_avoids_perforatedClosedDisk_inner
      g hg z w r c ρ hρpos hpair hinside havoid i
  let n : ι → ℤ := fun i ↦
    planarCircleIndex g hg (c i) w (ρ i)
      (hρpos i) (hinner i)
  have hcoord (q : P) (i : ι) :
      (q : ℂ) - c i ≠ 0 := by
    apply sub_ne_zero.mpr
    intro hqi
    have hcenter :
        (q : ℂ) ∈ Metric.ball (c i) (ρ i) := by
      rw [hqi, Metric.mem_ball, dist_self]
      exact hρpos i
    exact q.2.2
      (Set.mem_iUnion.mpr ⟨i, hcenter⟩)
  let corrected : C(P, PuncturedComplex) :=
    ⟨fun q ↦
      ⟨(g q - w) *
          ∏ i : ι, ((q : ℂ) - c i) ^ (-(n i)),
        mul_ne_zero
          (sub_ne_zero.mpr (havoid q q.2))
          (Finset.prod_ne_zero_iff.mpr
            (fun i _hi ↦ zpow_ne_zero _
              (hcoord q i)))⟩,
      Continuous.subtype_mk
        ((hg.comp continuous_subtype_val).sub
          continuous_const |>.mul
            (continuous_finsetProd _ fun i _hi ↦
              ((continuous_subtype_val.sub
                continuous_const).zpow₀ (-(n i))
                  (fun q ↦
                    Or.inl (hcoord q i))))) _⟩
  let hex (j : ι) :=
    exists_punctured_extension_of_corrected_inner_boundary
      g hg z w r c ρ hρpos hpair hinside
        havoid j
  let fill (j : ι) : C(ℂ, PuncturedComplex) :=
    Classical.choose (hex j)
  have hfill (j : ι) :=
    Classical.choose_spec (hex j)
  let fillBall (j : ι) :
      C(Metric.closedBall (c j) (ρ j),
        PuncturedComplex) :=
    fill j |>.comp
      ⟨fun q ↦
        ((q : ℂ) - c j) / (ρ j : ℂ), by
        fun_prop⟩
  have hboundary (j : ι) (q : ℂ)
      (hqP : q ∈ P)
      (hqB : q ∈ Metric.closedBall (c j) (ρ j)) :
      fillBall j ⟨q, hqB⟩ =
        corrected ⟨q, hqP⟩ := by
    have hnotBall :
        q ∉ Metric.ball (c j) (ρ j) := by
      intro hq
      exact hqP.2
        (Set.mem_iUnion.mpr ⟨j, hq⟩)
    have hdist : dist q (c j) = ρ j := by
      rw [Metric.mem_closedBall] at hqB
      rw [Metric.mem_ball] at hnotBall
      exact le_antisymm hqB (not_lt.mp hnotBall)
    obtain ⟨t, hqt⟩ :=
      exists_circlePoint_eq_of_dist_eq
        (c j) q (hρpos j) hdist
    have harg :
        (q - c j) / (ρ j : ℂ) =
          Complex.exp
            (((2 * Real.pi * (t : ℝ) : ℝ) : ℂ) *
              Complex.I) := by
      rw [← hqt, circlePoint, add_sub_cancel_left]
      field_simp [Complex.ofReal_ne_zero.mpr
        (ne_of_gt (hρpos j))]
    apply Subtype.ext
    change
      (fill j ((q - c j) / (ρ j : ℂ)) : ℂ) =
        (g q - w) *
          ∏ i : ι, (q - c i) ^ (-(n i))
    rw [harg]
    have hf := hfill j t
    rw [hf]
    change
      (g (circlePoint (c j) (ρ j) t) - w) *
          ∏ i : ι,
            (circlePoint (c j) (ρ j) t - c i) ^
              (-(planarCircleIndex g hg
                (c i) w (ρ i) (hρpos i)
                  (hinner i))) =
        (g q - w) *
          ∏ i : ι, (q - c i) ^ (-(n i))
    change
      (g (circlePoint (c j) (ρ j) t) - w) *
          ∏ i : ι,
            (circlePoint (c j) (ρ j) t - c i) ^
              (-(n i)) =
        (g q - w) *
          ∏ i : ι, (q - c i) ^ (-(n i))
    rw [hqt]
  let S : Option ι → Set ℂ
    | none => P
    | some i => Metric.closedBall (c i) (ρ i)
  let localMap :
      ∀ k, C(S k, PuncturedComplex)
    | none => corrected
    | some i => fillBall i
  have hSclosed (k : Option ι) : IsClosed (S k) := by
    cases k with
    | none =>
        exact (isCompact_perforatedClosedDisk
          z r c ρ).isClosed
    | some i =>
        exact Metric.isClosed_closedBall
  have hlocalCompat :
      ∀ i j q (hqi : q ∈ S i) (hqj : q ∈ S j),
        localMap i ⟨q, hqi⟩ =
          localMap j ⟨q, hqj⟩ := by
    intro i j q hqi hqj
    cases i with
    | none =>
        cases j with
        | none => rfl
        | some j =>
            exact (hboundary j q hqi hqj).symm
    | some i =>
        cases j with
        | none =>
            exact hboundary i q hqj hqi
        | some j =>
            by_cases hij : i = j
            · subst j
              rfl
            · exact False.elim
                ((hpair i j hij).le_bot
                  ⟨hqi, hqj⟩)
  obtain ⟨G, hG⟩ :=
    exists_continuousMap_iUnion_of_finite_closed
      S hSclosed localMap hlocalCompat
  have hcover (q : Metric.closedBall z r) :
      (q : ℂ) ∈ ⋃ k, S k := by
    by_cases hq : ∃ i, (q : ℂ) ∈
        Metric.closedBall (c i) (ρ i)
    · obtain ⟨i, hi⟩ := hq
      exact Set.mem_iUnion.mpr ⟨some i, hi⟩
    · apply Set.mem_iUnion.mpr
      refine ⟨none, q.2, ?_⟩
      intro hball
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hball
      exact hq
        ⟨i, Metric.ball_subset_closedBall hi⟩
  let e :
      C(Metric.closedBall z r, ⋃ k, S k) :=
    ⟨fun q ↦ ⟨q, hcover q⟩, by fun_prop⟩
  let F :
      C(Metric.closedBall z r, PuncturedComplex) :=
    G.comp e
  refine ⟨F, ?_⟩
  intro q
  change F ⟨q, q.2.1⟩ = corrected q
  have hGq := hG none (q : ℂ) q.2
  change
    G ⟨q, Set.mem_iUnion.mpr ⟨none, q.2⟩⟩ =
      corrected q at hGq
  simpa only [F, e, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk] using hGq

/--
%%handwave
name:
  Logarithmic increment of a constant path
statement:
  Every constant path in $\mathbb C\setminus\{0\}$ has logarithmic
  increment zero.
proof:
  Normalize the path to the constant loop at $1$. Its winding number is
  zero, so the winding-number formula for logarithmic increments gives the
  result.
-/
theorem puncturedPathLogIncrement_refl
    (a : PuncturedComplex) :
    puncturedPathLogIncrement (Path.refl a) = 0 := by
  rw [puncturedPathLogIncrement_eq_windingNumber_mul]
  have hn :
      normalizedPuncturedPathLoop (Path.refl a) =
        Path.refl
          (⟨1, one_ne_zero⟩ : PuncturedComplex) := by
    apply Path.ext
    funext t
    apply Subtype.ext
    simp [normalizedPuncturedPathLoop, a.2]
  rw [hn, puncturedLoopWindingNumber_refl]
  norm_num

/--
%%handwave
name:
  Logarithmic increment is unchanged by endpoint casts
statement:
  If a path $\gamma$ in $\mathbb C\setminus\{0\}$ is regarded as a path
  between propositionally equal choices of its endpoints, its logarithmic
  increment is unchanged.
proof:
  After substituting the endpoint equalities, the cast path is definitionally
  the original path.
-/
theorem puncturedPathLogIncrement_cast
    {a b a' b' : PuncturedComplex}
    (γ : Path a b) (ha : a' = a) (hb : b' = b) :
    puncturedPathLogIncrement (γ.cast ha hb) =
      puncturedPathLogIncrement γ := by
  subst a'
  subst b'
  rfl

/--
%%handwave
name:
  Boundary path of a punctured-plane map on a closed disk
statement:
  Let $r>0$ and let
  $F:\overline B(z,r)\to\mathbb C\setminus\{0\}$ be continuous. Its
  positively oriented boundary path is
  $$
    t\longmapsto F\bigl(z+r e^{2\pi i t}\bigr).
  $$
  This is a closed path in the punctured plane.
-/
noncomputable def puncturedClosedBallBoundaryPath
    (z : ℂ) {r : ℝ} (hr : 0 < r)
    (F : C(Metric.closedBall z r, PuncturedComplex)) :
    Path
      (F ⟨circlePoint z r 0, by
        rw [Metric.mem_closedBall,
          dist_circlePoint_center z hr]⟩)
      (F ⟨circlePoint z r 0, by
        rw [Metric.mem_closedBall,
          dist_circlePoint_center z hr]⟩) :=
  Path.mk
    (F.comp
      ⟨fun t ↦
        ⟨circlePoint z r t, by
          rw [Metric.mem_closedBall,
            dist_circlePoint_center z hr]⟩, by
        apply Continuous.subtype_mk
        dsimp [circlePoint]
        exact continuous_const.add
          (continuous_const.mul
            (Complex.continuous_exp.comp
              (by fun_prop)))⟩)
    rfl
    (by
      change F _ = F _
      congr 1
      apply Subtype.ext
      exact circlePoint_one z r |>.trans
        (circlePoint_zero z r).symm)

/--
%%handwave
name:
  Zero boundary increment for a punctured-plane disk map
statement:
  If $r>0$ and
  $F:\overline B(z,r)\to\mathbb C\setminus\{0\}$ is continuous, then
  $$
    \Delta\log\bigl(t\mapsto
      F(z+r e^{2\pi i t})\bigr)=0.
  $$
proof:
  Contract the boundary circle radially to the center of the disk. The
  logarithmic-increment identity on the boundary of the resulting parameter
  square says that the increment on the outer circle equals the increment
  on the constant center path, which is zero.
-/
theorem puncturedClosedBallBoundaryPath_logIncrement_eq_zero
    (z : ℂ) {r : ℝ} (hr : 0 < r)
    (F : C(Metric.closedBall z r, PuncturedComplex)) :
    puncturedPathLogIncrement
      (puncturedClosedBallBoundaryPath z hr F) = 0 := by
  let radius : unitInterval → ℝ :=
    fun s ↦ (s : ℝ) * r
  have hradius_nonneg (s : unitInterval) :
      0 ≤ radius s := mul_nonneg s.2.1 hr.le
  have hradius_le (s : unitInterval) :
      radius s ≤ r :=
    mul_le_of_le_one_left hr.le s.2.2
  let Q : C(unitInterval × unitInterval,
      Metric.closedBall z r) :=
    ⟨fun x ↦
      ⟨circlePoint z (radius x.1) x.2, by
        rw [Metric.mem_closedBall, Complex.dist_eq,
          circlePoint, add_sub_cancel_left, norm_mul,
          Complex.norm_real,
          Real.norm_of_nonneg (hradius_nonneg x.1),
          Complex.norm_exp_ofReal_mul_I, mul_one]
        exact hradius_le x.1⟩, by
      dsimp [circlePoint, radius]
      fun_prop⟩
  let H : C(unitInterval × unitInterval,
      PuncturedComplex) := F.comp Q
  let B := puncturedSquareHorizontalPath H 0
  let T := puncturedSquareHorizontalPath H 1
  let L := puncturedSquareVerticalPath H 0
  let R := puncturedSquareVerticalPath H 1
  have h0 : H (0, 0) = H (0, 1) := by
    change F (Q (0, 0)) = F (Q (0, 1))
    apply congrArg F
    apply Subtype.ext
    simp [Q, radius, circlePoint]
  have h1 : H (1, 0) = H (1, 1) := by
    change F (Q (1, 0)) = F (Q (1, 1))
    apply congrArg F
    apply Subtype.ext
    simpa [Q, radius] using
      (circlePoint_zero z r).trans
        (circlePoint_one z r).symm
  have hhorizontal :
      B = T.cast h0 h1 := by
    apply Path.ext
    funext s
    change F (Q (s, 0)) = F (Q (s, 1))
    apply congrArg F
    apply Subtype.ext
    exact (circlePoint_zero z (radius s)).trans
      (circlePoint_one z (radius s)).symm
  have hleft :
      L.cast rfl h0 =
        Path.refl (H (0, 0)) := by
    apply Path.ext
    funext t
    change F (Q (0, t)) = H (0, 0)
    change F (Q (0, t)) = F (Q (0, 0))
    apply congrArg F
    apply Subtype.ext
    simp [Q, radius, circlePoint]
  let p0 : Metric.closedBall z r :=
    ⟨circlePoint z r 0, by
      rw [Metric.mem_closedBall,
        dist_circlePoint_center z hr]⟩
  have hb0 : F p0 = H (1, 0) := by
    change F p0 = F (Q (1, 0))
    apply congrArg F
    apply Subtype.ext
    simp [p0, Q, radius]
  have hb1 : F p0 = H (1, 1) := by
    change F p0 = F (Q (1, 1))
    apply congrArg F
    apply Subtype.ext
    simp [p0, Q, radius, circlePoint_one,
      circlePoint_zero]
  have hright :
      R.cast hb0 hb1 =
        puncturedClosedBallBoundaryPath z hr F := by
    apply Path.ext
    funext t
    change F (Q (1, t)) =
      puncturedClosedBallBoundaryPath z hr F t
    change F (Q (1, t)) =
      F ⟨circlePoint z r t, _⟩
    apply congrArg F
    apply Subtype.ext
    simp [Q, radius]
  have hBinc :
      puncturedPathLogIncrement B =
        puncturedPathLogIncrement T := by
    rw [hhorizontal, puncturedPathLogIncrement_cast]
  have hLinc :
      puncturedPathLogIncrement L = 0 := by
    rw [← puncturedPathLogIncrement_cast L rfl h0,
      hleft, puncturedPathLogIncrement_refl]
  have hRinc :
      puncturedPathLogIncrement R =
        puncturedPathLogIncrement
          (puncturedClosedBallBoundaryPath z hr F) := by
    rw [← puncturedPathLogIncrement_cast R hb0 hb1,
      hright]
  have hsquare :=
    puncturedPathLogIncrement_square_boundary H
  change
    puncturedPathLogIncrement B +
        puncturedPathLogIncrement R =
      puncturedPathLogIncrement L +
        puncturedPathLogIncrement T at hsquare
  rw [hBinc, hLinc, hRinc] at hsquare
  linear_combination hsquare

/--
%%handwave
name:
  Smooth boundary additivity on a perforated disk
statement:
  Let $g:\mathbb C\to\mathbb C$ be smooth and avoid $w$ on
  $$
    P=\overline B(z,r)\setminus\bigcup_{i\in I}B(c_i,\rho_i),
  $$
  where $I$ is finite, $r>0$, the radii $\rho_i$ are positive, and the inner
  closed disks are pairwise disjoint and contained in $B(z,r)$. Then
  $$
    I(g,\partial B(z,r);w)
      =\sum_{i\in I} I(g,\partial B(c_i,\rho_i);w).
  $$
proof:
  If $n_i$ is the index on the $i$th inner circle, divide $g-w$ by
  $\prod_i(q-c_i)^{n_i}$. The [product law for logarithmic increments](lean:JJMath.Quasiconformal.puncturedPathLogIncrement_pointwiseMul) and [integer-power law](lean:JJMath.Quasiconformal.puncturedPathLogIncrement_zpow) make every corrected inner boundary loop have zero increment. [Fill each such loop by a nowhere-zero map](lean:JJMath.Quasiconformal.exists_punctured_extension_of_logIncrement_eq_zero) and paste the fillings across the disjoint holes. The corrected map then avoids zero on the full outer disk, so its outer index is zero. Each coordinate vortex has outer index one, which gives the stated sum.
-/
theorem planarCircleIndex_eq_sum_of_contDiff_of_avoids_perforatedClosedDisk
    {ι : Type*} [Fintype ι]
    (g : ℂ → ℂ) (hgdiff : ContDiff ℝ ∞ g) (z w : ℂ)
    {r : ℝ} (hr : 0 < r) (c : ι → ℂ) (ρ : ι → ℝ)
    (hρpos : ∀ i, 0 < ρ i)
    (hpair : ∀ i j, i ≠ j →
      Disjoint (Metric.closedBall (c i) (ρ i))
        (Metric.closedBall (c j) (ρ j)))
    (hinside : ∀ i, Metric.closedBall (c i) (ρ i) ⊆ Metric.ball z r)
    (havoid : ∀ q ∈ perforatedClosedDisk z r c ρ, g q ≠ w) :
    planarCircleIndex g hgdiff.continuous z w r hr
        (imageCircleLoop_ne_of_avoids_perforatedClosedDisk_outer
          g hgdiff.continuous z w hr c ρ hinside havoid) =
      ∑ i : ι,
        planarCircleIndex g hgdiff.continuous (c i) w (ρ i) (hρpos i)
          (imageCircleLoop_ne_of_avoids_perforatedClosedDisk_inner
            g hgdiff.continuous z w r c ρ hρpos hpair hinside havoid i) := by
  classical
  let hg : Continuous g := hgdiff.continuous
  let houter :=
    imageCircleLoop_ne_of_avoids_perforatedClosedDisk_outer
      g hg z w hr c ρ hinside havoid
  let hinner (i : ι) :=
    imageCircleLoop_ne_of_avoids_perforatedClosedDisk_inner
      g hg z w r c ρ hρpos hpair hinside havoid i
  let m : ℤ := planarCircleIndex g hg z w r hr houter
  let n : ι → ℤ := fun i ↦
    planarCircleIndex g hg (c i) w (ρ i)
      (hρpos i) (hinner i)
  obtain ⟨F, hF⟩ :=
    exists_punctured_extension_of_vortexCorrected_perforatedClosedDisk
      g hg z w r c ρ hρpos hpair hinside havoid
  have hFinc :
      puncturedPathLogIncrement
        (puncturedClosedBallBoundaryPath z hr F) = 0 :=
    puncturedClosedBallBoundaryPath_logIncrement_eq_zero
      z hr F
  have hcinside (i : ι) : dist (c i) z < r := by
    rw [← Metric.mem_ball]
    apply hinside i
    rw [Metric.mem_closedBall, dist_self]
    exact (hρpos i).le
  have hcoord (i : ι) :
      ∀ t, complexCircleLoop z r t ≠ c i :=
    complexCircleLoop_ne_of_dist_lt_radius
      z (c i) hr (hcinside i)
  let coordStart : ι → PuncturedComplex := fun i ↦
    ⟨complexCircleLoop z r 0 - c i,
      sub_ne_zero.mpr (hcoord i 0)⟩
  let coord : ∀ i, Path (coordStart i) (coordStart i) :=
    fun i ↦ puncturedPathAround
      (complexCircleLoop z r) (c i)
        (hcoord i) (complexCircleLoop_one_eq_zero z r)
  have hcoordInc (i : ι) :
      puncturedPathLogIncrement (coord i) =
        2 * Real.pi * Complex.I := by
    simpa [coord] using
      puncturedPathAround_complexCircleLoop_logIncrement_of_dist_lt_radius
        z (c i) hr (hcinside i)
  let factorStart : ι → PuncturedComplex := fun i ↦
    ⟨(coordStart i : ℂ) ^ (-(n i)),
      zpow_ne_zero _ (coordStart i).2⟩
  let factor :
      ∀ i, Path (factorStart i) (factorStart i) :=
    fun i ↦ puncturedPathZPow (coord i) (-(n i))
  have hfactorInc (i : ι) :
      puncturedPathLogIncrement (factor i) =
        (-(n i) : ℂ) *
          (2 * Real.pi * Complex.I) := by
    change puncturedPathLogIncrement
      (puncturedPathZPow (coord i) (-(n i))) = _
    rw [puncturedPathLogIncrement_zpow, hcoordInc]
    push_cast
    rfl
  let factors :=
    puncturedPathFinsetProd
      Finset.univ factorStart factor
  have hfactorsInc :
      puncturedPathLogIncrement factors =
        ∑ i : ι,
          (-(n i) : ℂ) *
            (2 * Real.pi * Complex.I) := by
    change puncturedPathLogIncrement
      (puncturedPathFinsetProd Finset.univ
        factorStart factor) = _
    rw [puncturedPathLogIncrement_finsetProd]
    simp_rw [hfactorInc]
  let baseStart : PuncturedComplex :=
    ⟨imageCircleLoop g hg z r 0 - w,
      sub_ne_zero.mpr (houter 0)⟩
  let base : Path baseStart baseStart :=
    puncturedPathAround
      (imageCircleLoop g hg z r) w
        houter (imageCircleLoop_one_eq_zero g hg z r)
  have hbaseInc :
      puncturedPathLogIncrement base =
        (m : ℂ) *
          (2 * Real.pi * Complex.I) := by
    change puncturedPathLogIncrement
      (puncturedPathAround
        (imageCircleLoop g hg z r) w
          houter
          (imageCircleLoop_one_eq_zero g hg z r)) = _
    rw [puncturedPathAround_logIncrement_eq_windingNumber_mul]
    rfl
  let corrected :=
    puncturedPathPointwiseMul base factors
  have hcorrectedInc :
      puncturedPathLogIncrement corrected =
        (m : ℂ) *
            (2 * Real.pi * Complex.I) +
          ∑ i : ι,
            (-(n i) : ℂ) *
              (2 * Real.pi * Complex.I) := by
    change puncturedPathLogIncrement
      (puncturedPathPointwiseMul base factors) = _
    rw [puncturedPathLogIncrement_pointwiseMul,
      hbaseInc, hfactorsInc]
  have hcorrectedValue (t : unitInterval) :
      (corrected t : ℂ) =
        (g (circlePoint z r t) - w) *
          ∏ i : ι,
            (circlePoint z r t - c i) ^ (-(n i)) := by
    change
      (imageCircleLoop g hg z r t - w) *
          (∏ i ∈ Finset.univ,
            (complexCircleLoop z r t - c i) ^ (-(n i))) =
        (g (circlePoint z r t) - w) *
          ∏ i : ι,
            (circlePoint z r t - c i) ^ (-(n i))
    simp [imageCircleLoop, complexCircleLoop]
  let p0 : Metric.closedBall z r :=
    ⟨circlePoint z r 0, by
      rw [Metric.mem_closedBall,
        dist_circlePoint_center z hr]⟩
  have hbasepoint :
      F p0 = corrected 0 := by
    let q0 : perforatedClosedDisk z r c ρ :=
      ⟨circlePoint z r 0,
        circlePoint_mem_perforatedClosedDisk_outer
          z hr c ρ hinside 0⟩
    apply Subtype.ext
    have hq := congrArg Subtype.val (hF q0)
    rw [hcorrectedValue]
    simpa [p0, q0, n] using hq
  have hboundaryPath :
      puncturedClosedBallBoundaryPath z hr F =
        corrected.cast hbasepoint hbasepoint := by
    apply Path.ext
    funext t
    let qt : perforatedClosedDisk z r c ρ :=
      ⟨circlePoint z r t,
        circlePoint_mem_perforatedClosedDisk_outer
          z hr c ρ hinside t⟩
    change F ⟨circlePoint z r t, _⟩ = corrected t
    apply Subtype.ext
    have hq := congrArg Subtype.val (hF qt)
    rw [hcorrectedValue]
    simpa [qt, n] using hq
  have hcorrectedZero :
      puncturedPathLogIncrement corrected = 0 := by
    rw [hboundaryPath,
      puncturedPathLogIncrement_cast] at hFinc
    exact hFinc
  have heq :
      (m : ℂ) *
          (2 * Real.pi * Complex.I) =
        (∑ i : ι, (n i : ℂ)) *
          (2 * Real.pi * Complex.I) := by
    rw [hcorrectedInc] at hcorrectedZero
    have hsumNeg :
        (∑ i : ι,
            (-(n i) : ℂ) *
              (2 * Real.pi * Complex.I)) =
          -(∑ i : ι, (n i : ℂ)) *
            (2 * Real.pi * Complex.I) := by
      rw [← Finset.sum_mul, Finset.sum_neg_distrib]
    rw [hsumNeg] at hcorrectedZero
    linear_combination hcorrectedZero
  have hcast :
      (m : ℂ) = ∑ i : ι, (n i : ℂ) :=
    mul_right_cancel₀ Complex.two_pi_I_ne_zero heq
  change m = ∑ i : ι, n i
  exact_mod_cast hcast

/--
%%handwave
name:
  Boundary index equals the sum of local indices
statement:
  Let $f:\mathbb C\to\mathbb C$ be continuous, let the fiber $f^{-1}(w)$ be
  finite and discrete, and suppose this fiber lies inside the disk $B(z,r)$
  with $r>0$. Then
  $$
    I(f,\partial B(z,r);w)
      =\sum_{x\in f^{-1}(w)} i(f,x;w).
  $$
proof:
  [Choose pairwise disjoint fiber-isolating closed disks strictly inside the outer disk](lean:JJMath.Quasiconformal.exists_pairwiseDisjoint_isolatingRadii_of_finite_fiber_subset_ball). [Approximate $f$ smoothly on the resulting compact perforated disk, preserving avoidance of $w$ and staying closer to $f$ than $f$ is to $w$](lean:JJMath.Quasiconformal.exists_contDiff_avoiding_approximationOn_perforatedClosedDisk). [This strict relative approximation preserves the winding number on every boundary circle](lean:JJMath.Quasiconformal.planarCircleIndex_eq_of_norm_sub_lt). Apply [smooth boundary additivity on the perforated disk](lean:JJMath.Quasiconformal.planarCircleIndex_eq_sum_of_contDiff_of_avoids_perforatedClosedDisk), then identify every inner circle index with the corresponding radius-independent local index.
-/
theorem planarCircleIndex_eq_planarFiberIndexSum_of_fiber_subset_ball
    (f : ℂ → ℂ) (hf : Continuous f) (z w : ℂ) {r : ℝ} (hr : 0 < r)
    (hdiscrete : IsDiscrete {x : ℂ | f x = w})
    (hfinite : {x : ℂ | f x = w}.Finite)
    (hfiber : {x : ℂ | f x = w} ⊆ Metric.ball z r) :
    planarCircleIndex f hf z w r hr
        (imageCircleLoop_ne_of_fiber_subset_ball f hf z w hr hfiber) =
      planarFiberIndexSum f hf w hdiscrete hfinite := by
  letI : Fintype {x : ℂ // f x = w} := hfinite.fintype
  obtain ⟨ρ, hρiso, hpair, hinside⟩ :=
    exists_pairwiseDisjoint_isolatingRadii_of_finite_fiber_subset_ball
      f z w hdiscrete hfinite hfiber
  have hρpos (x : {x : ℂ // f x = w}) : 0 < ρ x := (hρiso x).1
  let c : {x : ℂ // f x = w} → ℂ := fun x ↦ (x : ℂ)
  obtain ⟨g, hgdiff, hgavoid, hgclose⟩ :=
    exists_contDiff_avoiding_approximationOn_perforatedClosedDisk
      f hf z w hr ρ hρpos hinside
  have hgouter : ∀ t, imageCircleLoop g hgdiff.continuous z r t ≠ w :=
    imageCircleLoop_ne_of_avoids_perforatedClosedDisk_outer
      g hgdiff.continuous z w hr c ρ hinside hgavoid
  have hginner (x : {x : ℂ // f x = w}) :
      ∀ t, imageCircleLoop g hgdiff.continuous (c x) (ρ x) t ≠ w :=
    imageCircleLoop_ne_of_avoids_perforatedClosedDisk_inner
      g hgdiff.continuous z w r c ρ hρpos hpair hinside hgavoid x
  have houterEq :
      planarCircleIndex f hf z w r hr
          (imageCircleLoop_ne_of_fiber_subset_ball f hf z w hr hfiber) =
        planarCircleIndex g hgdiff.continuous z w r hr hgouter := by
    apply planarCircleIndex_eq_of_norm_sub_lt
    intro t
    exact hgclose _
      (circlePoint_mem_perforatedClosedDisk_outer z hr c ρ hinside t)
  have hinnerEq (x : {x : ℂ // f x = w}) :
      planarCircleIndex f hf (c x) w (ρ x) (hρpos x)
          (imageCircleLoop_ne_of_isFiberIsolatingRadius
            f hf (c x) w (hρiso x)) =
        planarCircleIndex g hgdiff.continuous (c x) w (ρ x) (hρpos x)
          (hginner x) := by
    apply planarCircleIndex_eq_of_norm_sub_lt
    intro t
    exact hgclose _
      (circlePoint_mem_perforatedClosedDisk_inner z r c ρ
        hρpos hpair hinside x t)
  calc
    planarCircleIndex f hf z w r hr
        (imageCircleLoop_ne_of_fiber_subset_ball f hf z w hr hfiber) =
        planarCircleIndex g hgdiff.continuous z w r hr hgouter := houterEq
    _ = ∑ x : {x : ℂ // f x = w},
          planarCircleIndex g hgdiff.continuous (c x) w (ρ x) (hρpos x)
            (hginner x) :=
      planarCircleIndex_eq_sum_of_contDiff_of_avoids_perforatedClosedDisk
        g hgdiff z w hr c ρ hρpos hpair hinside hgavoid
    _ = ∑ x : {x : ℂ // f x = w},
          planarCircleIndex f hf (c x) w (ρ x) (hρpos x)
            (imageCircleLoop_ne_of_isFiberIsolatingRadius
              f hf (c x) w (hρiso x)) := by
      apply Finset.sum_congr rfl
      intro x _
      exact (hinnerEq x).symm
    _ = planarFiberIndexSum f hf w hdiscrete hfinite := by
      simp only [planarFiberIndexSum]
      apply Finset.sum_congr rfl
      intro x _
      exact (planarLocalIndex_eq_planarCircleIndex
        f hf (c x) w x.2 hdiscrete (hρiso x)).symm

/--
%%handwave
name:
  Positive local indices summing to one give a singleton fiber
statement:
  Let $f^{-1}(w)$ be finite and discrete. If every local index in this fiber
  is positive and
  $$
    \sum_{z\in f^{-1}(w)} i(f,z;w)=1,
  $$
  then $w$ has exactly one preimage.
proof:
  Every positive integer local index is at least one. Hence the cardinality
  of the fiber is at most the sum, which is one. The sum cannot be one for an
  empty fiber, so the fiber is a singleton.
-/
theorem existsUnique_preimage_of_planarFiberIndexSum_eq_one_of_pos
    (f : ℂ → ℂ) (hf : Continuous f) (w : ℂ)
    (hdiscrete : IsDiscrete {z : ℂ | f z = w})
    (hfinite : {z : ℂ | f z = w}.Finite)
    (hpos : ∀ z : {z : ℂ | f z = w},
      0 < planarLocalIndex f hf z w z.2 hdiscrete)
    (hsum : planarFiberIndexSum f hf w hdiscrete hfinite = 1) :
    ∃! z : ℂ, f z = w := by
  letI : Fintype {z : ℂ | f z = w} := hfinite.fintype
  let index : {z : ℂ | f z = w} → ℤ := fun z ↦
    planarLocalIndex f hf z w z.2 hdiscrete
  have hsum' : ∑ z, index z = 1 := by
    simpa [planarFiberIndexSum, index] using hsum
  have hnonempty : Nonempty {z : ℂ | f z = w} := by
    by_contra hempty
    haveI : IsEmpty {z : ℂ | f z = w} := not_nonempty_iff.mp hempty
    have hzero : ∑ z, index z = 0 := by
      apply Finset.sum_eq_zero
      intro z _hz
      exact isEmptyElim z
    omega
  have hcardLe : Fintype.card {z : ℂ | f z = w} ≤ 1 := by
    have hsumOnes :
        ((Fintype.card {z : ℂ | f z = w} : ℕ) : ℤ) =
          ∑ _z : {z : ℂ | f z = w}, (1 : ℤ) := by simp
    have hle :
        (∑ _z : {z : ℂ | f z = w}, (1 : ℤ)) ≤
          ∑ z, index z := by
      apply Finset.sum_le_sum
      intro z _hz
      exact hpos z
    rw [← hsumOnes, hsum'] at hle
    exact_mod_cast hle
  have hcardEq : Fintype.card {z : ℂ | f z = w} = 1 := by
    have hcardPos : 0 < Fintype.card {z : ℂ | f z = w} :=
      Fintype.card_pos_iff.mpr hnonempty
    omega
  obtain ⟨z, hz⟩ := Fintype.card_eq_one_iff.mp hcardEq
  refine ⟨z, z.2, ?_⟩
  intro y hy
  have hy' : (⟨y, hy⟩ : {z : ℂ | f z = w}) = z := hz ⟨y, hy⟩
  exact congrArg Subtype.val hy'

/--
%%handwave
name:
  Total fiber index of a singleton fiber
statement:
  If $f^{-1}(w)=\{z\}$, then the sum of local indices over the fiber is the
  single local index $i(f,z;w)$.
proof:
  The finite fiber subtype has the unique element $z$, so its finite sum has
  one term.
-/
theorem planarFiberIndexSum_eq_planarLocalIndex_of_unique_preimage
    (f : ℂ → ℂ) (hf : Continuous f) (z w : ℂ) (hzw : f z = w)
    (hdiscrete : IsDiscrete {x : ℂ | f x = w})
    (hfinite : {x : ℂ | f x = w}.Finite)
    (hunique : ∀ x, f x = w → x = z) :
    planarFiberIndexSum f hf w hdiscrete hfinite =
      planarLocalIndex f hf z w hzw hdiscrete := by
  letI : Fintype {x : ℂ | f x = w} := hfinite.fintype
  let z' : {x : ℂ | f x = w} := ⟨z, hzw⟩
  letI : Unique {x : ℂ | f x = w} :=
    { default := z'
      uniq := fun x ↦ Subtype.ext (hunique x x.2) }
  change (∑ x : {x : ℂ | f x = w},
      planarLocalIndex f hf x w x.2 hdiscrete) = _
  rw [Fintype.sum_unique]
  rfl

/--
%%handwave
name:
  A close perturbation of a large circle has degree one
statement:
  Let $w$ lie inside the circle $|\zeta-z|=r$. Suppose a continuous map $f$
  satisfies
  $$
    |f(\zeta)-\zeta|<r-|w-z|
  $$
  at every point of this circle. Then the image circle avoids $w$, and its
  normalized loop around $w$ is homotopic in
  $\mathbb C\setminus\{0\}$ to the standard positive unit circle.
proof:
  The reverse triangle inequality gives
  $|\zeta-w|\geq r-|w-z|$, so the straight-line homotopy from the circle to
  its image avoids $w$. The unperturbed circle has positive class around
  every interior point.
-/
theorem exists_imageCircleLoop_avoids_and_homotopic_positive_of_close
    (f : ℂ → ℂ) (hf : Continuous f) (z w : ℂ) {r : ℝ}
    (hr : 0 < r) (hw : dist w z < r)
    (hclose : ∀ t,
      ‖f (complexCircleLoop z r t) - complexCircleLoop z r t‖ <
        r - dist w z) :
    ∃ hne : ∀ t, imageCircleLoop f hf z r t ≠ w,
      Path.Homotopic
        (normalizedLoopAround (imageCircleLoop f hf z r) w hne
          (imageCircleLoop_one_eq_zero f hf z r))
        positiveCircleLoop := by
  let γ : C(unitInterval, ℂ) := complexCircleLoop z r
  let γf : C(unitInterval, ℂ) := imageCircleLoop f hf z r
  have hγne : ∀ t, γ t ≠ w :=
    complexCircleLoop_ne_of_dist_lt_radius z w hr hw
  have hmargin (t : unitInterval) : r - dist w z ≤ ‖γ t - w‖ := by
    have htri : r ≤ dist (γ t) w + dist w z := by
      calc
        r = dist (γ t) z := (dist_circlePoint_center z hr t).symm
        _ ≤ dist (γ t) w + dist w z := dist_triangle _ _ _
    rw [Complex.dist_eq] at htri
    linarith
  have hγfne : ∀ t, γf t ≠ w := by
    intro t htw
    have hlt : ‖γf t - γ t‖ < ‖γ t - w‖ :=
      lt_of_lt_of_le (hclose t) (hmargin t)
    rw [htw, norm_sub_rev] at hlt
    exact (lt_irrefl _) hlt
  refine ⟨hγfne, ?_⟩
  have hperturb :
      Path.Homotopic
        (normalizedLoopAround γ w hγne
          (complexCircleLoop_one_eq_zero z r))
        (normalizedLoopAround γf w hγfne
          (imageCircleLoop_one_eq_zero f hf z r)) := by
    apply normalizedLoopAround_homotopic_of_norm_sub_lt
    intro t
    exact lt_of_lt_of_le (hclose t) (hmargin t)
  have hcircle :=
    normalizedLoopAround_complexCircleLoop_homotopic_positive z w hr hw
  exact hperturb.symm.trans hcircle

/--
%%handwave
name:
  Normalized boundary class is independent of radius
statement:
  Let $F:\Omega\to\Omega'$ be a homeomorphism and let $z\in\Omega$. If every
  positive circle whose radius lies between $r_0>0$ and $r_1>0$ is contained
  in $\Omega$, then the normalized image loops for radii $r_0$ and $r_1$ are
  homotopic in $\mathbb C\setminus\{0\}$.
proof:
  Interpolate linearly between $r_0$ and $r_1$. The resulting family of
  circles avoids $z$, and normalizing its image at the moving base point gives
  the required punctured-plane homotopy.
-/
theorem normalizedBoundaryLoop_radius_homotopic {Ω Ω' : Set ℂ}
    (F : Ω ≃ₜ Ω') (z : Ω)
    (r₀ r₁ : ℝ) (hr₀ : 0 < r₀) (hr₁ : 0 < r₁)
    (hfamily : ∀ s t : unitInterval,
      circlePoint z (((1 - (s : ℝ)) * r₀ + (s : ℝ) * r₁)) t ∈ Ω) :
    Path.Homotopic
      (normalizedBoundaryLoop F z r₀ hr₀ (fun t ↦ by simpa using hfamily 0 t))
      (normalizedBoundaryLoop F z r₁ hr₁ (fun t ↦ by simpa using hfamily 1 t)) := by
  let radius : unitInterval → ℝ := fun s ↦ (1 - (s : ℝ)) * r₀ + (s : ℝ) * r₁
  let H : C(unitInterval × unitInterval, Ω) :=
    ⟨fun x ↦ ⟨circlePoint z (radius x.1) x.2, hfamily x.1 x.2⟩, by
      apply Continuous.subtype_mk
      dsimp [circlePoint, radius]
      exact continuous_const.add
        ((by fun_prop : Continuous fun x : unitInterval × unitInterval ↦
          (((1 - (x.1 : ℝ)) * r₀ + (x.1 : ℝ) * r₁ : ℝ) : ℂ)).mul
            (Complex.continuous_exp.comp (by fun_prop)))⟩
  have hradius (s : unitInterval) : 0 < radius s := by
    dsimp [radius]
    have hs0 : 0 ≤ (s : ℝ) := s.2.1
    have hs1 : (s : ℝ) ≤ 1 := s.2.2
    by_cases hs : (s : ℝ) = 0
    · simp [hs, hr₀]
    · have hspos : 0 < (s : ℝ) := lt_of_le_of_ne hs0 (Ne.symm hs)
      have hfirst : 0 ≤ (1 - (s : ℝ)) * r₀ :=
        mul_nonneg (sub_nonneg.mpr hs1) hr₀.le
      have hsecond : 0 < (s : ℝ) * r₁ := mul_pos hspos hr₁
      linarith
  have hne (x : unitInterval × unitInterval) : H x ≠ z := by
    apply Subtype.coe_ne_coe.mp
    exact circlePoint_ne_center z (hradius x.1) x.2
  have hclosed (s : unitInterval) : H (s, 1) = H (s, 0) := by
    apply Subtype.ext
    exact (circlePoint_one z (radius s)).trans
      (circlePoint_zero z (radius s)).symm
  have hhom := normalizedImageLoopHomotopy F z H hne hclosed
  refine ⟨?_⟩
  convert hhom using 1 <;>
    apply Path.ext <;>
    funext t <;>
    apply Subtype.ext <;>
    simp [normalizedBoundaryLoop, normalizedImageLoop, H, radius]

/--
%%handwave
name:
  The normalized identity boundary is the positive unit circle
statement:
  For the identity homeomorphism, the normalized image of every positive
  boundary circle is exactly the positive unit-circle loop.
proof:
  Translation removes the center and division by the initial radius cancels
  the positive real scale.
-/
theorem normalizedBoundaryLoop_refl {Ω : Set ℂ} (z : Ω) (r : ℝ)
    (hr : 0 < r) (hcircle : ∀ t : unitInterval, circlePoint z r t ∈ Ω) :
    normalizedBoundaryLoop (Homeomorph.refl Ω) z r hr hcircle =
      positiveCircleLoop := by
  apply Path.ext
  funext t
  apply Subtype.ext
  change ((circlePoint z r t - z) / (circlePoint z r 0 - z)) =
    Complex.exp ((2 * Real.pi * (t : ℝ)) * Complex.I)
  rw [circlePoint_zero]
  simp only [add_sub_cancel_left]
  rw [circlePoint]
  simp only [add_sub_cancel_left]
  change ((r : ℂ) *
      Complex.exp (((2 * Real.pi * (t : ℝ) : ℝ) : ℂ) * Complex.I)) /
        (r : ℂ) = Complex.exp ((2 * Real.pi * (t : ℝ)) * Complex.I)
  field_simp [Complex.ofReal_ne_zero.mpr (ne_of_gt hr)]
  congr 1
  push_cast
  ring

/--
%%handwave
name:
  Orientation-preserving planar homeomorphism
statement:
  A homeomorphism $F:\Omega\to\Omega'$ preserves planar orientation if, near
  every $z\in\Omega$, there is a positive-radius closed disk centered at $z$
  and contained in $\Omega$ such that the image of its positively oriented
  boundary, viewed as a loop around $F(z)$ and normalized at its base point,
  is homotopic in $\mathbb C\setminus\{0\}$ to the positive unit circle.
-/
def PreservesPlanarOrientation {Ω Ω' : Set ℂ} (F : Ω ≃ₜ Ω') : Prop :=
  ∀ z : Ω,
    ∃ r : ℝ, ∃ hr : 0 < r,
      ∃ hball : Metric.closedBall (z : ℂ) r ⊆ Ω,
        (normalizedBoundaryLoop F z r hr
          (circlePoint_mem_of_closedBall_subset z hr hball)).Homotopic
            positiveCircleLoop

/--
%%handwave
name:
  Every protected positive circle has positive image class
statement:
  Let $F:\Omega\to\Omega'$ preserve planar orientation. If $r>0$ and the
  closed disk $\overline B(z,r)$ lies in $\Omega$, then the normalized image
  under $F$ of the positively oriented boundary circle is homotopic in
  $\mathbb C\setminus\{0\}$ to the positive unit circle.
proof:
  Compare the chosen circle with an orientation-witness circle at $z$.
  Every intermediate concentric circle lies in the larger of the two
  protected disks, so radius independence identifies their normalized image
  classes.
-/
theorem PreservesPlanarOrientation.normalizedBoundaryLoop_homotopic
    {Ω Ω' : Set ℂ} {F : Ω ≃ₜ Ω'}
    (hF : PreservesPlanarOrientation F) (z : Ω)
    {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall (z : ℂ) r ⊆ Ω) :
    (normalizedBoundaryLoop F z r hr
      (circlePoint_mem_of_closedBall_subset z hr hball)).Homotopic
        positiveCircleLoop := by
  obtain ⟨rF, hrF, hballF, hqF⟩ := hF z
  have hfamily : ∀ s t : unitInterval,
      circlePoint z (((1 - (s : ℝ)) * r + (s : ℝ) * rF)) t ∈ Ω := by
    intro s t
    have hs0 : 0 ≤ (s : ℝ) := s.2.1
    have hs1 : (s : ℝ) ≤ 1 := s.2.2
    have hradpos : 0 < (1 - (s : ℝ)) * r + (s : ℝ) * rF := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hs1) hr.le,
        mul_nonneg hs0 hrF.le]
    by_cases hrrF : r ≤ rF
    · apply hballF
      rw [Metric.mem_closedBall, dist_circlePoint_center z hradpos t]
      nlinarith [mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr hrrF),
        mul_nonneg hs0 (sub_nonneg.mpr hrrF)]
    · have hrFr : rF ≤ r := le_of_not_ge hrrF
      apply hball
      rw [Metric.mem_closedBall, dist_circlePoint_center z hradpos t]
      nlinarith [mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr hrFr),
        mul_nonneg hs0 (sub_nonneg.mpr hrFr)]
  exact (normalizedBoundaryLoop_radius_homotopic
    F z r rF hr hrF hfamily).trans hqF

/--
%%handwave
name:
  Orientation preservation under compact-uniform homeomorphic limits
statement:
  Let $\Omega\subseteq\mathbb C$ be open, let
  $F_n:\Omega\to\Omega'$ be orientation-preserving homeomorphisms, and let
  $G:\Omega\to\Omega'$ be a homeomorphism. Suppose $F_n\to G$ uniformly on
  every compact subset of $\Omega$. Then $G$ preserves planar orientation.
proof:
  Fix a protected positive circle around $z$. Continuity of $G^{-1}$ gives a
  positive lower bound for the distance from its $G$-image to $G(z)$.
  Compact-uniform convergence on the circle together with its center makes
  one $F_n$ uniformly closer than half this separation. The straight-line
  interpolation between the translated $F_n$- and $G$-image loops therefore
  avoids zero. Normalize at the moving base point to obtain a punctured-plane
  homotopy. The chosen $F_n$ loop has positive class because every protected
  circle does, hence so does the $G$ loop.
-/
theorem preservesPlanarOrientation_of_compactly_tendstoUniformly
    {Ω Ω' : Set ℂ} (hΩ : IsOpen Ω)
    (F : ℕ → Ω ≃ₜ Ω') (G : Ω ≃ₜ Ω')
    (hF : ∀ n, PreservesPlanarOrientation (F n))
    (hconv : ∀ K : Set Ω, IsCompact K →
      TendstoUniformlyOn (fun n z ↦ (F n z : ℂ))
        (fun z ↦ (G z : ℂ)) Filter.atTop K) :
    PreservesPlanarOrientation G := by
  intro z
  obtain ⟨ε, hε, hεball⟩ := (Metric.isOpen_iff.mp hΩ) z z.2
  let r : ℝ := ε / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrε : r < ε := by dsimp [r]; linarith
  have hball : Metric.closedBall (z : ℂ) r ⊆ Ω := by
    intro w hw
    apply hεball
    rw [Metric.mem_ball]
    exact lt_of_le_of_lt (Metric.mem_closedBall.mp hw) hrε
  let hcircle := circlePoint_mem_of_closedBall_subset z hr hball
  let source : C(unitInterval, Ω) := circlePath z r hcircle
  let K : Set Ω := Set.range source ∪ {z}
  have hK : IsCompact K :=
    (isCompact_range source.continuous).union isCompact_singleton
  let Ginv : Ω' → ℂ := fun y ↦ G.symm y
  have hGinv : Continuous Ginv :=
    continuous_subtype_val.comp G.symm.continuous
  obtain ⟨δ, hδ, hδmap⟩ :=
    (Metric.continuousAt_iff.mp hGinv.continuousAt) r hr
  have hsep (t : unitInterval) :
      δ ≤ dist (G (source t) : ℂ) (G z : ℂ) := by
    by_contra hnot
    have hclose : dist (G (source t)) (G z) < δ := by
      simpa [Subtype.dist_eq] using lt_of_not_ge hnot
    have hpre := hδmap hclose
    simp only [Ginv, G.symm_apply_apply] at hpre
    change dist (circlePoint z r t) z < r at hpre
    rw [dist_circlePoint_center z hr t] at hpre
    exact (lt_irrefl r) hpre
  have hevent : ∀ᶠ n in Filter.atTop,
      ∀ x ∈ K, dist (G x : ℂ) (F n x : ℂ) < δ / 4 :=
    (Metric.tendstoUniformlyOn_iff.mp (hconv K hK)) (δ / 4) (by positivity)
  obtain ⟨n, hnclose⟩ := hevent.exists
  have hFnpos :=
    (hF n).normalizedBoundaryLoop_homotopic z hr hball
  have hsource_zero_one : source 1 = source 0 := by
    apply Subtype.ext
    exact (circlePoint_one z r).trans (circlePoint_zero z r).symm
  have hraw_close (t : unitInterval) :
      ‖((F n (source t) : ℂ) - F n z) -
          ((G (source t) : ℂ) - G z)‖ < δ := by
    have htK : source t ∈ K := Or.inl ⟨t, rfl⟩
    have hzK : z ∈ K := Or.inr (Set.mem_singleton z)
    have ht := hnclose (source t) htK
    have hz := hnclose z hzK
    rw [Complex.dist_eq] at ht hz
    calc
      ‖((F n (source t) : ℂ) - F n z) -
          ((G (source t) : ℂ) - G z)‖ =
          ‖((F n (source t) : ℂ) - G (source t)) -
            ((F n z : ℂ) - G z)‖ := by ring_nf
      _ ≤ ‖(F n (source t) : ℂ) - G (source t)‖ +
          ‖(F n z : ℂ) - G z‖ := norm_sub_le _ _
      _ < δ / 4 + δ / 4 := add_lt_add (by simpa [norm_sub_rev] using ht)
        (by simpa [norm_sub_rev] using hz)
      _ < δ := by linarith
  let raw : unitInterval × unitInterval → ℂ := fun x ↦
    (1 - (x.1 : ℝ)) • ((F n (source x.2) : ℂ) - F n z) +
      (x.1 : ℝ) • ((G (source x.2) : ℂ) - G z)
  have hraw_ne (x : unitInterval × unitInterval) : raw x ≠ 0 := by
    let a : ℂ := (G (source x.2) : ℂ) - G z
    let b : ℂ := (F n (source x.2) : ℂ) - F n z
    have hs0 : 0 ≤ (x.1 : ℝ) := x.1.2.1
    have hs1 : (x.1 : ℝ) ≤ 1 := x.1.2.2
    have hdiff : raw x - a = (1 - (x.1 : ℝ)) • (b - a) := by
      apply Complex.ext <;>
        simp [raw, a, b, Complex.sub_re, Complex.sub_im,
          Complex.add_re, Complex.add_im] <;>
        ring
    have hlt : ‖raw x - a‖ < δ := by
      rw [hdiff, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr hs1)]
      exact lt_of_le_of_lt
        (mul_le_of_le_one_left (norm_nonneg _) (by linarith))
        (hraw_close x.2)
    intro hzero
    rw [hzero, zero_sub, norm_neg] at hlt
    exact (not_lt_of_ge (by
      simpa [a, Complex.dist_eq] using hsep x.2)) hlt
  have hraw_cont : Continuous raw := by
    dsimp [raw]
    fun_prop
  have hraw_closed (s : unitInterval) : raw (s, 1) = raw (s, 0) := by
    dsimp [raw]
    rw [hsource_zero_one]
  let H : C(unitInterval × unitInterval, PuncturedComplex) :=
    ⟨fun x ↦ ⟨raw x / raw (x.1, 0),
        div_ne_zero (hraw_ne x) (hraw_ne (x.1, 0))⟩, by
      apply Continuous.subtype_mk
      exact hraw_cont.div (hraw_cont.comp (by fun_prop))
        (fun x ↦ hraw_ne (x.1, 0))⟩
  have hFG :
      (normalizedBoundaryLoop (F n) z r hr hcircle).Homotopic
        (normalizedBoundaryLoop G z r hr hcircle) := by
    refine ⟨{
      toFun := H
      continuous_toFun := H.continuous
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }⟩
    · intro t
      apply Subtype.ext
      simp [H, raw, normalizedBoundaryLoop, source, circlePath]
    · intro t
      apply Subtype.ext
      simp [H, raw, normalizedBoundaryLoop, source, circlePath]
    · intro s t ht
      rcases ht with rfl | rfl
      · have hHs : H (s, 0) = (⟨1, one_ne_zero⟩ : PuncturedComplex) := by
          apply Subtype.ext
          exact div_self (hraw_ne (s, 0))
        exact hHs.trans
          (normalizedBoundaryLoop (F n) z r hr hcircle).source.symm
      · have hHs : H (s, 1) = (⟨1, one_ne_zero⟩ : PuncturedComplex) := by
          apply Subtype.ext
          change raw (s, 1) / raw (s, 0) = 1
          rw [hraw_closed]
          exact div_self (hraw_ne (s, 0))
        exact hHs.trans
          (normalizedBoundaryLoop (F n) z r hr hcircle).target.symm
  exact ⟨r, hr, hball, hFG.symm.trans hFnpos⟩

/--
%%handwave
name:
  Orientation preservation is local under restriction
statement:
  Let $F:\Omega\to\Omega'$ preserve planar orientation, let $U\subseteq\Omega$
  be open, and let $G:U\to V$ be a homeomorphism satisfying $G(z)=F(z)$ for
  every $z\in U$. Then $G$ preserves planar orientation.
proof:
  At each point, shrink an orientation-witness disk for $F$ into $U$.
  Radius independence preserves the positive boundary class, and the
  normalized boundary loops for $F$ and $G$ on the smaller circle agree
  exactly.
-/
theorem PreservesPlanarOrientation.restrict
    {Ω Ω' U V : Set ℂ} {F : Ω ≃ₜ Ω'} {G : U ≃ₜ V}
    (hF : PreservesPlanarOrientation F)
    (hU : IsOpen U) (hUΩ : U ⊆ Ω)
    (hG : ∀ z : U, (G z : ℂ) = F ⟨z, hUΩ z.2⟩) :
    PreservesPlanarOrientation G := by
  intro z
  let zΩ : Ω := ⟨z, hUΩ z.2⟩
  obtain ⟨rF, hrF, hballF, hqF⟩ := hF zΩ
  obtain ⟨ε, hε, hεball⟩ := (Metric.isOpen_iff.mp hU) z z.2
  let r : ℝ := min rF ε / 2
  have hmin : 0 < min rF ε := lt_min hrF hε
  have hr : 0 < r := by dsimp [r]; positivity
  have hrrF : r < rF := by
    dsimp [r]
    have hle := min_le_left rF ε
    linarith
  have hrε : r < ε := by
    dsimp [r]
    have hle := min_le_right rF ε
    linarith
  have hball : Metric.closedBall (z : ℂ) r ⊆ U := by
    intro w hw
    apply hεball
    rw [Metric.mem_ball]
    exact lt_of_le_of_lt (Metric.mem_closedBall.mp hw) hrε
  let hcircleG := circlePoint_mem_of_closedBall_subset z hr hball
  have hballΩ : Metric.closedBall (zΩ : ℂ) r ⊆ Ω :=
    hball.trans hUΩ
  let hcircleF := circlePoint_mem_of_closedBall_subset zΩ hr hballΩ
  have hfamily : ∀ s t : unitInterval,
      circlePoint zΩ (((1 - (s : ℝ)) * r + (s : ℝ) * rF)) t ∈ Ω := by
    intro s t
    apply hballF
    rw [Metric.mem_closedBall]
    have hs0 : 0 ≤ (s : ℝ) := s.2.1
    have hs1 : (s : ℝ) ≤ 1 := s.2.2
    have hradpos :
        0 < (1 - (s : ℝ)) * r + (s : ℝ) * rF := by
      nlinarith
    rw [dist_circlePoint_center zΩ hradpos t]
    nlinarith
  have hqSmall :
      (normalizedBoundaryLoop F zΩ r hr hcircleF).Homotopic
        positiveCircleLoop :=
    (normalizedBoundaryLoop_radius_homotopic
      F zΩ r rF hr hrF hfamily).trans hqF
  have hloops :
      normalizedBoundaryLoop G z r hr hcircleG =
        normalizedBoundaryLoop F zΩ r hr hcircleF := by
    apply Path.ext
    funext t
    apply Subtype.ext
    simp [normalizedBoundaryLoop, hG, zΩ]
  refine ⟨r, hr, hball, ?_⟩
  rw [hloops]
  exact hqSmall

/--
%%handwave
name:
  Composition preserves planar orientation
statement:
  The composition of two orientation-preserving homeomorphisms between open
  planar domains is orientation preserving.
proof:
  By [changing the radius through contained positive circles does not change the normalized boundary class](lean:JJMath.Quasiconformal.normalizedBoundaryLoop_radius_homotopic), shrink the first witness until its image lies in the second witness disk. Compactness lets one rescale the first punctured-plane homotopy into that disk. Apply the second homeomorphism, then rotate and rescale the resulting positive circle to the second witness boundary and concatenate the homotopies.
-/
theorem PreservesPlanarOrientation.trans
    {Ω₁ Ω₂ Ω₃ : Set ℂ} {F : Ω₁ ≃ₜ Ω₂} {G : Ω₂ ≃ₜ Ω₃}
    (hF : PreservesPlanarOrientation F) (hG : PreservesPlanarOrientation G) :
    PreservesPlanarOrientation (F.trans G) := by
  intro z
  obtain ⟨rF, hrF, hballF, hqF⟩ := hF z
  obtain ⟨rG, hrG, hballG, hqG⟩ := hG (F z)
  let Fval : Ω₁ → ℂ := fun w ↦ F w
  have hFval : Continuous Fval := continuous_subtype_val.comp F.continuous
  obtain ⟨δ, hδ, hδmap⟩ :=
    (Metric.continuousAt_iff.mp hFval.continuousAt) rG hrG
  let r : ℝ := min rF δ / 2
  have hmin : 0 < min rF δ := lt_min hrF hδ
  have hr : 0 < r := by dsimp [r]; positivity
  have hrrF : r < rF := by
    dsimp [r]
    have hle := min_le_left rF δ
    linarith
  have hrδ : r < δ := by
    dsimp [r]
    have hle := min_le_right rF δ
    linarith
  have hball : Metric.closedBall (z : ℂ) r ⊆ Ω₁ := by
    exact fun _ hw ↦ hballF (Metric.closedBall_subset_closedBall hrrF.le hw)
  let hcircle := circlePoint_mem_of_closedBall_subset z hr hball
  let source : C(unitInterval, Ω₁) := circlePath z r hcircle
  have hsource_ne (t : unitInterval) : source t ≠ z := by
    apply Subtype.coe_ne_coe.mp
    exact circlePoint_ne_center z hr t
  have hsource_closed : source 1 = source 0 := by
    apply Subtype.ext
    exact (circlePoint_one z r).trans (circlePoint_zero z r).symm
  have himage_close (t : unitInterval) :
      dist (F (source t) : ℂ) (F z : ℂ) < rG := by
    apply hδmap
    rw [Subtype.dist_eq]
    change dist (circlePoint z r t) z < δ
    rw [dist_circlePoint_center z hr t]
    exact hrδ
  have hfamilyF : ∀ s t : unitInterval,
      circlePoint z (((1 - (s : ℝ)) * r + (s : ℝ) * rF)) t ∈ Ω₁ := by
    intro s t
    have hs0 : 0 ≤ (s : ℝ) := s.2.1
    have hs1 : (s : ℝ) ≤ 1 := s.2.2
    have hdiff : 0 ≤ rF - r := sub_nonneg.mpr hrrF.le
    have hradpos : 0 < (1 - (s : ℝ)) * r + (s : ℝ) * rF := by
      nlinarith [mul_nonneg hs0 hdiff]
    have hradle : (1 - (s : ℝ)) * r + (s : ℝ) * rF ≤ rF := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hs1) hdiff]
    apply hballF
    rw [Metric.mem_closedBall, dist_circlePoint_center z hradpos t]
    exact hradle
  have hq :
      (normalizedBoundaryLoop F z r hr hcircle).Homotopic positiveCircleLoop :=
    (normalizedBoundaryLoop_radius_homotopic F z r rF hr hrF hfamilyF).trans hqF
  rcases hq with ⟨HF⟩
  let den : ℂ := (F (source 0) : ℂ) - F z
  have hden : den ≠ 0 := by
    apply sub_ne_zero.mpr
    exact Subtype.coe_ne_coe.mpr (F.injective.ne (hsource_ne 0))
  obtain ⟨M₀, hM₀⟩ := isCompact_univ.exists_bound_of_continuousOn
    (continuous_subtype_val.comp HF.continuous).continuousOn
  let M : ℝ := max M₀ 1
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hHFbound (x : unitInterval × unitInterval) : ‖(HF x : ℂ)‖ ≤ M :=
    le_trans (hM₀ x (mem_univ x)) (le_max_left _ _)
  have hdennorm : 0 < ‖den‖ := norm_pos_iff.mpr hden
  let ε : ℝ := min 1 (rG / (2 * ‖den‖ * M))
  have hquot : 0 < rG / (2 * ‖den‖ * M) := by positivity
  have hεpos : 0 < ε := by
    dsimp [ε]
    exact lt_min zero_lt_one hquot
  have hεle : ε ≤ 1 := by dsimp [ε]; exact min_le_left _ _
  have hεbound : ε * ‖den‖ * M < rG := by
    have hεquot : ε ≤ rG / (2 * ‖den‖ * M) := by
      dsimp [ε]
      exact min_le_right _ _
    have hprod : ε * ‖den‖ * M ≤ rG / 2 := by
      calc
        ε * ‖den‖ * M ≤ (rG / (2 * ‖den‖ * M)) * ‖den‖ * M := by
          gcongr
        _ = rG / 2 := by field_simp
    linarith
  let shrink : unitInterval → ℝ := fun s ↦ (1 - (s : ℝ)) + (s : ℝ) * ε
  have hshrink_pos (s : unitInterval) : 0 < shrink s := by
    dsimp [shrink]
    have hs0 : 0 ≤ (s : ℝ) := s.2.1
    have hs1 : (s : ℝ) ≤ 1 := s.2.2
    nlinarith [mul_nonneg hs0 hεpos.le]
  have hshrink_le (s : unitInterval) : shrink s ≤ 1 := by
    dsimp [shrink]
    have hs0 : 0 ≤ (s : ℝ) := s.2.1
    nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hεle)]
  let Hshrink : C(unitInterval × unitInterval, Ω₂) :=
    ⟨fun x ↦ ⟨(F z : ℂ) + (shrink x.1 : ℂ) * ((F (source x.2) : ℂ) - F z), by
        apply hballG
        rw [Metric.mem_closedBall, Complex.dist_eq]
        simp only [add_sub_cancel_left, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg (hshrink_pos x.1).le]
        have him := himage_close x.2
        rw [Complex.dist_eq] at him
        exact le_of_lt (lt_of_le_of_lt
          (mul_le_of_le_one_left (norm_nonneg _) (hshrink_le x.1))
          him)⟩, by
      apply Continuous.subtype_mk
      exact continuous_const.add
        ((Complex.continuous_ofReal.comp (by fun_prop)).mul
          ((continuous_subtype_val.comp
            (F.continuous.comp (source.continuous.comp (by fun_prop)))).sub
              continuous_const))⟩
  have hshrink_ne (x : unitInterval × unitInterval) : Hshrink x ≠ F z := by
    apply Subtype.coe_ne_coe.mp
    change (F z : ℂ) + (shrink x.1 : ℂ) * ((F (source x.2) : ℂ) - F z) ≠ F z
    rw [add_ne_left]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt (hshrink_pos x.1)))
      (sub_ne_zero.mpr (Subtype.coe_ne_coe.mpr
        (F.injective.ne (hsource_ne x.2))))
  have hshrink_closed (s : unitInterval) : Hshrink (s, 1) = Hshrink (s, 0) := by
    apply Subtype.ext
    change (F z : ℂ) + (shrink s : ℂ) * ((F (source 1) : ℂ) - F z) =
      (F z : ℂ) + (shrink s : ℂ) * ((F (source 0) : ℂ) - F z)
    rw [hsource_closed]
  have hhomShrink := normalizedImageLoopHomotopy G (F z) Hshrink
    hshrink_ne hshrink_closed
  let a : ℂ := (ε : ℂ) * den
  have ha : a ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hεpos)) hden
  have hanorm : ‖a‖ = ε * ‖den‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hεpos.le]
  let Hscaled : C(unitInterval × unitInterval, Ω₂) :=
    ⟨fun x ↦ ⟨(F z : ℂ) + a * (HF x : ℂ), by
        apply hballG
        rw [Metric.mem_closedBall, Complex.dist_eq, add_sub_cancel_left, norm_mul,
          hanorm]
        exact le_of_lt (lt_of_le_of_lt
          (mul_le_mul_of_nonneg_left (hHFbound x)
            (mul_nonneg hεpos.le hdennorm.le)) hεbound)⟩, by
      apply Continuous.subtype_mk
      exact continuous_const.add
        (continuous_const.mul (continuous_subtype_val.comp HF.continuous))⟩
  have hscaled_ne (x : unitInterval × unitInterval) : Hscaled x ≠ F z := by
    apply Subtype.coe_ne_coe.mp
    change (F z : ℂ) + a * (HF x : ℂ) ≠ F z
    rw [add_ne_left]
    exact mul_ne_zero ha (HF x).2
  have hscaled_closed (s : unitInterval) : Hscaled (s, 1) = Hscaled (s, 0) := by
    apply Subtype.ext
    change (F z : ℂ) + a * (HF (s, 1) : ℂ) =
      (F z : ℂ) + a * (HF (s, 0) : ℂ)
    have h1 := HF.prop' s 1 (by simp)
    have h0 := HF.prop' s 0 (by simp)
    change HF (s, 1) = _ at h1
    change HF (s, 0) = _ at h0
    rw [h1, h0]
    simp
  have hhomScaled := normalizedImageLoopHomotopy G (F z) Hscaled
    hscaled_ne hscaled_closed
  have hMone : 1 ≤ M := le_max_right _ _
  have hanorm_lt : ‖a‖ < rG := by
    rw [hanorm]
    have hm := mul_le_mul_of_nonneg_left hMone
      (mul_nonneg hεpos.le hdennorm.le)
    exact lt_of_le_of_lt (by simpa using hm) hεbound
  let turnRadius : unitInterval → ℝ := fun s ↦
    (1 - (s : ℝ)) * ‖a‖ + (s : ℝ) * rG
  let turnAngle : unitInterval → ℝ := fun s ↦ (1 - (s : ℝ)) * Complex.arg a
  let turnScalar : unitInterval → ℂ := fun s ↦
    (turnRadius s : ℂ) * Complex.exp ((turnAngle s : ℂ) * Complex.I)
  have hturnRadius_pos (s : unitInterval) : 0 < turnRadius s := by
    dsimp [turnRadius]
    have hs0 : 0 ≤ (s : ℝ) := s.2.1
    have hs1 : (s : ℝ) ≤ 1 := s.2.2
    have had : 0 < ‖a‖ := norm_pos_iff.mpr ha
    nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hanorm_lt.le)]
  have hturnRadius_le (s : unitInterval) : turnRadius s ≤ rG := by
    dsimp [turnRadius]
    have hs0 : 0 ≤ (s : ℝ) := s.2.1
    have hs1 : (s : ℝ) ≤ 1 := s.2.2
    nlinarith [mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr hanorm_lt.le)]
  have hturnScalar_ne (s : unitInterval) : turnScalar s ≠ 0 := by
    exact mul_ne_zero
      (Complex.ofReal_ne_zero.mpr (ne_of_gt (hturnRadius_pos s)))
      (Complex.exp_ne_zero _)
  have hturnScalar_norm (s : unitInterval) : ‖turnScalar s‖ = turnRadius s := by
    dsimp [turnScalar]
    rw [norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (hturnRadius_pos s).le,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  let Hturn : C(unitInterval × unitInterval, Ω₂) :=
    ⟨fun x ↦ ⟨(F z : ℂ) + turnScalar x.1 * (positiveCircleLoop x.2 : ℂ), by
        apply hballG
        rw [Metric.mem_closedBall, Complex.dist_eq, add_sub_cancel_left, norm_mul,
          hturnScalar_norm]
        rw [show ‖(positiveCircleLoop x.2 : ℂ)‖ = 1 by
          rw [show (positiveCircleLoop x.2 : ℂ) =
              Complex.exp ((((2 * Real.pi * (x.2 : ℝ)) : ℝ) : ℂ) * Complex.I) by
            simp [positiveCircleLoop]]
          exact Complex.norm_exp_ofReal_mul_I _]
        simpa using hturnRadius_le x.1⟩, by
      apply Continuous.subtype_mk
      exact continuous_const.add
        (((Complex.continuous_ofReal.comp (by fun_prop)).mul
          (Complex.continuous_exp.comp (by fun_prop))).mul
            (continuous_subtype_val.comp
              (positiveCircleLoop.continuous.comp (by fun_prop))))⟩
  have hturn_ne (x : unitInterval × unitInterval) : Hturn x ≠ F z := by
    apply Subtype.coe_ne_coe.mp
    change (F z : ℂ) + turnScalar x.1 * (positiveCircleLoop x.2 : ℂ) ≠ F z
    rw [add_ne_left]
    exact mul_ne_zero (hturnScalar_ne x.1) (positiveCircleLoop x.2).2
  have hturn_closed (s : unitInterval) : Hturn (s, 1) = Hturn (s, 0) := by
    apply Subtype.ext
    change (F z : ℂ) + turnScalar s * (positiveCircleLoop 1 : ℂ) =
      (F z : ℂ) + turnScalar s * (positiveCircleLoop 0 : ℂ)
    simp
  have hhomTurn := normalizedImageLoopHomotopy G (F z) Hturn hturn_ne hturn_closed
  let normalizedRow (H : C(unitInterval × unitInterval, Ω₂))
      (hne : ∀ x, H x ≠ F z) (hclosed : ∀ s, H (s, 1) = H (s, 0))
      (s : unitInterval) :=
    normalizedImageLoop G (F z)
      (H.comp ⟨fun t ↦ (s, t), by fun_prop⟩)
      (fun t ↦ hne (s, t)) (hclosed s)
  have hShrink :
      (normalizedRow Hshrink hshrink_ne hshrink_closed 0).Homotopic
        (normalizedRow Hshrink hshrink_ne hshrink_closed 1) := by
    refine ⟨?_⟩
    simpa [normalizedRow] using hhomShrink
  have hScaled :
      (normalizedRow Hscaled hscaled_ne hscaled_closed 0).Homotopic
        (normalizedRow Hscaled hscaled_ne hscaled_closed 1) := by
    refine ⟨?_⟩
    simpa [normalizedRow] using hhomScaled
  have hTurn :
      (normalizedRow Hturn hturn_ne hturn_closed 0).Homotopic
        (normalizedRow Hturn hturn_ne hturn_closed 1) := by
    refine ⟨?_⟩
    simpa [normalizedRow] using hhomTurn
  have hstart :
      normalizedBoundaryLoop (F.trans G) z r hr hcircle =
        normalizedRow Hshrink hshrink_ne hshrink_closed 0 := by
    apply Path.ext
    funext t
    apply Subtype.ext
    simp [normalizedBoundaryLoop, normalizedImageLoop, normalizedRow,
      Hshrink, shrink, source, circlePath]
  have hjoinSource₁ (t : unitInterval) : Hshrink (1, t) = Hscaled (0, t) := by
    apply Subtype.ext
    dsimp [Hshrink, Hscaled, shrink]
    simp only [one_mul, sub_self, zero_add]
    change (F z : ℂ) + (ε : ℂ) * ((F (source t) : ℂ) - F z) =
      (F z : ℂ) + a * (HF (0, t) : ℂ)
    have hzero := HF.map_zero_left t
    change HF (0, t) = normalizedBoundaryLoop F z r hr hcircle t at hzero
    rw [hzero]
    simp [a, den, normalizedBoundaryLoop, source, circlePath]
    have hD : (F (source 0) : ℂ) - F z ≠ 0 := by simpa [den] using hden
    change (F ⟨circlePoint z r 0, hcircle 0⟩ : ℂ) - F z ≠ 0 at hD
    field_simp [hD]
  have hjoin₁ :
      normalizedRow Hshrink hshrink_ne hshrink_closed 1 =
        normalizedRow Hscaled hscaled_ne hscaled_closed 0 := by
    apply Path.ext
    funext t
    apply Subtype.ext
    change ((G (Hshrink (1, t)) : ℂ) - G (F z)) /
        ((G (Hshrink (1, 0)) : ℂ) - G (F z)) =
      ((G (Hscaled (0, t)) : ℂ) - G (F z)) /
        ((G (Hscaled (0, 0)) : ℂ) - G (F z))
    rw [hjoinSource₁ t, hjoinSource₁ 0]
  have hjoinSource₂ (t : unitInterval) : Hscaled (1, t) = Hturn (0, t) := by
    apply Subtype.ext
    dsimp [Hscaled, Hturn]
    change (F z : ℂ) + a * (HF (1, t) : ℂ) =
      (F z : ℂ) + turnScalar 0 * (positiveCircleLoop t : ℂ)
    have hone := HF.map_one_left t
    change HF (1, t) = positiveCircleLoop t at hone
    rw [hone]
    simp [turnScalar, turnRadius, turnAngle]
  have hjoin₂ :
      normalizedRow Hscaled hscaled_ne hscaled_closed 1 =
        normalizedRow Hturn hturn_ne hturn_closed 0 := by
    apply Path.ext
    funext t
    apply Subtype.ext
    change ((G (Hscaled (1, t)) : ℂ) - G (F z)) /
        ((G (Hscaled (1, 0)) : ℂ) - G (F z)) =
      ((G (Hturn (0, t)) : ℂ) - G (F z)) /
        ((G (Hturn (0, 0)) : ℂ) - G (F z))
    rw [hjoinSource₂ t, hjoinSource₂ 0]
  have hendSource (t : unitInterval) :
      Hturn (1, t) =
        ⟨circlePoint (F z : ℂ) rG t,
          circlePoint_mem_of_closedBall_subset (F z) hrG hballG t⟩ := by
    apply Subtype.ext
    simp [Hturn, turnScalar, turnRadius, turnAngle, circlePoint,
      positiveCircleLoop]
  have hend :
      normalizedRow Hturn hturn_ne hturn_closed 1 =
        normalizedBoundaryLoop G (F z) rG hrG
          (circlePoint_mem_of_closedBall_subset (F z) hrG hballG) := by
    apply Path.ext
    funext t
    apply Subtype.ext
    change ((G (Hturn (1, t)) : ℂ) - G (F z)) /
        ((G (Hturn (1, 0)) : ℂ) - G (F z)) =
      ((G ⟨circlePoint (F z : ℂ) rG t,
          circlePoint_mem_of_closedBall_subset (F z) hrG hballG t⟩ : ℂ) - G (F z)) /
        ((G ⟨circlePoint (F z : ℂ) rG 0,
          circlePoint_mem_of_closedBall_subset (F z) hrG hballG 0⟩ : ℂ) - G (F z))
    rw [hendSource t, hendSource 0]
  refine ⟨r, hr, hball, ?_⟩
  rw [hstart]
  have hScaled' :
      (normalizedRow Hshrink hshrink_ne hshrink_closed 1).Homotopic
        (normalizedRow Hscaled hscaled_ne hscaled_closed 1) := by
    rw [hjoin₁]
    exact hScaled
  have hTurn' :
      (normalizedRow Hscaled hscaled_ne hscaled_closed 1).Homotopic
        (normalizedRow Hturn hturn_ne hturn_closed 1) := by
    rw [hjoin₂]
    exact hTurn
  have hG' :
      (normalizedRow Hturn hturn_ne hturn_closed 1).Homotopic
        positiveCircleLoop := by
    rw [hend]
    exact hqG
  exact hShrink.trans (hScaled'.trans (hTurn'.trans hG'))

/--
%%handwave
name:
  Orientation preservation is symmetric under inversion
statement:
  Let $F:\Omega\to\Omega'$ be a homeomorphism between open planar domains.
  If $F$ preserves planar orientation, then $F^{-1}$ preserves planar
  orientation.
proof:
  At the preimage of a target point, shrink a forward orientation-witness
  circle until its image lies in a small target disk. Rescale the forward
  punctured-plane homotopy inside that disk, then rotate and expand its final
  positive circle to the target boundary. Applying $F^{-1}$ throughout gives
  a homotopy from the normalized boundary of $F^{-1}\circ F$ to the desired
  inverse boundary. The first loop is the positive circle because
  $F^{-1}\circ F$ is the identity, so reversing the homotopy proves that the
  inverse boundary is positive.
-/
theorem PreservesPlanarOrientation.symm
    {Ω Ω' : Set ℂ} {F : Ω ≃ₜ Ω'}
    (hF : PreservesPlanarOrientation F) (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω') :
    PreservesPlanarOrientation F.symm := by
  intro y
  let z : Ω := F.symm y
  have hy : F z = y := by simp [z]
  rw [← hy]
  obtain ⟨rF, hrF, hballF, hqF⟩ := hF z
  obtain ⟨R, hR, hRball⟩ := (Metric.isOpen_iff.mp hΩ') (F z) (F z).2
  let rG : ℝ := R / 2
  have hrG : 0 < rG := by dsimp [rG]; positivity
  have hrGR : rG < R := by dsimp [rG]; linarith
  have hballG : Metric.closedBall (F z : ℂ) rG ⊆ Ω' := by
    intro w hw
    apply hRball
    rw [Metric.mem_ball]
    exact lt_of_le_of_lt (Metric.mem_closedBall.mp hw) hrGR
  let Fval : Ω → ℂ := fun w ↦ F w
  have hFval : Continuous Fval := continuous_subtype_val.comp F.continuous
  obtain ⟨δ, hδ, hδmap⟩ :=
    (Metric.continuousAt_iff.mp hFval.continuousAt) rG hrG
  let r : ℝ := min rF δ / 2
  have hmin : 0 < min rF δ := lt_min hrF hδ
  have hr : 0 < r := by dsimp [r]; positivity
  have hrrF : r < rF := by
    dsimp [r]
    have hle := min_le_left rF δ
    linarith
  have hrδ : r < δ := by
    dsimp [r]
    have hle := min_le_right rF δ
    linarith
  have hball : Metric.closedBall (z : ℂ) r ⊆ Ω := by
    exact fun _ hw ↦ hballF (Metric.closedBall_subset_closedBall hrrF.le hw)
  let hcircle := circlePoint_mem_of_closedBall_subset z hr hball
  let source : C(unitInterval, Ω) := circlePath z r hcircle
  have hsource_ne (t : unitInterval) : source t ≠ z := by
    apply Subtype.coe_ne_coe.mp
    exact circlePoint_ne_center z hr t
  have hsource_closed : source 1 = source 0 := by
    apply Subtype.ext
    exact (circlePoint_one z r).trans (circlePoint_zero z r).symm
  have himage_close (t : unitInterval) :
      dist (F (source t) : ℂ) (F z : ℂ) < rG := by
    apply hδmap
    rw [Subtype.dist_eq]
    change dist (circlePoint z r t) z < δ
    rw [dist_circlePoint_center z hr t]
    exact hrδ
  have hfamilyF : ∀ s t : unitInterval,
      circlePoint z (((1 - (s : ℝ)) * r + (s : ℝ) * rF)) t ∈ Ω := by
    intro s t
    have hs0 : 0 ≤ (s : ℝ) := s.2.1
    have hs1 : (s : ℝ) ≤ 1 := s.2.2
    have hdiff : 0 ≤ rF - r := sub_nonneg.mpr hrrF.le
    have hradpos : 0 < (1 - (s : ℝ)) * r + (s : ℝ) * rF := by
      nlinarith [mul_nonneg hs0 hdiff]
    have hradle : (1 - (s : ℝ)) * r + (s : ℝ) * rF ≤ rF := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hs1) hdiff]
    apply hballF
    rw [Metric.mem_closedBall, dist_circlePoint_center z hradpos t]
    exact hradle
  have hq :
      (normalizedBoundaryLoop F z r hr hcircle).Homotopic positiveCircleLoop :=
    (normalizedBoundaryLoop_radius_homotopic
      F z r rF hr hrF hfamilyF).trans hqF
  rcases hq with ⟨HF⟩
  let den : ℂ := (F (source 0) : ℂ) - F z
  have hden : den ≠ 0 := by
    apply sub_ne_zero.mpr
    exact Subtype.coe_ne_coe.mpr (F.injective.ne (hsource_ne 0))
  obtain ⟨M₀, hM₀⟩ := isCompact_univ.exists_bound_of_continuousOn
    (continuous_subtype_val.comp HF.continuous).continuousOn
  let M : ℝ := max M₀ 1
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hHFbound (x : unitInterval × unitInterval) : ‖(HF x : ℂ)‖ ≤ M :=
    le_trans (hM₀ x (mem_univ x)) (le_max_left _ _)
  have hdennorm : 0 < ‖den‖ := norm_pos_iff.mpr hden
  let ε : ℝ := min 1 (rG / (2 * ‖den‖ * M))
  have hquot : 0 < rG / (2 * ‖den‖ * M) := by positivity
  have hεpos : 0 < ε := by
    dsimp [ε]
    exact lt_min zero_lt_one hquot
  have hεle : ε ≤ 1 := by dsimp [ε]; exact min_le_left _ _
  have hεbound : ε * ‖den‖ * M < rG := by
    have hεquot : ε ≤ rG / (2 * ‖den‖ * M) := by
      dsimp [ε]
      exact min_le_right _ _
    have hprod : ε * ‖den‖ * M ≤ rG / 2 := by
      calc
        ε * ‖den‖ * M ≤ (rG / (2 * ‖den‖ * M)) * ‖den‖ * M := by
          gcongr
        _ = rG / 2 := by field_simp
    linarith
  let shrink : unitInterval → ℝ := fun s ↦ (1 - (s : ℝ)) + (s : ℝ) * ε
  have hshrink_pos (s : unitInterval) : 0 < shrink s := by
    dsimp [shrink]
    have hs0 : 0 ≤ (s : ℝ) := s.2.1
    have hs1 : (s : ℝ) ≤ 1 := s.2.2
    nlinarith [mul_nonneg hs0 hεpos.le]
  have hshrink_le (s : unitInterval) : shrink s ≤ 1 := by
    dsimp [shrink]
    have hs0 : 0 ≤ (s : ℝ) := s.2.1
    nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hεle)]
  let Hshrink : C(unitInterval × unitInterval, Ω') :=
    ⟨fun x ↦ ⟨(F z : ℂ) + (shrink x.1 : ℂ) * ((F (source x.2) : ℂ) - F z), by
        apply hballG
        rw [Metric.mem_closedBall, Complex.dist_eq]
        simp only [add_sub_cancel_left, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg (hshrink_pos x.1).le]
        have him := himage_close x.2
        rw [Complex.dist_eq] at him
        exact le_of_lt (lt_of_le_of_lt
          (mul_le_of_le_one_left (norm_nonneg _) (hshrink_le x.1))
          him)⟩, by
      apply Continuous.subtype_mk
      exact continuous_const.add
        ((Complex.continuous_ofReal.comp (by fun_prop)).mul
          ((continuous_subtype_val.comp
            (F.continuous.comp (source.continuous.comp (by fun_prop)))).sub
              continuous_const))⟩
  have hshrink_ne (x : unitInterval × unitInterval) : Hshrink x ≠ F z := by
    apply Subtype.coe_ne_coe.mp
    change (F z : ℂ) + (shrink x.1 : ℂ) * ((F (source x.2) : ℂ) - F z) ≠ F z
    rw [add_ne_left]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt (hshrink_pos x.1)))
      (sub_ne_zero.mpr (Subtype.coe_ne_coe.mpr
        (F.injective.ne (hsource_ne x.2))))
  have hshrink_closed (s : unitInterval) : Hshrink (s, 1) = Hshrink (s, 0) := by
    apply Subtype.ext
    change (F z : ℂ) + (shrink s : ℂ) * ((F (source 1) : ℂ) - F z) =
      (F z : ℂ) + (shrink s : ℂ) * ((F (source 0) : ℂ) - F z)
    rw [hsource_closed]
  have hhomShrink := normalizedImageLoopHomotopy F.symm (F z) Hshrink
    hshrink_ne hshrink_closed
  let a : ℂ := (ε : ℂ) * den
  have ha : a ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hεpos)) hden
  have hanorm : ‖a‖ = ε * ‖den‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hεpos.le]
  let Hscaled : C(unitInterval × unitInterval, Ω') :=
    ⟨fun x ↦ ⟨(F z : ℂ) + a * (HF x : ℂ), by
        apply hballG
        rw [Metric.mem_closedBall, Complex.dist_eq, add_sub_cancel_left, norm_mul,
          hanorm]
        exact le_of_lt (lt_of_le_of_lt
          (mul_le_mul_of_nonneg_left (hHFbound x)
            (mul_nonneg hεpos.le hdennorm.le)) hεbound)⟩, by
      apply Continuous.subtype_mk
      exact continuous_const.add
        (continuous_const.mul (continuous_subtype_val.comp HF.continuous))⟩
  have hscaled_ne (x : unitInterval × unitInterval) : Hscaled x ≠ F z := by
    apply Subtype.coe_ne_coe.mp
    change (F z : ℂ) + a * (HF x : ℂ) ≠ F z
    rw [add_ne_left]
    exact mul_ne_zero ha (HF x).2
  have hscaled_closed (s : unitInterval) : Hscaled (s, 1) = Hscaled (s, 0) := by
    apply Subtype.ext
    change (F z : ℂ) + a * (HF (s, 1) : ℂ) =
      (F z : ℂ) + a * (HF (s, 0) : ℂ)
    have h1 := HF.prop' s 1 (by simp)
    have h0 := HF.prop' s 0 (by simp)
    change HF (s, 1) = _ at h1
    change HF (s, 0) = _ at h0
    rw [h1, h0]
    simp
  have hhomScaled := normalizedImageLoopHomotopy F.symm (F z) Hscaled
    hscaled_ne hscaled_closed
  have hMone : 1 ≤ M := le_max_right _ _
  have hanorm_lt : ‖a‖ < rG := by
    rw [hanorm]
    have hm := mul_le_mul_of_nonneg_left hMone
      (mul_nonneg hεpos.le hdennorm.le)
    exact lt_of_le_of_lt (by simpa using hm) hεbound
  let turnRadius : unitInterval → ℝ := fun s ↦
    (1 - (s : ℝ)) * ‖a‖ + (s : ℝ) * rG
  let turnAngle : unitInterval → ℝ := fun s ↦ (1 - (s : ℝ)) * Complex.arg a
  let turnScalar : unitInterval → ℂ := fun s ↦
    (turnRadius s : ℂ) * Complex.exp ((turnAngle s : ℂ) * Complex.I)
  have hturnRadius_pos (s : unitInterval) : 0 < turnRadius s := by
    dsimp [turnRadius]
    have hs0 : 0 ≤ (s : ℝ) := s.2.1
    have hs1 : (s : ℝ) ≤ 1 := s.2.2
    have had : 0 < ‖a‖ := norm_pos_iff.mpr ha
    nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hanorm_lt.le)]
  have hturnRadius_le (s : unitInterval) : turnRadius s ≤ rG := by
    dsimp [turnRadius]
    have hs0 : 0 ≤ (s : ℝ) := s.2.1
    have hs1 : (s : ℝ) ≤ 1 := s.2.2
    nlinarith [mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr hanorm_lt.le)]
  have hturnScalar_ne (s : unitInterval) : turnScalar s ≠ 0 := by
    exact mul_ne_zero
      (Complex.ofReal_ne_zero.mpr (ne_of_gt (hturnRadius_pos s)))
      (Complex.exp_ne_zero _)
  have hturnScalar_norm (s : unitInterval) : ‖turnScalar s‖ = turnRadius s := by
    dsimp [turnScalar]
    rw [norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (hturnRadius_pos s).le,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  let Hturn : C(unitInterval × unitInterval, Ω') :=
    ⟨fun x ↦ ⟨(F z : ℂ) + turnScalar x.1 * (positiveCircleLoop x.2 : ℂ), by
        apply hballG
        rw [Metric.mem_closedBall, Complex.dist_eq, add_sub_cancel_left, norm_mul,
          hturnScalar_norm]
        rw [show ‖(positiveCircleLoop x.2 : ℂ)‖ = 1 by
          rw [show (positiveCircleLoop x.2 : ℂ) =
              Complex.exp ((((2 * Real.pi * (x.2 : ℝ)) : ℝ) : ℂ) * Complex.I) by
            simp [positiveCircleLoop]]
          exact Complex.norm_exp_ofReal_mul_I _]
        simpa using hturnRadius_le x.1⟩, by
      apply Continuous.subtype_mk
      exact continuous_const.add
        (((Complex.continuous_ofReal.comp (by fun_prop)).mul
          (Complex.continuous_exp.comp (by fun_prop))).mul
            (continuous_subtype_val.comp
              (positiveCircleLoop.continuous.comp (by fun_prop))))⟩
  have hturn_ne (x : unitInterval × unitInterval) : Hturn x ≠ F z := by
    apply Subtype.coe_ne_coe.mp
    change (F z : ℂ) + turnScalar x.1 * (positiveCircleLoop x.2 : ℂ) ≠ F z
    rw [add_ne_left]
    exact mul_ne_zero (hturnScalar_ne x.1) (positiveCircleLoop x.2).2
  have hturn_closed (s : unitInterval) : Hturn (s, 1) = Hturn (s, 0) := by
    apply Subtype.ext
    change (F z : ℂ) + turnScalar s * (positiveCircleLoop 1 : ℂ) =
      (F z : ℂ) + turnScalar s * (positiveCircleLoop 0 : ℂ)
    simp
  have hhomTurn := normalizedImageLoopHomotopy F.symm (F z) Hturn
    hturn_ne hturn_closed
  let normalizedRow (H : C(unitInterval × unitInterval, Ω'))
      (hne : ∀ x, H x ≠ F z) (hclosed : ∀ s, H (s, 1) = H (s, 0))
      (s : unitInterval) :=
    normalizedImageLoop F.symm (F z)
      (H.comp ⟨fun t ↦ (s, t), by fun_prop⟩)
      (fun t ↦ hne (s, t)) (hclosed s)
  have hShrink :
      (normalizedRow Hshrink hshrink_ne hshrink_closed 0).Homotopic
        (normalizedRow Hshrink hshrink_ne hshrink_closed 1) := by
    refine ⟨?_⟩
    simpa [normalizedRow] using hhomShrink
  have hScaled :
      (normalizedRow Hscaled hscaled_ne hscaled_closed 0).Homotopic
        (normalizedRow Hscaled hscaled_ne hscaled_closed 1) := by
    refine ⟨?_⟩
    simpa [normalizedRow] using hhomScaled
  have hTurn :
      (normalizedRow Hturn hturn_ne hturn_closed 0).Homotopic
        (normalizedRow Hturn hturn_ne hturn_closed 1) := by
    refine ⟨?_⟩
    simpa [normalizedRow] using hhomTurn
  have hstart :
      normalizedBoundaryLoop (F.trans F.symm) z r hr hcircle =
        normalizedRow Hshrink hshrink_ne hshrink_closed 0 := by
    apply Path.ext
    funext t
    apply Subtype.ext
    simp [normalizedBoundaryLoop, normalizedImageLoop, normalizedRow,
      Hshrink, shrink, source, circlePath]
  have hjoinSource₁ (t : unitInterval) : Hshrink (1, t) = Hscaled (0, t) := by
    apply Subtype.ext
    dsimp [Hshrink, Hscaled, shrink]
    simp only [one_mul, sub_self, zero_add]
    change (F z : ℂ) + (ε : ℂ) * ((F (source t) : ℂ) - F z) =
      (F z : ℂ) + a * (HF (0, t) : ℂ)
    have hzero := HF.map_zero_left t
    change HF (0, t) = normalizedBoundaryLoop F z r hr hcircle t at hzero
    rw [hzero]
    simp [a, den, normalizedBoundaryLoop, source, circlePath]
    have hD : (F (source 0) : ℂ) - F z ≠ 0 := by
      simpa [den] using hden
    change (F ⟨circlePoint z r 0, hcircle 0⟩ : ℂ) - F z ≠ 0 at hD
    field_simp [hD]
  have hjoin₁ :
      normalizedRow Hshrink hshrink_ne hshrink_closed 1 =
        normalizedRow Hscaled hscaled_ne hscaled_closed 0 := by
    apply Path.ext
    funext t
    apply Subtype.ext
    change ((F.symm (Hshrink (1, t)) : ℂ) - F.symm (F z)) /
        ((F.symm (Hshrink (1, 0)) : ℂ) - F.symm (F z)) =
      ((F.symm (Hscaled (0, t)) : ℂ) - F.symm (F z)) /
        ((F.symm (Hscaled (0, 0)) : ℂ) - F.symm (F z))
    rw [hjoinSource₁ t, hjoinSource₁ 0]
  have hjoinSource₂ (t : unitInterval) : Hscaled (1, t) = Hturn (0, t) := by
    apply Subtype.ext
    dsimp [Hscaled, Hturn]
    change (F z : ℂ) + a * (HF (1, t) : ℂ) =
      (F z : ℂ) + turnScalar 0 * (positiveCircleLoop t : ℂ)
    have hone := HF.map_one_left t
    change HF (1, t) = positiveCircleLoop t at hone
    rw [hone]
    simp [turnScalar, turnRadius, turnAngle]
  have hjoin₂ :
      normalizedRow Hscaled hscaled_ne hscaled_closed 1 =
        normalizedRow Hturn hturn_ne hturn_closed 0 := by
    apply Path.ext
    funext t
    apply Subtype.ext
    change ((F.symm (Hscaled (1, t)) : ℂ) - F.symm (F z)) /
        ((F.symm (Hscaled (1, 0)) : ℂ) - F.symm (F z)) =
      ((F.symm (Hturn (0, t)) : ℂ) - F.symm (F z)) /
        ((F.symm (Hturn (0, 0)) : ℂ) - F.symm (F z))
    rw [hjoinSource₂ t, hjoinSource₂ 0]
  have hendSource (t : unitInterval) :
      Hturn (1, t) =
        ⟨circlePoint (F z : ℂ) rG t,
          circlePoint_mem_of_closedBall_subset (F z) hrG hballG t⟩ := by
    apply Subtype.ext
    simp [Hturn, turnScalar, turnRadius, turnAngle, circlePoint,
      positiveCircleLoop]
  have hend :
      normalizedRow Hturn hturn_ne hturn_closed 1 =
        normalizedBoundaryLoop F.symm (F z) rG hrG
          (circlePoint_mem_of_closedBall_subset (F z) hrG hballG) := by
    apply Path.ext
    funext t
    apply Subtype.ext
    change ((F.symm (Hturn (1, t)) : ℂ) - F.symm (F z)) /
        ((F.symm (Hturn (1, 0)) : ℂ) - F.symm (F z)) =
      ((F.symm ⟨circlePoint (F z : ℂ) rG t,
          circlePoint_mem_of_closedBall_subset (F z) hrG hballG t⟩ : ℂ) -
          F.symm (F z)) /
        ((F.symm ⟨circlePoint (F z : ℂ) rG 0,
          circlePoint_mem_of_closedBall_subset (F z) hrG hballG 0⟩ : ℂ) -
          F.symm (F z))
    rw [hendSource t, hendSource 0]
  refine ⟨rG, hrG, hballG, ?_⟩
  have hScaled' :
      (normalizedRow Hshrink hshrink_ne hshrink_closed 1).Homotopic
        (normalizedRow Hscaled hscaled_ne hscaled_closed 1) := by
    rw [hjoin₁]
    exact hScaled
  have hTurn' :
      (normalizedRow Hscaled hscaled_ne hscaled_closed 1).Homotopic
        (normalizedRow Hturn hturn_ne hturn_closed 1) := by
    rw [hjoin₂]
    exact hTurn
  have hchain :
      (normalizedBoundaryLoop (F.trans F.symm) z r hr hcircle).Homotopic
        (normalizedBoundaryLoop F.symm (F z) rG hrG
          (circlePoint_mem_of_closedBall_subset (F z) hrG hballG)) := by
    rw [hstart, ← hend]
    exact hShrink.trans (hScaled'.trans hTurn')
  have hcomp : F.trans F.symm = Homeomorph.refl Ω := by
    ext w
    exact congrArg Subtype.val (F.symm_apply_apply w)
  have hstart_positive :
      (normalizedBoundaryLoop (F.trans F.symm) z r hr hcircle).Homotopic
        positiveCircleLoop := by
    rw [hcomp, normalizedBoundaryLoop_refl]
  exact hchain.symm.trans hstart_positive

/--
%%handwave
name:
  Whole-plane homeomorphism on the universal planar domains
statement:
  A homeomorphism $F:\mathbb C\to\mathbb C$ restricts to the corresponding
  homeomorphism between the universal planar domains
  $\mathbb C\subseteq\mathbb C$ and $\mathbb C\subseteq\mathbb C$.
-/
def wholePlaneSubtypeHomeomorph (F : ℂ ≃ₜ ℂ) :
    (Set.univ : Set ℂ) ≃ₜ (Set.univ : Set ℂ) :=
  F.subtype (p := fun _ ↦ True) (q := fun _ ↦ True) (fun _ ↦ Iff.rfl)

/--
%%handwave
name:
  Ambient value of the whole-plane subtype homeomorphism
statement:
  The universal-domain restriction of $F$ has ambient value $F(z)$ at every
  point $z$.
proof:
  Restriction to the universal set does not change the forward map.
-/
@[simp]
theorem wholePlaneSubtypeHomeomorph_apply (F : ℂ ≃ₜ ℂ)
    (z : (Set.univ : Set ℂ)) :
    (wholePlaneSubtypeHomeomorph F z : ℂ) = F z := rfl

/--
%%handwave
name:
  Fibers of a plane homeomorphism are discrete
statement:
  For every homeomorphism $F:\mathbb C\to\mathbb C$ and every $w$, the fiber
  $F^{-1}(w)$ is a discrete subset of the plane.
proof:
  Injectivity makes the fiber a subsingleton, and every subsingleton subset is
  discrete.
-/
theorem isDiscrete_fiber_homeomorph (F : ℂ ≃ₜ ℂ) (w : ℂ) :
    IsDiscrete {z : ℂ | F z = w} := by
  apply Set.Subsingleton.isDiscrete
  intro x hx y hy
  exact F.injective (hx.trans hy.symm)

/--
%%handwave
name:
  Clopen neighborhoods of compact connected components
statement:
  Let $X$ be compact Hausdorff, let $x\in X$, and let $U$ be open with
  $\operatorname{Comp}_X(x)\subseteq U$. There is a clopen set $C$ such that
  $$
    \operatorname{Comp}_X(x)\subseteq C\subseteq U.
  $$
proof:
  In a compact Hausdorff space, the connected component of $x$ is the
  intersection of all clopen neighborhoods of $x$. These neighborhoods form
  a family directed by finite intersections. Compactness therefore puts one
  of them inside the prescribed neighborhood $U$.
-/
theorem exists_isClopen_connectedComponent_subset_of_compact
    {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] {x : X} {U : Set X} (hUopen : IsOpen U)
    (hcomponent : connectedComponent x ⊆ U) :
    ∃ C : Set X, IsClopen C ∧
      connectedComponent x ⊆ C ∧ C ⊆ U := by
  let J := {C : Set X // IsClopen C ∧ x ∈ C}
  let F : J → Set X := fun C ↦ C
  letI : Nonempty J :=
    ⟨⟨Set.univ, isClopen_univ, Set.mem_univ x⟩⟩
  have hdir : Directed (fun A B : Set X ↦ A ⊇ B) F := by
    intro A B
    let C : J :=
      ⟨(A : Set X) ∩ (B : Set X), A.2.1.inter B.2.1,
        A.2.2, B.2.2⟩
    exact ⟨C, inter_subset_left, inter_subset_right⟩
  have hclosed (C : J) : IsClosed (F C) := C.2.1.1
  have hinter : (⋂ C, F C) = connectedComponent x :=
    (connectedComponent_eq_iInter_isClopen x).symm
  obtain ⟨C, hCU⟩ :=
    exists_subset_nhds_of_compactSpace hdir hclosed
      (U := U)
      (fun y hy ↦ hUopen.mem_nhds
        (hcomponent (hinter ▸ hy)))
  refine ⟨C, C.2.1, ?_, hCU⟩
  rw [← hinter]
  exact iInter_subset F C

/--
%%handwave
name:
  Directed intersection of continua
statement:
  In a Hausdorff normal space, let $(K_i)_{i\in I}$ be a nonempty family of
  nonempty compact connected sets which is directed by reverse inclusion.
  Then
  $$
    \bigcap_{i\in I}K_i
  $$
  is nonempty and connected.
proof:
  Compactness gives nonemptiness of the directed intersection. If the
  intersection were disconnected, its two compact pieces would have
  disjoint open neighborhoods. Directed compactness puts some $K_i$ inside
  their union, while both pieces still meet $K_i$. This contradicts
  connectedness of $K_i$.
-/
theorem isConnected_iInter_of_directed_nonempty_compact_connected
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormalSpace X] [Nonempty ι] (K : ι → Set X)
    (hdir : Directed (fun A B : Set X ↦ A ⊇ B) K)
    (hcompact : ∀ i, IsCompact (K i))
    (hconnected : ∀ i, IsConnected (K i)) :
    IsConnected (⋂ i, K i) := by
  let I : Set X := ⋂ i, K i
  have hclosed (i : ι) : IsClosed (K i) := (hcompact i).isClosed
  have hInonempty : I.Nonempty := by
    exact IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      K hdir (fun i ↦ (hconnected i).nonempty) hcompact hclosed
  let i₀ : ι := Classical.choice inferInstance
  have hIclosed : IsClosed I := isClosed_iInter hclosed
  have hIcompact : IsCompact I :=
    (hcompact i₀).of_isClosed_subset hIclosed (iInter_subset K i₀)
  refine ⟨hInonempty, ?_⟩
  rw [isPreconnected_iff_subset_of_disjoint]
  intro u v hu hv hIuv hIinter
  by_cases hIu : I ⊆ u
  · exact Or.inl hIu
  by_cases hIv : I ⊆ v
  · exact Or.inr hIv
  let A : Set X := I \ v
  let B : Set X := I \ u
  have hAcompact : IsCompact A := hIcompact.diff hv
  have hBcompact : IsCompact B := hIcompact.diff hu
  have hAnonempty : A.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hAempty
    apply hIv
    intro x hxI
    by_contra hxv
    have hxA : x ∈ A := ⟨hxI, hxv⟩
    rw [hAempty] at hxA
    exact hxA
  have hBnonempty : B.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hBempty
    apply hIu
    intro x hxI
    by_contra hxu
    have hxB : x ∈ B := ⟨hxI, hxu⟩
    rw [hBempty] at hxB
    exact hxB
  have hABdisjoint : Disjoint A B := by
    rw [Set.disjoint_left]
    intro x hxA hxB
    rcases hIuv hxA.1 with hxu | hxv
    · exact hxB.2 hxu
    · exact hxA.2 hxv
  have hIAB : I ⊆ A ∪ B := by
    intro x hxI
    rcases hIuv hxI with hxu | hxv
    · refine Or.inl ⟨hxI, ?_⟩
      intro hxv
      have hx : x ∈ I ∩ (u ∩ v) := ⟨hxI, hxu, hxv⟩
      rw [hIinter] at hx
      exact hx
    · refine Or.inr ⟨hxI, ?_⟩
      intro hxu
      have hx : x ∈ I ∩ (u ∩ v) := ⟨hxI, hxu, hxv⟩
      rw [hIinter] at hx
      exact hx
  obtain ⟨U, V, hUopen, hVopen, hAU, hBV, hUV⟩ :=
    normal_separation hAcompact.isClosed hBcompact.isClosed
      hABdisjoint
  have hIUV : I ⊆ U ∪ V :=
    hIAB.trans (Set.union_subset_union hAU hBV)
  obtain ⟨i, hi⟩ := exists_subset_nhds_of_isCompact hdir hcompact
    (U := U ∪ V)
    (fun x hxI ↦ (hUopen.union hVopen).mem_nhds (hIUV hxI))
  rcases (hconnected i).isPreconnected.subset_or_subset
      hUopen hVopen hUV hi with hKiU | hKiV
  · obtain ⟨b, hbB⟩ := hBnonempty
    have hbI : b ∈ I := hbB.1
    have hbKi : b ∈ K i := (iInter_subset K i) hbI
    exact (Set.disjoint_left.mp hUV (hKiU hbKi) (hBV hbB)).elim
  · obtain ⟨a, haA⟩ := hAnonempty
    have haI : a ∈ I := haA.1
    have haKi : a ∈ K i := (iInter_subset K i) haI
    exact (Set.disjoint_left.mp hUV (hAU haA) (hKiV haKi)).elim

/--
%%handwave
name:
  Nested intersection of continua
statement:
  In a Hausdorff normal space, let
  $$
    K_0\supseteq K_1\supseteq K_2\supseteq\cdots
  $$
  be nonempty compact connected sets. Then
  $\bigcap_{n=0}^{\infty}K_n$ is nonempty and connected.
proof:
  A decreasing sequence is directed by reverse inclusion, so this is the
  [directed intersection theorem](lean:JJMath.Quasiconformal.isConnected_iInter_of_directed_nonempty_compact_connected).
-/
theorem isConnected_iInter_of_antitone_nonempty_compact_connected
    {X : Type*} [TopologicalSpace X] [T2Space X] [NormalSpace X]
    (K : ℕ → Set X) (hanti : Antitone K)
    (hcompact : ∀ n, IsCompact (K n))
    (hconnected : ∀ n, IsConnected (K n)) :
    IsConnected (⋂ n, K n) :=
  isConnected_iInter_of_directed_nonempty_compact_connected
    K hanti.directed_ge hcompact hconnected

/--
%%handwave
name:
  Boundary-avoiding neighborhoods of compact totally disconnected sets
statement:
  Let $F\subseteq\mathbb C$ be compact and totally disconnected, let $U$ be
  open, and let $x\in F\cap U$. There is an open set $V$ such that
  $$
    x\in V,\qquad \overline V\subseteq U,\qquad
    \partial V\cap F=\varnothing.
  $$
proof:
  In the compact space $F$, choose a clopen neighborhood $C$ of $x$ contained
  in $F\cap U$. Its images $C$ and $F\setminus C$ in the plane are disjoint
  compact sets. Normality gives an open neighborhood $V$ of $C$ whose closure
  lies in $U\setminus(F\setminus C)$. Points of $C$ lie in the interior of
  $V$, while points of $F\setminus C$ lie outside its closure, so the boundary
  misses $F$.
-/
theorem exists_open_closure_subset_frontier_disjoint_of_compact_totallyDisconnected
    {F U : Set ℂ} (hFcompact : IsCompact F)
    (hFtd : IsTotallyDisconnected F) (hU : IsOpen U)
    {x : ℂ} (hxF : x ∈ F) (hxU : x ∈ U) :
    ∃ V : Set ℂ, IsOpen V ∧ x ∈ V ∧ closure V ⊆ U ∧
      Disjoint (frontier V) F := by
  let xF : F := ⟨x, hxF⟩
  let UF : Set F := ((↑) : F → ℂ) ⁻¹' U
  have hUFopen : IsOpen UF := hU.preimage continuous_subtype_val
  have hxUF : xF ∈ UF := hxU
  letI : CompactSpace F := isCompact_iff_compactSpace.mp hFcompact
  letI : TotallyDisconnectedSpace F :=
    totallyDisconnectedSpace_subtype_iff.mpr hFtd
  obtain ⟨C, hCclopen, hxC, hCU⟩ :=
    compact_exists_isClopen_in_isOpen hUFopen hxUF
  let K : Set ℂ := ((↑) : F → ℂ) '' C
  let L : Set ℂ := ((↑) : F → ℂ) '' Cᶜ
  have hKcompact : IsCompact K :=
    hCclopen.1.isCompact.image continuous_subtype_val
  have hLcompact : IsCompact L :=
    hCclopen.compl.1.isCompact.image continuous_subtype_val
  have hKclosed : IsClosed K := hKcompact.isClosed
  have hLclosed : IsClosed L := hLcompact.isClosed
  have hxK : x ∈ K := ⟨xF, hxC, rfl⟩
  have hKU : K ⊆ U := by
    rintro y ⟨yF, hyC, rfl⟩
    exact hCU hyC
  have hKL : Disjoint K L := by
    rw [Set.disjoint_left]
    rintro y ⟨yF, hyC, rfl⟩ ⟨yF', hyC', hyEq⟩
    have : yF = yF' := Subtype.ext hyEq.symm
    subst yF'
    exact hyC' hyC
  have hFsub : F ⊆ K ∪ L := by
    intro y hyF
    let yF : F := ⟨y, hyF⟩
    by_cases hyC : yF ∈ C
    · exact Or.inl ⟨yF, hyC, rfl⟩
    · exact Or.inr ⟨yF, hyC, rfl⟩
  let T : Set ℂ := U \ L
  have hTopen : IsOpen T := hU.sdiff hLclosed
  have hKT : K ⊆ T := by
    intro y hyK
    exact ⟨hKU hyK, Set.disjoint_left.mp hKL hyK⟩
  obtain ⟨V, hVopen, hKV, hVclosure⟩ :=
    normal_exists_closure_subset hKclosed hTopen hKT
  refine ⟨V, hVopen, hKV hxK, ?_, ?_⟩
  · intro y hy
    exact (hVclosure hy).1
  · rw [Set.disjoint_left]
    intro y hyfront hyF
    rcases hFsub hyF with hyK | hyL
    · have hyV : y ∈ V := hKV hyK
      have hyInterior : y ∈ interior V :=
        mem_interior_iff_mem_nhds.mpr (hVopen.mem_nhds hyV)
      exact hyfront.2 hyInterior
    · exact (hVclosure hyfront.1).2 hyL

/--
%%handwave
name:
  Boundary-avoiding neighborhoods for light planar fibers
statement:
  Let $f:\mathbb C\to\mathbb C$ be continuous and suppose every connected
  subset of every fiber $f^{-1}(w)$ is a singleton or empty. If $f(x)=w$ and
  $U$ is an open neighborhood of $x$, then there is an open set $V$ such that
  $$
    x\in V,\qquad \overline V\subseteq U,\qquad
    \partial V\cap f^{-1}(w)=\varnothing.
  $$
  Moreover, $\overline V$ is compact.
proof:
  Choose a closed disk centered at $x$ and contained in $U$. The part of the
  fiber in that disk is compact and totally disconnected. Apply the [boundary-avoiding neighborhood theorem](lean:JJMath.Quasiconformal.exists_open_closure_subset_frontier_disjoint_of_compact_totallyDisconnected) inside a smaller concentric disk. Since the resulting closure stays in the smaller disk, every fiber point on its boundary would belong to the compact fiber piece, which the construction excludes.
-/
theorem exists_open_closure_subset_frontier_disjoint_fiber_of_light
    {f : ℂ → ℂ} (hf : Continuous f)
    (hlight : ∀ w (E : Set ℂ), IsConnected E →
      E ⊆ {z : ℂ | f z = w} → E.Subsingleton)
    {x w : ℂ} (hxw : f x = w) {U : Set ℂ}
    (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ V : Set ℂ, IsOpen V ∧ x ∈ V ∧ closure V ⊆ U ∧
      IsCompact (closure V) ∧
      Disjoint (frontier V) {z : ℂ | f z = w} := by
  let fiber : Set ℂ := {z : ℂ | f z = w}
  have hfiberClosed : IsClosed fiber :=
    isClosed_singleton.preimage hf
  have hfiberTD : IsTotallyDisconnected fiber := by
    intro E hEsub hEpre
    rcases E.eq_empty_or_nonempty with rfl | hEnonempty
    · exact subsingleton_empty
    · exact hlight w E ⟨hEnonempty, hEpre⟩ hEsub
  obtain ⟨r, hr, hballU⟩ := Metric.isOpen_iff.mp hU x hxU
  let ρ : ℝ := r / 2
  have hρ : 0 < ρ := by positivity
  let F : Set ℂ := fiber ∩ Metric.closedBall x ρ
  have hFcompact : IsCompact F :=
    (ProperSpace.isCompact_closedBall x ρ).inter_left hfiberClosed
  have hFtd : IsTotallyDisconnected F := by
    intro E hEF hEpre
    exact hfiberTD E (hEF.trans inter_subset_left) hEpre
  have hxF : x ∈ F := ⟨hxw, by simp [ρ, hρ.le]⟩
  have hxball : x ∈ Metric.ball x ρ := by simp [hρ]
  obtain ⟨V, hVopen, hxV, hVclosure, hVfrontier⟩ :=
    exists_open_closure_subset_frontier_disjoint_of_compact_totallyDisconnected
      hFcompact hFtd Metric.isOpen_ball hxF hxball
  have hVcompact : IsCompact (closure V) :=
    (ProperSpace.isCompact_closedBall x ρ).of_isClosed_subset
      isClosed_closure
      (hVclosure.trans Metric.ball_subset_closedBall)
  refine ⟨V, hVopen, hxV, ?_, hVcompact, ?_⟩
  · exact hVclosure.trans <|
      (Metric.ball_subset_ball (by dsimp [ρ]; linarith)).trans hballU
  · rw [Set.disjoint_left]
    intro y hyfront hyfiber
    apply Set.disjoint_left.mp hVfrontier hyfront
    exact ⟨hyfiber, Metric.mem_closedBall.mpr
      (le_of_lt (Metric.mem_ball.mp (hVclosure hyfront.1)))⟩

/--
%%handwave
name:
  Boundary of a component of an open planar set
statement:
  If $W\subseteq\mathbb C$ is open, $x\in W$, and $C$ is the connected
  component of $x$ in $W$, then
  $$
    \partial C\subseteq\partial W.
  $$
proof:
  The component $C$ is open because the plane is locally connected. It is
  also closed relative to $W$: in the subspace $W$ it is an ordinary
  connected component, hence closed. Thus a point in the closure of $C$
  which still lies in $W$ belongs to $C$ and cannot lie on its boundary.
-/
theorem frontier_connectedComponentIn_subset_frontier_of_isOpen
    {W : Set ℂ} {x : ℂ} (hWopen : IsOpen W) (hxW : x ∈ W) :
    frontier (connectedComponentIn W x) ⊆ frontier W := by
  intro y hyfront
  have hCsubW : connectedComponentIn W x ⊆ W :=
    connectedComponentIn_subset W x
  have hyClosureW : y ∈ closure W :=
    closure_mono hCsubW hyfront.1
  refine ⟨hyClosureW, ?_⟩
  intro hyInteriorW
  have hyW : y ∈ W := interior_subset hyInteriorW
  have hyClosureSubtype :
      (⟨y, hyW⟩ : W) ∈
        closure (connectedComponent (⟨x, hxW⟩ : W)) := by
    rw [closure_subtype, ← connectedComponentIn_eq_image hxW]
    exact hyfront.1
  have hyComponentSubtype :
      (⟨y, hyW⟩ : W) ∈
        connectedComponent (⟨x, hxW⟩ : W) :=
    (isClosed_connectedComponent.closure_subset_iff.mpr subset_rfl)
      hyClosureSubtype
  have hyComponent : y ∈ connectedComponentIn W x := by
    rw [connectedComponentIn_eq_image hxW]
    exact ⟨⟨y, hyW⟩, hyComponentSubtype, rfl⟩
  have hCopen : IsOpen (connectedComponentIn W x) :=
    hWopen.connectedComponentIn
  exact hyfront.2 <|
    mem_interior_iff_mem_nhds.mpr (hCopen.mem_nhds hyComponent)

/--
%%handwave
name:
  Connected boundary-avoiding neighborhoods for light planar fibers
statement:
  Let $f:\mathbb C\to\mathbb C$ be continuous and suppose every connected
  subset of every fiber is a singleton or empty. If $f(x)=w$ and $U$ is an
  open neighborhood of $x$, then there is a connected open set $V$ such that
  $$
    x\in V,\qquad \overline V\subseteq U,\qquad
    \partial V\cap f^{-1}(w)=\varnothing.
  $$
  Moreover, $\overline V$ is compact.
proof:
  First choose a possibly disconnected [boundary-avoiding neighborhood](lean:JJMath.Quasiconformal.exists_open_closure_subset_frontier_disjoint_fiber_of_light). Take its connected component containing $x$. Components of open subsets of the plane are open, their closures remain in the original closure, and [their boundaries lie in the original boundary](lean:JJMath.Quasiconformal.frontier_connectedComponentIn_subset_frontier_of_isOpen).
-/
theorem exists_connected_open_closure_subset_frontier_disjoint_fiber_of_light
    {f : ℂ → ℂ} (hf : Continuous f)
    (hlight : ∀ w (E : Set ℂ), IsConnected E →
      E ⊆ {z : ℂ | f z = w} → E.Subsingleton)
    {x w : ℂ} (hxw : f x = w) {U : Set ℂ}
    (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ V : Set ℂ, IsOpen V ∧ IsConnected V ∧ x ∈ V ∧
      closure V ⊆ U ∧ IsCompact (closure V) ∧
      Disjoint (frontier V) {z : ℂ | f z = w} := by
  obtain ⟨W, hWopen, hxW, hWclosure, hWcompact, hWfrontier⟩ :=
    exists_open_closure_subset_frontier_disjoint_fiber_of_light
      hf hlight hxw hU hxU
  let V : Set ℂ := connectedComponentIn W x
  have hVopen : IsOpen V := hWopen.connectedComponentIn
  have hxV : x ∈ V := mem_connectedComponentIn hxW
  have hVconnected : IsConnected V :=
    isConnected_connectedComponentIn_iff.mpr hxW
  have hVclosure : closure V ⊆ U :=
    (closure_mono (connectedComponentIn_subset W x)).trans hWclosure
  have hVcompact : IsCompact (closure V) :=
    hWcompact.of_isClosed_subset isClosed_closure
      (closure_mono (connectedComponentIn_subset W x))
  have hVfrontier : Disjoint (frontier V) {z : ℂ | f z = w} := by
    rw [Set.disjoint_left] at hWfrontier ⊢
    intro y hyV hyfiber
    exact hWfrontier
      (frontier_connectedComponentIn_subset_frontier_of_isOpen
        hWopen hxW hyV) hyfiber
  exact ⟨V, hVopen, hVconnected, hxV, hVclosure, hVcompact, hVfrontier⟩

/--
%%handwave
name:
  Small target-ball components are trapped for light maps
statement:
  Let $f:\mathbb C\to\mathbb C$ be continuous and light, let $f(x)=w$, and
  let $V$ be an open neighborhood of $x$ with compact closure. There is an
  $r>0$ such that the connected component $C_r$ of $x$ in
  $$
    \overline V\cap f^{-1}\bigl(\overline B(w,r)\bigr)
  $$
  is disjoint from $\partial V$.
proof:
  If every component reached $\partial V$, take radii $2^{-n}$ and the
  corresponding decreasing compact connected components. Their intersections
  with $\partial V$ are decreasing nonempty compact sets, so they have a
  common boundary point. The [nested intersection of the components is connected](lean:JJMath.Quasiconformal.isConnected_iInter_of_antitone_nonempty_compact_connected), contains both $x$ and that boundary point, and lies in $f^{-1}(w)$. Lightness makes it a singleton, contradicting $x\in V$.
-/
theorem exists_closedBall_preimage_component_disjoint_frontier_of_light
    {f : ℂ → ℂ} (hf : Continuous f)
    (hlight : ∀ w (E : Set ℂ), IsConnected E →
      E ⊆ {z : ℂ | f z = w} → E.Subsingleton)
    {x w : ℂ} (hxw : f x = w) {V : Set ℂ}
    (hVopen : IsOpen V) (hxV : x ∈ V)
    (hVcompact : IsCompact (closure V)) :
    ∃ r : ℝ, 0 < r ∧
      Disjoint
        (connectedComponentIn
          (closure V ∩ f ⁻¹' Metric.closedBall w r) x)
        (frontier V) := by
  let r : ℕ → ℝ := fun n ↦ (1 / 2 : ℝ) ^ n
  have hrpos (n : ℕ) : 0 < r n := by
    dsimp [r]
    positivity
  have hranti : Antitone r := by
    apply antitone_nat_of_succ_le
    intro n
    dsimp [r]
    rw [pow_succ]
    have hn : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
    nlinarith
  let S : ℕ → Set ℂ := fun n ↦
    closure V ∩ f ⁻¹' Metric.closedBall w (r n)
  have hScompact (n : ℕ) : IsCompact (S n) :=
    hVcompact.inter_right (Metric.isClosed_closedBall.preimage hf)
  have hxS (n : ℕ) : x ∈ S n := by
    refine ⟨subset_closure hxV, ?_⟩
    change dist (f x) w ≤ r n
    rw [hxw, dist_self]
    exact (hrpos n).le
  have hSanti : Antitone S := by
    intro m n hmn z hz
    refine ⟨hz.1, ?_⟩
    exact preimage_mono
      (Metric.closedBall_subset_closedBall (hranti hmn)) hz.2
  let K : ℕ → Set ℂ := fun n ↦ connectedComponentIn (S n) x
  have hxK (n : ℕ) : x ∈ K n :=
    mem_connectedComponentIn (hxS n)
  have hKconnected (n : ℕ) : IsConnected (K n) :=
    isConnected_connectedComponentIn_iff.mpr (hxS n)
  have hKcompact (n : ℕ) : IsCompact (K n) := by
    letI : CompactSpace (S n) :=
      isCompact_iff_compactSpace.mp (hScompact n)
    change IsCompact (connectedComponentIn (S n) x)
    rw [connectedComponentIn_eq_image (hxS n)]
    exact isClosed_connectedComponent.isCompact.image
      continuous_subtype_val
  have hKanti : Antitone K := by
    intro m n hmn
    exact connectedComponentIn_mono x (hSanti hmn)
  by_contra hnone
  have hnone' (ρ : ℝ) (hρ : 0 < ρ) :
      ¬ Disjoint
        (connectedComponentIn
          (closure V ∩ f ⁻¹' Metric.closedBall w ρ) x)
        (frontier V) := by
    intro hdisjoint
    exact hnone ⟨ρ, hρ, hdisjoint⟩
  have hLnonempty (n : ℕ) :
      (K n ∩ frontier V).Nonempty :=
    Set.not_disjoint_iff_nonempty_inter.mp (hnone' (r n) (hrpos n))
  let L : ℕ → Set ℂ := fun n ↦ K n ∩ frontier V
  have hLcompact (n : ℕ) : IsCompact (L n) :=
    (hKcompact n).inter_right isClosed_frontier
  have hLclosed (n : ℕ) : IsClosed (L n) :=
    (hLcompact n).isClosed
  have hLstep (n : ℕ) : L (n + 1) ⊆ L n := by
    intro z hz
    exact ⟨hKanti (Nat.le_succ n) hz.1, hz.2⟩
  have hLinterNonempty : (⋂ n, L n).Nonempty :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      L hLstep hLnonempty (hLcompact 0) hLclosed
  obtain ⟨y, hyL⟩ := hLinterNonempty
  have hyK (n : ℕ) : y ∈ K n :=
    (Set.mem_iInter.mp hyL n).1
  have hyfront : y ∈ frontier V :=
    (Set.mem_iInter.mp hyL 0).2
  have hKinterConnected : IsConnected (⋂ n, K n) :=
    isConnected_iInter_of_antitone_nonempty_compact_connected
      K hKanti hKcompact hKconnected
  have hKinterFiber :
      (⋂ n, K n) ⊆ {z : ℂ | f z = w} := by
    intro z hzK
    have hzS (n : ℕ) : z ∈ S n :=
      connectedComponentIn_subset (S n) x
        (Set.mem_iInter.mp hzK n)
    have hdistLe (n : ℕ) : dist (f z) w ≤ r n :=
      (hzS n).2
    have hrzero : Filter.Tendsto r Filter.atTop (nhds 0) := by
      dsimp [r]
      exact tendsto_pow_atTop_nhds_zero_of_abs_lt_one
        (by norm_num)
    have hdistNonpos : dist (f z) w ≤ 0 :=
      le_of_tendsto_of_tendsto' tendsto_const_nhds hrzero hdistLe
    exact dist_le_zero.mp hdistNonpos
  have hsubsingleton : (⋂ n, K n).Subsingleton :=
    hlight w (⋂ n, K n) hKinterConnected hKinterFiber
  have hxy : x = y :=
    hsubsingleton (Set.mem_iInter.mpr hxK)
      (Set.mem_iInter.mpr hyK)
  subst y
  have hxInterior : x ∈ interior V :=
    mem_interior_iff_mem_nhds.mpr (hVopen.mem_nhds hxV)
  exact hyfront.2 hxInterior

/--
%%handwave
name:
  Normal source domains for light planar maps
statement:
  Let $f:\mathbb C\to\mathbb C$ be continuous and light, let $f(x)=w$, and
  let $U$ be an open neighborhood of $x$. There are a connected open set
  $W$, with compact closure contained in $U$, and a number $r>0$ such that
  $$
    x\in W,\qquad
    |f(z)-w|>r\quad(z\in\partial W).
  $$
proof:
  Start with a relatively compact fiber-isolating neighborhood and use the
  [component-trapping theorem](lean:JJMath.Quasiconformal.exists_closedBall_preimage_component_disjoint_frontier_of_light). In the compact preimage of the closed target ball, surround the trapped component by a clopen set. Its two compact complementary pieces can be separated in the plane by an open set whose closure stays in the original neighborhood. The boundary of this open set misses the whole closed-ball preimage. Passing to the component containing $x$ makes the source domain connected without enlarging its boundary.
-/
theorem exists_normalSourceDomain_of_light
    {f : ℂ → ℂ} (hf : Continuous f)
    (hlight : ∀ w (E : Set ℂ), IsConnected E →
      E ⊆ {z : ℂ | f z = w} → E.Subsingleton)
    {x w : ℂ} (hxw : f x = w) {U : Set ℂ}
    (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ W : Set ℂ, ∃ r : ℝ,
      IsOpen W ∧ IsConnected W ∧ x ∈ W ∧
      closure W ⊆ U ∧ IsCompact (closure W) ∧ 0 < r ∧
      ∀ z ∈ frontier W, r < dist (f z) w := by
  obtain ⟨V, hVopen, _hVconnected, hxV, hVclosure,
      hVcompact, _hVfrontier⟩ :=
    exists_connected_open_closure_subset_frontier_disjoint_fiber_of_light
      hf hlight hxw hU hxU
  obtain ⟨r, hr, hCfrontier⟩ :=
    exists_closedBall_preimage_component_disjoint_frontier_of_light
      hf hlight hxw hVopen hxV hVcompact
  let S : Set ℂ :=
    closure V ∩ f ⁻¹' Metric.closedBall w r
  have hScompact : IsCompact S :=
    hVcompact.inter_right
      (Metric.isClosed_closedBall.preimage hf)
  have hxS : x ∈ S := by
    refine ⟨subset_closure hxV, ?_⟩
    change dist (f x) w ≤ r
    rw [hxw, dist_self]
    exact hr.le
  let C : Set ℂ := connectedComponentIn S x
  have hCsubV : C ⊆ V := by
    intro z hzC
    have hzS : z ∈ S :=
      connectedComponentIn_subset S x hzC
    by_contra hzV
    have hzfront : z ∈ frontier V :=
      ⟨hzS.1, fun hzInterior ↦
        hzV (interior_subset hzInterior)⟩
    exact Set.disjoint_left.mp hCfrontier hzC hzfront
  let xS : S := ⟨x, hxS⟩
  let VS : Set S := ((↑) : S → ℂ) ⁻¹' V
  have hVSopen : IsOpen VS :=
    hVopen.preimage continuous_subtype_val
  have hcomponentSub :
      connectedComponent xS ⊆ VS := by
    intro z hzcomponent
    apply hCsubV
    change (z : ℂ) ∈ connectedComponentIn S x
    rw [connectedComponentIn_eq_image hxS]
    exact ⟨z, hzcomponent, rfl⟩
  letI : CompactSpace S :=
    isCompact_iff_compactSpace.mp hScompact
  obtain ⟨Q, hQclopen, hcomponentQ, hQVS⟩ :=
    exists_isClopen_connectedComponent_subset_of_compact
      hVSopen hcomponentSub
  let K : Set ℂ := ((↑) : S → ℂ) '' Q
  let L : Set ℂ := ((↑) : S → ℂ) '' Qᶜ
  have hKcompact : IsCompact K :=
    hQclopen.1.isCompact.image continuous_subtype_val
  have hLcompact : IsCompact L :=
    hQclopen.compl.1.isCompact.image continuous_subtype_val
  have hxK : x ∈ K :=
    ⟨xS, hcomponentQ mem_connectedComponent, rfl⟩
  have hKsubV : K ⊆ V := by
    rintro z ⟨zS, hzQ, rfl⟩
    exact hQVS hzQ
  have hKL : Disjoint K L := by
    rw [Set.disjoint_left]
    rintro z ⟨zS, hzQ, rfl⟩
      ⟨zS', hzQ', hzEq⟩
    have : zS = zS' := Subtype.ext hzEq.symm
    subst zS'
    exact hzQ' hzQ
  have hSsub : S ⊆ K ∪ L := by
    intro z hzS
    let zS : S := ⟨z, hzS⟩
    by_cases hzQ : zS ∈ Q
    · exact Or.inl ⟨zS, hzQ, rfl⟩
    · exact Or.inr ⟨zS, hzQ, rfl⟩
  let T : Set ℂ := V \ L
  have hTopen : IsOpen T :=
    hVopen.sdiff hLcompact.isClosed
  have hKT : K ⊆ T := by
    intro z hzK
    exact ⟨hKsubV hzK,
      Set.disjoint_left.mp hKL hzK⟩
  obtain ⟨O, hOopen, hKO, hOclosureT⟩ :=
    normal_exists_closure_subset
      hKcompact.isClosed hTopen hKT
  have hxO : x ∈ O := hKO hxK
  have hOclosureV : closure O ⊆ V :=
    fun z hz ↦ (hOclosureT hz).1
  have hOclosureU : closure O ⊆ U :=
    hOclosureV.trans (subset_closure.trans hVclosure)
  have hOcompact : IsCompact (closure O) :=
    hVcompact.of_isClosed_subset isClosed_closure
      (hOclosureV.trans subset_closure)
  have hOfrontierS : Disjoint (frontier O) S := by
    rw [Set.disjoint_left]
    intro z hzfront hzS
    rcases hSsub hzS with hzK | hzL
    · have hzO : z ∈ O := hKO hzK
      exact hzfront.2 <|
        mem_interior_iff_mem_nhds.mpr
          (hOopen.mem_nhds hzO)
    · exact (hOclosureT hzfront.1).2 hzL
  have hOseparated :
      ∀ z ∈ frontier O, r < dist (f z) w := by
    intro z hzfront
    apply lt_of_not_ge
    intro hzdist
    apply Set.disjoint_left.mp hOfrontierS hzfront
    exact
      ⟨subset_closure (hOclosureV hzfront.1),
        Metric.mem_closedBall.mpr hzdist⟩
  let W : Set ℂ := connectedComponentIn O x
  have hWopen : IsOpen W :=
    hOopen.connectedComponentIn
  have hxW : x ∈ W :=
    mem_connectedComponentIn hxO
  have hWconnected : IsConnected W :=
    isConnected_connectedComponentIn_iff.mpr hxO
  have hWclosureO : closure W ⊆ closure O :=
    closure_mono (connectedComponentIn_subset O x)
  have hWcompact : IsCompact (closure W) :=
    hOcompact.of_isClosed_subset isClosed_closure
      hWclosureO
  have hWseparated :
      ∀ z ∈ frontier W, r < dist (f z) w := by
    intro z hzfront
    exact hOseparated z
      (frontier_connectedComponentIn_subset_frontier_of_isOpen
        hOopen hxO hzfront)
  exact ⟨W, r, hWopen, hWconnected, hxW,
    hWclosureO.trans hOclosureU, hWcompact, hr,
    hWseparated⟩

/--
%%handwave
name:
  Local index one gives planar orientation
statement:
  Let $F:\mathbb C\to\mathbb C$ be a homeomorphism. If its local index at
  every $z$ over $F(z)$ is $1$, then its universal-domain restriction
  preserves planar orientation.
proof:
  Every positive-radius disk isolates $z$ in the fiber over $F(z)$ by
  injectivity. Thus the local index equals the winding number of the
  normalized image of its boundary. Winding number one characterizes the
  positive punctured-plane loop class, which is precisely the orientation
  predicate.
-/
theorem preservesPlanarOrientation_wholePlaneSubtype_of_localIndex_eq_one
    (F : ℂ ≃ₜ ℂ)
    (hindex : ∀ z : ℂ,
      planarLocalIndex F F.continuous z (F z) rfl
        (isDiscrete_fiber_homeomorph F (F z)) = 1) :
    PreservesPlanarOrientation (wholePlaneSubtypeHomeomorph F) := by
  intro z
  let r : ℝ := 1
  have hr : 0 < r := by simp [r]
  have hball : Metric.closedBall (z : ℂ) r ⊆ (Set.univ : Set ℂ) :=
    fun _ _ ↦ Set.mem_univ _
  have hiso : IsFiberIsolatingRadius F (z : ℂ) (F z) r := by
    refine ⟨hr, ?_⟩
    intro x _hx hFx
    exact F.injective hFx
  let havoid :=
    imageCircleLoop_ne_of_isFiberIsolatingRadius
      F F.continuous (z : ℂ) (F z) hiso
  have hcircleIndex :
      planarCircleIndex F F.continuous (z : ℂ) (F z) r hr havoid = 1 := by
    rw [← planarLocalIndex_eq_planarCircleIndex
      F F.continuous (z : ℂ) (F z) rfl
        (isDiscrete_fiber_homeomorph F (F z)) hiso]
    exact hindex z
  have hpositive :
      Path.Homotopic
        (normalizedLoopAround
          (imageCircleLoop F F.continuous (z : ℂ) r) (F z) havoid
            (imageCircleLoop_one_eq_zero F F.continuous (z : ℂ) r))
        positiveCircleLoop :=
    puncturedLoop_homotopic_positive_iff_windingNumber_eq_one.mpr
      hcircleIndex
  refine ⟨r, hr, hball, ?_⟩
  exact hpositive

end

end Quasiconformal

end JJMath
