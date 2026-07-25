import JJMath.Quasiconformal.SquareBoundary
import JJMath.Quasiconformal.ApproxDifferentiability
import Mathlib.Data.Nat.Pairing
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv

/-!
# Change of variables and inverse quasiconformal maps

This file exposes the finite-distortion area and inverse layer needed by the
quasiconformal library.  It first records the classical differentiable area
formula already supplied by Mathlib and derives the Lusin $N$ property from
an area formula. It also proves that almost-everywhere differentiability plus
the Lusin property suffices for the full area formula. The corresponding
Sobolev area formula, Bochner change of variables, and inverse theorem are
assembled at their standard strength, including the planar Sobolev
adjugate/Piola identity used to identify the inverse weak differential.
-/

namespace JJMath

open MeasureTheory Set
open scoped ENNReal NNReal Function Topology

namespace Quasiconformal

noncomputable section

/--
%%handwave
name:
  Lusin $N$ property on a planar set
statement:
  A map $f:\mathbb C\to\mathbb C$ has the Lusin $N$ property on
  $\Omega\subseteq\mathbb C$ when every null set $S\subseteq\Omega$ has null
  image:
  $$
    |S|=0\quad\Longrightarrow\quad|f(S)|=0.
  $$
-/
def HasLusinNOn (Ω : Set ℂ) (f : ℂ → ℂ) : Prop :=
  ∀ s : Set ℂ, s ⊆ Ω → volume s = 0 → volume (f '' s) = 0

/--
%%handwave
name:
  Lusin $N^{-1}$ property for a planar homeomorphism
statement:
  A homeomorphism $F:\Omega\to\Omega'$ has the Lusin $N^{-1}$ property when
  its inverse sends every null subset of $\Omega'$ to a null subset of
  $\Omega$.
-/
def HasLusinNInvOn {Ω Ω' : Set ℂ} (F : Ω ≃ₜ Ω') : Prop :=
  HasLusinNOn Ω' (ambientMap F.symm)

/--
%%handwave
name:
  Transport of almost-everywhere properties through a Lusin homeomorphism
statement:
  Let $F:\Omega\to\Omega'$ be a homeomorphism with the Lusin $N$ property.
  Suppose $P(z)$ holds for almost every $z\in\Omega$ and, for every
  $z\in\Omega$, $P(z)$ implies $Q(F(z))$. Then $Q(y)$ holds for almost every
  $y\in\Omega'$.
proof:
  The source points where $P$ fails form a null set, whose image is null by
  the Lusin property. Every target point outside this image has a unique
  preimage where $P$ holds, and hence satisfies $Q$.
-/
theorem ae_restrict_target_of_ae_restrict_source_of_hasLusinNOn
    {Ω Ω' : Set ℂ} (F : Ω ≃ₜ Ω')
    (hΩ' : MeasurableSet Ω') (hN : HasLusinNOn Ω (ambientMap F))
    {P Q : ℂ → Prop}
    (hP : ∀ᵐ z ∂volume.restrict Ω, P z)
    (hPQ : ∀ z ∈ Ω, P z → Q (ambientMap F z)) :
    ∀ᵐ y ∂volume.restrict Ω', Q y := by
  have hPglobal : ∀ᵐ z ∂volume, z ∈ Ω → P z := ae_imp_of_ae_restrict hP
  have hbad0 : volume {z | ¬ (z ∈ Ω → P z)} = 0 := ae_iff.mp hPglobal
  have himage0 : volume (ambientMap F '' {z | ¬ (z ∈ Ω → P z)}) = 0 :=
    hN _ (by intro z hz; by_contra hzΩ; exact hz (fun h ↦ (hzΩ h).elim)) hbad0
  have htarget_global : ∀ᵐ y ∂volume, y ∈ Ω' → Q y := by
    apply ae_iff.mpr
    apply measure_mono_null _ himage0
    intro y hy
    have hyΩ' : y ∈ Ω' := by
      by_contra h
      exact hy (fun h' ↦ (h h').elim)
    let yΩ' : Ω' := ⟨y, hyΩ'⟩
    let z : ℂ := ambientMap F.symm y
    have hzΩ : z ∈ Ω := by
      have hz : z = F.symm yΩ' := ambientMap_apply F.symm yΩ'
      rw [hz]
      exact (F.symm yΩ').2
    have hmap : ambientMap F z = y := by
      simpa only [z, Homeomorph.symm_symm] using
        (ambientMap_symm_apply_ambientMap F.symm yΩ')
    refine ⟨z, ?_, hmap⟩
    intro hzimp
    exact hy (fun _ ↦ hmap ▸ hPQ z hzΩ (hzimp hzΩ))
  filter_upwards [ae_restrict_of_ae htarget_global,
    ae_restrict_mem hΩ'] with y hy hyΩ'
  exact hy hyΩ'

/--
%%handwave
name:
  Lusin property for planar local $W^{1,2}$ homeomorphisms
statement:
  Let $F:\Omega\to\Omega'$ be a homeomorphism between open planar domains.
  If its ambient representative is locally $W^{1,2}$ on $\Omega$, then every
  null set $A\subseteq\Omega$ has null image $F(A)$.
proof:
  Enlarge $A$ to a measurable null set and intersect it with $\Omega$. Its image is measurable. By inner regularity it suffices to prove that each compact subset $L$ of this image is null. The inverse image $F^{-1}(L)$ is a compact null subset of $\Omega$, so [the compact-null Lusin theorem](lean:JJMath.Quasiconformal.IsLocalW12On.volume_ambientMap_image_eq_zero_of_isCompact_null) shows that $L$ is null.
tags:
  milestone
-/
theorem IsLocalW12On.hasLusinNOn_ambientMap
    {Ω Ω' : Set ℂ} (F : Ω ≃ₜ Ω') (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω')
    {df : ℂ → ℂ →L[ℝ] ℂ} (hW : IsLocalW12On Ω (ambientMap F) df) :
    HasLusinNOn Ω (ambientMap F) := by
  intro A hAΩ hAzero
  obtain ⟨T, hAT, hTmeas, hTzero⟩ :=
    exists_measurable_superset_of_null hAzero
  let U : Set ℂ := T ∩ Ω
  have hAU : A ⊆ U := fun z hz => ⟨hAT hz, hAΩ hz⟩
  have hUmeas : MeasurableSet U := hTmeas.inter hΩ.measurableSet
  have hUΩ : U ⊆ Ω := inter_subset_right
  have hUzero : volume U = 0 := measure_mono_null inter_subset_left hTzero
  have hFUmeas : MeasurableSet (ambientMap F '' U) :=
    MeasurableSet.ambientMap_image F hΩ'.measurableSet hUmeas hUΩ
  apply measure_mono_null (image_mono hAU)
  rw [hFUmeas.measure_eq_iSup_isCompact]
  simp only [ENNReal.iSup_eq_zero]
  intro L hLFU hLcompact
  have hLΩ' : L ⊆ Ω' := by
    intro y hy
    rcases hLFU hy with ⟨z, hzU, rfl⟩
    let zΩ : Ω := ⟨z, hUΩ hzU⟩
    have hz : ambientMap F z = F zΩ := ambientMap_apply F zΩ
    rw [hz]
    exact (F zΩ).2
  let K : Set ℂ := ambientMap F.symm '' L
  have hKcompact : IsCompact K :=
    hLcompact.image_of_continuousOn
      ((continuousOn_ambientMap F.symm).mono hLΩ')
  have hKU : K ⊆ U := by
    rintro x ⟨y, hyL, rfl⟩
    rcases hLFU hyL with ⟨z, hzU, hzy⟩
    let zΩ : Ω := ⟨z, hUΩ hzU⟩
    have hcancel : ambientMap F.symm y = z := by
      rw [← hzy]
      exact ambientMap_symm_apply_ambientMap F zΩ
    rw [hcancel]
    exact hzU
  have hKzero : volume K = 0 := measure_mono_null hKU hUzero
  have hFKzero := hW.volume_ambientMap_image_eq_zero_of_isCompact_null
    F hΩ hΩ' hKcompact (hKU.trans hUΩ) hKzero
  have hLFK : L = ambientMap F '' K := by
    apply Subset.antisymm
    · intro y hyL
      have hyΩ' : y ∈ Ω' := hLΩ' hyL
      let yΩ' : Ω' := ⟨y, hyΩ'⟩
      refine ⟨ambientMap F.symm y, ⟨y, hyL, rfl⟩, ?_⟩
      simpa only [Homeomorph.symm_symm] using
        (ambientMap_symm_apply_ambientMap F.symm yΩ')
    · rintro w ⟨x, ⟨y, hyL, rfl⟩, rfl⟩
      have hyΩ' : y ∈ Ω' := hLΩ' hyL
      let yΩ' : Ω' := ⟨y, hyΩ'⟩
      have hcancel : ambientMap F (ambientMap F.symm y) = y := by
        simpa only [Homeomorph.symm_symm] using
          (ambientMap_symm_apply_ambientMap F.symm yΩ')
      rw [hcancel]
      exact hyL
  rwa [← hLFK] at hFKzero

/--
%%handwave
name:
  Classical area formula in the plane
statement:
  Let $f:\Omega\to\mathbb C$ be injective and differentiable at every point
  of $\Omega$, with real differential $Df(z)$. For every measurable
  $s\subseteq\Omega$ and every $g:\mathbb C\to[0,\infty]$,
  $$
  \int_{f(s)}g(y)\,dy
  =\int_s |\operatorname{Jac}f(z)|g(f(z))\,dz.
  $$
proof:
  Apply the change-of-variables theorem for an injective map differentiable
  on a measurable set.
-/
theorem areaFormula_of_hasFDerivAt
    {Ω : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (hinj : Set.InjOn f Ω)
    (hderiv : ∀ z ∈ Ω, HasFDerivAt f (df z) z)
    {s : Set ℂ} (hs : MeasurableSet s) (hsΩ : s ⊆ Ω)
    (g : ℂ → ℝ≥0∞) :
    ∫⁻ y in f '' s, g y ∂volume =
      ∫⁻ z in s, ENNReal.ofReal |weakJacobian (df z)| * g (f z) ∂volume := by
  simpa [weakJacobian] using
    (lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs
      (fun z hz ↦ (hderiv z (hsΩ hz)).hasFDerivWithinAt)
      (hinj.mono hsΩ) g)

/--
%%handwave
name:
  Classical area formula from differentiation within a measurable set
statement:
  Let $s\subseteq\mathbb C$ be measurable and let $f:\mathbb C\to\mathbb C$
  be injective on $s$. If, at every $z\in s$, the restriction of $f$ to $s$
  has real differential $Df(z)$, then for every
  $g:\mathbb C\to[0,\infty]$,
  $$
  \int_{f(s)}g(y)\,dy
  =\int_s |\operatorname{Jac}f(z)|g(f(z))\,dz.
  $$
proof:
  Apply the change-of-variables theorem for an injective map differentiable
  within a measurable set.
-/
theorem areaFormula_of_hasFDerivWithinAt
    {s : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (hs : MeasurableSet s) (hinj : Set.InjOn f s)
    (hderiv : ∀ z ∈ s, HasFDerivWithinAt f (df z) s z)
    (g : ℂ → ℝ≥0∞) :
    ∫⁻ y in f '' s, g y ∂volume =
      ∫⁻ z in s, ENNReal.ofReal |weakJacobian (df z)| * g (f z) ∂volume := by
  simpa [weakJacobian] using
    (lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs hderiv hinj g)

/--
%%handwave
name:
  Planar preimage multiplicity
statement:
  For a map $f:\mathbb C\to\mathbb C$, a source set $S$, and a target point
  $y$, the multiplicity
  $$
    N(f,S,y)=\#\{x\in S:f(x)=y\}
  $$
  is the extended nonnegative cardinality of the fiber in $S$. An infinite
  fiber has multiplicity $+\infty$.
-/
def preimageMultiplicity
    (f : ℂ → ℂ) (S : Set ℂ) (y : ℂ) : ℝ≥0∞ :=
  (S ∩ f ⁻¹' {y}).encard

/--
%%handwave
name:
  Countable injective decomposition of the positive-Jacobian locus
statement:
  Let $S\subset\mathbb C$ be measurable. Suppose that $f$ has real
  differential $Df(x)$ at every $x\in S$, relative to $S$, and that
  $J(Df(x))>0$ throughout $S$. Then there are pairwise disjoint measurable
  sets $S_n$ covering $S$ such that $f$ is injective on every $S_n$.
proof:
  Use [the measurable approximation partition](lean:exists_partition_approximatesLinearOn_of_hasFDerivWithinAt), choosing at an invertible linear map $A$ an error smaller than half the inverse norm of $A^{-1}$. Every model map selected by the partition is the differential at a point of $S$, hence has positive Jacobian and is invertible. The quantitative inverse-function estimate then makes $f$ injective on each piece.
-/
theorem exists_countable_measurable_injective_cover_of_hasFDerivWithinAt_of_weakJacobian_pos
    {S : Set ℂ} {f : ℂ → ℂ}
    {df : ℂ → ℂ →L[ℝ] ℂ}
    (hSmeas : MeasurableSet S)
    (hderiv :
      ∀ x ∈ S, HasFDerivWithinAt f (df x) S x)
    (hJ : ∀ x ∈ S, 0 < weakJacobian (df x)) :
    ∃ t : ℕ → Set ℂ,
      Pairwise (Disjoint on t) ∧
        (∀ n, MeasurableSet (t n)) ∧
          (∀ n, t n ⊆ S) ∧
            S ⊆ ⋃ n, t n ∧
              ∀ n, Set.InjOn f (t n) := by
  rcases eq_empty_or_nonempty S with hS | hSne
  · subst S
    refine ⟨fun _ => ∅, ?_, ?_, ?_, ?_, ?_⟩
    · exact
        pairwise_disjoint_mono
          (disjoint_disjointed fun _ : ℕ => ∅)
          fun _ => empty_subset _
    · simp
    · simp
    · simp
    · simp
  let rad : (ℂ →L[ℝ] ℂ) → ℝ≥0 :=
    fun A =>
      if hJA : 0 < weakJacobian A then
        ‖(realLinearEquivOfWirtinger
          (weakDZ A) (weakDBar A)
          (by
            simpa [
              weakJacobian_eq_norm_weakDZ_sq_sub_norm_weakDBar_sq]
              using hJA)).symm.toContinuousLinearMap‖₊⁻¹ / 2
      else 1
  have hrad : ∀ A, rad A ≠ 0 := by
    intro A
    dsimp [rad]
    split_ifs with hJA
    · let e :=
        realLinearEquivOfWirtinger
          (weakDZ A) (weakDBar A)
          (by
            simpa [
              weakJacobian_eq_norm_weakDZ_sq_sub_norm_weakDBar_sq]
              using hJA)
      have heq :
          e.symm.toContinuousLinearMap ≠ 0 := by
        intro hzero
        have hone :
            e.symm (1 : ℂ) ≠ 0 :=
          e.symm.map_ne_zero_iff.mpr one_ne_zero
        apply hone
        change e.symm.toContinuousLinearMap 1 = 0
        rw [hzero]
        rfl
      have hnorm :
          ‖e.symm.toContinuousLinearMap‖₊ ≠ 0 := by
        rw [ne_eq, nnnorm_eq_zero]
        exact heq
      exact div_ne_zero (inv_ne_zero hnorm) (by norm_num)
    · norm_num
  obtain
      ⟨u, A, hudisj, humeas, hcover,
        happrox, hA⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt
      f S df hderiv rad hrad
  let t : ℕ → Set ℂ :=
    fun n => S ∩ u n
  refine ⟨t, ?_, ?_, ?_, ?_, ?_⟩
  · exact
      pairwise_disjoint_mono hudisj
        fun n => inter_subset_right
  · intro n
    exact hSmeas.inter (humeas n)
  · intro n
    exact inter_subset_left
  · intro x hx
    rcases Set.mem_iUnion.mp (hcover hx) with
      ⟨n, hn⟩
    exact Set.mem_iUnion.mpr ⟨n, hx, hn⟩
  · intro n
    obtain ⟨y, hy, hAy⟩ :=
      hA hSne n
    have hJn :
        0 < weakJacobian (A n) := by
      rw [hAy]
      exact hJ y hy
    let e :=
      realLinearEquivOfWirtinger
        (weakDZ (A n)) (weakDBar (A n))
        (by
          simpa [
            weakJacobian_eq_norm_weakDZ_sq_sub_norm_weakDBar_sq]
            using hJn)
    have he :
        e.toContinuousLinearMap = A n := by
      change
        realLinearMapOfWirtinger
          (weakDZ (A n)) (weakDBar (A n)) = A n
      exact ext_weakDZ_weakDBar (by simp) (by simp)
    have happ :
        ApproximatesLinearOn f
          (e : ℂ →L[ℝ] ℂ) (t n) (rad (A n)) := by
      simpa [t, he] using happrox n
    apply happ.injOn
    right
    have heq :
        e.symm.toContinuousLinearMap ≠ 0 := by
      intro hzero
      have hone :
          e.symm (1 : ℂ) ≠ 0 :=
        e.symm.map_ne_zero_iff.mpr one_ne_zero
      apply hone
      change e.symm.toContinuousLinearMap 1 = 0
      rw [hzero]
      rfl
    have hnorm :
        ‖e.symm.toContinuousLinearMap‖₊ ≠ 0 := by
      rw [ne_eq, nnnorm_eq_zero]
      exact heq
    have hpos :
        0 < ‖e.symm.toContinuousLinearMap‖₊⁻¹ := by
      exact inv_pos.mpr (bot_lt_iff_ne_bot.mpr hnorm)
    have hrad_eq :
        rad (A n) =
          ‖e.symm.toContinuousLinearMap‖₊⁻¹ / 2 := by
      dsimp [rad]
      rw [dif_pos hJn]
    rw [hrad_eq]
    exact half_lt_self hpos

/--
%%handwave
name:
  Countable injective decomposition of the negative-Jacobian locus
statement:
  Let $S\subset\mathbb C$ be measurable. Suppose that $f$ has real
  differential $Df(x)$ at every $x\in S$, relative to $S$, and that
  $J(Df(x))<0$ throughout $S$. Then there are pairwise disjoint measurable
  sets $S_n$ covering $S$ such that $f$ is injective on every $S_n$.
proof:
  Postcompose $f$ with complex conjugation. This changes the sign of every
  Jacobian and preserves injectivity, so [the positive-Jacobian injective-sheet decomposition](lean:JJMath.Quasiconformal.exists_countable_measurable_injective_cover_of_hasFDerivWithinAt_of_weakJacobian_pos) applies.
-/
theorem exists_countable_measurable_injective_cover_of_hasFDerivWithinAt_of_weakJacobian_neg
    {S : Set ℂ} {f : ℂ → ℂ}
    {df : ℂ → ℂ →L[ℝ] ℂ}
    (hSmeas : MeasurableSet S)
    (hderiv :
      ∀ x ∈ S, HasFDerivWithinAt f (df x) S x)
    (hJ : ∀ x ∈ S, weakJacobian (df x) < 0) :
    ∃ t : ℕ → Set ℂ,
      Pairwise (Disjoint on t) ∧
        (∀ n, MeasurableSet (t n)) ∧
          (∀ n, t n ⊆ S) ∧
            S ⊆ ⋃ n, t n ∧
              ∀ n, Set.InjOn f (t n) := by
  let g : ℂ → ℂ := fun x ↦ star (f x)
  let dg : ℂ → ℂ →L[ℝ] ℂ :=
    fun x ↦ (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (df x)
  have hgderiv :
      ∀ x ∈ S, HasFDerivWithinAt g (dg x) S x := by
    intro x hx
    exact
      Complex.conjCLE.hasFDerivAt.comp_hasFDerivWithinAt x
        (hderiv x hx)
  have hgJ :
      ∀ x ∈ S, 0 < weakJacobian (dg x) := by
    intro x hx
    calc
      0 < -weakJacobian (df x) :=
        neg_pos.mpr (hJ x hx)
      _ = weakJacobian (dg x) := by
        simp [dg, weakJacobian]
  obtain ⟨t, htdisj, htmeas, htS, hcover, hginj⟩ :=
    exists_countable_measurable_injective_cover_of_hasFDerivWithinAt_of_weakJacobian_pos
      hSmeas hgderiv hgJ
  refine ⟨t, htdisj, htmeas, htS, hcover, ?_⟩
  intro n x hx y hy hxy
  apply hginj n hx hy
  simp [g, hxy]

/--
%%handwave
name:
  Injective-sheet count equals preimage multiplicity
statement:
  Let pairwise disjoint sets $S_n\subseteq S$ cover $S$, and suppose that
  $f$ is injective on every $S_n$. Then, for every $y\in\mathbb C$,
  $$
    \sum_n \mathbf 1_{f(S_n)}(y)=N(f,S,y).
  $$
proof:
  Every preimage of $y$ belongs to a unique sheet, and injectivity gives at
  most one preimage on each sheet. Thus the fiber over $y$ is in bijection
  with the set of sheet indices whose images contain $y$.
-/
theorem tsum_image_indicator_one_eq_preimageMultiplicity
    {S : Set ℂ} {f : ℂ → ℂ}
    (t : ℕ → Set ℂ)
    (htS : ∀ n, t n ⊆ S)
    (htdisj : Pairwise (Disjoint on t))
    (hcover : S ⊆ ⋃ n, t n)
    (hinj : ∀ n, Set.InjOn f (t n))
    (y : ℂ) :
    ∑' n : ℕ,
        (f '' t n).indicator (fun _ => (1 : ℝ≥0∞)) y =
      preimageMultiplicity f S y := by
  let P : Set ℂ :=
    S ∩ f ⁻¹' {y}
  let I : Set ℕ :=
    {n | y ∈ f '' t n}
  have hexists (x : P) :
      ∃ n, x.1 ∈ t n := by
    have hxS : x.1 ∈ S := x.2.1
    rcases Set.mem_iUnion.mp (hcover hxS) with
      ⟨n, hn⟩
    exact ⟨n, hn⟩
  let sheetIndex : P → ℕ :=
    fun x => Classical.choose (hexists x)
  have hsheetIndex (x : P) :
      x.1 ∈ t (sheetIndex x) :=
    Classical.choose_spec (hexists x)
  let e : P → I :=
    fun x =>
      ⟨sheetIndex x,
        ⟨x.1, hsheetIndex x, by simpa [P] using x.2.2⟩⟩
  have heinj : Function.Injective e := by
    intro x x' hxx'
    have hindex :
        sheetIndex x = sheetIndex x' :=
      congrArg Subtype.val hxx'
    apply Subtype.ext
    apply hinj (sheetIndex x)
    · exact hsheetIndex x
    · rw [hindex]
      exact hsheetIndex x'
    · simpa [P] using x.2.2.trans x'.2.2.symm
  have hesurj : Function.Surjective e := by
    intro n
    rcases n.2 with ⟨x, hxt, hxy⟩
    let xP : P :=
      ⟨x, htS n.1 hxt, by simpa [P] using hxy⟩
    refine ⟨xP, Subtype.ext ?_⟩
    change sheetIndex xP = n.1
    by_contra hne
    exact Set.disjoint_left.1 (htdisj hne)
      (hsheetIndex xP) hxt
  have hcard :
      P.encard = I.encard :=
    Set.encard_congr (Equiv.ofBijective e ⟨heinj, hesurj⟩)
  calc
    ∑' n : ℕ,
        (f '' t n).indicator
          (fun _ => (1 : ℝ≥0∞)) y =
        ∑' _ : I, (1 : ℝ≥0∞) := by
      rw [tsum_subtype I
        (fun _ : ℕ => (1 : ℝ≥0∞))]
      apply tsum_congr
      intro n
      by_cases hn : y ∈ f '' t n
      · have hnI : n ∈ I := hn
        rw [Set.indicator_of_mem hn,
          Set.indicator_of_mem hnI]
      · have hnI : n ∉ I := hn
        rw [Set.indicator_of_notMem hn,
          Set.indicator_of_notMem hnI]
    _ = (I.encard : ℝ≥0∞) :=
      ENNReal.tsum_set_one I
    _ = (P.encard : ℝ≥0∞) := by
      exact congrArg ENat.toENNReal hcard.symm
    _ = preimageMultiplicity f S y := by
      simp [P, preimageMultiplicity]

/--
%%handwave
name:
  Measurability of multiplicity from injective sheets
statement:
  Suppose a planar set $S$ is covered by countably many pairwise disjoint
  measurable sets $S_n$, the map $f$ is injective and differentiable within
  each $S_n$, and $S_n\subseteq S$. Then
  $y\mapsto N(f,S,y)$ is measurable.
proof:
  Each sheet image $f(S_n)$ is measurable by the differentiable injective
  area theorem. The multiplicity is [the countable sum of the indicators of these sheet images](lean:JJMath.Quasiconformal.tsum_image_indicator_one_eq_preimageMultiplicity), hence is measurable.
-/
theorem measurable_preimageMultiplicity_of_injective_sheets
    {S : Set ℂ} {f : ℂ → ℂ}
    {df : ℂ → ℂ →L[ℝ] ℂ}
    (t : ℕ → Set ℂ)
    (htmeas : ∀ n, MeasurableSet (t n))
    (htS : ∀ n, t n ⊆ S)
    (htdisj : Pairwise (Disjoint on t))
    (hcover : S ⊆ ⋃ n, t n)
    (hderiv :
      ∀ n x, x ∈ t n →
        HasFDerivWithinAt f (df x) (t n) x)
    (hinj : ∀ n, Set.InjOn f (t n)) :
    Measurable (preimageMultiplicity f S) := by
  have himageMeas :
      ∀ n, MeasurableSet (f '' t n) := by
    intro n
    exact
      measurable_image_of_fderivWithin
        (htmeas n) (hderiv n) (hinj n)
  have hsum : Measurable (fun y : ℂ ↦
      ∑' n : ℕ,
        (f '' t n).indicator (fun _ ↦ (1 : ℝ≥0∞)) y) :=
    Measurable.tsum fun n ↦
      measurable_const.indicator (himageMeas n)
  convert hsum using 1
  funext y
  exact
    (tsum_image_indicator_one_eq_preimageMultiplicity
      t htS htdisj hcover hinj y).symm

/--
%%handwave
name:
  Area formula counting injective sheets
statement:
  Let pairwise disjoint measurable sets $S_n\subseteq S$ cover $S$.
  Suppose $f$ is injective on each $S_n$ and has real differential $Df(x)$
  there. For every almost-everywhere measurable
  $g:\mathbb C\to[0,\infty]$,
  $$
    \int_{\mathbb C}
      \sum_n \mathbf 1_{f(S_n)}(y)g(y)\,dy
      =
    \int_S
      |J(Df(x))|g(f(x))\,dx.
  $$
  Thus the target integral counts every injective sheet containing $y$.
proof:
  Every image $f(S_n)$ is measurable by the injective differentiable area
  theorem. Tonelli moves the nonnegative sum outside the target integral.
  Apply [the injective area formula on each sheet](lean:JJMath.Quasiconformal.areaFormula_of_hasFDerivWithinAt), then sum the source integrals over the pairwise disjoint cover of $S$.
-/
theorem areaFormula_counting_injective_sheets
    {S : Set ℂ} {f : ℂ → ℂ}
    {df : ℂ → ℂ →L[ℝ] ℂ}
    (t : ℕ → Set ℂ)
    (htmeas : ∀ n, MeasurableSet (t n))
    (htS : ∀ n, t n ⊆ S)
    (htdisj : Pairwise (Disjoint on t))
    (hcover : S ⊆ ⋃ n, t n)
    (hderiv :
      ∀ n x, x ∈ t n →
        HasFDerivWithinAt f (df x) (t n) x)
    (hinj : ∀ n, Set.InjOn f (t n))
    (g : ℂ → ℝ≥0∞)
    (hg : AEMeasurable g volume) :
    ∫⁻ y, ∑' n : ℕ,
        (f '' t n).indicator g y ∂volume =
      ∫⁻ x in S,
        ENNReal.ofReal |weakJacobian (df x)| *
          g (f x) ∂volume := by
  let integrand : ℂ → ℝ≥0∞ :=
    fun x =>
      ENNReal.ofReal |weakJacobian (df x)| *
        g (f x)
  have himageMeas :
      ∀ n, MeasurableSet (f '' t n) := by
    intro n
    exact
      measurable_image_of_fderivWithin
        (htmeas n) (hderiv n) (hinj n)
  have hUnion : ⋃ n, t n = S := by
    apply Subset.antisymm
    · exact iUnion_subset htS
    · exact hcover
  calc
    ∫⁻ y, ∑' n : ℕ,
        (f '' t n).indicator g y ∂volume =
        ∑' n : ℕ,
          ∫⁻ y, (f '' t n).indicator g y ∂volume := by
      rw [lintegral_tsum]
      exact fun n => hg.indicator (himageMeas n)
    _ =
        ∑' n : ℕ,
          ∫⁻ y in f '' t n, g y ∂volume := by
      apply tsum_congr
      intro n
      exact lintegral_indicator (himageMeas n) g
    _ =
        ∑' n : ℕ,
          ∫⁻ x in t n, integrand x ∂volume := by
      apply tsum_congr
      intro n
      simpa [integrand] using
        areaFormula_of_hasFDerivWithinAt
          (htmeas n) (hinj n) (hderiv n) g
    _ =
        ∫⁻ x in ⋃ n, t n, integrand x ∂volume :=
      (lintegral_iUnion htmeas htdisj integrand).symm
    _ =
        ∫⁻ x in S,
            ENNReal.ofReal |weakJacobian (df x)| *
            g (f x) ∂volume := by
      rw [hUnion]

/--
%%handwave
name:
  Area formula with preimage multiplicity
statement:
  Let pairwise disjoint measurable sets $S_n\subseteq S$ cover $S$.
  Suppose $f$ is injective on each $S_n$ and has real differential $Df(x)$
  there. For every almost-everywhere measurable
  $g:\mathbb C\to[0,\infty]$,
  $$
    \int_{\mathbb C}N(f,S,y)g(y)\,dy
      =
    \int_S |J(Df(x))|g(f(x))\,dx.
  $$
proof:
  By [the injective-sheet count is the preimage multiplicity](lean:JJMath.Quasiconformal.tsum_image_indicator_one_eq_preimageMultiplicity). Substitute this identity into [the area formula counting injective sheets](lean:JJMath.Quasiconformal.areaFormula_counting_injective_sheets).
-/
theorem areaFormula_preimageMultiplicity_of_injective_sheets
    {S : Set ℂ} {f : ℂ → ℂ}
    {df : ℂ → ℂ →L[ℝ] ℂ}
    (t : ℕ → Set ℂ)
    (htmeas : ∀ n, MeasurableSet (t n))
    (htS : ∀ n, t n ⊆ S)
    (htdisj : Pairwise (Disjoint on t))
    (hcover : S ⊆ ⋃ n, t n)
    (hderiv :
      ∀ n x, x ∈ t n →
        HasFDerivWithinAt f (df x) (t n) x)
    (hinj : ∀ n, Set.InjOn f (t n))
    (g : ℂ → ℝ≥0∞)
    (hg : AEMeasurable g volume) :
    ∫⁻ y,
        preimageMultiplicity f S y * g y ∂volume =
      ∫⁻ x in S,
        ENNReal.ofReal |weakJacobian (df x)| *
          g (f x) ∂volume := by
  rw [← areaFormula_counting_injective_sheets
    t htmeas htS htdisj hcover hderiv hinj g hg]
  apply lintegral_congr
  intro y
  rw [← tsum_image_indicator_one_eq_preimageMultiplicity
    t htS htdisj hcover hinj y]
  rw [← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro n
  by_cases hy : y ∈ f '' t n
  · simp [hy]
  · simp [hy]

/--
%%handwave
name:
  Multiplicity area formula on the positive-Jacobian locus
statement:
  Let $S\subseteq\mathbb C$ be measurable. Suppose that $f$ has real
  differential $Df(x)$ at every $x\in S$, relative to $S$, and
  $J(Df(x))>0$ throughout $S$. Then, for every almost-everywhere measurable
  $g:\mathbb C\to[0,\infty]$,
  $$
    \int_{\mathbb C}N(f,S,y)g(y)\,dy
      =
    \int_S J(Df(x))g(f(x))\,dx.
  $$
proof:
  Decompose the positive-Jacobian locus into countably many measurable injective sheets, and apply [the area formula with preimage multiplicity](lean:JJMath.Quasiconformal.areaFormula_preimageMultiplicity_of_injective_sheets).
-/
theorem areaFormula_preimageMultiplicity_of_hasFDerivWithinAt_of_weakJacobian_pos
    {S : Set ℂ} {f : ℂ → ℂ}
    {df : ℂ → ℂ →L[ℝ] ℂ}
    (hSmeas : MeasurableSet S)
    (hderiv :
      ∀ x ∈ S, HasFDerivWithinAt f (df x) S x)
    (hJ : ∀ x ∈ S, 0 < weakJacobian (df x))
    (g : ℂ → ℝ≥0∞)
    (hg : AEMeasurable g volume) :
    ∫⁻ y,
        preimageMultiplicity f S y * g y ∂volume =
      ∫⁻ x in S,
        ENNReal.ofReal (weakJacobian (df x)) *
          g (f x) ∂volume := by
  obtain
      ⟨t, htdisj, htmeas, htS, hcover, hinj⟩ :=
    exists_countable_measurable_injective_cover_of_hasFDerivWithinAt_of_weakJacobian_pos
      hSmeas hderiv hJ
  have htderiv :
      ∀ n x, x ∈ t n →
        HasFDerivWithinAt f (df x) (t n) x := by
    intro n x hx
    exact (hderiv x (htS n hx)).mono (htS n)
  rw [areaFormula_preimageMultiplicity_of_injective_sheets
    t htmeas htS htdisj hcover htderiv hinj g hg]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem hSmeas] with x hx
  rw [abs_of_pos (hJ x hx)]

/--
%%handwave
name:
  Multiplicity area formula on the negative-Jacobian locus
statement:
  Let $S\subseteq\mathbb C$ be measurable. Suppose that $f$ has real
  differential $Df(x)$ at every $x\in S$, relative to $S$, and
  $J(Df(x))<0$ throughout $S$. Then, for every almost-everywhere measurable
  $g:\mathbb C\to[0,\infty]$,
  $$
    \int_{\mathbb C}N(f,S,y)g(y)\,dy
      =
    \int_S -J(Df(x))g(f(x))\,dx.
  $$
proof:
  Decompose the negative-Jacobian locus into countably many measurable
  injective sheets and apply the area formula on those sheets. Since the
  Jacobian is negative, its absolute value is $-J(Df)$.
-/
theorem areaFormula_preimageMultiplicity_of_hasFDerivWithinAt_of_weakJacobian_neg
    {S : Set ℂ} {f : ℂ → ℂ}
    {df : ℂ → ℂ →L[ℝ] ℂ}
    (hSmeas : MeasurableSet S)
    (hderiv :
      ∀ x ∈ S, HasFDerivWithinAt f (df x) S x)
    (hJ : ∀ x ∈ S, weakJacobian (df x) < 0)
    (g : ℂ → ℝ≥0∞)
    (hg : AEMeasurable g volume) :
    ∫⁻ y,
        preimageMultiplicity f S y * g y ∂volume =
      ∫⁻ x in S,
        ENNReal.ofReal (-weakJacobian (df x)) *
          g (f x) ∂volume := by
  obtain
      ⟨t, htdisj, htmeas, htS, hcover, hinj⟩ :=
    exists_countable_measurable_injective_cover_of_hasFDerivWithinAt_of_weakJacobian_neg
      hSmeas hderiv hJ
  have htderiv :
      ∀ n x, x ∈ t n →
        HasFDerivWithinAt f (df x) (t n) x := by
    intro n x hx
    exact (hderiv x (htS n hx)).mono (htS n)
  rw [areaFormula_preimageMultiplicity_of_injective_sheets
    t htmeas htS htdisj hcover htderiv hinj g hg]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem hSmeas] with x hx
  rw [abs_of_neg (hJ x hx)]

/--
%%handwave
name:
  Measurability of multiplicity on a positive-Jacobian locus
statement:
  Let $S\subseteq\mathbb C$ be measurable. If $f$ is differentiable within
  $S$ and $J_f>0$ throughout $S$, then
  $y\mapsto N(f,S,y)$ is measurable.
proof:
  Use [the positive-Jacobian injective-sheet decomposition](lean:JJMath.Quasiconformal.exists_countable_measurable_injective_cover_of_hasFDerivWithinAt_of_weakJacobian_pos) and [measurability of the resulting sheet count](lean:JJMath.Quasiconformal.measurable_preimageMultiplicity_of_injective_sheets).
-/
theorem measurable_preimageMultiplicity_of_hasFDerivWithinAt_of_weakJacobian_pos
    {S : Set ℂ} {f : ℂ → ℂ}
    {df : ℂ → ℂ →L[ℝ] ℂ}
    (hSmeas : MeasurableSet S)
    (hderiv :
      ∀ x ∈ S, HasFDerivWithinAt f (df x) S x)
    (hJ : ∀ x ∈ S, 0 < weakJacobian (df x)) :
    Measurable (preimageMultiplicity f S) := by
  obtain ⟨t, htdisj, htmeas, htS, hcover, hinj⟩ :=
    exists_countable_measurable_injective_cover_of_hasFDerivWithinAt_of_weakJacobian_pos
      hSmeas hderiv hJ
  exact
    measurable_preimageMultiplicity_of_injective_sheets
      t htmeas htS htdisj hcover
        (fun n x hx ↦ (hderiv x (htS n hx)).mono (htS n)) hinj

/--
%%handwave
name:
  Measurability of multiplicity on a negative-Jacobian locus
statement:
  Let $S\subseteq\mathbb C$ be measurable. If $f$ is differentiable within
  $S$ and $J_f<0$ throughout $S$, then
  $y\mapsto N(f,S,y)$ is measurable.
proof:
  Use [the negative-Jacobian injective-sheet decomposition](lean:JJMath.Quasiconformal.exists_countable_measurable_injective_cover_of_hasFDerivWithinAt_of_weakJacobian_neg) and [measurability of the resulting sheet count](lean:JJMath.Quasiconformal.measurable_preimageMultiplicity_of_injective_sheets).
-/
theorem measurable_preimageMultiplicity_of_hasFDerivWithinAt_of_weakJacobian_neg
    {S : Set ℂ} {f : ℂ → ℂ}
    {df : ℂ → ℂ →L[ℝ] ℂ}
    (hSmeas : MeasurableSet S)
    (hderiv :
      ∀ x ∈ S, HasFDerivWithinAt f (df x) S x)
    (hJ : ∀ x ∈ S, weakJacobian (df x) < 0) :
    Measurable (preimageMultiplicity f S) := by
  obtain ⟨t, htdisj, htmeas, htS, hcover, hinj⟩ :=
    exists_countable_measurable_injective_cover_of_hasFDerivWithinAt_of_weakJacobian_neg
      hSmeas hderiv hJ
  exact
    measurable_preimageMultiplicity_of_injective_sheets
      t htmeas htS htdisj hcover
        (fun n x hx ↦ (hderiv x (htS n hx)).mono (htS n)) hinj

/--
%%handwave
name:
  Real-valued area formula on a positive-Jacobian locus
statement:
  Let $S\subseteq\mathbb C$ be measurable, let $f$ be differentiable within
  $S$ with $J_f>0$, and let $\psi:\mathbb C\to[0,\infty)$ be measurable.
  If $x\mapsto J_f(x)\psi(f(x))$ is integrable on $S$, then
  $$
    \int_{\mathbb C}N(f,S,y)\psi(y)\,dy
      =
    \int_S J_f(x)\psi(f(x))\,dx.
  $$
  On the left, the extended multiplicity is interpreted as a real number;
  the finite integral makes infinite weighted fibers negligible.
proof:
  Apply [the extended nonnegative multiplicity area formula on the positive-Jacobian locus](lean:JJMath.Quasiconformal.areaFormula_preimageMultiplicity_of_hasFDerivWithinAt_of_weakJacobian_pos). Its source integral is finite by assumption, so the target integrand is finite almost everywhere. Taking real parts of the two extended nonnegative integrals gives the stated Bochner-integral identity.
-/
theorem integral_preimageMultiplicity_toReal_mul_eq_integral_weakJacobian_mul_of_pos
    {S : Set ℂ} {f : ℂ → ℂ}
    {df : ℂ → ℂ →L[ℝ] ℂ}
    (hSmeas : MeasurableSet S)
    (hderiv :
      ∀ x ∈ S, HasFDerivWithinAt f (df x) S x)
    (hJ : ∀ x ∈ S, 0 < weakJacobian (df x))
    (ψ : ℂ → ℝ) (hψmeas : Measurable ψ)
    (hψnonneg : ∀ y, 0 ≤ ψ y)
    (hint : Integrable
      (fun x ↦ weakJacobian (df x) * ψ (f x))
      (volume.restrict S)) :
    (∫ y : ℂ,
        (preimageMultiplicity f S y).toReal * ψ y ∂volume) =
      ∫ x in S,
        weakJacobian (df x) * ψ (f x) ∂volume := by
  let G : ℂ → ℝ≥0∞ := fun y ↦
    preimageMultiplicity f S y * ENNReal.ofReal (ψ y)
  let H : ℂ → ℝ≥0∞ := fun x ↦
    ENNReal.ofReal
      (weakJacobian (df x) * ψ (f x))
  have hmultMeas :
      Measurable (preimageMultiplicity f S) :=
    measurable_preimageMultiplicity_of_hasFDerivWithinAt_of_weakJacobian_pos
      hSmeas hderiv hJ
  have hGmeas : Measurable G := by
    exact hmultMeas.mul (ENNReal.measurable_ofReal.comp hψmeas)
  have harea :=
    areaFormula_preimageMultiplicity_of_hasFDerivWithinAt_of_weakJacobian_pos
      hSmeas hderiv hJ (fun y ↦ ENNReal.ofReal (ψ y))
        (ENNReal.measurable_ofReal.comp hψmeas).aemeasurable
  have hsource :
      (∫⁻ x in S,
          ENNReal.ofReal (weakJacobian (df x)) *
            ENNReal.ofReal (ψ (f x)) ∂volume) =
        ∫⁻ x, H x ∂volume.restrict S := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem hSmeas] with x hx
    rw [← ENNReal.ofReal_mul (le_of_lt (hJ x hx))]
  have harea' :
      ∫⁻ y, G y ∂volume =
        ∫⁻ x, H x ∂volume.restrict S := by
    simpa [G] using harea.trans hsource
  have hH_ne_top :
      ∫⁻ x, H x ∂volume.restrict S ≠ ∞ := by
    simpa [H] using hint.lintegral_lt_top.ne
  have hG_ne_top :
      ∫⁻ y, G y ∂volume ≠ ∞ := by
    rw [harea']
    exact hH_ne_top
  have hG_lt_top :
      ∀ᵐ y ∂volume, G y < ∞ :=
    ae_lt_top hGmeas hG_ne_top
  have hHmeas :
      AEMeasurable H (volume.restrict S) := by
    exact hint.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hH_lt_top :
      ∀ᵐ x ∂volume.restrict S, H x < ∞ :=
    ae_lt_top' hHmeas hH_ne_top
  calc
    (∫ y : ℂ,
        (preimageMultiplicity f S y).toReal * ψ y ∂volume) =
        ∫ y : ℂ, (G y).toReal ∂volume := by
      apply integral_congr_ae
      filter_upwards with y
      simp [G, ENNReal.toReal_mul, hψnonneg y]
    _ = (∫⁻ y, G y ∂volume).toReal :=
      integral_toReal hGmeas.aemeasurable hG_lt_top
    _ = (∫⁻ x, H x ∂volume.restrict S).toReal := by
      rw [harea']
    _ = ∫ x, (H x).toReal ∂volume.restrict S :=
      (integral_toReal hHmeas hH_lt_top).symm
    _ = ∫ x in S,
        weakJacobian (df x) * ψ (f x) ∂volume := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hSmeas] with x hx
      exact ENNReal.toReal_ofReal
        (mul_nonneg (le_of_lt (hJ x hx)) (hψnonneg (f x)))

/--
%%handwave
name:
  Real-valued area formula on a negative-Jacobian locus
statement:
  Let $S\subseteq\mathbb C$ be measurable, let $f$ be differentiable within
  $S$ with $J_f<0$, and let $\psi:\mathbb C\to[0,\infty)$ be measurable.
  If $x\mapsto -J_f(x)\psi(f(x))$ is integrable on $S$, then
  $$
    \int_{\mathbb C}N(f,S,y)\psi(y)\,dy
      =
    \int_S -J_f(x)\psi(f(x))\,dx.
  $$
  On the left, the extended multiplicity is interpreted as a real number;
  the finite integral makes infinite weighted fibers negligible.
proof:
  Apply [the extended nonnegative multiplicity area formula on the negative-Jacobian locus](lean:JJMath.Quasiconformal.areaFormula_preimageMultiplicity_of_hasFDerivWithinAt_of_weakJacobian_neg). Its source integral is finite by assumption, so the target integrand is finite almost everywhere. Taking real parts of the two extended nonnegative integrals gives the stated Bochner-integral identity.
-/
theorem integral_preimageMultiplicity_toReal_mul_eq_integral_neg_weakJacobian_mul_of_neg
    {S : Set ℂ} {f : ℂ → ℂ}
    {df : ℂ → ℂ →L[ℝ] ℂ}
    (hSmeas : MeasurableSet S)
    (hderiv :
      ∀ x ∈ S, HasFDerivWithinAt f (df x) S x)
    (hJ : ∀ x ∈ S, weakJacobian (df x) < 0)
    (ψ : ℂ → ℝ) (hψmeas : Measurable ψ)
    (hψnonneg : ∀ y, 0 ≤ ψ y)
    (hint : Integrable
      (fun x ↦ -weakJacobian (df x) * ψ (f x))
      (volume.restrict S)) :
    (∫ y : ℂ,
        (preimageMultiplicity f S y).toReal * ψ y ∂volume) =
      ∫ x in S,
        -weakJacobian (df x) * ψ (f x) ∂volume := by
  let G : ℂ → ℝ≥0∞ := fun y ↦
    preimageMultiplicity f S y * ENNReal.ofReal (ψ y)
  let H : ℂ → ℝ≥0∞ := fun x ↦
    ENNReal.ofReal
      (-weakJacobian (df x) * ψ (f x))
  have hmultMeas :
      Measurable (preimageMultiplicity f S) :=
    measurable_preimageMultiplicity_of_hasFDerivWithinAt_of_weakJacobian_neg
      hSmeas hderiv hJ
  have hGmeas : Measurable G := by
    exact hmultMeas.mul (ENNReal.measurable_ofReal.comp hψmeas)
  have harea :=
    areaFormula_preimageMultiplicity_of_hasFDerivWithinAt_of_weakJacobian_neg
      hSmeas hderiv hJ (fun y ↦ ENNReal.ofReal (ψ y))
        (ENNReal.measurable_ofReal.comp hψmeas).aemeasurable
  have hsource :
      (∫⁻ x in S,
          ENNReal.ofReal (-weakJacobian (df x)) *
            ENNReal.ofReal (ψ (f x)) ∂volume) =
        ∫⁻ x, H x ∂volume.restrict S := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem hSmeas] with x hx
    rw [← ENNReal.ofReal_mul (neg_nonneg.mpr (le_of_lt (hJ x hx)))]
  have harea' :
      ∫⁻ y, G y ∂volume =
        ∫⁻ x, H x ∂volume.restrict S := by
    simpa [G] using harea.trans hsource
  have hH_ne_top :
      ∫⁻ x, H x ∂volume.restrict S ≠ ∞ := by
    simpa [H] using hint.lintegral_lt_top.ne
  have hG_ne_top :
      ∫⁻ y, G y ∂volume ≠ ∞ := by
    rw [harea']
    exact hH_ne_top
  have hG_lt_top :
      ∀ᵐ y ∂volume, G y < ∞ :=
    ae_lt_top hGmeas hG_ne_top
  have hHmeas :
      AEMeasurable H (volume.restrict S) := by
    exact hint.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hH_lt_top :
      ∀ᵐ x ∂volume.restrict S, H x < ∞ :=
    ae_lt_top' hHmeas hH_ne_top
  calc
    (∫ y : ℂ,
        (preimageMultiplicity f S y).toReal * ψ y ∂volume) =
        ∫ y : ℂ, (G y).toReal ∂volume := by
      apply integral_congr_ae
      filter_upwards with y
      simp [G, ENNReal.toReal_mul, hψnonneg y]
    _ = (∫⁻ y, G y ∂volume).toReal :=
      integral_toReal hGmeas.aemeasurable hG_lt_top
    _ = (∫⁻ x, H x ∂volume.restrict S).toReal := by
      rw [harea']
    _ = ∫ x, (H x).toReal ∂volume.restrict S :=
      (integral_toReal hHmeas hH_lt_top).symm
    _ = ∫ x in S,
        -weakJacobian (df x) * ψ (f x) ∂volume := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hSmeas] with x hx
      exact ENNReal.toReal_ofReal
        (mul_nonneg (neg_nonneg.mpr (le_of_lt (hJ x hx)))
          (hψnonneg (f x)))

/--
%%handwave
name:
  Integrability of weighted multiplicity on a positive-Jacobian locus
statement:
  Under the hypotheses of the real positive-Jacobian area formula, if
  $J_f(\psi\circ f)$ is integrable on $S$, then
  $N(f,S,\cdot)\psi$ is integrable on the target.
proof:
  The extended nonnegative area formula identifies the target $L^1$ norm
  with the finite source integral. Taking real parts gives the asserted
  integrability.
-/
theorem integrable_preimageMultiplicity_toReal_mul_of_pos
    {S : Set ℂ} {f : ℂ → ℂ}
    {df : ℂ → ℂ →L[ℝ] ℂ}
    (hSmeas : MeasurableSet S)
    (hderiv :
      ∀ x ∈ S, HasFDerivWithinAt f (df x) S x)
    (hJ : ∀ x ∈ S, 0 < weakJacobian (df x))
    (ψ : ℂ → ℝ) (hψmeas : Measurable ψ)
    (hψnonneg : ∀ y, 0 ≤ ψ y)
    (hint : Integrable
      (fun x ↦ weakJacobian (df x) * ψ (f x))
      (volume.restrict S)) :
    Integrable
      (fun y ↦ (preimageMultiplicity f S y).toReal * ψ y)
      volume := by
  let G : ℂ → ℝ≥0∞ := fun y ↦
    preimageMultiplicity f S y * ENNReal.ofReal (ψ y)
  have hmultMeas :
      Measurable (preimageMultiplicity f S) :=
    measurable_preimageMultiplicity_of_hasFDerivWithinAt_of_weakJacobian_pos
      hSmeas hderiv hJ
  have hGmeas : Measurable G :=
    hmultMeas.mul (ENNReal.measurable_ofReal.comp hψmeas)
  have harea :=
    areaFormula_preimageMultiplicity_of_hasFDerivWithinAt_of_weakJacobian_pos
      hSmeas hderiv hJ (fun y ↦ ENNReal.ofReal (ψ y))
        (ENNReal.measurable_ofReal.comp hψmeas).aemeasurable
  have hsource_ne_top :
      (∫⁻ x in S,
          ENNReal.ofReal (weakJacobian (df x)) *
            ENNReal.ofReal (ψ (f x)) ∂volume) ≠ ∞ := by
    have heq :
        (∫⁻ x in S,
            ENNReal.ofReal (weakJacobian (df x)) *
              ENNReal.ofReal (ψ (f x)) ∂volume) =
          ∫⁻ x in S,
            ENNReal.ofReal
              (weakJacobian (df x) * ψ (f x)) ∂volume := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hSmeas] with x hx
      rw [ENNReal.ofReal_mul (le_of_lt (hJ x hx))]
    rw [heq]
    exact hint.lintegral_lt_top.ne
  have hG_ne_top :
      ∫⁻ y, G y ∂volume ≠ ∞ := by
    simpa [G] using harea.trans_ne hsource_ne_top
  have htoReal :
      Integrable (fun y ↦ (G y).toReal) volume :=
    integrable_toReal_of_lintegral_ne_top
      hGmeas.aemeasurable hG_ne_top
  apply htoReal.congr
  filter_upwards with y
  simp [G, ENNReal.toReal_mul, hψnonneg y]

/--
%%handwave
name:
  Integrability of weighted multiplicity on a negative-Jacobian locus
statement:
  Under the hypotheses of the real negative-Jacobian area formula, if
  $-J_f(\psi\circ f)$ is integrable on $S$, then
  $N(f,S,\cdot)\psi$ is integrable on the target.
proof:
  The extended nonnegative area formula identifies the target $L^1$ norm
  with the finite source integral. Taking real parts gives the asserted
  integrability.
-/
theorem integrable_preimageMultiplicity_toReal_mul_of_neg
    {S : Set ℂ} {f : ℂ → ℂ}
    {df : ℂ → ℂ →L[ℝ] ℂ}
    (hSmeas : MeasurableSet S)
    (hderiv :
      ∀ x ∈ S, HasFDerivWithinAt f (df x) S x)
    (hJ : ∀ x ∈ S, weakJacobian (df x) < 0)
    (ψ : ℂ → ℝ) (hψmeas : Measurable ψ)
    (hψnonneg : ∀ y, 0 ≤ ψ y)
    (hint : Integrable
      (fun x ↦ -weakJacobian (df x) * ψ (f x))
      (volume.restrict S)) :
    Integrable
      (fun y ↦ (preimageMultiplicity f S y).toReal * ψ y)
      volume := by
  let G : ℂ → ℝ≥0∞ := fun y ↦
    preimageMultiplicity f S y * ENNReal.ofReal (ψ y)
  have hmultMeas :
      Measurable (preimageMultiplicity f S) :=
    measurable_preimageMultiplicity_of_hasFDerivWithinAt_of_weakJacobian_neg
      hSmeas hderiv hJ
  have hGmeas : Measurable G :=
    hmultMeas.mul (ENNReal.measurable_ofReal.comp hψmeas)
  have harea :=
    areaFormula_preimageMultiplicity_of_hasFDerivWithinAt_of_weakJacobian_neg
      hSmeas hderiv hJ (fun y ↦ ENNReal.ofReal (ψ y))
        (ENNReal.measurable_ofReal.comp hψmeas).aemeasurable
  have hsource_ne_top :
      (∫⁻ x in S,
          ENNReal.ofReal (-weakJacobian (df x)) *
            ENNReal.ofReal (ψ (f x)) ∂volume) ≠ ∞ := by
    have heq :
        (∫⁻ x in S,
            ENNReal.ofReal (-weakJacobian (df x)) *
              ENNReal.ofReal (ψ (f x)) ∂volume) =
          ∫⁻ x in S,
            ENNReal.ofReal
              (-weakJacobian (df x) * ψ (f x)) ∂volume := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hSmeas] with x hx
      rw [ENNReal.ofReal_mul
        (neg_nonneg.mpr (le_of_lt (hJ x hx)))]
    rw [heq]
    exact hint.lintegral_lt_top.ne
  have hG_ne_top :
      ∫⁻ y, G y ∂volume ≠ ∞ := by
    simpa [G] using harea.trans_ne hsource_ne_top
  have htoReal :
      Integrable (fun y ↦ (G y).toReal) volume :=
    integrable_toReal_of_lintegral_ne_top
      hGmeas.aemeasurable hG_ne_top
  apply htoReal.congr
  filter_upwards with y
  simp [G, ENNReal.toReal_mul, hψnonneg y]

/--
%%handwave
name:
  Measurable multiplicity and its area formula from differentiability pieces
statement:
  Let pairwise disjoint measurable sets $T_n\subseteq S$ cover a measurable
  set $S$. Suppose that $f$ has real differential $Df(x)$ on every $T_n$,
  relative to $T_n$, that $x\mapsto J(Df(x))$ is measurable, and that
  $J(Df(x))\geq0$ on $S$. Then, for every almost-everywhere measurable
  $g:\mathbb C\to[0,\infty]$,
  $$
    \int_{\mathbb C}N(f,S,y)g(y)\,dy
      =
    \int_S J(Df(x))g(f(x))\,dx.
  $$
  Moreover, $y\mapsto N(f,S,y)$ is measurable up to a null set.
proof:
  On each $T_n$, split off the positive-Jacobian locus and decompose it into countably many injective sheets. Pairing the two indices gives one countable, pairwise disjoint sheet family covering the positive-Jacobian locus of $S$. Apply [the injective-sheet multiplicity formula](lean:JJMath.Quasiconformal.areaFormula_preimageMultiplicity_of_injective_sheets). The zero-Jacobian pieces have null images by the fixed-dimensional Sard lemma, and their countable union changes neither side of the formula.
-/
theorem areaFormula_preimageMultiplicity_of_countable_hasFDerivWithinAt_of_weakJacobian_nonneg_and_aemeasurable
    {S : Set ℂ} {f : ℂ → ℂ}
    {df : ℂ → ℂ →L[ℝ] ℂ}
    (hSmeas : MeasurableSet S)
    (t : ℕ → Set ℂ)
    (htmeas : ∀ n, MeasurableSet (t n))
    (htS : ∀ n, t n ⊆ S)
    (htdisj : Pairwise (Disjoint on t))
    (hcover : S ⊆ ⋃ n, t n)
    (hderiv :
      ∀ n x, x ∈ t n →
        HasFDerivWithinAt f (df x) (t n) x)
    (hJmeas :
      Measurable (fun x => weakJacobian (df x)))
    (hJ : ∀ x ∈ S, 0 ≤ weakJacobian (df x))
    (g : ℂ → ℝ≥0∞)
    (hg : AEMeasurable g volume) :
    AEMeasurable (preimageMultiplicity f S) volume ∧
      ∫⁻ y,
          preimageMultiplicity f S y * g y ∂volume =
        ∫⁻ x in S,
          ENNReal.ofReal (weakJacobian (df x)) *
            g (f x) ∂volume := by
  let P : Set ℂ :=
    S ∩ {x | 0 < weakJacobian (df x)}
  let Z : Set ℂ :=
    S ∩ {x | weakJacobian (df x) = 0}
  let p : ℕ → Set ℂ :=
    fun n =>
      t n ∩ {x | 0 < weakJacobian (df x)}
  let z : ℕ → Set ℂ :=
    fun n =>
      t n ∩ {x | weakJacobian (df x) = 0}
  have hPmeas : MeasurableSet P := by
    exact hSmeas.inter
      (measurableSet_Ioi.preimage hJmeas)
  have hpmeas :
      ∀ n, MeasurableSet (p n) := by
    intro n
    exact (htmeas n).inter
      (measurableSet_Ioi.preimage hJmeas)
  have hpderiv :
      ∀ n x, x ∈ p n →
        HasFDerivWithinAt f (df x) (p n) x := by
    intro n x hx
    exact (hderiv n x hx.1).mono inter_subset_left
  have hpJ :
      ∀ n x, x ∈ p n →
        0 < weakJacobian (df x) := by
    intro n x hx
    exact hx.2
  have huexists :
      ∀ n, ∃ u : ℕ → Set ℂ,
        Pairwise (Disjoint on u) ∧
          (∀ m, MeasurableSet (u m)) ∧
            (∀ m, u m ⊆ p n) ∧
              p n ⊆ ⋃ m, u m ∧
                ∀ m, Set.InjOn f (u m) := by
    intro n
    exact
      exists_countable_measurable_injective_cover_of_hasFDerivWithinAt_of_weakJacobian_pos
        (hpmeas n) (hpderiv n) (hpJ n)
  choose u hu using huexists
  have hudisj :
      ∀ n, Pairwise (Disjoint on u n) :=
    fun n => (hu n).1
  have humeas :
      ∀ n m, MeasurableSet (u n m) :=
    fun n => (hu n).2.1
  have hup :
      ∀ n m, u n m ⊆ p n :=
    fun n => (hu n).2.2.1
  have hucover :
      ∀ n, p n ⊆ ⋃ m, u n m :=
    fun n => (hu n).2.2.2.1
  have huinj :
      ∀ n m, Set.InjOn f (u n m) :=
    fun n => (hu n).2.2.2.2
  let q : ℕ → Set ℂ :=
    fun k =>
      u (Nat.unpair k).1 (Nat.unpair k).2
  have hqmeas :
      ∀ k, MeasurableSet (q k) := by
    intro k
    exact humeas _ _
  have hqP :
      ∀ k, q k ⊆ P := by
    intro k x hx
    have hxp :
        x ∈ p (Nat.unpair k).1 :=
      hup _ _ hx
    exact ⟨htS _ hxp.1, hxp.2⟩
  have hqdisj :
      Pairwise (Disjoint on q) := by
    intro a b hab
    by_cases hfirst :
        (Nat.unpair a).1 =
          (Nat.unpair b).1
    · have hsecond :
          (Nat.unpair a).2 ≠
            (Nat.unpair b).2 := by
        intro hs
        apply hab
        exact Nat.pairEquiv.symm.injective
          (Prod.ext hfirst hs)
      change
        Disjoint
          (u (Nat.unpair a).1
            (Nat.unpair a).2)
          (u (Nat.unpair b).1
            (Nat.unpair b).2)
      rw [← hfirst]
      exact hudisj (Nat.unpair a).1 hsecond
    · apply (htdisj hfirst).mono
      · exact
          (hup _ _).trans inter_subset_left
      · exact
          (hup _ _).trans inter_subset_left
  have hqcover :
      P ⊆ ⋃ k, q k := by
    intro x hx
    rcases Set.mem_iUnion.mp
        (hcover hx.1) with
      ⟨n, hxt⟩
    have hxp : x ∈ p n :=
      ⟨hxt, hx.2⟩
    rcases Set.mem_iUnion.mp
        (hucover n hxp) with
      ⟨m, hxu⟩
    refine Set.mem_iUnion.mpr
      ⟨Nat.pair n m, ?_⟩
    simpa [q, Nat.unpair_pair] using hxu
  have hqderiv :
      ∀ k x, x ∈ q k →
        HasFDerivWithinAt f (df x) (q k) x := by
    intro k x hx
    have hxp :
        x ∈ p (Nat.unpair k).1 :=
      hup _ _ hx
    exact
      (hderiv (Nat.unpair k).1 x hxp.1).mono
        ((hup _ _).trans inter_subset_left)
  have hqinj :
      ∀ k, Set.InjOn f (q k) := by
    intro k
    exact huinj _ _
  have hpositiveAbs :=
    areaFormula_preimageMultiplicity_of_injective_sheets
      q hqmeas hqP hqdisj hqcover
        hqderiv hqinj g hg
  have hpositive :
      ∫⁻ y,
          preimageMultiplicity f P y * g y ∂volume =
        ∫⁻ x in P,
          ENNReal.ofReal (weakJacobian (df x)) *
            g (f x) ∂volume := by
    rw [hpositiveAbs]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem hPmeas] with x hx
    rw [abs_of_pos hx.2]
  have hzderiv :
      ∀ n x, x ∈ z n →
        HasFDerivWithinAt f (df x) (z n) x := by
    intro n x hx
    exact (hderiv n x hx.1).mono inter_subset_left
  have hzdet :
      ∀ n x, x ∈ z n →
        (df x).det = 0 := by
    intro n x hx
    simpa [weakJacobian] using hx.2
  have hzimage :
      ∀ n, volume (f '' z n) = 0 := by
    intro n
    exact
      MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero
        (μ := volume) (hzderiv n) (hzdet n)
  have hZcover :
      Z ⊆ ⋃ n, z n := by
    intro x hx
    rcases Set.mem_iUnion.mp
        (hcover hx.1) with
      ⟨n, hxt⟩
    exact Set.mem_iUnion.mpr
      ⟨n, hxt, hx.2⟩
  have himageZ :
      volume (f '' Z) = 0 := by
    have hsubset :
        f '' Z ⊆ ⋃ n, f '' z n := by
      rintro y ⟨x, hxZ, rfl⟩
      rcases Set.mem_iUnion.mp
          (hZcover hxZ) with
        ⟨n, hxn⟩
      exact Set.mem_iUnion.mpr
        ⟨n, ⟨x, hxn, rfl⟩⟩
    apply le_antisymm
    · calc
        volume (f '' Z) ≤
            volume (⋃ n, f '' z n) :=
          measure_mono hsubset
        _ ≤ ∑' n, volume (f '' z n) :=
          measure_iUnion_le _
        _ = 0 := by
          simp [hzimage]
    · exact bot_le
  have hmult :
      ∀ᵐ y ∂volume,
        preimageMultiplicity f S y =
          preimageMultiplicity f P y := by
    filter_upwards [compl_mem_ae_iff.mpr himageZ] with y hy
    have hfiber :
        S ∩ f ⁻¹' {y} =
          P ∩ f ⁻¹' {y} := by
      ext x
      constructor
      · intro hx
        have hxS : x ∈ S := hx.1
        have hxy : f x = y := by
          simpa using hx.2
        by_cases hpos :
            0 < weakJacobian (df x)
        · exact ⟨⟨hxS, hpos⟩, hx.2⟩
        · have hzero :
              weakJacobian (df x) = 0 :=
            le_antisymm (not_lt.mp hpos) (hJ x hxS)
          exfalso
          apply hy
          exact ⟨x, ⟨hxS, hzero⟩, hxy⟩
      · intro hx
        exact ⟨hx.1.1, hx.2⟩
    simp only [preimageMultiplicity]
    rw [hfiber]
  have hmultPMeas :
      Measurable (preimageMultiplicity f P) :=
    measurable_preimageMultiplicity_of_injective_sheets
      q hqmeas hqP hqdisj hqcover hqderiv hqinj
  have hmultSAE :
      AEMeasurable (preimageMultiplicity f S) volume :=
    hmultPMeas.aemeasurable.congr
      (hmult.mono fun _ hy => hy.symm)
  let H : ℂ → ℝ≥0∞ :=
    fun x =>
      ENNReal.ofReal (weakJacobian (df x)) *
        g (f x)
  have hsource :
      ∫⁻ x in P, H x ∂volume =
        ∫⁻ x in S, H x ∂volume := by
    rw [← lintegral_indicator hPmeas,
      ← lintegral_indicator hSmeas]
    apply lintegral_congr
    intro x
    by_cases hxS : x ∈ S
    · by_cases hpos :
          0 < weakJacobian (df x)
      · have hxP : x ∈ P :=
          ⟨hxS, hpos⟩
        rw [Set.indicator_of_mem hxP,
          Set.indicator_of_mem hxS]
      · have hxP : x ∉ P := by
          intro hx
          exact hpos hx.2
        have hzero :
            weakJacobian (df x) = 0 :=
          le_antisymm (not_lt.mp hpos) (hJ x hxS)
        rw [Set.indicator_of_notMem hxP,
          Set.indicator_of_mem hxS]
        simp [H, hzero]
    · have hxP : x ∉ P :=
        fun hx => hxS hx.1
      rw [Set.indicator_of_notMem hxP,
        Set.indicator_of_notMem hxS]
  refine ⟨hmultSAE, ?_⟩
  calc
    ∫⁻ y,
        preimageMultiplicity f S y * g y ∂volume =
        ∫⁻ y,
          preimageMultiplicity f P y * g y ∂volume := by
      apply lintegral_congr_ae
      filter_upwards [hmult] with y hy
      rw [hy]
    _ = ∫⁻ x in P, H x ∂volume := by
      simpa [H] using hpositive
    _ = ∫⁻ x in S, H x ∂volume :=
      hsource
    _ = ∫⁻ x in S,
        ENNReal.ofReal (weakJacobian (df x)) *
          g (f x) ∂volume := by
      rfl

/--
%%handwave
name:
  Multiplicity area formula from countably many differentiability pieces
statement:
  Let pairwise disjoint measurable sets $T_n\subseteq S$ cover a measurable
  set $S$. Suppose that $f$ has real differential $Df(x)$ on every $T_n$,
  relative to $T_n$, that $x\mapsto J(Df(x))$ is measurable, and that
  $J(Df(x))\geq0$ on $S$. Then, for every almost-everywhere measurable
  $g:\mathbb C\to[0,\infty]$,
  $$
    \int_{\mathbb C}N(f,S,y)g(y)\,dy
      =
    \int_S J(Df(x))g(f(x))\,dx.
  $$
proof:
  Apply [the measurable multiplicity formula on the same differentiability pieces](lean:JJMath.Quasiconformal.areaFormula_preimageMultiplicity_of_countable_hasFDerivWithinAt_of_weakJacobian_nonneg_and_aemeasurable) and retain its integral identity.
-/
theorem areaFormula_preimageMultiplicity_of_countable_hasFDerivWithinAt_of_weakJacobian_nonneg
    {S : Set ℂ} {f : ℂ → ℂ}
    {df : ℂ → ℂ →L[ℝ] ℂ}
    (hSmeas : MeasurableSet S)
    (t : ℕ → Set ℂ)
    (htmeas : ∀ n, MeasurableSet (t n))
    (htS : ∀ n, t n ⊆ S)
    (htdisj : Pairwise (Disjoint on t))
    (hcover : S ⊆ ⋃ n, t n)
    (hderiv :
      ∀ n x, x ∈ t n →
        HasFDerivWithinAt f (df x) (t n) x)
    (hJmeas :
      Measurable (fun x => weakJacobian (df x)))
    (hJ : ∀ x ∈ S, 0 ≤ weakJacobian (df x))
    (g : ℂ → ℝ≥0∞)
    (hg : AEMeasurable g volume) :
    ∫⁻ y,
        preimageMultiplicity f S y * g y ∂volume =
      ∫⁻ x in S,
        ENNReal.ofReal (weakJacobian (df x)) *
          g (f x) ∂volume :=
  (areaFormula_preimageMultiplicity_of_countable_hasFDerivWithinAt_of_weakJacobian_nonneg_and_aemeasurable
    hSmeas t htmeas htS htdisj hcover hderiv hJmeas hJ g hg).2

/--
%%handwave
name:
  Area formula from countably many differentiability pieces and Lusin $N$
statement:
  Let $f:\Omega\to\mathbb C$ be injective and have the Lusin $N$ property.
  Suppose pairwise disjoint measurable sets $t_n\subseteq\Omega$ cover
  almost every point of $\Omega$, and on every $t_n$ the restriction of $f$
  has real differential $Df(z)$. Then for every measurable
  $s\subseteq\Omega$ and every $g:\mathbb C\to[0,\infty]$,
  $$
  \int_{f(s)}g(y)\,dy
  =\int_s |\operatorname{Jac}f(z)|g(f(z))\,dz.
  $$
proof:
  Intersect the differentiability pieces with $s$. Apply [the area formula on each measurable piece](lean:JJMath.Quasiconformal.areaFormula_of_hasFDerivWithinAt) and sum over their pairwise disjoint images. The omitted source set is null, and Lusin $N$ makes its image null.
-/
theorem areaFormula_of_countable_hasFDerivWithinAt_of_hasLusinNOn
    {Ω : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (hinj : Set.InjOn f Ω) (hN : HasLusinNOn Ω f)
    (t : ℕ → Set ℂ) (htmeas : ∀ n, MeasurableSet (t n))
    (htΩ : ∀ n, t n ⊆ Ω) (htdisj : Pairwise (Disjoint on t))
    (hcover : ∀ᵐ z ∂volume.restrict Ω, z ∈ ⋃ n, t n)
    (hderiv : ∀ n z, z ∈ t n → HasFDerivWithinAt f (df z) (t n) z)
    {s : Set ℂ} (hs : MeasurableSet s) (hsΩ : s ⊆ Ω)
    (g : ℂ → ℝ≥0∞) :
    ∫⁻ y in f '' s, g y ∂volume =
      ∫⁻ z in s, ENNReal.ofReal |weakJacobian (df z)| * g (f z) ∂volume := by
  let U : Set ℂ := ⋃ n, t n
  let q : Set ℂ := s ∩ U
  let u : ℕ → Set ℂ := fun n ↦ s ∩ t n
  have humeas : ∀ n, MeasurableSet (u n) := fun n ↦ hs.inter (htmeas n)
  have huΩ : ∀ n, u n ⊆ Ω := fun n ↦
    inter_subset_right.trans (htΩ n)
  have hudisj : Pairwise (Disjoint on u) :=
    pairwise_disjoint_mono htdisj fun n ↦ inter_subset_right
  have himage_meas : ∀ n, MeasurableSet (f '' u n) := by
    intro n
    exact measurable_image_of_fderivWithin (humeas n)
      (fun z hz ↦ (hderiv n z hz.2).mono inter_subset_right)
      (hinj.mono (huΩ n))
  have himage_disj : Pairwise (Disjoint on fun n ↦ f '' u n) := by
    intro i j hij
    apply Disjoint.image _ hinj (huΩ i) (huΩ j)
    exact hudisj hij
  have hcover_global : ∀ᵐ z ∂volume, z ∈ Ω → z ∈ U := by
    simpa [U] using ae_imp_of_ae_restrict hcover
  have hcover_s : ∀ᵐ z ∂volume, z ∈ s → z ∈ U := by
    filter_upwards [hcover_global] with z hz
    exact fun hzs ↦ hz (hsΩ hzs)
  have hq_ae : q =ᵐ[volume] s := by
    filter_upwards [hcover_s] with z hz
    apply propext
    constructor
    · exact fun hzq ↦ hzq.1
    · exact fun hzs ↦ ⟨hzs, hz hzs⟩
  have hsq0 : volume (s \ q) = 0 := (ae_eq_set.1 hq_ae).2
  have himage0 : volume (f '' (s \ q)) = 0 :=
    hN (s \ q) (diff_subset.trans hsΩ) hsq0
  have himage_ae : f '' q =ᵐ[volume] f '' s := by
    apply ae_eq_set.2
    constructor
    · rw [diff_eq_empty.mpr (image_mono inter_subset_left), measure_empty]
    · apply measure_mono_null _ himage0
      intro y hy
      obtain ⟨x, hxs, rfl⟩ := hy.1
      exact ⟨x, ⟨hxs, fun hxq ↦ hy.2 ⟨x, hxq, rfl⟩⟩, rfl⟩
  have hq_union : q = ⋃ n, u n := by
    simp only [q, u, U]
    rw [inter_iUnion]
  let integrand : ℂ → ℝ≥0∞ := fun z ↦
    ENNReal.ofReal |weakJacobian (df z)| * g (f z)
  calc
    ∫⁻ y in f '' s, g y ∂volume = ∫⁻ y in f '' q, g y ∂volume :=
      setLIntegral_congr himage_ae.symm
    _ = ∫⁻ y in ⋃ n, f '' u n, g y ∂volume := by rw [← image_iUnion, ← hq_union]
    _ = ∑' n, ∫⁻ y in f '' u n, g y ∂volume :=
      lintegral_iUnion himage_meas himage_disj g
    _ = ∑' n, ∫⁻ z in u n, integrand z ∂volume := by
      apply tsum_congr
      intro n
      simpa [integrand] using
        areaFormula_of_hasFDerivWithinAt (humeas n) (hinj.mono (huΩ n))
          (fun z hz ↦ (hderiv n z hz.2).mono inter_subset_right) g
    _ = ∫⁻ z in ⋃ n, u n, integrand z ∂volume :=
      (lintegral_iUnion humeas hudisj integrand).symm
    _ = ∫⁻ z in q, integrand z ∂volume := by rw [hq_union]
    _ = ∫⁻ z in s, integrand z ∂volume := setLIntegral_congr hq_ae

/--
%%handwave
name:
  Area formula from a countable differentiability cover and Lusin $N$
statement:
  Let $f:\Omega\to\mathbb C$ be injective and have the Lusin $N$ property.
  Suppose measurable sets $t_n\subseteq\Omega$ cover almost every point of
  $\Omega$, and on every $t_n$ the restriction of $f$ has real differential
  $Df(z)$. Then for every measurable $s\subseteq\Omega$ and every
  $g:\mathbb C\to[0,\infty]$,
  $$
  \int_{f(s)}g(y)\,dy
  =\int_s |\operatorname{Jac}f(z)|g(f(z))\,dz.
  $$
proof:
  Replace the cover by its successive disjoint differences. These pieces have the same union, and differentiation within an original piece restricts to its corresponding difference. Apply [the area formula for pairwise disjoint differentiability pieces](lean:JJMath.Quasiconformal.areaFormula_of_countable_hasFDerivWithinAt_of_hasLusinNOn).
-/
theorem areaFormula_of_countable_cover_hasFDerivWithinAt_of_hasLusinNOn
    {Ω : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (hinj : Set.InjOn f Ω) (hN : HasLusinNOn Ω f)
    (t : ℕ → Set ℂ) (htmeas : ∀ n, MeasurableSet (t n))
    (htΩ : ∀ n, t n ⊆ Ω)
    (hcover : ∀ᵐ z ∂volume.restrict Ω, z ∈ ⋃ n, t n)
    (hderiv : ∀ n z, z ∈ t n → HasFDerivWithinAt f (df z) (t n) z)
    {s : Set ℂ} (hs : MeasurableSet s) (hsΩ : s ⊆ Ω)
    (g : ℂ → ℝ≥0∞) :
    ∫⁻ y in f '' s, g y ∂volume =
      ∫⁻ z in s, ENNReal.ofReal |weakJacobian (df z)| * g (f z) ∂volume := by
  apply areaFormula_of_countable_hasFDerivWithinAt_of_hasLusinNOn
    hinj hN (disjointed t)
  · exact MeasurableSet.disjointed htmeas
  · exact fun n ↦ (disjointed_subset t n).trans (htΩ n)
  · exact disjoint_disjointed t
  · simpa only [iUnion_disjointed] using hcover
  · intro n z hz
    exact (hderiv n z (disjointed_subset t n hz)).mono (disjointed_subset t n)
  · exact hs
  · exact hsΩ

/--
%%handwave
name:
  Area formula for a planar homeomorphism from a differentiability cover
statement:
  Let $F:\Omega\to\Omega'$ be a homeomorphism with the Lusin $N$ property.
  Suppose measurable sets $t_n\subseteq\Omega$ cover almost every point of
  $\Omega$, and on every $t_n$ the ambient representative of $F$ has real
  differential $Df(z)$ within $t_n$. Then for every measurable
  $s\subseteq\Omega$ and every $g:\mathbb C\to[0,\infty]$,
  $$
  \int_{F(s)}g(y)\,dy
  =\int_s |\operatorname{Jac}f(z)|g(F(z))\,dz.
  $$
proof:
  The ambient representative is injective on $\Omega$, so apply [the area formula from a countable differentiability cover and Lusin $N$](lean:JJMath.Quasiconformal.areaFormula_of_countable_cover_hasFDerivWithinAt_of_hasLusinNOn).
-/
theorem areaFormula_ambientMap_of_countable_cover_hasFDerivWithinAt_of_hasLusinNOn
    {Ω Ω' : Set ℂ} (F : Ω ≃ₜ Ω') {df : ℂ → ℂ →L[ℝ] ℂ}
    (hN : HasLusinNOn Ω (ambientMap F))
    (t : ℕ → Set ℂ) (htmeas : ∀ n, MeasurableSet (t n))
    (htΩ : ∀ n, t n ⊆ Ω)
    (hcover : ∀ᵐ z ∂volume.restrict Ω, z ∈ ⋃ n, t n)
    (hderiv : ∀ n z, z ∈ t n →
      HasFDerivWithinAt (ambientMap F) (df z) (t n) z)
    {s : Set ℂ} (hs : MeasurableSet s) (hsΩ : s ⊆ Ω)
    (g : ℂ → ℝ≥0∞) :
    ∫⁻ y in ambientMap F '' s, g y ∂volume =
      ∫⁻ z in s,
        ENNReal.ofReal |weakJacobian (df z)| * g (ambientMap F z) ∂volume := by
  exact areaFormula_of_countable_cover_hasFDerivWithinAt_of_hasLusinNOn
    (ambientMap_injOn F) hN t htmeas htΩ hcover hderiv hs hsΩ g

/--
%%handwave
name:
  An area formula implies the Lusin property
statement:
  Suppose $\Omega\subseteq\mathbb C$ is measurable and
  $f:\mathbb C\to\mathbb C$ satisfies
  $$
  \int_{f(s)}g(y)\,dy
  =\int_s |J(z)|g(f(z))\,dz
  $$
  for every measurable $s\subseteq\Omega$ and every
  $g:\mathbb C\to[0,\infty]$. Then $f$ sends every null subset of $\Omega$
  to a null set.
proof:
  Enlarge a null set to a measurable null set, intersect it with $\Omega$,
  and apply the area formula with $g=1$. The integral on the source vanishes,
  so the image of the measurable enlargement has measure zero.
-/
theorem hasLusinNOn_of_areaFormula
    {Ω : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (hΩ : MeasurableSet Ω)
    (harea : ∀ {s : Set ℂ}, MeasurableSet s → s ⊆ Ω → ∀ g : ℂ → ℝ≥0∞,
      ∫⁻ y in f '' s, g y ∂volume =
        ∫⁻ z in s, ENNReal.ofReal |weakJacobian (df z)| * g (f z) ∂volume) :
    HasLusinNOn Ω f := by
  intro s hsΩ hs0
  obtain ⟨t, hst, htmeas, ht0⟩ := exists_measurable_superset_of_null hs0
  let u : Set ℂ := t ∩ Ω
  have hsu : s ⊆ u := fun z hz ↦ ⟨hst hz, hsΩ hz⟩
  have humeas : MeasurableSet u := htmeas.inter hΩ
  have huΩ : u ⊆ Ω := inter_subset_right
  have hu0 : volume u = 0 := measure_mono_null inter_subset_left ht0
  have hformula := harea humeas huΩ (fun _ ↦ 1)
  have himage : volume (f '' u) = 0 := by
    rw [setLIntegral_one] at hformula
    rw [setLIntegral_measure_zero u
      (fun z ↦ ENNReal.ofReal |weakJacobian (df z)| * 1) hu0] at hformula
    exact hformula
  exact measure_mono_null (image_mono hsu) himage

/--
%%handwave
name:
  Nonnegative Jacobian of a quasiconformal weak differential
statement:
  If $F:\Omega\to\Omega'$ is $K$-quasiconformal and $Df$ is any of its local
  weak differentials, then
  $$\operatorname{Jac}f(z)\geq0$$
  for almost every $z\in\Omega$.
proof:
  The distortion inequality bounds the nonnegative number
  $\|Df(z)\|_{\mathrm{op}}^2$ above by $K\operatorname{Jac}f(z)$, while
  $K\geq1$.
-/
theorem IsKQuasiconformalBetween.weakJacobian_nonneg_ae
    {K : ℝ} {Ω Ω' : Set ℂ} {F : Ω ≃ₜ Ω'}
    (hF : IsKQuasiconformalBetween K F) {df : ℂ → ℂ →L[ℝ] ℂ}
    (hdf : IsLocalW12On Ω (ambientMap F) df) :
    ∀ᵐ z ∂volume.restrict Ω, 0 ≤ weakJacobian (df z) := by
  have hdist := hF.distortion_of_weakDifferential hdf
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hF.1
  filter_upwards [hdist] with z hz
  by_contra hJ
  have hJneg : weakJacobian (df z) < 0 := lt_of_not_ge hJ
  have hright : K * weakJacobian (df z) < 0 := mul_neg_of_pos_of_neg hKpos hJneg
  nlinarith [sq_nonneg ‖df z‖]

/--
%%handwave
name:
  Sobolev area formula for a planar quasiconformal homeomorphism
statement:
  Let $F:\Omega\to\Omega'$ be $K$-quasiconformal with weak differential
  $Df$. For every measurable $s\subseteq\Omega$ and every
  $g:\mathbb C\to[0,\infty]$,
  $$
  \int_{f(s)}g(y)\,dy
  =\int_s |\operatorname{Jac}f(z)|g(f(z))\,dz.
  $$
proof:
  First prove the Lusin $N$ property independently. Establish approximate
  differentiability almost everywhere with approximate differential $Df$ and
  cover almost all of the source by countably many measurable sets on which
  the map has differential $Df$ within the set. Apply [the area formula for a planar homeomorphism from such a differentiability cover](lean:JJMath.Quasiconformal.areaFormula_ambientMap_of_countable_cover_hasFDerivWithinAt_of_hasLusinNOn).
-/
theorem IsKQuasiconformalBetween.areaFormula_abs
    {K : ℝ} {Ω Ω' : Set ℂ} {F : Ω ≃ₜ Ω'}
    (hF : IsKQuasiconformalBetween K F) {df : ℂ → ℂ →L[ℝ] ℂ}
    (hdf : IsLocalW12On Ω (ambientMap F) df)
    {s : Set ℂ} (hs : MeasurableSet s) (hsΩ : s ⊆ Ω)
    (g : ℂ → ℝ≥0∞) :
    ∫⁻ y in ambientMap F '' s, g y ∂volume =
      ∫⁻ z in s,
        ENNReal.ofReal |weakJacobian (df z)| * g (ambientMap F z) ∂volume := by
  obtain ⟨T, hTmeas, hTΩ, hcover, hderiv⟩ :=
    hdf.exists_countable_measurable_cover_hasFDerivWithinAt
  exact areaFormula_ambientMap_of_countable_cover_hasFDerivWithinAt_of_hasLusinNOn
    F (hdf.hasLusinNOn_ambientMap F hdf.1 hF.2.1)
      T hTmeas hTΩ hcover hderiv hs hsΩ g

/--
%%handwave
name:
  Oriented Sobolev area formula for a planar quasiconformal homeomorphism
statement:
  Let $F:\Omega\to\Omega'$ be $K$-quasiconformal with weak differential
  $Df$. For every measurable $s\subseteq\Omega$ and every
  $g:\mathbb C\to[0,\infty]$,
  $$
  \int_{f(s)}g(y)\,dy
  =\int_s \operatorname{Jac}f(z)g(f(z))\,dz.
  $$
proof:
  Combine [the Sobolev area formula](lean:JJMath.Quasiconformal.IsKQuasiconformalBetween.areaFormula_abs) with the almost-everywhere nonnegativity of the Jacobian.
-/
theorem IsKQuasiconformalBetween.areaFormula
    {K : ℝ} {Ω Ω' : Set ℂ} {F : Ω ≃ₜ Ω'}
    (hF : IsKQuasiconformalBetween K F) {df : ℂ → ℂ →L[ℝ] ℂ}
    (hdf : IsLocalW12On Ω (ambientMap F) df)
    {s : Set ℂ} (hs : MeasurableSet s) (hsΩ : s ⊆ Ω)
    (g : ℂ → ℝ≥0∞) :
    ∫⁻ y in ambientMap F '' s, g y ∂volume =
      ∫⁻ z in s,
        ENNReal.ofReal (weakJacobian (df z)) * g (ambientMap F z) ∂volume := by
  rw [hF.areaFormula_abs hdf hs hsΩ g]
  apply lintegral_congr_ae
  have hnonneg := ae_restrict_of_ae_restrict_of_subset hsΩ
    (hF.weakJacobian_nonneg_ae hdf)
  filter_upwards [hnonneg] with z hz
  rw [abs_of_nonneg hz]

/--
%%handwave
name:
  Differential energy is controlled by image area
statement:
  Let $F:\Omega\to\Omega'$ be $K$-quasiconformal with weak differential
  $Df$. For every measurable set $E\subseteq\Omega$,
  $$
    \int_E \lVert Df(z)\rVert_{\mathrm{op}}^2\,dz
      \leq K\,|f(E)|.
  $$
  Both sides are interpreted as extended nonnegative integrals.
proof:
  Integrate the pointwise distortion inequality
  $\lVert Df\rVert_{\mathrm{op}}^2\leq K\operatorname{Jac}f$. The
  [oriented Sobolev area formula](lean:JJMath.Quasiconformal.IsKQuasiconformalBetween.areaFormula)
  identifies the integral of the nonnegative Jacobian over $E$ with the
  area of $f(E)$.
-/
theorem IsKQuasiconformalBetween.lintegral_norm_weakDifferential_sq_le_volume_image
    {K : ℝ} {Ω Ω' : Set ℂ} {F : Ω ≃ₜ Ω'}
    (hF : IsKQuasiconformalBetween K F) {df : ℂ → ℂ →L[ℝ] ℂ}
    (hdf : IsLocalW12On Ω (ambientMap F) df)
    {s : Set ℂ} (hs : MeasurableSet s) (hsΩ : s ⊆ Ω) :
    (∫⁻ z in s, ENNReal.ofReal (‖df z‖ ^ 2) ∂volume) ≤
      ENNReal.ofReal K * volume (ambientMap F '' s) := by
  have hK : 0 ≤ K := zero_le_one.trans hF.1
  have hdist := ae_restrict_of_ae_restrict_of_subset hsΩ
    (hF.distortion_of_weakDifferential hdf)
  have hJ := ae_restrict_of_ae_restrict_of_subset hsΩ
    (hF.weakJacobian_nonneg_ae hdf)
  have hpoint : ∀ᵐ z ∂volume.restrict s,
      ENNReal.ofReal (‖df z‖ ^ 2) ≤
        ENNReal.ofReal K * ENNReal.ofReal (weakJacobian (df z)) := by
    filter_upwards [hdist, hJ] with z hzdist hzJ
    calc
      ENNReal.ofReal (‖df z‖ ^ 2) ≤
          ENNReal.ofReal (K * weakJacobian (df z)) :=
        ENNReal.ofReal_mono hzdist
      _ = ENNReal.ofReal K * ENNReal.ofReal (weakJacobian (df z)) := by
        rw [ENNReal.ofReal_mul hK]
  have harea := hF.areaFormula hdf hs hsΩ (fun _ ↦ 1)
  have harea' :
      (∫⁻ z in s, ENNReal.ofReal (weakJacobian (df z)) ∂volume) =
        volume (ambientMap F '' s) := by
    simpa [setLIntegral_one] using harea.symm
  calc
    (∫⁻ z in s, ENNReal.ofReal (‖df z‖ ^ 2) ∂volume) ≤
        ∫⁻ z in s,
          ENNReal.ofReal K * ENNReal.ofReal (weakJacobian (df z)) ∂volume :=
      lintegral_mono_ae hpoint
    _ = ENNReal.ofReal K *
        ∫⁻ z in s, ENNReal.ofReal (weakJacobian (df z)) ∂volume := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal K * volume (ambientMap F '' s) := by rw [harea']

/--
%%handwave
name:
  Oriented Sobolev change of variables for Bochner integrals
statement:
  Let $F:\Omega\to\Omega'$ be a planar quasiconformal homeomorphism with
  weak differential $Df$. If $s\subseteq\Omega$ is measurable and
  $g:\mathbb C\to E$ is strongly measurable almost everywhere on $F(s)$,
  then
  $$
    \int_{F(s)} g(y)\,dy
      =\int_s J(Df(z))\,g(F(z))\,dz.
  $$
proof:
  Put the density $\max\{J(Df),0\}$ on the restricted source measure. The
  nonnegative area formula, applied to indicators of measurable sets, says
  that its pushforward by $F$ is Lebesgue measure restricted to $F(s)$.
  Apply the Bochner integral mapping theorem and then use the almost-everywhere
  nonnegativity of the Jacobian.
-/
theorem IsKQuasiconformalBetween.integral_image_eq_integral_weakJacobian_smul
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : ℝ} {Ω Ω' : Set ℂ} {F : Ω ≃ₜ Ω'}
    (hF : IsKQuasiconformalBetween K F) {df : ℂ → ℂ →L[ℝ] ℂ}
    (hdf : IsLocalW12On Ω (ambientMap F) df)
    {s : Set ℂ} (hs : MeasurableSet s) (hsΩ : s ⊆ Ω)
    {g : ℂ → E}
    (hg : AEStronglyMeasurable g
      (volume.restrict (ambientMap F '' s))) :
    ∫ y in ambientMap F '' s, g y ∂volume =
      ∫ z in s,
        weakJacobian (df z) • g (ambientMap F z) ∂volume := by
  let j : ℂ → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (weakJacobian (df z))
  let ν : Measure ℂ := (volume.restrict s).withDensity j
  have hdf_aesm : AEStronglyMeasurable df (volume.restrict Ω) :=
    hdf.differential_locallyIntegrableOn.aestronglyMeasurable
  have hdf_s : AEStronglyMeasurable df (volume.restrict s) :=
    hdf_aesm.mono_measure (Measure.restrict_mono hsΩ le_rfl)
  have hj : AEMeasurable j (volume.restrict s) := by
    exact ENNReal.continuous_ofReal.measurable.comp_aemeasurable
      (continuous_weakJacobian.measurable.comp_aemeasurable
        hdf_s.aemeasurable)
  have hf_s : AEStronglyMeasurable (ambientMap F) (volume.restrict s) :=
    ((continuousOn_ambientMap F).mono hsΩ).aestronglyMeasurable hs
  have hf_ν : AEMeasurable (ambientMap F) ν := by
    exact hf_s.aemeasurable.mono'
      (withDensity_absolutelyContinuous (volume.restrict s) j)
  have hmeasure : Measure.map (ambientMap F) ν =
      volume.restrict (ambientMap F '' s) := by
    apply Measure.ext
    intro t ht
    rw [Measure.map_apply_of_aemeasurable hf_ν ht]
    have harea := hF.areaFormula hdf hs hsΩ
      (t.indicator (fun _ ↦ 1))
    rw [lintegral_indicator ht] at harea
    rw [setLIntegral_one] at harea
    have hpre := hf_s.aemeasurable.nullMeasurableSet_preimage ht
    rw [withDensity_apply₀ j hpre, ← lintegral_indicator₀ hpre, harea]
    apply lintegral_congr_ae
    filter_upwards with z
    by_cases hz : ambientMap F z ∈ t
    · simp [j, hz]
    · simp [j, hz]
  have hmap_integral :
      ∫ y, g y ∂Measure.map (ambientMap F) ν =
        ∫ z, g (ambientMap F z) ∂ν :=
    integral_map hf_ν (by simpa [hmeasure] using hg)
  rw [hmeasure] at hmap_integral
  rw [integral_withDensity_eq_integral_toReal_smul₀ hj
    (by filter_upwards with z; exact ENNReal.ofReal_lt_top)] at hmap_integral
  calc
    ∫ y in ambientMap F '' s, g y ∂volume =
        ∫ z in s, (j z).toReal • g (ambientMap F z) ∂volume :=
      hmap_integral
    _ = ∫ z in s,
        weakJacobian (df z) • g (ambientMap F z) ∂volume := by
      apply integral_congr_ae
      have hJ := ae_restrict_of_ae_restrict_of_subset hsΩ
        (hF.weakJacobian_nonneg_ae hdf)
      filter_upwards [hJ] with z hz
      simp [j, ENNReal.toReal_ofReal hz]

/--
%%handwave
name:
  Null image of the zero-Jacobian set
statement:
  Let $F:\Omega\to\Omega'$ be a planar quasiconformal homeomorphism with
  weak differential $Df$. If $s\subseteq\Omega$ is measurable and
  $\operatorname{Jac}f(z)=0$ for almost every $z\in s$, then $F(s)$ has
  planar measure zero.
proof:
  Apply the oriented area formula to $s$ with constant integrand one. Its
  source integral vanishes because the Jacobian vanishes almost everywhere.
-/
theorem IsKQuasiconformalBetween.volume_ambientMap_image_eq_zero_of_weakJacobian_eq_zero_ae
    {K : ℝ} {Ω Ω' : Set ℂ} {F : Ω ≃ₜ Ω'}
    (hF : IsKQuasiconformalBetween K F) {df : ℂ → ℂ →L[ℝ] ℂ}
    (hdf : IsLocalW12On Ω (ambientMap F) df)
    {s : Set ℂ} (hs : MeasurableSet s) (hsΩ : s ⊆ Ω)
    (hzero : ∀ᵐ z ∂volume.restrict s, weakJacobian (df z) = 0) :
    volume (ambientMap F '' s) = 0 := by
  have harea := hF.areaFormula hdf hs hsΩ (fun _ ↦ 1)
  rw [setLIntegral_one] at harea
  rw [harea]
  calc
    ∫⁻ z in s, ENNReal.ofReal (weakJacobian (df z)) * 1 ∂volume =
        ∫⁻ _z in s, 0 ∂volume := by
      apply lintegral_congr_ae
      filter_upwards [hzero] with z hz
      simp [hz]
    _ = 0 := lintegral_zero

/--
%%handwave
name:
  Locally square-integrable inverse differential candidate
statement:
  Let $F:\Omega\to\Omega'$ be a planar $K$-quasiconformal homeomorphism
  with weak differential $Df$. There is a field $G$ of real-linear maps on
  the target such that
  $$G(F(z))=(Df(z))^{\dagger}$$
  for almost every $z\in\Omega$, and $G\in L^2(C)$ for every compact
  $C\subseteq\Omega'$. Moreover,
  $$\|G(y)\|_{\mathrm{op}}^2\le KJ(G(y))$$
  for almost every $y\in\Omega'$.
proof:
  Choose a globally measurable representative of $Df$ on $\Omega$ and set
  $G(y)=(Df(F^{-1}(y)))^{\dagger}$. For compact $C\subseteq\Omega'$, apply
  the oriented area formula on $F^{-1}(C)$. The pointwise estimate
  $\|(Df)^{\dagger}\|^2\operatorname{Jac}f\le K$ bounds the resulting
  integral by $K$ times the finite area of the compact set $F^{-1}(C)$.
-/
theorem IsKQuasiconformalBetween.exists_inverseDifferentialCandidate_memLpOn_compact
    {K : ℝ} {Ω Ω' : Set ℂ} {F : Ω ≃ₜ Ω'}
    (hF : IsKQuasiconformalBetween K F) {df : ℂ → ℂ →L[ℝ] ℂ}
    (hdf : IsLocalW12On Ω (ambientMap F) df) :
    ∃ dg : ℂ → ℂ →L[ℝ] ℂ,
      (∀ᵐ z ∂volume.restrict Ω,
        dg (ambientMap F z) = realLinearPseudoInverse (df z)) ∧
      (∀ C : Set ℂ, IsCompact C → C ⊆ Ω' →
        MemLp dg 2 (volume.restrict C)) ∧
      ∀ᵐ y ∂volume.restrict Ω',
        ‖dg y‖ ^ 2 ≤ K * weakJacobian (dg y) := by
  have hdf_aesm : AEStronglyMeasurable df (volume.restrict Ω) :=
    hdf.differential_locallyIntegrableOn.aestronglyMeasurable
  have hind_aesm : AEStronglyMeasurable (Ω.indicator df) volume :=
    (aestronglyMeasurable_indicator_iff hdf.1.measurableSet).2 hdf_aesm
  let dfm : ℂ → ℂ →L[ℝ] ℂ := hind_aesm.mk (Ω.indicator df)
  let dg : ℂ → ℂ →L[ℝ] ℂ := fun y ↦
    realLinearPseudoInverse (dfm (ambientMap F.symm y))
  have hdfm_eq : ∀ᵐ z ∂volume.restrict Ω, dfm z = df z := by
    filter_upwards [ae_restrict_of_ae hind_aesm.ae_eq_mk,
      ae_restrict_mem hdf.1.measurableSet] with z hz hzΩ
    simpa [dfm, indicator_of_mem hzΩ] using hz.symm
  refine ⟨dg, ?_, ?_, ?_⟩
  · filter_upwards [hdfm_eq, ae_restrict_mem hdf.1.measurableSet] with z hz hzΩ
    simp only [dg]
    rw [ambientMap_symm_apply_ambientMap F ⟨z, hzΩ⟩, hz]
  intro C hC hCΩ'
  let A : Set ℂ := ambientMap F.symm '' C
  have hAcompact : IsCompact A :=
    hC.image_of_continuousOn
      ((continuousOn_ambientMap F.symm).mono hCΩ')
  have hAΩ : A ⊆ Ω := by
    rintro z ⟨y, hyC, rfl⟩
    let yΩ' : Ω' := ⟨y, hCΩ' hyC⟩
    have hy : ambientMap F.symm y = F.symm yΩ' := ambientMap_apply F.symm yΩ'
    rw [hy]
    exact (F.symm yΩ').2
  have himage : ambientMap F '' A = C := by
    apply Subset.antisymm
    · rintro w ⟨z, ⟨y, hyC, rfl⟩, rfl⟩
      let yΩ' : Ω' := ⟨y, hCΩ' hyC⟩
      have hcancel : ambientMap F (ambientMap F.symm y) = y := by
        simpa only [Homeomorph.symm_symm] using
          (ambientMap_symm_apply_ambientMap F.symm yΩ')
      rwa [hcancel]
    · intro y hyC
      let yΩ' : Ω' := ⟨y, hCΩ' hyC⟩
      refine ⟨ambientMap F.symm y, ⟨y, hyC, rfl⟩, ?_⟩
      simpa only [Homeomorph.symm_symm] using
        (ambientMap_symm_apply_ambientMap F.symm yΩ')
  have hinv_aesm : AEStronglyMeasurable (ambientMap F.symm)
      (volume.restrict C) :=
    ((continuousOn_ambientMap F.symm).mono hCΩ').aestronglyMeasurable_of_isCompact
      hC hC.measurableSet
  have hdg_aesm : AEStronglyMeasurable dg (volume.restrict C) := by
    have houter : Measurable (fun z ↦ realLinearPseudoInverse (dfm z)) :=
      measurable_realLinearPseudoInverse.comp
        hind_aesm.stronglyMeasurable_mk.measurable
    exact (houter.comp_aemeasurable hinv_aesm.aemeasurable).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hdg_aesm]
  refine ⟨hdg_aesm.norm.pow 2, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal]
  · let g : ℂ → ℝ≥0∞ := fun y ↦ ENNReal.ofReal (‖dg y‖ ^ 2)
    have harea := hF.areaFormula hdf hAcompact.measurableSet hAΩ g
    rw [himage] at harea
    have hJ_A := ae_restrict_of_ae_restrict_of_subset hAΩ
      (hF.weakJacobian_nonneg_ae hdf)
    have hdist_A := ae_restrict_of_ae_restrict_of_subset hAΩ
      (hF.distortion_of_weakDifferential hdf)
    have hdfm_A := ae_restrict_of_ae_restrict_of_subset hAΩ hdfm_eq
    have hlin_le :
        ∫⁻ y in C, ENNReal.ofReal (‖dg y‖ ^ 2) ∂volume ≤
          ∫⁻ _z in A, ENNReal.ofReal K ∂volume := by
      rw [harea]
      apply lintegral_mono_ae
      filter_upwards [hJ_A, hdist_A, hdfm_A,
        ae_restrict_mem hAcompact.measurableSet] with z hJz hdistz hdfmz hzA
      have hzΩ : z ∈ Ω := hAΩ hzA
      have hdg : dg (ambientMap F z) = realLinearPseudoInverse (df z) := by
        simp only [dg]
        rw [ambientMap_symm_apply_ambientMap F ⟨z, hzΩ⟩, hdfmz]
      change ENNReal.ofReal (weakJacobian (df z)) *
        ENNReal.ofReal (‖dg (ambientMap F z)‖ ^ 2) ≤ ENNReal.ofReal K
      rw [hdg, ← ENNReal.ofReal_mul hJz]
      apply ENNReal.ofReal_le_ofReal
      simpa [mul_comm] using
        norm_sq_realLinearPseudoInverse_mul_weakJacobian_le_of_nonneg
          (df z) hJz K (le_trans (by norm_num) hF.1) hdistz
    refine lt_of_le_of_lt hlin_le ?_
    rw [setLIntegral_const]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (lt_top_iff_ne_top.2 hAcompact.measure_ne_top)
  · filter_upwards with y
    exact sq_nonneg ‖dg y‖
  apply ae_restrict_target_of_ae_restrict_source_of_hasLusinNOn
    (P := fun z ↦ dfm z = df z ∧
      0 ≤ weakJacobian (df z) ∧
        ‖df z‖ ^ 2 ≤ K * weakJacobian (df z))
    (Q := fun y ↦ ‖dg y‖ ^ 2 ≤ K * weakJacobian (dg y))
    F hF.2.1.measurableSet
      (hdf.hasLusinNOn_ambientMap F hdf.1 hF.2.1)
  · filter_upwards [hdfm_eq, hF.weakJacobian_nonneg_ae hdf,
      hF.distortion_of_weakDifferential hdf] with z hdfmz hJz hdistz
    exact ⟨hdfmz, hJz, hdistz⟩
  · intro z hzΩ hz
    rcases hz with ⟨hdfmz, hJz, hdistz⟩
    have hdg : dg (ambientMap F z) = realLinearPseudoInverse (df z) := by
      simp only [dg]
      rw [ambientMap_symm_apply_ambientMap F ⟨z, hzΩ⟩, hdfmz]
    rw [hdg]
    exact distortion_realLinearPseudoInverse_of_nonneg_weakJacobian
      (df z) hJz K hdistz

/--
%%handwave
name:
  Lusin property of a planar quasiconformal homeomorphism
statement:
  Every planar quasiconformal homeomorphism
  $F:\Omega\to\Omega'$ sends null subsets of $\Omega$ to null sets.
proof:
  Apply [the Sobolev area formula](lean:JJMath.Quasiconformal.IsKQuasiconformalBetween.areaFormula_abs) with constant integrand one to a measurable null enlargement of the given set.
-/
theorem IsKQuasiconformalBetween.hasLusinNOn
    {K : ℝ} {Ω Ω' : Set ℂ} {F : Ω ≃ₜ Ω'}
    (hF : IsKQuasiconformalBetween K F) :
    HasLusinNOn Ω (ambientMap F) := by
  obtain ⟨df, hdf, -⟩ := hF.2.2.2
  apply hasLusinNOn_of_areaFormula hdf.1.measurableSet
  intro s hs hsΩ g
  exact hF.areaFormula_abs hdf hs hsΩ g

/--
%%handwave
name:
  Vanishing of bounded $L^2$ pairings
statement:
  Let $a_n:X\to\mathbb R$ and $b_n:X\to E$ be square-integrable functions
  on a measure space, where $E$ is a real normed vector space. If
  $\lVert a_n\rVert_{L^2}\to0$ and there is a finite constant $C$ such that
  $\lVert b_n\rVert_{L^2}\le C$ for every $n$, then
  $$
    \int_X a_n(x)b_n(x)\,d\mu(x)\longrightarrow0
  $$
  in $E$.
proof:
  Hölder's inequality bounds the $L^1$ norm of the product by
  $\lVert a_n\rVert_{L^2}\lVert b_n\rVert_{L^2}$, which tends to zero by the
  uniform bound. Continuity of the Bochner integral with respect to the
  $L^1$ seminorm gives the conclusion.
-/
theorem integral_smul_tendsto_zero_of_L2_tendsto_zero_of_L2_bounded
    {α E : Type} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} {a : ℕ → α → ℝ} {b : ℕ → α → E}
    (ha : ∀ n, MemLp (a n) 2 μ) (hb : ∀ n, MemLp (b n) 2 μ)
    (ha_zero : Filter.Tendsto (fun n => eLpNorm (a n) 2 μ)
      Filter.atTop (𝓝 0))
    (hb_bounded : ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ n, eLpNorm (b n) 2 μ ≤ C) :
    Filter.Tendsto (fun n => ∫ x, a n x • b n x ∂μ)
      Filter.atTop (𝓝 0) := by
  obtain ⟨C, hCtop, hC⟩ := hb_bounded
  have hprod_int : ∀ n, Integrable (fun x => a n x • b n x) μ := by
    intro n
    apply memLp_one_iff_integrable.mp
    exact (hb n).smul (ha n)
  have hholder : ∀ n,
      eLpNorm (fun x => a n x • b n x) 1 μ ≤
        eLpNorm (a n) 2 μ * eLpNorm (b n) 2 μ := by
    intro n
    exact eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1)
      (hb n).aestronglyMeasurable (ha n).aestronglyMeasurable
  have hprod_zero : Filter.Tendsto
      (fun n => eLpNorm (fun x => a n x • b n x) 1 μ)
      Filter.atTop (𝓝 0) := by
    have hupper : Filter.Tendsto (fun n => eLpNorm (a n) 2 μ * C)
        Filter.atTop (𝓝 0) := by
      have hmul := ENNReal.Tendsto.mul_const ha_zero (Or.inr hCtop)
      simpa using hmul
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
      (fun _ => zero_le)
      (fun n => (hholder n).trans (mul_le_mul_right (hC n) _))
  have ht := tendsto_integral_of_L1' (μ := μ)
    (F := fun n x => a n x • b n x) (l := Filter.atTop)
    (f := fun _ : α => (0 : E))
    aestronglyMeasurable_zero (Filter.Eventually.of_forall hprod_int)
    (by
      convert hprod_zero using 1
      funext n
      congr 1
      funext x
      simp)
  simpa using ht

/--
%%handwave
name:
  Vanishing of pairings with a strongly convergent vector factor
statement:
  Let $a_n:X\to\mathbb R$ and $b_n:X\to E$ be square-integrable functions.
  If the sequence $a_n$ is bounded in $L^2$ and
  $\|b_n\|_{L^2}\to0$, then
  $$
    \int_X a_n(x)b_n(x)\,d\mu(x)\longrightarrow0
  $$
  in $E$.
proof:
  Hölder's inequality bounds the $L^1$ norm of the product by
  $\|a_n\|_{L^2}\|b_n\|_{L^2}$. The first factor is uniformly bounded
  and the second tends to zero, so continuity of the Bochner integral in the
  $L^1$ seminorm gives the conclusion.
-/
theorem integral_smul_tendsto_zero_of_L2_bounded_of_L2_tendsto_zero
    {α E : Type} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} {a : ℕ → α → ℝ} {b : ℕ → α → E}
    (ha : ∀ n, MemLp (a n) 2 μ) (hb : ∀ n, MemLp (b n) 2 μ)
    (ha_bounded : ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ n, eLpNorm (a n) 2 μ ≤ C)
    (hb_zero : Filter.Tendsto (fun n => eLpNorm (b n) 2 μ)
      Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun n => ∫ x, a n x • b n x ∂μ)
      Filter.atTop (𝓝 0) := by
  obtain ⟨C, hCtop, hC⟩ := ha_bounded
  have hprod_int : ∀ n, Integrable (fun x => a n x • b n x) μ := by
    intro n
    apply memLp_one_iff_integrable.mp
    exact (hb n).smul (ha n)
  have hholder : ∀ n,
      eLpNorm (fun x => a n x • b n x) 1 μ ≤
        eLpNorm (a n) 2 μ * eLpNorm (b n) 2 μ := by
    intro n
    exact eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1)
      (hb n).aestronglyMeasurable (ha n).aestronglyMeasurable
  have hprod_zero : Filter.Tendsto
      (fun n => eLpNorm (fun x => a n x • b n x) 1 μ)
      Filter.atTop (𝓝 0) := by
    have hupper : Filter.Tendsto (fun n => C * eLpNorm (b n) 2 μ)
        Filter.atTop (𝓝 0) := by
      have hmul := ENNReal.Tendsto.const_mul hb_zero (Or.inr hCtop)
      simpa using hmul
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
      (fun _ => zero_le)
      (fun n => (hholder n).trans (mul_left_mono (a := eLpNorm (b n) 2 μ) (hC n)))
  have ht := tendsto_integral_of_L1' (μ := μ)
    (F := fun n x => a n x • b n x) (l := Filter.atTop)
    (f := fun _ : α => (0 : E))
    aestronglyMeasurable_zero (Filter.Eventually.of_forall hprod_int)
    (by
      convert hprod_zero using 1
      funext n
      congr 1
      funext x
      simp)
  simpa using ht

/--
%%handwave
name:
  Vanishing of two strongly convergent $L^2$ pairings
statement:
  Let $a_n:X\to\mathbb R$ and $b_n:X\to E$ be square-integrable. If
  $\|a_n\|_{L^2}\to0$ and $\|b_n\|_{L^2}\to0$, then
  $$
    \int_X a_n(x)b_n(x)\,d\mu(x)\longrightarrow0
  $$
  in $E$.
proof:
  Hölder's inequality bounds the $L^1$ norm of the product by
  $\|a_n\|_{L^2}\|b_n\|_{L^2}$. Both factors tend to zero, and continuity of
  the Bochner integral with respect to the $L^1$ seminorm gives the result.
-/
theorem integral_smul_tendsto_zero_of_L2_tendsto_zero
    {α E : Type} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} {a : ℕ → α → ℝ} {b : ℕ → α → E}
    (ha : ∀ n, MemLp (a n) 2 μ) (hb : ∀ n, MemLp (b n) 2 μ)
    (ha_zero : Filter.Tendsto (fun n => eLpNorm (a n) 2 μ)
      Filter.atTop (𝓝 0))
    (hb_zero : Filter.Tendsto (fun n => eLpNorm (b n) 2 μ)
      Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun n => ∫ x, a n x • b n x ∂μ)
      Filter.atTop (𝓝 0) := by
  have hprod_int : ∀ n, Integrable (fun x => a n x • b n x) μ := by
    intro n
    apply memLp_one_iff_integrable.mp
    exact (hb n).smul (ha n)
  have hholder : ∀ n,
      eLpNorm (fun x => a n x • b n x) 1 μ ≤
        eLpNorm (a n) 2 μ * eLpNorm (b n) 2 μ := by
    intro n
    exact eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1)
      (hb n).aestronglyMeasurable (ha n).aestronglyMeasurable
  have hupper : Filter.Tendsto
      (fun n => eLpNorm (a n) 2 μ * eLpNorm (b n) 2 μ)
      Filter.atTop (𝓝 0) := by
    have hmul := ENNReal.Tendsto.mul ha_zero (Or.inr ENNReal.zero_ne_top)
      hb_zero (Or.inr ENNReal.zero_ne_top)
    simpa using hmul
  have hprod_zero : Filter.Tendsto
      (fun n => eLpNorm (fun x => a n x • b n x) 1 μ)
      Filter.atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
      (fun _ => zero_le) hholder
  have ht := tendsto_integral_of_L1' (μ := μ)
    (F := fun n x => a n x • b n x) (l := Filter.atTop)
    (f := fun _ : α => (0 : E))
    aestronglyMeasurable_zero (Filter.Eventually.of_forall hprod_int)
    (by
      convert hprod_zero using 1
      funext n
      congr 1
      funext x
      simp)
  simpa using ht

/--
%%handwave
name:
  Strong $L^2$ convergence under two-component linear reconstruction
statement:
  Let $a_n:X\to E$ and $b_n:X\to F$ converge strongly to zero in $L^2$,
  and let $L:E\to G$ and $M:F\to G$ be continuous real-linear maps. Then
  every function $x\mapsto L(a_n(x))+M(b_n(x))$ belongs to $L^2(X,G)$ and
  $$
    \bigl\|L\circ a_n+M\circ b_n\bigr\|_{L^2}\longrightarrow0.
  $$
proof:
  The triangle inequality and the operator-norm bounds for $L$ and $M$ give
  $$
    \|L\circ a_n+M\circ b_n\|_{L^2}
      \leq \|L\|\|a_n\|_{L^2}+\|M\|\|b_n\|_{L^2}.
  $$
  Both terms on the right tend to zero.
-/
theorem continuousLinearMap_pair_sum_memLp_and_tendsto_zero
    {α E F G : Type} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {μ : Measure α} (L : E →L[ℝ] G) (M : F →L[ℝ] G)
    {a : ℕ → α → E} {b : ℕ → α → F}
    (ha : ∀ n, MemLp (a n) 2 μ) (hb : ∀ n, MemLp (b n) 2 μ)
    (ha_zero : Filter.Tendsto (fun n => eLpNorm (a n) 2 μ)
      Filter.atTop (𝓝 0))
    (hb_zero : Filter.Tendsto (fun n => eLpNorm (b n) 2 μ)
      Filter.atTop (𝓝 0)) :
    (∀ n, MemLp (fun x => L (a n x) + M (b n x)) 2 μ) ∧
      Filter.Tendsto
        (fun n => eLpNorm (fun x => L (a n x) + M (b n x)) 2 μ)
        Filter.atTop (𝓝 0) := by
  have hmem : ∀ n, MemLp (fun x => L (a n x) + M (b n x)) 2 μ := by
    intro n
    exact (L.comp_memLp' (ha n)).add (M.comp_memLp' (hb n))
  refine ⟨hmem, ?_⟩
  have hbound : ∀ n,
      eLpNorm (fun x => L (a n x) + M (b n x)) 2 μ ≤
        ENNReal.ofReal ‖L‖ * eLpNorm (a n) 2 μ +
          ENNReal.ofReal ‖M‖ * eLpNorm (b n) 2 μ := by
    intro n
    have hLa : MemLp (fun x => L (a n x)) 2 μ := L.comp_memLp' (ha n)
    have hMb : MemLp (fun x => M (b n x)) 2 μ := M.comp_memLp' (hb n)
    calc
      eLpNorm (fun x => L (a n x) + M (b n x)) 2 μ ≤
          eLpNorm (fun x => L (a n x)) 2 μ +
            eLpNorm (fun x => M (b n x)) 2 μ := by
        exact eLpNorm_add_le (μ := μ) (p := 2)
          hLa.aestronglyMeasurable hMb.aestronglyMeasurable (by norm_num)
      _ ≤ ENNReal.ofReal ‖L‖ * eLpNorm (a n) 2 μ +
          ENNReal.ofReal ‖M‖ * eLpNorm (b n) 2 μ := by
        apply add_le_add
        · exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul
            (μ := μ) (f := fun x => L (a n x)) (g := a n) (c := ‖L‖)
            (Filter.Eventually.of_forall fun x => L.le_opNorm _) 2
        · exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul
            (μ := μ) (f := fun x => M (b n x)) (g := b n) (c := ‖M‖)
            (Filter.Eventually.of_forall fun x => M.le_opNorm _) 2
  have hLzero : Filter.Tendsto
      (fun n => ENNReal.ofReal ‖L‖ * eLpNorm (a n) 2 μ)
      Filter.atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul ha_zero
      (Or.inr (ENNReal.ofReal_ne_top : ENNReal.ofReal ‖L‖ ≠ ∞))
  have hMzero : Filter.Tendsto
      (fun n => ENNReal.ofReal ‖M‖ * eLpNorm (b n) 2 μ)
      Filter.atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hb_zero
      (Or.inr (ENNReal.ofReal_ne_top : ENNReal.ofReal ‖M‖ ≠ ∞))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using hLzero.add hMzero) (fun _ => zero_le) hbound

/--
%%handwave
name:
  Strong $L^2$ convergence under a uniform pointwise linear bound
statement:
  Let $a_n:X\to E$ converge strongly to zero in $L^2$, and let
  $b_n:X\to F$ be almost everywhere strongly measurable. If one constant
  $C$ satisfies $\|b_n(x)\|\leq C\|a_n(x)\|$ for every $n$ and almost every
  $x$, then every $b_n$ belongs to $L^2$ and
  $\|b_n\|_{L^2}\to0$.
proof:
  Monotonicity of the $L^2$ seminorm gives
  $\|b_n\|_{L^2}\leq C\|a_n\|_{L^2}$, and the right-hand side tends to zero.
-/
theorem memLp_and_tendsto_zero_of_norm_le_mul
    {α E F : Type} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    {μ : Measure α} {a : ℕ → α → E} {b : ℕ → α → F} {C : ℝ}
    (ha : ∀ n, MemLp (a n) 2 μ)
    (hb_meas : ∀ n, AEStronglyMeasurable (b n) μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖b n x‖ ≤ C * ‖a n x‖)
    (ha_zero : Filter.Tendsto (fun n => eLpNorm (a n) 2 μ)
      Filter.atTop (𝓝 0)) :
    (∀ n, MemLp (b n) 2 μ) ∧
      Filter.Tendsto (fun n => eLpNorm (b n) 2 μ)
        Filter.atTop (𝓝 0) := by
  have hb : ∀ n, MemLp (b n) 2 μ := by
    intro n
    exact (ha n).of_le_mul (hb_meas n) (hbound n)
  refine ⟨hb, ?_⟩
  have hnorm : ∀ n,
      eLpNorm (b n) 2 μ ≤ ENNReal.ofReal C * eLpNorm (a n) 2 μ := by
    intro n
    exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul (hbound n) 2
  have hupper : Filter.Tendsto
      (fun n => ENNReal.ofReal C * eLpNorm (a n) 2 μ)
      Filter.atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul ha_zero
      (Or.inr (ENNReal.ofReal_ne_top : ENNReal.ofReal C ≠ ∞))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun _ => zero_le) hnorm

/--
%%handwave
name:
  Strong $L^2$ convergence under Lipschitz composition
statement:
  Let $u_n,f:X\to E$ be almost everywhere strongly measurable and let
  $g:E\to F$ be $K$-Lipschitz. If $u_n-f$ belongs to $L^2$ for every $n$ and
  $\|u_n-f\|_{L^2}\to0$, then $g\circ u_n-g\circ f$ belongs to $L^2$ and
  $$
    \|g\circ u_n-g\circ f\|_{L^2}\longrightarrow0.
  $$
proof:
  The Lipschitz inequality gives the pointwise estimate
  $\|g(u_n(x))-g(f(x))\|\leq K\|u_n(x)-f(x)\|$. Apply monotonicity of the
  $L^2$ seminorm and pass to the limit.
-/
theorem lipschitz_comp_sub_memLp_and_tendsto_zero
    {α E F : Type} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    {μ : Measure α} {K : NNReal} {g : E → F}
    (hg : LipschitzWith K g) {u : ℕ → α → E} {f : α → E}
    (hu_meas : ∀ n, AEStronglyMeasurable (u n) μ)
    (hf_meas : AEStronglyMeasurable f μ)
    (herror_mem : ∀ n, MemLp (fun x => u n x - f x) 2 μ)
    (herror_zero : Filter.Tendsto
      (fun n => eLpNorm (fun x => u n x - f x) 2 μ)
      Filter.atTop (𝓝 0)) :
    (∀ n, MemLp (fun x => g (u n x) - g (f x)) 2 μ) ∧
      Filter.Tendsto
        (fun n => eLpNorm (fun x => g (u n x) - g (f x)) 2 μ)
        Filter.atTop (𝓝 0) := by
  have hpoint : ∀ n, ∀ x,
      ‖g (u n x) - g (f x)‖ ≤ (K : ℝ) * ‖u n x - f x‖ := by
    intro n x
    simpa [dist_eq_norm] using hg.norm_sub_le (u n x) (f x)
  have hmem : ∀ n, MemLp (fun x => g (u n x) - g (f x)) 2 μ := by
    intro n
    apply (herror_mem n).of_le_mul
    · exact (hg.continuous.comp_aestronglyMeasurable (hu_meas n)).sub
        (hg.continuous.comp_aestronglyMeasurable hf_meas)
    · exact Filter.Eventually.of_forall (hpoint n)
  refine ⟨hmem, ?_⟩
  have hbound : ∀ n,
      eLpNorm (fun x => g (u n x) - g (f x)) 2 μ ≤
        ENNReal.ofReal (K : ℝ) *
          eLpNorm (fun x => u n x - f x) 2 μ := by
    intro n
    exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul
      (Filter.Eventually.of_forall (hpoint n)) 2
  have hupper : Filter.Tendsto
      (fun n => ENNReal.ofReal (K : ℝ) *
        eLpNorm (fun x => u n x - f x) 2 μ)
      Filter.atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul herror_zero
      (Or.inr (ENNReal.ofReal_ne_top : ENNReal.ofReal (K : ℝ) ≠ ∞))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun _ => zero_le) hbound

/-- Smooth complex-valued graph-norm approximation data on a planar set. -/
structure PlanarWeakSobolevSmoothApproxGraphL2Data
    (Q : Set ℂ) (f : ℂ → ℂ) (df : ℂ → ℂ →L[ℝ] ℂ) where
  approximants : ℕ → ℂ → ℂ
  smooth : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (approximants n)
  value_error_memLp : ∀ n,
    MemLp (fun z => approximants n z - f z) 2 (volume.restrict Q)
  value_tendsto_l2 : Filter.Tendsto
    (fun n => eLpNorm (fun z => approximants n z - f z) 2
      (volume.restrict Q)) Filter.atTop (𝓝 0)
  derivative_error_memLp : ∀ n,
    MemLp (fun z => fderiv ℝ (approximants n) z - df z) 2
      (volume.restrict Q)
  derivative_tendsto_l2 : Filter.Tendsto
    (fun n => eLpNorm (fun z => fderiv ℝ (approximants n) z - df z) 2
      (volume.restrict Q)) Filter.atTop (𝓝 0)

/--
%%handwave
name:
  Almost-everywhere convergent subsequence of a planar graph approximation
statement:
  Let $Q\subset\mathbb C$, and suppose smooth maps
  $T_n:\mathbb C\to\mathbb C$ converge strongly to a measurable map
  $f:Q\to\mathbb C$ in $L^2(Q)$. Then there is a strictly increasing
  sequence $n_k$ such that $T_{n_k}(z)\to f(z)$ for almost every $z\in Q$.
proof:
  Strong $L^2$ convergence implies convergence in measure. Every sequence
  converging in measure has a subsequence converging almost everywhere.
-/
theorem PlanarWeakSobolevSmoothApproxGraphL2Data.exists_strictMono_approximants_tendsto_ae
    {Q : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (hgraph : PlanarWeakSobolevSmoothApproxGraphL2Data Q f df)
    (hf : AEStronglyMeasurable f (volume.restrict Q)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ z ∂volume.restrict Q,
        Filter.Tendsto (fun n => hgraph.approximants (ns n) z)
          Filter.atTop (𝓝 (f z)) := by
  apply TendstoInMeasure.exists_seq_tendsto_ae
  apply tendstoInMeasure_of_tendsto_eLpNorm (p := 2)
  · norm_num
  · exact fun n => (hgraph.smooth n).continuous.aestronglyMeasurable
  · exact hf
  · simpa only [Pi.sub_apply] using hgraph.value_tendsto_l2

/--
%%handwave
name:
  Smooth planar graph approximation with uniform convergence for continuous data
statement:
  Let $f\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb C)$ have weak differential
  $Df$. Suppose $Q$ and $P$ are compact subsets of the open set $\Omega$ and
  some closed positive-radius neighborhood of $Q$ is contained in $P$. Then
  there are smooth maps $T_n:\mathbb C\to\mathbb C$ such that
  $$
    \|T_n-f\|_{L^2(Q)}\longrightarrow0,
    \qquad
    \|DT_n-Df\|_{L^2(Q)}\longrightarrow0.
  $$
  The same sequence converges uniformly on $Q$ whenever $f$ is continuous.
proof:
  Apply scalar smooth graph-density separately to the real and imaginary
  parts of $f$. Recombine the two approximation sequences using the standard
  real and imaginary coordinate embeddings into $\mathbb C$. The weak
  differentials recombine to $Df$, and [strong $L^2$ convergence is preserved by this two-component linear reconstruction](lean:JJMath.Quasiconformal.continuousLinearMap_pair_sum_memLp_and_tendsto_zero).
-/
theorem IsLocalW12On.exists_smoothApproxGraphL2Data_on_compact_with_uniform_if_continuous
    {Ω : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (hdf : IsLocalW12On Ω f df) {Q P : Set ℂ}
    (hQ : IsCompact Q) (hP : IsCompact P)
    (hQP : ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ Q ⊆ P)
    (hPΩ : P ⊆ Ω) :
    ∃ hgraph : PlanarWeakSobolevSmoothApproxGraphL2Data Q f df,
      Continuous f →
        TendstoUniformlyOn hgraph.approximants f Filter.atTop Q := by
  let dRe : ℂ → ℂ →L[ℝ] ℝ := fun z => Complex.reCLM.comp (df z)
  let dIm : ℂ → ℂ →L[ℝ] ℝ := fun z => Complex.imCLM.comp (df z)
  let postRe : (ℂ →L[ℝ] ℂ) →L[ℝ] (ℂ →L[ℝ] ℝ) :=
    (isBoundedBilinearMap_comp
      (𝕜 := ℝ) (E := ℂ) (F := ℂ) (G := ℝ)).toContinuousLinearMap
        Complex.reCLM
  let postIm : (ℂ →L[ℝ] ℂ) →L[ℝ] (ℂ →L[ℝ] ℝ) :=
    (isBoundedBilinearMap_comp
      (𝕜 := ℝ) (E := ℂ) (F := ℂ) (G := ℝ)).toContinuousLinearMap
        Complex.imCLM
  have hweakRe := weakDerivative_postcomp_continuousLinearMap
    Complex.reCLM hdf.2.1
  have hweakIm := weakDerivative_postcomp_continuousLinearMap
    Complex.imCLM hdf.2.1
  have hfP := (hdf.2.2 P hP hPΩ).1
  have hdfP := (hdf.2.2 P hP hPΩ).2
  have hfRe : MemLp (fun z => (f z).re) 2 (volume.restrict P) := by
    simpa only [Complex.reCLM_apply] using Complex.reCLM.comp_memLp' hfP
  have hfIm : MemLp (fun z => (f z).im) 2 (volume.restrict P) := by
    simpa only [Complex.imCLM_apply] using Complex.imCLM.comp_memLp' hfP
  have hdRe : MemLp dRe 2 (volume.restrict P) := by
    simpa [dRe, postRe, Function.comp_def] using postRe.comp_memLp' hdfP
  have hdIm : MemLp dIm 2 (volume.restrict P) := by
    simpa [dIm, postIm, Function.comp_def] using postIm.comp_memLp' hdfP
  rcases
      JJMath.Uniformization.euclideanSobolev_smooth_graph_density_l2_on_compact_with_uniform_if_continuous
        hQ hP hQP hPΩ hdf.1 hweakRe hfRe hdRe with
    ⟨hRe, hReUniform⟩
  rcases
      JJMath.Uniformization.euclideanSobolev_smooth_graph_density_l2_on_compact_with_uniform_if_continuous
        hQ hP hQP hPΩ hdf.1 hweakIm hfIm hdIm with
    ⟨hIm, hImUniform⟩
  let imOfReal : ℝ →L[ℝ] ℂ :=
    (realLinearMapOfWirtinger Complex.I 0).comp Complex.ofRealCLM
  let embedRe : (ℂ →L[ℝ] ℝ) →L[ℝ] (ℂ →L[ℝ] ℂ) :=
    (isBoundedBilinearMap_comp
      (𝕜 := ℝ) (E := ℂ) (F := ℝ) (G := ℂ)).toContinuousLinearMap
        Complex.ofRealCLM
  let embedIm : (ℂ →L[ℝ] ℝ) →L[ℝ] (ℂ →L[ℝ] ℂ) :=
    (isBoundedBilinearMap_comp
      (𝕜 := ℝ) (E := ℂ) (F := ℝ) (G := ℂ)).toContinuousLinearMap
        imOfReal
  let T : ℕ → ℂ → ℂ := fun n z =>
    Complex.ofReal (hRe.approximants n z) + imOfReal (hIm.approximants n z)
  have hT_smooth : ∀ n,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (T n) := by
    intro n
    exact (Complex.ofRealCLM.contDiff.comp (hRe.smooth n)).add
      (imOfReal.contDiff.comp (hIm.smooth n))
  let valueRe : ℕ → ℂ → ℝ := fun n z =>
    hRe.approximants n z - (f z).re
  let valueIm : ℕ → ℂ → ℝ := fun n z =>
    hIm.approximants n z - (f z).im
  have hvalue_error_eq : ∀ n,
      (fun z => T n z - f z) =
        fun z => Complex.ofReal (valueRe n z) + imOfReal (valueIm n z) := by
    intro n
    funext z
    apply Complex.ext <;>
      simp [T, valueRe, valueIm, imOfReal, realLinearMapOfWirtinger]
  have hvalue_pair :=
    continuousLinearMap_pair_sum_memLp_and_tendsto_zero
      Complex.ofRealCLM imOfReal
      (fun n => by simpa [valueRe] using hRe.value_error_memLp n)
      (fun n => by simpa [valueIm] using hIm.value_error_memLp n)
      (by simpa [valueRe] using hRe.value_tendsto_l2)
      (by simpa [valueIm] using hIm.value_tendsto_l2)
  have hvalue_mem : ∀ n,
      MemLp (fun z => T n z - f z) 2 (volume.restrict Q) := by
    intro n
    rw [hvalue_error_eq n]
    exact hvalue_pair.1 n
  have hvalue_zero : Filter.Tendsto
      (fun n => eLpNorm (fun z => T n z - f z) 2 (volume.restrict Q))
      Filter.atTop (𝓝 0) := by
    have heq : (fun n => eLpNorm (fun z => T n z - f z) 2
        (volume.restrict Q)) =
        fun n => eLpNorm
          (fun z => Complex.ofRealCLM (valueRe n z) + imOfReal (valueIm n z))
            2 (volume.restrict Q) := by
      funext n
      rw [hvalue_error_eq n]
      simp only [Complex.ofRealCLM_apply]
    rw [heq]
    exact hvalue_pair.2
  let derivRe : ℕ → ℂ → ℂ →L[ℝ] ℝ := fun n z =>
    fderiv ℝ (hRe.approximants n) z - dRe z
  let derivIm : ℕ → ℂ → ℂ →L[ℝ] ℝ := fun n z =>
    fderiv ℝ (hIm.approximants n) z - dIm z
  have hfderiv_T : ∀ n z,
      fderiv ℝ (T n) z =
        embedRe (fderiv ℝ (hRe.approximants n) z) +
          embedIm (fderiv ℝ (hIm.approximants n) z) := by
    intro n z
    have hReDiff : DifferentiableAt ℝ (hRe.approximants n) z :=
      (hRe.smooth n).differentiable (by simp) z
    have hImDiff : DifferentiableAt ℝ (hIm.approximants n) z :=
      (hIm.smooth n).differentiable (by simp) z
    have hReCompDiff : DifferentiableAt ℝ
        (fun w => Complex.ofRealCLM (hRe.approximants n w)) z :=
      Complex.ofRealCLM.differentiableAt.comp z hReDiff
    have hImCompDiff : DifferentiableAt ℝ
        (fun w => imOfReal (hIm.approximants n w)) z :=
      imOfReal.differentiableAt.comp z hImDiff
    have hReDeriv :
        fderiv ℝ (fun w => Complex.ofRealCLM (hRe.approximants n w)) z =
          Complex.ofRealCLM.comp (fderiv ℝ (hRe.approximants n) z) := by
      simpa [Function.comp_def] using
        fderiv_comp z Complex.ofRealCLM.differentiableAt hReDiff
    have hImDeriv :
        fderiv ℝ (fun w => imOfReal (hIm.approximants n w)) z =
          imOfReal.comp (fderiv ℝ (hIm.approximants n) z) := by
      simpa [Function.comp_def] using
        fderiv_comp z imOfReal.differentiableAt hImDiff
    change fderiv ℝ
      ((fun w => Complex.ofRealCLM (hRe.approximants n w)) +
        fun w => imOfReal (hIm.approximants n w)) z = _
    rw [fderiv_add hReCompDiff hImCompDiff, hReDeriv, hImDeriv]
    rfl
  have hdf_decomp : ∀ z,
      df z = embedRe (dRe z) + embedIm (dIm z) := by
    intro z
    ext w
    apply Complex.ext <;>
      simp [embedRe, embedIm, dRe, dIm, imOfReal,
        realLinearMapOfWirtinger]
  have hderiv_error_eq : ∀ n,
      (fun z => fderiv ℝ (T n) z - df z) =
        fun z => embedRe (derivRe n z) + embedIm (derivIm n z) := by
    intro n
    funext z
    rw [hfderiv_T n z, hdf_decomp z]
    simp only [derivRe, derivIm, map_sub]
    abel
  have hderiv_pair :=
    continuousLinearMap_pair_sum_memLp_and_tendsto_zero
      embedRe embedIm
      (fun n => by
        simpa [derivRe, dRe] using hRe.derivative_error_memLp n)
      (fun n => by
        simpa [derivIm, dIm] using hIm.derivative_error_memLp n)
      (by simpa [derivRe, dRe] using hRe.derivative_tendsto_l2)
      (by simpa [derivIm, dIm] using hIm.derivative_tendsto_l2)
  have hderiv_mem : ∀ n,
      MemLp (fun z => fderiv ℝ (T n) z - df z) 2
        (volume.restrict Q) := by
    intro n
    rw [hderiv_error_eq n]
    exact hderiv_pair.1 n
  have hderiv_zero : Filter.Tendsto
      (fun n => eLpNorm (fun z => fderiv ℝ (T n) z - df z) 2
        (volume.restrict Q)) Filter.atTop (𝓝 0) := by
    have heq : (fun n => eLpNorm (fun z => fderiv ℝ (T n) z - df z) 2
        (volume.restrict Q)) =
        fun n => eLpNorm
          (fun z => embedRe (derivRe n z) + embedIm (derivIm n z)) 2
            (volume.restrict Q) := by
      funext n
      rw [hderiv_error_eq n]
    rw [heq]
    exact hderiv_pair.2
  refine ⟨{
    approximants := T
    smooth := hT_smooth
    value_error_memLp := hvalue_mem
    value_tendsto_l2 := hvalue_zero
    derivative_error_memLp := hderiv_mem
    derivative_tendsto_l2 := hderiv_zero }, ?_⟩
  intro hf_cont
  have hRe_cont : Continuous (fun z ↦ (f z).re) :=
    Complex.reCLM.continuous.comp hf_cont
  have hIm_cont : Continuous (fun z ↦ (f z).im) :=
    Complex.imCLM.continuous.comp hf_cont
  have hRe_tendsto :=
    hReUniform hRe_cont
  have hIm_tendsto :=
    hImUniform hIm_cont
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hεhalf : 0 < ε / 2 :=
    half_pos hε
  have hRe_eventually :=
    (Metric.tendstoUniformlyOn_iff.mp hRe_tendsto)
      (ε / 2) hεhalf
  have hIm_eventually :=
    (Metric.tendstoUniformlyOn_iff.mp hIm_tendsto)
      (ε / 2) hεhalf
  filter_upwards [hRe_eventually, hIm_eventually] with n hnRe hnIm x hxQ
  have hnRe' : |valueRe n x| < ε / 2 := by
    simpa [valueRe, Real.dist_eq, abs_sub_comm] using hnRe x hxQ
  have hnIm' : |valueIm n x| < ε / 2 := by
    simpa [valueIm, Real.dist_eq, abs_sub_comm] using hnIm x hxQ
  rw [dist_comm, Complex.dist_eq]
  rw [show T n x - f x =
      Complex.ofReal (valueRe n x) + imOfReal (valueIm n x) by
    exact congrFun (hvalue_error_eq n) x]
  exact
    (Complex.norm_le_abs_re_add_abs_im
      (Complex.ofReal (valueRe n x) + imOfReal (valueIm n x))).trans_lt
      (by
        simpa [imOfReal, realLinearMapOfWirtinger] using
          add_lt_add hnRe' hnIm')

/--
%%handwave
name:
  Smooth planar Sobolev graph approximation on a compact set
statement:
  Let $f\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb C)$ have weak differential
  $Df$. If compact sets $Q\Subset P\subset\Omega$, then there are smooth maps
  $T_n:\mathbb C\to\mathbb C$ such that
  $$
    \|T_n-f\|_{L^2(Q)}\longrightarrow0,
    \qquad
    \|DT_n-Df\|_{L^2(Q)}\longrightarrow0.
  $$
proof:
  Use [the componentwise localized mollifier sequence which also converges uniformly for continuous maps](lean:JJMath.Quasiconformal.IsLocalW12On.exists_smoothApproxGraphL2Data_on_compact_with_uniform_if_continuous) and retain its Sobolev graph-convergence data.
-/
theorem IsLocalW12On.exists_smoothApproxGraphL2Data_on_compact
    {Ω : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (hdf : IsLocalW12On Ω f df) {Q P : Set ℂ}
    (hQ : IsCompact Q) (hP : IsCompact P)
    (hQP : ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ Q ⊆ P)
    (hPΩ : P ⊆ Ω) :
    Nonempty (PlanarWeakSobolevSmoothApproxGraphL2Data Q f df) := by
  obtain ⟨hgraph, _⟩ :=
    IsLocalW12On.exists_smoothApproxGraphL2Data_on_compact_with_uniform_if_continuous
      hdf hQ hP hQP hPΩ
  exact ⟨hgraph⟩

/--
%%handwave
name:
  Simultaneous compact-uniform and Sobolev graph approximation
statement:
  Let $f:\Omega\to\mathbb C$ be continuous and locally $W^{1,2}$ with weak
  differential $Df$. If compact sets $Q\Subset P\subset\Omega$, then there
  are smooth maps $T_n:\mathbb C\to\mathbb C$ such that
  $$
    T_n\longrightarrow f\quad\hbox{uniformly on }Q,
    \qquad
    \|T_n-f\|_{L^2(Q)}+\|DT_n-Df\|_{L^2(Q)}
      \longrightarrow0.
  $$
proof:
  Localize $f$ by a smooth cutoff which is one on a neighborhood of $Q$,
  then convolve with a standard approximate identity. Continuity gives
  uniform convergence of the mollifications on $Q$, while the standard
  Sobolev mollification theorem gives convergence in the $W^{1,2}$ graph
  norm.
-/
theorem IsLocalW12On.exists_smoothApproxGraphL2Data_on_compact_tendstoUniformlyOn
    {Ω : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (hdf : IsLocalW12On Ω f df) (hf : Continuous f)
    {Q P : Set ℂ}
    (hQ : IsCompact Q) (hP : IsCompact P)
    (hQP : ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ Q ⊆ P)
    (hPΩ : P ⊆ Ω) :
    ∃ hgraph : PlanarWeakSobolevSmoothApproxGraphL2Data Q f df,
      TendstoUniformlyOn hgraph.approximants f Filter.atTop Q := by
  obtain ⟨hgraph, huniform⟩ :=
    IsLocalW12On.exists_smoothApproxGraphL2Data_on_compact_with_uniform_if_continuous
      hdf hQ hP hQP hPΩ
  exact ⟨hgraph, huniform hf⟩

/--
%%handwave
name:
  Test-function convergence along planar graph approximants
statement:
  Let $T_n:\mathbb C\to\mathbb C$ converge to $f$ in $L^2(Q)$ as part of a
  smooth planar Sobolev graph approximation, and assume $f$ is almost
  everywhere strongly measurable on $Q$. For every smooth compactly
  supported real function $\varphi$ on a planar region,
  $$
    \|\varphi\circ T_n-\varphi\circ f\|_{L^2(Q)}\longrightarrow0.
  $$
proof:
  A smooth function with compact support is globally Lipschitz. Apply
  [strong $L^2$ convergence under Lipschitz composition](lean:JJMath.Quasiconformal.lipschitz_comp_sub_memLp_and_tendsto_zero) to the value part of the graph approximation.
-/
theorem PlanarWeakSobolevSmoothApproxGraphL2Data.testFunction_comp_sub_tendsto_l2
    {Q : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (hgraph : PlanarWeakSobolevSmoothApproxGraphL2Data Q f df)
    (hf_meas : AEStronglyMeasurable f (volume.restrict Q))
    {Ω' : Set ℂ}
    (φ : JJMath.Uniformization.SmoothCompactlySupportedManifoldCoordinateFunction Ω') :
    (∀ n, MemLp
      (fun z => φ (hgraph.approximants n z) - φ (f z)) 2
        (volume.restrict Q)) ∧
      Filter.Tendsto
        (fun n => eLpNorm
          (fun z => φ (hgraph.approximants n z) - φ (f z)) 2
            (volume.restrict Q)) Filter.atTop (𝓝 0) := by
  rcases φ.smooth.lipschitzWith_of_hasCompactSupport φ.compact_support
      (by simp) with ⟨C, hφlip⟩
  exact lipschitz_comp_sub_memLp_and_tendsto_zero hφlip
    (fun n => (hgraph.smooth n).continuous.aestronglyMeasurable)
    hf_meas hgraph.value_error_memLp hgraph.value_tendsto_l2

/--
%%handwave
name:
  Compact cutoff-adjugate multipliers preserve strong $L^2$ convergence
statement:
  Let $Q\subset\mathbb C$ be compact, let
  $\chi:\mathbb C\to\mathbb R$ be smooth, fix $v\in\mathbb C$, and suppose
  $A_n:Q\to\operatorname{Hom}_{\mathbb R}(\mathbb C,\mathbb C)$ converges
  strongly to zero in $L^2(Q)$. Then
  $$
    z\longmapsto
      \partial_{\operatorname{adj}(A_n(z))v}\chi(z)\,z
  $$
  belongs to $L^2(Q,\mathbb C)$ and converges strongly to zero there.
proof:
  On $Q$, both $\|D\chi(z)\|$ and $\|z\|$ are bounded. Moreover,
  $\|\operatorname{adj}(A_n(z))v\|\leq\|A_n(z)\|\|v\|$. Thus the displayed
  field is bounded pointwise by one fixed constant times $\|A_n(z)\|$.
  Apply [strong $L^2$ convergence under a uniform pointwise linear bound](lean:JJMath.Quasiconformal.memLp_and_tendsto_zero_of_norm_le_mul).
-/
theorem cutoff_adjugate_multiplier_tendsto_l2
    {Q : Set ℂ} (hQ : IsCompact Q) {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (v : ℂ)
    {A : ℕ → ℂ → ℂ →L[ℝ] ℂ}
    (hA : ∀ n, MemLp (A n) 2 (volume.restrict Q))
    (hA_zero : Filter.Tendsto
      (fun n => eLpNorm (A n) 2 (volume.restrict Q))
      Filter.atTop (𝓝 0)) :
    (∀ n, MemLp
      (fun z => (fderiv ℝ χ z (realLinearAdjugate (A n z) v)) • z)
      2 (volume.restrict Q)) ∧
      Filter.Tendsto
        (fun n => eLpNorm
          (fun z => (fderiv ℝ χ z (realLinearAdjugate (A n z) v)) • z)
          2 (volume.restrict Q)) Filter.atTop (𝓝 0) := by
  have hdχ_cont : Continuous (fun z : ℂ => fderiv ℝ χ z) :=
    hχ.continuous_fderiv (by simp)
  rcases hQ.exists_bound_of_continuousOn hdχ_cont.continuousOn with
    ⟨Cχ, hCχ⟩
  rcases hQ.exists_bound_of_continuousOn continuous_id.continuousOn with
    ⟨Cz, hCz⟩
  let b : ℕ → ℂ → ℂ := fun n z =>
    (fderiv ℝ χ z (realLinearAdjugate (A n z) v)) • z
  have hb_meas : ∀ n, AEStronglyMeasurable (b n) (volume.restrict Q) := by
    intro n
    have hAdj : AEStronglyMeasurable (fun z => realLinearAdjugate (A n z))
        (volume.restrict Q) :=
      continuous_realLinearAdjugate.comp_aestronglyMeasurable
        (hA n).aestronglyMeasurable
    have hAdjv : AEStronglyMeasurable
        (fun z => realLinearAdjugate (A n z) v) (volume.restrict Q) :=
      hAdj.apply_continuousLinearMap v
    have hdχ : AEStronglyMeasurable (fun z : ℂ => fderiv ℝ χ z)
        (volume.restrict Q) := hdχ_cont.aestronglyMeasurable
    have hscalar : AEStronglyMeasurable
        (fun z => fderiv ℝ χ z (realLinearAdjugate (A n z) v))
        (volume.restrict Q) :=
      (ContinuousLinearMap.apply ℝ ℝ).flip.aestronglyMeasurable_comp₂ hdχ hAdjv
    exact hscalar.smul continuous_id.aestronglyMeasurable
  have hbound : ∀ n, ∀ᵐ z ∂volume.restrict Q,
      ‖b n z‖ ≤ (Cχ * ‖v‖ * Cz) * ‖A n z‖ := by
    intro n
    filter_upwards [ae_restrict_mem hQ.measurableSet] with z hzQ
    dsimp [b]
    have hCχ_nonneg : 0 ≤ Cχ :=
      (norm_nonneg (fderiv ℝ χ z)).trans (hCχ z hzQ)
    have hAdj_nonneg : 0 ≤ ‖realLinearAdjugate (A n z)‖ * ‖v‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    calc
      ‖(fderiv ℝ χ z (realLinearAdjugate (A n z) v)) • z‖
          = ‖fderiv ℝ χ z (realLinearAdjugate (A n z) v)‖ * ‖z‖ :=
            norm_smul _ _
      _ ≤ (‖fderiv ℝ χ z‖ * ‖realLinearAdjugate (A n z) v‖) * ‖z‖ := by
        gcongr
        exact (fderiv ℝ χ z).le_opNorm _
      _ ≤ (‖fderiv ℝ χ z‖ *
            (‖realLinearAdjugate (A n z)‖ * ‖v‖)) * ‖z‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            ((realLinearAdjugate (A n z)).le_opNorm v) (norm_nonneg _))
          (norm_nonneg _)
      _ ≤ (Cχ * (‖realLinearAdjugate (A n z)‖ * ‖v‖)) * ‖z‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hCχ z hzQ) hAdj_nonneg)
          (norm_nonneg _)
      _ ≤ (Cχ * (‖realLinearAdjugate (A n z)‖ * ‖v‖)) * Cz := by
        exact mul_le_mul_of_nonneg_left (hCz z hzQ)
          (mul_nonneg hCχ_nonneg hAdj_nonneg)
      _ = (Cχ * ‖v‖ * Cz) * ‖A n z‖ := by
        rw [norm_realLinearAdjugate]
        ring
  exact memLp_and_tendsto_zero_of_norm_le_mul hA hb_meas hbound hA_zero

/--
%%handwave
name:
  Strong convergence of scalar cutoff-adjugate multipliers
statement:
  Let $Q\subset\mathbb C$ be compact, let $\chi:\mathbb C\to\mathbb R$ be
  smooth, and fix $v\in\mathbb C$. If
  $A_n\to0$ in $L^2(Q)$, then
  $$
    D\chi(z)\bigl(\operatorname{adj}(A_n(z))v\bigr)
      \longrightarrow0
      \quad\text{in }L^2(Q).
  $$
proof:
  On $Q$, the norm of $D\chi$ has a uniform bound. The adjugate is linear
  and preserves the operator norm in the plane, so the displayed scalar is
  bounded by one fixed constant times $\lVert A_n(z)\rVert$. Apply strong
  $L^2$ convergence under a uniform pointwise linear bound.
-/
theorem cutoff_adjugate_scalar_multiplier_tendsto_l2
    {Q : Set ℂ} (hQ : IsCompact Q) {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (v : ℂ)
    {A : ℕ → ℂ → ℂ →L[ℝ] ℂ}
    (hA : ∀ n, MemLp (A n) 2 (volume.restrict Q))
    (hA_zero : Filter.Tendsto
      (fun n => eLpNorm (A n) 2 (volume.restrict Q))
      Filter.atTop (𝓝 0)) :
    (∀ n, MemLp
      (fun z => fderiv ℝ χ z
        (realLinearAdjugate (A n z) v))
      2 (volume.restrict Q)) ∧
      Filter.Tendsto
        (fun n => eLpNorm
          (fun z => fderiv ℝ χ z
            (realLinearAdjugate (A n z) v))
          2 (volume.restrict Q)) Filter.atTop (𝓝 0) := by
  have hdχ_cont : Continuous (fun z : ℂ => fderiv ℝ χ z) :=
    hχ.continuous_fderiv (by simp)
  rcases hQ.exists_bound_of_continuousOn hdχ_cont.continuousOn with
    ⟨Cχ, hCχ⟩
  let b : ℕ → ℂ → ℝ := fun n z =>
    fderiv ℝ χ z (realLinearAdjugate (A n z) v)
  have hb_meas : ∀ n,
      AEStronglyMeasurable (b n) (volume.restrict Q) := by
    intro n
    have hAdj :
        AEStronglyMeasurable
          (fun z => realLinearAdjugate (A n z))
          (volume.restrict Q) :=
      continuous_realLinearAdjugate.comp_aestronglyMeasurable
        (hA n).aestronglyMeasurable
    have hAdjv :
        AEStronglyMeasurable
          (fun z => realLinearAdjugate (A n z) v)
          (volume.restrict Q) :=
      hAdj.apply_continuousLinearMap v
    exact
      (ContinuousLinearMap.apply ℝ ℝ).flip.aestronglyMeasurable_comp₂
        hdχ_cont.aestronglyMeasurable hAdjv
  have hbound : ∀ n, ∀ᵐ z ∂volume.restrict Q,
      ‖b n z‖ ≤ (Cχ * ‖v‖) * ‖A n z‖ := by
    intro n
    filter_upwards [ae_restrict_mem hQ.measurableSet] with z hzQ
    have hCχ_nonneg : 0 ≤ Cχ :=
      (norm_nonneg (fderiv ℝ χ z)).trans (hCχ z hzQ)
    calc
      ‖b n z‖ ≤
          ‖fderiv ℝ χ z‖ *
            ‖realLinearAdjugate (A n z) v‖ :=
        (fderiv ℝ χ z).le_opNorm _
      _ ≤
          ‖fderiv ℝ χ z‖ *
            (‖realLinearAdjugate (A n z)‖ * ‖v‖) := by
        exact mul_le_mul_of_nonneg_left
          ((realLinearAdjugate (A n z)).le_opNorm v)
          (norm_nonneg _)
      _ ≤ Cχ *
            (‖realLinearAdjugate (A n z)‖ * ‖v‖) := by
        exact mul_le_mul_of_nonneg_right (hCχ z hzQ)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = (Cχ * ‖v‖) * ‖A n z‖ := by
        rw [norm_realLinearAdjugate]
        ring
  simpa [b] using
    memLp_and_tendsto_zero_of_norm_le_mul
      hA hb_meas hbound hA_zero

/--
%%handwave
name:
  Vanishing of the localized Piola cutoff error
statement:
  Let $Q\subset\mathbb C$ be compact, let smooth maps $T_n$ converge to $f$
  in the $W^{1,2}(Q)$ graph norm with weak differential $Df$, and let
  $\chi:\mathbb C\to\mathbb R$ be smooth. Fix $v\in\mathbb C$ and suppose
  that a smooth compactly supported function $\varphi$ satisfies
  $$
    \varphi(f(z))\,
      \partial_{\operatorname{adj}(Df(z))v}\chi(z)\,z=0
  $$
  for every $z\in Q$. Then
  $$
    \int_Q \varphi(T_n(z))
      \partial_{\operatorname{adj}(DT_n(z))v}\chi(z)\,z\,dz
      \longrightarrow0.
  $$
proof:
  Write $DT_n=(DT_n-Df)+Df$ and use linearity of the planar adjugate. The
  factor $\varphi(T_n)-\varphi(f)$ tends to zero in $L^2$. The multiplier
  built from $DT_n-Df$ also tends to zero in $L^2$ by
  [the compact cutoff-adjugate estimate](lean:JJMath.Quasiconformal.cutoff_adjugate_multiplier_tendsto_l2), so both its pairing with the composition error and its pairing with the fixed function $\varphi\circ f$ vanish. The multiplier built from $Df$ is a fixed $L^2$ function, and its pairing with the composition error vanishes by [the bounded $L^2$ pairing estimate](lean:JJMath.Quasiconformal.integral_smul_tendsto_zero_of_L2_tendsto_zero_of_L2_bounded). The remaining fixed product is zero by hypothesis.
-/
theorem PlanarWeakSobolevSmoothApproxGraphL2Data.cutoffError_integral_tendsto_zero
    {Q : Set ℂ} (hQ : IsCompact Q) {f : ℂ → ℂ}
    {df : ℂ → ℂ →L[ℝ] ℂ}
    (hgraph : PlanarWeakSobolevSmoothApproxGraphL2Data Q f df)
    (hf : MemLp f 2 (volume.restrict Q))
    (hdf : MemLp df 2 (volume.restrict Q))
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    {Ω' : Set ℂ}
    (φ : JJMath.Uniformization.SmoothCompactlySupportedManifoldCoordinateFunction Ω')
    (v : ℂ)
    (hlimit : ∀ z ∈ Q,
      φ (f z) •
        ((fderiv ℝ χ z (realLinearAdjugate (df z) v)) • z) = 0) :
    Filter.Tendsto
      (fun n => ∫ z in Q,
        φ (hgraph.approximants n z) •
          ((fderiv ℝ χ z
            (realLinearAdjugate (fderiv ℝ (hgraph.approximants n) z) v)) • z)
        ∂volume) Filter.atTop (𝓝 0) := by
  let a : ℕ → ℂ → ℝ := fun n z =>
    φ (hgraph.approximants n z) - φ (f z)
  let Aerr : ℕ → ℂ → ℂ →L[ℝ] ℂ := fun n z =>
    fderiv ℝ (hgraph.approximants n) z - df z
  let berr : ℕ → ℂ → ℂ := fun n z =>
    (fderiv ℝ χ z (realLinearAdjugate (Aerr n z) v)) • z
  let c : ℂ → ℂ := fun z =>
    (fderiv ℝ χ z (realLinearAdjugate (df z) v)) • z
  let φf : ℂ → ℝ := fun z => φ (f z)
  have ha := hgraph.testFunction_comp_sub_tendsto_l2 hf.aestronglyMeasurable φ
  have hberr := cutoff_adjugate_multiplier_tendsto_l2 hQ hχ v
    hgraph.derivative_error_memLp hgraph.derivative_tendsto_l2
  have hberr_mem : ∀ n, MemLp (berr n) 2 (volume.restrict Q) := by
    simpa [berr, Aerr] using hberr.1
  have hberr_zero : Filter.Tendsto
      (fun n => eLpNorm (berr n) 2 (volume.restrict Q))
      Filter.atTop (𝓝 0) := by
    simpa [berr, Aerr] using hberr.2
  let Aseq : ℕ → ℂ → ℂ →L[ℝ] ℂ := fun n z =>
    if n = 0 then df z else 0
  have hAseq_mem : ∀ n, MemLp (Aseq n) 2 (volume.restrict Q) := by
    intro n
    by_cases hn : n = 0
    · subst n
      simpa [Aseq] using hdf
    · have hzero : Aseq n = (0 : ℂ → (ℂ →L[ℝ] ℂ)) := by
        funext z
        simp [Aseq, hn]
      rw [hzero]
      exact (MemLp.zero (α := ℂ) (ε := ℂ →L[ℝ] ℂ)
        (p := 2) (μ := volume.restrict Q))
  have hAseq_zero : Filter.Tendsto
      (fun n => eLpNorm (Aseq n) 2 (volume.restrict Q))
      Filter.atTop (𝓝 0) := by
    apply Filter.Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
    have hn0 : n ≠ 0 := Nat.ne_of_gt hn
    have hzero : Aseq n = (0 : ℂ → (ℂ →L[ℝ] ℂ)) := by
      funext z
      simp [Aseq, hn0]
    rw [hzero]
    exact (eLpNorm_zero (α := ℂ) (ε := ℂ →L[ℝ] ℂ)
      (p := 2) (μ := volume.restrict Q)).symm
  have hfixed_seq := cutoff_adjugate_multiplier_tendsto_l2 hQ hχ v
    hAseq_mem hAseq_zero
  have hc : MemLp c 2 (volume.restrict Q) := by
    simpa [c, Aseq] using hfixed_seq.1 0
  have hpair_err : Filter.Tendsto
      (fun n => ∫ z, a n z • berr n z ∂volume.restrict Q)
      Filter.atTop (𝓝 0) :=
    integral_smul_tendsto_zero_of_L2_tendsto_zero
      (by simpa [a] using ha.1) hberr_mem
      (by simpa [a] using ha.2) hberr_zero
  have hpair_fixed : Filter.Tendsto
      (fun n => ∫ z, a n z • c z ∂volume.restrict Q)
      Filter.atTop (𝓝 0) := by
    apply integral_smul_tendsto_zero_of_L2_tendsto_zero_of_L2_bounded
      (by simpa [a] using ha.1) (fun _ => hc) (by simpa [a] using ha.2)
    exact ⟨eLpNorm c 2 (volume.restrict Q),
      ne_of_lt hc.eLpNorm_lt_top, fun _ => le_rfl⟩
  haveI : IsFiniteMeasure (volume.restrict Q) :=
    isFiniteMeasure_restrict.2 hQ.measure_ne_top
  rcases φ.smooth.lipschitzWith_of_hasCompactSupport φ.compact_support
      (by simp) with ⟨Cφ, hφlip⟩
  have hφshift : MemLp (fun z => φ (f z) - φ 0) 2
      (volume.restrict Q) := by
    have hlip : LipschitzWith Cφ (fun y : ℂ => φ y - φ 0) := by
      intro x y
      simpa using hφlip x y
    simpa [Function.comp_def] using hlip.comp_memLp (by simp) hf
  have hφf : MemLp φf 2 (volume.restrict Q) := by
    have hsum := hφshift.add
      (memLp_const (μ := volume.restrict Q) (p := 2) (φ 0))
    have heq : φf =
        (fun z => φ (f z) - φ 0) + (fun _ : ℂ => φ 0) := by
      funext z
      simp [φf]
    rw [heq]
    exact hsum
  have hpair_φf_err : Filter.Tendsto
      (fun n => ∫ z, φf z • berr n z ∂volume.restrict Q)
      Filter.atTop (𝓝 0) := by
    apply integral_smul_tendsto_zero_of_L2_bounded_of_L2_tendsto_zero
      (fun _ => hφf) hberr_mem
    · exact ⟨eLpNorm φf 2 (volume.restrict Q),
        ne_of_lt hφf.eLpNorm_lt_top, fun _ => le_rfl⟩
    · exact hberr_zero
  have hpair_sum : Filter.Tendsto
      (fun n => ∫ z, a n z • (berr n z + c z) ∂volume.restrict Q)
      Filter.atTop (𝓝 0) := by
    have hsum := hpair_err.add hpair_fixed
    convert hsum using 1
    · funext n
      have hierr : Integrable (fun z => a n z • berr n z)
          (volume.restrict Q) := by
        apply memLp_one_iff_integrable.mp
        show MemLp (fun z => a n z • berr n z) 1 (volume.restrict Q)
        exact MemLp.smul (p := 2) (q := 2) (r := 1) (hberr_mem n)
          (by simpa [a] using ha.1 n)
      have hifix : Integrable (fun z => a n z • c z)
          (volume.restrict Q) := by
        apply memLp_one_iff_integrable.mp
        show MemLp (fun z => a n z • c z) 1 (volume.restrict Q)
        exact MemLp.smul (p := 2) (q := 2) (r := 1) hc
          (by simpa [a] using ha.1 n)
      rw [← integral_add hierr hifix]
      apply integral_congr_ae
      filter_upwards with z
      simp [smul_add]
    · simp
  have htotal := hpair_sum.add hpair_φf_err
  have htotal' : Filter.Tendsto
      (fun n => (∫ z, a n z • (berr n z + c z) ∂volume.restrict Q) +
        ∫ z, φf z • berr n z ∂volume.restrict Q)
      Filter.atTop (𝓝 0) := by
    simpa using htotal
  apply htotal'.congr'
  filter_upwards with n
  have hi1 : Integrable (fun z => a n z • (berr n z + c z))
      (volume.restrict Q) := by
    have hab : MemLp (fun z => berr n z + c z) 2
        (volume.restrict Q) := (hberr_mem n).add hc
    apply memLp_one_iff_integrable.mp
    exact MemLp.smul (p := 2) (q := 2) (r := 1) hab
      (by simpa [a] using ha.1 n)
  have hi2 : Integrable (fun z => φf z • berr n z)
      (volume.restrict Q) := by
    apply memLp_one_iff_integrable.mp
    exact MemLp.smul (p := 2) (q := 2) (r := 1) (hberr_mem n) hφf
  rw [← integral_add hi1 hi2]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hQ.measurableSet] with z hzQ
  have hAdj : realLinearAdjugate
      (fderiv ℝ (hgraph.approximants n) z) v =
        realLinearAdjugate (Aerr n z) v + realLinearAdjugate (df z) v := by
    have hsplit : fderiv ℝ (hgraph.approximants n) z = Aerr n z + df z := by
      simp [Aerr]
    rw [hsplit]
    apply Complex.ext <;>
      simp [realLinearAdjugate, realLinearMapOfWirtinger, weakDZ, weakDBar] <;>
      ring
  rw [hAdj, map_add, add_smul]
  have hz : φf z • c z = 0 := by
    simpa [φf, c] using hlimit z hzQ
  change a n z • (berr n z + c z) + φf z • berr n z =
    φ (hgraph.approximants n z) • (berr n z + c z)
  have hsplit : φ (hgraph.approximants n z) = a n z + φf z := by
    simp [a, φf]
  rw [hsplit, add_smul, smul_add, smul_add, hz, add_zero]

/--
%%handwave
name:
  Strong convergence of the scalar Piola cutoff term
statement:
  Let $Q\subset\mathbb C$ be compact and let smooth maps
  $T_n:\mathbb C\to\mathbb C$ converge to $(f,Df)$ in the
  $W^{1,2}(Q)$ graph norm. For smooth $\chi$ and smooth compactly supported
  $\varphi$, and for $v\in\mathbb C$,
  $$
    \int_Q\varphi(T_n(z))D\chi(z)
      \bigl(\operatorname{adj}(DT_n(z))v\bigr)\,dz
      \longrightarrow
    \int_Q\varphi(f(z))D\chi(z)
      \bigl(\operatorname{adj}(Df(z))v\bigr)\,dz.
  $$
proof:
  Split both the composition and the differential into their limiting parts
  and errors. The composition error tends to zero in $L^2$, and [the scalar
  cutoff-adjugate multiplier of the differential error also tends to zero
  in $L^2$](lean:JJMath.Quasiconformal.cutoff_adjugate_scalar_multiplier_tendsto_l2). The three error pairings vanish by Cauchy--Schwarz, leaving the fixed limiting pairing.
-/
theorem PlanarWeakSobolevSmoothApproxGraphL2Data.cutoffScalarTerm_integral_tendsto
    {Q : Set ℂ} (hQ : IsCompact Q) {f : ℂ → ℂ}
    {df : ℂ → ℂ →L[ℝ] ℂ}
    (hgraph : PlanarWeakSobolevSmoothApproxGraphL2Data Q f df)
    (hf : MemLp f 2 (volume.restrict Q))
    (hdf : MemLp df 2 (volume.restrict Q))
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    {Ω' : Set ℂ}
    (φ : JJMath.Uniformization.SmoothCompactlySupportedManifoldCoordinateFunction Ω')
    (v : ℂ) :
    Filter.Tendsto
      (fun n => ∫ z in Q,
        φ (hgraph.approximants n z) *
          fderiv ℝ χ z
            (realLinearAdjugate
              (fderiv ℝ (hgraph.approximants n) z) v)
        ∂volume)
      Filter.atTop
      (𝓝 (∫ z in Q,
        φ (f z) *
          fderiv ℝ χ z (realLinearAdjugate (df z) v)
        ∂volume)) := by
  let μ : Measure ℂ := volume.restrict Q
  let a : ℕ → ℂ → ℝ := fun n z =>
    φ (hgraph.approximants n z) - φ (f z)
  let Aerr : ℕ → ℂ → ℂ →L[ℝ] ℂ := fun n z =>
    fderiv ℝ (hgraph.approximants n) z - df z
  let berr : ℕ → ℂ → ℝ := fun n z =>
    fderiv ℝ χ z (realLinearAdjugate (Aerr n z) v)
  let bfix : ℂ → ℝ := fun z =>
    fderiv ℝ χ z (realLinearAdjugate (df z) v)
  let φf : ℂ → ℝ := fun z => φ (f z)
  have ha :=
    hgraph.testFunction_comp_sub_tendsto_l2
      hf.aestronglyMeasurable φ
  have hberr :=
    cutoff_adjugate_scalar_multiplier_tendsto_l2 hQ hχ v
      hgraph.derivative_error_memLp hgraph.derivative_tendsto_l2
  have hberr_mem : ∀ n, MemLp (berr n) 2 μ := by
    simpa [berr, Aerr, μ] using hberr.1
  have hberr_zero :
      Filter.Tendsto
        (fun n => eLpNorm (berr n) 2 μ)
        Filter.atTop (𝓝 0) := by
    simpa [berr, Aerr, μ] using hberr.2
  have hdχcont : Continuous (fun z : ℂ => fderiv ℝ χ z) :=
    hχ.continuous_fderiv (by simp)
  rcases hQ.exists_bound_of_continuousOn hdχcont.continuousOn with
    ⟨Cχ0, hCχ0⟩
  let Cχ : ℝ := max Cχ0 0
  let C : ℝ := Cχ * ‖v‖
  have hCχ : ∀ z ∈ Q, ‖fderiv ℝ χ z‖ ≤ Cχ :=
    fun z hz => (hCχ0 z hz).trans (le_max_left _ _)
  have hCχnonneg : 0 ≤ Cχ := le_max_right _ _
  have hbfix_meas : AEStronglyMeasurable bfix μ := by
    have hAdj :
        AEStronglyMeasurable
          (fun z => realLinearAdjugate (df z)) μ :=
      continuous_realLinearAdjugate.comp_aestronglyMeasurable
        hdf.aestronglyMeasurable
    have hAdjv :
        AEStronglyMeasurable
          (fun z => realLinearAdjugate (df z) v) μ :=
      hAdj.apply_continuousLinearMap v
    exact
      (ContinuousLinearMap.apply ℝ ℝ).flip.aestronglyMeasurable_comp₂
        hdχcont.aestronglyMeasurable hAdjv
  have hbfix_bound : ∀ᵐ z ∂μ,
      ‖bfix z‖ ≤ C * ‖df z‖ := by
    filter_upwards [ae_restrict_mem hQ.measurableSet] with z hz
    calc
      ‖bfix z‖ ≤
          ‖fderiv ℝ χ z‖ *
            ‖realLinearAdjugate (df z) v‖ :=
        (fderiv ℝ χ z).le_opNorm _
      _ ≤
          ‖fderiv ℝ χ z‖ *
            (‖realLinearAdjugate (df z)‖ * ‖v‖) := by
        exact mul_le_mul_of_nonneg_left
          ((realLinearAdjugate (df z)).le_opNorm v)
          (norm_nonneg _)
      _ ≤ Cχ * (‖realLinearAdjugate (df z)‖ * ‖v‖) := by
        exact mul_le_mul_of_nonneg_right (hCχ z hz)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = C * ‖df z‖ := by
        rw [norm_realLinearAdjugate]
        simp only [C]
        ring
  have hbfix : MemLp bfix 2 μ :=
    hdf.of_le_mul hbfix_meas hbfix_bound
  haveI : IsFiniteMeasure μ :=
    isFiniteMeasure_restrict.2 hQ.measure_ne_top
  rcases φ.smooth.lipschitzWith_of_hasCompactSupport φ.compact_support
      (by simp) with ⟨Cφ, hφlip⟩
  have hφshift : MemLp (fun z => φ (f z) - φ 0) 2 μ := by
    have hlip : LipschitzWith Cφ
        (fun y : ℂ => φ y - φ 0) := by
      intro x y
      simpa using hφlip x y
    simpa [Function.comp_def, μ] using
      hlip.comp_memLp (by simp) hf
  have hφf : MemLp φf 2 μ := by
    have hsum :=
      hφshift.add (memLp_const (μ := μ) (p := 2) (φ 0))
    have heq : φf =
        (fun z => φ (f z) - φ 0) +
          (fun _ : ℂ => φ 0) := by
      funext z
      simp [φf]
    rw [heq]
    exact hsum
  have h_a_berr :
      Filter.Tendsto
        (fun n => ∫ z, a n z * berr n z ∂μ)
        Filter.atTop (𝓝 0) := by
    simpa only [smul_eq_mul] using
      integral_smul_tendsto_zero_of_L2_tendsto_zero
        (by simpa [a, μ] using ha.1) hberr_mem
        (by simpa [a, μ] using ha.2) hberr_zero
  have h_a_bfix :
      Filter.Tendsto
        (fun n => ∫ z, a n z * bfix z ∂μ)
        Filter.atTop (𝓝 0) := by
    simpa only [smul_eq_mul] using
      integral_smul_tendsto_zero_of_L2_tendsto_zero_of_L2_bounded
        (by simpa [a, μ] using ha.1) (fun _ => hbfix)
        (by simpa [a, μ] using ha.2)
        ⟨eLpNorm bfix 2 μ, ne_of_lt hbfix.eLpNorm_lt_top,
          fun _ => le_rfl⟩
  have h_φf_berr :
      Filter.Tendsto
        (fun n => ∫ z, φf z * berr n z ∂μ)
        Filter.atTop (𝓝 0) := by
    simpa only [smul_eq_mul] using
      integral_smul_tendsto_zero_of_L2_bounded_of_L2_tendsto_zero
        (fun _ => hφf) hberr_mem
        ⟨eLpNorm φf 2 μ, ne_of_lt hφf.eLpNorm_lt_top,
          fun _ => le_rfl⟩ hberr_zero
  have hfixed :
      Filter.Tendsto
        (fun _ : ℕ => ∫ z, φf z * bfix z ∂μ)
        Filter.atTop
        (𝓝 (∫ z, φf z * bfix z ∂μ)) :=
    tendsto_const_nhds
  have hsum :=
    ((h_a_berr.add h_a_bfix).add h_φf_berr).add hfixed
  convert hsum using 1
  · funext n
    have hi1 : Integrable (fun z => a n z * berr n z) μ := by
      apply memLp_one_iff_integrable.mp
      simpa only [smul_eq_mul] using
        MemLp.smul (p := 2) (q := 2) (r := 1)
          (hberr_mem n) (by simpa [a, μ] using ha.1 n)
    have hi2 : Integrable (fun z => a n z * bfix z) μ := by
      apply memLp_one_iff_integrable.mp
      simpa only [smul_eq_mul] using
        MemLp.smul (p := 2) (q := 2) (r := 1)
          hbfix (by simpa [a, μ] using ha.1 n)
    have hi3 : Integrable (fun z => φf z * berr n z) μ := by
      apply memLp_one_iff_integrable.mp
      simpa only [smul_eq_mul] using
        MemLp.smul (p := 2) (q := 2) (r := 1)
          (hberr_mem n) hφf
    have hi4 : Integrable (fun z => φf z * bfix z) μ := by
      apply memLp_one_iff_integrable.mp
      simpa only [smul_eq_mul] using
        MemLp.smul (p := 2) (q := 2) (r := 1)
          hbfix hφf
    change
      (∫ z,
        φ (hgraph.approximants n z) *
          fderiv ℝ χ z
            (realLinearAdjugate
              (fderiv ℝ (hgraph.approximants n) z) v) ∂μ) = _
    calc
      _ = ∫ z,
          ((a n z * berr n z + a n z * bfix z) +
            φf z * berr n z) + φf z * bfix z ∂μ := by
        apply integral_congr_ae
        filter_upwards with z
        have hAdj :
            realLinearAdjugate
                (fderiv ℝ (hgraph.approximants n) z) v =
              realLinearAdjugate (Aerr n z) v +
                realLinearAdjugate (df z) v := by
          have hsplit :
              fderiv ℝ (hgraph.approximants n) z =
                Aerr n z + df z := by
            simp [Aerr]
          rw [hsplit]
          apply Complex.ext <;>
            simp [realLinearAdjugate,
              realLinearMapOfWirtinger, weakDZ, weakDBar] <;>
            ring
        rw [hAdj, map_add]
        simp only [a, berr, bfix, φf]
        ring
      _ =
          (((∫ z, a n z * berr n z ∂μ) +
              ∫ z, a n z * bfix z ∂μ) +
            ∫ z, φf z * berr n z ∂μ) +
          ∫ z, φf z * bfix z ∂μ := by
        calc
          ∫ z,
              ((a n z * berr n z + a n z * bfix z) +
                φf z * berr n z) + φf z * bfix z ∂μ =
              (∫ z,
                (a n z * berr n z + a n z * bfix z) +
                  φf z * berr n z ∂μ) +
                ∫ z, φf z * bfix z ∂μ :=
            integral_add ((hi1.add hi2).add hi3) hi4
          _ =
              ((∫ z, a n z * berr n z +
                  a n z * bfix z ∂μ) +
                ∫ z, φf z * berr n z ∂μ) +
                ∫ z, φf z * bfix z ∂μ := by
            apply congrArg
              (fun q => q + ∫ z, φf z * bfix z ∂μ)
            simpa only [Pi.add_apply] using
              integral_add (hi1.add hi2) hi3
          _ =
              (((∫ z, a n z * berr n z ∂μ) +
                  ∫ z, a n z * bfix z ∂μ) +
                ∫ z, φf z * berr n z ∂μ) +
                ∫ z, φf z * bfix z ∂μ := by
            apply congrArg
              (fun q =>
                (q + ∫ z, φf z * berr n z ∂μ) +
                  ∫ z, φf z * bfix z ∂μ)
            simpa only [Pi.add_apply] using
              integral_add hi1 hi2
  · simp [φf, bfix, μ]

/--
%%handwave
name:
  Square-integrable planar differentials have integrable Jacobian
statement:
  Let $(X,\mu)$ be a measure space and let
  $A:X\to\operatorname{Hom}_{\mathbb R}(\mathbb C,\mathbb C)$ belong to
  $L^2(\mu)$. Then $x\mapsto J(A(x))$ belongs to $L^1(\mu)$.
proof:
  The quadratic difference estimate with the zero map gives
  $|J(A(x))|\leq 2\|A(x)\|^2$. The right-hand side is integrable by
  Hölder's inequality.
-/
theorem weakJacobian_integrable_of_memLp_two
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {A : α → ℂ →L[ℝ] ℂ} (hA : MemLp A 2 μ) :
    Integrable (fun x => weakJacobian (A x)) μ := by
  have hprod : MemLp (fun x => ‖A x‖ * ‖A x‖) 1 μ := by
    simpa only [smul_eq_mul] using
      MemLp.smul (p := 2) (q := 2) (r := 1) hA.norm hA.norm
  have hmajor : Integrable (fun x => 2 * (‖A x‖ * ‖A x‖)) μ := by
    exact memLp_one_iff_integrable.mp (hprod.const_mul 2)
  apply hmajor.mono'
  · exact continuous_weakJacobian.comp_aestronglyMeasurable hA.aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs]
    have h := abs_weakJacobian_sub_le (A x) 0
    have hzero : weakJacobian (0 : ℂ →L[ℝ] ℂ) = 0 := by
      simp [weakJacobian]
    simpa [hzero, mul_assoc] using h

/--
%%handwave
name:
  Strong local $L^1$ convergence of planar Jacobians
statement:
  Let $Q\subset\mathbb C$, let $Df\in L^2(Q)$, and let smooth maps
  $T_n:\mathbb C\to\mathbb C$ satisfy
  $$
    \|DT_n-Df\|_{L^2(Q)}\longrightarrow0.
  $$
  Then
  $$
    \int_Q |J(DT_n(z))-J(Df(z))|\,dz\longrightarrow0.
  $$
proof:
  By [the quadratic difference estimate for the planar Jacobian](lean:JJMath.Quasiconformal.abs_weakJacobian_sub_le), the integrand is bounded by a constant multiple of
  $\|DT_n-Df\|^2+2\|Df\|\|DT_n-Df\|$. The first term tends to zero in
  $L^1$ by pairing the derivative error with itself, and the second does so
  by pairing it with the fixed $L^2$ field $Df$.
-/
theorem PlanarWeakSobolevSmoothApproxGraphL2Data.weakJacobian_integral_abs_sub_tendsto_zero
    {Q : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (hgraph : PlanarWeakSobolevSmoothApproxGraphL2Data Q f df)
    (hdf : MemLp df 2 (volume.restrict Q)) :
    Filter.Tendsto
      (fun n => ∫ z in Q,
        |weakJacobian (fderiv ℝ (hgraph.approximants n) z) -
          weakJacobian (df z)| ∂volume)
      Filter.atTop (𝓝 0) := by
  let E : ℕ → ℂ → ℂ →L[ℝ] ℂ := fun n z =>
    fderiv ℝ (hgraph.approximants n) z - df z
  have hE_mem : ∀ n, MemLp (E n) 2 (volume.restrict Q) := by
    simpa [E] using hgraph.derivative_error_memLp
  have hE_zero : Filter.Tendsto
      (fun n => eLpNorm (E n) 2 (volume.restrict Q))
      Filter.atTop (𝓝 0) := by
    simpa [E] using hgraph.derivative_tendsto_l2
  have hEnorm_mem : ∀ n, MemLp (fun z => ‖E n z‖) 2
      (volume.restrict Q) := fun n => (hE_mem n).norm
  have hEnorm_zero : Filter.Tendsto
      (fun n => eLpNorm (fun z => ‖E n z‖) 2 (volume.restrict Q))
      Filter.atTop (𝓝 0) := by
    simpa only [eLpNorm_norm] using hE_zero
  have hsq : Filter.Tendsto
      (fun n => ∫ z, ‖E n z‖ * ‖E n z‖ ∂volume.restrict Q)
      Filter.atTop (𝓝 0) := by
    simpa only [smul_eq_mul] using
      integral_smul_tendsto_zero_of_L2_tendsto_zero
        hEnorm_mem hEnorm_mem hEnorm_zero hEnorm_zero
  have hcross : Filter.Tendsto
      (fun n => ∫ z, ‖df z‖ * ‖E n z‖ ∂volume.restrict Q)
      Filter.atTop (𝓝 0) := by
    have hraw := integral_smul_tendsto_zero_of_L2_tendsto_zero_of_L2_bounded
      hEnorm_mem (fun _ => hdf.norm) hEnorm_zero
      ⟨eLpNorm (fun z => ‖df z‖) 2 (volume.restrict Q),
        ne_of_lt hdf.norm.eLpNorm_lt_top, fun _ => le_rfl⟩
    simpa only [smul_eq_mul, mul_comm] using hraw
  let upper : ℕ → ℂ → ℝ := fun n z =>
    2 * (‖E n z‖ * ‖E n z‖) + 4 * (‖df z‖ * ‖E n z‖)
  have hsq_int : ∀ n, Integrable (fun z => ‖E n z‖ * ‖E n z‖)
      (volume.restrict Q) := by
    intro n
    apply memLp_one_iff_integrable.mp
    show MemLp (fun z => ‖E n z‖ * ‖E n z‖) 1 (volume.restrict Q)
    simpa only [smul_eq_mul] using
      MemLp.smul (p := 2) (q := 2) (r := 1) (hEnorm_mem n) (hEnorm_mem n)
  have hcross_int : ∀ n, Integrable (fun z => ‖df z‖ * ‖E n z‖)
      (volume.restrict Q) := by
    intro n
    apply memLp_one_iff_integrable.mp
    show MemLp (fun z => ‖df z‖ * ‖E n z‖) 1 (volume.restrict Q)
    simpa only [smul_eq_mul, mul_comm] using
      MemLp.smul (p := 2) (q := 2) (r := 1) hdf.norm (hEnorm_mem n)
  have hupper_int : ∀ n, Integrable (upper n) (volume.restrict Q) := by
    intro n
    exact ((hsq_int n).const_mul 2).add ((hcross_int n).const_mul 4)
  have hupper_integral : ∀ n,
      ∫ z, upper n z ∂volume.restrict Q =
        2 * ∫ z, ‖E n z‖ * ‖E n z‖ ∂volume.restrict Q +
          4 * ∫ z, ‖df z‖ * ‖E n z‖ ∂volume.restrict Q := by
    intro n
    simp only [upper]
    rw [integral_add ((hsq_int n).const_mul 2) ((hcross_int n).const_mul 4),
      integral_const_mul, integral_const_mul]
  have hupper_zero : Filter.Tendsto
      (fun n => ∫ z, upper n z ∂volume.restrict Q)
      Filter.atTop (𝓝 0) := by
    have ht := (Filter.Tendsto.const_mul 2 hsq).add
      (Filter.Tendsto.const_mul 4 hcross)
    convert ht using 1
    · funext n
      exact hupper_integral n
    · norm_num
  have hpoint : ∀ n z,
      |weakJacobian (fderiv ℝ (hgraph.approximants n) z) -
          weakJacobian (df z)| ≤ upper n z := by
    intro n z
    have hJ := abs_weakJacobian_sub_le
      (fderiv ℝ (hgraph.approximants n) z) (df z)
    have hD_le : ‖fderiv ℝ (hgraph.approximants n) z‖ ≤
        ‖E n z‖ + ‖df z‖ := by
      have hsplit : fderiv ℝ (hgraph.approximants n) z = E n z + df z := by
        simp [E]
      rw [hsplit]
      exact norm_add_le _ _
    calc
      |weakJacobian (fderiv ℝ (hgraph.approximants n) z) -
          weakJacobian (df z)| ≤
          2 * (‖fderiv ℝ (hgraph.approximants n) z‖ + ‖df z‖) *
            ‖fderiv ℝ (hgraph.approximants n) z - df z‖ := hJ
      _ ≤ 2 * ((‖E n z‖ + ‖df z‖) + ‖df z‖) * ‖E n z‖ := by
        simp only [E]
        gcongr
      _ = upper n z := by
        simp only [upper]
        ring
  have hJ_meas : ∀ n, AEStronglyMeasurable
      (fun z => |weakJacobian (fderiv ℝ (hgraph.approximants n) z) -
        weakJacobian (df z)|) (volume.restrict Q) := by
    intro n
    have hDn : AEStronglyMeasurable
        (fun z => fderiv ℝ (hgraph.approximants n) z) (volume.restrict Q) :=
      ((hgraph.smooth n).continuous_fderiv (by simp)).aestronglyMeasurable
    simpa only [Real.norm_eq_abs] using
      ((continuous_weakJacobian.comp_aestronglyMeasurable hDn).sub
        (continuous_weakJacobian.comp_aestronglyMeasurable
          hdf.aestronglyMeasurable)).norm
  have hJ_int : ∀ n, Integrable
      (fun z => |weakJacobian (fderiv ℝ (hgraph.approximants n) z) -
        weakJacobian (df z)|) (volume.restrict Q) := by
    intro n
    exact (hupper_int n).mono' (hJ_meas n) (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_abs]
      exact hpoint n z)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    hupper_zero
    (fun n => integral_nonneg fun z => abs_nonneg _)
    (fun n => integral_mono (hJ_int n) (hupper_int n) (hpoint n))

/--
%%handwave
name:
  Convergence of Jacobian-weighted target tests under uniform graph approximation
statement:
  Let smooth maps $T_n:\mathbb C\to\mathbb C$ converge to a map $f$
  uniformly on a compact set $Q$, and suppose
  $DT_n\to Df$ in $L^2(Q)$. For every smooth compactly supported
  $\varphi:\mathbb C\to\mathbb R$,
  $$
    \int_Q J_{T_n}(x)\varphi(T_n(x))\,dx
      \longrightarrow
    \int_Q J_f(x)\varphi(f(x))\,dx.
  $$
proof:
  Split the difference into
  $(J_{T_n}-J_f)(\varphi\circ T_n)$ and
  $J_f(\varphi\circ T_n-\varphi\circ f)$. The test function is globally
  bounded. [The Jacobians converge strongly in $L^1(Q)$](lean:JJMath.Quasiconformal.PlanarWeakSobolevSmoothApproxGraphL2Data.weakJacobian_integral_abs_sub_tendsto_zero), so the first term tends to zero. Uniform convergence and continuity of $\varphi$ give pointwise convergence of the second term, while a constant multiple of $|J_f|$ is an integrable dominator.
-/
theorem PlanarWeakSobolevSmoothApproxGraphL2Data.weakJacobian_test_comp_integral_tendsto_of_tendstoUniformlyOn
    {Q : Set ℂ} (hQ : IsCompact Q) {f : ℂ → ℂ}
    {df : ℂ → ℂ →L[ℝ] ℂ}
    (hgraph : PlanarWeakSobolevSmoothApproxGraphL2Data Q f df)
    (hdf : MemLp df 2 (volume.restrict Q))
    (huniform :
      TendstoUniformlyOn hgraph.approximants f Filter.atTop Q)
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ)
    (hφcompact : HasCompactSupport φ) :
    Filter.Tendsto
      (fun n ↦ ∫ x in Q,
        weakJacobian (fderiv ℝ (hgraph.approximants n) x) *
          φ (hgraph.approximants n x) ∂volume)
      Filter.atTop
      (𝓝 (∫ x in Q,
        weakJacobian (df x) * φ (f x) ∂volume)) := by
  let μ : Measure ℂ := volume.restrict Q
  let T : ℕ → ℂ → ℂ := hgraph.approximants
  let Jn : ℕ → ℂ → ℝ := fun n x ↦
    weakJacobian (fderiv ℝ (T n) x)
  let J : ℂ → ℝ := fun x ↦ weakJacobian (df x)
  let err : ℕ → ℂ → ℝ := fun n x ↦
    (Jn n x - J x) * φ (T n x)
  let fixed : ℕ → ℂ → ℝ := fun n x ↦
    J x * φ (T n x)
  let limit : ℂ → ℝ := fun x ↦
    J x * φ (f x)
  rcases hφ.continuous.bounded_above_of_compact_support hφcompact with
    ⟨C₀, hC₀⟩
  let C : ℝ := max C₀ 0
  have hCnonneg : 0 ≤ C := le_max_right _ _
  have hφbound : ∀ y, |φ y| ≤ C := by
    intro y
    rw [← Real.norm_eq_abs]
    exact (hC₀ y).trans (le_max_left C₀ 0)
  have hJint : Integrable J μ := by
    simpa [J, μ] using weakJacobian_integrable_of_memLp_two hdf
  have hdomInt : Integrable (fun x ↦ C * |J x|) μ := by
    simpa only [Real.norm_eq_abs] using hJint.norm.const_mul C
  have hfixedMeas :
      ∀ n, AEStronglyMeasurable (fixed n) μ := by
    intro n
    have hTcont : Continuous (T n) :=
      (hgraph.smooth n).continuous
    exact hJint.aestronglyMeasurable.mul
      (hφ.continuous.comp hTcont).aestronglyMeasurable
  have hfixedBound :
      ∀ n, ∀ᵐ x ∂μ, ‖fixed n x‖ ≤ C * |J x| := by
    intro n
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul]
    simpa [mul_comm] using
      mul_le_mul_of_nonneg_left
        (hφbound (T n x)) (abs_nonneg (J x))
  have hfixedTendsto :
      Filter.Tendsto (fun n ↦ ∫ x, fixed n x ∂μ)
        Filter.atTop (𝓝 (∫ x, limit x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun x ↦ C * |J x|) hfixedMeas hdomInt hfixedBound
    filter_upwards [ae_restrict_mem hQ.measurableSet] with x hx
    have hTx :
        Filter.Tendsto (fun n ↦ T n x) Filter.atTop (𝓝 (f x)) :=
      huniform.tendsto_at hx
    have hφx :
        Filter.Tendsto (fun n ↦ φ (T n x))
          Filter.atTop (𝓝 (φ (f x))) :=
      hφ.continuous.continuousAt.tendsto.comp hTx
    simpa [fixed, limit] using
      Filter.Tendsto.const_mul (J x) hφx
  have hJdiffZero :
      Filter.Tendsto
        (fun n ↦ ∫ x, |Jn n x - J x| ∂μ)
        Filter.atTop (𝓝 0) := by
    simpa [Jn, J, T, μ] using
      hgraph.weakJacobian_integral_abs_sub_tendsto_zero hdf
  have hDTmem :
      ∀ n, MemLp (fun x ↦ fderiv ℝ (T n) x) 2 μ := by
    intro n
    have hsum := (hgraph.derivative_error_memLp n).add hdf
    have heq :
        (fun x ↦ fderiv ℝ (T n) x) =
          (fun x ↦ fderiv ℝ (hgraph.approximants n) x - df x) + df := by
      funext x
      simp [T]
    rw [heq]
    simpa [μ] using hsum
  have hJnInt : ∀ n, Integrable (Jn n) μ := by
    intro n
    simpa [Jn] using weakJacobian_integrable_of_memLp_two (hDTmem n)
  have hJdiffInt :
      ∀ n, Integrable (fun x ↦ |Jn n x - J x|) μ := by
    intro n
    exact ((hJnInt n).sub hJint).abs
  have herrMeas :
      ∀ n, AEStronglyMeasurable (err n) μ := by
    intro n
    have hTcont : Continuous (T n) :=
      (hgraph.smooth n).continuous
    exact ((hJnInt n).aestronglyMeasurable.sub
      hJint.aestronglyMeasurable).mul
        (hφ.continuous.comp hTcont).aestronglyMeasurable
  have herrBound :
      ∀ n, ∀ᵐ x ∂μ, ‖err n x‖ ≤ C * |Jn n x - J x| := by
    intro n
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul]
    simpa [mul_comm] using
      mul_le_mul_of_nonneg_left
        (hφbound (T n x)) (abs_nonneg (Jn n x - J x))
  have herrInt : ∀ n, Integrable (err n) μ := by
    intro n
    exact ((hJdiffInt n).const_mul C).mono'
      (herrMeas n) (herrBound n)
  have herrTendsto :
      Filter.Tendsto (fun n ↦ ∫ x, err n x ∂μ)
        Filter.atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hmajorZero :
        Filter.Tendsto
          (fun n ↦ ∫ x, C * |Jn n x - J x| ∂μ)
          Filter.atTop (𝓝 0) := by
      have ht := Filter.Tendsto.const_mul C hJdiffZero
      simpa only [integral_const_mul, mul_zero] using ht
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hmajorZero
      (fun _ ↦ norm_nonneg _)
      (fun n ↦ norm_integral_le_of_norm_le
        ((hJdiffInt n).const_mul C) (herrBound n))
  have hsum := herrTendsto.add hfixedTendsto
  convert hsum using 1
  · funext n
    rw [← integral_add (herrInt n)
      (hdomInt.mono' (hfixedMeas n) (hfixedBound n))]
    apply integral_congr_ae
    filter_upwards with x
    simp [err, fixed, Jn, J, T]
    ring
  · rw [zero_add]

/--
%%handwave
name:
  Subsequence convergence of the localized Jacobian main term
statement:
  Let $Q\subset\mathbb C$ be compact, let $f,Df\in L^2(Q)$, and let
  smooth maps $T_n:\mathbb C\to\mathbb C$ converge to $(f,Df)$ in the
  $W^{1,2}(Q)$ graph norm. For a smooth function
  $\chi:\mathbb C\to\mathbb R$, a smooth compactly supported function
  $\varphi$, and $v\in\mathbb C$, there is a strictly increasing sequence
  $n_k$ such that
  $$
    \int_Q \chi(z)J(DT_{n_k}(z))
      \partial_v\varphi(T_{n_k}(z))\,z\,dz
      \longrightarrow
    \int_Q \chi(z)J(Df(z))\partial_v\varphi(f(z))\,z\,dz.
  $$
proof:
  Choose [an almost-everywhere convergent subsequence of the smooth maps](lean:JJMath.Quasiconformal.PlanarWeakSobolevSmoothApproxGraphL2Data.exists_strictMono_approximants_tendsto_ae). The Jacobians converge strongly in $L^1$ by [strong local $L^1$ convergence of planar Jacobians](lean:JJMath.Quasiconformal.PlanarWeakSobolevSmoothApproxGraphL2Data.weakJacobian_integral_abs_sub_tendsto_zero), and the remaining coefficient is uniformly bounded on $Q$. For the term with fixed Jacobian $J(Df)$, almost-everywhere convergence and continuity of $D\varphi$ give convergence by the dominated convergence theorem.
-/
theorem PlanarWeakSobolevSmoothApproxGraphL2Data.exists_strictMono_mainTerm_integral_tendsto
    {Q : Set ℂ} (hQ : IsCompact Q) {f : ℂ → ℂ}
    {df : ℂ → ℂ →L[ℝ] ℂ}
    (hgraph : PlanarWeakSobolevSmoothApproxGraphL2Data Q f df)
    (hf : MemLp f 2 (volume.restrict Q))
    (hdf : MemLp df 2 (volume.restrict Q))
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    {Ω' : Set ℂ}
    (φ : JJMath.Uniformization.SmoothCompactlySupportedManifoldCoordinateFunction Ω')
    (v : ℂ) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      Filter.Tendsto
        (fun n => ∫ z in Q,
          (χ z * weakJacobian
              (fderiv ℝ (hgraph.approximants (ns n)) z) *
            fderiv ℝ (φ : ℂ → ℝ) (hgraph.approximants (ns n) z) v) • z
          ∂volume)
        Filter.atTop
        (𝓝 (∫ z in Q,
          (χ z * weakJacobian (df z) *
            fderiv ℝ (φ : ℂ → ℝ) (f z) v) • z ∂volume)) := by
  rcases hgraph.exists_strictMono_approximants_tendsto_ae
      hf.aestronglyMeasurable with ⟨ns, hns, hT_ae⟩
  refine ⟨ns, hns, ?_⟩
  let μ : Measure ℂ := volume.restrict Q
  let T : ℕ → ℂ → ℂ := fun n => hgraph.approximants (ns n)
  let Jn : ℕ → ℂ → ℝ := fun n z =>
    weakJacobian (fderiv ℝ (T n) z)
  let J : ℂ → ℝ := fun z => weakJacobian (df z)
  let dφ : ℂ → ℝ := fun y => fderiv ℝ (φ : ℂ → ℝ) y v
  let c : ℕ → ℂ → ℝ := fun n z => χ z * dφ (T n z)
  let c0 : ℂ → ℝ := fun z => χ z * dφ (f z)
  let err : ℕ → ℂ → ℂ := fun n z => (c n z * (Jn n z - J z)) • z
  let fixed : ℕ → ℂ → ℂ := fun n z => (c n z * J z) • z
  let limit : ℂ → ℂ := fun z => (c0 z * J z) • z
  have hχ_cont : Continuous χ := hχ.continuous
  have hdφ_cont : Continuous dφ := by
    exact (φ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  rcases hQ.exists_bound_of_continuousOn hχ_cont.continuousOn with
    ⟨Cχ0, hCχ0⟩
  rcases hQ.exists_bound_of_continuousOn continuous_id.continuousOn with
    ⟨Cz0, hCz0⟩
  rcases φ.smooth.lipschitzWith_of_hasCompactSupport φ.compact_support
      (by simp) with ⟨Cφ, hφlip⟩
  let Cχ : ℝ := max Cχ0 0
  let Cz : ℝ := max Cz0 0
  let C : ℝ := Cχ * ((Cφ : ℝ) * ‖v‖) * Cz
  have hCχ : ∀ z ∈ Q, ‖χ z‖ ≤ Cχ := fun z hz =>
    (hCχ0 z hz).trans (le_max_left _ _)
  have hCz : ∀ z ∈ Q, ‖z‖ ≤ Cz := fun z hz =>
    (hCz0 z hz).trans (le_max_left _ _)
  have hCχ_nonneg : 0 ≤ Cχ := le_max_right _ _
  have hCz_nonneg : 0 ≤ Cz := le_max_right _ _
  have hdφ_bound (y : ℂ) : |dφ y| ≤ (Cφ : ℝ) * ‖v‖ := by
    rw [← Real.norm_eq_abs]
    exact (fderiv ℝ (φ : ℂ → ℝ) y).le_opNorm v |>.trans
      (mul_le_mul_of_nonneg_right
        (norm_fderiv_le_of_lipschitz (𝕜 := ℝ) hφlip) (norm_nonneg v))
  have hc_bound : ∀ n, ∀ z ∈ Q, |c n z| * ‖z‖ ≤ C := by
    intro n z hz
    have hχz : |χ z| ≤ Cχ := by simpa [Real.norm_eq_abs] using hCχ z hz
    have hφ_nonneg : 0 ≤ (Cφ : ℝ) * ‖v‖ :=
      mul_nonneg Cφ.coe_nonneg (norm_nonneg v)
    calc
      |c n z| * ‖z‖ = (|χ z| * |dφ (T n z)|) * ‖z‖ := by
        simp [c, abs_mul]
      _ ≤ (Cχ * ((Cφ : ℝ) * ‖v‖)) * ‖z‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul hχz (hdφ_bound _) (abs_nonneg _) hCχ_nonneg)
          (norm_nonneg z)
      _ ≤ (Cχ * ((Cφ : ℝ) * ‖v‖)) * Cz := by
        exact mul_le_mul_of_nonneg_left (hCz z hz)
          (mul_nonneg hCχ_nonneg hφ_nonneg)
      _ = C := rfl
  have hJ_int : Integrable J μ := by
    simpa [J, μ] using weakJacobian_integrable_of_memLp_two hdf
  have hbound_int : Integrable (fun z => C * |J z|) μ := by
    simpa only [Real.norm_eq_abs] using hJ_int.norm.const_mul C
  have hfixed_meas : ∀ n, AEStronglyMeasurable (fixed n) μ := by
    intro n
    have hTcont : Continuous (T n) := (hgraph.smooth (ns n)).continuous
    have hccont : Continuous (c n) := hχ_cont.mul (hdφ_cont.comp hTcont)
    have hJmeas : AEStronglyMeasurable J μ := hJ_int.aestronglyMeasurable
    exact ((hccont.aestronglyMeasurable.mul hJmeas).smul
      continuous_id.aestronglyMeasurable)
  have hfixed_bound : ∀ n, ∀ᵐ z ∂μ,
      ‖fixed n z‖ ≤ C * |J z| := by
    intro n
    filter_upwards [ae_restrict_mem hQ.measurableSet] with z hz
    calc
      ‖fixed n z‖ = |c n z| * ‖z‖ * |J z| := by
        simp [fixed, mul_comm, mul_left_comm]
      _ ≤ C * |J z| :=
        mul_le_mul_of_nonneg_right (hc_bound n z hz) (abs_nonneg _)
  have hfixed_tendsto : Filter.Tendsto
      (fun n => ∫ z, fixed n z ∂μ) Filter.atTop
      (𝓝 (∫ z, limit z ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun z => C * |J z|) hfixed_meas hbound_int hfixed_bound
    filter_upwards [hT_ae] with z hz
    have hdφz : Filter.Tendsto (fun n => dφ (T n z))
        Filter.atTop (𝓝 (dφ (f z))) := hdφ_cont.continuousAt.tendsto.comp hz
    have hcz : Filter.Tendsto (fun n => c n z)
        Filter.atTop (𝓝 (c0 z)) := by
      simpa [c, c0] using (Filter.Tendsto.const_mul (χ z) hdφz)
    simpa [fixed, limit] using
      ((hcz.mul tendsto_const_nhds).smul_const z)
  have hJdiff_zero : Filter.Tendsto
      (fun n => ∫ z, |Jn n z - J z| ∂μ)
      Filter.atTop (𝓝 0) := by
    simpa [Jn, J, T, μ] using
      (hgraph.weakJacobian_integral_abs_sub_tendsto_zero hdf).comp
        hns.tendsto_atTop
  have hDT_mem : ∀ n, MemLp (fun z => fderiv ℝ (T n) z) 2 μ := by
    intro n
    have hsum := (hgraph.derivative_error_memLp (ns n)).add hdf
    have heq : (fun z => fderiv ℝ (T n) z) =
        (fun z => fderiv ℝ (hgraph.approximants (ns n)) z - df z) + df := by
      funext z
      simp [T]
    rw [heq]
    simpa [μ] using hsum
  have hJn_int : ∀ n, Integrable (Jn n) μ := by
    intro n
    simpa [Jn] using weakJacobian_integrable_of_memLp_two (hDT_mem n)
  have hJdiff_int : ∀ n, Integrable (fun z => |Jn n z - J z|) μ := by
    intro n
    exact ((hJn_int n).sub hJ_int).abs
  have herr_meas : ∀ n, AEStronglyMeasurable (err n) μ := by
    intro n
    have hTcont : Continuous (T n) := (hgraph.smooth (ns n)).continuous
    have hccont : Continuous (c n) := hχ_cont.mul (hdφ_cont.comp hTcont)
    have hdiff_meas : AEStronglyMeasurable (fun z => Jn n z - J z) μ :=
      (hJn_int n).aestronglyMeasurable.sub hJ_int.aestronglyMeasurable
    exact ((hccont.aestronglyMeasurable.mul hdiff_meas).smul
      continuous_id.aestronglyMeasurable)
  have herr_bound : ∀ n, ∀ᵐ z ∂μ,
      ‖err n z‖ ≤ C * |Jn n z - J z| := by
    intro n
    filter_upwards [ae_restrict_mem hQ.measurableSet] with z hz
    calc
      ‖err n z‖ = |c n z| * ‖z‖ * |Jn n z - J z| := by
        rw [show err n z = (c n z * (Jn n z - J z)) • z by rfl]
        rw [norm_smul, Real.norm_eq_abs, abs_mul]
        ring
      _ ≤ C * |Jn n z - J z| :=
        mul_le_mul_of_nonneg_right (hc_bound n z hz) (abs_nonneg _)
  have herr_int : ∀ n, Integrable (err n) μ := by
    intro n
    exact ((hJdiff_int n).const_mul C).mono' (herr_meas n) (herr_bound n)
  have herr_tendsto : Filter.Tendsto
      (fun n => ∫ z, err n z ∂μ) Filter.atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hmajor_zero : Filter.Tendsto
        (fun n => ∫ z, C * |Jn n z - J z| ∂μ)
        Filter.atTop (𝓝 0) := by
      have ht := Filter.Tendsto.const_mul C hJdiff_zero
      simpa only [integral_const_mul, mul_zero] using ht
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      hmajor_zero (fun n => norm_nonneg _)
      (fun n => norm_integral_le_of_norm_le
        ((hJdiff_int n).const_mul C) (herr_bound n))
  have hsum := herr_tendsto.add hfixed_tendsto
  convert hsum using 1
  · funext n
    rw [← integral_add (herr_int n)
      (hbound_int.mono' (hfixed_meas n) (hfixed_bound n))]
    apply integral_congr_ae
    filter_upwards with z
    simp only [err, fixed, c, Jn, J, T]
    module
  · rw [zero_add]
    congr 1
    apply integral_congr_ae
    filter_upwards with z
    simp only [limit, c0, J, dφ]
    module

/--
%%handwave
name:
  Subsequence convergence of the scalar localized Jacobian term
statement:
  Let $Q\subset\mathbb C$ be compact, let $f,Df\in L^2(Q)$, and let
  smooth maps $T_n:\mathbb C\to\mathbb C$ converge to $(f,Df)$ in the
  $W^{1,2}(Q)$ graph norm. For smooth $\chi$, a smooth compactly supported
  $\varphi$, and $v\in\mathbb C$, there is a strictly increasing sequence
  $n_k$ such that
  $$
    \int_Q\chi(z)J(DT_{n_k}(z))D\varphi(T_{n_k}(z))v\,dz
      \longrightarrow
    \int_Q\chi(z)J(Df(z))D\varphi(f(z))v\,dz.
  $$
proof:
  Choose an almost-everywhere convergent subsequence of the smooth maps.
  The Jacobians converge strongly in $L^1(Q)$, while the remaining
  coefficient is uniformly bounded on $Q$. The part with fixed Jacobian
  converges by dominated convergence.
-/
theorem PlanarWeakSobolevSmoothApproxGraphL2Data.exists_strictMono_scalarMainTerm_integral_tendsto
    {Q : Set ℂ} (hQ : IsCompact Q) {f : ℂ → ℂ}
    {df : ℂ → ℂ →L[ℝ] ℂ}
    (hgraph : PlanarWeakSobolevSmoothApproxGraphL2Data Q f df)
    (hf : MemLp f 2 (volume.restrict Q))
    (hdf : MemLp df 2 (volume.restrict Q))
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    {Ω' : Set ℂ}
    (φ : JJMath.Uniformization.SmoothCompactlySupportedManifoldCoordinateFunction Ω')
    (v : ℂ) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      Filter.Tendsto
        (fun n => ∫ z in Q,
          χ z *
            weakJacobian
              (fderiv ℝ (hgraph.approximants (ns n)) z) *
            fderiv ℝ (φ : ℂ → ℝ)
              (hgraph.approximants (ns n) z) v
          ∂volume)
        Filter.atTop
        (𝓝 (∫ z in Q,
          χ z * weakJacobian (df z) *
            fderiv ℝ (φ : ℂ → ℝ) (f z) v
          ∂volume)) := by
  rcases hgraph.exists_strictMono_approximants_tendsto_ae
      hf.aestronglyMeasurable with
    ⟨ns, hns, hT_ae⟩
  refine ⟨ns, hns, ?_⟩
  let μ : Measure ℂ := volume.restrict Q
  let T : ℕ → ℂ → ℂ := fun n =>
    hgraph.approximants (ns n)
  let Jn : ℕ → ℂ → ℝ := fun n z =>
    weakJacobian (fderiv ℝ (T n) z)
  let J : ℂ → ℝ := fun z => weakJacobian (df z)
  let dφ : ℂ → ℝ := fun y =>
    fderiv ℝ (φ : ℂ → ℝ) y v
  let c : ℕ → ℂ → ℝ := fun n z =>
    χ z * dφ (T n z)
  let c0 : ℂ → ℝ := fun z =>
    χ z * dφ (f z)
  let err : ℕ → ℂ → ℝ := fun n z =>
    c n z * (Jn n z - J z)
  let fixed : ℕ → ℂ → ℝ := fun n z =>
    c n z * J z
  let limit : ℂ → ℝ := fun z =>
    c0 z * J z
  have hχcont : Continuous χ := hχ.continuous
  have hdφcont : Continuous dφ :=
    (φ.smooth.continuous_fderiv (by simp)).clm_apply
      continuous_const
  rcases hQ.exists_bound_of_continuousOn
      hχcont.continuousOn with
    ⟨Cχ0, hCχ0⟩
  rcases φ.smooth.lipschitzWith_of_hasCompactSupport
      φ.compact_support (by simp) with
    ⟨Cφ, hφlip⟩
  let Cχ : ℝ := max Cχ0 0
  let C : ℝ := Cχ * ((Cφ : ℝ) * ‖v‖)
  have hCχ : ∀ z ∈ Q, ‖χ z‖ ≤ Cχ :=
    fun z hz =>
      (hCχ0 z hz).trans (le_max_left _ _)
  have hCχnonneg : 0 ≤ Cχ :=
    le_max_right _ _
  have hdφbound (y : ℂ) :
      |dφ y| ≤ (Cφ : ℝ) * ‖v‖ := by
    rw [← Real.norm_eq_abs]
    exact
      ((fderiv ℝ (φ : ℂ → ℝ) y).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right
          (norm_fderiv_le_of_lipschitz
            (𝕜 := ℝ) hφlip)
          (norm_nonneg v))
  have hcbound : ∀ n, ∀ z ∈ Q,
      |c n z| ≤ C := by
    intro n z hz
    have hχz : |χ z| ≤ Cχ := by
      simpa [Real.norm_eq_abs] using hCχ z hz
    calc
      |c n z| =
          |χ z| * |dφ (T n z)| := by
        simp [c, abs_mul]
      _ ≤ Cχ * ((Cφ : ℝ) * ‖v‖) :=
        mul_le_mul hχz (hdφbound _)
          (abs_nonneg _) hCχnonneg
      _ = C := rfl
  have hJint : Integrable J μ := by
    simpa [J, μ] using
      weakJacobian_integrable_of_memLp_two hdf
  have hboundInt :
      Integrable (fun z => C * |J z|) μ := by
    simpa only [Real.norm_eq_abs] using
      hJint.norm.const_mul C
  have hfixedMeas :
      ∀ n, AEStronglyMeasurable (fixed n) μ := by
    intro n
    have hTcont : Continuous (T n) :=
      (hgraph.smooth (ns n)).continuous
    have hccont : Continuous (c n) :=
      hχcont.mul (hdφcont.comp hTcont)
    exact hccont.aestronglyMeasurable.mul
      hJint.aestronglyMeasurable
  have hfixedBound :
      ∀ n, ∀ᵐ z ∂μ,
        ‖fixed n z‖ ≤ C * |J z| := by
    intro n
    filter_upwards
      [ae_restrict_mem hQ.measurableSet] with z hz
    rw [Real.norm_eq_abs, abs_mul]
    exact
      mul_le_mul_of_nonneg_right
        (hcbound n z hz) (abs_nonneg _)
  have hfixedTendsto :
      Filter.Tendsto
        (fun n => ∫ z, fixed n z ∂μ)
        Filter.atTop
        (𝓝 (∫ z, limit z ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun z => C * |J z|) hfixedMeas
      hboundInt hfixedBound
    filter_upwards [hT_ae] with z hz
    have hdφz :
        Filter.Tendsto
          (fun n => dφ (T n z))
          Filter.atTop (𝓝 (dφ (f z))) :=
      hdφcont.continuousAt.tendsto.comp hz
    have hcz :
        Filter.Tendsto (fun n => c n z)
          Filter.atTop (𝓝 (c0 z)) := by
      simpa [c, c0] using
        Filter.Tendsto.const_mul (χ z) hdφz
    simpa [fixed, limit] using
      hcz.mul_const (J z)
  have hJdiffZero :
      Filter.Tendsto
        (fun n => ∫ z, |Jn n z - J z| ∂μ)
        Filter.atTop (𝓝 0) := by
    simpa [Jn, J, T, μ] using
      (hgraph.weakJacobian_integral_abs_sub_tendsto_zero
        hdf).comp hns.tendsto_atTop
  have hDTmem :
      ∀ n, MemLp
        (fun z => fderiv ℝ (T n) z) 2 μ := by
    intro n
    have hsum :=
      (hgraph.derivative_error_memLp (ns n)).add hdf
    have heq :
        (fun z => fderiv ℝ (T n) z) =
          (fun z =>
            fderiv ℝ
              (hgraph.approximants (ns n)) z - df z) +
            df := by
      funext z
      simp [T]
    rw [heq]
    simpa [μ] using hsum
  have hJnInt : ∀ n, Integrable (Jn n) μ := by
    intro n
    simpa [Jn] using
      weakJacobian_integrable_of_memLp_two (hDTmem n)
  have hJdiffInt :
      ∀ n, Integrable
        (fun z => |Jn n z - J z|) μ := by
    intro n
    exact ((hJnInt n).sub hJint).abs
  have herrMeas :
      ∀ n, AEStronglyMeasurable (err n) μ := by
    intro n
    have hTcont : Continuous (T n) :=
      (hgraph.smooth (ns n)).continuous
    have hccont : Continuous (c n) :=
      hχcont.mul (hdφcont.comp hTcont)
    exact hccont.aestronglyMeasurable.mul
      ((hJnInt n).aestronglyMeasurable.sub
        hJint.aestronglyMeasurable)
  have herrBound :
      ∀ n, ∀ᵐ z ∂μ,
        ‖err n z‖ ≤ C * |Jn n z - J z| := by
    intro n
    filter_upwards
      [ae_restrict_mem hQ.measurableSet] with z hz
    rw [Real.norm_eq_abs, abs_mul]
    exact
      mul_le_mul_of_nonneg_right
        (hcbound n z hz) (abs_nonneg _)
  have herrInt : ∀ n, Integrable (err n) μ := by
    intro n
    exact ((hJdiffInt n).const_mul C).mono'
      (herrMeas n) (herrBound n)
  have herrTendsto :
      Filter.Tendsto
        (fun n => ∫ z, err n z ∂μ)
        Filter.atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hmajorZero :
        Filter.Tendsto
          (fun n =>
            ∫ z, C * |Jn n z - J z| ∂μ)
          Filter.atTop (𝓝 0) := by
      have ht :=
        Filter.Tendsto.const_mul C hJdiffZero
      simpa only [integral_const_mul, mul_zero] using ht
    exact
      tendsto_of_tendsto_of_tendsto_of_le_of_le
        tendsto_const_nhds hmajorZero
        (fun _ => norm_nonneg _)
        (fun n =>
          norm_integral_le_of_norm_le
            ((hJdiffInt n).const_mul C)
            (herrBound n))
  have hsum := herrTendsto.add hfixedTendsto
  convert hsum using 1
  · funext n
    rw [← integral_add (herrInt n)
      (hboundInt.mono'
        (hfixedMeas n) (hfixedBound n))]
    apply integral_congr_ae
    filter_upwards with z
    simp [err, fixed, c, Jn, J, T]
    ring
  · rw [zero_add]
    congr 1
    apply integral_congr_ae
    filter_upwards with z
    simp [limit, c0, J, dφ]
    ring


/--
%%handwave
name:
  Strong convergence of the localized adjugate side
statement:
  Let $Q\subset\mathbb C$ be compact, let $f,Df\in L^2(Q)$, and let
  smooth maps $T_n:\mathbb C\to\mathbb C$ converge to $(f,Df)$ in the
  $W^{1,2}(Q)$ graph norm. For a smooth function
  $\chi:\mathbb C\to\mathbb R$, a smooth compactly supported function
  $\varphi$, and $v\in\mathbb C$,
  $$
    \int_Q \chi(z)\varphi(T_n(z))\operatorname{adj}(DT_n(z))v\,dz
      \longrightarrow
    \int_Q \chi(z)\varphi(f(z))\operatorname{adj}(Df(z))v\,dz.
  $$
proof:
  Split $DT_n=(DT_n-Df)+Df$ and
  $\varphi(T_n)=\bigl(\varphi(T_n)-\varphi(f)\bigr)+\varphi(f)$.
  Multiplication by $\chi$ and application of the planar adjugate to $v$
  preserve strong $L^2$ convergence on $Q$. The three resulting error terms
  vanish by the two strong and bounded-strong $L^2$ pairing estimates,
  including [vanishing when the vector factor converges strongly](lean:JJMath.Quasiconformal.integral_smul_tendsto_zero_of_L2_bounded_of_L2_tendsto_zero).
-/
theorem PlanarWeakSobolevSmoothApproxGraphL2Data.adjugateSide_integral_tendsto
    {Q : Set ℂ} (hQ : IsCompact Q) {f : ℂ → ℂ}
    {df : ℂ → ℂ →L[ℝ] ℂ}
    (hgraph : PlanarWeakSobolevSmoothApproxGraphL2Data Q f df)
    (hf : MemLp f 2 (volume.restrict Q))
    (hdf : MemLp df 2 (volume.restrict Q))
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    {Ω' : Set ℂ}
    (φ : JJMath.Uniformization.SmoothCompactlySupportedManifoldCoordinateFunction Ω')
    (v : ℂ) :
    Filter.Tendsto
      (fun n => ∫ z in Q,
        (χ z * φ (hgraph.approximants n z)) •
          realLinearAdjugate (fderiv ℝ (hgraph.approximants n) z) v
        ∂volume)
      Filter.atTop
      (𝓝 (∫ z in Q,
        (χ z * φ (f z)) • realLinearAdjugate (df z) v ∂volume)) := by
  let μ : Measure ℂ := volume.restrict Q
  let a : ℕ → ℂ → ℝ := fun n z =>
    φ (hgraph.approximants n z) - φ (f z)
  let E : ℕ → ℂ → ℂ →L[ℝ] ℂ := fun n z =>
    fderiv ℝ (hgraph.approximants n) z - df z
  let berr : ℕ → ℂ → ℂ := fun n z =>
    χ z • realLinearAdjugate (E n z) v
  let bfix : ℂ → ℂ := fun z => χ z • realLinearAdjugate (df z) v
  let φf : ℂ → ℝ := fun z => φ (f z)
  let limit : ℂ → ℂ := fun z => φf z • bfix z
  have ha := hgraph.testFunction_comp_sub_tendsto_l2
    hf.aestronglyMeasurable φ
  have hχ_cont : Continuous χ := hχ.continuous
  rcases hQ.exists_bound_of_continuousOn hχ_cont.continuousOn with
    ⟨Cχ0, hCχ0⟩
  let Cχ : ℝ := max Cχ0 0
  let C : ℝ := Cχ * ‖v‖
  have hCχ : ∀ z ∈ Q, ‖χ z‖ ≤ Cχ := fun z hz =>
    (hCχ0 z hz).trans (le_max_left _ _)
  have hCχ_nonneg : 0 ≤ Cχ := le_max_right _ _
  have hE_mem : ∀ n, MemLp (E n) 2 μ := by
    simpa [E, μ] using hgraph.derivative_error_memLp
  have hE_zero : Filter.Tendsto (fun n => eLpNorm (E n) 2 μ)
      Filter.atTop (𝓝 0) := by
    simpa [E, μ] using hgraph.derivative_tendsto_l2
  have hberr_meas : ∀ n, AEStronglyMeasurable (berr n) μ := by
    intro n
    have hAdj : AEStronglyMeasurable (fun z => realLinearAdjugate (E n z)) μ :=
      continuous_realLinearAdjugate.comp_aestronglyMeasurable
        (hE_mem n).aestronglyMeasurable
    exact hχ_cont.aestronglyMeasurable.smul (hAdj.apply_continuousLinearMap v)
  have hberr_bound : ∀ n, ∀ᵐ z ∂μ,
      ‖berr n z‖ ≤ C * ‖E n z‖ := by
    intro n
    filter_upwards [ae_restrict_mem hQ.measurableSet] with z hz
    calc
      ‖berr n z‖ = ‖χ z‖ * ‖realLinearAdjugate (E n z) v‖ := by
        simp [berr]
      _ ≤ ‖χ z‖ * (‖realLinearAdjugate (E n z)‖ * ‖v‖) := by
        exact mul_le_mul_of_nonneg_left
          ((realLinearAdjugate (E n z)).le_opNorm v) (norm_nonneg _)
      _ = ‖χ z‖ * (‖E n z‖ * ‖v‖) := by
        rw [norm_realLinearAdjugate]
      _ ≤ Cχ * (‖E n z‖ * ‖v‖) := by
        exact mul_le_mul_of_nonneg_right (hCχ z hz)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = C * ‖E n z‖ := by
        simp only [C]
        ring
  have hberr := memLp_and_tendsto_zero_of_norm_le_mul hE_mem
    hberr_meas hberr_bound hE_zero
  have hbfix_meas : AEStronglyMeasurable bfix μ := by
    have hAdj : AEStronglyMeasurable (fun z => realLinearAdjugate (df z)) μ :=
      continuous_realLinearAdjugate.comp_aestronglyMeasurable
        hdf.aestronglyMeasurable
    exact hχ_cont.aestronglyMeasurable.smul (hAdj.apply_continuousLinearMap v)
  have hbfix_bound : ∀ᵐ z ∂μ, ‖bfix z‖ ≤ C * ‖df z‖ := by
    filter_upwards [ae_restrict_mem hQ.measurableSet] with z hz
    calc
      ‖bfix z‖ = ‖χ z‖ * ‖realLinearAdjugate (df z) v‖ := by
        simp [bfix]
      _ ≤ ‖χ z‖ * (‖realLinearAdjugate (df z)‖ * ‖v‖) := by
        exact mul_le_mul_of_nonneg_left
          ((realLinearAdjugate (df z)).le_opNorm v) (norm_nonneg _)
      _ = ‖χ z‖ * (‖df z‖ * ‖v‖) := by
        rw [norm_realLinearAdjugate]
      _ ≤ Cχ * (‖df z‖ * ‖v‖) := by
        exact mul_le_mul_of_nonneg_right (hCχ z hz)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = C * ‖df z‖ := by
        simp only [C]
        ring
  have hbfix : MemLp bfix 2 μ := hdf.of_le_mul hbfix_meas hbfix_bound
  haveI : IsFiniteMeasure μ := isFiniteMeasure_restrict.2 hQ.measure_ne_top
  rcases φ.smooth.lipschitzWith_of_hasCompactSupport φ.compact_support
      (by simp) with ⟨Cφ, hφlip⟩
  have hφshift : MemLp (fun z => φ (f z) - φ 0) 2 μ := by
    have hlip : LipschitzWith Cφ (fun y : ℂ => φ y - φ 0) := by
      intro x y
      simpa using hφlip x y
    simpa [Function.comp_def] using hlip.comp_memLp (by simp) hf
  have hφf : MemLp φf 2 μ := by
    have hsum := hφshift.add (memLp_const (μ := μ) (p := 2) (φ 0))
    have heq : φf =
        (fun z => φ (f z) - φ 0) + (fun _ : ℂ => φ 0) := by
      funext z
      simp [φf]
    rw [heq]
    exact hsum
  have h_a_berr : Filter.Tendsto
      (fun n => ∫ z, a n z • berr n z ∂μ) Filter.atTop (𝓝 0) :=
    integral_smul_tendsto_zero_of_L2_tendsto_zero
      (by simpa [a, μ] using ha.1) hberr.1
      (by simpa [a, μ] using ha.2) hberr.2
  have h_a_bfix : Filter.Tendsto
      (fun n => ∫ z, a n z • bfix z ∂μ) Filter.atTop (𝓝 0) := by
    apply integral_smul_tendsto_zero_of_L2_tendsto_zero_of_L2_bounded
      (by simpa [a, μ] using ha.1) (fun _ => hbfix)
      (by simpa [a, μ] using ha.2)
    exact ⟨eLpNorm bfix 2 μ, ne_of_lt hbfix.eLpNorm_lt_top,
      fun _ => le_rfl⟩
  have h_φf_berr : Filter.Tendsto
      (fun n => ∫ z, φf z • berr n z ∂μ) Filter.atTop (𝓝 0) := by
    apply integral_smul_tendsto_zero_of_L2_bounded_of_L2_tendsto_zero
      (fun _ => hφf) hberr.1
    · exact ⟨eLpNorm φf 2 μ, ne_of_lt hφf.eLpNorm_lt_top,
        fun _ => le_rfl⟩
    · exact hberr.2
  have hsum := ((h_a_berr.add h_a_bfix).add h_φf_berr).add
    (tendsto_const_nhds : Filter.Tendsto
      (fun _ : ℕ => ∫ z, limit z ∂μ) Filter.atTop
      (𝓝 (∫ z, limit z ∂μ)))
  convert hsum using 1
  · funext n
    have hi1 : Integrable (fun z => a n z • berr n z) μ := by
      apply memLp_one_iff_integrable.mp
      exact MemLp.smul (p := 2) (q := 2) (r := 1) (hberr.1 n)
        (by simpa [a, μ] using ha.1 n)
    have hi2 : Integrable (fun z => a n z • bfix z) μ := by
      apply memLp_one_iff_integrable.mp
      exact MemLp.smul (p := 2) (q := 2) (r := 1) hbfix
        (by simpa [a, μ] using ha.1 n)
    have hi3 : Integrable (fun z => φf z • berr n z) μ := by
      apply memLp_one_iff_integrable.mp
      exact MemLp.smul (p := 2) (q := 2) (r := 1) (hberr.1 n) hφf
    have hi4 : Integrable limit μ := by
      apply memLp_one_iff_integrable.mp
      exact MemLp.smul (p := 2) (q := 2) (r := 1) hbfix hφf
    change (∫ z,
      (χ z * φ (hgraph.approximants n z)) •
        realLinearAdjugate (fderiv ℝ (hgraph.approximants n) z) v ∂μ) = _
    calc
      _ = ∫ z, ((a n z • berr n z + a n z • bfix z) +
          φf z • berr n z) + limit z ∂μ := by
        apply integral_congr_ae
        filter_upwards with z
        have hAdj : realLinearAdjugate
            (fderiv ℝ (hgraph.approximants n) z) v =
              realLinearAdjugate (E n z) v + realLinearAdjugate (df z) v := by
          have hsplit : fderiv ℝ (hgraph.approximants n) z = E n z + df z := by
            simp [E]
          rw [hsplit]
          apply Complex.ext <;>
            simp [realLinearAdjugate, realLinearMapOfWirtinger, weakDZ, weakDBar] <;>
            ring
        rw [hAdj]
        simp only [a, berr, bfix, φf, limit, smul_add]
        module
      _ = (∫ z, (a n z • berr n z + a n z • bfix z) +
          φf z • berr n z ∂μ) + ∫ z, limit z ∂μ :=
        integral_add ((hi1.add hi2).add hi3) hi4
      _ = ((∫ z, a n z • berr n z + a n z • bfix z ∂μ) +
          ∫ z, φf z • berr n z ∂μ) + ∫ z, limit z ∂μ := by
        congr 1
        simpa only [Pi.add_apply] using integral_add (hi1.add hi2) hi3
      _ = (((∫ z, a n z • berr n z ∂μ) +
          ∫ z, a n z • bfix z ∂μ) +
          ∫ z, φf z • berr n z ∂μ) + ∫ z, limit z ∂μ := by
        congr 2
        simpa only [Pi.add_apply] using integral_add hi1 hi2
  · simp only [zero_add]
    change (𝓝 (∫ z,
      (χ z * φ (f z)) • realLinearAdjugate (df z) v ∂μ)) =
        𝓝 (∫ z, limit z ∂μ)
    congr 1
    apply integral_congr_ae
    filter_upwards with z
    simp only [limit, bfix, φf]
    module


/--
%%handwave
name:
  Smooth Cartesian Piola integration by parts
statement:
  Let $\psi,A,B:\mathbb C\to\mathbb R$ be smooth, with $\psi$ compactly
  supported, and suppose
  $$
    \partial_1 A(z)+\partial_i B(z)=0
  $$
  for every $z\in\mathbb C$. Then
  $$
    \int_{\mathbb C}
      \bigl(\partial_1\psi(z)A(z)+\partial_i\psi(z)B(z)\bigr)z\,dz
    =-\int_{\mathbb C}\psi(z)\bigl(A(z)+iB(z)\bigr)\,dz.
  $$
proof:
  Integrate the $A$ term by parts in the real direction and the $B$ term in
  the imaginary direction. Differentiating $A(z)z$ and $B(z)z$ produces the
  displayed right-hand side and the extra term
  $\psi(z)(\partial_1A(z)+\partial_iB(z))z$, which vanishes by hypothesis.
-/
theorem integral_cartesianPiola_of_contDiff
    {ψ A B : ℂ → ℝ}
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A)
    (hB : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) B)
    (hψc : HasCompactSupport ψ)
    (hdiv : ∀ z : ℂ,
      fderiv ℝ A z (1 : ℂ) + fderiv ℝ B z Complex.I = 0) :
    ∫ z : ℂ,
        (fderiv ℝ ψ z (1 : ℂ) * A z +
          fderiv ℝ ψ z Complex.I * B z) • z ∂volume =
      -∫ z : ℂ, ψ z • ((A z : ℂ) + Complex.I * (B z : ℂ)) ∂volume := by
  let gA : ℂ → ℂ := fun z => A z • z
  let gB : ℂ → ℂ := fun z => B z • z
  have hgA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) gA := by
    simpa [gA] using hA.smul
      (contDiff_id : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (id : ℂ → ℂ))
  have hgB : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) gB := by
    simpa [gB] using hB.smul
      (contDiff_id : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (id : ℂ → ℂ))
  have hdψ1c : HasCompactSupport (fun z : ℂ => fderiv ℝ ψ z (1 : ℂ)) :=
    hψc.fderiv_apply (𝕜 := ℝ) (1 : ℂ)
  have hdψIc : HasCompactSupport (fun z : ℂ => fderiv ℝ ψ z Complex.I) :=
    hψc.fderiv_apply (𝕜 := ℝ) Complex.I
  have hψcont : Continuous ψ := hψ.continuous
  have hgAcont : Continuous gA := hgA.continuous
  have hgBcont : Continuous gB := hgB.continuous
  have hdψ1cont : Continuous (fun z : ℂ => fderiv ℝ ψ z (1 : ℂ)) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdψIcont : Continuous (fun z : ℂ => fderiv ℝ ψ z Complex.I) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdgA1cont : Continuous (fun z : ℂ => fderiv ℝ gA z (1 : ℂ)) :=
    (hgA.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdgBIcont : Continuous (fun z : ℂ => fderiv ℝ gB z Complex.I) :=
    (hgB.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdψ1gA_int :
      Integrable (fun z : ℂ => fderiv ℝ ψ z (1 : ℂ) • gA z) volume :=
    (hdψ1cont.smul hgAcont).integrable_of_hasCompactSupport hdψ1c.smul_right
  have hψdgA1_int :
      Integrable (fun z : ℂ => ψ z • fderiv ℝ gA z (1 : ℂ)) volume :=
    (hψcont.smul hdgA1cont).integrable_of_hasCompactSupport hψc.smul_right
  have hdψIgB_int :
      Integrable (fun z : ℂ => fderiv ℝ ψ z Complex.I • gB z) volume :=
    (hdψIcont.smul hgBcont).integrable_of_hasCompactSupport hdψIc.smul_right
  have hψdgBI_int :
      Integrable (fun z : ℂ => ψ z • fderiv ℝ gB z Complex.I) volume :=
    (hψcont.smul hdgBIcont).integrable_of_hasCompactSupport hψc.smul_right
  have hA_ibp :
      ∫ z : ℂ, ψ z • fderiv ℝ gA z (1 : ℂ) ∂volume =
        -∫ z : ℂ, fderiv ℝ ψ z (1 : ℂ) • gA z ∂volume := by
    apply integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
    · exact hdψ1gA_int
    · exact hψdgA1_int
    · exact (hψcont.smul hgAcont).integrable_of_hasCompactSupport
          hψc.smul_right
    · intro z _
      exact hψ.differentiable (by simp) z
    · intro z _
      exact hgA.differentiable (by simp) z
  have hB_ibp :
      ∫ z : ℂ, ψ z • fderiv ℝ gB z Complex.I ∂volume =
        -∫ z : ℂ, fderiv ℝ ψ z Complex.I • gB z ∂volume := by
    apply integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
    · exact hdψIgB_int
    · exact hψdgBI_int
    · exact (hψcont.smul hgBcont).integrable_of_hasCompactSupport
          hψc.smul_right
    · intro z _
      exact hψ.differentiable (by simp) z
    · intro z _
      exact hgB.differentiable (by simp) z
  have hdgA (z : ℂ) :
      fderiv ℝ gA z (1 : ℂ) =
        (A z : ℂ) + (fderiv ℝ A z (1 : ℂ)) • z := by
    rw [show gA = fun w : ℂ => A w • id w by rfl]
    rw [fderiv_fun_smul (hA.differentiable (by simp) z) differentiableAt_id]
    simp
  have hdgB (z : ℂ) :
      fderiv ℝ gB z Complex.I =
        Complex.I * (B z : ℂ) + (fderiv ℝ B z Complex.I) • z := by
    rw [show gB = fun w : ℂ => B w • id w by rfl]
    rw [fderiv_fun_smul (hB.differentiable (by simp) z) differentiableAt_id]
    simp [mul_comm]
  have hA_rev :
      ∫ z : ℂ, fderiv ℝ ψ z (1 : ℂ) • gA z ∂volume =
        -∫ z : ℂ, ψ z • fderiv ℝ gA z (1 : ℂ) ∂volume := by
    simpa using (congrArg Neg.neg hA_ibp).symm
  have hB_rev :
      ∫ z : ℂ, fderiv ℝ ψ z Complex.I • gB z ∂volume =
        -∫ z : ℂ, ψ z • fderiv ℝ gB z Complex.I ∂volume := by
    simpa using (congrArg Neg.neg hB_ibp).symm
  calc
    ∫ z : ℂ,
        (fderiv ℝ ψ z (1 : ℂ) * A z +
          fderiv ℝ ψ z Complex.I * B z) • z ∂volume =
        ∫ z : ℂ,
          (fderiv ℝ ψ z (1 : ℂ) • gA z +
            fderiv ℝ ψ z Complex.I • gB z) ∂volume := by
          apply integral_congr_ae
          filter_upwards [] with z
          simp [gA, gB, add_smul, mul_smul]
    _ = (∫ z : ℂ, fderiv ℝ ψ z (1 : ℂ) • gA z ∂volume) +
        ∫ z : ℂ, fderiv ℝ ψ z Complex.I • gB z ∂volume :=
      integral_add hdψ1gA_int hdψIgB_int
    _ = -((∫ z : ℂ, ψ z • fderiv ℝ gA z (1 : ℂ) ∂volume) +
        ∫ z : ℂ, ψ z • fderiv ℝ gB z Complex.I ∂volume) := by
      rw [hA_rev, hB_rev]
      abel
    _ = -∫ z : ℂ,
        (ψ z • fderiv ℝ gA z (1 : ℂ) +
          ψ z • fderiv ℝ gB z Complex.I) ∂volume := by
      rw [integral_add hψdgA1_int hψdgBI_int]
    _ = -∫ z : ℂ, ψ z • ((A z : ℂ) + Complex.I * (B z : ℂ)) ∂volume := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with z
      rw [← smul_add, hdgA, hdgB]
      congr 1
      have hz := congrArg (fun r : ℝ => r • z) (hdiv z)
      simp only [zero_smul] at hz
      rw [add_smul] at hz
      linear_combination hz

/--
%%handwave
name:
  Divergence-free adjugate field of a smooth planar map
statement:
  Let $T:\mathbb C\to\mathbb C$ be smooth and let $v\in\mathbb C$. If
  $$
    A(z)=\operatorname{Re}(\operatorname{adj}(DT(z))v),\qquad
    B(z)=\operatorname{Im}(\operatorname{adj}(DT(z))v),
  $$
  then
  $$
    \partial_1 A(z)+\partial_i B(z)=0
  $$
  for every $z\in\mathbb C$.
proof:
  Expand the two adjugate components in the coordinate columns $DT(1)$ and
  $DT(i)$. After differentiation, the coefficient of
  $\operatorname{Re}v$ and the coefficient of $\operatorname{Im}v$ both
  vanish by symmetry of the second Fréchet derivative of $T$.
-/
theorem realLinearAdjugate_fderiv_divergence
    {T : ℂ → ℂ} (hT : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) T) (v z : ℂ) :
    fderiv ℝ
        (fun w : ℂ => (realLinearAdjugate (fderiv ℝ T w) v).re) z (1 : ℂ) +
      fderiv ℝ
        (fun w : ℂ => (realLinearAdjugate (fderiv ℝ T w) v).im) z Complex.I = 0 := by
  let T1 : ℂ → ℂ := fun w => fderiv ℝ T w (1 : ℂ)
  let TI : ℂ → ℂ := fun w => fderiv ℝ T w Complex.I
  have hDT : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ T) :=
    hT.fderiv_right (by simp)
  have hT1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) T1 := by
    simpa [T1] using hDT.clm_apply (contDiff_const :
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : ℂ => (1 : ℂ)))
  have hTI : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) TI := by
    simpa [TI] using hDT.clm_apply (contDiff_const :
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : ℂ => Complex.I))
  have hT1diff : DifferentiableAt ℝ T1 z :=
    hT1.differentiable (by simp) z
  have hTIdiff : DifferentiableAt ℝ TI z :=
    hTI.differentiable (by simp) z
  have hT1re : DifferentiableAt ℝ (fun w => (T1 w).re) z :=
    Complex.reCLM.differentiableAt.comp z hT1diff
  have hT1im : DifferentiableAt ℝ (fun w => (T1 w).im) z :=
    Complex.imCLM.differentiableAt.comp z hT1diff
  have hTIre : DifferentiableAt ℝ (fun w => (TI w).re) z :=
    Complex.reCLM.differentiableAt.comp z hTIdiff
  have hTIim : DifferentiableAt ℝ (fun w => (TI w).im) z :=
    Complex.imCLM.differentiableAt.comp z hTIdiff
  have hEval (e : ℂ) :
      fderiv ℝ (fun w : ℂ => fderiv ℝ T w e) z =
        (fderiv ℝ (fderiv ℝ T) z).flip e := by
    rw [fderiv_clm_apply (hDT.differentiable (by simp) z)
      (differentiableAt_const e)]
    ext u
    simp [ContinuousLinearMap.flip_apply]
  have hmix : fderiv ℝ TI z (1 : ℂ) = fderiv ℝ T1 z Complex.I := by
    rw [show TI = fun w : ℂ => fderiv ℝ T w Complex.I by rfl]
    rw [show T1 = fun w : ℂ => fderiv ℝ T w (1 : ℂ) by rfl]
    rw [hEval Complex.I, hEval (1 : ℂ)]
    simpa [ContinuousLinearMap.flip_apply] using
      (hT.contDiffAt.isSymmSndFDerivAt (by
        rw [minSmoothness_of_isRCLikeNormedField (𝕜 := ℝ)]
        exact WithTop.coe_le_coe.2 le_top)).eq (1 : ℂ) Complex.I
  have hmix_re :
      fderiv ℝ (fun w => (TI w).re) z (1 : ℂ) =
        fderiv ℝ (fun w => (T1 w).re) z Complex.I := by
    have hleft := (Complex.reCLM.hasFDerivAt.comp z hTIdiff.hasFDerivAt).fderiv
    have hright := (Complex.reCLM.hasFDerivAt.comp z hT1diff.hasFDerivAt).fderiv
    calc
      fderiv ℝ (fun w => (TI w).re) z (1 : ℂ) =
          (fderiv ℝ TI z (1 : ℂ)).re := by
        simpa [Function.comp_def, ContinuousLinearMap.comp_apply] using
          congrArg (fun L : ℂ →L[ℝ] ℝ => L (1 : ℂ)) hleft
      _ = (fderiv ℝ T1 z Complex.I).re := congrArg Complex.re hmix
      _ = fderiv ℝ (fun w => (T1 w).re) z Complex.I := by
        simpa [Function.comp_def, ContinuousLinearMap.comp_apply] using
          (congrArg (fun L : ℂ →L[ℝ] ℝ => L Complex.I) hright).symm
  have hmix_im :
      fderiv ℝ (fun w => (TI w).im) z (1 : ℂ) =
        fderiv ℝ (fun w => (T1 w).im) z Complex.I := by
    have hleft := (Complex.imCLM.hasFDerivAt.comp z hTIdiff.hasFDerivAt).fderiv
    have hright := (Complex.imCLM.hasFDerivAt.comp z hT1diff.hasFDerivAt).fderiv
    calc
      fderiv ℝ (fun w => (TI w).im) z (1 : ℂ) =
          (fderiv ℝ TI z (1 : ℂ)).im := by
        simpa [Function.comp_def, ContinuousLinearMap.comp_apply] using
          congrArg (fun L : ℂ →L[ℝ] ℝ => L (1 : ℂ)) hleft
      _ = (fderiv ℝ T1 z Complex.I).im := congrArg Complex.im hmix
      _ = fderiv ℝ (fun w => (T1 w).im) z Complex.I := by
        simpa [Function.comp_def, ContinuousLinearMap.comp_apply] using
          (congrArg (fun L : ℂ →L[ℝ] ℝ => L Complex.I) hright).symm
  rw [funext fun w => real_part_realLinearAdjugate_apply (fderiv ℝ T w) v]
  rw [funext fun w => imag_part_realLinearAdjugate_apply (fderiv ℝ T w) v]
  change fderiv ℝ (fun w => (TI w).im * v.re - (TI w).re * v.im) z (1 : ℂ) +
    fderiv ℝ (fun w => -(T1 w).im * v.re + (T1 w).re * v.im) z Complex.I = 0
  have hAreorder :
      (fun w => (TI w).im * v.re - (TI w).re * v.im) =
        fun w => v.re * (TI w).im - v.im * (TI w).re := by
    funext w
    ring
  have hBreorder :
      (fun w => -(T1 w).im * v.re + (T1 w).re * v.im) =
        fun w => -(v.re * (T1 w).im) + v.im * (T1 w).re := by
    funext w
    ring
  rw [hAreorder, hBreorder]
  change
    (fderiv ℝ
      ((fun w : ℂ => v.re * (TI w).im) - fun w : ℂ => v.im * (TI w).re) z)
        (1 : ℂ) +
      (fderiv ℝ
        (-(fun w : ℂ => v.re * (T1 w).im) +
          fun w : ℂ => v.im * (T1 w).re) z) Complex.I = 0
  rw [fderiv_sub (hTIim.const_mul v.re) (hTIre.const_mul v.im)]
  rw [fderiv_add ((hT1im.const_mul v.re).neg) (hT1re.const_mul v.im)]
  rw [fderiv_const_mul hTIim v.re]
  rw [fderiv_const_mul hTIre v.im]
  rw [fderiv_neg]
  rw [fderiv_const_mul hT1im v.re]
  rw [fderiv_const_mul hT1re v.im]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [hmix_re, hmix_im]
  ring

/--
%%handwave
name:
  Scalar planar Piola identity
statement:
  Let $T:\mathbb C\to\mathbb C$ and
  $\psi:\mathbb C\to\mathbb R$ be smooth, with $\psi$ compactly supported.
  For every $v\in\mathbb C$,
  $$
    \int_{\mathbb C}
      D\psi(z)\bigl(\operatorname{adj}(DT(z))v\bigr)\,dz=0.
  $$
proof:
  Resolve the adjugate vector into its real and imaginary components and
  integrate the two directional derivatives by parts. The remaining
  integrand is $\psi$ times the divergence of
  $\operatorname{adj}(DT)v$, which vanishes by the planar Piola identity.
-/
theorem integral_fderiv_realLinearAdjugate_eq_zero_of_contDiff
    {ψ : ℂ → ℝ} {T : ℂ → ℂ}
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hT : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) T)
    (hψc : HasCompactSupport ψ) (v : ℂ) :
    ∫ z : ℂ,
        fderiv ℝ ψ z
          (realLinearAdjugate (fderiv ℝ T z) v) ∂volume = 0 := by
  let A : ℂ → ℝ := fun z =>
    (realLinearAdjugate (fderiv ℝ T z) v).re
  let B : ℂ → ℝ := fun z =>
    (realLinearAdjugate (fderiv ℝ T z) v).im
  have hDT : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ T) :=
    hT.fderiv_right (by simp)
  have hDTI : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => fderiv ℝ T z Complex.I) :=
    hDT.clm_apply contDiff_const
  have hDT1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => fderiv ℝ T z (1 : ℂ)) :=
    hDT.clm_apply contDiff_const
  have hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A := by
    rw [show A = fun z =>
      (fderiv ℝ T z Complex.I).im * v.re -
        (fderiv ℝ T z Complex.I).re * v.im by
      funext z
      exact real_part_realLinearAdjugate_apply (fderiv ℝ T z) v]
    exact ((Complex.imCLM.contDiff.comp hDTI).mul contDiff_const).sub
      ((Complex.reCLM.contDiff.comp hDTI).mul contDiff_const)
  have hB : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) B := by
    rw [show B = fun z =>
      -(fderiv ℝ T z (1 : ℂ)).im * v.re +
        (fderiv ℝ T z (1 : ℂ)).re * v.im by
      funext z
      exact imag_part_realLinearAdjugate_apply (fderiv ℝ T z) v]
    exact ((Complex.imCLM.contDiff.comp hDT1).neg.mul
      (contDiff_const : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun _ : ℂ => v.re))).add
      ((Complex.reCLM.contDiff.comp hDT1).mul
        (contDiff_const : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun _ : ℂ => v.im)))
  have hψcont : Continuous ψ := hψ.continuous
  have hAcont : Continuous A := hA.continuous
  have hBcont : Continuous B := hB.continuous
  have hdψ1cont : Continuous
      (fun z : ℂ => fderiv ℝ ψ z (1 : ℂ)) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdψIcont : Continuous
      (fun z : ℂ => fderiv ℝ ψ z Complex.I) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdA1cont : Continuous
      (fun z : ℂ => fderiv ℝ A z (1 : ℂ)) :=
    (hA.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdBIcont : Continuous
      (fun z : ℂ => fderiv ℝ B z Complex.I) :=
    (hB.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdψ1c :
      HasCompactSupport (fun z : ℂ => fderiv ℝ ψ z (1 : ℂ)) :=
    hψc.fderiv_apply (𝕜 := ℝ) (1 : ℂ)
  have hdψIc :
      HasCompactSupport (fun z : ℂ => fderiv ℝ ψ z Complex.I) :=
    hψc.fderiv_apply (𝕜 := ℝ) Complex.I
  have hdψ1A_int :
      Integrable (fun z : ℂ => fderiv ℝ ψ z (1 : ℂ) * A z) volume :=
    (hdψ1cont.mul hAcont).integrable_of_hasCompactSupport
      hdψ1c.mul_right
  have hψdA1_int :
      Integrable (fun z : ℂ => ψ z * fderiv ℝ A z (1 : ℂ)) volume :=
    (hψcont.mul hdA1cont).integrable_of_hasCompactSupport
      hψc.mul_right
  have hψA_int :
      Integrable (fun z : ℂ => ψ z * A z) volume :=
    (hψcont.mul hAcont).integrable_of_hasCompactSupport
      hψc.mul_right
  have hdψIB_int :
      Integrable (fun z : ℂ => fderiv ℝ ψ z Complex.I * B z) volume :=
    (hdψIcont.mul hBcont).integrable_of_hasCompactSupport
      hdψIc.mul_right
  have hψdBI_int :
      Integrable (fun z : ℂ => ψ z * fderiv ℝ B z Complex.I) volume :=
    (hψcont.mul hdBIcont).integrable_of_hasCompactSupport
      hψc.mul_right
  have hψB_int :
      Integrable (fun z : ℂ => ψ z * B z) volume :=
    (hψcont.mul hBcont).integrable_of_hasCompactSupport
      hψc.mul_right
  have hA_ibp :
      ∫ z : ℂ, fderiv ℝ ψ z (1 : ℂ) * A z ∂volume =
        -∫ z : ℂ, ψ z * fderiv ℝ A z (1 : ℂ) ∂volume := by
    have h :=
      integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        hdψ1A_int hψdA1_int hψA_int
        (fun z _ => hψ.differentiable (by simp) z)
        (fun z _ => hA.differentiable (by simp) z)
    simpa using (congrArg Neg.neg h).symm
  have hB_ibp :
      ∫ z : ℂ, fderiv ℝ ψ z Complex.I * B z ∂volume =
        -∫ z : ℂ, ψ z * fderiv ℝ B z Complex.I ∂volume := by
    have h :=
      integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        hdψIB_int hψdBI_int hψB_int
        (fun z _ => hψ.differentiable (by simp) z)
        (fun z _ => hB.differentiable (by simp) z)
    simpa using (congrArg Neg.neg h).symm
  have hdecomp (M : ℂ →L[ℝ] ℝ) (w : ℂ) :
      M w = w.re * M (1 : ℂ) + w.im * M Complex.I := by
    have hw : w = w.re • (1 : ℂ) + w.im • Complex.I := by
      apply Complex.ext <;> simp
    rw [hw, map_add, map_smul, map_smul]
    simp [smul_eq_mul]
  calc
    ∫ z : ℂ,
        fderiv ℝ ψ z
          (realLinearAdjugate (fderiv ℝ T z) v) ∂volume =
        ∫ z : ℂ,
          (fderiv ℝ ψ z (1 : ℂ) * A z +
            fderiv ℝ ψ z Complex.I * B z) ∂volume := by
          apply integral_congr_ae
          filter_upwards [] with z
          rw [hdecomp]
          simp only [A, B]
          ring
    _ =
        (∫ z : ℂ, fderiv ℝ ψ z (1 : ℂ) * A z ∂volume) +
          ∫ z : ℂ, fderiv ℝ ψ z Complex.I * B z ∂volume :=
      integral_add hdψ1A_int hdψIB_int
    _ = -((∫ z : ℂ, ψ z * fderiv ℝ A z (1 : ℂ) ∂volume) +
          ∫ z : ℂ, ψ z * fderiv ℝ B z Complex.I ∂volume) := by
      rw [hA_ibp, hB_ibp]
      ring
    _ = -∫ z : ℂ,
        ψ z *
          (fderiv ℝ A z (1 : ℂ) +
            fderiv ℝ B z Complex.I) ∂volume := by
      congr 1
      rw [← integral_add hψdA1_int hψdBI_int]
      apply integral_congr_ae
      filter_upwards [] with z
      ring
    _ = 0 := by
      apply neg_eq_zero.mpr
      apply integral_eq_zero_of_ae
      filter_upwards [] with z
      rw [realLinearAdjugate_fderiv_divergence hT v z]
      simp

/--
%%handwave
name:
  Smooth planar adjugate integration by parts
statement:
  Let $T:\mathbb C\to\mathbb C$ and $\psi:\mathbb C\to\mathbb R$ be smooth,
  with $\psi$ compactly supported. For every $v\in\mathbb C$,
  $$
    \int_{\mathbb C}
      \partial_{\operatorname{adj}(DT(z))v}\psi(z)\,z\,dz
    =-\int_{\mathbb C}
      \psi(z)\operatorname{adj}(DT(z))v\,dz.
  $$
proof:
  Apply [Cartesian Piola integration by parts](lean:JJMath.Quasiconformal.integral_cartesianPiola_of_contDiff) to the real and imaginary components of $\operatorname{adj}(DT)v$. Their divergence vanishes by [the smooth adjugate field is divergence-free](lean:JJMath.Quasiconformal.realLinearAdjugate_fderiv_divergence), and real linearity recombines the two coordinate derivatives into the displayed directional derivative.
-/
theorem integral_fderiv_realLinearAdjugate_of_contDiff
    {ψ : ℂ → ℝ} {T : ℂ → ℂ}
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hT : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) T)
    (hψc : HasCompactSupport ψ) (v : ℂ) :
    ∫ z : ℂ,
        (fderiv ℝ ψ z (realLinearAdjugate (fderiv ℝ T z) v)) • z ∂volume =
      -∫ z : ℂ, ψ z • realLinearAdjugate (fderiv ℝ T z) v ∂volume := by
  let A : ℂ → ℝ := fun z => (realLinearAdjugate (fderiv ℝ T z) v).re
  let B : ℂ → ℝ := fun z => (realLinearAdjugate (fderiv ℝ T z) v).im
  have hDT : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ T) :=
    hT.fderiv_right (by simp)
  have hDTI : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => fderiv ℝ T z Complex.I) :=
    hDT.clm_apply contDiff_const
  have hDT1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => fderiv ℝ T z (1 : ℂ)) :=
    hDT.clm_apply contDiff_const
  have hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A := by
    rw [show A = fun z =>
      (fderiv ℝ T z Complex.I).im * v.re -
        (fderiv ℝ T z Complex.I).re * v.im by
      funext z
      exact real_part_realLinearAdjugate_apply (fderiv ℝ T z) v]
    exact ((Complex.imCLM.contDiff.comp hDTI).mul contDiff_const).sub
      ((Complex.reCLM.contDiff.comp hDTI).mul contDiff_const)
  have hB : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) B := by
    rw [show B = fun z =>
      -(fderiv ℝ T z (1 : ℂ)).im * v.re +
        (fderiv ℝ T z (1 : ℂ)).re * v.im by
      funext z
      exact imag_part_realLinearAdjugate_apply (fderiv ℝ T z) v]
    exact ((Complex.imCLM.contDiff.comp hDT1).neg.mul
      (contDiff_const : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun _ : ℂ => v.re))).add
      ((Complex.reCLM.contDiff.comp hDT1).mul
        (contDiff_const : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun _ : ℂ => v.im)))
  have hbase := integral_cartesianPiola_of_contDiff hψ hA hB hψc
    (fun z => realLinearAdjugate_fderiv_divergence hT v z)
  have hdecomp (M : ℂ →L[ℝ] ℝ) (w : ℂ) :
      M w = w.re * M (1 : ℂ) + w.im * M Complex.I := by
    have hw : w = w.re • (1 : ℂ) + w.im • Complex.I := by
      apply Complex.ext <;> simp
    rw [hw, map_add, map_smul, map_smul]
    simp [smul_eq_mul]
  convert hbase using 1
  · apply integral_congr_ae
    filter_upwards [] with z
    rw [hdecomp]
    simp only [A, B]
    ring
  · congr 1
    apply integral_congr_ae
    filter_upwards [] with z
    congr 1
    apply Complex.ext
    · simp [A, B]
    · simp [A, B]

/--
%%handwave
name:
  Smooth cutoff Piola identity for a composition
statement:
  Let $\chi,\varphi:\mathbb C\to\mathbb R$ and
  $T:\mathbb C\to\mathbb C$ be smooth, with $\chi$ compactly supported.
  For every $v\in\mathbb C$,
  $$
  \begin{aligned}
    \int_{\mathbb C}\Big(&\chi(z)J(DT(z))
      \partial_v\varphi(T(z))\\
      &+\varphi(T(z))
      \partial_{\operatorname{adj}(DT(z))v}\chi(z)\Big)z\,dz
    =-\int_{\mathbb C}\chi(z)\varphi(T(z))
      \operatorname{adj}(DT(z))v\,dz.
  \end{aligned}
  $$
proof:
  Apply [smooth planar adjugate integration by parts](lean:JJMath.Quasiconformal.integral_fderiv_realLinearAdjugate_of_contDiff) to $\psi=\chi(\varphi\circ T)$. Expand its derivative by the product and chain rules, then use [the identity $DT\circ\operatorname{adj}(DT)=J(DT)\operatorname{id}$](lean:JJMath.Quasiconformal.comp_realLinearAdjugate).
-/
theorem integral_cutoff_composition_adjugate_of_contDiff
    {χ φ : ℂ → ℝ} {T : ℂ → ℂ}
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hT : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) T)
    (hχc : HasCompactSupport χ) (v : ℂ) :
    ∫ z : ℂ,
        (χ z * weakJacobian (fderiv ℝ T z) * fderiv ℝ φ (T z) v +
          φ (T z) * fderiv ℝ χ z
            (realLinearAdjugate (fderiv ℝ T z) v)) • z ∂volume =
      -∫ z : ℂ, (χ z * φ (T z)) •
        realLinearAdjugate (fderiv ℝ T z) v ∂volume := by
  let ψ : ℂ → ℝ := fun z => χ z * φ (T z)
  have hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ := by
    exact hχ.mul (hφ.comp hT)
  have hψc : HasCompactSupport ψ := by
    exact hχc.mul_right
  have hsmooth := integral_fderiv_realLinearAdjugate_of_contDiff hψ hT hψc v
  convert hsmooth using 1
  apply integral_congr_ae
  filter_upwards [] with z
  have hχdiff : DifferentiableAt ℝ χ z := hχ.differentiable (by simp) z
  have hφdiff : DifferentiableAt ℝ φ (T z) := hφ.differentiable (by simp) (T z)
  have hTdiff : DifferentiableAt ℝ T z := hT.differentiable (by simp) z
  have hφTdiff : DifferentiableAt ℝ (fun w => φ (T w)) z :=
    hφdiff.comp z hTdiff
  have hchain :
      fderiv ℝ (fun w => φ (T w)) z =
        (fderiv ℝ φ (T z)).comp (fderiv ℝ T z) := by
    simpa [Function.comp_def] using fderiv_comp z hφdiff hTdiff
  rw [show ψ = fun w => χ w * φ (T w) by rfl]
  rw [fderiv_fun_mul hχdiff hφTdiff]
  rw [hchain]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul]
  have hcomp := congrArg (fun L : ℂ →L[ℝ] ℂ => L v)
    (comp_realLinearAdjugate (fderiv ℝ T z))
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply] at hcomp
  rw [hcomp, map_smul]
  simp only [smul_eq_mul]
  ring

/--
%%handwave
name:
  Smooth scalar cutoff Piola identity for a composition
statement:
  Let $\chi,\varphi:\mathbb C\to\mathbb R$ and
  $T:\mathbb C\to\mathbb C$ be smooth, with $\chi$ compactly supported.
  For every $v\in\mathbb C$,
  $$
    \int_{\mathbb C}\left[
      \chi(z)J(DT(z))\,D\varphi(T(z))v+
      \varphi(T(z))D\chi(z)
        \bigl(\operatorname{adj}(DT(z))v\bigr)
    \right]\,dz=0.
  $$
proof:
  Apply [the scalar planar Piola identity](lean:JJMath.Quasiconformal.integral_fderiv_realLinearAdjugate_eq_zero_of_contDiff) to $\psi=\chi(\varphi\circ T)$. Expand its derivative by the product and chain rules and use $DT\circ\operatorname{adj}(DT)=J(DT)\operatorname{id}$.
-/
theorem integral_cutoff_composition_jacobian_eq_zero_of_contDiff
    {χ φ : ℂ → ℝ} {T : ℂ → ℂ}
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hT : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) T)
    (hχc : HasCompactSupport χ) (v : ℂ) :
    ∫ z : ℂ,
        (χ z * weakJacobian (fderiv ℝ T z) *
            fderiv ℝ φ (T z) v +
          φ (T z) * fderiv ℝ χ z
            (realLinearAdjugate (fderiv ℝ T z) v)) ∂volume = 0 := by
  let ψ : ℂ → ℝ := fun z => χ z * φ (T z)
  have hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ :=
    hχ.mul (hφ.comp hT)
  have hψc : HasCompactSupport ψ :=
    hχc.mul_right
  have hsmooth :=
    integral_fderiv_realLinearAdjugate_eq_zero_of_contDiff
      hψ hT hψc v
  convert hsmooth using 1
  apply integral_congr_ae
  filter_upwards [] with z
  have hχdiff : DifferentiableAt ℝ χ z :=
    hχ.differentiable (by simp) z
  have hφdiff : DifferentiableAt ℝ φ (T z) :=
    hφ.differentiable (by simp) (T z)
  have hTdiff : DifferentiableAt ℝ T z :=
    hT.differentiable (by simp) z
  have hφTdiff : DifferentiableAt ℝ (fun w => φ (T w)) z :=
    hφdiff.comp z hTdiff
  have hchain :
      fderiv ℝ (fun w => φ (T w)) z =
        (fderiv ℝ φ (T z)).comp (fderiv ℝ T z) := by
    simpa [Function.comp_def] using
      fderiv_comp z hφdiff hTdiff
  rw [show ψ = fun w => χ w * φ (T w) by rfl]
  rw [fderiv_fun_mul hχdiff hφTdiff]
  rw [hchain]
  simp only [ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul]
  have hcomp := congrArg (fun L : ℂ →L[ℝ] ℂ => L v)
    (comp_realLinearAdjugate (fderiv ℝ T z))
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply] at hcomp
  rw [hcomp, map_smul]
  simp only [smul_eq_mul]
  ring

/--
%%handwave
name:
  Sobolev scalar cutoff Piola identity
statement:
  Let $f:\mathbb C\to\mathbb C$ be locally $W^{1,2}$ with weak
  differential $Df$. For smooth compactly supported real functions
  $\chi,\varphi$ and every $v\in\mathbb C$,
  $$
  \begin{aligned}
    &\int_{\mathbb C}
      \chi(z)J_f(z)D\varphi(f(z))v\,dz\\
    &\qquad+
      \int_{\mathbb C}
      \varphi(f(z))D\chi(z)
        \bigl(\operatorname{adj}(Df(z))v\bigr)\,dz=0.
  \end{aligned}
  $$
proof:
  Approximate $f$ in the local $W^{1,2}$ graph norm on the compact support
  of $\chi$ and apply the smooth scalar cutoff identity. Along one
  subsequence, [the Jacobian term converges](lean:JJMath.Quasiconformal.PlanarWeakSobolevSmoothApproxGraphL2Data.exists_strictMono_scalarMainTerm_integral_tendsto), while [the cutoff-adjugate term converges along the full sequence](lean:JJMath.Quasiconformal.PlanarWeakSobolevSmoothApproxGraphL2Data.cutoffScalarTerm_integral_tendsto). Uniqueness of limits gives the identity.
-/
theorem IsLocalW12On.integral_cutoff_composition_jacobian_eq_zero
    {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (hdf : IsLocalW12On Set.univ f df)
    (χ φ :
      JJMath.Uniformization.SmoothCompactlySupportedManifoldCoordinateFunction
        (Set.univ : Set ℂ))
    (v : ℂ) :
    (∫ z : ℂ,
        χ z * weakJacobian (df z) *
          fderiv ℝ (φ : ℂ → ℝ) (f z) v ∂volume) +
      ∫ z : ℂ,
        φ (f z) *
          fderiv ℝ (χ : ℂ → ℝ) z
            (realLinearAdjugate (df z) v) ∂volume = 0 := by
  let Q : Set ℂ := tsupport (χ : ℂ → ℝ)
  let P : Set ℂ := Metric.cthickening 1 Q
  have hQ : IsCompact Q :=
    χ.compact_support
  have hP : IsCompact P :=
    hQ.cthickening
  have hQP :
      ∃ δ : ℝ, 0 < δ ∧
        Metric.cthickening δ Q ⊆ P :=
    ⟨1, zero_lt_one, by rfl⟩
  obtain ⟨hgraph⟩ :=
    hdf.exists_smoothApproxGraphL2Data_on_compact
      hQ hP hQP (Set.subset_univ P)
  have hfQ : MemLp f 2 (volume.restrict Q) :=
    (hdf.2.2 Q hQ (Set.subset_univ Q)).1
  have hdfQ : MemLp df 2 (volume.restrict Q) :=
    (hdf.2.2 Q hQ (Set.subset_univ Q)).2
  obtain ⟨ns, hns, hmain⟩ :=
    hgraph.exists_strictMono_scalarMainTerm_integral_tendsto
      hQ hfQ hdfQ χ.smooth φ v
  have herr :=
    (hgraph.cutoffScalarTerm_integral_tendsto
      hQ hfQ hdfQ χ.smooth φ v).comp
        hns.tendsto_atTop
  have heq (n : ℕ) :
      (∫ z in Q,
          χ z *
            weakJacobian
              (fderiv ℝ
                (hgraph.approximants (ns n)) z) *
            fderiv ℝ (φ : ℂ → ℝ)
              (hgraph.approximants (ns n) z) v
          ∂volume) +
        ∫ z in Q,
          φ (hgraph.approximants (ns n) z) *
            fderiv ℝ (χ : ℂ → ℝ) z
              (realLinearAdjugate
                (fderiv ℝ
                  (hgraph.approximants (ns n)) z) v)
          ∂volume = 0 := by
    let T : ℂ → ℂ :=
      hgraph.approximants (ns n)
    let main : ℂ → ℝ := fun z =>
      χ z * weakJacobian (fderiv ℝ T z) *
        fderiv ℝ (φ : ℂ → ℝ) (T z) v
    let err : ℂ → ℝ := fun z =>
      φ (T z) *
        fderiv ℝ (χ : ℂ → ℝ) z
          (realLinearAdjugate (fderiv ℝ T z) v)
    have hT :
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) T :=
      hgraph.smooth (ns n)
    have hmainCont : Continuous main := by
      exact
        ((χ.smooth.continuous.mul
          (continuous_weakJacobian.comp
            (hT.continuous_fderiv (by simp)))).mul
          (((φ.smooth.continuous_fderiv (by simp)).clm_apply
            continuous_const).comp
            hT.continuous))
    have herrCont : Continuous err := by
      have hAdj : Continuous (fun z =>
          realLinearAdjugate (fderiv ℝ T z) v) :=
        (continuous_realLinearAdjugate.comp
          (hT.continuous_fderiv (by simp))).clm_apply
            continuous_const
      have hdχ : Continuous (fun z =>
          fderiv ℝ (χ : ℂ → ℝ) z
            (realLinearAdjugate
              (fderiv ℝ T z) v)) :=
        (χ.smooth.continuous_fderiv (by simp)).clm_apply
          hAdj
      exact (φ.smooth.continuous.comp hT.continuous).mul
        hdχ
    have hmainZero :
        ∀ z, z ∉ Q → main z = 0 := by
      intro z hz
      have hχz : χ z = 0 :=
        image_eq_zero_of_notMem_tsupport hz
      simp [main, hχz]
    have herrZero :
        ∀ z, z ∉ Q → err z = 0 := by
      intro z hz
      have hdχ :
          fderiv ℝ (χ : ℂ → ℝ) z = 0 :=
        fderiv_of_notMem_tsupport
          (𝕜 := ℝ) (f := (χ : ℂ → ℝ)) hz
      simp [err, hdχ]
    have hcompactOfZero {g : ℂ → ℝ}
        (hzero : ∀ z, z ∉ Q → g z = 0) :
        IsCompact (tsupport g) := by
      apply hQ.of_isClosed_subset (isClosed_tsupport g)
      intro z hz
      by_contra hzQ
      have hzeroEv :
          g =ᶠ[𝓝 z] (0 : ℂ → ℝ) := by
        filter_upwards
          [hQ.isClosed.isOpen_compl.mem_nhds hzQ] with
          y hy
        exact hzero y hy
      exact
        (notMem_tsupport_iff_eventuallyEq.mpr
          hzeroEv) hz
    have hmainInt : Integrable main volume :=
      hmainCont.integrable_of_hasCompactSupport
        (hcompactOfZero hmainZero)
    have herrInt : Integrable err volume :=
      herrCont.integrable_of_hasCompactSupport
        (hcompactOfZero herrZero)
    have hmainLocal :=
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (μ := volume) (s := Q) hmainZero
    have herrLocal :=
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (μ := volume) (s := Q) herrZero
    have hsmooth :=
      integral_cutoff_composition_jacobian_eq_zero_of_contDiff
        χ.smooth φ.smooth hT χ.compact_support v
    have hsmooth' :
        (∫ z, main z + err z ∂volume) = 0 := by
      simpa [main, err, T] using hsmooth
    rw [integral_add hmainInt herrInt] at hsmooth'
    change
      (∫ z in Q, main z ∂volume) +
        ∫ z in Q, err z ∂volume = 0
    rw [hmainLocal, herrLocal]
    exact hsmooth'
  have hsum := hmain.add herr
  have hsumZero :
      Filter.Tendsto
        (fun n =>
          (∫ z in Q,
              χ z *
                weakJacobian
                  (fderiv ℝ
                    (hgraph.approximants (ns n)) z) *
                fderiv ℝ (φ : ℂ → ℝ)
                  (hgraph.approximants (ns n) z) v
              ∂volume) +
            ∫ z in Q,
              φ (hgraph.approximants (ns n) z) *
                fderiv ℝ (χ : ℂ → ℝ) z
                  (realLinearAdjugate
                    (fderiv ℝ
                      (hgraph.approximants (ns n)) z) v)
              ∂volume)
        Filter.atTop (𝓝 0) := by
    apply Filter.Tendsto.congr'
      (Filter.Eventually.of_forall fun n =>
        (heq n).symm)
      tendsto_const_nhds
  have hlimit :
      (∫ z in Q,
          χ z * weakJacobian (df z) *
            fderiv ℝ (φ : ℂ → ℝ) (f z) v
          ∂volume) +
        ∫ z in Q,
          φ (f z) *
            fderiv ℝ (χ : ℂ → ℝ) z
              (realLinearAdjugate (df z) v)
          ∂volume = 0 :=
    tendsto_nhds_unique hsum hsumZero
  have hmainZero :
      ∀ z, z ∉ Q →
        χ z * weakJacobian (df z) *
          fderiv ℝ (φ : ℂ → ℝ) (f z) v = 0 := by
    intro z hz
    have hχz : χ z = 0 :=
      image_eq_zero_of_notMem_tsupport hz
    simp [hχz]
  have herrZero :
      ∀ z, z ∉ Q →
        φ (f z) *
          fderiv ℝ (χ : ℂ → ℝ) z
            (realLinearAdjugate (df z) v) = 0 := by
    intro z hz
    have hdχ :
        fderiv ℝ (χ : ℂ → ℝ) z = 0 :=
      fderiv_of_notMem_tsupport
        (𝕜 := ℝ) (f := (χ : ℂ → ℝ)) hz
    simp [hdχ]
  have hmainLocal :=
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (μ := volume) (s := Q) hmainZero
  have herrLocal :=
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (μ := volume) (s := Q) herrZero
  rw [hmainLocal, herrLocal] at hlimit
  exact hlimit

/--
%%handwave
name:
  A protected cutoff gives a stationary weighted Jacobian
statement:
  Let $f:\mathbb C\to\mathbb C$ be locally $W^{1,2}$ with weak
  differential $Df$, and let $\chi$ be smooth and compactly supported.
  Suppose
  $$
    D\chi(z)=0\qquad\text{whenever }f(z)\in\overline{B}(w,r).
  $$
  If the smooth compactly supported function $\varphi$ is supported in
  $B(w,r)$, then for every $v\in\mathbb C$,
  $$
    \int_{\mathbb C}
      \chi(z)J_f(z)D\varphi(f(z))v\,dz=0.
  $$
proof:
  Apply [the Sobolev scalar cutoff Piola identity](lean:JJMath.Quasiconformal.IsLocalW12On.integral_cutoff_composition_jacobian_eq_zero). Its cutoff-error term vanishes pointwise: on the inverse image of the support of $\varphi$, the cutoff differential is zero, and off that inverse image the target test itself is zero.
-/
theorem IsLocalW12On.integral_cutoff_jacobian_fderiv_comp_eq_zero
    {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (hdf : IsLocalW12On Set.univ f df)
    (χ φ :
      JJMath.Uniformization.SmoothCompactlySupportedManifoldCoordinateFunction
        (Set.univ : Set ℂ))
    {w : ℂ} {r : ℝ}
    (hφsupport :
      tsupport (φ : ℂ → ℝ) ⊆ Metric.ball w r)
    (hχzero : ∀ z, dist (f z) w ≤ r →
      fderiv ℝ (χ : ℂ → ℝ) z = 0)
    (v : ℂ) :
    ∫ z : ℂ,
        χ z * weakJacobian (df z) *
          fderiv ℝ (φ : ℂ → ℝ) (f z) v
        ∂volume = 0 := by
  have hidentity :=
    hdf.integral_cutoff_composition_jacobian_eq_zero
      χ φ v
  have herr :
      (∫ z : ℂ,
        φ (f z) *
          fderiv ℝ (χ : ℂ → ℝ) z
            (realLinearAdjugate (df z) v)
        ∂volume) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [] with z
    by_cases hz :
        f z ∈ tsupport (φ : ℂ → ℝ)
    · have hzball :=
        Metric.mem_ball.mp (hφsupport hz)
      rw [hχzero z hzball.le]
      simp
    · have hφz : φ (f z) = 0 :=
        image_eq_zero_of_notMem_tsupport hz
      simp [hφz]
  rw [herr, add_zero] at hidentity
  exact hidentity

/--
%%handwave
name:
  Planar Sobolev adjugate integration by parts
statement:
  Let $F:\Omega\to\Omega'$ be a homeomorphism between open planar sets and
  suppose its ambient representative belongs to
  $W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb C)$ with weak differential $Df$.
  For every smooth compactly supported $\varphi:\Omega'\to\mathbb R$ and
  every $v\in\mathbb C$,
  $$
    \int_\Omega J(Df(z))\,\partial_v\varphi(F(z))\,z\,dz
      =-\int_\Omega \varphi(F(z))\,\operatorname{adj}(Df(z))v\,dz.
  $$
proof:
  Choose a smooth cutoff equal to one, with zero differential, on the compact
  preimage of $\operatorname{supp}\varphi$, and approximate $F$ in the local
  $W^{1,2}$ graph norm on the compact support of this cutoff. Apply [the smooth cutoff composition identity](lean:JJMath.Quasiconformal.integral_cutoff_composition_adjugate_of_contDiff) to the approximants. Along a subsequence, [the localized Jacobian term converges](lean:JJMath.Quasiconformal.PlanarWeakSobolevSmoothApproxGraphL2Data.exists_strictMono_mainTerm_integral_tendsto); the cutoff error tends to zero and the adjugate side converges by their $L^2$ estimates. Uniqueness of limits gives the localized identity, and the cutoff can then be removed because it equals one wherever $\varphi\circ F$ or its differential is nonzero.
-/
theorem IsLocalW12On.planarAdjugate_test_identity
    {Ω Ω' : Set ℂ} {F : Ω ≃ₜ Ω'} {df : ℂ → ℂ →L[ℝ] ℂ}
    (hdf : IsLocalW12On Ω (ambientMap F) df) (hΩ' : IsOpen Ω')
    (φ : JJMath.Uniformization.SmoothCompactlySupportedManifoldCoordinateFunction Ω')
    (v : ℂ) :
    ∫ z in Ω, weakJacobian (df z) •
        ((fderiv ℝ (φ : ℂ → ℝ) (ambientMap F z) v) • z) ∂volume =
      -∫ z in Ω,
        φ (ambientMap F z) • (realLinearAdjugate (df z) v) ∂volume := by
  let Kφ : Set ℂ := tsupport (φ : ℂ → ℝ)
  have hKφ : IsCompact Kφ := φ.compact_support
  have hKφΩ' : Kφ ⊆ Ω' := φ.support_subset
  let K : Set ℂ := ambientMap F.symm '' Kφ
  have hK : IsCompact K :=
    hKφ.image_of_continuousOn
      ((continuousOn_ambientMap F.symm).mono hKφΩ')
  have hKΩ : K ⊆ Ω := by
    rintro z ⟨y, hy, rfl⟩
    let yΩ' : Ω' := ⟨y, hKφΩ' hy⟩
    have heq : ambientMap F.symm y = F.symm yΩ' := ambientMap_apply F.symm yΩ'
    rw [heq]
    exact (F.symm yΩ').2
  rcases JJMath.Uniformization.exists_scalarWeakSobolevCutoff
      hK hKΩ hdf.1 with ⟨χ⟩
  let Q : Set ℂ := tsupport (χ : ℂ → ℝ)
  have hQ : IsCompact Q := χ.compact_support
  have hQΩ : Q ⊆ Ω := χ.support_subset
  obtain ⟨δ, hδ, hδΩ⟩ :=
    hQ.exists_cthickening_subset_open hdf.1 hQΩ
  let P : Set ℂ := Metric.cthickening δ Q
  have hP : IsCompact P := hQ.cthickening
  have hQP : ∃ ε : ℝ, 0 < ε ∧ Metric.cthickening ε Q ⊆ P :=
    ⟨δ, hδ, by rfl⟩
  have hPΩ : P ⊆ Ω := hδΩ
  rcases hdf.exists_smoothApproxGraphL2Data_on_compact hQ hP hQP hPΩ with
    ⟨hgraph⟩
  have hfQ : MemLp (ambientMap F) 2 (volume.restrict Q) :=
    (hdf.2.2 Q hQ hQΩ).1
  have hdfQ : MemLp df 2 (volume.restrict Q) :=
    (hdf.2.2 Q hQ hQΩ).2
  have hpreimage {z : ℂ} (hzΩ : z ∈ Ω)
      (hzφ : ambientMap F z ∈ Kφ) : z ∈ K := by
    refine ⟨ambientMap F z, hzφ, ?_⟩
    exact ambientMap_symm_apply_ambientMap F ⟨z, hzΩ⟩
  have hcutoffErrorZero : ∀ z ∈ Q,
      φ (ambientMap F z) •
        ((fderiv ℝ (χ : ℂ → ℝ) z
          (realLinearAdjugate (df z) v)) • z) = 0 := by
    intro z hzQ
    by_cases hzφ : ambientMap F z ∈ Kφ
    · have hzK : z ∈ K := hpreimage (hQΩ hzQ) hzφ
      rw [χ.fderiv_eq_zero_on z hzK]
      simp
    · have hφzero : φ (ambientMap F z) = 0 :=
        image_eq_zero_of_notMem_tsupport hzφ
      simp [hφzero]
  rcases hgraph.exists_strictMono_mainTerm_integral_tendsto
      hQ hfQ hdfQ χ.smooth φ v with ⟨ns, hns, hmain⟩
  have herr :=
    (hgraph.cutoffError_integral_tendsto_zero hQ hfQ hdfQ χ.smooth φ v
      hcutoffErrorZero).comp hns.tendsto_atTop
  have hright :=
    (hgraph.adjugateSide_integral_tendsto hQ hfQ hdfQ χ.smooth φ v).comp
      hns.tendsto_atTop
  have heq (n : ℕ) :
      (∫ z in Q,
          ((χ z * weakJacobian
              (fderiv ℝ (hgraph.approximants (ns n)) z) *
            fderiv ℝ (φ : ℂ → ℝ)
              (hgraph.approximants (ns n) z) v) • z) ∂volume) +
        ∫ z in Q,
          φ (hgraph.approximants (ns n) z) •
            ((fderiv ℝ (χ : ℂ → ℝ) z
              (realLinearAdjugate
                (fderiv ℝ (hgraph.approximants (ns n)) z) v)) • z)
          ∂volume =
        -∫ z in Q,
          (χ z * φ (hgraph.approximants (ns n) z)) •
            realLinearAdjugate
              (fderiv ℝ (hgraph.approximants (ns n)) z) v ∂volume := by
    let T : ℂ → ℂ := hgraph.approximants (ns n)
    let main : ℂ → ℂ := fun z =>
      (χ z * weakJacobian (fderiv ℝ T z) *
        fderiv ℝ (φ : ℂ → ℝ) (T z) v) • z
    let err : ℂ → ℂ := fun z =>
      φ (T z) •
        ((fderiv ℝ (χ : ℂ → ℝ) z
          (realLinearAdjugate (fderiv ℝ T z) v)) • z)
    let right : ℂ → ℂ := fun z =>
      (χ z * φ (T z)) • realLinearAdjugate (fderiv ℝ T z) v
    have hT : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) T :=
      hgraph.smooth (ns n)
    have hmain_cont : Continuous main := by
      exact ((χ.smooth.continuous.mul
        (continuous_weakJacobian.comp
          (hT.continuous_fderiv (by simp)))).mul
        (((φ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const).comp
          hT.continuous)).smul continuous_id
    have herr_cont : Continuous err := by
      have hAdj : Continuous (fun z =>
          realLinearAdjugate (fderiv ℝ T z) v) :=
        (continuous_realLinearAdjugate.comp
          (hT.continuous_fderiv (by simp))).clm_apply continuous_const
      have hdχ : Continuous (fun z =>
          fderiv ℝ (χ : ℂ → ℝ) z
            (realLinearAdjugate (fderiv ℝ T z) v)) :=
        (χ.smooth.continuous_fderiv (by simp)).clm_apply hAdj
      exact (φ.smooth.continuous.comp hT.continuous).smul
        (hdχ.smul continuous_id)
    have hright_cont : Continuous right := by
      have hAdj : Continuous (fun z =>
          realLinearAdjugate (fderiv ℝ T z) v) :=
        (continuous_realLinearAdjugate.comp
          (hT.continuous_fderiv (by simp))).clm_apply continuous_const
      exact (χ.smooth.continuous.mul
        (φ.smooth.continuous.comp hT.continuous)).smul hAdj
    have hmain_zero : ∀ z, z ∉ Q → main z = 0 := by
      intro z hz
      have hχz : χ z = 0 := image_eq_zero_of_notMem_tsupport hz
      simp [main, hχz]
    have herr_zero : ∀ z, z ∉ Q → err z = 0 := by
      intro z hz
      have hdχ : fderiv ℝ (χ : ℂ → ℝ) z = 0 :=
        fderiv_of_notMem_tsupport (𝕜 := ℝ) (f := (χ : ℂ → ℝ)) hz
      simp [err, hdχ]
    have hright_zero : ∀ z, z ∉ Q → right z = 0 := by
      intro z hz
      have hχz : χ z = 0 := image_eq_zero_of_notMem_tsupport hz
      simp [right, hχz]
    have hcompact_of_zero {g : ℂ → ℂ}
        (hzero : ∀ z, z ∉ Q → g z = 0) : IsCompact (tsupport g) := by
      apply hQ.of_isClosed_subset (isClosed_tsupport g)
      intro z hz
      by_contra hzQ
      have hzero_ev : g =ᶠ[𝓝 z] (0 : ℂ → ℂ) := by
        filter_upwards [hQ.isClosed.isOpen_compl.mem_nhds hzQ] with y hy
        exact hzero y hy
      exact (notMem_tsupport_iff_eventuallyEq.mpr hzero_ev) hz
    have hmain_compact : IsCompact (tsupport main) :=
      hcompact_of_zero hmain_zero
    have herr_compact : IsCompact (tsupport err) :=
      hcompact_of_zero herr_zero
    have hright_compact : IsCompact (tsupport right) :=
      hcompact_of_zero hright_zero
    have hmain_int : Integrable main volume :=
      hmain_cont.integrable_of_hasCompactSupport hmain_compact
    have herr_int : Integrable err volume :=
      herr_cont.integrable_of_hasCompactSupport herr_compact
    have hright_int : Integrable right volume :=
      hright_cont.integrable_of_hasCompactSupport hright_compact
    have hmain_local :=
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (μ := volume) (s := Q) hmain_zero
    have herr_local :=
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (μ := volume) (s := Q) herr_zero
    have hright_local :=
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (μ := volume) (s := Q) hright_zero
    have hsmooth := integral_cutoff_composition_adjugate_of_contDiff
      χ.smooth φ.smooth hT χ.compact_support v
    have hsmooth' : (∫ z, main z + err z ∂volume) =
        -∫ z, right z ∂volume := by
      convert hsmooth using 1
      apply integral_congr_ae
      filter_upwards with z
      simp only [main, err, add_smul, smul_smul]
    rw [integral_add hmain_int herr_int] at hsmooth'
    change (∫ z in Q, main z ∂volume) + (∫ z in Q, err z ∂volume) =
      -∫ z in Q, right z ∂volume
    rw [hmain_local, herr_local, hright_local]
    exact hsmooth'
  have hleft := hmain.add herr
  have hleft' : Filter.Tendsto
      (fun n =>
        (∫ z in Q,
          ((χ z * weakJacobian
              (fderiv ℝ (hgraph.approximants (ns n)) z) *
            fderiv ℝ (φ : ℂ → ℝ)
              (hgraph.approximants (ns n) z) v) • z) ∂volume) +
        ∫ z in Q,
          φ (hgraph.approximants (ns n) z) •
            ((fderiv ℝ (χ : ℂ → ℝ) z
              (realLinearAdjugate
                (fderiv ℝ (hgraph.approximants (ns n)) z) v)) • z)
          ∂volume)
      Filter.atTop
      (𝓝 (∫ z in Q,
        (χ z * weakJacobian (df z) *
          fderiv ℝ (φ : ℂ → ℝ) (ambientMap F z) v) • z ∂volume)) := by
    simpa only [Function.comp_apply, add_zero] using hleft
  have hright_neg := hright.neg
  have hright_neg' : Filter.Tendsto
      (fun n => -∫ z in Q,
        (χ z * φ (hgraph.approximants (ns n) z)) •
          realLinearAdjugate
            (fderiv ℝ (hgraph.approximants (ns n)) z) v ∂volume)
      Filter.atTop
      (𝓝 (-∫ z in Q,
        (χ z * φ (ambientMap F z)) •
          realLinearAdjugate (df z) v ∂volume)) := by
    simpa only [Function.comp_apply] using hright_neg
  have hleft_to_right : Filter.Tendsto
      (fun n =>
        (∫ z in Q,
          ((χ z * weakJacobian
              (fderiv ℝ (hgraph.approximants (ns n)) z) *
            fderiv ℝ (φ : ℂ → ℝ)
              (hgraph.approximants (ns n) z) v) • z) ∂volume) +
        ∫ z in Q,
          φ (hgraph.approximants (ns n) z) •
            ((fderiv ℝ (χ : ℂ → ℝ) z
              (realLinearAdjugate
                (fderiv ℝ (hgraph.approximants (ns n)) z) v)) • z)
          ∂volume)
      Filter.atTop
      (𝓝 (-∫ z in Q,
        (χ z * φ (ambientMap F z)) •
          realLinearAdjugate (df z) v ∂volume)) := by
    apply hright_neg'.congr'
    exact Filter.Eventually.of_forall fun n => (heq n).symm
  have hQidentity :
      (∫ z in Q,
        (χ z * weakJacobian (df z) *
          fderiv ℝ (φ : ℂ → ℝ) (ambientMap F z) v) • z ∂volume) =
        -∫ z in Q,
          (χ z * φ (ambientMap F z)) •
            realLinearAdjugate (df z) v ∂volume :=
    tendsto_nhds_unique hleft' hleft_to_right
  have hmain_pointwise {z : ℂ} (hzΩ : z ∈ Ω) :
      (χ z * weakJacobian (df z) *
        fderiv ℝ (φ : ℂ → ℝ) (ambientMap F z) v) • z =
      weakJacobian (df z) •
        ((fderiv ℝ (φ : ℂ → ℝ) (ambientMap F z) v) • z) := by
    by_cases hzφ : ambientMap F z ∈ Kφ
    · rw [χ.eq_one_on z (hpreimage hzΩ hzφ)]
      simp [mul_assoc]
    · have hdφ : fderiv ℝ (φ : ℂ → ℝ) (ambientMap F z) = 0 :=
        fderiv_of_notMem_tsupport (𝕜 := ℝ)
          (f := (φ : ℂ → ℝ)) hzφ
      rw [hdφ]
      simp
  have hright_pointwise {z : ℂ} (hzΩ : z ∈ Ω) :
      (χ z * φ (ambientMap F z)) • realLinearAdjugate (df z) v =
        φ (ambientMap F z) • realLinearAdjugate (df z) v := by
    by_cases hzφ : ambientMap F z ∈ Kφ
    · rw [χ.eq_one_on z (hpreimage hzΩ hzφ)]
      simp
    · have hφzero : φ (ambientMap F z) = 0 :=
        image_eq_zero_of_notMem_tsupport hzφ
      simp [hφzero]
  have hmain_domain :
      (∫ z in Ω, weakJacobian (df z) •
        ((fderiv ℝ (φ : ℂ → ℝ) (ambientMap F z) v) • z) ∂volume) =
      ∫ z in Q,
        (χ z * weakJacobian (df z) *
          fderiv ℝ (φ : ℂ → ℝ) (ambientMap F z) v) • z ∂volume := by
    calc
      _ = ∫ z in Ω,
          (χ z * weakJacobian (df z) *
            fderiv ℝ (φ : ℂ → ℝ) (ambientMap F z) v) • z ∂volume := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hdf.1.measurableSet] with z hzΩ
        exact hmain_pointwise hzΩ |>.symm
      _ = _ := setIntegral_eq_of_subset_of_forall_diff_eq_zero
        hdf.1.measurableSet hQΩ (by
          intro z hz
          have hχz : χ z = 0 := image_eq_zero_of_notMem_tsupport hz.2
          simp [hχz])
  have hright_domain :
      (∫ z in Ω,
        φ (ambientMap F z) • realLinearAdjugate (df z) v ∂volume) =
      ∫ z in Q,
        (χ z * φ (ambientMap F z)) •
          realLinearAdjugate (df z) v ∂volume := by
    calc
      _ = ∫ z in Ω,
          (χ z * φ (ambientMap F z)) •
            realLinearAdjugate (df z) v ∂volume := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hdf.1.measurableSet] with z hzΩ
        exact hright_pointwise hzΩ |>.symm
      _ = _ := setIntegral_eq_of_subset_of_forall_diff_eq_zero
        hdf.1.measurableSet hQΩ (by
          intro z hz
          have hχz : χ z = 0 := image_eq_zero_of_notMem_tsupport hz.2
          simp [hχz])
  rw [hmain_domain, hright_domain]
  exact hQidentity

/--
%%handwave
name:
  Distributional differential of the inverse homeomorphism
statement:
  Let $F:\Omega\to\Omega'$ be a planar quasiconformal homeomorphism with
  weak differential $Df$. Suppose a locally square-integrable field $G$ on
  $\Omega'$ satisfies
  $$G(F(z))=(Df(z))^{\dagger}$$
  for almost every $z\in\Omega$. Then $G$ is the distributional weak
  differential of $F^{-1}$ on $\Omega'$.
proof:
  The two test integrands are integrable because their scalar factors have
  compact support and $G$ is locally square-integrable. Pull both target
  integrals back using [oriented Sobolev change of variables for Bochner integrals](lean:JJMath.Quasiconformal.IsKQuasiconformalBetween.integral_image_eq_integral_weakJacobian_smul). The identity
  $\operatorname{adj}(Df)=J(Df)(Df)^\dagger$ follows from the distortion
  inequality, including on the zero-Jacobian set. The resulting source
  identity is exactly [planar Sobolev adjugate integration by parts](lean:JJMath.Quasiconformal.IsLocalW12On.planarAdjugate_test_identity).
-/
theorem IsKQuasiconformalBetween.inverseDifferentialCandidate_isWeakDerivativeOn
    {K : ℝ} {Ω Ω' : Set ℂ} {F : Ω ≃ₜ Ω'}
    (hF : IsKQuasiconformalBetween K F) {df dg : ℂ → ℂ →L[ℝ] ℂ}
    (hdf : IsLocalW12On Ω (ambientMap F) df)
    (hdg_comp : ∀ᵐ z ∂volume.restrict Ω,
      dg (ambientMap F z) = realLinearPseudoInverse (df z))
    (hdg_L2 : ∀ C : Set ℂ, IsCompact C → C ⊆ Ω' →
      MemLp dg 2 (volume.restrict C)) :
    JJMath.Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues
      Ω' (ambientMap F.symm) dg := by
  intro φ v
  let dφ : ℂ → ℝ := fun y ↦ fderiv ℝ (φ : ℂ → ℝ) y v
  let left : ℂ → ℂ := fun y ↦ dφ y • ambientMap F.symm y
  let right : ℂ → ℂ := fun y ↦ φ y • dg y v
  let Kφ : Set ℂ := tsupport (φ : ℂ → ℝ)
  have hKφ : IsCompact Kφ := φ.compact_support
  have hKφΩ' : Kφ ⊆ Ω' := φ.support_subset
  have hdφ_cont : Continuous dφ :=
    ((φ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hdφ_tsupport : tsupport dφ ⊆ Kφ := by
    simpa [dφ, Kφ] using
      (tsupport_fderiv_apply_subset (𝕜 := ℝ)
        (f := (φ : ℂ → ℝ)) v)
  have hleft_cont : ContinuousOn left Kφ := by
    exact hdφ_cont.continuousOn.smul
      ((continuousOn_ambientMap F.symm).mono hKφΩ')
  have hleft_support : Function.support left ⊆ Kφ := by
    intro y hy
    apply hdφ_tsupport
    apply subset_tsupport
    intro hzero
    exact hy (by simp [left, dφ, hzero])
  have hleft_int : Integrable left (volume.restrict Ω') := by
    have hleft_global : Integrable left volume :=
      (integrableOn_iff_integrable_of_support_subset hleft_support).mp
        (hleft_cont.integrableOn_compact hKφ)
    exact hleft_global.mono_measure Measure.restrict_le_self
  have hright_support : Function.support right ⊆ Kφ := by
    intro y hy
    apply subset_tsupport
    intro hzero
    exact hy (by simp [right, hzero])
  have hright_int : Integrable right (volume.restrict Ω') := by
    let μK : Measure ℂ := volume.restrict Kφ
    haveI : IsFiniteMeasure μK :=
      isFiniteMeasure_restrict.2 hKφ.measure_ne_top
    have hdg_int : Integrable dg μK :=
      (hdg_L2 Kφ hKφ hKφΩ').integrable (by norm_num)
    have heval_int : Integrable (fun y ↦ dg y v) μK :=
      ((ContinuousLinearMap.apply ℝ ℂ) v).integrable_comp hdg_int
    rcases hKφ.exists_bound_of_continuousOn
        φ.smooth.continuous.continuousOn with ⟨C, hC⟩
    have hright_K : Integrable right μK := by
      have h := heval_int.bdd_smul C
        φ.smooth.continuous.aestronglyMeasurable
        (ae_restrict_of_forall_mem hKφ.measurableSet hC)
      simpa [right, μK] using h
    have hright_global : Integrable right volume :=
      (integrableOn_iff_integrable_of_support_subset hright_support).mp
        hright_K
    exact hright_global.mono_measure Measure.restrict_le_self
  refine ⟨?_, ?_, ?_⟩
  · simpa [left, dφ] using hleft_int
  · simpa [right] using hright_int
  have himage : ambientMap F '' Ω = Ω' := by
    apply Subset.antisymm
    · rintro y ⟨z, hzΩ, rfl⟩
      let zΩ : Ω := ⟨z, hzΩ⟩
      have heq : ambientMap F z = F zΩ := ambientMap_apply F zΩ
      rw [heq]
      exact (F zΩ).2
    · intro y hyΩ'
      let yΩ' : Ω' := ⟨y, hyΩ'⟩
      refine ⟨ambientMap F.symm y, ?_, ?_⟩
      · have heq : ambientMap F.symm y = F.symm yΩ' :=
          ambientMap_apply F.symm yΩ'
        rw [heq]
        exact (F.symm yΩ').2
      · simpa only [Homeomorph.symm_symm] using
          (ambientMap_symm_apply_ambientMap F.symm yΩ')
  have hcov_left := hF.integral_image_eq_integral_weakJacobian_smul
    hdf hdf.1.measurableSet Subset.rfl
      (by simpa [himage] using hleft_int.aestronglyMeasurable)
  have hcov_right := hF.integral_image_eq_integral_weakJacobian_smul
    hdf hdf.1.measurableSet Subset.rfl
      (by simpa [himage] using hright_int.aestronglyMeasurable)
  rw [himage] at hcov_left hcov_right
  have hleft_source :
      (∫ z in Ω,
          weakJacobian (df z) • left (ambientMap F z) ∂volume) =
        ∫ z in Ω, weakJacobian (df z) •
          ((fderiv ℝ (φ : ℂ → ℝ) (ambientMap F z) v) • z)
          ∂volume := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hdf.1.measurableSet] with z hzΩ
    simp only [left, dφ]
    rw [show ambientMap F.symm (ambientMap F z) = z by
      exact ambientMap_symm_apply_ambientMap F ⟨z, hzΩ⟩]
  have hAdj : ∀ᵐ z ∂volume.restrict Ω,
      realLinearAdjugate (df z) =
        weakJacobian (df z) • dg (ambientMap F z) := by
    filter_upwards [hdg_comp, hF.weakJacobian_nonneg_ae hdf,
      hF.distortion_of_weakDifferential hdf] with z hdg hJ hdist
    rw [hdg]
    exact
      realLinearAdjugate_eq_weakJacobian_smul_realLinearPseudoInverse_of_nonneg
        (df z) hJ K hdist
  have hright_source :
      (∫ z in Ω,
          weakJacobian (df z) • right (ambientMap F z) ∂volume) =
        ∫ z in Ω, φ (ambientMap F z) •
          (realLinearAdjugate (df z) v) ∂volume := by
    apply integral_congr_ae
    filter_upwards [hAdj] with z hz
    simp only [right, hz, ContinuousLinearMap.smul_apply]
    module
  calc
    ∫ y in Ω', (fderiv ℝ (φ : ℂ → ℝ) y v) •
        ambientMap F.symm y ∂volume =
        ∫ y in Ω', left y ∂volume := by rfl
    _ = ∫ z in Ω,
          weakJacobian (df z) • left (ambientMap F z) ∂volume := hcov_left
    _ = ∫ z in Ω, weakJacobian (df z) •
          ((fderiv ℝ (φ : ℂ → ℝ) (ambientMap F z) v) • z)
          ∂volume := hleft_source
    _ = -∫ z in Ω, φ (ambientMap F z) •
          (realLinearAdjugate (df z) v) ∂volume :=
      hdf.planarAdjugate_test_identity hF.2.1 φ v
    _ = -∫ z in Ω,
          weakJacobian (df z) • right (ambientMap F z) ∂volume := by
      rw [hright_source]
    _ = -∫ y in Ω', right y ∂volume := by rw [hcov_right]
    _ = -∫ y in Ω', φ y • dg y v ∂volume := by rfl

/--
%%handwave
name:
  Inverse of a planar quasiconformal homeomorphism
statement:
  Let $\Omega,\Omega'\subseteq\mathbb C$ be open. If
  $F:\Omega\to\Omega'$ is $K$-quasiconformal, then its inverse is also
  $K$-quasiconformal.
proof:
  Choose [the locally square-integrable inverse differential candidate with the same distortion bound](lean:JJMath.Quasiconformal.IsKQuasiconformalBetween.exists_inverseDifferentialCandidate_memLpOn_compact). [The distributional inverse theorem identifies this field as the weak differential of $F^{-1}$](lean:JJMath.Quasiconformal.IsKQuasiconformalBetween.inverseDifferentialCandidate_isWeakDerivativeOn), while continuity gives local square-integrability of the inverse values. Use [symmetry of orientation preservation under inversion](lean:JJMath.Quasiconformal.PreservesPlanarOrientation.symm) for the topological condition.
-/
theorem IsKQuasiconformalBetween.symm
    {K : ℝ} {Ω Ω' : Set ℂ} {F : Ω ≃ₜ Ω'}
    (hF : IsKQuasiconformalBetween K F) :
    IsKQuasiconformalBetween K F.symm := by
  obtain ⟨df, hdf, -⟩ := hF.2.2.2
  obtain ⟨dg, hdg_comp, hdg_L2, hdist⟩ :=
    hF.exists_inverseDifferentialCandidate_memLpOn_compact hdf
  refine ⟨hF.1, hdf.1, hF.2.2.1.symm hdf.1 hF.2.1, dg, ?_, hdist⟩
  refine ⟨hF.2.1, ?_, ?_⟩
  · exact hF.inverseDifferentialCandidate_isWeakDerivativeOn
      hdf hdg_comp hdg_L2
  · intro C hC hCΩ'
    exact ⟨memLp_restrict_of_isCompact_of_continuousOn hC
      ((continuousOn_ambientMap F.symm).mono hCΩ'), hdg_L2 C hC hCΩ'⟩

/--
%%handwave
name:
  Inverse Lusin property of a planar quasiconformal homeomorphism
statement:
  Let $\Omega,\Omega'\subseteq\mathbb C$ be open. If
  $F:\Omega\to\Omega'$ is quasiconformal, then the inverse map sends null
  subsets of $\Omega'$ to null sets.
proof:
  [The inverse is quasiconformal](lean:JJMath.Quasiconformal.IsKQuasiconformalBetween.symm), so it has the Lusin $N$ property.
-/
theorem IsKQuasiconformalBetween.hasLusinNInvOn
    {K : ℝ} {Ω Ω' : Set ℂ} {F : Ω ≃ₜ Ω'}
    (hF : IsKQuasiconformalBetween K F) :
    HasLusinNInvOn F := by
  exact hF.symm.hasLusinNOn

/--
%%handwave
name:
  Strict positivity of the weak Jacobian almost everywhere
statement:
  Let $F:\Omega\to\Omega'$ be a planar quasiconformal homeomorphism between
  open sets, and let $Df$ be any weak differential of its ambient
  representative. Then
  $$
    \operatorname{Jac}f(z)>0
  $$
  for almost every $z\in\Omega$.
proof:
  The Jacobian is nonnegative almost everywhere. Choose a measurable
  representative of $Df$ and let $Z\subseteq\Omega$ be its zero-Jacobian
  locus. [The area formula gives $|F(Z)|=0$](lean:JJMath.Quasiconformal.IsKQuasiconformalBetween.volume_ambientMap_image_eq_zero_of_weakJacobian_eq_zero_ae), while [the inverse Lusin property](lean:JJMath.Quasiconformal.IsKQuasiconformalBetween.hasLusinNInvOn) gives $|Z|=0$. Thus the nonnegative Jacobian vanishes only on a null set.
-/
theorem IsKQuasiconformalBetween.weakJacobian_pos_ae
    {K : ℝ} {Ω Ω' : Set ℂ} {F : Ω ≃ₜ Ω'}
    (hF : IsKQuasiconformalBetween K F) {df : ℂ → ℂ →L[ℝ] ℂ}
    (hdf : IsLocalW12On Ω (ambientMap F) df) :
    ∀ᵐ z ∂volume.restrict Ω, 0 < weakJacobian (df z) := by
  have hdf_aesm : AEStronglyMeasurable df (volume.restrict Ω) :=
    hdf.differential_locallyIntegrableOn.aestronglyMeasurable
  have hind_aesm : AEStronglyMeasurable (Ω.indicator df) volume :=
    (aestronglyMeasurable_indicator_iff hdf.1.measurableSet).2 hdf_aesm
  let dfm : ℂ → ℂ →L[ℝ] ℂ := hind_aesm.mk (Ω.indicator df)
  have hdfm_meas : Measurable dfm :=
    hind_aesm.stronglyMeasurable_mk.measurable
  have hdfm_eq : ∀ᵐ z ∂volume.restrict Ω, dfm z = df z := by
    filter_upwards [ae_restrict_of_ae hind_aesm.ae_eq_mk,
      ae_restrict_mem hdf.1.measurableSet] with z hz hzΩ
    simpa [dfm, indicator_of_mem hzΩ] using hz.symm
  let Z : Set ℂ := Ω ∩ {z | weakJacobian (dfm z) = 0}
  have hZmeas : MeasurableSet Z := by
    exact hdf.1.measurableSet.inter
      ((measurableSet_singleton 0).preimage
        (continuous_weakJacobian.measurable.comp hdfm_meas))
  have hZΩ : Z ⊆ Ω := inter_subset_left
  have hzero : ∀ᵐ z ∂volume.restrict Z, weakJacobian (df z) = 0 := by
    have hdfm_Z := ae_restrict_of_ae_restrict_of_subset hZΩ hdfm_eq
    filter_upwards [hdfm_Z, ae_restrict_mem hZmeas] with z hz hZz
    rw [← hz]
    exact hZz.2
  have himage_zero : volume (ambientMap F '' Z) = 0 :=
    hF.volume_ambientMap_image_eq_zero_of_weakJacobian_eq_zero_ae
      hdf hZmeas hZΩ hzero
  have himageΩ' : ambientMap F '' Z ⊆ Ω' := by
    rintro y ⟨z, hzZ, rfl⟩
    let zΩ : Ω := ⟨z, hZΩ hzZ⟩
    rw [ambientMap_apply F zΩ]
    exact (F zΩ).2
  have hdouble_image_zero :
      volume (ambientMap F.symm '' (ambientMap F '' Z)) = 0 :=
    hF.hasLusinNInvOn _ himageΩ' himage_zero
  have hZzero : volume Z = 0 := by
    apply measure_mono_null _ hdouble_image_zero
    intro z hzZ
    refine ⟨ambientMap F z, ⟨z, hzZ, rfl⟩, ?_⟩
    exact ambientMap_symm_apply_ambientMap F ⟨z, hZΩ hzZ⟩
  have hnotZ : ∀ᵐ z ∂volume, z ∉ Z := by
    rw [ae_iff]
    simpa only [not_not] using hZzero
  filter_upwards [hF.weakJacobian_nonneg_ae hdf, hdfm_eq,
    ae_restrict_of_ae hnotZ, ae_restrict_mem hdf.1.measurableSet]
      with z hJ hdfmz hzZ hzΩ
  refine lt_of_le_of_ne hJ ?_
  intro hzero
  apply hzZ
  exact ⟨hzΩ, by simpa [hdfmz] using hzero.symm⟩

/--
%%handwave
name:
  Multiplicity area formula from an overlapping differentiability cover
statement:
  Let measurable sets $T_n\subseteq S$ cover a measurable set $S$.
  Suppose that $f$ has real differential $Df(x)$ on every $T_n$, relative
  to $T_n$, that $x\mapsto J(Df(x))$ is measurable, and that
  $J(Df(x))\geq0$ on $S$. Then
  $$
    \int_{\mathbb C}N(f,S,y)g(y)\,dy
      =
    \int_S J(Df(x))g(f(x))\,dx
  $$
  for every almost-everywhere measurable $g:\mathbb C\to[0,\infty]$.
proof:
  Replace the cover by its successive disjoint differences and apply [the multiplicity formula for pairwise disjoint differentiability pieces](lean:JJMath.Quasiconformal.areaFormula_preimageMultiplicity_of_countable_hasFDerivWithinAt_of_weakJacobian_nonneg).
-/
theorem areaFormula_preimageMultiplicity_of_countable_cover_hasFDerivWithinAt_of_weakJacobian_nonneg
    {S : Set ℂ} {f : ℂ → ℂ}
    {df : ℂ → ℂ →L[ℝ] ℂ}
    (hSmeas : MeasurableSet S)
    (t : ℕ → Set ℂ)
    (htmeas : ∀ n, MeasurableSet (t n))
    (htS : ∀ n, t n ⊆ S)
    (hcover : S ⊆ ⋃ n, t n)
    (hderiv :
      ∀ n x, x ∈ t n →
        HasFDerivWithinAt f (df x) (t n) x)
    (hJmeas :
      Measurable (fun x => weakJacobian (df x)))
    (hJ : ∀ x ∈ S, 0 ≤ weakJacobian (df x))
    (g : ℂ → ℝ≥0∞)
    (hg : AEMeasurable g volume) :
    ∫⁻ y,
        preimageMultiplicity f S y * g y ∂volume =
      ∫⁻ x in S,
        ENNReal.ofReal (weakJacobian (df x)) *
          g (f x) ∂volume := by
  apply
    areaFormula_preimageMultiplicity_of_countable_hasFDerivWithinAt_of_weakJacobian_nonneg
      hSmeas (disjointed t)
  · exact MeasurableSet.disjointed htmeas
  · intro n
    exact (disjointed_subset t n).trans (htS n)
  · exact disjoint_disjointed t
  · simpa only [iUnion_disjointed] using hcover
  · intro n x hx
    exact
      (hderiv n x (disjointed_subset t n hx)).mono
        (disjointed_subset t n)
  · exact hJmeas
  · exact hJ
  · exact hg

/--
%%handwave
name:
  Almost-everywhere measurability of multiplicity from differentiability pieces
statement:
  Let measurable sets $T_n\subseteq S$ cover a measurable set $S$. Suppose
  that $f$ has real differential $Df(x)$ on every $T_n$ relative to $T_n$,
  that $x\mapsto J(Df(x))$ is measurable, and that $J(Df(x))\geq0$ on $S$.
  Then $y\mapsto N(f,S,y)$ is measurable up to a null set.
proof:
  Replace the cover by its pairwise disjoint successive differences and apply [almost-everywhere measurability from pairwise disjoint differentiability pieces](lean:JJMath.Quasiconformal.areaFormula_preimageMultiplicity_of_countable_hasFDerivWithinAt_of_weakJacobian_nonneg_and_aemeasurable).
-/
theorem aemeasurable_preimageMultiplicity_of_countable_cover_hasFDerivWithinAt_of_weakJacobian_nonneg
    {S : Set ℂ} {f : ℂ → ℂ}
    {df : ℂ → ℂ →L[ℝ] ℂ}
    (hSmeas : MeasurableSet S)
    (t : ℕ → Set ℂ)
    (htmeas : ∀ n, MeasurableSet (t n))
    (htS : ∀ n, t n ⊆ S)
    (hcover : S ⊆ ⋃ n, t n)
    (hderiv :
      ∀ n x, x ∈ t n →
        HasFDerivWithinAt f (df x) (t n) x)
    (hJmeas :
      Measurable (fun x => weakJacobian (df x)))
    (hJ : ∀ x ∈ S, 0 ≤ weakJacobian (df x)) :
    AEMeasurable (preimageMultiplicity f S) volume := by
  exact
    (areaFormula_preimageMultiplicity_of_countable_hasFDerivWithinAt_of_weakJacobian_nonneg_and_aemeasurable
      hSmeas (disjointed t)
      (MeasurableSet.disjointed htmeas)
      (fun n => (disjointed_subset t n).trans (htS n))
      (disjoint_disjointed t)
      (by simpa only [iUnion_disjointed] using hcover)
      (fun n x hx =>
        (hderiv n x (disjointed_subset t n hx)).mono
          (disjointed_subset t n))
      hJmeas hJ (fun _ => 0) measurable_const.aemeasurable).1

/--
%%handwave
name:
  Measurable multiplicity and area formula from an almost-everywhere cover
statement:
  Let measurable sets $T_n\subseteq S$ cover almost every point of a set
  $S$. Suppose that $f$ has the Lusin $N$ property on $S$,
  has real differential $Df(x)$ on every $T_n$ relative to $T_n$, the
  function $x\mapsto J(Df(x))$ is measurable, and $J(Df(x))\geq0$ on $S$.
  Then, for every almost-everywhere measurable
  $g:\mathbb C\to[0,\infty]$,
  $$
    \int_{\mathbb C}N(f,S,y)g(y)\,dy
      =
    \int_S J(Df(x))g(f(x))\,dx.
  $$
  Moreover, $y\mapsto N(f,S,y)$ is measurable up to a null set.
proof:
  Apply [the multiplicity formula on the union of the differentiability pieces](lean:JJMath.Quasiconformal.areaFormula_preimageMultiplicity_of_countable_cover_hasFDerivWithinAt_of_weakJacobian_nonneg). The omitted part of $S$ is null, and Lusin $N$ makes its image null. Hence deleting it changes neither the source integral nor the target fiber multiplicity almost everywhere.
-/
theorem areaFormula_preimageMultiplicity_of_countable_cover_hasFDerivWithinAt_of_hasLusinNOn_and_aemeasurable
    {S : Set ℂ} {f : ℂ → ℂ}
    {df : ℂ → ℂ →L[ℝ] ℂ}
    (hN : HasLusinNOn S f)
    (t : ℕ → Set ℂ)
    (htmeas : ∀ n, MeasurableSet (t n))
    (htS : ∀ n, t n ⊆ S)
    (hcover :
      ∀ᵐ x ∂volume.restrict S,
        x ∈ ⋃ n, t n)
    (hderiv :
      ∀ n x, x ∈ t n →
        HasFDerivWithinAt f (df x) (t n) x)
    (hJmeas :
      Measurable (fun x => weakJacobian (df x)))
    (hJ : ∀ x ∈ S, 0 ≤ weakJacobian (df x))
    (g : ℂ → ℝ≥0∞)
    (hg : AEMeasurable g volume) :
    AEMeasurable (preimageMultiplicity f S) volume ∧
      ∫⁻ y,
          preimageMultiplicity f S y * g y ∂volume =
        ∫⁻ x in S,
          ENNReal.ofReal (weakJacobian (df x)) *
            g (f x) ∂volume := by
  let U : Set ℂ :=
    ⋃ n, t n
  have hUmeas : MeasurableSet U :=
    MeasurableSet.iUnion htmeas
  have hUS : U ⊆ S :=
    iUnion_subset htS
  have htU :
      ∀ n, t n ⊆ U := by
    intro n
    exact subset_iUnion t n
  have hformulaU :=
    areaFormula_preimageMultiplicity_of_countable_cover_hasFDerivWithinAt_of_weakJacobian_nonneg
      hUmeas t htmeas htU (Subset.rfl)
        hderiv hJmeas
        (fun x hx => hJ x (hUS hx)) g hg
  have hmultUAE :
      AEMeasurable (preimageMultiplicity f U) volume :=
    aemeasurable_preimageMultiplicity_of_countable_cover_hasFDerivWithinAt_of_weakJacobian_nonneg
      hUmeas t htmeas htU (Subset.rfl)
        hderiv hJmeas (fun x hx => hJ x (hUS hx))
  have hcoverGlobal :
      ∀ᵐ x ∂volume,
        x ∈ S → x ∈ U := by
    simpa [U] using
      ae_imp_of_ae_restrict hcover
  have hUae :
      U =ᵐ[volume] S := by
    filter_upwards [hcoverGlobal] with x hx
    apply propext
    constructor
    · exact fun hxU => hUS hxU
    · exact fun hxS => hx hxS
  have hSUzero :
      volume (S \ U) = 0 :=
    (ae_eq_set.1 hUae).2
  have himageZero :
      volume (f '' (S \ U)) = 0 :=
    hN (S \ U) diff_subset hSUzero
  have hmult :
      ∀ᵐ y ∂volume,
        preimageMultiplicity f S y =
          preimageMultiplicity f U y := by
    filter_upwards
        [compl_mem_ae_iff.mpr himageZero] with y hy
    have hfiber :
        S ∩ f ⁻¹' {y} =
          U ∩ f ⁻¹' {y} := by
      ext x
      constructor
      · intro hx
        by_cases hxU : x ∈ U
        · exact ⟨hxU, hx.2⟩
        · exfalso
          apply hy
          have hxy : f x = y := by
            simpa using hx.2
          exact
            ⟨x, ⟨hx.1, hxU⟩, hxy⟩
      · intro hx
        exact ⟨hUS hx.1, hx.2⟩
    simp only [preimageMultiplicity]
    rw [hfiber]
  have hmultSAE :
      AEMeasurable (preimageMultiplicity f S) volume :=
    hmultUAE.congr (hmult.mono fun _ hy => hy.symm)
  let H : ℂ → ℝ≥0∞ :=
    fun x =>
      ENNReal.ofReal (weakJacobian (df x)) *
        g (f x)
  refine ⟨hmultSAE, ?_⟩
  calc
    ∫⁻ y,
        preimageMultiplicity f S y * g y ∂volume =
        ∫⁻ y,
          preimageMultiplicity f U y * g y ∂volume := by
      apply lintegral_congr_ae
      filter_upwards [hmult] with y hy
      rw [hy]
    _ = ∫⁻ x in U, H x ∂volume := by
      simpa [H] using hformulaU
    _ = ∫⁻ x in S, H x ∂volume :=
      setLIntegral_congr hUae
    _ = ∫⁻ x in S,
        ENNReal.ofReal (weakJacobian (df x)) *
          g (f x) ∂volume := by
      rfl

/--
%%handwave
name:
  Measurable Sobolev multiplicity and its area formula
statement:
  Let $f\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb C)$ have weak
  differential $Df$, the Lusin $N$ property, and
  $J_f\geq0$ almost everywhere. If $S\subseteq\Omega$ is measurable, then
  for every almost-everywhere measurable $g:\mathbb C\to[0,\infty]$,
  $$
    \int_{\mathbb C}N(f,S,y)g(y)\,dy
      =
    \int_S J_f(x)g(f(x))\,dx.
  $$
  Moreover, $y\mapsto N(f,S,y)$ is measurable up to a null set.
proof:
  Choose a globally measurable representative of the weak differential and replace its negative-Jacobian values by zero; this does not change it almost everywhere. Remove one measurable null set so the representative agrees pointwise with the weak differential on the remaining source. Intersect [the countable within-differentiability cover](lean:JJMath.Quasiconformal.IsLocalW12On.exists_countable_measurable_cover_hasFDerivWithinAt) with that source and with $S$, then apply [the multiplicity formula from an almost-everywhere differentiability cover](lean:JJMath.Quasiconformal.areaFormula_preimageMultiplicity_of_countable_cover_hasFDerivWithinAt_of_hasLusinNOn).
-/
theorem IsLocalW12On.areaFormula_preimageMultiplicity_of_hasLusinNOn_of_weakJacobian_nonneg_ae_and_aemeasurable
    {Ω : Set ℂ} {f : ℂ → ℂ}
    {df : ℂ → ℂ →L[ℝ] ℂ}
    (hW : IsLocalW12On Ω f df)
    (hN : HasLusinNOn Ω f)
    (hJ :
      ∀ᵐ x ∂volume.restrict Ω,
        0 ≤ weakJacobian (df x))
    {S : Set ℂ}
    (hSmeas : MeasurableSet S)
    (hSΩ : S ⊆ Ω)
    (g : ℂ → ℝ≥0∞)
    (hg : AEMeasurable g volume) :
    AEMeasurable (preimageMultiplicity f S) volume ∧
      ∫⁻ y,
          preimageMultiplicity f S y * g y ∂volume =
        ∫⁻ x in S,
          ENNReal.ofReal (weakJacobian (df x)) *
            g (f x) ∂volume := by
  have hdfAesm :
      AEStronglyMeasurable df
        (volume.restrict Ω) :=
    hW.differential_locallyIntegrableOn.aestronglyMeasurable
  have hindAesm :
      AEStronglyMeasurable (Ω.indicator df) volume :=
    (aestronglyMeasurable_indicator_iff
      hW.1.measurableSet).2 hdfAesm
  let dfm : ℂ → ℂ →L[ℝ] ℂ :=
    hindAesm.mk (Ω.indicator df)
  have hdfmMeas : Measurable dfm :=
    hindAesm.stronglyMeasurable_mk.measurable
  have hdfmEq :
      ∀ᵐ x ∂volume.restrict Ω,
        dfm x = df x := by
    filter_upwards
        [ae_restrict_of_ae hindAesm.ae_eq_mk,
          ae_restrict_mem hW.1.measurableSet] with x hx hxΩ
    simpa [dfm, indicator_of_mem hxΩ] using hx.symm
  let dfg : ℂ → ℂ →L[ℝ] ℂ :=
    fun x =>
      if 0 ≤ weakJacobian (dfm x) then dfm x else 0
  have hdfgMeas : Measurable dfg := by
    apply Measurable.ite
    · exact measurableSet_Ici.preimage
        (continuous_weakJacobian.measurable.comp hdfmMeas)
    · exact hdfmMeas
    · exact measurable_const
  have hdfgJ :
      ∀ x, 0 ≤ weakJacobian (dfg x) := by
    intro x
    dsimp [dfg]
    split_ifs with hx
    · exact hx
    · simp [weakJacobian]
  have hdfgEq :
      ∀ᵐ x ∂volume.restrict Ω,
        dfg x = df x := by
    filter_upwards [hdfmEq, hJ] with x hx hJx
    dsimp [dfg]
    rw [if_pos (by rwa [hx]), hx]
  have hdfgEqGlobal :
      ∀ᵐ x ∂volume,
        x ∈ Ω → dfg x = df x :=
    ae_imp_of_ae_restrict hdfgEq
  let B : Set ℂ :=
    {x | ¬ (x ∈ Ω → dfg x = df x)}
  have hBzero : volume B = 0 := by
    simpa [B] using ae_iff.mp hdfgEqGlobal
  obtain ⟨N, hBN, hNmeas, hNzero⟩ :=
    exists_measurable_superset_of_null hBzero
  let C : Set ℂ :=
    Ω \ N
  have hCmeas : MeasurableSet C :=
    hW.1.measurableSet.diff hNmeas
  have hCeq :
      ∀ x ∈ C, dfg x = df x := by
    intro x hx
    have hxgood :
        x ∈ Ω → dfg x = df x := by
      by_contra hbad
      exact hx.2 (hBN hbad)
    exact hxgood hx.1
  obtain ⟨T, hTmeas, hTΩ, hTcover, hTderiv⟩ :=
    hW.exists_countable_measurable_cover_hasFDerivWithinAt
  let t : ℕ → Set ℂ :=
    fun n =>
      (S ∩ C) ∩ T n
  have htmeas :
      ∀ n, MeasurableSet (t n) := by
    intro n
    exact
      (hSmeas.inter hCmeas).inter
        (hTmeas n)
  have htS :
      ∀ n, t n ⊆ S := by
    intro n x hx
    exact hx.1.1
  have htderiv :
      ∀ n x, x ∈ t n →
        HasFDerivWithinAt f (dfg x) (t n) x := by
    intro n x hx
    have hbase :=
      (hTderiv n x hx.2).mono
        (show t n ⊆ T n by
          intro y hy
          exact hy.2)
    exact hbase.congr_fderiv
      (hCeq x hx.1.2).symm
  have hTcoverS :
      ∀ᵐ x ∂volume.restrict S,
        x ∈ ⋃ n, T n :=
    ae_restrict_of_ae_restrict_of_subset
      hSΩ hTcover
  have hnotNS :
      ∀ᵐ x ∂volume.restrict S,
        x ∉ N :=
    ae_restrict_of_ae
      (compl_mem_ae_iff.mpr hNzero)
  have htcover :
      ∀ᵐ x ∂volume.restrict S,
        x ∈ ⋃ n, t n := by
    filter_upwards
        [hTcoverS, hnotNS,
          ae_restrict_mem hSmeas] with x hxT hxN hxS
    rcases Set.mem_iUnion.mp hxT with
      ⟨n, hxn⟩
    exact Set.mem_iUnion.mpr
      ⟨n, ⟨⟨hxS, hSΩ hxS, hxN⟩, hxn⟩⟩
  have hNS : HasLusinNOn S f := by
    intro A hAS hAzero
    exact hN A (hAS.trans hSΩ) hAzero
  obtain ⟨hmultAE, hformula⟩ :=
    areaFormula_preimageMultiplicity_of_countable_cover_hasFDerivWithinAt_of_hasLusinNOn_and_aemeasurable
      hNS t htmeas htS htcover htderiv
        (continuous_weakJacobian.measurable.comp hdfgMeas)
        (fun x _ => hdfgJ x) g hg
  refine ⟨hmultAE, ?_⟩
  rw [hformula]
  apply lintegral_congr_ae
  have hdfgEqS :=
    ae_restrict_of_ae_restrict_of_subset
      hSΩ hdfgEq
  filter_upwards [hdfgEqS] with x hx
  rw [hx]

/--
%%handwave
name:
  Sobolev multiplicity area formula
statement:
  Let $f\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb C)$ have weak
  differential $Df$, the Lusin $N$ property, and $J_f\geq0$ almost
  everywhere. If $S\subseteq\Omega$ is measurable, then for every
  almost-everywhere measurable $g:\mathbb C\to[0,\infty]$,
  $$
    \int_{\mathbb C}N(f,S,y)g(y)\,dy
      =
    \int_S J_f(x)g(f(x))\,dx.
  $$
proof:
  Apply [the measurable Sobolev multiplicity formula](lean:JJMath.Quasiconformal.IsLocalW12On.areaFormula_preimageMultiplicity_of_hasLusinNOn_of_weakJacobian_nonneg_ae_and_aemeasurable) and retain its integral identity.
-/
theorem IsLocalW12On.areaFormula_preimageMultiplicity_of_hasLusinNOn_of_weakJacobian_nonneg_ae
    {Ω : Set ℂ} {f : ℂ → ℂ}
    {df : ℂ → ℂ →L[ℝ] ℂ}
    (hW : IsLocalW12On Ω f df)
    (hN : HasLusinNOn Ω f)
    (hJ :
      ∀ᵐ x ∂volume.restrict Ω,
        0 ≤ weakJacobian (df x))
    {S : Set ℂ}
    (hSmeas : MeasurableSet S)
    (hSΩ : S ⊆ Ω)
    (g : ℂ → ℝ≥0∞)
    (hg : AEMeasurable g volume) :
    ∫⁻ y,
        preimageMultiplicity f S y * g y ∂volume =
      ∫⁻ x in S,
        ENNReal.ofReal (weakJacobian (df x)) *
          g (f x) ∂volume :=
  (hW.areaFormula_preimageMultiplicity_of_hasLusinNOn_of_weakJacobian_nonneg_ae_and_aemeasurable
    hN hJ hSmeas hSΩ g hg).2

/--
%%handwave
name:
  Almost-everywhere measurability of Sobolev multiplicity
statement:
  Let $f\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb C)$ have weak
  differential $Df$, the Lusin $N$ property, and $J_f\geq0$ almost
  everywhere. If $S\subseteq\Omega$ is measurable, then
  $y\mapsto N(f,S,y)$ is measurable up to a null set.
proof:
  Apply [the measurable Sobolev multiplicity formula](lean:JJMath.Quasiconformal.IsLocalW12On.areaFormula_preimageMultiplicity_of_hasLusinNOn_of_weakJacobian_nonneg_ae_and_aemeasurable) with the zero target weight and retain its measurability conclusion.
-/
theorem IsLocalW12On.aemeasurable_preimageMultiplicity_of_hasLusinNOn_of_weakJacobian_nonneg_ae
    {Ω : Set ℂ} {f : ℂ → ℂ}
    {df : ℂ → ℂ →L[ℝ] ℂ}
    (hW : IsLocalW12On Ω f df)
    (hN : HasLusinNOn Ω f)
    (hJ :
      ∀ᵐ x ∂volume.restrict Ω,
        0 ≤ weakJacobian (df x))
    {S : Set ℂ}
    (hSmeas : MeasurableSet S)
    (hSΩ : S ⊆ Ω) :
    AEMeasurable (preimageMultiplicity f S) volume :=
  (hW.areaFormula_preimageMultiplicity_of_hasLusinNOn_of_weakJacobian_nonneg_ae_and_aemeasurable
    hN hJ hSmeas hSΩ (fun _ => 0) measurable_const.aemeasurable).1

/--
%%handwave
name:
  Jacobian measure on a source set
statement:
  For a measurable planar differential field $Df$ and a source set
  $S\subseteq\mathbb C$, the Jacobian measure on $S$ is
  $$
    J_f\,\mathbf 1_S\,dx.
  $$
  Its density is understood as the nonnegative part
  $\max(J_f,0)$, so the construction is a positive measure without any
  sign assumption.
-/
noncomputable def weakJacobianMeasureOn
    (S : Set ℂ) (df : ℂ → ℂ →L[ℝ] ℂ) : Measure ℂ :=
  (volume.restrict S).withDensity
    (fun x ↦ ENNReal.ofReal (weakJacobian (df x)))

/--
%%handwave
name:
  Pushforward Jacobian measure is multiplicity-weighted area
statement:
  Let $f\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb C)$ have the Lusin
  $N$ property and satisfy $J_f\geq0$ almost everywhere. If
  $S\subseteq\Omega$ is measurable, then
  $$
    f_\#\bigl(J_f\,\mathbf 1_S\,dx\bigr)
      =N(f,S,\cdot)\,dy.
  $$
proof:
  Test both measures against an arbitrary nonnegative measurable function.
  The pushforward integral is the source integral of the pullback test, and
  [the Sobolev multiplicity area formula](lean:JJMath.Quasiconformal.IsLocalW12On.areaFormula_preimageMultiplicity_of_hasLusinNOn_of_weakJacobian_nonneg_ae) identifies it with the multiplicity-weighted target integral.
-/
theorem IsLocalW12On.map_weakJacobianMeasureOn_eq_withDensity_preimageMultiplicity
    {Ω : Set ℂ} {f : ℂ → ℂ}
    {df : ℂ → ℂ →L[ℝ] ℂ}
    (hW : IsLocalW12On Ω f df)
    (hf : Measurable f)
    (hN : HasLusinNOn Ω f)
    (hJ :
      ∀ᵐ x ∂volume.restrict Ω,
        0 ≤ weakJacobian (df x))
    {S : Set ℂ}
    (hSmeas : MeasurableSet S)
    (hSΩ : S ⊆ Ω) :
    Measure.map f (weakJacobianMeasureOn S df) =
      volume.withDensity (preimageMultiplicity f S) := by
  have hdfAE :
      AEStronglyMeasurable df (volume.restrict S) :=
    hW.differential_locallyIntegrableOn.aestronglyMeasurable.mono_measure
      (Measure.restrict_mono_set volume hSΩ)
  have hJAE :
      AEMeasurable
        (fun x ↦ ENNReal.ofReal (weakJacobian (df x)))
        (volume.restrict S) :=
    (continuous_weakJacobian.comp_aestronglyMeasurable
      hdfAE).aemeasurable.ennreal_ofReal
  have hmultAE :
      AEMeasurable (preimageMultiplicity f S) volume :=
    hW.aemeasurable_preimageMultiplicity_of_hasLusinNOn_of_weakJacobian_nonneg_ae
      hN hJ hSmeas hSΩ
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_map' hg.aemeasurable hf.aemeasurable]
  change
    (∫⁻ x : ℂ, (g ∘ f) x ∂
        (volume.restrict S).withDensity
          (fun z ↦ ENNReal.ofReal (weakJacobian (df z)))) =
      ∫⁻ y : ℂ, g y ∂
        volume.withDensity (preimageMultiplicity f S)
  rw [lintegral_withDensity_eq_lintegral_mul₀
    hJAE ((hg.comp hf).aemeasurable)]
  rw [lintegral_withDensity_eq_lintegral_mul₀
    hmultAE hg.aemeasurable]
  exact
    (hW.areaFormula_preimageMultiplicity_of_hasLusinNOn_of_weakJacobian_nonneg_ae
      hN hJ hSmeas hSΩ g hg.aemeasurable).symm

/--
%%handwave
name:
  Weighted Jacobian measure on a source set
statement:
  Given a real source weight $q$, the weighted Jacobian measure on
  $S\subseteq\mathbb C$ is
  $$
    q_+(x)(J_f(x))_+\,\mathbf 1_S(x)\,dx,
  $$
  where $a_+=\max(a,0)$.
-/
noncomputable def weightedWeakJacobianMeasureOn
    (S : Set ℂ) (df : ℂ → ℂ →L[ℝ] ℂ)
    (q : ℂ → ℝ) : Measure ℂ :=
  (weakJacobianMeasureOn S df).withDensity
    (fun x ↦ ENNReal.ofReal (q x))

/--
%%handwave
name:
  Finiteness of Jacobian measure on a compact source set
statement:
  If $f\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb C)$ and
  $S\subseteq\Omega$ is compact, then the positive Jacobian measure
  $(J_f)_+\mathbf 1_S\,dx$ is finite.
proof:
  The weak differential belongs to $L^2(S)$, so its Jacobian belongs to
  $L^1(S)$. Hence its positive part has finite integral.
-/
theorem IsLocalW12On.isFiniteMeasure_weakJacobianMeasureOn_of_compact
    {Ω : Set ℂ} {f : ℂ → ℂ}
    {df : ℂ → ℂ →L[ℝ] ℂ}
    (hW : IsLocalW12On Ω f df)
    {S : Set ℂ} (hS : IsCompact S) (hSΩ : S ⊆ Ω) :
    IsFiniteMeasure (weakJacobianMeasureOn S df) := by
  have hJint :
      Integrable (fun x ↦ weakJacobian (df x))
        (volume.restrict S) :=
    weakJacobian_integrable_of_memLp_two
      (hW.2.2 S hS hSΩ).2
  exact
    isFiniteMeasure_withDensity_ofReal
      hJint.hasFiniteIntegral

/--
%%handwave
name:
  Finiteness of a cutoff-weighted Jacobian measure
statement:
  Let $f\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb C)$, let
  $S\subseteq\Omega$ be compact, and let $\chi$ be smooth and compactly
  supported. Then
  $$
    \chi(x)^2(J_f(x))_+\,\mathbf 1_S(x)\,dx
  $$
  is a finite measure.
proof:
  [The positive Jacobian measure is finite on $S$](lean:JJMath.Quasiconformal.IsLocalW12On.isFiniteMeasure_weakJacobianMeasureOn_of_compact). The function $\chi^2$ is continuous and compactly supported, hence integrable against every finite measure.
-/
theorem IsLocalW12On.isFiniteMeasure_weightedWeakJacobianMeasureOn_sq_of_compact
    {Ω : Set ℂ} {f : ℂ → ℂ}
    {df : ℂ → ℂ →L[ℝ] ℂ}
    (hW : IsLocalW12On Ω f df)
    {S : Set ℂ} (hS : IsCompact S) (hSΩ : S ⊆ Ω)
    (χ :
      JJMath.Uniformization.SmoothCompactlySupportedManifoldCoordinateFunction
        (Set.univ : Set ℂ)) :
    IsFiniteMeasure
      (weightedWeakJacobianMeasureOn S df
        (fun x ↦ χ x ^ 2)) := by
  let μ : Measure ℂ := weakJacobianMeasureOn S df
  haveI hμfin : IsFiniteMeasure μ := by
    dsimp [μ]
    exact
      hW.isFiniteMeasure_weakJacobianMeasureOn_of_compact
        hS hSΩ
  have hqcont :
      Continuous (fun x : ℂ ↦ χ x ^ 2) :=
    χ.smooth.continuous.pow 2
  have hχcompact :
      HasCompactSupport (χ : ℂ → ℝ) :=
    χ.compact_support
  have hqcompact :
      HasCompactSupport (fun x : ℂ ↦ χ x ^ 2) := by
    simpa [pow_two] using hχcompact.mul_right
  have hqint :
      Integrable (fun x : ℂ ↦ χ x ^ 2) μ :=
    hqcont.integrable_of_hasCompactSupport hqcompact
  change
    IsFiniteMeasure
      (μ.withDensity
        (fun x ↦ ENNReal.ofReal (χ x ^ 2)))
  exact
    isFiniteMeasure_withDensity_ofReal
      hqint.hasFiniteIntegral

/--
%%handwave
name:
  Absolute continuity of weighted Jacobian pushforward
statement:
  Let $f\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb C)$ be measurable, have
  the Lusin $N$ property, and satisfy $J_f\geq0$ almost everywhere. For every
  measurable $S\subseteq\Omega$ and every real source weight $q$,
  $$
    f_\#\bigl(q_+(J_f)_+\mathbf 1_S\,dx\bigr)\ll dy.
  $$
proof:
  The weighted source measure is absolutely continuous with respect to the
  unweighted Jacobian measure. Push this domination forward. By [the measure form of the area formula](lean:JJMath.Quasiconformal.IsLocalW12On.map_weakJacobianMeasureOn_eq_withDensity_preimageMultiplicity), the latter pushforward is multiplicity-weighted area and is therefore absolutely continuous with respect to area.
-/
theorem IsLocalW12On.map_weightedWeakJacobianMeasureOn_absolutelyContinuous
    {Ω : Set ℂ} {f : ℂ → ℂ}
    {df : ℂ → ℂ →L[ℝ] ℂ}
    (hW : IsLocalW12On Ω f df)
    (hf : Measurable f)
    (hN : HasLusinNOn Ω f)
    (hJ :
      ∀ᵐ x ∂volume.restrict Ω,
        0 ≤ weakJacobian (df x))
    {S : Set ℂ}
    (hSmeas : MeasurableSet S)
    (hSΩ : S ⊆ Ω)
    (q : ℂ → ℝ) :
    Measure.map f (weightedWeakJacobianMeasureOn S df q) ≪
      volume := by
  have hsource :
      weightedWeakJacobianMeasureOn S df q ≪
        weakJacobianMeasureOn S df :=
    withDensity_absolutelyContinuous _ _
  have hmap := hsource.map hf
  rw [hW.map_weakJacobianMeasureOn_eq_withDensity_preimageMultiplicity
    hf hN hJ hSmeas hSΩ] at hmap
  exact
    hmap.trans
      (withDensity_absolutelyContinuous _ _)

/--
%%handwave
name:
  Density of a weighted Jacobian pushforward
statement:
  The weighted Jacobian density associated with $f$, a source set $S$, a
  weak differential $Df$, and a source weight $q$ is the real
  Radon--Nikodym density
  $$
    \rho(y)=
      \frac{d\,f_\#\!\left(q_+(J_f)_+\mathbf 1_S\,dx\right)}{dy}(y).
  $$
-/
noncomputable def weightedWeakJacobianDensity
    (f : ℂ → ℂ) (S : Set ℂ)
    (df : ℂ → ℂ →L[ℝ] ℂ) (q : ℂ → ℝ) :
    ℂ → ℝ :=
  fun y ↦
    ((Measure.map f
      (weightedWeakJacobianMeasureOn S df q)).rnDeriv
        volume y).toReal

/--
%%handwave
name:
  Integrability of a finite weighted Jacobian density
statement:
  If the weighted source Jacobian measure is finite, then its pushforward
  density $\rho$ belongs to $L^1(\mathbb C)$.
proof:
  A pushforward of a finite measure is finite, and the real
  Radon--Nikodym density of a finite measure is integrable.
-/
theorem integrable_weightedWeakJacobianDensity
    {f : ℂ → ℂ} {S : Set ℂ}
    {df : ℂ → ℂ →L[ℝ] ℂ} {q : ℂ → ℝ}
    [IsFiniteMeasure (weightedWeakJacobianMeasureOn S df q)] :
    Integrable
      (weightedWeakJacobianDensity f S df q)
      volume := by
  let μ : Measure ℂ :=
    Measure.map f (weightedWeakJacobianMeasureOn S df q)
  haveI : IsFiniteMeasure μ :=
    Measure.isFiniteMeasure_map
      (weightedWeakJacobianMeasureOn S df q) f
  exact
    Measure.integrable_toReal_rnDeriv

/--
%%handwave
name:
  Source integral for a weighted Jacobian measure
statement:
  Let $f\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb C)$, let
  $S\subseteq\Omega$, and suppose $J_f\geq0$ almost everywhere on $S$. If
  $q\geq0$ is measurable, then every real function $g$ satisfies
  $$
    \int_{\mathbb C}g(f(x))\,
      d\!\left(q(J_f)_+\mathbf 1_S\,dx\right)
      =
    \int_S q(x)J_f(x)g(f(x))\,dx.
  $$
proof:
  Expand the two successive density changes. Nonnegativity of $q$ and the
  almost-everywhere nonnegativity of $J_f$ remove both positive-part
  operations.
-/
theorem IsLocalW12On.integral_comp_weightedWeakJacobianMeasureOn
    {Ω S : Set ℂ} {f : ℂ → ℂ}
    {df : ℂ → ℂ →L[ℝ] ℂ}
    (hW : IsLocalW12On Ω f df)
    (hSΩ : S ⊆ Ω)
    (q : ℂ → ℝ)
    (hqmeas : Measurable q)
    (hq : ∀ x, 0 ≤ q x)
    (hJ :
      ∀ᵐ x ∂volume.restrict S,
        0 ≤ weakJacobian (df x))
    (g : ℂ → ℝ) :
    (∫ x : ℂ, g (f x) ∂
        weightedWeakJacobianMeasureOn S df q) =
      ∫ x in S,
        q x * weakJacobian (df x) * g (f x)
        ∂volume := by
  let μJ : Measure ℂ :=
    (volume.restrict S).withDensity
      (fun z ↦ ENNReal.ofReal (weakJacobian (df z)))
  have hdfAE :
      AEStronglyMeasurable df (volume.restrict S) :=
    hW.differential_locallyIntegrableOn.aestronglyMeasurable.mono_measure
      (Measure.restrict_mono_set volume hSΩ)
  have hJAE :
      AEMeasurable
        (fun x ↦ ENNReal.ofReal (weakJacobian (df x)))
        (volume.restrict S) :=
    (continuous_weakJacobian.comp_aestronglyMeasurable
      hdfAE).aemeasurable.ennreal_ofReal
  have hqAE :
      AEMeasurable
        (fun x : ℂ ↦ ENNReal.ofReal (q x)) μJ :=
    (ENNReal.measurable_ofReal.comp hqmeas).aemeasurable
  change
    (∫ x : ℂ, g (f x) ∂
        μJ.withDensity
          (fun z ↦ ENNReal.ofReal (q z))) = _
  rw [integral_withDensity_eq_integral_toReal_smul₀
    hqAE
    (Filter.Eventually.of_forall fun _ ↦
      ENNReal.ofReal_lt_top)]
  dsimp [μJ]
  rw [integral_withDensity_eq_integral_toReal_smul₀
    hJAE
    (Filter.Eventually.of_forall fun _ ↦
      ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [hJ] with x hx
  simp [ENNReal.toReal_ofReal, hq x, hx, smul_eq_mul]
  ring

/--
%%handwave
name:
  Radon--Nikodym pairing for a weighted Jacobian density
statement:
  Suppose the weighted source Jacobian measure is finite and its
  pushforward by $f$ is absolutely continuous with respect to planar area.
  If $\rho$ is its weighted Jacobian density, then for every real function
  $g$,
  $$
    \int_{\mathbb C}\rho(y)g(y)\,dy
      =
    \int_{\mathbb C}g(y)\,
      d f_\#\!\left(q_+(J_f)_+\mathbf 1_S\,dx\right)(y).
  $$
proof:
  This is the integral form of the Radon--Nikodym theorem.
-/
theorem integral_weightedWeakJacobianDensity_smul
    {f : ℂ → ℂ} {S : Set ℂ}
    {df : ℂ → ℂ →L[ℝ] ℂ} {q : ℂ → ℝ}
    [IsFiniteMeasure (weightedWeakJacobianMeasureOn S df q)]
    (hAC :
      Measure.map f (weightedWeakJacobianMeasureOn S df q) ≪
        volume)
    (g : ℂ → ℝ) :
    (∫ y : ℂ,
        weightedWeakJacobianDensity f S df q y • g y
        ∂volume) =
      ∫ y : ℂ, g y ∂
        Measure.map f
          (weightedWeakJacobianMeasureOn S df q) := by
  let μ : Measure ℂ :=
    Measure.map f
      (weightedWeakJacobianMeasureOn S df q)
  haveI : IsFiniteMeasure μ :=
    Measure.isFiniteMeasure_map
      (weightedWeakJacobianMeasureOn S df q) f
  simpa [weightedWeakJacobianDensity, μ] using
    (integral_rnDeriv_smul hAC (f := g))

/--
%%handwave
name:
  Real Sobolev multiplicity area formula for nonnegative weights
statement:
  Let $f\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb C)$ have weak
  differential $Df$, the Lusin $N$ property, and $J_f\geq0$ almost
  everywhere. Let $S\subseteq\Omega$ be measurable and let
  $\psi:\mathbb C\to[0,\infty)$ be measurable. If
  $x\mapsto J_f(x)\psi(f(x))$ is integrable on $S$, then
  $$
    \int_{\mathbb C}N(f,S,y)\psi(y)\,dy
      =
    \int_S J_f(x)\psi(f(x))\,dx,
  $$
  where the extended multiplicity on the left is interpreted as a real
  number.
proof:
  Apply [the extended Sobolev multiplicity formula](lean:JJMath.Quasiconformal.IsLocalW12On.areaFormula_preimageMultiplicity_of_hasLusinNOn_of_weakJacobian_nonneg_ae) to the weight $\operatorname{ofReal}\psi$. Source integrability makes both extended integrals finite. Use [almost-everywhere measurability of multiplicity](lean:JJMath.Quasiconformal.IsLocalW12On.aemeasurable_preimageMultiplicity_of_hasLusinNOn_of_weakJacobian_nonneg_ae) and take real parts of the two extended integrals.
-/
theorem IsLocalW12On.integral_preimageMultiplicity_toReal_mul_eq_integral_weakJacobian_mul_of_hasLusinNOn_of_weakJacobian_nonneg_ae
    {Ω : Set ℂ} {f : ℂ → ℂ}
    {df : ℂ → ℂ →L[ℝ] ℂ}
    (hW : IsLocalW12On Ω f df)
    (hN : HasLusinNOn Ω f)
    (hJ :
      ∀ᵐ x ∂volume.restrict Ω,
        0 ≤ weakJacobian (df x))
    {S : Set ℂ}
    (hSmeas : MeasurableSet S)
    (hSΩ : S ⊆ Ω)
    (ψ : ℂ → ℝ)
    (hψmeas : Measurable ψ)
    (hψnonneg : ∀ y, 0 ≤ ψ y)
    (hint : Integrable
      (fun x ↦ weakJacobian (df x) * ψ (f x))
      (volume.restrict S)) :
    (∫ y : ℂ,
        (preimageMultiplicity f S y).toReal * ψ y ∂volume) =
      ∫ x in S,
        weakJacobian (df x) * ψ (f x) ∂volume := by
  let G : ℂ → ℝ≥0∞ := fun y ↦
    preimageMultiplicity f S y * ENNReal.ofReal (ψ y)
  let H : ℂ → ℝ≥0∞ := fun x ↦
    ENNReal.ofReal
      (weakJacobian (df x) * ψ (f x))
  have hmultAE :
      AEMeasurable (preimageMultiplicity f S) volume :=
    hW.aemeasurable_preimageMultiplicity_of_hasLusinNOn_of_weakJacobian_nonneg_ae
      hN hJ hSmeas hSΩ
  have hGAE : AEMeasurable G volume := by
    exact hmultAE.mul
      (ENNReal.measurable_ofReal.comp hψmeas).aemeasurable
  have harea :=
    hW.areaFormula_preimageMultiplicity_of_hasLusinNOn_of_weakJacobian_nonneg_ae
      hN hJ hSmeas hSΩ
        (fun y ↦ ENNReal.ofReal (ψ y))
        (ENNReal.measurable_ofReal.comp hψmeas).aemeasurable
  have hJS :
      ∀ᵐ x ∂volume.restrict S,
        0 ≤ weakJacobian (df x) :=
    ae_restrict_of_ae_restrict_of_subset hSΩ hJ
  have hsource :
      (∫⁻ x in S,
          ENNReal.ofReal (weakJacobian (df x)) *
            ENNReal.ofReal (ψ (f x)) ∂volume) =
        ∫⁻ x, H x ∂volume.restrict S := by
    apply lintegral_congr_ae
    filter_upwards [hJS] with x hx
    rw [← ENNReal.ofReal_mul hx]
  have harea' :
      ∫⁻ y, G y ∂volume =
        ∫⁻ x, H x ∂volume.restrict S := by
    simpa [G] using harea.trans hsource
  have hH_ne_top :
      ∫⁻ x, H x ∂volume.restrict S ≠ ∞ := by
    simpa [H] using hint.lintegral_lt_top.ne
  have hG_ne_top :
      ∫⁻ y, G y ∂volume ≠ ∞ := by
    rw [harea']
    exact hH_ne_top
  have hG_lt_top :
      ∀ᵐ y ∂volume, G y < ∞ :=
    ae_lt_top' hGAE hG_ne_top
  have hHAE :
      AEMeasurable H (volume.restrict S) :=
    hint.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hH_lt_top :
      ∀ᵐ x ∂volume.restrict S, H x < ∞ :=
    ae_lt_top' hHAE hH_ne_top
  calc
    (∫ y : ℂ,
        (preimageMultiplicity f S y).toReal * ψ y ∂volume) =
        ∫ y : ℂ, (G y).toReal ∂volume := by
      apply integral_congr_ae
      filter_upwards with y
      simp [G, ENNReal.toReal_mul, hψnonneg y]
    _ = (∫⁻ y, G y ∂volume).toReal :=
      integral_toReal hGAE hG_lt_top
    _ = (∫⁻ x, H x ∂volume.restrict S).toReal := by
      rw [harea']
    _ = ∫ x, (H x).toReal ∂volume.restrict S :=
      (integral_toReal hHAE hH_lt_top).symm
    _ = ∫ x in S,
        weakJacobian (df x) * ψ (f x) ∂volume := by
      apply integral_congr_ae
      filter_upwards [hJS] with x hx
      exact ENNReal.toReal_ofReal
        (mul_nonneg hx (hψnonneg (f x)))

/--
%%handwave
name:
  Integrability of weighted Sobolev multiplicity
statement:
  Let $f\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb C)$ have weak
  differential $Df$, the Lusin $N$ property, and $J_f\geq0$ almost
  everywhere. Let $S\subseteq\Omega$ be measurable and let
  $\psi:\mathbb C\to[0,\infty)$ be measurable. If
  $x\mapsto J_f(x)\psi(f(x))$ is integrable on $S$, then
  $y\mapsto N(f,S,y)\psi(y)$, with extended multiplicity interpreted as a
  real number, is integrable on $\mathbb C$.
proof:
  The extended Sobolev multiplicity formula identifies the target
  nonnegative integral with the finite source integral. Almost-everywhere
  measurability of multiplicity then permits taking real parts.
-/
theorem IsLocalW12On.integrable_preimageMultiplicity_toReal_mul_of_hasLusinNOn_of_weakJacobian_nonneg_ae
    {Ω : Set ℂ} {f : ℂ → ℂ}
    {df : ℂ → ℂ →L[ℝ] ℂ}
    (hW : IsLocalW12On Ω f df)
    (hN : HasLusinNOn Ω f)
    (hJ :
      ∀ᵐ x ∂volume.restrict Ω,
        0 ≤ weakJacobian (df x))
    {S : Set ℂ}
    (hSmeas : MeasurableSet S)
    (hSΩ : S ⊆ Ω)
    (ψ : ℂ → ℝ)
    (hψmeas : Measurable ψ)
    (hψnonneg : ∀ y, 0 ≤ ψ y)
    (hint : Integrable
      (fun x ↦ weakJacobian (df x) * ψ (f x))
      (volume.restrict S)) :
    Integrable
      (fun y ↦ (preimageMultiplicity f S y).toReal * ψ y)
      volume := by
  let G : ℂ → ℝ≥0∞ := fun y ↦
    preimageMultiplicity f S y * ENNReal.ofReal (ψ y)
  have hmultAE :
      AEMeasurable (preimageMultiplicity f S) volume :=
    hW.aemeasurable_preimageMultiplicity_of_hasLusinNOn_of_weakJacobian_nonneg_ae
      hN hJ hSmeas hSΩ
  have hGAE : AEMeasurable G volume := by
    exact hmultAE.mul
      (ENNReal.measurable_ofReal.comp hψmeas).aemeasurable
  have harea :=
    hW.areaFormula_preimageMultiplicity_of_hasLusinNOn_of_weakJacobian_nonneg_ae
      hN hJ hSmeas hSΩ
        (fun y ↦ ENNReal.ofReal (ψ y))
        (ENNReal.measurable_ofReal.comp hψmeas).aemeasurable
  have hJS :
      ∀ᵐ x ∂volume.restrict S,
        0 ≤ weakJacobian (df x) :=
    ae_restrict_of_ae_restrict_of_subset hSΩ hJ
  have hsource_ne_top :
      (∫⁻ x in S,
          ENNReal.ofReal (weakJacobian (df x)) *
            ENNReal.ofReal (ψ (f x)) ∂volume) ≠ ∞ := by
    have heq :
        (∫⁻ x in S,
            ENNReal.ofReal (weakJacobian (df x)) *
              ENNReal.ofReal (ψ (f x)) ∂volume) =
          ∫⁻ x in S,
            ENNReal.ofReal
              (weakJacobian (df x) * ψ (f x)) ∂volume := by
      apply lintegral_congr_ae
      filter_upwards [hJS] with x hx
      rw [ENNReal.ofReal_mul hx]
    rw [heq]
    exact hint.lintegral_lt_top.ne
  have hG_ne_top :
      ∫⁻ y, G y ∂volume ≠ ∞ := by
    simpa [G] using harea.trans_ne hsource_ne_top
  have htoReal :
      Integrable (fun y ↦ (G y).toReal) volume :=
    integrable_toReal_of_lintegral_ne_top hGAE hG_ne_top
  apply htoReal.congr
  filter_upwards with y
  simp [G, ENNReal.toReal_mul, hψnonneg y]

end

end Quasiconformal

end JJMath
