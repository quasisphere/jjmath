import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Smooth implicit level coordinates on a surface

A nonzero real covector on the complex plane, together with its oriented
quarter-turn, gives real product coordinates.  The smooth inverse-function
theorem therefore upgrades a regular level to a genuinely smooth local
product chart.
-/

open Set
open scoped Manifold Topology ContDiff

namespace JJMath.Manifold

noncomputable section

section PartialDiffeomorph

variable {k : Type*} [NontriviallyNormedField k]
variable {E F G : Type*}
variable [NormedAddCommGroup E] [NormedSpace k E]
variable [NormedAddCommGroup F] [NormedSpace k F]
variable [NormedAddCommGroup G] [NormedSpace k G]
variable {H H' H'' : Type*}
variable [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
variable {M N P : Type*}
variable [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P]
variable [ChartedSpace H M] [ChartedSpace H' N] [ChartedSpace H'' P]
variable {I : ModelWithCorners k E H} {J : ModelWithCorners k F H'}
variable {K : ModelWithCorners k G H''} {n : WithTop ℕ∞}

/-- An element of the maximal smooth atlas, viewed as a partial
diffeomorphism from the manifold to its model space. -/
def partialDiffeomorphOfMemMaximalAtlas
    [IsManifold I n M]
    (e : OpenPartialHomeomorph M H) (he : e ∈ IsManifold.maximalAtlas I n M) :
    PartialDiffeomorph I I M H n where
  toPartialEquiv := e.toPartialEquiv
  open_source := e.open_source
  open_target := e.open_target
  contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas he
  contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas he

/-- Composition of partial diffeomorphisms, on the maximal open set where
the two maps can be composed. -/
protected def PartialDiffeomorph.trans
    (Phi : PartialDiffeomorph I J M N n)
    (Psi : PartialDiffeomorph J K N P n) :
    PartialDiffeomorph I K M P n where
  toPartialEquiv := Phi.toPartialEquiv.trans Psi.toPartialEquiv
  open_source :=
    (Phi.toOpenPartialHomeomorph.trans Psi.toOpenPartialHomeomorph).open_source
  open_target :=
    (Phi.toOpenPartialHomeomorph.trans Psi.toOpenPartialHomeomorph).open_target
  contMDiffOn_toFun := by
    rw [PartialEquiv.trans_source]
    exact Psi.contMDiffOn_toFun.comp
      (Phi.contMDiffOn_toFun.mono inter_subset_left) inter_subset_right
  contMDiffOn_invFun := by
    rw [PartialEquiv.trans_target]
    exact Phi.contMDiffOn_invFun.comp
      (Psi.contMDiffOn_invFun.mono inter_subset_left) inter_subset_right

/-- Restrict the source of a partial diffeomorphism to an open set. -/
protected def PartialDiffeomorph.restrOpen
    (Phi : PartialDiffeomorph I J M N n) (s : Set M) (hs : IsOpen s) :
    PartialDiffeomorph I J M N n where
  toPartialEquiv := Phi.toPartialEquiv.restr s
  open_source := by
    rw [PartialEquiv.restr_source]
    exact Phi.open_source.inter hs
  open_target :=
    (Phi.toOpenPartialHomeomorph.restrOpen s hs).open_target
  contMDiffOn_toFun := by
    apply Phi.contMDiffOn_toFun.mono
    rw [PartialEquiv.restr_source]
    exact inter_subset_left
  contMDiffOn_invFun := by
    apply Phi.contMDiffOn_invFun.mono
    rw [PartialEquiv.restr_target]
    exact inter_subset_left

/-- Restrict the target of a partial diffeomorphism to an open set. -/
protected def PartialDiffeomorph.restrTargetOpen
    (Phi : PartialDiffeomorph I J M N n) (t : Set N) (ht : IsOpen t) :
    PartialDiffeomorph I J M N n :=
  (JJMath.Manifold.PartialDiffeomorph.restrOpen Phi.symm t ht).symm

@[simp]
theorem PartialDiffeomorph.trans_apply
    (Phi : PartialDiffeomorph I J M N n)
    (Psi : PartialDiffeomorph J K N P n) (x : M) :
    PartialDiffeomorph.trans Phi Psi x = Psi (Phi x) :=
  rfl

@[simp]
theorem PartialDiffeomorph.restrOpen_apply
    (Phi : PartialDiffeomorph I J M N n) (s : Set M) (hs : IsOpen s) (x : M) :
    PartialDiffeomorph.restrOpen Phi s hs x = Phi x :=
  rfl

end PartialDiffeomorph

/-- The oriented tangential covector associated to a real covector on the
complex plane. -/
def surfaceQuarterTurnCovector (dr : ℂ →L[ℝ] ℝ) : ℂ →L[ℝ] ℝ :=
  (-dr Complex.I) • Complex.reCLM + dr 1 • Complex.imCLM

theorem realCovector_apply_eq_re_im
    (dr : ℂ →L[ℝ] ℝ) (z : ℂ) :
    dr z = dr 1 * z.re + dr Complex.I * z.im := by
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    apply Complex.ext <;> simp
  calc
    dr z = dr (z.re • (1 : ℂ) + z.im • Complex.I) := congrArg dr hz
    _ = z.re • dr 1 + z.im • dr Complex.I := by
      rw [map_add, map_smul, map_smul]
    _ = dr 1 * z.re + dr Complex.I * z.im := by
      simp [smul_eq_mul, mul_comm]

theorem surfaceQuarterTurnCovector_apply
    (dr : ℂ →L[ℝ] ℝ) (z : ℂ) :
    surfaceQuarterTurnCovector dr z =
      -(dr Complex.I) * z.re + dr 1 * z.im := by
  simp [surfaceQuarterTurnCovector, smul_eq_mul,
    Complex.reCLM_apply, Complex.imCLM_apply]

/-- Quarter-turning a nonzero real covector on the complex plane again gives
a nonzero covector. -/
theorem surfaceQuarterTurnCovector_ne_zero
    {dr : ℂ →L[ℝ] ℝ} (hdr : dr ≠ 0) :
    surfaceQuarterTurnCovector dr ≠ 0 := by
  intro hzero
  have hI := congrArg (fun L : ℂ →L[ℝ] ℝ => L Complex.I) hzero
  have h1 := congrArg (fun L : ℂ →L[ℝ] ℝ => L 1) hzero
  have hdr1 : dr 1 = 0 := by
    simpa [surfaceQuarterTurnCovector_apply] using hI
  have hdrI : dr Complex.I = 0 := by
    simpa [surfaceQuarterTurnCovector_apply] using h1
  apply hdr
  ext z
  rw [ContinuousLinearMap.zero_apply, realCovector_apply_eq_re_im,
    hdr1, hdrI]
  ring

/-- The normal and oriented tangential covectors form an invertible real
linear coordinate map whenever the normal covector is nonzero. -/
noncomputable def surfaceRegularCovectorEquiv
    (dr : ℂ →L[ℝ] ℝ) (hdr : dr ≠ 0) :
    ℂ ≃L[ℝ] ℝ × ℝ := by
  let L : ℂ →L[ℝ] ℝ × ℝ := dr.prod (surfaceQuarterTurnCovector dr)
  have hs : dr 1 ^ 2 + dr Complex.I ^ 2 ≠ 0 := by
    intro hs_zero
    have ha : dr 1 = 0 := by nlinarith [sq_nonneg (dr 1), sq_nonneg (dr Complex.I)]
    have hb : dr Complex.I = 0 := by
      nlinarith [sq_nonneg (dr 1), sq_nonneg (dr Complex.I)]
    apply hdr
    ext z
    rw [ContinuousLinearMap.zero_apply, realCovector_apply_eq_re_im, ha, hb]
    ring
  have hinj : Function.Injective L := by
    intro z w hzw
    have hnormal : dr z = dr w := congrArg Prod.fst hzw
    have htangent :
        surfaceQuarterTurnCovector dr z =
          surfaceQuarterTurnCovector dr w := congrArg Prod.snd hzw
    have hre : z.re = w.re := by
      have hnormal' :
          dr 1 * z.re + dr Complex.I * z.im =
            dr 1 * w.re + dr Complex.I * w.im := by
        calc
          _ = dr z := (realCovector_apply_eq_re_im dr z).symm
          _ = dr w := hnormal
          _ = _ := realCovector_apply_eq_re_im dr w
      have htangent' :
          -(dr Complex.I) * z.re + dr 1 * z.im =
            -(dr Complex.I) * w.re + dr 1 * w.im := by
        calc
          _ = surfaceQuarterTurnCovector dr z :=
            (surfaceQuarterTurnCovector_apply dr z).symm
          _ = surfaceQuarterTurnCovector dr w := htangent
          _ = _ := surfaceQuarterTurnCovector_apply dr w
      have hmul :
          (dr 1 ^ 2 + dr Complex.I ^ 2) * (z.re - w.re) = 0 := by
        linear_combination
          (dr 1) * hnormal' - (dr Complex.I) * htangent'
      exact sub_eq_zero.mp (mul_eq_zero.mp hmul |>.resolve_left hs)
    have him : z.im = w.im := by
      have hnormal' :
          dr 1 * z.re + dr Complex.I * z.im =
            dr 1 * w.re + dr Complex.I * w.im := by
        calc
          _ = dr z := (realCovector_apply_eq_re_im dr z).symm
          _ = dr w := hnormal
          _ = _ := realCovector_apply_eq_re_im dr w
      have htangent' :
          -(dr Complex.I) * z.re + dr 1 * z.im =
            -(dr Complex.I) * w.re + dr 1 * w.im := by
        calc
          _ = surfaceQuarterTurnCovector dr z :=
            (surfaceQuarterTurnCovector_apply dr z).symm
          _ = surfaceQuarterTurnCovector dr w := htangent
          _ = _ := surfaceQuarterTurnCovector_apply dr w
      have hmul :
          (dr 1 ^ 2 + dr Complex.I ^ 2) * (z.im - w.im) = 0 := by
        linear_combination
          (dr Complex.I) * hnormal' + (dr 1) * htangent'
      exact sub_eq_zero.mp (mul_eq_zero.mp hmul |>.resolve_left hs)
    exact Complex.ext hre him
  have hsurj : Function.Surjective L := by
    rintro ⟨u, v⟩
    let s : ℝ := dr 1 ^ 2 + dr Complex.I ^ 2
    let z : ℂ :=
      ⟨(dr 1 * u - dr Complex.I * v) / s,
        (dr Complex.I * u + dr 1 * v) / s⟩
    refine ⟨z, ?_⟩
    apply Prod.ext
    · change dr z = u
      rw [realCovector_apply_eq_re_im]
      dsimp [z]
      field_simp [s, hs]
      ring
    · change surfaceQuarterTurnCovector dr z = v
      rw [surfaceQuarterTurnCovector_apply]
      dsimp [z]
      field_simp [s, hs]
      ring
  exact ContinuousLinearEquiv.ofBijective L
    (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr hsurj)

/-- Smooth product coordinates centered at a regular point of a real-valued
function on the complex plane.  The first coordinate is the function itself,
and the coordinate inverse is smooth at the distinguished target point. -/
theorem exists_smoothRegularLevelProductChart
    {r : ℂ → ℝ} {z₀ : ℂ}
    (hr : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r z₀)
    {dr : ℂ →L[ℝ] ℝ} (hr' : HasFDerivAt r dr z₀)
    (hdr : dr ≠ 0) :
    ∃ Φ : OpenPartialHomeomorph ℂ (ℝ × ℝ),
      z₀ ∈ Φ.source ∧
      Φ z₀ = (r z₀, 0) ∧
      (∀ z ∈ Φ.source, (Φ z).1 = r z) ∧
      ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ.symm (r z₀, 0) := by
  let A : ℂ ≃L[ℝ] ℝ × ℝ := surfaceRegularCovectorEquiv dr hdr
  let F : ℂ → ℝ × ℝ :=
    fun z =>
      (r z,
        surfaceQuarterTurnCovector dr z - surfaceQuarterTurnCovector dr z₀)
  have hF : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F z₀ := by
    apply hr.prodMk
    exact (surfaceQuarterTurnCovector dr).contDiff.contDiffAt.sub contDiffAt_const
  have hF' : HasFDerivAt F (A : ℂ →L[ℝ] ℝ × ℝ) z₀ := by
    change HasFDerivAt F
      (dr.prod (surfaceQuarterTurnCovector dr)) z₀
    exact hr'.prodMk
      ((surfaceQuarterTurnCovector dr).hasFDerivAt.sub_const
        (surfaceQuarterTurnCovector dr z₀))
  let Φ : OpenPartialHomeomorph ℂ (ℝ × ℝ) :=
    hF.toOpenPartialHomeomorph F hF' (by simp)
  refine ⟨Φ, hF.mem_toOpenPartialHomeomorph_source hF' (by simp), ?_, ?_, ?_⟩
  · change F z₀ = (r z₀, 0)
    simp [F]
  · intro z _hz
    rfl
  · simpa [Φ, ContDiffAt.localInverse, F] using
      hF.to_localInverse hF' (by simp)

/-- A regular real level on the complex plane admits a partial product
coordinate of any order that can be localized from the order known at the
base point.  Its first coordinate is the defining function. -/
theorem exists_regularLevelPartialDiffeomorph
    {n m : WithTop ℕ∞} {r : ℂ → ℝ} {z₀ : ℂ}
    (hr : ContDiffAt ℝ n r z₀)
    (hmn : m ≤ n) (hlocalize : m = ∞ → n = ω) (hn : n ≠ 0)
    {dr : ℂ →L[ℝ] ℝ} (hr' : HasFDerivAt r dr z₀)
    (hdr : dr ≠ 0) :
    ∃ Ψ : PartialDiffeomorph
        𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ × ℝ) ℂ (ℝ × ℝ) m,
      z₀ ∈ Ψ.source ∧
      Ψ z₀ = (r z₀, 0) ∧
      ∀ z ∈ Ψ.source, (Ψ z).1 = r z := by
  let A : ℂ ≃L[ℝ] ℝ × ℝ := surfaceRegularCovectorEquiv dr hdr
  let F : ℂ → ℝ × ℝ :=
    fun z =>
      (r z,
        surfaceQuarterTurnCovector dr z - surfaceQuarterTurnCovector dr z₀)
  have hF : ContDiffAt ℝ n F z₀ := by
    apply hr.prodMk
    exact (surfaceQuarterTurnCovector dr).contDiff.contDiffAt.sub contDiffAt_const
  have hF' : HasFDerivAt F (A : ℂ →L[ℝ] ℝ × ℝ) z₀ := by
    change HasFDerivAt F
      (dr.prod (surfaceQuarterTurnCovector dr)) z₀
    exact hr'.prodMk
      ((surfaceQuarterTurnCovector dr).hasFDerivAt.sub_const
        (surfaceQuarterTurnCovector dr z₀))
  let Φ : OpenPartialHomeomorph ℂ (ℝ × ℝ) :=
    hF.toOpenPartialHomeomorph F hF' hn
  have hzΦ : z₀ ∈ Φ.source :=
    hF.mem_toOpenPartialHomeomorph_source hF' hn
  have hΦz : Φ z₀ = (r z₀, 0) := by
    change F z₀ = (r z₀, 0)
    simp [F]
  have hinv : ContDiffAt ℝ n Φ.symm (r z₀, 0) := by
    simpa [Φ, ContDiffAt.localInverse, F] using
      hF.to_localInverse hF' hn
  rcases hF.contDiffOn' hmn hlocalize with
    ⟨U₀, hU₀_open, hzU₀, hFU₀⟩
  rcases hinv.contDiffOn' hmn hlocalize with
    ⟨V₀, hV₀_open, hΦzV₀, hinvV₀⟩
  let ΦV : OpenPartialHomeomorph ℂ (ℝ × ℝ) :=
    (Φ.symm.restrOpen V₀ hV₀_open).symm
  let ΦVU : OpenPartialHomeomorph ℂ (ℝ × ℝ) :=
    ΦV.restrOpen U₀ hU₀_open
  have hzΦV : z₀ ∈ ΦV.source := by
    have hy : (r z₀, 0) ∈ (Φ.symm.restrOpen V₀ hV₀_open).source := by
      rw [OpenPartialHomeomorph.restrOpen_source]
      exact ⟨by simpa [hΦz] using Φ.map_source hzΦ, hΦzV₀⟩
    have hmap := (Φ.symm.restrOpen V₀ hV₀_open).map_source hy
    have hval :
        (Φ.symm.restrOpen V₀ hV₀_open) (r z₀, 0) = z₀ := by
      change Φ.symm (r z₀, 0) = z₀
      rw [← hΦz]
      exact Φ.left_inv hzΦ
    change z₀ ∈ (Φ.symm.restrOpen V₀ hV₀_open).target
    rw [← hval]
    exact hmap
  have hzΦVU : z₀ ∈ ΦVU.source := by
    rw [OpenPartialHomeomorph.restrOpen_source]
    exact ⟨hzΦV, hzU₀⟩
  let Ψ : PartialDiffeomorph
      𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ × ℝ) ℂ (ℝ × ℝ) m :=
    { toPartialEquiv := ΦVU.toPartialEquiv
      open_source := ΦVU.open_source
      open_target := ΦVU.open_target
      contMDiffOn_toFun := by
        apply ContDiffOn.contMDiffOn
        intro z hz
        have hz' : z ∈ ΦV.source ∧ z ∈ U₀ := by
          simpa [ΦVU] using hz
        have hlocal := hFU₀ z ⟨by simp, hz'.2⟩
        have hmono := hlocal.mono (by
          intro w hw
          have hw' : w ∈ ΦV.source ∧ w ∈ U₀ := by
            simpa [ΦVU] using hw
          exact ⟨by simp, hw'.2⟩)
        simpa [ΦVU, ΦV, Φ, F] using hmono
      contMDiffOn_invFun := by
        apply ContDiffOn.contMDiffOn
        intro y hy
        have hy' : y ∈ ΦV.target := by
          change y ∈ (ΦV.toPartialEquiv.restr U₀).target at hy
          rw [PartialEquiv.restr_target] at hy
          exact hy.1
        have hyV : y ∈ V₀ := by
          change y ∈ (Φ.symm.restrOpen V₀ hV₀_open).source at hy'
          rw [OpenPartialHomeomorph.restrOpen_source] at hy'
          exact hy'.2
        have hlocal := hinvV₀ y ⟨by simp, hyV⟩
        have hmono := hlocal.mono (by
          intro w hw
          have hw' : w ∈ ΦV.target := by
            change w ∈ (ΦV.toPartialEquiv.restr U₀).target at hw
            rw [PartialEquiv.restr_target] at hw
            exact hw.1
          have hwV : w ∈ V₀ := by
            change w ∈ (Φ.symm.restrOpen V₀ hV₀_open).source at hw'
            rw [OpenPartialHomeomorph.restrOpen_source] at hw'
            exact hw'.2
          exact ⟨by simp, hwV⟩)
        simpa [ΦVU, ΦV] using hmono }
  refine ⟨Ψ, ?_, ?_, ?_⟩
  · exact hzΦVU
  · change ΦVU z₀ = (r z₀, 0)
    simpa [ΦVU, ΦV] using hΦz
  · intro z hz
    change (ΦVU z).1 = r z
    change (Φ z).1 = r z
    rfl

/-- A regular level function that is smooth on one fixed neighborhood has a
genuinely smooth partial product coordinate.  The uniform neighborhood
hypothesis is what permits the inverse chart to be smooth to every finite
order on one target neighborhood. -/
theorem exists_smoothRegularLevelPartialDiffeomorph_of_contDiffOnNhd
    {r : ℂ → ℝ} {z₀ : ℂ}
    (hr : ∃ V : Set ℂ, V ∈ 𝓝 z₀ ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r V)
    {dr : ℂ →L[ℝ] ℝ} (hr' : HasFDerivAt r dr z₀)
    (hdr : dr ≠ 0) :
    ∃ Ψ : PartialDiffeomorph
        𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ × ℝ) ℂ (ℝ × ℝ)
          ((⊤ : ℕ∞) : WithTop ℕ∞),
      z₀ ∈ Ψ.source ∧
      Ψ z₀ = (r z₀, 0) ∧
      ∀ z ∈ Ψ.source, (Ψ z).1 = r z := by
  rcases hr with ⟨V, hV_nhds, hrV⟩
  rcases mem_nhds_iff.mp hV_nhds with ⟨U, hUV, hU_open, hz₀U⟩
  have hrU : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r U :=
    hrV.mono hUV
  let A : ℂ ≃L[ℝ] ℝ × ℝ := surfaceRegularCovectorEquiv dr hdr
  let F : ℂ → ℝ × ℝ :=
    fun z =>
      (r z,
        surfaceQuarterTurnCovector dr z - surfaceQuarterTurnCovector dr z₀)
  have hFU : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F U := by
    apply hrU.prodMk
    exact ((surfaceQuarterTurnCovector dr).contDiff.sub contDiff_const).contDiffOn
  have hF_at : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F z₀ :=
    hFU.contDiffAt (hU_open.mem_nhds hz₀U)
  have hF' : HasFDerivAt F (A : ℂ →L[ℝ] ℝ × ℝ) z₀ := by
    change HasFDerivAt F
      (dr.prod (surfaceQuarterTurnCovector dr)) z₀
    exact hr'.prodMk
      ((surfaceQuarterTurnCovector dr).hasFDerivAt.sub_const
        (surfaceQuarterTurnCovector dr z₀))
  let Φ : OpenPartialHomeomorph ℂ (ℝ × ℝ) :=
    hF_at.toOpenPartialHomeomorph F hF' (by simp)
  have hz₀Φ : z₀ ∈ Φ.source :=
    hF_at.mem_toOpenPartialHomeomorph_source hF' (by simp)
  have hΦz₀ : Φ z₀ = (r z₀, 0) := by
    change F z₀ = (r z₀, 0)
    simp [F]
  have hderiv_invertible : (fderiv ℝ F z₀).IsInvertible := by
    refine ⟨A, ?_⟩
    exact hF'.fderiv.symm
  rcases exists_continuousLinearEquiv_fderiv_symm_eq
      (hF_at.of_le (by
        change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
        exact WithTop.coe_le_coe.2 le_top)) hderiv_invertible with
    ⟨N, _hN_smooth, _hNsymm_smooth, hN_eventually, _hN_deriv⟩
  rcases mem_nhds_iff.mp hN_eventually with
    ⟨Q, hQ_sub, hQ_open, hz₀Q⟩
  let S : Set ℂ := U ∩ Q
  have hS_open : IsOpen S := hU_open.inter hQ_open
  have hz₀S : z₀ ∈ S := ⟨hz₀U, hz₀Q⟩
  let ΦS : OpenPartialHomeomorph ℂ (ℝ × ℝ) :=
    Φ.restrOpen S hS_open
  have hz₀ΦS : z₀ ∈ ΦS.source := by
    rw [OpenPartialHomeomorph.restrOpen_source]
    exact ⟨hz₀Φ, hz₀S⟩
  let Ψ : PartialDiffeomorph
      𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ × ℝ) ℂ (ℝ × ℝ)
        ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    { toPartialEquiv := ΦS.toPartialEquiv
      open_source := ΦS.open_source
      open_target := ΦS.open_target
      contMDiffOn_toFun := by
        apply ContDiffOn.contMDiffOn
        intro z hz
        have hz' : z ∈ Φ.source ∧ z ∈ S := by
          simpa [ΦS] using hz
        have hlocal := hFU z hz'.2.1
        have hmono := hlocal.mono (by
          intro w hw
          have hw' : w ∈ Φ.source ∧ w ∈ S := by
            simpa [ΦS] using hw
          exact hw'.2.1)
        simpa [ΦS, Φ] using hmono
      contMDiffOn_invFun := by
        apply ContDiffOn.contMDiffOn
        intro y hy
        let x : ℂ := ΦS.symm y
        have hx_source : x ∈ ΦS.source := ΦS.symm.map_source hy
        have hx' : x ∈ Φ.source ∧ x ∈ S := by
          simpa [ΦS] using hx_source
        have hNx : N x = fderiv ℝ F x := hQ_sub hx'.2.2
        have hF_x : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F x :=
          hFU.contDiffAt (hU_open.mem_nhds hx'.2.1)
        have hFderiv_x : HasFDerivAt F (N x : ℂ →L[ℝ] ℝ × ℝ) x := by
          rw [hNx]
          exact (hF_x.differentiableAt (by simp)).hasFDerivAt
        have hΦS_x :
            HasFDerivAt ΦS (N x : ℂ →L[ℝ] ℝ × ℝ) x := by
          simpa [ΦS, Φ] using hFderiv_x
        have hΦS_smooth_x :
            ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ΦS x := by
          simpa [ΦS, Φ] using hF_x
        exact (ΦS.contDiffAt_symm hy hΦS_x hΦS_smooth_x).contDiffWithinAt }
  refine ⟨Ψ, hz₀ΦS, ?_, ?_⟩
  · change ΦS z₀ = (r z₀, 0)
    simpa [ΦS] using hΦz₀
  · intro z hz
    change (ΦS z).1 = r z
    change (F z).1 = r z
    rfl

end

end JJMath.Manifold
