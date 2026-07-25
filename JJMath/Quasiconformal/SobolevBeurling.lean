import JJMath.Quasiconformal.ChangeOfVariables
import JJMath.Quasiconformal.CauchyTransform
import JJMath.Quasiconformal.BeltramiLpSolver

/-!
# The Beurling identity for localized Sobolev maps

This file passes the test-function identity
`S (∂̄u) = ∂u` to compactly supported planar Sobolev maps.  Its main use is
the cutoff localization step in the higher-integrability proof for maps of
bounded distortion.
-/

namespace JJMath

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace Quasiconformal

noncomputable section

/--
%%handwave
name:
  Beltrami coefficient localized to a cutoff support
statement:
  For a cutoff $\chi:\mathbb C\to\mathbb R$ and a coefficient
  $\mu:\mathbb C\to\mathbb C$, define
  $$
    \mu_\chi(z)=
    \begin{cases}
      \mu(z),&z\in\operatorname{tsupp}\chi,\\
      0,&z\notin\operatorname{tsupp}\chi.
    \end{cases}
  $$
-/
def localizedBeltramiCoefficient
    (χ : ℂ → ℝ) (μ : ℂ → ℂ) : ℂ → ℂ :=
  (tsupport χ).indicator μ

/--
%%handwave
name:
  Measurability of a cutoff-localized Beltrami coefficient
statement:
  If $\mu:\mathbb C\to\mathbb C$ is strongly measurable almost everywhere
  and $\chi$ is a smooth compactly supported cutoff, then
  $\mu_\chi$ is strongly measurable almost everywhere.
proof:
  The topological support of $\chi$ is compact and hence measurable.
  Restricting a measurable function to a measurable set preserves
  measurability.
-/
theorem localizedBeltramiCoefficient_aestronglyMeasurable
    {Q Ω : Set ℂ}
    (χ : JJMath.Uniformization.ScalarWeakSobolevCutoff Q Ω)
    {μ : ℂ → ℂ}
    (hμ : AEStronglyMeasurable μ (volume : Measure ℂ)) :
    AEStronglyMeasurable
      (localizedBeltramiCoefficient (χ : ℂ → ℝ) μ)
      (volume : Measure ℂ) := by
  exact hμ.indicator χ.compact_support.measurableSet

/--
%%handwave
name:
  Essential bound for a cutoff-localized Beltrami coefficient
statement:
  If $|\mu(z)|\leq k$ almost everywhere, then
  $$
    |\mu_\chi(z)|\leq k
  $$
  almost everywhere.
proof:
  On the support of $\chi$ this is the assumed bound for $\mu$, while off
  that support the localized coefficient is zero.
-/
theorem localizedBeltramiCoefficient_ae_norm_le
    {Q Ω : Set ℂ}
    (χ : JJMath.Uniformization.ScalarWeakSobolevCutoff Q Ω)
    {μ : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k)
    (hμ : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ k) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      ‖localizedBeltramiCoefficient (χ : ℂ → ℝ) μ z‖ ≤ k := by
  filter_upwards [hμ] with z hz
  by_cases hzK : z ∈ tsupport (χ : ℂ → ℝ)
  · simpa [localizedBeltramiCoefficient, Set.indicator_of_mem hzK] using hz
  · simp [localizedBeltramiCoefficient, Set.indicator_of_notMem hzK, hk]

/--
%%handwave
name:
  Compact support of a cutoff-localized Beltrami coefficient
statement:
  A Beltrami coefficient localized to the support of a compactly supported
  cutoff vanishes outside some closed disk: there is $R\in\mathbb R$ such
  that
  $$
    R\leq|z|\quad\Longrightarrow\quad\mu_\chi(z)=0.
  $$
proof:
  The compact support of $\chi$ is bounded, so it is contained in a closed
  disk. Outside a slightly larger disk the indicator defining
  $\mu_\chi$ vanishes.
-/
theorem exists_closedBall_support_localizedBeltramiCoefficient
    {Q Ω : Set ℂ}
    (χ : JJMath.Uniformization.ScalarWeakSobolevCutoff Q Ω)
    (μ : ℂ → ℂ) :
    ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ →
      localizedBeltramiCoefficient (χ : ℂ → ℝ) μ z = 0 := by
  rcases χ.compact_support.exists_bound_of_continuousOn
      continuous_id.continuousOn with ⟨R, hR⟩
  refine ⟨R + 1, ?_⟩
  intro z hz
  rw [localizedBeltramiCoefficient, Set.indicator_of_notMem]
  intro hzK
  have hzR : ‖z‖ ≤ R := hR z hzK
  linarith

/--
%%handwave
name:
  Measurability of the cutoff error in the Beltrami equation
statement:
  Let $\chi:\mathbb C\to\mathbb R$ be smooth, let
  $f:\mathbb C\to\mathbb C$ be continuous, and let
  $\mu:\mathbb C\to\mathbb C$ be strongly measurable almost everywhere.
  Then
  $$
    G_{\chi,f,\mu}
      =\partial_{\bar z}(D\chi\otimes f)
        -\mu\,\partial_z(D\chi\otimes f)
  $$
  is strongly measurable almost everywhere.
proof:
  The rank-one field $D\chi\otimes f$ is continuous, as are both Wirtinger
  projections. The product with the measurable coefficient $\mu$ and the
  difference of the two terms are therefore measurable.
-/
theorem complexWeakSobolevCutoffBeltramiError_aestronglyMeasurable
    {Q Ω : Set ℂ}
    (χ : JJMath.Uniformization.ScalarWeakSobolevCutoff Q Ω)
    {f μ : ℂ → ℂ} (hf : Continuous f)
    (hμ : AEStronglyMeasurable μ (volume : Measure ℂ)) :
    AEStronglyMeasurable
      (complexWeakSobolevCutoffBeltramiError
        (χ : ℂ → ℝ) f μ)
      (volume : Measure ℂ) := by
  have hdχ : Continuous
      (fun z : ℂ ↦ fderiv ℝ (χ : ℂ → ℝ) z) :=
    χ.smooth.continuous_fderiv (by simp)
  have hrank : Continuous
      (fun z : ℂ ↦
        (fderiv ℝ (χ : ℂ → ℝ) z).smulRight (f z)) :=
    (ContinuousLinearMap.smulRightL ℝ ℂ ℂ).continuous₂.comp₂ hdχ hf
  have hA : Continuous
      (complexWeakSobolevCutoffDZError (χ : ℂ → ℝ) f) := by
    simpa only [complexWeakSobolevCutoffDZError] using
      continuous_weakDZ.comp hrank
  have hB : Continuous
      (complexWeakSobolevCutoffDBarError (χ : ℂ → ℝ) f) := by
    simpa only [complexWeakSobolevCutoffDBarError] using
      continuous_weakDBar.comp hrank
  exact hB.aestronglyMeasurable.sub
    (hμ.mul hA.aestronglyMeasurable)

/--
%%handwave
name:
  Bounded compact support of the cutoff error
statement:
  Let $\chi$ be smooth and compactly supported, let $f$ be continuous, and
  suppose $|\mu|\leq k$ almost everywhere for some $k\geq0$. Then there are
  constants $C,R\in\mathbb R$ such that
  $$
    |G_{\chi,f,\mu}(z)|\leq C
    \quad\text{for almost every }z,
    \qquad
    R\leq|z|\Longrightarrow G_{\chi,f,\mu}(z)=0.
  $$
proof:
  On the compact support of $\chi$, both $f$ and $D\chi$ are bounded.
  Each Wirtinger projection of $D\chi\otimes f$ has norm at most
  $\|D\chi\|\,|f|$, giving a bound by
  $(1+k)\|D\chi\|\,|f|$. Off the support of $\chi$, its differential
  vanishes, so both cutoff-error terms are zero.
-/
theorem exists_bound_and_closedBall_support_complexWeakSobolevCutoffBeltramiError
    {Q Ω : Set ℂ}
    (χ : JJMath.Uniformization.ScalarWeakSobolevCutoff Q Ω)
    {f μ : ℂ → ℂ} (hf : Continuous f)
    {k : ℝ} (hk : 0 ≤ k)
    (hμ : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ k) :
    ∃ C R : ℝ,
      (∀ᵐ z ∂(volume : Measure ℂ),
        ‖complexWeakSobolevCutoffBeltramiError
          (χ : ℂ → ℝ) f μ z‖ ≤ C) ∧
      (∀ z : ℂ, R ≤ ‖z‖ →
        complexWeakSobolevCutoffBeltramiError
          (χ : ℂ → ℝ) f μ z = 0) := by
  let K : Set ℂ := tsupport (χ : ℂ → ℝ)
  have hK : IsCompact K := χ.compact_support
  have hdχ : Continuous
      (fun z : ℂ ↦ fderiv ℝ (χ : ℂ → ℝ) z) :=
    χ.smooth.continuous_fderiv (by simp)
  rcases hK.exists_bound_of_continuousOn hdχ.continuousOn with
    ⟨Cχ₀, hCχ₀⟩
  rcases hK.exists_bound_of_continuousOn hf.continuousOn with
    ⟨Cf₀, hCf₀⟩
  rcases hK.exists_bound_of_continuousOn continuous_id.continuousOn with
    ⟨R, hR⟩
  let Cχ : ℝ := max 0 Cχ₀
  let Cf : ℝ := max 0 Cf₀
  refine ⟨(1 + k) * (Cχ * Cf), R + 1, ?_, ?_⟩
  · filter_upwards [hμ] with z hμz
    by_cases hzK : z ∈ K
    · have hCχ : ‖fderiv ℝ (χ : ℂ → ℝ) z‖ ≤ Cχ :=
        (hCχ₀ z hzK).trans (le_max_right 0 Cχ₀)
      have hCf : ‖f z‖ ≤ Cf :=
        (hCf₀ z hzK).trans (le_max_right 0 Cf₀)
      have hCχ_nonneg : 0 ≤ Cχ := le_max_left 0 Cχ₀
      have hCf_nonneg : 0 ≤ Cf := le_max_left 0 Cf₀
      let L : ℂ →L[ℝ] ℂ :=
        (fderiv ℝ (χ : ℂ → ℝ) z).smulRight (f z)
      have hL : ‖L‖ ≤ Cχ * Cf := by
        change
          ‖(fderiv ℝ (χ : ℂ → ℝ) z).smulRight (f z)‖ ≤ Cχ * Cf
        rw [ContinuousLinearMap.norm_smulRight_apply]
        exact mul_le_mul hCχ hCf (norm_nonneg _) hCχ_nonneg
      have hA : ‖weakDZ L‖ ≤ ‖L‖ := by
        rw [norm_eq_norm_weakDZ_add_norm_weakDBar]
        exact le_add_of_nonneg_right (norm_nonneg _)
      have hB : ‖weakDBar L‖ ≤ ‖L‖ := by
        rw [norm_eq_norm_weakDZ_add_norm_weakDBar]
        exact le_add_of_nonneg_left (norm_nonneg _)
      calc
        ‖complexWeakSobolevCutoffBeltramiError
            (χ : ℂ → ℝ) f μ z‖
            = ‖weakDBar L - μ z * weakDZ L‖ := by
                rfl
        _ ≤ ‖weakDBar L‖ + ‖μ z * weakDZ L‖ := norm_sub_le _ _
        _ = ‖weakDBar L‖ + ‖μ z‖ * ‖weakDZ L‖ := by rw [norm_mul]
        _ ≤ ‖L‖ + k * ‖L‖ := by
          exact add_le_add hB
            (mul_le_mul hμz hA (norm_nonneg _) hk)
        _ ≤ Cχ * Cf + k * (Cχ * Cf) := by
          exact add_le_add hL (mul_le_mul_of_nonneg_left hL hk)
        _ = (1 + k) * (Cχ * Cf) := by ring
    · have hdχz : fderiv ℝ (χ : ℂ → ℝ) z = 0 :=
        fderiv_of_notMem_tsupport
          (𝕜 := ℝ) (f := (χ : ℂ → ℝ)) hzK
      have herrzero :
          complexWeakSobolevCutoffBeltramiError
            (χ : ℂ → ℝ) f μ z = 0 := by
        simp [complexWeakSobolevCutoffBeltramiError,
          complexWeakSobolevCutoffDZError,
          complexWeakSobolevCutoffDBarError, weakDZ, weakDBar, hdχz]
      rw [herrzero, norm_zero]
      exact mul_nonneg (add_nonneg zero_le_one hk)
        (mul_nonneg (le_max_left 0 Cχ₀) (le_max_left 0 Cf₀))
  · intro z hz
    have hzK : z ∉ K := by
      intro hzK
      have hzR : ‖z‖ ≤ R := hR z hzK
      linarith
    have hdχz : fderiv ℝ (χ : ℂ → ℝ) z = 0 :=
      fderiv_of_notMem_tsupport
        (𝕜 := ℝ) (f := (χ : ℂ → ℝ)) hzK
    simp [complexWeakSobolevCutoffBeltramiError,
      complexWeakSobolevCutoffDZError,
      complexWeakSobolevCutoffDBarError, weakDZ, weakDBar, hdχz]

/--
%%handwave
name:
  Integrability of the cutoff error at every exponent
statement:
  Let $\chi$ be smooth and compactly supported, let $f$ be continuous, and
  let $\mu$ be measurable with $|\mu|\leq k$ almost everywhere for some
  $k\geq0$. Then
  $$
    G_{\chi,f,\mu}\in L^p(\mathbb C)
  $$
  for every extended exponent $p$.
proof:
  The cutoff error is measurable, essentially bounded, and supported in a
  disk. A bounded measurable function on a set of finite area belongs to
  every $L^p$ space.
-/
theorem complexWeakSobolevCutoffBeltramiError_memLp
    {Q Ω : Set ℂ}
    (χ : JJMath.Uniformization.ScalarWeakSobolevCutoff Q Ω)
    {f μ : ℂ → ℂ} (hf : Continuous f)
    (hμmeas : AEStronglyMeasurable μ (volume : Measure ℂ))
    {k : ℝ} (hk : 0 ≤ k)
    (hμ : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ k)
    (p : ENNReal) :
    MemLp
      (complexWeakSobolevCutoffBeltramiError
        (χ : ℂ → ℝ) f μ)
      p (volume : Measure ℂ) := by
  obtain ⟨C, R, hbound, hzero⟩ :=
    exists_bound_and_closedBall_support_complexWeakSobolevCutoffBeltramiError
      χ hf hk hμ
  exact memLp_of_ae_bound_of_ae_zero_outside_closedBall
    (complexWeakSobolevCutoffBeltramiError
      (χ : ℂ → ℝ) f μ)
    (complexWeakSobolevCutoffBeltramiError_aestronglyMeasurable
      χ hf hμmeas)
    hbound (ae_of_all _ hzero) p

/--
%%handwave
name:
  Whole-plane localized Beltrami equation
statement:
  Suppose
  $\partial_{\bar z}f=\mu\,\partial_zf$ almost everywhere on a measurable
  set $\Omega$, and let $\chi$ be a smooth cutoff supported in $\Omega$.
  Then, almost everywhere on $\mathbb C$,
  $$
    \partial_{\bar z}(\chi f)
      =\mu_\chi\,\partial_z(\chi f)+G_{\chi,f,\mu}.
  $$
proof:
  On the support of $\chi$, the localized coefficient equals $\mu$ and the
  formula is the product-rule form of the original Beltrami equation. Off
  that support, $\chi$ and $D\chi$ vanish, so every term in the formula is
  zero.
-/
theorem weakDBarField_complexWeakSobolevCutoffDerivative_eq_localized_ae
    {Q Ω : Set ℂ}
    (hΩ : MeasurableSet Ω)
    (χ : JJMath.Uniformization.ScalarWeakSobolevCutoff Q Ω)
    {f μ : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (heq : WeakBeltramiEquationOn Ω μ df) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      weakDBarField
          (complexWeakSobolevCutoffDerivative
            (χ : ℂ → ℝ) f df) z =
        localizedBeltramiCoefficient (χ : ℂ → ℝ) μ z *
            weakDZField
              (complexWeakSobolevCutoffDerivative
                (χ : ℂ → ℝ) f df) z +
          complexWeakSobolevCutoffBeltramiError
            (χ : ℂ → ℝ) f μ z := by
  have heq_global :
      ∀ᵐ z ∂(volume : Measure ℂ), z ∈ Ω →
        weakDBarField df z = μ z * weakDZField df z :=
    (ae_restrict_iff' hΩ).1 heq
  filter_upwards [heq_global] with z hz
  by_cases hzK : z ∈ tsupport (χ : ℂ → ℝ)
  · simpa [localizedBeltramiCoefficient,
      Set.indicator_of_mem hzK] using
        weakDBarField_complexWeakSobolevCutoffDerivative_eq
          (χ : ℂ → ℝ) f df μ z (hz (χ.support_subset hzK))
  · have hχz : χ z = 0 :=
      image_eq_zero_of_notMem_tsupport hzK
    have hdχz : fderiv ℝ (χ : ℂ → ℝ) z = 0 :=
      fderiv_of_notMem_tsupport
        (𝕜 := ℝ) (f := (χ : ℂ → ℝ)) hzK
    simp [localizedBeltramiCoefficient,
      Set.indicator_of_notMem hzK,
      complexWeakSobolevCutoffDerivative,
      complexWeakSobolevCutoffBeltramiError,
      complexWeakSobolevCutoffDZError,
      complexWeakSobolevCutoffDBarError,
      weakDZField, weakDBarField, weakDZ, weakDBar,
      hχz, hdχz]

/--
%%handwave
name:
  Smooth cutoff localization as a planar test function
statement:
  Let $\chi:\mathbb C\to\mathbb R$ be smooth and compactly supported, and
  let $g:\mathbb C\to\mathbb C$ be smooth. Then
  $$
    z\longmapsto\chi(z)g(z)
  $$
  is a smooth compactly supported planar test function.
-/
def scalarCutoffPlaneTestFunction
    {Q Ω : Set ℂ}
    (χ : JJMath.Uniformization.ScalarWeakSobolevCutoff Q Ω)
    (g : ℂ → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    PlaneTestFunction where
  toFun z := χ z • g z
  contDiff' := χ.smooth.smul hg
  hasCompactSupport' :=
    (show HasCompactSupport (χ : ℂ → ℝ) from χ.compact_support).smul_right
  tsupport_subset' := Set.subset_univ _

/--
%%handwave
name:
  Differential of a smoothly cutoff planar test function
statement:
  If $g:\mathbb C\to\mathbb C$ is smooth, then
  $$
    D(\chi g)(z)=\chi(z)Dg(z)+D\chi(z)\otimes g(z).
  $$
proof:
  Apply the classical product rule to the scalar multiplication map
  $(a,w)\mapsto aw$.
-/
theorem fderiv_scalarCutoffPlaneTestFunction
    {Q Ω : Set ℂ}
    (χ : JJMath.Uniformization.ScalarWeakSobolevCutoff Q Ω)
    (g : ℂ → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (z : ℂ) :
    fderiv ℝ (scalarCutoffPlaneTestFunction χ g hg : ℂ → ℂ) z =
      complexWeakSobolevCutoffDerivative
        (χ : ℂ → ℝ) g (fun w ↦ fderiv ℝ g w) z := by
  change fderiv ℝ ((χ : ℂ → ℝ) • g) z = _
  rw [fderiv_smul
    (χ.smooth.differentiable (by simp) z)
    (hg.differentiable (by simp) z)]
  rfl

set_option maxHeartbeats 3000000 in
/--
%%handwave
name:
  Strong convergence of cutoff-localized smooth differentials
statement:
  Let smooth maps $T_n:\mathbb C\to\mathbb C$ converge to $f$ in the
  $W^{1,2}$ graph norm on a compact set $Q$. Let $\chi$ be a smooth cutoff
  whose support is contained in $Q$. Then
  $$
    D(\chi T_n)\longrightarrow
      \chi Df+D\chi\otimes f
    \quad\text{in }L^2(\mathbb C).
  $$
proof:
  The difference is
  $$
    \chi(DT_n-Df)+D\chi\otimes(T_n-f).
  $$
  Both coefficients are bounded on $Q$, so the two graph-norm errors tend to
  zero in $L^2(Q)$. Every field in the difference is supported in $Q$, hence
  the restricted and whole-plane norms agree.
-/
theorem PlanarWeakSobolevSmoothApproxGraphL2Data.complexCutoffDifferential_tendsto_l2
    {Q P Ω : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (hgraph : PlanarWeakSobolevSmoothApproxGraphL2Data Q f df)
    (hQ : IsCompact Q)
    (χ : JJMath.Uniformization.ScalarWeakSobolevCutoff P Ω)
    (hχQ : tsupport (χ : ℂ → ℝ) ⊆ Q) :
    Tendsto
      (fun n ↦ eLpNorm
        (fun z : ℂ ↦
          complexWeakSobolevCutoffDerivative
              (χ : ℂ → ℝ) (hgraph.approximants n)
              (fun w ↦ fderiv ℝ (hgraph.approximants n) w) z -
            complexWeakSobolevCutoffDerivative
              (χ : ℂ → ℝ) f df z)
        2 volume)
      atTop (𝓝 0) := by
  let dχ : ℂ → ℂ →L[ℝ] ℝ :=
    fun z ↦ fderiv ℝ (χ : ℂ → ℝ) z
  let E₀ : ℕ → ℂ → ℂ :=
    fun n z ↦ hgraph.approximants n z - f z
  let E₁ : ℕ → ℂ → ℂ →L[ℝ] ℂ :=
    fun n z ↦ fderiv ℝ (hgraph.approximants n) z - df z
  let A : ℕ → ℂ → ℂ →L[ℝ] ℂ :=
    fun n z ↦ χ z • E₁ n z
  let B : ℕ → ℂ → ℂ →L[ℝ] ℂ :=
    fun n z ↦ (dχ z).smulRight (E₀ n z)
  let E : ℕ → ℂ → ℂ →L[ℝ] ℂ :=
    fun n z ↦
      complexWeakSobolevCutoffDerivative
          (χ : ℂ → ℝ) (hgraph.approximants n)
          (fun w ↦ fderiv ℝ (hgraph.approximants n) w) z -
        complexWeakSobolevCutoffDerivative (χ : ℂ → ℝ) f df z
  have hE : ∀ n, E n = A n + B n := by
    intro n
    funext z
    ext v
    simp only [E, A, B, E₀, E₁, dχ,
      complexWeakSobolevCutoffDerivative, Pi.add_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply]
    rw [smul_sub, smul_sub]
    abel
  have hE_support : ∀ n, Function.support (E n) ⊆ Q := by
    intro n z hz
    by_contra hzQ
    have hzχ : z ∉ tsupport (χ : ℂ → ℝ) := fun hzχ ↦ hzQ (hχQ hzχ)
    have hχ_zero : χ z = 0 := image_eq_zero_of_notMem_tsupport hzχ
    have hdχ_zero : dχ z = 0 := by
      exact fderiv_of_notMem_tsupport
        (𝕜 := ℝ) (f := (χ : ℂ → ℝ)) hzχ
    exact hz (by simp [E, complexWeakSobolevCutoffDerivative,
      dχ, hχ_zero, hdχ_zero])
  have hχ_cont : Continuous (χ : ℂ → ℝ) := χ.smooth.continuous
  rcases hQ.exists_bound_of_continuousOn hχ_cont.continuousOn with
    ⟨Cχ, hCχ⟩
  have hdχ_cont : Continuous dχ := by
    exact χ.smooth.continuous_fderiv (by simp)
  rcases hQ.exists_bound_of_continuousOn hdχ_cont.continuousOn with
    ⟨Cdχ, hCdχ⟩
  have hA_mem : ∀ n, MemLp (A n) 2 (volume.restrict Q) := by
    intro n
    have hχ_aesm :
        AEStronglyMeasurable (χ : ℂ → ℝ) (volume.restrict Q) :=
      hχ_cont.aestronglyMeasurable
    apply MemLp.of_le_mul (hgraph.derivative_error_memLp n)
      (hχ_aesm.smul (hgraph.derivative_error_memLp n).aestronglyMeasurable)
    exact ae_restrict_of_forall_mem hQ.measurableSet fun z hz ↦ by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (hCχ z hz) (norm_nonneg _)
  have hB_mem : ∀ n, MemLp (B n) 2 (volume.restrict Q) := by
    intro n
    have hdχ_aesm :
        AEStronglyMeasurable dχ (volume.restrict Q) :=
      hdχ_cont.aestronglyMeasurable
    have hB_aesm : AEStronglyMeasurable (B n) (volume.restrict Q) :=
      (ContinuousLinearMap.smulRightL ℝ ℂ ℂ).continuous₂
        |>.comp_aestronglyMeasurable₂ hdχ_aesm
          (hgraph.value_error_memLp n).aestronglyMeasurable
    apply MemLp.of_le_mul (hgraph.value_error_memLp n) hB_aesm
    exact ae_restrict_of_forall_mem hQ.measurableSet fun z hz ↦ by
      rw [ContinuousLinearMap.norm_smulRight_apply]
      exact mul_le_mul_of_nonneg_right (hCdχ z hz) (norm_nonneg _)
  have hA_bound : ∀ n,
      eLpNorm (A n) 2 (volume.restrict Q) ≤
        ENNReal.ofReal Cχ *
          eLpNorm (E₁ n) 2 (volume.restrict Q) := by
    intro n
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    exact ae_restrict_of_forall_mem hQ.measurableSet fun z hz ↦ by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (hCχ z hz) (norm_nonneg _)
  have hB_bound : ∀ n,
      eLpNorm (B n) 2 (volume.restrict Q) ≤
        ENNReal.ofReal Cdχ *
          eLpNorm (E₀ n) 2 (volume.restrict Q) := by
    intro n
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    exact ae_restrict_of_forall_mem hQ.measurableSet fun z hz ↦ by
      rw [ContinuousLinearMap.norm_smulRight_apply]
      exact mul_le_mul_of_nonneg_right (hCdχ z hz) (norm_nonneg _)
  have hupper : Tendsto
      (fun n ↦
        ENNReal.ofReal Cχ *
            eLpNorm (E₁ n) 2 (volume.restrict Q) +
          ENNReal.ofReal Cdχ *
            eLpNorm (E₀ n) 2 (volume.restrict Q))
      atTop (𝓝 0) := by
    have h₁ : Tendsto
        (fun n ↦ ENNReal.ofReal Cχ *
          eLpNorm (E₁ n) 2 (volume.restrict Q))
        atTop (𝓝 0) := by
      simpa [E₁] using
        ENNReal.Tendsto.const_mul hgraph.derivative_tendsto_l2
          (Or.inr ENNReal.ofReal_ne_top)
    have h₀ : Tendsto
        (fun n ↦ ENNReal.ofReal Cdχ *
          eLpNorm (E₀ n) 2 (volume.restrict Q))
        atTop (𝓝 0) := by
      simpa [E₀] using
        ENNReal.Tendsto.const_mul hgraph.value_tendsto_l2
          (Or.inr ENNReal.ofReal_ne_top)
    simpa using h₁.add h₀
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hupper
  · intro n
    exact zero_le
  · intro n
    change
      eLpNorm (E n) 2 volume ≤
        ENNReal.ofReal Cχ * eLpNorm (E₁ n) 2 (volume.restrict Q) +
          ENNReal.ofReal Cdχ * eLpNorm (E₀ n) 2 (volume.restrict Q)
    have hrestrict :
        eLpNorm (E n) 2 volume =
          eLpNorm (E n) 2 (volume.restrict Q) :=
      (eLpNorm_restrict_eq_of_support_subset
        (p := (2 : ENNReal)) (μ := volume) (s := Q) (f := E n)
        (hE_support n)).symm
    rw [hrestrict, hE n]
    exact
      (eLpNorm_add_le
        (hA_mem n).aestronglyMeasurable
        (hB_mem n).aestronglyMeasurable
        (by norm_num : (1 : ENNReal) ≤ 2)).trans
        (add_le_add (hA_bound n) (hB_bound n))

/--
%%handwave
name:
  Strong convergence of cutoff-localized Wirtinger derivatives
statement:
  Under strong $W^{1,2}$ graph convergence $T_n\to f$ on a compact set
  containing the support of a smooth cutoff $\chi$, both localized
  Wirtinger derivatives converge strongly:
  $$
    \partial_z(\chi T_n)\to\partial_z(\chi f),\qquad
    \partial_{\bar z}(\chi T_n)\to\partial_{\bar z}(\chi f)
    \quad\text{in }L^2(\mathbb C).
  $$
proof:
  Each Wirtinger projection has norm at most the operator norm of the full
  real differential. Apply this pointwise estimate to the strong convergence
  of the localized differential fields.
-/
theorem PlanarWeakSobolevSmoothApproxGraphL2Data.complexCutoffWirtinger_tendsto_l2
    {Q P Ω : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (hgraph : PlanarWeakSobolevSmoothApproxGraphL2Data Q f df)
    (hQ : IsCompact Q)
    (χ : JJMath.Uniformization.ScalarWeakSobolevCutoff P Ω)
    (hχQ : tsupport (χ : ℂ → ℝ) ⊆ Q) :
    Tendsto
      (fun n ↦ eLpNorm
        (weakDZField
            (complexWeakSobolevCutoffDerivative
              (χ : ℂ → ℝ) (hgraph.approximants n)
              (fun w ↦ fderiv ℝ (hgraph.approximants n) w)) -
          weakDZField
            (complexWeakSobolevCutoffDerivative
              (χ : ℂ → ℝ) f df))
        2 volume)
      atTop (𝓝 0) ∧
    Tendsto
      (fun n ↦ eLpNorm
        (weakDBarField
            (complexWeakSobolevCutoffDerivative
              (χ : ℂ → ℝ) (hgraph.approximants n)
              (fun w ↦ fderiv ℝ (hgraph.approximants n) w)) -
          weakDBarField
            (complexWeakSobolevCutoffDerivative
              (χ : ℂ → ℝ) f df))
        2 volume)
      atTop (𝓝 0) := by
  let D : ℕ → ℂ → ℂ →L[ℝ] ℂ :=
    fun n ↦
      complexWeakSobolevCutoffDerivative
        (χ : ℂ → ℝ) (hgraph.approximants n)
        (fun w ↦ fderiv ℝ (hgraph.approximants n) w)
  let D₀ : ℂ → ℂ →L[ℝ] ℂ :=
    complexWeakSobolevCutoffDerivative (χ : ℂ → ℝ) f df
  have hfull := hgraph.complexCutoffDifferential_tendsto_l2 hQ χ hχQ
  change Tendsto
    (fun n ↦ eLpNorm (fun z ↦ D n z - D₀ z) 2 volume)
    atTop (𝓝 0) at hfull
  have hz_le : ∀ n,
      eLpNorm (weakDZField (D n) - weakDZField D₀) 2 volume ≤
        eLpNorm (fun z ↦ D n z - D₀ z) 2 volume := by
    intro n
    apply eLpNorm_mono_ae
    filter_upwards with z
    have heq :
        weakDZField (D n) z - weakDZField D₀ z =
          weakDZ (D n z - D₀ z) := by
      simp [weakDZField, weakDZ]
      ring
    rw [Pi.sub_apply, heq]
    rw [norm_eq_norm_weakDZ_add_norm_weakDBar]
    exact le_add_of_nonneg_right (norm_nonneg _)
  have hbar_le : ∀ n,
      eLpNorm (weakDBarField (D n) - weakDBarField D₀) 2 volume ≤
        eLpNorm (fun z ↦ D n z - D₀ z) 2 volume := by
    intro n
    apply eLpNorm_mono_ae
    filter_upwards with z
    have heq :
        weakDBarField (D n) z - weakDBarField D₀ z =
          weakDBar (D n z - D₀ z) := by
      simp [weakDBarField, weakDBar]
      ring
    rw [Pi.sub_apply, heq]
    rw [norm_eq_norm_weakDZ_add_norm_weakDBar]
    exact le_add_of_nonneg_left (norm_nonneg _)
  constructor
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hfull (fun _ ↦ zero_le) hz_le
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hfull (fun _ ↦ zero_le) hbar_le

/--
%%handwave
name:
  Whole-plane $L^2$ class of the localized holomorphic derivative
statement:
  Let $f\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb C)$ and let $\chi$ be a
  smooth compactly supported cutoff in $\Omega$. The holomorphic Wirtinger
  derivative of $\chi f$ determines an element
  $[\partial_z(\chi f)]\in L^2(\mathbb C)$.
-/
def complexWeakSobolevCutoffDZPlaneL2
    {Q Ω : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (hW : IsLocalW12On Ω f df)
    (χ : JJMath.Uniformization.ScalarWeakSobolevCutoff Q Ω) :
    PlaneL2 :=
  let hD :=
    MemLp.weakDZField (hW.complexWeakSobolevCutoff_memLp χ).2
  hD.toLp
    (weakDZField
      (complexWeakSobolevCutoffDerivative (χ : ℂ → ℝ) f df))

/--
%%handwave
name:
  Whole-plane $L^2$ class of the localized antiholomorphic derivative
statement:
  Let $f\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb C)$ and let $\chi$ be a
  smooth compactly supported cutoff in $\Omega$. The antiholomorphic
  Wirtinger derivative of $\chi f$ determines an element
  $[\partial_{\bar z}(\chi f)]\in L^2(\mathbb C)$.
-/
def complexWeakSobolevCutoffDBarPlaneL2
    {Q Ω : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (hW : IsLocalW12On Ω f df)
    (χ : JJMath.Uniformization.ScalarWeakSobolevCutoff Q Ω) :
    PlaneL2 :=
  let hD :=
    MemLp.weakDBarField (hW.complexWeakSobolevCutoff_memLp χ).2
  hD.toLp
    (weakDBarField
      (complexWeakSobolevCutoffDerivative (χ : ℂ → ℝ) f df))

set_option maxHeartbeats 3000000 in
/--
%%handwave
name:
  Beurling identity for a cutoff-localized Sobolev map
statement:
  Let $f\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb C)$ and let $\chi$ be a
  smooth compactly supported cutoff in $\Omega$. Then
  $$
    \mathcal S\bigl(\partial_{\bar z}(\chi f)\bigr)
      =\partial_z(\chi f)
    \quad\text{in }L^2(\mathbb C).
  $$
proof:
  Approximate $f$ and $Df$ in the local $W^{1,2}$ graph norm on the compact
  support of $\chi$. Multiplication by $\chi$ turns the smooth approximants
  into planar test functions, and both localized Wirtinger derivatives
  converge strongly in $L^2(\mathbb C)$. Apply the test-function
  Cauchy--Beurling identity and pass to the limit through the bounded
  $L^2$ Beurling operator.
-/
theorem beurlingTransformL2_complexWeakSobolevCutoffDBarPlaneL2
    {Q Ω : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (hW : IsLocalW12On Ω f df)
    (χ : JJMath.Uniformization.ScalarWeakSobolevCutoff Q Ω) :
    beurlingTransformL2
        (complexWeakSobolevCutoffDBarPlaneL2 hW χ) =
      complexWeakSobolevCutoffDZPlaneL2 hW χ := by
  let K : Set ℂ := tsupport (χ : ℂ → ℝ)
  have hK : IsCompact K := χ.compact_support
  have hKΩ : K ⊆ Ω := χ.support_subset
  obtain ⟨δ, hδ, hδΩ⟩ :=
    hK.exists_cthickening_subset_open hW.1 hKΩ
  let P : Set ℂ := Metric.cthickening δ K
  have hP : IsCompact P := hK.cthickening
  have hPΩ : P ⊆ Ω := by simpa [P] using hδΩ
  obtain ⟨hgraph⟩ :=
    hW.exists_smoothApproxGraphL2Data_on_compact
      (Q := K) (P := P) hK hP
      ⟨δ, hδ, by simp [P]⟩ hPΩ
  let φ : ℕ → PlaneTestFunction :=
    fun n ↦ scalarCutoffPlaneTestFunction
      χ (hgraph.approximants n) (hgraph.smooth n)
  let D : ℕ → ℂ → ℂ →L[ℝ] ℂ :=
    fun n ↦ complexWeakSobolevCutoffDerivative
      (χ : ℂ → ℝ) (hgraph.approximants n)
      (fun z ↦ fderiv ℝ (hgraph.approximants n) z)
  let D₀ : ℂ → ℂ →L[ℝ] ℂ :=
    complexWeakSobolevCutoffDerivative (χ : ℂ → ℝ) f df
  have hwirtinger :=
    hgraph.complexCutoffWirtinger_tendsto_l2 hK χ
      (by exact Set.Subset.rfl)
  change
    Tendsto
      (fun n ↦ eLpNorm
        (weakDZField (D n) - weakDZField D₀) 2 volume)
      atTop (𝓝 0) ∧
    Tendsto
      (fun n ↦ eLpNorm
        (weakDBarField (D n) - weakDBarField D₀) 2 volume)
      atTop (𝓝 0) at hwirtinger
  have hD₀ : MemLp D₀ 2 volume := by
    simpa [D₀] using (hW.complexWeakSobolevCutoff_memLp χ).2
  have hz₀ : MemLp (weakDZField D₀) 2 volume :=
    MemLp.weakDZField hD₀
  have hbar₀ : MemLp (weakDBarField D₀) 2 volume :=
    MemLp.weakDBarField hD₀
  let Z₀ : PlaneL2 := hz₀.toLp (weakDZField D₀)
  let B₀ : PlaneL2 := hbar₀.toLp (weakDBarField D₀)
  let Zn : ℕ → PlaneL2 :=
    fun n ↦ testFunctionPlaneL2 (planeTestFunctionZ (φ n))
  let Bn : ℕ → PlaneL2 :=
    fun n ↦ testFunctionPlaneL2 (planeTestFunctionDBar (φ n))
  have hφD : ∀ n z,
      fderiv ℝ (φ n : ℂ → ℂ) z = D n z := by
    intro n z
    exact fderiv_scalarCutoffPlaneTestFunction
      χ (hgraph.approximants n) (hgraph.smooth n) z
  have hZn_ae : ∀ n,
      (Zn n : ℂ → ℂ) =ᵐ[volume] weakDZField (D n) := by
    intro n
    filter_upwards [testFunctionPlaneL2_coeFn
      (planeTestFunctionZ (φ n))] with z hz
    rw [hz, planeTestFunctionZ_apply]
    change weakDZ (fderiv ℝ (φ n : ℂ → ℂ) z) =
      weakDZField (D n) z
    rw [hφD n z]
    rfl
  have hBn_ae : ∀ n,
      (Bn n : ℂ → ℂ) =ᵐ[volume] weakDBarField (D n) := by
    intro n
    filter_upwards [testFunctionPlaneL2_coeFn
      (planeTestFunctionDBar (φ n))] with z hz
    rw [hz, planeTestFunctionDBar_apply]
    change weakDBar (fderiv ℝ (φ n : ℂ → ℂ) z) =
      weakDBarField (D n) z
    rw [hφD n z]
    rfl
  have hZ₀_ae : (Z₀ : ℂ → ℂ) =ᵐ[volume] weakDZField D₀ := by
    exact hz₀.coeFn_toLp
  have hB₀_ae : (B₀ : ℂ → ℂ) =ᵐ[volume] weakDBarField D₀ := by
    exact hbar₀.coeFn_toLp
  have hZn_norm : Tendsto
      (fun n ↦ eLpNorm ((Zn n : ℂ → ℂ) - (Z₀ : ℂ → ℂ)) 2 volume)
      atTop (𝓝 0) := by
    have heq : ∀ n,
        eLpNorm ((Zn n : ℂ → ℂ) - (Z₀ : ℂ → ℂ)) 2 volume =
          eLpNorm (weakDZField (D n) - weakDZField D₀) 2 volume := by
      intro n
      apply eLpNorm_congr_ae
      filter_upwards [hZn_ae n, hZ₀_ae] with z hn h0
      simp only [Pi.sub_apply, hn, h0]
    simpa only [heq] using hwirtinger.1
  have hBn_norm : Tendsto
      (fun n ↦ eLpNorm ((Bn n : ℂ → ℂ) - (B₀ : ℂ → ℂ)) 2 volume)
      atTop (𝓝 0) := by
    have heq : ∀ n,
        eLpNorm ((Bn n : ℂ → ℂ) - (B₀ : ℂ → ℂ)) 2 volume =
          eLpNorm (weakDBarField (D n) - weakDBarField D₀) 2 volume := by
      intro n
      apply eLpNorm_congr_ae
      filter_upwards [hBn_ae n, hB₀_ae] with z hn h0
      simp only [Pi.sub_apply, hn, h0]
    simpa only [heq] using hwirtinger.2
  have hZn_tend : Tendsto Zn atTop (𝓝 Z₀) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm' Zn Z₀).2 hZn_norm
  have hBn_tend : Tendsto Bn atTop (𝓝 B₀) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm' Bn B₀).2 hBn_norm
  have hS_tend :
      Tendsto (fun n ↦ beurlingTransformL2 (Bn n))
        atTop (𝓝 (beurlingTransformL2 B₀)) :=
    beurlingTransformL2.continuous.continuousAt.tendsto.comp hBn_tend
  have hS_tend' : Tendsto Zn atTop (𝓝 (beurlingTransformL2 B₀)) := by
    convert hS_tend using 1
    funext n
    exact (beurlingTransformL2_testFunctionDBar (φ n)).symm
  have hlimit : beurlingTransformL2 B₀ = Z₀ :=
    tendsto_nhds_unique hS_tend' hZn_tend
  simpa [B₀, Z₀, D₀, complexWeakSobolevCutoffDBarPlaneL2,
    complexWeakSobolevCutoffDZPlaneL2] using hlimit

/--
%%handwave
name:
  The cutoff derivatives solve an $L^2$ Beltrami equation
statement:
  Let $f\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb C)$ be continuous and
  satisfy
  $\partial_{\bar z}f=\mu\,\partial_zf$ almost everywhere in $\Omega$.
  Suppose $\mu$ is measurable and $|\mu|\leq k$ almost everywhere, where
  $k\geq0$. For every smooth compactly supported cutoff $\chi$ in $\Omega$,
  $$
    [\partial_{\bar z}(\chi f)]
      -[\mu_\chi]\,
        \mathcal S_2[\partial_{\bar z}(\chi f)]
      =[G_{\chi,f,\mu}]
    \quad\text{in }L^2(\mathbb C).
  $$
proof:
  The whole-plane cutoff equation gives the equality of representatives
  almost everywhere. The Sobolev Beurling identity replaces
  $\partial_z(\chi f)$ by
  $\mathcal S_2\partial_{\bar z}(\chi f)$.
-/
theorem complexWeakSobolevCutoffDBarPlaneL2_beltramiEquation
    {Q Ω : Set ℂ} {f μ : ℂ → ℂ}
    {df : ℂ → ℂ →L[ℝ] ℂ}
    (hW : IsLocalW12On Ω f df) (hf : Continuous f)
    (χ : JJMath.Uniformization.ScalarWeakSobolevCutoff Q Ω)
    (hμmeas : AEStronglyMeasurable μ (volume : Measure ℂ))
    {k : ℝ} (hk : 0 ≤ k)
    (hμbound : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ k)
    (heq : WeakBeltramiEquationOn Ω μ df) :
    let ν :=
      localizedBeltramiCoefficient (χ : ℂ → ℝ) μ
    let hνTop : MemLp ν ∞ (volume : Measure ℂ) :=
      memLp_top_of_bound
        (localizedBeltramiCoefficient_aestronglyMeasurable χ hμmeas)
        k (localizedBeltramiCoefficient_ae_norm_le χ hk hμbound)
    let G :=
      complexWeakSobolevCutoffBeltramiError
        (χ : ℂ → ℝ) f μ
    let hG2 : MemLp G 2 (volume : Measure ℂ) :=
      complexWeakSobolevCutoffBeltramiError_memLp
        χ hf hμmeas hk hμbound 2
    complexWeakSobolevCutoffDBarPlaneL2 hW χ -
        hνTop.toLp ν •
          beurlingTransformL2
            (complexWeakSobolevCutoffDBarPlaneL2 hW χ) =
      hG2.toLp G := by
  dsimp only
  let D : ℂ → ℂ →L[ℝ] ℂ :=
    complexWeakSobolevCutoffDerivative (χ : ℂ → ℝ) f df
  let A : ℂ → ℂ := weakDZField D
  let B : ℂ → ℂ := weakDBarField D
  let ν : ℂ → ℂ :=
    localizedBeltramiCoefficient (χ : ℂ → ℝ) μ
  let G : ℂ → ℂ :=
    complexWeakSobolevCutoffBeltramiError
      (χ : ℂ → ℝ) f μ
  have hD2 : MemLp D 2 (volume : Measure ℂ) := by
    simpa [D] using (hW.complexWeakSobolevCutoff_memLp χ).2
  have hA2 : MemLp A 2 (volume : Measure ℂ) := by
    simpa [A] using MemLp.weakDZField hD2
  have hB2 : MemLp B 2 (volume : Measure ℂ) := by
    simpa [B] using MemLp.weakDBarField hD2
  have hνmeas : AEStronglyMeasurable ν (volume : Measure ℂ) := by
    simpa [ν] using
      localizedBeltramiCoefficient_aestronglyMeasurable χ hμmeas
  have hνbound : ∀ᵐ z ∂(volume : Measure ℂ), ‖ν z‖ ≤ k := by
    simpa [ν] using
      localizedBeltramiCoefficient_ae_norm_le χ hk hμbound
  let hνTop : MemLp ν ∞ (volume : Measure ℂ) :=
    memLp_top_of_bound hνmeas k hνbound
  have hG2 : MemLp G 2 (volume : Measure ℂ) := by
    simpa [G] using
      complexWeakSobolevCutoffBeltramiError_memLp
        χ hf hμmeas hk hμbound 2
  let A2 : PlaneL2 := hA2.toLp A
  let B2 : PlaneL2 := hB2.toLp B
  let νTop : Lp ℂ ∞ (volume : Measure ℂ) := hνTop.toLp ν
  let G2 : PlaneL2 := hG2.toLp G
  have hS : beurlingTransformL2 B2 = A2 := by
    simpa [A2, B2, A, B, D,
      complexWeakSobolevCutoffDBarPlaneL2,
      complexWeakSobolevCutoffDZPlaneL2] using
        beurlingTransformL2_complexWeakSobolevCutoffDBarPlaneL2 hW χ
  have hpoint :
      ∀ᵐ z ∂(volume : Measure ℂ), B z = ν z * A z + G z := by
    simpa [A, B, D, ν, G] using
      weakDBarField_complexWeakSobolevCutoffDerivative_eq_localized_ae
        hW.1.measurableSet χ heq
  have hclass : B2 = νTop • A2 + G2 := by
    apply Lp.ext
    filter_upwards [
      hB2.coeFn_toLp,
      hA2.coeFn_toLp,
      hνTop.coeFn_toLp,
      hG2.coeFn_toLp,
      Lp.coeFn_add (νTop • A2) G2,
      Lp.coeFn_lpSMul (r := (2 : ENNReal)) νTop A2,
      hpoint] with z hBz hAz hνz hGz hadd hmul hpointz
    calc
      (B2 : ℂ → ℂ) z = B z := hBz
      _ = ν z * A z + G z := hpointz
      _ = (νTop : ℂ → ℂ) z * (A2 : ℂ → ℂ) z +
          (G2 : ℂ → ℂ) z := by rw [hνz, hAz, hGz]
      _ = (νTop • A2 : PlaneL2) z + (G2 : ℂ → ℂ) z := by
        rw [hmul]
        rfl
      _ = (νTop • A2 + G2 : PlaneL2) z := hadd.symm
  change B2 - νTop • beurlingTransformL2 B2 = G2
  rw [hS]
  apply sub_eq_iff_eq_add.mpr
  calc
    B2 = νTop • A2 + G2 := hclass
    _ = G2 + νTop • A2 := add_comm _ _

set_option maxHeartbeats 3000000 in
/--
%%handwave
name:
  Higher integrability of a cutoff-localized Beltrami solution
statement:
  Let $f\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb C)$ be continuous and
  satisfy
  $\partial_{\bar z}f=\mu\,\partial_zf$ almost everywhere in $\Omega$.
  Suppose $\mu$ is measurable and $|\mu|\leq k<1$ almost everywhere.
  For every smooth compactly supported cutoff $\chi$ in $\Omega$, there is
  an exponent $r$ with $2<r<3$ such that
  $$
    D(\chi f)\in L^r(\mathbb C).
  $$
proof:
  The cutoff derivatives satisfy
  $h-\mu_\chi\mathcal S_2h=G_{\chi,f,\mu}$ in $L^2$. The coefficient
  $\mu_\chi$ and the right-hand side are bounded and compactly supported.
  Choose the near-$2$ exponent for which
  $I-M_{\mu_\chi}\mathcal S_r$ is invertible. Its $L^r$ solution is also in
  $L^2$ and hence, by uniqueness, equals
  $\partial_{\bar z}(\chi f)$. Compatibility of the $L^r$ and $L^2$
  Beurling transforms then gives the same integrability for
  $\partial_z(\chi f)$. The identity
  $\|D(\chi f)\|=|\partial_z(\chi f)|
    +|\partial_{\bar z}(\chi f)|$
  finishes the proof.
-/
theorem IsLocalW12On.exists_memLp_complexWeakSobolevCutoffDerivative
    {Q Ω : Set ℂ} {f μ : ℂ → ℂ}
    {df : ℂ → ℂ →L[ℝ] ℂ}
    (hW : IsLocalW12On Ω f df) (hf : Continuous f)
    (χ : JJMath.Uniformization.ScalarWeakSobolevCutoff Q Ω)
    (hμmeas : AEStronglyMeasurable μ (volume : Measure ℂ))
    {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1)
    (hμbound : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ k)
    (heq : WeakBeltramiEquationOn Ω μ df) :
    ∃ r : ℝ, 2 < r ∧ r < 3 ∧
      MemLp
        (complexWeakSobolevCutoffDerivative
          (χ : ℂ → ℝ) f df)
        (ENNReal.ofReal r) (volume : Measure ℂ) := by
  let D : ℂ → ℂ →L[ℝ] ℂ :=
    complexWeakSobolevCutoffDerivative (χ : ℂ → ℝ) f df
  let A : ℂ → ℂ := weakDZField D
  let B : ℂ → ℂ := weakDBarField D
  let ν : ℂ → ℂ :=
    localizedBeltramiCoefficient (χ : ℂ → ℝ) μ
  let G : ℂ → ℂ :=
    complexWeakSobolevCutoffBeltramiError
      (χ : ℂ → ℝ) f μ
  have hD2 : MemLp D 2 (volume : Measure ℂ) := by
    simpa [D] using (hW.complexWeakSobolevCutoff_memLp χ).2
  have hA2 : MemLp A 2 (volume : Measure ℂ) := by
    simpa [A] using MemLp.weakDZField hD2
  have hB2 : MemLp B 2 (volume : Measure ℂ) := by
    simpa [B] using MemLp.weakDBarField hD2
  have hνmeas : AEStronglyMeasurable ν (volume : Measure ℂ) := by
    simpa [ν] using
      localizedBeltramiCoefficient_aestronglyMeasurable χ hμmeas
  have hνbound : ∀ᵐ z ∂(volume : Measure ℂ), ‖ν z‖ ≤ k := by
    simpa [ν] using
      localizedBeltramiCoefficient_ae_norm_le χ hk hμbound
  let hνTop : MemLp ν ∞ (volume : Measure ℂ) :=
    memLp_top_of_bound hνmeas k hνbound
  let νTop : Lp ℂ ∞ (volume : Measure ℂ) := hνTop.toLp ν
  have hνnorm : ‖νTop‖ < 1 := by
    exact
      (norm_toLp_top_le_of_ae_bound ν hνTop hk hνbound).trans_lt hk1
  let P : NearTwoBeurlingParameters ‖νTop‖ :=
    chosenNearTwoBeurlingParameters hνnorm
  have hG2 : MemLp G 2 (volume : Measure ℂ) := by
    simpa [G] using
      complexWeakSobolevCutoffBeltramiError_memLp
        χ hf hμmeas hk hμbound 2
  have hGp : MemLp G (ENNReal.ofReal P.exponent)
      (volume : Measure ℂ) := by
    simpa [G] using
      complexWeakSobolevCutoffBeltramiError_memLp
        χ hf hμmeas hk hμbound (ENNReal.ofReal P.exponent)
  let G2 : PlaneL2 := hG2.toLp G
  let Gp : Lp ℂ (ENNReal.ofReal P.exponent) (volume : Measure ℂ) :=
    hGp.toLp G
  let A2 : PlaneL2 := hA2.toLp A
  let B2 : PlaneL2 := hB2.toLp B
  have hS : beurlingTransformL2 B2 = A2 := by
    simpa [A2, B2, A, B, D,
      complexWeakSobolevCutoffDBarPlaneL2,
      complexWeakSobolevCutoffDZPlaneL2] using
        beurlingTransformL2_complexWeakSobolevCutoffDBarPlaneL2 hW χ
  have hL2eq :
      B2 - νTop • beurlingTransformL2 B2 = G2 := by
    simpa [B2, νTop, G2, B, D, ν, G, hνTop, hG2] using
      complexWeakSobolevCutoffDBarPlaneL2_beltramiEquation
        hW hf χ hμmeas hk hμbound heq
  obtain ⟨R, hνzero_pointwise⟩ :=
    exists_closedBall_support_localizedBeltramiCoefficient χ μ
  have hνzero :
      ∀ᵐ z ∂(volume : Measure ℂ), R ≤ ‖z‖ →
        (νTop : ℂ → ℂ) z = 0 := by
    filter_upwards [hνTop.coeFn_toLp] with z hz hRz
    rw [hz]
    exact hνzero_pointwise z hRz
  have hGp2 : MemLp (Gp : ℂ → ℂ) 2 (volume : Measure ℂ) := by
    exact hG2.congr_norm (Lp.stronglyMeasurable Gp).aestronglyMeasurable
      (hGp.coeFn_toLp.symm.mono fun z hz ↦ congrArg norm hz)
  have hGp2class : hGp2.toLp (Gp : ℂ → ℂ) = G2 := by
    apply Lp.ext
    filter_upwards [
      hGp2.coeFn_toLp,
      hGp.coeFn_toLp,
      hG2.coeFn_toLp] with z hp2 hp h2
    calc
      (hGp2.toLp (Gp : ℂ → ℂ) : ℂ → ℂ) z =
          (Gp : ℂ → ℂ) z := hp2
      _ = G z := hp
      _ = (G2 : ℂ → ℂ) z := h2.symm
  let Sr :
      Lp ℂ (ENNReal.ofReal P.exponent) (volume : Measure ℂ) →L[ℂ]
        Lp ℂ (ENNReal.ofReal P.exponent) (volume : Measure ℂ) :=
    beurlingTransformLpNearTwo
      P.exponent P.dualExponent P.theta P.dual_holder
        P.two_lt_exponent.le
        ⟨P.theta_mem.1.le, P.theta_mem.2.le⟩
        P.reciprocal_exponent
  let H : Lp ℂ (ENNReal.ofReal P.exponent) (volume : Measure ℂ) :=
    beltramiLpNearTwoSolution
      νTop P.exponent P.dualExponent P.theta P.dual_holder
        P.two_lt_exponent.le
        ⟨P.theta_mem.1.le, P.theta_mem.2.le⟩
        P.reciprocal_exponent P.contraction Gp
  let hH2 : MemLp (H : ℂ → ℂ) 2 (volume : Measure ℂ) :=
    memLp_two_beltramiLpNearTwoSolution
      νTop P.exponent P.dualExponent P.theta P.dual_holder
        P.two_lt_exponent.le
        ⟨P.theta_mem.1.le, P.theta_mem.2.le⟩
        P.reciprocal_exponent P.contraction hνzero Gp hGp2
  have hidentify :
      hH2.toLp (H : ℂ → ℂ) =
        beltramiL2Solution νTop hνnorm
          (hGp2.toLp (Gp : ℂ → ℂ)) := by
    simpa [H, hH2] using
      beltramiLpNearTwoSolution_toLp_two_eq_beltramiL2Solution
        νTop hνnorm
        P.exponent P.dualExponent P.theta P.dual_holder
          P.two_lt_exponent.le
          ⟨P.theta_mem.1.le, P.theta_mem.2.le⟩
          P.reciprocal_exponent P.contraction hνzero Gp hGp2
  have hBsolution :
      B2 = beltramiL2Solution νTop hνnorm G2 :=
    beltramiL2Solution_unique νTop hνnorm G2 B2 hL2eq
  have hHclass : hH2.toLp (H : ℂ → ℂ) = B2 := by
    calc
      hH2.toLp (H : ℂ → ℂ) =
          beltramiL2Solution νTop hνnorm
            (hGp2.toLp (Gp : ℂ → ℂ)) := hidentify
      _ = beltramiL2Solution νTop hνnorm G2 := by rw [hGp2class]
      _ = B2 := hBsolution.symm
  have hHB : (H : ℂ → ℂ) =ᵐ[volume] B := by
    filter_upwards [hH2.coeFn_toLp, hB2.coeFn_toLp] with z hHz hBz
    rw [hHclass] at hHz
    exact hHz.symm.trans hBz
  have hBp : MemLp B (ENNReal.ofReal P.exponent)
      (volume : Measure ℂ) := by
    exact (Lp.memLp H).congr_norm hB2.aestronglyMeasurable
      (hHB.mono fun z hz ↦ congrArg norm hz)
  have hcompat :
      (Sr H : ℂ → ℂ) =ᵐ[volume]
        (beurlingTransformL2
          (hH2.toLp (H : ℂ → ℂ)) : ℂ → ℂ) := by
    simpa only [Sr, Lp.toLp_coeFn] using
      (beurlingTransformLpNearTwo_toLp_ae_eq_beurlingTransformL2
        P.exponent P.dualExponent P.theta P.dual_holder
          P.two_lt_exponent.le
          ⟨P.theta_mem.1.le, P.theta_mem.2.le⟩
          P.reciprocal_exponent
          (Lp.stronglyMeasurable H) (Lp.memLp H) hH2)
  rw [hHclass, hS] at hcompat
  have hSrA : (Sr H : ℂ → ℂ) =ᵐ[volume] A := by
    filter_upwards [hcompat, hA2.coeFn_toLp] with z hSz hAz
    exact hSz.trans hAz
  have hAp : MemLp A (ENNReal.ofReal P.exponent)
      (volume : Measure ℂ) := by
    exact (Lp.memLp (Sr H)).congr_norm hA2.aestronglyMeasurable
      (hSrA.mono fun z hz ↦ congrArg norm hz)
  refine ⟨P.exponent, P.two_lt_exponent, P.exponent_lt_three, ?_⟩
  change MemLp D (ENNReal.ofReal P.exponent) (volume : Measure ℂ)
  exact (hAp.norm.add hBp.norm).of_le hD2.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z ↦ by
      change ‖D z‖ ≤ ‖(‖A z‖ + ‖B z‖ : ℝ)‖
      rw [Real.norm_eq_abs,
        abs_of_nonneg (add_nonneg (norm_nonneg (A z)) (norm_nonneg (B z)))]
      simpa only [A, B, weakDZField, weakDBarField] using
        (norm_eq_norm_weakDZ_add_norm_weakDBar (D z)).le)

/--
%%handwave
name:
  Local higher integrability for planar Beltrami solutions
statement:
  Let $f\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb C)$ be continuous and
  satisfy
  $\partial_{\bar z}f=\mu\,\partial_zf$ almost everywhere in $\Omega$.
  Suppose $\mu$ is measurable and $|\mu|\leq k<1$ almost everywhere.
  Then for every compact set $Q\subset\Omega$ there is an exponent
  $r$ with $2<r<3$ such that
  $$
    Df\in L^r(Q).
  $$
proof:
  Choose a smooth cutoff equal to one with zero differential on $Q$ and
  compactly supported in $\Omega$. The cutoff-localized higher-integrability
  theorem gives $D(\chi f)\in L^r(\mathbb C)$ for some $2<r<3$.
  Since $D(\chi f)=Df$ on $Q$, restricting the global estimate proves the
  claim.
-/
theorem IsLocalW12On.exists_derivative_memLpOn_compact_nearTwo
    {Ω : Set ℂ} {f μ : ℂ → ℂ}
    {df : ℂ → ℂ →L[ℝ] ℂ}
    (hW : IsLocalW12On Ω f df) (hf : Continuous f)
    (hμmeas : AEStronglyMeasurable μ (volume : Measure ℂ))
    {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1)
    (hμbound : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ k)
    (heq : WeakBeltramiEquationOn Ω μ df)
    {Q : Set ℂ} (hQ : IsCompact Q) (hQΩ : Q ⊆ Ω) :
    ∃ r : ℝ, 2 < r ∧ r < 3 ∧
      MemLp df (ENNReal.ofReal r)
        ((volume : Measure ℂ).restrict Q) := by
  obtain ⟨χ⟩ :=
    JJMath.Uniformization.exists_scalarWeakSobolevCutoff
      hQ hQΩ hW.1
  obtain ⟨r, hr2, hr3, hDr⟩ :=
    hW.exists_memLp_complexWeakSobolevCutoffDerivative
      hf χ hμmeas hk hk1 hμbound heq
  refine ⟨r, hr2, hr3, ?_⟩
  have hDrQ :
      MemLp
        (complexWeakSobolevCutoffDerivative
          (χ : ℂ → ℝ) f df)
        (ENNReal.ofReal r) ((volume : Measure ℂ).restrict Q) :=
    hDr.mono_measure Measure.restrict_le_self
  have hdf2 :
      MemLp df 2 ((volume : Measure ℂ).restrict Q) :=
    (hW.2.2 Q hQ hQΩ).2
  apply hDrQ.congr_norm hdf2.aestronglyMeasurable
  exact ae_restrict_of_forall_mem hQ.measurableSet fun z hz ↦ by
    have hχz : χ z = 1 := χ.eq_one_on z hz
    have hdχz : fderiv ℝ (χ : ℂ → ℝ) z = 0 :=
      χ.fderiv_eq_zero_on z hz
    congr 1
    ext v
    simp [complexWeakSobolevCutoffDerivative, hχz, hdχz]

end

end Quasiconformal

end JJMath
