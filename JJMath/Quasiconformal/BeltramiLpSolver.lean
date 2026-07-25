import JJMath.Quasiconformal.BeurlingComplexInterpolation
import JJMath.Quasiconformal.BeltramiSolver
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The Beltrami equation above exponent two

This file turns the interpolated Beurling transform into the bounded operator
`M_μ S` on planar `L^r`.  For exponents on the interpolation segment from
`2` to `3`, the quantitative estimate proved here is the strict contraction
needed for the Neumann solution of the Beltrami equation.
-/

namespace JJMath

open MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology

namespace Quasiconformal

noncomputable section

/--
%%handwave
name:
  Near-$2$ Beurling contraction parameters
statement:
  For a real number $k<1$, near-$2$ contraction data consist of exponents
  $\theta,r,s$ with $0<\theta<1$, $2<r<3$, $s$ Hölder conjugate to $r$,
  $$
    \frac1r=\frac{1-\theta}{2}+\frac\theta3,
  $$
  and $kA_{3/2}^{\theta}<1$.
-/
structure NearTwoBeurlingParameters (k : ℝ) where
  theta : ℝ
  exponent : ℝ
  dualExponent : ℝ
  theta_mem : theta ∈ Set.Ioo (0 : ℝ) 1
  exponent_eq : exponent = beurlingNearTwoExponent theta
  two_lt_exponent : 2 < exponent
  exponent_lt_three : exponent < 3
  dual_holder : dualExponent.HolderConjugate exponent
  reciprocal_exponent :
    exponent⁻¹ = (1 - theta) / 2 + theta / 3
  contraction :
    k * (beurlingInterpolationNorm (3 / 2 : ℝ)).toReal ^ theta < 1

/--
%%handwave
name:
  Chosen near-$2$ Beurling contraction parameters
statement:
  For every real $k<1$, choose parameters $\theta,r,s$ satisfying
  $0<\theta<1$, $2<r<3$, the Hölder-conjugacy and reciprocal interpolation
  identities, and
  $$
    kA_{3/2}^{\theta}<1.
  $$
-/
def chosenNearTwoBeurlingParameters
    {k : ℝ} (hk : k < 1) : NearTwoBeurlingParameters k := by
  have hnonempty : Nonempty (NearTwoBeurlingParameters k) := by
    obtain ⟨θ, r, s, hθ, hr, hr2, hr3, hrs, hrrec, hcontract⟩ :=
      exists_beurlingNearTwo_contraction_parameters hk
    exact ⟨⟨θ, r, s, hθ, hr, hr2, hr3, hrs, hrrec, hcontract⟩⟩
  exact Classical.choice hnonempty

/--
%%handwave
name:
  The chosen near-$2$ exponent is an $L^p$ exponent
statement:
  Every near-$2$ contraction exponent $r$ satisfies $1\leq r$, and hence
  $1\leq\operatorname{ofReal}(r)$.
proof:
  The parameter data give the stronger inequality $2<r$.
-/
instance nearTwoBeurlingParametersFactOneLe
    {k : ℝ} (P : NearTwoBeurlingParameters k) :
    Fact (1 ≤ ENNReal.ofReal P.exponent) :=
  ⟨ENNReal.one_le_ofReal.mpr
    (le_trans (by norm_num) P.two_lt_exponent.le)⟩

/--
%%handwave
name:
  Algebraic $L^\infty$ multiplier on planar $L^r$
statement:
  For $r\geq1$ and $m\in L^\infty(\mathbb C)$, pointwise multiplication
  defines a complex-linear map
  $$
    L^r(\mathbb C)\longrightarrow L^r(\mathbb C),\qquad f\longmapsto mf.
  $$
-/
def lpPointwiseMultiplierLinearMap
    (r : ℝ) [Fact (1 ≤ ENNReal.ofReal r)]
    (m : Lp (α := ℂ) ℂ ∞ volume) :
    Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ) →ₗ[ℂ]
      Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ) where
  toFun f := m • f
  map_add' f g := MeasureTheory.Lp.add_smul m f g
  map_smul' c f := (MeasureTheory.Lp.smul_comm c m f).symm

/--
%%handwave
name:
  Bounded $L^\infty$ multiplier on planar $L^r$
statement:
  For $r\geq1$ and $m\in L^\infty(\mathbb C)$, pointwise multiplication is
  a bounded complex-linear operator
  $$
    M_m:L^r(\mathbb C)\longrightarrow L^r(\mathbb C),
    \qquad M_mf=mf.
  $$
-/
def lpPointwiseMultiplier
    (r : ℝ) [Fact (1 ≤ ENNReal.ofReal r)]
    (m : Lp (α := ℂ) ℂ ∞ volume) :
    Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ) →L[ℂ]
      Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ) :=
  LinearMap.mkContinuous (lpPointwiseMultiplierLinearMap r m) ‖m‖ fun f ↦
    MeasureTheory.Lp.norm_smul_le m f

/--
%%handwave
name:
  Operator norm of an $L^\infty$ multiplier on $L^r$
statement:
  For $r\geq1$ and $m\in L^\infty(\mathbb C)$,
  $$
    \|M_m\|_{L^r\to L^r}\leq\|m\|_{L^\infty}.
  $$
proof:
  The pointwise product satisfies the usual Hölder estimate
  $\|mf\|_r\leq\|m\|_\infty\|f\|_r$.
-/
theorem norm_lpPointwiseMultiplier_le
    (r : ℝ) [Fact (1 ≤ ENNReal.ofReal r)]
    (m : Lp (α := ℂ) ℂ ∞ volume) :
    ‖lpPointwiseMultiplier r m‖ ≤ ‖m‖ := by
  exact LinearMap.mkContinuous_norm_le
    (lpPointwiseMultiplierLinearMap r m) (norm_nonneg m)
      (fun f ↦ MeasureTheory.Lp.norm_smul_le m f)

/--
%%handwave
name:
  Lowering a compactly supported exponent from $r$ to $2$
statement:
  Let $r\geq2$. If $f\in L^r(\mathbb C)$ and there is $R\in\mathbb R$ such
  that $f(z)=0$ for almost every $z$ with $R\leq|z|$, then
  $f\in L^2(\mathbb C)$.
proof:
  Replace $f$ on a null set by its restriction to the closed disk of radius
  $R$. This disk has finite area, so finite-measure exponent monotonicity
  lowers $L^r$ to $L^2$. Almost-everywhere equality transfers the result back
  to $f$.
-/
theorem memLp_two_of_memLp_of_ae_zero_outside_closedBall
    {r : ℝ} (hr2 : 2 ≤ r) {f : ℂ → ℂ}
    (hfr : MemLp f (ENNReal.ofReal r) (volume : Measure ℂ))
    {R : ℝ}
    (hzero : ∀ᵐ z ∂(volume : Measure ℂ), R ≤ ‖z‖ → f z = 0) :
    MemLp f 2 (volume : Measure ℂ) := by
  let s : Set ℂ := Metric.closedBall 0 R
  let ν : ℂ → ℂ := s.indicator f
  have hνr : MemLp ν (ENNReal.ofReal r) (volume : Measure ℂ) :=
    hfr.indicator measurableSet_closedBall
  have h2r : (2 : ENNReal) ≤ ENNReal.ofReal r := by
    simpa using ENNReal.ofReal_le_ofReal hr2
  have hν2 : MemLp ν 2 (volume : Measure ℂ) :=
    hνr.mono_exponent_of_measure_support_ne_top
      (s := s)
      (fun z hz ↦ Set.indicator_of_notMem hz f)
      measure_closedBall_lt_top.ne h2r
  have hνf : ν =ᵐ[(volume : Measure ℂ)] f := by
    filter_upwards [hzero] with z hz
    by_cases hzs : z ∈ s
    · exact Set.indicator_of_mem hzs f
    · have hRz : R ≤ ‖z‖ := by
        have : ¬ ‖z‖ ≤ R := by
          simpa [s, Metric.mem_closedBall, dist_zero_right] using hzs
        exact (lt_of_not_ge this).le
      change s.indicator f z = f z
      rw [Set.indicator_of_notMem hzs, hz hRz]
  exact hν2.congr_norm hfr.aestronglyMeasurable
    (hνf.mono fun z hz ↦ congrArg norm hz)

/--
%%handwave
name:
  Every finite exponent for a bounded disk-supported function
statement:
  Let $f:\mathbb C\to\mathbb C$ be strongly measurable and essentially
  bounded. If $f$ vanishes almost everywhere outside a disk, then
  $f\in L^p(\mathbb C)$ for every extended exponent $p$.
proof:
  Replace $f$ on a null set by its restriction to the disk. The restricted
  function is essentially bounded and supported on a finite-area set, so
  finite-measure exponent monotonicity gives every lower exponent.
-/
theorem memLp_of_ae_bound_of_ae_zero_outside_closedBall
    (f : ℂ → ℂ)
    (hfmeas : AEStronglyMeasurable f (volume : Measure ℂ))
    {C R : ℝ}
    (hbound : ∀ᵐ z ∂(volume : Measure ℂ), ‖f z‖ ≤ C)
    (hzero : ∀ᵐ z ∂(volume : Measure ℂ), R ≤ ‖z‖ → f z = 0)
    (p : ENNReal) : MemLp f p (volume : Measure ℂ) := by
  let s : Set ℂ := Metric.closedBall 0 R
  let ν : ℂ → ℂ := s.indicator f
  have hfTop : MemLp f ∞ (volume : Measure ℂ) :=
    memLp_top_of_bound hfmeas C hbound
  have hνTop : MemLp ν ∞ (volume : Measure ℂ) :=
    hfTop.indicator measurableSet_closedBall
  have hνp : MemLp ν p (volume : Measure ℂ) :=
    hνTop.mono_exponent_of_measure_support_ne_top
      (s := s)
      (fun z hz ↦ Set.indicator_of_notMem hz f)
      measure_closedBall_lt_top.ne le_top
  have hνf : ν =ᵐ[(volume : Measure ℂ)] f := by
    filter_upwards [hzero] with z hz
    by_cases hzs : z ∈ s
    · exact Set.indicator_of_mem hzs f
    · have hRz : R ≤ ‖z‖ := by
        have : ¬ ‖z‖ ≤ R := by
          simpa [s, Metric.mem_closedBall, dist_zero_right] using hzs
        exact (lt_of_not_ge this).le
      change s.indicator f z = f z
      rw [Set.indicator_of_notMem hzs, hz hRz]
  exact hνp.congr_norm hfmeas (hνf.mono fun z hz ↦ congrArg norm hz)

/--
%%handwave
name:
  Planar $L^r$ Beltrami operator associated with a bounded transform
statement:
  If $T$ is a bounded complex-linear operator on $L^r(\mathbb C)$ and
  $\mu\in L^\infty(\mathbb C)$, define
  $$
    M_\mu T:L^r(\mathbb C)\longrightarrow L^r(\mathbb C),
    \qquad h\longmapsto\mu\,Th.
  $$
-/
def beltramiLpOperator
    (r : ℝ) [Fact (1 ≤ ENNReal.ofReal r)]
    (μ : Lp (α := ℂ) ℂ ∞ volume)
    (T : Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ) →L[ℂ]
      Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ)) :
    Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ) →L[ℂ]
      Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ) :=
  (lpPointwiseMultiplier r μ).comp T

/--
%%handwave
name:
  Norm bound for the planar $L^r$ Beltrami operator
statement:
  For every bounded complex-linear operator $T$ on $L^r(\mathbb C)$ and
  every $\mu\in L^\infty(\mathbb C)$,
  $$
    \|M_\mu T\|_{L^r\to L^r}
      \leq\|\mu\|_{L^\infty}\|T\|_{L^r\to L^r}.
  $$
proof:
  Bound the norm of the composition by the product of the two operator
  norms and use the $L^\infty$ multiplier estimate.
-/
theorem norm_beltramiLpOperator_le
    (r : ℝ) [Fact (1 ≤ ENNReal.ofReal r)]
    (μ : Lp (α := ℂ) ℂ ∞ volume)
    (T : Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ) →L[ℂ]
      Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ)) :
    ‖beltramiLpOperator r μ T‖ ≤ ‖μ‖ * ‖T‖ := by
  calc
    ‖beltramiLpOperator r μ T‖ ≤
        ‖lpPointwiseMultiplier r μ‖ * ‖T‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖μ‖ * ‖T‖ :=
      mul_le_mul_of_nonneg_right (norm_lpPointwiseMultiplier_le r μ)
        (norm_nonneg T)

/--
%%handwave
name:
  Beurling transform on the interpolation segment just above $2$
statement:
  Suppose $2\leq r$, $s$ is Hölder conjugate to $r$, $0\leq\theta\leq1$,
  and
  $$
    \frac1r=\frac{1-\theta}{2}+\frac\theta3.
  $$
  Then interpolation between the exact $L^2$ transform and the $L^3$
  estimate defines a bounded Beurling transform on $L^r(\mathbb C)$.
-/
def beurlingTransformLpNearTwo
    (r s θ : ℝ) [Fact (1 ≤ ENNReal.ofReal r)]
    (hrs : s.HolderConjugate r) (hr2 : 2 ≤ r)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hr_interp : r⁻¹ = (1 - θ) / 2 + θ / 3) :
    Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ) →L[ℂ]
      Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ) := by
  letI : Fact (1 ≤ ENNReal.ofReal (3 / 2 : ℝ)) := ⟨by norm_num⟩
  letI : Fact (1 ≤ ENNReal.ofReal (3 : ℝ)) := ⟨by norm_num⟩
  exact beurlingTransformLpInterpolated
    (3 / 2 : ℝ) 3 threeHalves_holderConjugate_three
      (by norm_num) (by norm_num)
    r s θ hrs hr2 hθ hr_interp

/--
%%handwave
name:
  Norm bound for the near-$2$ Beurling transform
statement:
  Under the interpolation hypotheses,
  $$
    \|\mathcal S_r\|_{L^r\to L^r}\leq A_{3/2}^{\theta}.
  $$
proof:
  This is the completed operator-norm interpolation estimate with endpoints
  $2$ and $3$ and below-$2$ dual exponent $3/2$.
-/
theorem norm_beurlingTransformLpNearTwo_le
    (r s θ : ℝ) [Fact (1 ≤ ENNReal.ofReal r)]
    (hrs : s.HolderConjugate r) (hr2 : 2 ≤ r)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hr_interp : r⁻¹ = (1 - θ) / 2 + θ / 3) :
    ‖beurlingTransformLpNearTwo r s θ hrs hr2 hθ hr_interp‖ ≤
      (beurlingInterpolationNorm (3 / 2 : ℝ)).toReal ^ θ := by
  letI : Fact (1 ≤ ENNReal.ofReal (3 / 2 : ℝ)) := ⟨by norm_num⟩
  letI : Fact (1 ≤ ENNReal.ofReal (3 : ℝ)) := ⟨by norm_num⟩
  exact norm_beurlingTransformLpInterpolated_operator_le
    (3 / 2 : ℝ) 3 threeHalves_holderConjugate_three
      (by norm_num) (by norm_num)
    r s θ hrs hr2 hθ hr_interp

/--
%%handwave
name:
  Near-$2$ interpolation agrees with the exact transform on simple data
statement:
  Under the interpolation hypotheses, the completed near-$2$ Beurling
  transform of every finite-support simple function agrees almost everywhere
  with the exact Fourier-multiplier $L^2$ transform of the same function.
proof:
  This is the common-core compatibility theorem for the completed
  interpolation operator, specialized to the endpoints $3/2$ and $3$.
-/
theorem
    beurlingTransformLpNearTwo_apply_simpleFunc_ae_eq_beurlingTransformL2
    (r s θ : ℝ) [Fact (1 ≤ ENNReal.ofReal r)]
    (hrs : s.HolderConjugate r) (hr2 : 2 ≤ r)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hr_interp : r⁻¹ = (1 - θ) / 2 + θ / 3)
    (F : Lp.simpleFunc ℂ (ENNReal.ofReal r) (volume : Measure ℂ)) :
    let F₁ : ℂ →₁[volume] ℂ :=
      simpleFuncToL1LinearMap (volume : Measure ℂ) (ENNReal.ofReal r)
        (ENNReal.ofReal_ne_zero_iff.mpr hrs.symm.pos)
        ENNReal.ofReal_ne_top F
    let hF₂ : MemLp (F₁ : ℂ → ℂ) 2 volume :=
      memLp_two_simpleFuncToL1LinearMap (volume : Measure ℂ)
        (ENNReal.ofReal r) (ENNReal.ofReal_ne_zero_iff.mpr hrs.symm.pos)
        ENNReal.ofReal_ne_top F
    (beurlingTransformLpNearTwo
        r s θ hrs hr2 hθ hr_interp
        (F : Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ)) : ℂ → ℂ)
      =ᵐ[volume]
        (beurlingTransformL2
          (hF₂.toLp (F₁ : ℂ → ℂ)) : ℂ → ℂ) := by
  letI : Fact (1 ≤ ENNReal.ofReal (3 / 2 : ℝ)) := ⟨by norm_num⟩
  letI : Fact (1 ≤ ENNReal.ofReal (3 : ℝ)) := ⟨by norm_num⟩
  simpa only [beurlingTransformLpNearTwo] using
    beurlingTransformLpInterpolated_apply_simpleFunc_ae_eq_beurlingTransformL2
      (3 / 2 : ℝ) 3 threeHalves_holderConjugate_three
        (by norm_num) (by norm_num)
      r s θ hrs hr2 hθ hr_interp F

/--
%%handwave
name:
  Compatibility of the near-$2$ and exact Beurling transforms
statement:
  Under the interpolation hypotheses, let
  $f:\mathbb C\to\mathbb C$ be strongly measurable and belong to both
  $L^r(\mathbb C)$ and $L^2(\mathbb C)$. Then
  $$
    \mathcal S_r[f]_{L^r}=\mathcal S_2[f]_{L^2}
  $$
  almost everywhere.
proof:
  Approximate $f$ by the same measurable simple functions simultaneously in
  $L^r$ and $L^2$. The two transforms agree on every approximant, while
  boundedness gives convergence in the respective $L^p$ norms and hence in
  measure. Uniqueness of the limit in measure gives the result.
-/
theorem beurlingTransformLpNearTwo_toLp_ae_eq_beurlingTransformL2
    (r s θ : ℝ) [Fact (1 ≤ ENNReal.ofReal r)]
    (hrs : s.HolderConjugate r) (hr2 : 2 ≤ r)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hr_interp : r⁻¹ = (1 - θ) / 2 + θ / 3)
    {f : ℂ → ℂ} (hfmeas : StronglyMeasurable f)
    (hfr : MemLp f (ENNReal.ofReal r) (volume : Measure ℂ))
    (hf2 : MemLp f 2 (volume : Measure ℂ)) :
    (beurlingTransformLpNearTwo r s θ hrs hr2 hθ hr_interp
        (hfr.toLp f) : ℂ → ℂ) =ᵐ[volume]
      (beurlingTransformL2 (hf2.toLp f) : ℂ → ℂ) := by
  letI : SeparableSpace (Set.range f ∪ {0} : Set ℂ) :=
    hfmeas.separableSpace_range_union_singleton
  let φ : ℕ → SimpleFunc ℂ ℂ := fun n ↦
    SimpleFunc.approxOn f hfmeas.measurable
      (Set.range f ∪ {0}) 0 (by simp) n
  let hφr (n : ℕ) : MemLp (φ n : ℂ → ℂ)
      (ENNReal.ofReal r) (volume : Measure ℂ) :=
    SimpleFunc.memLp_approxOn_range hfmeas.measurable hfr n
  let hφ2 (n : ℕ) : MemLp (φ n : ℂ → ℂ)
      2 (volume : Measure ℂ) :=
    SimpleFunc.memLp_approxOn_range hfmeas.measurable hf2 n
  let Fr (n : ℕ) :
      Lp.simpleFunc ℂ (ENNReal.ofReal r) (volume : Measure ℂ) :=
    SimpleFunc.toLp (φ n) (hφr n)
  have hinputr : Tendsto
      (fun n ↦ (Fr n :
        Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ))) atTop
      (𝓝 (hfr.toLp f)) := by
    simpa only [Fr, φ, hφr] using
      (SimpleFunc.tendsto_approxOn_range_Lp
        (p := ENNReal.ofReal r) ENNReal.ofReal_ne_top
        hfmeas.measurable hfr)
  have hinput2 : Tendsto
      (fun n ↦ (hφ2 n).toLp (φ n)) atTop
      (𝓝 (hf2.toLp f)) := by
    simpa only [φ, hφ2] using
      (SimpleFunc.tendsto_approxOn_range_Lp
        (p := (2 : ENNReal)) (by norm_num)
        hfmeas.measurable hf2)
  have houtputr : TendstoInMeasure (volume : Measure ℂ)
      (fun n ↦
        (beurlingTransformLpNearTwo r s θ hrs hr2 hθ hr_interp
          (Fr n : Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ)) :
            ℂ → ℂ)) atTop
      (beurlingTransformLpNearTwo r s θ hrs hr2 hθ hr_interp
        (hfr.toLp f) : ℂ → ℂ) := by
    apply tendstoInMeasure_of_tendsto_Lp
    exact (beurlingTransformLpNearTwo
      r s θ hrs hr2 hθ hr_interp).continuous.continuousAt.tendsto.comp hinputr
  have houtput2 : TendstoInMeasure (volume : Measure ℂ)
      (fun n ↦
        (beurlingTransformL2 ((hφ2 n).toLp (φ n)) : ℂ → ℂ)) atTop
      (beurlingTransformL2 (hf2.toLp f) : ℂ → ℂ) := by
    apply tendstoInMeasure_of_tendsto_Lp
    exact beurlingTransformL2.continuous.continuousAt.tendsto.comp hinput2
  have hcoreInput (n : ℕ) :
      let F₁ : ℂ →₁[volume] ℂ :=
        simpleFuncToL1LinearMap (volume : Measure ℂ) (ENNReal.ofReal r)
          (ENNReal.ofReal_ne_zero_iff.mpr hrs.symm.pos)
          ENNReal.ofReal_ne_top (Fr n)
      let hF₂ : MemLp (F₁ : ℂ → ℂ) 2 volume :=
        memLp_two_simpleFuncToL1LinearMap (volume : Measure ℂ)
          (ENNReal.ofReal r) (ENNReal.ofReal_ne_zero_iff.mpr hrs.symm.pos)
          ENNReal.ofReal_ne_top (Fr n)
      hF₂.toLp (F₁ : ℂ → ℂ) = (hφ2 n).toLp (φ n) := by
    dsimp only
    apply Lp.ext
    filter_upwards [
      (memLp_two_simpleFuncToL1LinearMap (volume : Measure ℂ)
        (ENNReal.ofReal r) (ENNReal.ofReal_ne_zero_iff.mpr hrs.symm.pos)
        ENNReal.ofReal_ne_top (Fr n)).coeFn_toLp,
      (hφ2 n).coeFn_toLp,
      (integrable_simpleFunc_toSimpleFunc
        (ENNReal.ofReal_ne_zero_iff.mpr hrs.symm.pos)
        ENNReal.ofReal_ne_top (Fr n)).coeFn_toL1,
      Lp.simpleFunc.toSimpleFunc_toLp (φ n) (hφr n)] with
        z hleft hright hL1 hsimple
    exact hleft.trans (hL1.trans (hsimple.trans hright.symm))
  have hcore (n : ℕ) :
      (beurlingTransformLpNearTwo r s θ hrs hr2 hθ hr_interp
          (Fr n : Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ)) : ℂ → ℂ)
        =ᵐ[volume]
      (beurlingTransformL2 ((hφ2 n).toLp (φ n)) : ℂ → ℂ) := by
    simpa only [hcoreInput n] using
      (beurlingTransformLpNearTwo_apply_simpleFunc_ae_eq_beurlingTransformL2
        r s θ hrs hr2 hθ hr_interp (Fr n))
  exact tendstoInMeasure_ae_unique houtputr
    (houtput2.congr_left fun n ↦ (hcore n).symm)

/--
%%handwave
name:
  Near-$2$ Beltrami--Beurling operator
statement:
  Under the interpolation hypotheses and for
  $\mu\in L^\infty(\mathbb C)$, define the bounded operator on
  $L^r(\mathbb C)$ by
  $$
    T_{\mu,r}=M_\mu\mathcal S_r,
    \qquad T_{\mu,r}h=\mu\,\mathcal S_rh.
  $$
-/
def beltramiLpNearTwoOperator
    (μ : Lp (α := ℂ) ℂ ∞ volume)
    (r s θ : ℝ) [Fact (1 ≤ ENNReal.ofReal r)]
    (hrs : s.HolderConjugate r) (hr2 : 2 ≤ r)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hr_interp : r⁻¹ = (1 - θ) / 2 + θ / 3) :
    Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ) →L[ℂ]
      Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ) :=
  beltramiLpOperator r μ
    (beurlingTransformLpNearTwo r s θ hrs hr2 hθ hr_interp)

/--
%%handwave
name:
  Action of the near-$2$ Beltrami--Beurling operator
statement:
  Under the interpolation hypotheses, for every $h\in L^r(\mathbb C)$,
  $$
    T_{\mu,r}h=\mu\,\mathcal S_rh.
  $$
proof:
  This is the defining composition of the interpolated Beurling transform
  with pointwise multiplication by $\mu$.
-/
@[simp]
theorem beltramiLpNearTwoOperator_apply
    (μ : Lp (α := ℂ) ℂ ∞ volume)
    (r s θ : ℝ) [Fact (1 ≤ ENNReal.ofReal r)]
    (hrs : s.HolderConjugate r) (hr2 : 2 ≤ r)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hr_interp : r⁻¹ = (1 - θ) / 2 + θ / 3)
    (h : Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ)) :
    beltramiLpNearTwoOperator μ r s θ hrs hr2 hθ hr_interp h =
      μ • beurlingTransformLpNearTwo r s θ hrs hr2 hθ hr_interp h := rfl

/--
%%handwave
name:
  Strict contraction of the near-$2$ Beltrami--Beurling operator
statement:
  Under the interpolation hypotheses, if
  $$
    \|\mu\|_{L^\infty}A_{3/2}^{\theta}<1,
  $$
  then
  $$
    \|M_\mu\mathcal S_r\|_{L^r\to L^r}<1.
  $$
proof:
  The multiplier norm is at most $\|\mu\|_\infty$ and the interpolated
  Beurling norm is at most $A_{3/2}^{\theta}$, so the norm of their
  composition is strictly less than one.
-/
theorem norm_beltramiLpOperator_beurlingNearTwo_lt_one
    (μ : Lp (α := ℂ) ℂ ∞ volume)
    (r s θ : ℝ) [Fact (1 ≤ ENNReal.ofReal r)]
    (hrs : s.HolderConjugate r) (hr2 : 2 ≤ r)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hr_interp : r⁻¹ = (1 - θ) / 2 + θ / 3)
    (hcontract :
      ‖μ‖ * (beurlingInterpolationNorm (3 / 2 : ℝ)).toReal ^ θ < 1) :
    ‖beltramiLpNearTwoOperator μ r s θ hrs hr2 hθ hr_interp‖ < 1 := by
  calc
    ‖beltramiLpNearTwoOperator μ r s θ hrs hr2 hθ hr_interp‖ ≤
      ‖μ‖ * ‖beurlingTransformLpNearTwo
        r s θ hrs hr2 hθ hr_interp‖ :=
      norm_beltramiLpOperator_le r μ _
    _ ≤ ‖μ‖ *
        (beurlingInterpolationNorm (3 / 2 : ℝ)).toReal ^ θ :=
      mul_le_mul_of_nonneg_left
        (norm_beurlingTransformLpNearTwo_le
          r s θ hrs hr2 hθ hr_interp) (norm_nonneg μ)
    _ < 1 := hcontract

/--
%%handwave
name:
  Invertible near-$2$ Beltrami resolvent
statement:
  Under the interpolation hypotheses, suppose
  $$
    \|\mu\|_{L^\infty}A_{3/2}^{\theta}<1.
  $$
  Then $I-M_\mu\mathcal S_r$ is an invertible bounded operator on
  $L^r(\mathbb C)$, with inverse given by its norm-convergent Neumann series.
-/
def beltramiLpNearTwoResolventUnit
    (μ : Lp (α := ℂ) ℂ ∞ volume)
    (r s θ : ℝ) [Fact (1 ≤ ENNReal.ofReal r)]
    (hrs : s.HolderConjugate r) (hr2 : 2 ≤ r)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hr_interp : r⁻¹ = (1 - θ) / 2 + θ / 3)
    (hcontract :
      ‖μ‖ * (beurlingInterpolationNorm (3 / 2 : ℝ)).toReal ^ θ < 1) :
    (Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ) →L[ℂ]
      Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ))ˣ :=
  Units.oneSub
    (beltramiLpNearTwoOperator μ r s θ hrs hr2 hθ hr_interp)
    (norm_beltramiLpOperator_beurlingNearTwo_lt_one
      μ r s θ hrs hr2 hθ hr_interp hcontract)

/--
%%handwave
name:
  Near-$2$ $L^r$ Beltrami solution
statement:
  Under the interpolation hypotheses and the strict contraction bound, for
  $g\in L^r(\mathbb C)$ define
  $$
    h=(I-M_\mu\mathcal S_r)^{-1}g.
  $$
-/
def beltramiLpNearTwoSolution
    (μ : Lp (α := ℂ) ℂ ∞ volume)
    (r s θ : ℝ) [Fact (1 ≤ ENNReal.ofReal r)]
    (hrs : s.HolderConjugate r) (hr2 : 2 ≤ r)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hr_interp : r⁻¹ = (1 - θ) / 2 + θ / 3)
    (hcontract :
      ‖μ‖ * (beurlingInterpolationNorm (3 / 2 : ℝ)).toReal ^ θ < 1)
    (g : Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ)) :
    Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ) :=
  (↑(beltramiLpNearTwoResolventUnit
    μ r s θ hrs hr2 hθ hr_interp hcontract)⁻¹ :
      Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ) →L[ℂ]
        Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ)) g

/--
%%handwave
name:
  The near-$2$ Neumann solution satisfies the Beltrami equation
statement:
  Under the interpolation hypotheses and
  $\|\mu\|_\infty A_{3/2}^{\theta}<1$, the Neumann solution associated with
  $g\in L^r(\mathbb C)$ satisfies
  $$
    h-\mu\,\mathcal S_rh=g.
  $$
proof:
  The contraction estimate makes $I-M_\mu\mathcal S_r$ a unit. Multiplying
  its inverse by the unit gives the identity operator.
-/
theorem beltramiLpNearTwoSolution_spec
    (μ : Lp (α := ℂ) ℂ ∞ volume)
    (r s θ : ℝ) [Fact (1 ≤ ENNReal.ofReal r)]
    (hrs : s.HolderConjugate r) (hr2 : 2 ≤ r)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hr_interp : r⁻¹ = (1 - θ) / 2 + θ / 3)
    (hcontract :
      ‖μ‖ * (beurlingInterpolationNorm (3 / 2 : ℝ)).toReal ^ θ < 1)
    (g : Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ)) :
    beltramiLpNearTwoSolution
        μ r s θ hrs hr2 hθ hr_interp hcontract g -
      μ • beurlingTransformLpNearTwo r s θ hrs hr2 hθ hr_interp
        (beltramiLpNearTwoSolution
          μ r s θ hrs hr2 hθ hr_interp hcontract g) = g := by
  let u := beltramiLpNearTwoResolventUnit
    μ r s θ hrs hr2 hθ hr_interp hcontract
  change (u : Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ) →L[ℂ]
      Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ))
      ((↑u⁻¹ : Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ) →L[ℂ]
        Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ)) g) = g
  rw [← ContinuousLinearMap.mul_apply, Units.mul_inv,
    ContinuousLinearMap.one_apply]

/--
%%handwave
name:
  Support of the near-$2$ Beltrami solution
statement:
  Under the interpolation and contraction hypotheses, suppose that both
  $mu$ and $g$ vanish almost everywhere outside the disk
  $overline B(0,R)$. Then the solution of
  $$
    h-\mu\,\mathcal S_rh=g
  $$
  also vanishes almost everywhere outside $overline B(0,R)$.
proof:
  Outside the disk the two prescribed functions vanish, so the equation
  reduces almost everywhere to $h=0$.
-/
theorem beltramiLpNearTwoSolution_ae_zero_outside_closedBall
    (μ : Lp (α := ℂ) ℂ ∞ volume)
    (r s θ : ℝ) [Fact (1 ≤ ENNReal.ofReal r)]
    (hrs : s.HolderConjugate r) (hr2 : 2 ≤ r)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hr_interp : r⁻¹ = (1 - θ) / 2 + θ / 3)
    (hcontract :
      ‖μ‖ * (beurlingInterpolationNorm (3 / 2 : ℝ)).toReal ^ θ < 1)
    {R : ℝ}
    (hμzero : ∀ᵐ z ∂(volume : Measure ℂ),
      R ≤ ‖z‖ → (μ : ℂ → ℂ) z = 0)
    (g : Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ))
    (hgzero : ∀ᵐ z ∂(volume : Measure ℂ),
      R ≤ ‖z‖ → (g : ℂ → ℂ) z = 0) :
    ∀ᵐ z ∂(volume : Measure ℂ), R ≤ ‖z‖ →
      (beltramiLpNearTwoSolution
        μ r s θ hrs hr2 hθ hr_interp hcontract g : ℂ → ℂ) z = 0 := by
  let S := beurlingTransformLpNearTwo r s θ hrs hr2 hθ hr_interp
  let h := beltramiLpNearTwoSolution
    μ r s θ hrs hr2 hθ hr_interp hcontract g
  have hspec : h - μ • S h = g :=
    beltramiLpNearTwoSolution_spec
      μ r s θ hrs hr2 hθ hr_interp hcontract g
  have hclass : ((h - μ • S h :
      Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ)) : ℂ → ℂ)
      =ᵐ[volume] (g : ℂ → ℂ) := by
    rw [hspec]
  filter_upwards [hμzero, hgzero, hclass,
      Lp.coeFn_sub h (μ • S h),
      Lp.coeFn_lpSMul (r := ENNReal.ofReal r) μ (S h)] with
      z hμz hgz hclassz hsubz hmulz
  intro hR
  rw [hsubz] at hclassz
  change (h : ℂ → ℂ) z - (μ • S h :
      Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ)) z =
        (g : ℂ → ℂ) z at hclassz
  rw [hmulz] at hclassz
  change (h : ℂ → ℂ) z -
      (μ : ℂ → ℂ) z * (S h : ℂ → ℂ) z = (g : ℂ → ℂ) z at hclassz
  rw [hμz hR, hgz hR, zero_mul, sub_zero] at hclassz
  exact hclassz

/--
%%handwave
name:
  Square integrability of the compactly supported near-$2$ solution
statement:
  Under the interpolation and contraction hypotheses, suppose
  $\mu\in L^\infty(\mathbb C)$ vanishes almost everywhere outside a disk.
  If $g\in L^r(\mathbb C)$ is also represented by an $L^2$ function, then
  the near-$2$ Neumann solution of
  $$
    h-\mu\,\mathcal S_rh=g
  $$
  belongs to $L^2(\mathbb C)$.
proof:
  The product $\mu\mathcal S_rh$ belongs to $L^r$ and is supported in the
  same finite-area disk as $\mu$, hence belongs to $L^2$ because $r\geq2$.
  The equation writes $h$ as the sum of this product and the $L^2$ right-hand
  side.
-/
theorem memLp_two_beltramiLpNearTwoSolution
    (μ : Lp (α := ℂ) ℂ ∞ volume)
    (r s θ : ℝ) [Fact (1 ≤ ENNReal.ofReal r)]
    (hrs : s.HolderConjugate r) (hr2 : 2 ≤ r)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hr_interp : r⁻¹ = (1 - θ) / 2 + θ / 3)
    (hcontract :
      ‖μ‖ * (beurlingInterpolationNorm (3 / 2 : ℝ)).toReal ^ θ < 1)
    {R : ℝ}
    (hμzero : ∀ᵐ z ∂(volume : Measure ℂ),
      R ≤ ‖z‖ → (μ : ℂ → ℂ) z = 0)
    (g : Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ))
    (hg2 : MemLp (g : ℂ → ℂ) 2 (volume : Measure ℂ)) :
    MemLp
      (beltramiLpNearTwoSolution
        μ r s θ hrs hr2 hθ hr_interp hcontract g : ℂ → ℂ)
      2 (volume : Measure ℂ) := by
  let S := beurlingTransformLpNearTwo r s θ hrs hr2 hθ hr_interp
  let h := beltramiLpNearTwoSolution
    μ r s θ hrs hr2 hθ hr_interp hcontract g
  let v : Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ) :=
    lpPointwiseMultiplier r μ (S h)
  have hvzero : ∀ᵐ z ∂(volume : Measure ℂ),
      R ≤ ‖z‖ → (v : ℂ → ℂ) z = 0 := by
    filter_upwards [hμzero,
      Lp.coeFn_lpSMul (r := ENNReal.ofReal r) μ (S h)] with z hμz hvz
    intro hR
    change (μ • S h :
      Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ)) z = 0
    rw [hvz]
    change (μ : ℂ → ℂ) z * (S h : ℂ → ℂ) z = 0
    rw [hμz hR, zero_mul]
  have hv2 : MemLp (v : ℂ → ℂ) 2 (volume : Measure ℂ) :=
    memLp_two_of_memLp_of_ae_zero_outside_closedBall
      hr2 (Lp.memLp v) hvzero
  have hspec : h - v = g := by
    exact beltramiLpNearTwoSolution_spec
      μ r s θ hrs hr2 hθ hr_interp hcontract g
  have heq : h = v + g := by
    calc
      h = g + v := (sub_eq_iff_eq_add).mp hspec
      _ = v + g := add_comm _ _
  rw [show beltramiLpNearTwoSolution
      μ r s θ hrs hr2 hθ hr_interp hcontract g = h from rfl, heq]
  exact MemLp.ae_eq (Lp.coeFn_add v g).symm (hv2.add hg2)

/--
%%handwave
name:
  Identification of the near-$2$ and $L^2$ Beltrami solutions
statement:
  Under the interpolation and contraction hypotheses, suppose
  $\|\mu\|_\infty<1$ and $mu$ vanishes almost everywhere outside a disk.
  If $g$ belongs to both $L^r(\mathbb C)$ and $L^2(\mathbb C)$, then the
  near-$2$ Neumann solution belongs to $L^2$ and its $L^2$ class equals
  $$
    (I-M_\mu\mathcal S_2)^{-1}g.
  $$
proof:
  Compact support first places the near-$2$ solution in $L^2$. Compatibility
  of the interpolated and exact Beurling transforms on
  $L^r\cap L^2$ turns its equation into the exact $L^2$ Beltrami equation.
  Uniqueness of the $L^2$ Neumann solution gives the equality.
-/
theorem beltramiLpNearTwoSolution_toLp_two_eq_beltramiL2Solution
    (μ : Lp (α := ℂ) ℂ ∞ volume) (hμ : ‖μ‖ < 1)
    (r s θ : ℝ) [Fact (1 ≤ ENNReal.ofReal r)]
    (hrs : s.HolderConjugate r) (hr2 : 2 ≤ r)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hr_interp : r⁻¹ = (1 - θ) / 2 + θ / 3)
    (hcontract :
      ‖μ‖ * (beurlingInterpolationNorm (3 / 2 : ℝ)).toReal ^ θ < 1)
    {R : ℝ}
    (hμzero : ∀ᵐ z ∂(volume : Measure ℂ),
      R ≤ ‖z‖ → (μ : ℂ → ℂ) z = 0)
    (g : Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ))
    (hg2 : MemLp (g : ℂ → ℂ) 2 (volume : Measure ℂ)) :
    let h := beltramiLpNearTwoSolution
      μ r s θ hrs hr2 hθ hr_interp hcontract g
    let hh2 : MemLp (h : ℂ → ℂ) 2 (volume : Measure ℂ) :=
      memLp_two_beltramiLpNearTwoSolution
        μ r s θ hrs hr2 hθ hr_interp hcontract hμzero g hg2
    hh2.toLp (h : ℂ → ℂ) =
      beltramiL2Solution μ hμ (hg2.toLp (g : ℂ → ℂ)) := by
  dsimp only
  let Sr := beurlingTransformLpNearTwo r s θ hrs hr2 hθ hr_interp
  let h := beltramiLpNearTwoSolution
    μ r s θ hrs hr2 hθ hr_interp hcontract g
  let hh2 : MemLp (h : ℂ → ℂ) 2 (volume : Measure ℂ) :=
    memLp_two_beltramiLpNearTwoSolution
      μ r s θ hrs hr2 hθ hr_interp hcontract hμzero g hg2
  have hcompat :
      (Sr h : ℂ → ℂ) =ᵐ[volume]
        (beurlingTransformL2 (hh2.toLp (h : ℂ → ℂ)) : ℂ → ℂ) := by
    simpa only [Sr, Lp.toLp_coeFn] using
      (beurlingTransformLpNearTwo_toLp_ae_eq_beurlingTransformL2
        r s θ hrs hr2 hθ hr_interp (Lp.stronglyMeasurable h)
          (Lp.memLp h) hh2)
  have hspec : h - μ • Sr h = g := by
    exact beltramiLpNearTwoSolution_spec
      μ r s θ hrs hr2 hθ hr_interp hcontract g
  have hclass :
      ((h - μ • Sr h :
        Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ)) : ℂ → ℂ)
        =ᵐ[volume] (g : ℂ → ℂ) := by
    rw [hspec]
  have hL2eq :
      hh2.toLp (h : ℂ → ℂ) -
          μ • beurlingTransformL2 (hh2.toLp (h : ℂ → ℂ)) =
        hg2.toLp (g : ℂ → ℂ) := by
    apply Lp.ext
    filter_upwards [
      hh2.coeFn_toLp,
      hg2.coeFn_toLp,
      Lp.coeFn_sub (hh2.toLp (h : ℂ → ℂ))
        (μ • beurlingTransformL2 (hh2.toLp (h : ℂ → ℂ))),
      Lp.coeFn_lpSMul (r := (2 : ENNReal)) μ
        (beurlingTransformL2 (hh2.toLp (h : ℂ → ℂ))),
      hcompat,
      hclass,
      Lp.coeFn_sub h (μ • Sr h),
      Lp.coeFn_lpSMul (r := ENNReal.ofReal r) μ (Sr h)] with
        z hh hg hsub2 hmul2 hSz hclassz hsubr hmulr
    calc
      (hh2.toLp (h : ℂ → ℂ) -
          μ • beurlingTransformL2 (hh2.toLp (h : ℂ → ℂ)) : PlaneL2) z =
          (hh2.toLp (h : ℂ → ℂ) : ℂ → ℂ) z -
            (μ • beurlingTransformL2
              (hh2.toLp (h : ℂ → ℂ)) : PlaneL2) z := hsub2
      _ = (h : ℂ → ℂ) z -
            (μ • beurlingTransformL2
              (hh2.toLp (h : ℂ → ℂ)) : PlaneL2) z := by rw [hh]
      _ = (h : ℂ → ℂ) z -
            (μ : ℂ → ℂ) z *
              (beurlingTransformL2
                (hh2.toLp (h : ℂ → ℂ)) : ℂ → ℂ) z := by
          rw [hmul2]
          rfl
      _ = (h : ℂ → ℂ) z -
            (μ : ℂ → ℂ) z * (Sr h : ℂ → ℂ) z := by rw [hSz]
      _ = (h : ℂ → ℂ) z - (μ • Sr h :
            Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ)) z := by
          rw [hmulr]
          rfl
      _ = (h - μ • Sr h :
            Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ)) z := hsubr.symm
      _ = (g : ℂ → ℂ) z := hclassz
      _ = (hg2.toLp (g : ℂ → ℂ) : ℂ → ℂ) z := hg.symm
  exact beltramiL2Solution_unique μ hμ
    (hg2.toLp (g : ℂ → ℂ)) (hh2.toLp (h : ℂ → ℂ)) hL2eq

/--
%%handwave
name:
  Uniqueness of the near-$2$ $L^r$ Beltrami solution
statement:
  Under the interpolation hypotheses and the strict contraction bound, if
  $g,h\in L^r(\mathbb C)$ satisfy
  $$
    h-\mu\,\mathcal S_rh=g,
  $$
  then $h=(I-M_\mu\mathcal S_r)^{-1}g$.
proof:
  Apply the inverse of the unit $I-M_\mu\mathcal S_r$ to the equation.
-/
theorem beltramiLpNearTwoSolution_unique
    (μ : Lp (α := ℂ) ℂ ∞ volume)
    (r s θ : ℝ) [Fact (1 ≤ ENNReal.ofReal r)]
    (hrs : s.HolderConjugate r) (hr2 : 2 ≤ r)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hr_interp : r⁻¹ = (1 - θ) / 2 + θ / 3)
    (hcontract :
      ‖μ‖ * (beurlingInterpolationNorm (3 / 2 : ℝ)).toReal ^ θ < 1)
    (g h : Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ))
    (hh : h - μ • beurlingTransformLpNearTwo
      r s θ hrs hr2 hθ hr_interp h = g) :
    h = beltramiLpNearTwoSolution
      μ r s θ hrs hr2 hθ hr_interp hcontract g := by
  let u := beltramiLpNearTwoResolventUnit
    μ r s θ hrs hr2 hθ hr_interp hcontract
  have hu_apply (x : Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ)) :
      (u : Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ) →L[ℂ]
        Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ)) x =
          x - μ • beurlingTransformLpNearTwo
            r s θ hrs hr2 hθ hr_interp x := by
    rfl
  have hinv_apply (x : Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ)) :
      (↑u⁻¹ : Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ) →L[ℂ]
        Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ))
          ((u : Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ) →L[ℂ]
            Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ)) x) = x := by
    rw [← ContinuousLinearMap.mul_apply, Units.inv_mul,
      ContinuousLinearMap.one_apply]
  calc
    h = (↑u⁻¹ : Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ) →L[ℂ]
        Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ))
          ((u : Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ) →L[ℂ]
            Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ)) h) :=
      (hinv_apply h).symm
    _ = (↑u⁻¹ : Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ) →L[ℂ]
        Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ)) g := by
      rw [hu_apply, hh]
    _ = beltramiLpNearTwoSolution
        μ r s θ hrs hr2 hθ hr_interp hcontract g := rfl

/--
%%handwave
name:
  Existence and uniqueness for the near-$2$ $L^r$ Beltrami equation
statement:
  Under the interpolation hypotheses and
  $\|\mu\|_\infty A_{3/2}^{\theta}<1$, every $g\in L^r(\mathbb C)$ admits
  a unique $h\in L^r(\mathbb C)$ satisfying
  $$
    h-\mu\,\mathcal S_rh=g.
  $$
proof:
  The inverse of $I-M_\mu\mathcal S_r$ supplies the solution, and applying
  the same inverse to any other solution proves uniqueness.
-/
theorem existsUnique_beltramiLpNearTwoEquation
    (μ : Lp (α := ℂ) ℂ ∞ volume)
    (r s θ : ℝ) [Fact (1 ≤ ENNReal.ofReal r)]
    (hrs : s.HolderConjugate r) (hr2 : 2 ≤ r)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hr_interp : r⁻¹ = (1 - θ) / 2 + θ / 3)
    (hcontract :
      ‖μ‖ * (beurlingInterpolationNorm (3 / 2 : ℝ)).toReal ^ θ < 1)
    (g : Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ)) :
    ∃! h : Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ),
      h - μ • beurlingTransformLpNearTwo
        r s θ hrs hr2 hθ hr_interp h = g := by
  refine ⟨beltramiLpNearTwoSolution
      μ r s θ hrs hr2 hθ hr_interp hcontract g,
    beltramiLpNearTwoSolution_spec
      μ r s θ hrs hr2 hθ hr_interp hcontract g, ?_⟩
  intro h hh
  exact beltramiLpNearTwoSolution_unique
    μ r s θ hrs hr2 hθ hr_interp hcontract g h hh

/--
%%handwave
name:
  Compactly supported Beltrami equation above exponent two
statement:
  Let $\mu:\mathbb C\to\mathbb C$ be strongly measurable, vanish almost
  everywhere outside a disk, and satisfy $|\mu|\leq k$ almost everywhere for
  $0\leq k<1$. Then there are parameters $0<\theta<1$ and $2<r<3$ for which
  $\|M_\mu\mathcal S_r\|<1$, and the equation
  $$
    h-\mu\,\mathcal S_rh=\mu
  $$
  has a unique solution $h\in L^r(\mathbb C)$.
proof:
  The essential bound gives $\|\mu\|_\infty<1$. Choose the near-$2$
  interpolation parameters for this norm. Bounded disk support places
  $\mu$ in the resulting $L^r$ space, and the Neumann resolvent gives the
  unique solution.
-/
theorem existsUnique_compactlySupported_beltramiLpNearTwoEquation
    (μ : ℂ → ℂ)
    (hμmeas : AEStronglyMeasurable μ (volume : Measure ℂ))
    {k R : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hbound : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ k)
    (hzero : ∀ᵐ z ∂(volume : Measure ℂ), R ≤ ‖z‖ → μ z = 0) :
    let hμTop : MemLp μ ∞ (volume : Measure ℂ) :=
      memLp_top_of_bound hμmeas k hbound
    ∃ P : NearTwoBeurlingParameters ‖hμTop.toLp μ‖,
      let hμr : MemLp μ (ENNReal.ofReal P.exponent)
          (volume : Measure ℂ) :=
        memLp_of_ae_bound_of_ae_zero_outside_closedBall
          μ hμmeas hbound hzero (ENNReal.ofReal P.exponent)
      ∃! h : Lp ℂ (ENNReal.ofReal P.exponent) (volume : Measure ℂ),
        h - hμTop.toLp μ •
            beurlingTransformLpNearTwo
              P.exponent P.dualExponent P.theta P.dual_holder
                P.two_lt_exponent.le
                ⟨P.theta_mem.1.le, P.theta_mem.2.le⟩
                P.reciprocal_exponent h =
          hμr.toLp μ := by
  dsimp only
  let hμTop : MemLp μ ∞ (volume : Measure ℂ) :=
    memLp_top_of_bound hμmeas k hbound
  have hnorm : ‖hμTop.toLp μ‖ < 1 :=
    (norm_toLp_top_le_of_ae_bound μ hμTop hk0 hbound).trans_lt hk1
  let P : NearTwoBeurlingParameters ‖hμTop.toLp μ‖ :=
    chosenNearTwoBeurlingParameters hnorm
  refine ⟨P, ?_⟩
  dsimp only
  let hμr : MemLp μ (ENNReal.ofReal P.exponent)
      (volume : Measure ℂ) :=
    memLp_of_ae_bound_of_ae_zero_outside_closedBall
      μ hμmeas hbound hzero (ENNReal.ofReal P.exponent)
  exact existsUnique_beltramiLpNearTwoEquation
    (hμTop.toLp μ)
    P.exponent P.dualExponent P.theta P.dual_holder
      P.two_lt_exponent.le
      ⟨P.theta_mem.1.le, P.theta_mem.2.le⟩
      P.reciprocal_exponent P.contraction (hμr.toLp μ)

end

end Quasiconformal

end JJMath
