import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import JJMath.Analysis.ConvergenceInMeasure
import JJMath.Quasiconformal.BeurlingWeakType

/-!
# Extension of the Beurling transform toward L¹

This file begins the density extension of the Beurling transform from
$L^1\cap L^2$ to $L^1$. The restricted weak $(1,1)$ estimate first gives the
key continuity statement: $L^1$-small inputs in the restricted domain have
Beurling transforms converging to zero in measure.
-/

namespace JJMath

open MeasureTheory Filter
open scoped ENNReal Topology

namespace Quasiconformal

noncomputable section

/--
%%handwave
name:
  Canonical simple approximation of an integrable planar function
statement:
  For $f\in L^1(\mathbb C)$, first replace $f$ on a null set by a measurable
  representative. Its $n$th range approximation is a simple function taking
  finitely many values near the range of $f$ and converging to $f$ in $L^1$.
-/
def integrableSimpleApproximation
    (f : ℂ → ℂ) (hf : Integrable f volume) (n : ℕ) : SimpleFunc ℂ ℂ :=
  let f' := hf.1.mk f
  SimpleFunc.approxOn f' hf.1.measurable_mk (Set.range f' ∪ {0}) 0 (by simp) n

/--
%%handwave
name:
  Integrability of the canonical simple approximants
statement:
  If $f\in L^1(\mathbb C)$, then every canonical simple approximant $f_n$ is
  integrable on $\mathbb C$.
proof:
  The measurable representative of $f$ is integrable because it agrees with
  $f$ almost everywhere. Apply integrability of the standard range-simple
  approximations.
-/
theorem integrable_integrableSimpleApproximation
    (f : ℂ → ℂ) (hf : Integrable f volume) (n : ℕ) :
    Integrable (integrableSimpleApproximation f hf n : ℂ → ℂ) volume := by
  let f' := hf.1.mk f
  have hf' : Integrable f' volume := hf.congr hf.1.ae_eq_mk
  exact SimpleFunc.integrable_approxOn_range hf.1.measurable_mk hf' n

/--
%%handwave
name:
  Square integrability of the canonical simple approximants
statement:
  If $f\in L^1(\mathbb C)$, then every canonical simple approximant $f_n$
  also belongs to $L^2(\mathbb C)$.
proof:
  An integrable simple function has level sets of finite measure away from
  zero. Since it takes only finitely many bounded values, the same condition
  places it in every finite $L^p$ space, in particular $L^2$.
-/
theorem memLp_two_integrableSimpleApproximation
    (f : ℂ → ℂ) (hf : Integrable f volume) (n : ℕ) :
    MemLp (integrableSimpleApproximation f hf n : ℂ → ℂ) 2 volume := by
  apply (SimpleFunc.memLp_iff_integrable (p := (2 : ENNReal))
    (by norm_num) (by norm_num)).2
  exact integrable_integrableSimpleApproximation f hf n

/--
%%handwave
name:
  Beurling transform of the canonical simple approximation
statement:
  For $f\in L^1(\mathbb C)$ and its canonical simple approximants $f_n$, the
  $n$th transformed approximation is the $L^2$ Beurling transform
  $\mathcal S f_n$, represented as a measurable function on $\mathbb C$.
-/
def integrableBeurlingApproximation
    (f : ℂ → ℂ) (hf : Integrable f volume) (n : ℕ) : ℂ → ℂ :=
  beurlingTransformL2
    ((memLp_two_integrableSimpleApproximation f hf n).toLp
      (integrableSimpleApproximation f hf n))

/--
%%handwave
name:
  Measurability of the transformed simple approximants
statement:
  If $f\in L^1(\mathbb C)$, then every function $\mathcal S f_n$ obtained
  from its canonical simple approximation is strongly measurable almost
  everywhere.
proof:
  Each transformed approximant is represented by an element of
  $L^2(\mathbb C)$, whose function representative is strongly measurable
  almost everywhere.
-/
theorem aestronglyMeasurable_integrableBeurlingApproximation
    (f : ℂ → ℂ) (hf : Integrable f volume) (n : ℕ) :
    AEStronglyMeasurable (integrableBeurlingApproximation f hf n) volume := by
  exact Lp.aestronglyMeasurable _

/--
%%handwave
name:
  $L^1$ convergence of the canonical simple approximants
statement:
  If $f\in L^1(\mathbb C)$ and $f_n$ is its canonical simple approximation,
  then
  $$
    \|f_n-f\|_1\longrightarrow0.
  $$
proof:
  The standard range-simple approximations converge in $L^1$ to the chosen
  measurable representative of $f$. That representative equals $f$ almost
  everywhere, so the same seminorm convergence holds for $f$.
-/
theorem eLpNorm_one_integrableSimpleApproximation_sub_tendsto_zero
    (f : ℂ → ℂ) (hf : Integrable f volume) :
    Tendsto
      (fun n ↦ eLpNorm
        ((integrableSimpleApproximation f hf n : ℂ → ℂ) - f) 1 volume)
      atTop (𝓝 0) := by
  let f' := hf.1.mk f
  have hf' : Integrable f' volume := hf.congr hf.1.ae_eq_mk
  have happrox :=
    SimpleFunc.tendsto_approxOn_range_L1_enorm hf.1.measurable_mk hf'
  simp only [← eLpNorm_one_eq_lintegral_enorm] at happrox
  apply Tendsto.congr' _ happrox
  filter_upwards with n
  apply eLpNorm_congr_ae
  exact EventuallyEq.rfl.sub hf.1.ae_eq_mk.symm

/--
%%handwave
name:
  $L^1$ masses of the canonical simple approximants converge
statement:
  If $f\in L^1(\mathbb C)$ and $f_n$ is its canonical simple approximation,
  then
  $$
    \int_{\mathbb C}|f_n(z)|\,dz
      \longrightarrow \int_{\mathbb C}|f(z)|\,dz.
  $$
proof:
  The approximants converge to $f$ in $L^1$. Continuity of the norm on the
  Banach space $L^1(\mathbb C)$ gives convergence of their norms, which are
  the displayed lower integrals.
-/
theorem lintegral_enorm_integrableSimpleApproximation_tendsto
    (f : ℂ → ℂ) (hf : Integrable f volume) :
    Tendsto
      (fun n ↦ ∫⁻ z,
        ‖(integrableSimpleApproximation f hf n : ℂ → ℂ) z‖ₑ ∂volume)
      atTop (𝓝 (∫⁻ z, ‖f z‖ₑ ∂volume)) := by
  let hfn : ∀ n, MemLp
      (integrableSimpleApproximation f hf n : ℂ → ℂ) 1 volume := fun n ↦
    memLp_one_iff_integrable.mpr
      (integrable_integrableSimpleApproximation f hf n)
  let hf₁ : MemLp f 1 volume := memLp_one_iff_integrable.mpr hf
  have happ_Lp : Tendsto
      (fun n ↦ (hfn n).toLp
        (integrableSimpleApproximation f hf n : ℂ → ℂ)) atTop
      (𝓝 (hf₁.toLp f)) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun n ↦ (integrableSimpleApproximation f hf n : ℂ → ℂ))
      hfn f hf₁).2
    exact eLpNorm_one_integrableSimpleApproximation_sub_tendsto_zero f hf
  have hnorm : Tendsto
      (fun n ↦ ‖(hfn n).toLp
        (integrableSimpleApproximation f hf n : ℂ → ℂ)‖) atTop
      (𝓝 ‖hf₁.toLp f‖) :=
    continuous_norm.continuousAt.tendsto.comp happ_Lp
  have henorm := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hnorm
  have hfn_fin : ∀ n,
      (∫⁻ z, ‖(integrableSimpleApproximation f hf n : ℂ → ℂ) z‖ₑ
        ∂volume) ≠ ∞ := by
    intro n
    simpa only [← eLpNorm_one_eq_lintegral_enorm] using (hfn n).2.ne
  have hf_fin : (∫⁻ z, ‖f z‖ₑ ∂volume) ≠ ∞ := by
    simpa only [← eLpNorm_one_eq_lintegral_enorm] using hf₁.2.ne
  simpa only [Function.comp_def, Lp.norm_toLp,
    eLpNorm_one_eq_lintegral_enorm, ENNReal.ofReal_toReal (hfn_fin _),
    ENNReal.ofReal_toReal hf_fin] using henorm

/--
%%handwave
name:
  The canonical simple approximants are $L^1$-Cauchy
statement:
  If $f\in L^1(\mathbb C)$ and $f_n$ is its canonical simple approximation,
  then
  $$
    \|f_n-f_m\|_1\longrightarrow0
    \qquad(n,m\to\infty).
  $$
proof:
  The triangle inequality gives
  $\|f_n-f_m\|_1\leq\|f_n-f\|_1+\|f_m-f\|_1$, and both terms tend to zero
  by the $L^1$ convergence of the approximants.
-/
theorem eLpNorm_one_integrableSimpleApproximation_cauchy
    (f : ℂ → ℂ) (hf : Integrable f volume) :
    Tendsto
      (fun nm : ℕ × ℕ ↦ eLpNorm
        ((integrableSimpleApproximation f hf nm.1 : ℂ → ℂ) -
          (integrableSimpleApproximation f hf nm.2 : ℂ → ℂ)) 1 volume)
      (atTop ×ˢ atTop) (𝓝 0) := by
  let a : ℕ → ENNReal := fun n ↦ eLpNorm
    ((integrableSimpleApproximation f hf n : ℂ → ℂ) - f) 1 volume
  have ha : Tendsto a atTop (𝓝 0) := by
    simpa only [a] using
      eLpNorm_one_integrableSimpleApproximation_sub_tendsto_zero f hf
  have hupper : Tendsto (fun nm : ℕ × ℕ ↦ a nm.1 + a nm.2)
      (atTop ×ˢ atTop) (𝓝 0) := by
    simpa using (ha.comp tendsto_fst).add (ha.comp tendsto_snd)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    hupper (fun _ ↦ zero_le) (fun nm ↦ ?_)
  have hn : AEStronglyMeasurable
      ((integrableSimpleApproximation f hf nm.1 : ℂ → ℂ) - f) volume :=
    (integrable_integrableSimpleApproximation f hf nm.1).1.sub hf.1
  have hm : AEStronglyMeasurable
      ((integrableSimpleApproximation f hf nm.2 : ℂ → ℂ) - f) volume :=
    (integrable_integrableSimpleApproximation f hf nm.2).1.sub hf.1
  rw [show
    (integrableSimpleApproximation f hf nm.1 : ℂ → ℂ) -
        (integrableSimpleApproximation f hf nm.2 : ℂ → ℂ) =
      ((integrableSimpleApproximation f hf nm.1 : ℂ → ℂ) - f) +
        -((integrableSimpleApproximation f hf nm.2 : ℂ → ℂ) - f) by
      funext z
      simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply]
      abel]
  simpa only [a, eLpNorm_neg] using
    eLpNorm_add_le hn hm.neg (by norm_num : (1 : ENNReal) ≤ 1)

/--
%%handwave
name:
  $L^1$-small restricted inputs have Beurling transforms vanishing in measure
statement:
  Let $f_i\in L^1(\mathbb C)\cap L^2(\mathbb C)$ be a family indexed by a
  filter. If $\|f_i\|_1\to0$, then the $L^2$ Beurling transforms satisfy
  $\mathcal S f_i\to0$ in measure on $\mathbb C$.
proof:
  For every finite $t>0$, [the restricted weak $(1,1)$ estimate](lean:JJMath.Quasiconformal.beurlingTransformL2_distribution_le_lintegral_of_integrable_memLp_two) gives
  $$
    t\,|\{|\mathcal S f_i|\geq t\}|
      \leq(40+16\pi)\|f_i\|_1.
  $$
  The right-hand side tends to zero, so [vanishing weak distribution bounds imply convergence in measure](lean:JJMath.HarmonicAnalysis.tendstoInMeasure_zero_of_weak_distribution_bound).
-/
theorem beurlingTransformL2_tendstoInMeasure_zero_of_eLpNorm_one_tendsto_zero
    {ι : Type*} {u : Filter ι} {f : ι → ℂ → ℂ}
    (hf₁ : ∀ i, Integrable (f i) volume)
    (hf₂ : ∀ i, MemLp (f i) 2 volume)
    (hf_zero : Tendsto (fun i ↦ eLpNorm (f i) 1 volume) u (𝓝 0)) :
    TendstoInMeasure volume
      (fun i ↦
        (beurlingTransformL2 ((hf₂ i).toLp (f i)) : ℂ → ℂ)) u 0 := by
  apply HarmonicAnalysis.tendstoInMeasure_zero_of_weak_distribution_bound
    (C := ENNReal.ofReal (40 + 16 * Real.pi)) ENNReal.ofReal_ne_top hf_zero
  intro i t ht0 httop
  simpa only [eLpNorm_one_eq_lintegral_enorm] using
    beurlingTransformL2_distribution_le_lintegral_of_integrable_memLp_two
      (hf₁ i) (hf₂ i) ht0 httop

/--
%%handwave
name:
  $L^1$-Cauchy restricted inputs have Beurling transforms Cauchy in measure
statement:
  Let $f_n\in L^1(\mathbb C)\cap L^2(\mathbb C)$ and suppose
  $$
    \|f_n-f_m\|_1\longrightarrow0
    \qquad(n,m\to\infty).
  $$
  Then
  $$
    \mathcal S f_n-\mathcal S f_m\longrightarrow0
  $$
  in measure on $\mathbb C$ as $n,m\to\infty$.
proof:
  Apply [the restricted continuity in measure](lean:JJMath.Quasiconformal.beurlingTransformL2_tendstoInMeasure_zero_of_eLpNorm_one_tendsto_zero) to the two-parameter family $f_n-f_m$. Linearity of the $L^2$ Beurling transform identifies its transform with $\mathcal S f_n-\mathcal S f_m$ almost everywhere.
-/
theorem beurlingTransformL2_cauchyInMeasure_of_eLpNorm_one_cauchy
    {f : ℕ → ℂ → ℂ}
    (hf₁ : ∀ n, Integrable (f n) volume)
    (hf₂ : ∀ n, MemLp (f n) 2 volume)
    (hf_cauchy : Tendsto
      (fun nm : ℕ × ℕ ↦ eLpNorm (f nm.1 - f nm.2) 1 volume)
      (atTop ×ˢ atTop) (𝓝 0)) :
    TendstoInMeasure volume
      (fun nm : ℕ × ℕ ↦
        (beurlingTransformL2 ((hf₂ nm.1).toLp (f nm.1)) : ℂ → ℂ) -
          (beurlingTransformL2 ((hf₂ nm.2).toLp (f nm.2)) : ℂ → ℂ))
      (atTop ×ˢ atTop) 0 := by
  let hdiff₂ : ∀ nm : ℕ × ℕ, MemLp (f nm.1 - f nm.2) 2 volume :=
    fun nm ↦ (hf₂ nm.1).sub (hf₂ nm.2)
  have hzero :=
    beurlingTransformL2_tendstoInMeasure_zero_of_eLpNorm_one_tendsto_zero
      (u := atTop ×ˢ atTop) (f := fun nm : ℕ × ℕ ↦ f nm.1 - f nm.2)
      (fun nm ↦ (hf₁ nm.1).sub (hf₁ nm.2)) hdiff₂ hf_cauchy
  apply hzero.congr_left
  intro nm
  have hLp :
      (hdiff₂ nm).toLp (f nm.1 - f nm.2) =
        (hf₂ nm.1).toLp (f nm.1) - (hf₂ nm.2).toLp (f nm.2) := by
    exact MemLp.toLp_sub (hf₂ nm.1) (hf₂ nm.2)
  rw [hLp, map_sub]
  exact Lp.coeFn_sub
    (beurlingTransformL2 ((hf₂ nm.1).toLp (f nm.1)))
    (beurlingTransformL2 ((hf₂ nm.2).toLp (f nm.2)))

/--
%%handwave
name:
  Beurling transforms of the canonical simple approximants are Cauchy in measure
statement:
  If $f\in L^1(\mathbb C)$ and $f_n$ is its canonical simple approximation,
  then
  $$
    \mathcal S f_n-\mathcal S f_m\longrightarrow0
  $$
  in measure on $\mathbb C$ as $n,m\to\infty$.
proof:
  Each $f_n$ lies in $L^1\cap L^2$, and the family is $L^1$-Cauchy. Apply [restricted $L^1$-Cauchy continuity of the Beurling transform](lean:JJMath.Quasiconformal.beurlingTransformL2_cauchyInMeasure_of_eLpNorm_one_cauchy).
-/
theorem beurlingTransformL2_integrableSimpleApproximation_cauchyInMeasure
    (f : ℂ → ℂ) (hf : Integrable f volume) :
    TendstoInMeasure volume
      (fun nm : ℕ × ℕ ↦
        integrableBeurlingApproximation f hf nm.1 -
          integrableBeurlingApproximation f hf nm.2)
      (atTop ×ˢ atTop) 0 := by
  simpa only [integrableBeurlingApproximation] using
    beurlingTransformL2_cauchyInMeasure_of_eLpNorm_one_cauchy
      (fun n ↦ integrable_integrableSimpleApproximation f hf n)
      (fun n ↦ memLp_two_integrableSimpleApproximation f hf n)
      (eLpNorm_one_integrableSimpleApproximation_cauchy f hf)

/--
%%handwave
name:
  Almost-everywhere limit of the transformed simple approximants
statement:
  For every $f\in L^1(\mathbb C)$, there are a strongly measurable function
  $G:\mathbb C\to\mathbb C$ and strictly increasing integers $n_k$ such that
  $$
    \mathcal S f_{n_k}(z)\longrightarrow G(z)
  $$
  for almost every $z$, where $f_n$ is the canonical simple approximation of
  $f$.
proof:
  The transformed approximants are strongly measurable almost everywhere
  and Cauchy in measure. Apply [the almost-everywhere subsequence extraction theorem](lean:JJMath.exists_strictMono_tendsto_ae_of_cauchyInMeasure).
-/
theorem exists_integrableBeurlingLimit
    (f : ℂ → ℂ) (hf : Integrable f volume) :
    ∃ G : ℂ → ℂ, AEStronglyMeasurable G volume ∧
      ∃ ns : ℕ → ℕ, StrictMono ns ∧
        ∀ᵐ z ∂volume,
          Tendsto (fun k ↦ integrableBeurlingApproximation f hf (ns k) z)
            atTop (𝓝 (G z)) := by
  exact exists_strictMono_tendsto_ae_of_cauchyInMeasure
    (fun n ↦ aestronglyMeasurable_integrableBeurlingApproximation f hf n)
    (beurlingTransformL2_integrableSimpleApproximation_cauchyInMeasure f hf)

/--
%%handwave
name:
  Canonical measurable Beurling limit of an integrable function
statement:
  For $f\in L^1(\mathbb C)$, choose the measurable almost-everywhere limit of
  a rapidly convergent subsequence of the Beurling transforms of its canonical
  simple approximants. This function is the candidate weak-$L^1$ Beurling
  transform of $f$.
-/
def integrableBeurlingLimit
    (f : ℂ → ℂ) (hf : Integrable f volume) : ℂ → ℂ :=
  Classical.choose (exists_integrableBeurlingLimit f hf)

/--
%%handwave
name:
  Measurability of the canonical Beurling limit
statement:
  For every $f\in L^1(\mathbb C)$, its canonical Beurling limit is strongly
  measurable almost everywhere.
proof:
  This is part of the defining choice of the canonical limit.
-/
theorem aestronglyMeasurable_integrableBeurlingLimit
    (f : ℂ → ℂ) (hf : Integrable f volume) :
    AEStronglyMeasurable (integrableBeurlingLimit f hf) volume :=
  (Classical.choose_spec (exists_integrableBeurlingLimit f hf)).1

/--
%%handwave
name:
  A subsequence converges almost everywhere to the canonical Beurling limit
statement:
  If $f\in L^1(\mathbb C)$, then there is a strictly increasing sequence
  $n_k$ such that
  $$
    \mathcal S f_{n_k}(z)\longrightarrow G_f(z)
  $$
  for almost every $z$, where $G_f$ is the canonical Beurling limit.
proof:
  This is the convergence property included in the defining choice of
  $G_f$.
-/
theorem exists_strictMono_integrableBeurlingApproximation_tendsto_ae
    (f : ℂ → ℂ) (hf : Integrable f volume) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ z ∂volume,
        Tendsto (fun k ↦ integrableBeurlingApproximation f hf (ns k) z)
          atTop (𝓝 (integrableBeurlingLimit f hf z)) :=
  (Classical.choose_spec (exists_integrableBeurlingLimit f hf)).2

/--
%%handwave
name:
  Local convergence in measure to the canonical Beurling limit
statement:
  Let $f\in L^1(\mathbb C)$ and let $G_f$ be its canonical Beurling limit.
  For every $R\in\mathbb R$, the full sequence of transformed simple
  approximants satisfies
  $$
    \mathcal S f_n\longrightarrow G_f
  $$
  in measure on the closed disk $\overline B(0,R)$.
proof:
  Restriction to the disk is a finite measure space. The full transformed
  sequence remains Cauchy in measure there, while a strictly increasing
  subsequence converges almost everywhere to $G_f$. Apply [the finite-measure Cauchy criterion with a known subsequential limit](lean:JJMath.tendstoInMeasure_of_cauchyInMeasure_of_subseq_ae).
-/
theorem integrableBeurlingApproximation_tendstoInMeasure_restrict_closedBall
    (f : ℂ → ℂ) (hf : Integrable f volume) (R : ℝ) :
    TendstoInMeasure (volume.restrict (Metric.closedBall (0 : ℂ) R))
      (integrableBeurlingApproximation f hf) atTop
      (integrableBeurlingLimit f hf) := by
  let ν : Measure ℂ := volume.restrict (Metric.closedBall (0 : ℂ) R)
  letI : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 (by
    simp only [Complex.volume_closedBall]
    finiteness)
  rcases exists_strictMono_integrableBeurlingApproximation_tendsto_ae f hf with
    ⟨ns, hns, hsub⟩
  apply tendstoInMeasure_of_cauchyInMeasure_of_subseq_ae
    (μ := ν) (ns := ns)
  · intro n
    exact (aestronglyMeasurable_integrableBeurlingApproximation f hf n).mono_measure
      Measure.restrict_le_self
  · exact JJMath.tendstoInMeasure_mono_measure Measure.restrict_le_self
      (beurlingTransformL2_integrableSimpleApproximation_cauchyInMeasure f hf)
  · exact hns
  · exact ae_mono Measure.restrict_le_self hsub

/--
%%handwave
name:
  $L^2$ convergence of the canonical simple approximants
statement:
  If $f\in L^1(\mathbb C)\cap L^2(\mathbb C)$ and $f_n$ is its canonical
  simple approximation, then
  $$
    \|f_n-f\|_2\longrightarrow0.
  $$
proof:
  The range-simple approximation of a measurable $L^2$ representative
  converges in $L^2$. The chosen representative agrees with $f$ almost
  everywhere, so the same seminorm convergence holds for $f$.
-/
theorem eLpNorm_two_integrableSimpleApproximation_sub_tendsto_zero
    (f : ℂ → ℂ) (hf₁ : Integrable f volume) (hf₂ : MemLp f 2 volume) :
    Tendsto
      (fun n ↦ eLpNorm
        ((integrableSimpleApproximation f hf₁ n : ℂ → ℂ) - f) 2 volume)
      atTop (𝓝 0) := by
  let f' := hf₁.1.mk f
  have hf₂' : MemLp f' 2 volume := hf₂.ae_eq hf₁.1.ae_eq_mk
  have happrox := SimpleFunc.tendsto_approxOn_range_Lp_eLpNorm
    (p := (2 : ENNReal)) (by norm_num) hf₁.1.measurable_mk hf₂'.2
  apply Tendsto.congr' _ happrox
  filter_upwards with n
  apply eLpNorm_congr_ae
  exact EventuallyEq.rfl.sub hf₁.1.ae_eq_mk.symm

/--
%%handwave
name:
  Transformed simple approximants converge to the $L^2$ Beurling transform
statement:
  If $f\in L^1(\mathbb C)\cap L^2(\mathbb C)$, then the Beurling transforms
  of its canonical simple approximants converge in measure on $\mathbb C$ to
  the $L^2$ Beurling transform $\mathcal Sf$.
proof:
  The simple approximants converge to $f$ in $L^2$. Continuity of the
  isometric $L^2$ Beurling transform preserves this convergence, and
  convergence in $L^2$ implies convergence in measure.
-/
theorem integrableBeurlingApproximation_tendstoInMeasure_beurlingTransformL2
    (f : ℂ → ℂ) (hf₁ : Integrable f volume) (hf₂ : MemLp f 2 volume) :
    TendstoInMeasure volume (integrableBeurlingApproximation f hf₁) atTop
      (beurlingTransformL2 (hf₂.toLp f) : ℂ → ℂ) := by
  have happ_Lp : Tendsto
      (fun n ↦ (memLp_two_integrableSimpleApproximation f hf₁ n).toLp
        (integrableSimpleApproximation f hf₁ n)) atTop
      (𝓝 (hf₂.toLp f)) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun n ↦ (integrableSimpleApproximation f hf₁ n : ℂ → ℂ))
      (fun n ↦ memLp_two_integrableSimpleApproximation f hf₁ n)
      f hf₂).2
    exact eLpNorm_two_integrableSimpleApproximation_sub_tendsto_zero f hf₁ hf₂
  have htransform_Lp : Tendsto
      (fun n ↦ beurlingTransformL2
        ((memLp_two_integrableSimpleApproximation f hf₁ n).toLp
          (integrableSimpleApproximation f hf₁ n))) atTop
      (𝓝 (beurlingTransformL2 (hf₂.toLp f))) :=
    (beurlingTransformL2.continuous.tendsto _).comp happ_Lp
  simpa only [integrableBeurlingApproximation] using
    (tendstoInMeasure_of_tendsto_Lp htransform_Lp)

/--
%%handwave
name:
  Compatibility of the canonical $L^1$ limit with the $L^2$ Beurling transform
statement:
  If $f\in L^1(\mathbb C)\cap L^2(\mathbb C)$, then its canonical Beurling
  limit agrees almost everywhere with the Fourier-multiplier $L^2$ Beurling
  transform:
  $$
    G_f(z)=\mathcal Sf(z)
    \quad\text{for almost every }z\in\mathbb C.
  $$
proof:
  On each closed integer-radius disk, the transformed simple approximants
  converge in measure both to $G_f$ and to the $L^2$ transform. Uniqueness of
  limits in measure identifies the two functions almost everywhere on that
  disk. The increasing integer disks exhaust $\mathbb C$.
-/
theorem integrableBeurlingLimit_ae_eq_beurlingTransformL2
    (f : ℂ → ℂ) (hf₁ : Integrable f volume) (hf₂ : MemLp f 2 volume) :
    integrableBeurlingLimit f hf₁ =ᵐ[volume]
      (beurlingTransformL2 (hf₂.toLp f) : ℂ → ℂ) := by
  have hglobalL2 :=
    integrableBeurlingApproximation_tendstoInMeasure_beurlingTransformL2
      f hf₁ hf₂
  have hpiece : ∀ n : ℕ,
      integrableBeurlingLimit f hf₁ =ᵐ[volume.restrict
        (Metric.closedBall (0 : ℂ) (n : ℝ))]
        (beurlingTransformL2 (hf₂.toLp f) : ℂ → ℂ) := by
    intro n
    apply tendstoInMeasure_ae_unique
      (integrableBeurlingApproximation_tendstoInMeasure_restrict_closedBall
        f hf₁ n)
    exact JJMath.tendstoInMeasure_mono_measure Measure.restrict_le_self hglobalL2
  have hglobal : integrableBeurlingLimit f hf₁ =ᵐ[volume.restrict
      (⋃ n : ℕ, Metric.closedBall (0 : ℂ) n)]
      (beurlingTransformL2 (hf₂.toLp f) : ℂ → ℂ) :=
    (ae_eq_restrict_iUnion_iff
      (fun n : ℕ ↦ Metric.closedBall (0 : ℂ) n)
      (integrableBeurlingLimit f hf₁)
      (beurlingTransformL2 (hf₂.toLp f) : ℂ → ℂ)).2 hpiece
  simpa [Metric.iUnion_closedBall_nat, Measure.restrict_univ] using hglobal

/--
%%handwave
name:
  Canonical simple approximations respect almost-everywhere equality in $L^1$
statement:
  Let $f,g\in L^1(\mathbb C)$ and suppose $f=g$ almost everywhere. If
  $f_n,g_n$ are their canonical simple approximants, then
  $$
    \|f_n-g_n\|_1\longrightarrow0.
  $$
proof:
  Almost everywhere,
  $f_n-g_n=(f_n-f)-(g_n-g)$. The $L^1$ triangle inequality bounds its norm
  by $\|f_n-f\|_1+\|g_n-g\|_1$, and both terms tend to zero.
-/
theorem eLpNorm_one_integrableSimpleApproximation_sub_of_ae_eq_tendsto_zero
    {f g : ℂ → ℂ} (hf : Integrable f volume) (hg : Integrable g volume)
    (hfg : f =ᵐ[volume] g) :
    Tendsto
      (fun n ↦ eLpNorm
        ((integrableSimpleApproximation f hf n : ℂ → ℂ) -
          (integrableSimpleApproximation g hg n : ℂ → ℂ)) 1 volume)
      atTop (𝓝 0) := by
  have hf_zero :=
    eLpNorm_one_integrableSimpleApproximation_sub_tendsto_zero f hf
  have hg_zero :=
    eLpNorm_one_integrableSimpleApproximation_sub_tendsto_zero g hg
  have hupper : Tendsto
      (fun n ↦ eLpNorm
          ((integrableSimpleApproximation f hf n : ℂ → ℂ) - f) 1 volume +
        eLpNorm
          ((integrableSimpleApproximation g hg n : ℂ → ℂ) - g) 1 volume)
      atTop (𝓝 0) := by
    simpa using hf_zero.add hg_zero
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    hupper (fun _ ↦ zero_le) (fun n ↦ ?_)
  have heq :
      (integrableSimpleApproximation f hf n : ℂ → ℂ) -
          (integrableSimpleApproximation g hg n : ℂ → ℂ) =ᵐ[volume]
        ((integrableSimpleApproximation f hf n : ℂ → ℂ) - f) -
          ((integrableSimpleApproximation g hg n : ℂ → ℂ) - g) := by
    filter_upwards [hfg] with z hz
    simp only [Pi.sub_apply]
    rw [hz]
    abel
  rw [eLpNorm_congr_ae heq]
  exact eLpNorm_sub_le
    ((integrable_integrableSimpleApproximation f hf n).1.sub hf.1)
    ((integrable_integrableSimpleApproximation g hg n).1.sub hg.1)
    (by norm_num)

/--
%%handwave
name:
  Transformed canonical approximations respect almost-everywhere equality
statement:
  Let $f,g\in L^1(\mathbb C)$ and suppose $f=g$ almost everywhere. Then
  $$
    \mathcal S f_n-\mathcal S g_n\longrightarrow0
  $$
  in measure on $\mathbb C$, where $f_n,g_n$ are their canonical simple
  approximants.
proof:
  The differences $f_n-g_n$ lie in $L^1\cap L^2$ and tend to zero in $L^1$.
  Apply [restricted continuity of the Beurling transform in measure](lean:JJMath.Quasiconformal.beurlingTransformL2_tendstoInMeasure_zero_of_eLpNorm_one_tendsto_zero) and use linearity of the $L^2$ transform.
-/
theorem integrableBeurlingApproximation_sub_tendstoInMeasure_zero_of_ae_eq
    {f g : ℂ → ℂ} (hf : Integrable f volume) (hg : Integrable g volume)
    (hfg : f =ᵐ[volume] g) :
    TendstoInMeasure volume
      (fun n ↦ integrableBeurlingApproximation f hf n -
        integrableBeurlingApproximation g hg n) atTop 0 := by
  let d : ℕ → ℂ → ℂ := fun n ↦
    (integrableSimpleApproximation f hf n : ℂ → ℂ) -
      (integrableSimpleApproximation g hg n : ℂ → ℂ)
  let hd₂ : ∀ n, MemLp (d n) 2 volume := fun n ↦
    (memLp_two_integrableSimpleApproximation f hf n).sub
      (memLp_two_integrableSimpleApproximation g hg n)
  have hzero :=
    beurlingTransformL2_tendstoInMeasure_zero_of_eLpNorm_one_tendsto_zero
      (f := d)
      (fun n ↦ (integrable_integrableSimpleApproximation f hf n).sub
        (integrable_integrableSimpleApproximation g hg n))
      hd₂
      (eLpNorm_one_integrableSimpleApproximation_sub_of_ae_eq_tendsto_zero
        hf hg hfg)
  apply hzero.congr_left
  intro n
  have hLp : (hd₂ n).toLp (d n) =
      (memLp_two_integrableSimpleApproximation f hf n).toLp
          (integrableSimpleApproximation f hf n) -
        (memLp_two_integrableSimpleApproximation g hg n).toLp
          (integrableSimpleApproximation g hg n) := by
    exact MemLp.toLp_sub
      (memLp_two_integrableSimpleApproximation f hf n)
      (memLp_two_integrableSimpleApproximation g hg n)
  rw [hLp, map_sub]
  exact Lp.coeFn_sub _ _

/--
%%handwave
name:
  The canonical Beurling limit depends only on the almost-everywhere class
statement:
  If $f,g\in L^1(\mathbb C)$ and $f=g$ almost everywhere, then their
  canonical Beurling limits agree almost everywhere:
  $$
    G_f=G_g\quad\text{almost everywhere on }\mathbb C.
  $$
proof:
  On every closed integer-radius disk, the transformed approximants converge
  in measure to $G_f$ and $G_g$, while their difference converges in measure
  to zero. Preservation of convergence in measure under subtraction and
  uniqueness of the limit give $G_f-G_g=0$ almost everywhere on that disk.
  The integer disks exhaust the plane.
-/
theorem integrableBeurlingLimit_congr_ae
    {f g : ℂ → ℂ} (hf : Integrable f volume) (hg : Integrable g volume)
    (hfg : f =ᵐ[volume] g) :
    integrableBeurlingLimit f hf =ᵐ[volume]
      integrableBeurlingLimit g hg := by
  have hzero :=
    integrableBeurlingApproximation_sub_tendstoInMeasure_zero_of_ae_eq
      hf hg hfg
  have hpiece : ∀ n : ℕ,
      integrableBeurlingLimit f hf =ᵐ[volume.restrict
        (Metric.closedBall (0 : ℂ) (n : ℝ))]
        integrableBeurlingLimit g hg := by
    intro n
    have hf_local :=
      integrableBeurlingApproximation_tendstoInMeasure_restrict_closedBall
        f hf n
    have hg_local :=
      integrableBeurlingApproximation_tendstoInMeasure_restrict_closedBall
        g hg n
    have hlimit_sub := tendstoInMeasure_sub hf_local hg_local
    have hzero_local := JJMath.tendstoInMeasure_mono_measure
      (ν := volume.restrict (Metric.closedBall (0 : ℂ) (n : ℝ)))
      Measure.restrict_le_self hzero
    have hsub_zero := tendstoInMeasure_ae_unique hlimit_sub hzero_local
    filter_upwards [hsub_zero] with z hz
    exact sub_eq_zero.mp hz
  have hglobal : integrableBeurlingLimit f hf =ᵐ[volume.restrict
      (⋃ n : ℕ, Metric.closedBall (0 : ℂ) n)]
      integrableBeurlingLimit g hg :=
    (ae_eq_restrict_iUnion_iff
      (fun n : ℕ ↦ Metric.closedBall (0 : ℂ) n)
      (integrableBeurlingLimit f hf)
      (integrableBeurlingLimit g hg)).2 hpiece
  simpa [Metric.iUnion_closedBall_nat, Measure.restrict_univ] using hglobal

/--
%%handwave
name:
  Canonical simple approximation is asymptotically additive in $L^1$
statement:
  Let $f,g\in L^1(\mathbb C)$, and write $f_n$, $g_n$, and $h_n$ for the
  canonical simple approximants of $f$, $g$, and $f+g$, respectively. Then
  $$
    \|h_n-(f_n+g_n)\|_1\longrightarrow0.
  $$
proof:
  Insert $f+g$ and use the triangle inequality to bound the left-hand side
  by
  $\|h_n-(f+g)\|_1+\|f_n-f\|_1+\|g_n-g\|_1$. Each term tends to zero by
  $L^1$ convergence of the canonical approximants.
-/
theorem eLpNorm_one_integrableSimpleApproximation_add_sub_tendsto_zero
    (f g : ℂ → ℂ) (hf : Integrable f volume) (hg : Integrable g volume) :
    Tendsto
      (fun n ↦ eLpNorm
        ((integrableSimpleApproximation (f + g) (hf.add hg) n : ℂ → ℂ) -
          ((integrableSimpleApproximation f hf n : ℂ → ℂ) +
            (integrableSimpleApproximation g hg n : ℂ → ℂ))) 1 volume)
      atTop (𝓝 0) := by
  have hfg_zero :=
    eLpNorm_one_integrableSimpleApproximation_sub_tendsto_zero
      (f + g) (hf.add hg)
  have hf_zero :=
    eLpNorm_one_integrableSimpleApproximation_sub_tendsto_zero f hf
  have hg_zero :=
    eLpNorm_one_integrableSimpleApproximation_sub_tendsto_zero g hg
  have hupper : Tendsto
      (fun n ↦
        eLpNorm
          ((integrableSimpleApproximation (f + g) (hf.add hg) n : ℂ → ℂ) -
            (f + g)) 1 volume +
          (eLpNorm
            ((integrableSimpleApproximation f hf n : ℂ → ℂ) - f) 1 volume +
          eLpNorm
            ((integrableSimpleApproximation g hg n : ℂ → ℂ) - g) 1 volume))
      atTop (𝓝 0) := by
    simpa using hfg_zero.add (hf_zero.add hg_zero)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    hupper (fun _ ↦ zero_le) (fun n ↦ ?_)
  have heq :
      (integrableSimpleApproximation (f + g) (hf.add hg) n : ℂ → ℂ) -
          ((integrableSimpleApproximation f hf n : ℂ → ℂ) +
            (integrableSimpleApproximation g hg n : ℂ → ℂ)) =
        ((integrableSimpleApproximation (f + g) (hf.add hg) n : ℂ → ℂ) -
          (f + g)) -
        (((integrableSimpleApproximation f hf n : ℂ → ℂ) - f) +
          ((integrableSimpleApproximation g hg n : ℂ → ℂ) - g)) := by
    funext z
    simp only [Pi.sub_apply, Pi.add_apply]
    abel
  rw [heq]
  refine (eLpNorm_sub_le
    ((integrable_integrableSimpleApproximation (f + g) (hf.add hg) n).1.sub
      (hf.add hg).1)
    (((integrable_integrableSimpleApproximation f hf n).1.sub hf.1).add
      ((integrable_integrableSimpleApproximation g hg n).1.sub hg.1))
    (by norm_num : (1 : ENNReal) ≤ 1)).trans ?_
  exact add_le_add_right
    (eLpNorm_add_le
      ((integrable_integrableSimpleApproximation f hf n).1.sub hf.1)
      ((integrable_integrableSimpleApproximation g hg n).1.sub hg.1)
      (by norm_num : (1 : ENNReal) ≤ 1)) _

/--
%%handwave
name:
  Transformed canonical approximants are asymptotically additive
statement:
  Let $f,g\in L^1(\mathbb C)$. If $f_n$, $g_n$, and $h_n$ are the canonical
  simple approximants of $f$, $g$, and $f+g$, then
  $$
    \mathcal S h_n-(\mathcal S f_n+\mathcal S g_n)\longrightarrow0
  $$
  in measure on $\mathbb C$.
proof:
  The inputs $h_n-(f_n+g_n)$ lie in $L^1\cap L^2$ and tend to zero in
  $L^1$. Apply [restricted continuity of the Beurling transform in measure](lean:JJMath.Quasiconformal.beurlingTransformL2_tendstoInMeasure_zero_of_eLpNorm_one_tendsto_zero), then use additivity of the $L^2$ transform.
-/
theorem integrableBeurlingApproximation_add_sub_tendstoInMeasure_zero
    (f g : ℂ → ℂ) (hf : Integrable f volume) (hg : Integrable g volume) :
    TendstoInMeasure volume
      (fun n ↦ integrableBeurlingApproximation (f + g) (hf.add hg) n -
        (integrableBeurlingApproximation f hf n +
          integrableBeurlingApproximation g hg n)) atTop 0 := by
  let d : ℕ → ℂ → ℂ := fun n ↦
    (integrableSimpleApproximation (f + g) (hf.add hg) n : ℂ → ℂ) -
      ((integrableSimpleApproximation f hf n : ℂ → ℂ) +
        (integrableSimpleApproximation g hg n : ℂ → ℂ))
  let hd₂ : ∀ n, MemLp (d n) 2 volume := fun n ↦
    (memLp_two_integrableSimpleApproximation (f + g) (hf.add hg) n).sub
      ((memLp_two_integrableSimpleApproximation f hf n).add
        (memLp_two_integrableSimpleApproximation g hg n))
  have hzero :=
    beurlingTransformL2_tendstoInMeasure_zero_of_eLpNorm_one_tendsto_zero
      (f := d)
      (fun n ↦
        (integrable_integrableSimpleApproximation (f + g) (hf.add hg) n).sub
          ((integrable_integrableSimpleApproximation f hf n).add
            (integrable_integrableSimpleApproximation g hg n)))
      hd₂
      (eLpNorm_one_integrableSimpleApproximation_add_sub_tendsto_zero
        f g hf hg)
  apply hzero.congr_left
  intro n
  have hLp : (hd₂ n).toLp (d n) =
      (memLp_two_integrableSimpleApproximation (f + g) (hf.add hg) n).toLp
          (integrableSimpleApproximation (f + g) (hf.add hg) n) -
        ((memLp_two_integrableSimpleApproximation f hf n).toLp
            (integrableSimpleApproximation f hf n) +
          (memLp_two_integrableSimpleApproximation g hg n).toLp
            (integrableSimpleApproximation g hg n)) := by
    rfl
  rw [hLp, map_sub, map_add]
  filter_upwards [Lp.coeFn_sub
    (beurlingTransformL2
      ((memLp_two_integrableSimpleApproximation (f + g) (hf.add hg) n).toLp
        (integrableSimpleApproximation (f + g) (hf.add hg) n)))
    (beurlingTransformL2
      ((memLp_two_integrableSimpleApproximation f hf n).toLp
        (integrableSimpleApproximation f hf n)) +
      beurlingTransformL2
        ((memLp_two_integrableSimpleApproximation g hg n).toLp
          (integrableSimpleApproximation g hg n))),
    Lp.coeFn_add
      (beurlingTransformL2
        ((memLp_two_integrableSimpleApproximation f hf n).toLp
          (integrableSimpleApproximation f hf n)))
      (beurlingTransformL2
        ((memLp_two_integrableSimpleApproximation g hg n).toLp
          (integrableSimpleApproximation g hg n)))] with z hsub hadd
  exact hsub.trans (congrArg
    (fun w ↦ integrableBeurlingApproximation (f + g) (hf.add hg) n z - w)
    hadd)

/--
%%handwave
name:
  Additivity of the canonical Beurling limit
statement:
  For $f,g\in L^1(\mathbb C)$, the canonical limits satisfy
  $$
    G_{f+g}=G_f+G_g
    \quad\text{almost everywhere on }\mathbb C.
  $$
proof:
  On each closed integer-radius disk, the three transformed approximation
  sequences converge in measure to their canonical limits. Their failure of
  additivity tends to zero in measure, so uniqueness of limits in measure
  gives the identity on that disk. The integer disks exhaust the plane.
-/
theorem integrableBeurlingLimit_add
    (f g : ℂ → ℂ) (hf : Integrable f volume) (hg : Integrable g volume) :
    integrableBeurlingLimit (f + g) (hf.add hg) =ᵐ[volume]
      integrableBeurlingLimit f hf + integrableBeurlingLimit g hg := by
  have hzero :=
    integrableBeurlingApproximation_add_sub_tendstoInMeasure_zero f g hf hg
  have hpiece : ∀ n : ℕ,
      integrableBeurlingLimit (f + g) (hf.add hg) =ᵐ[volume.restrict
        (Metric.closedBall (0 : ℂ) (n : ℝ))]
        integrableBeurlingLimit f hf + integrableBeurlingLimit g hg := by
    intro n
    have hfg_local :=
      integrableBeurlingApproximation_tendstoInMeasure_restrict_closedBall
        (f + g) (hf.add hg) n
    have hsum_local := tendstoInMeasure_add
      (integrableBeurlingApproximation_tendstoInMeasure_restrict_closedBall
        f hf n)
      (integrableBeurlingApproximation_tendstoInMeasure_restrict_closedBall
        g hg n)
    have hlimit_sub := tendstoInMeasure_sub hfg_local hsum_local
    have hzero_local := JJMath.tendstoInMeasure_mono_measure
      (ν := volume.restrict (Metric.closedBall (0 : ℂ) (n : ℝ)))
      Measure.restrict_le_self hzero
    have hsub_zero := tendstoInMeasure_ae_unique hlimit_sub hzero_local
    filter_upwards [hsub_zero] with z hz
    exact sub_eq_zero.mp hz
  have hglobal : integrableBeurlingLimit (f + g) (hf.add hg) =ᵐ[
      volume.restrict (⋃ n : ℕ, Metric.closedBall (0 : ℂ) n)]
      integrableBeurlingLimit f hf + integrableBeurlingLimit g hg :=
    (ae_eq_restrict_iUnion_iff
      (fun n : ℕ ↦ Metric.closedBall (0 : ℂ) n)
      (integrableBeurlingLimit (f + g) (hf.add hg))
      (integrableBeurlingLimit f hf + integrableBeurlingLimit g hg)).2 hpiece
  simpa [Metric.iUnion_closedBall_nat, Measure.restrict_univ] using hglobal

/--
%%handwave
name:
  Integrability is preserved by complex scalar multiplication
statement:
  If $f\in L^1(\mathbb C)$ and $c\in\mathbb C$, then $cf$ is integrable.
proof:
  Pointwise multiplication by $c$ multiplies the norm of $f$ by the finite
  constant $|c|$.
-/
theorem integrable_const_smul_complex
    (c : ℂ) (f : ℂ → ℂ) (hf : Integrable f volume) :
    Integrable (c • f) volume := by
  simpa only [Pi.smul_apply, smul_eq_mul] using hf.const_mul c

/--
%%handwave
name:
  Canonical simple approximation is asymptotically homogeneous in $L^1$
statement:
  Let $f\in L^1(\mathbb C)$ and $c\in\mathbb C$. If $f_n$ and $h_n$ are
  the canonical simple approximants of $f$ and $cf$, respectively, then
  $$
    \|h_n-cf_n\|_1\longrightarrow0.
  $$
proof:
  Insert $cf$ and use the triangle inequality to bound the left-hand side by
  $\|h_n-cf\|_1+|c|\,\|f_n-f\|_1$. Both terms tend to zero by $L^1$
  convergence of the canonical approximants.
-/
theorem eLpNorm_one_integrableSimpleApproximation_const_smul_sub_tendsto_zero
    (c : ℂ) (f : ℂ → ℂ) (hf : Integrable f volume) :
    Tendsto
      (fun n ↦ eLpNorm
        ((integrableSimpleApproximation (c • f)
            (integrable_const_smul_complex c f hf) n :
            ℂ → ℂ) -
          c • (integrableSimpleApproximation f hf n : ℂ → ℂ)) 1 volume)
      atTop (𝓝 0) := by
  have hcf_zero :=
    eLpNorm_one_integrableSimpleApproximation_sub_tendsto_zero
      (c • f) (integrable_const_smul_complex c f hf)
  have hf_zero :=
    eLpNorm_one_integrableSimpleApproximation_sub_tendsto_zero f hf
  have hc_zero : Tendsto
      (fun n ↦ ‖c‖ₑ * eLpNorm
        ((integrableSimpleApproximation f hf n : ℂ → ℂ) - f) 1 volume)
      atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hf_zero (a := ‖c‖ₑ)
      (Or.inr (by finiteness))
  have hupper : Tendsto
      (fun n ↦
        eLpNorm
          ((integrableSimpleApproximation (c • f)
              (integrable_const_smul_complex c f hf) n :
              ℂ → ℂ) - c • f) 1 volume +
        ‖c‖ₑ * eLpNorm
          ((integrableSimpleApproximation f hf n : ℂ → ℂ) - f) 1 volume)
      atTop (𝓝 0) := by
    simpa using hcf_zero.add hc_zero
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    hupper (fun _ ↦ zero_le) (fun n ↦ ?_)
  have heq :
      (integrableSimpleApproximation (c • f)
          (integrable_const_smul_complex c f hf) n : ℂ → ℂ) -
          c • (integrableSimpleApproximation f hf n : ℂ → ℂ) =
        ((integrableSimpleApproximation (c • f)
            (integrable_const_smul_complex c f hf) n :
            ℂ → ℂ) - c • f) -
          c • ((integrableSimpleApproximation f hf n : ℂ → ℂ) - f) := by
    funext z
    simp only [Pi.sub_apply, Pi.smul_apply]
    module
  rw [heq]
  refine (eLpNorm_sub_le
    ((integrable_integrableSimpleApproximation (c • f)
      (integrable_const_smul_complex c f hf) n).1.sub
      (integrable_const_smul_complex c f hf).1)
    (((integrable_integrableSimpleApproximation f hf n).1.sub hf.1).const_smul c)
    (by norm_num : (1 : ENNReal) ≤ 1)).trans ?_
  rw [eLpNorm_const_smul]

/--
%%handwave
name:
  Transformed canonical approximants are asymptotically homogeneous
statement:
  Let $f\in L^1(\mathbb C)$ and $c\in\mathbb C$. If $f_n$ and $h_n$ are
  the canonical simple approximants of $f$ and $cf$, then
  $$
    \mathcal S h_n-c\,\mathcal S f_n\longrightarrow0
  $$
  in measure on $\mathbb C$.
proof:
  The inputs $h_n-cf_n$ lie in $L^1\cap L^2$ and tend to zero in $L^1$.
  Apply [restricted continuity of the Beurling transform in measure](lean:JJMath.Quasiconformal.beurlingTransformL2_tendstoInMeasure_zero_of_eLpNorm_one_tendsto_zero), then use complex homogeneity of the $L^2$ transform.
-/
theorem integrableBeurlingApproximation_const_smul_sub_tendstoInMeasure_zero
    (c : ℂ) (f : ℂ → ℂ) (hf : Integrable f volume) :
    TendstoInMeasure volume
      (fun n ↦ integrableBeurlingApproximation (c • f)
        (integrable_const_smul_complex c f hf) n -
        c • integrableBeurlingApproximation f hf n) atTop 0 := by
  let d : ℕ → ℂ → ℂ := fun n ↦
    (integrableSimpleApproximation (c • f)
      (integrable_const_smul_complex c f hf) n : ℂ → ℂ) -
      c • (integrableSimpleApproximation f hf n : ℂ → ℂ)
  let hd₂ : ∀ n, MemLp (d n) 2 volume := fun n ↦
    (memLp_two_integrableSimpleApproximation (c • f)
      (integrable_const_smul_complex c f hf) n).sub
      ((memLp_two_integrableSimpleApproximation f hf n).const_smul c)
  have hzero :=
    beurlingTransformL2_tendstoInMeasure_zero_of_eLpNorm_one_tendsto_zero
      (f := d)
      (fun n ↦
        (integrable_integrableSimpleApproximation
          (c • f) (integrable_const_smul_complex c f hf) n).sub
          (integrable_const_smul_complex c
            (integrableSimpleApproximation f hf n : ℂ → ℂ)
            (integrable_integrableSimpleApproximation f hf n)))
      hd₂
      (eLpNorm_one_integrableSimpleApproximation_const_smul_sub_tendsto_zero
        c f hf)
  apply hzero.congr_left
  intro n
  have hLp : (hd₂ n).toLp (d n) =
      (memLp_two_integrableSimpleApproximation (c • f)
        (integrable_const_smul_complex c f hf) n).toLp
          (integrableSimpleApproximation (c • f)
            (integrable_const_smul_complex c f hf) n) -
        c • (memLp_two_integrableSimpleApproximation f hf n).toLp
          (integrableSimpleApproximation f hf n) := by
    rfl
  rw [hLp, map_sub, map_smul]
  filter_upwards [Lp.coeFn_sub
    (beurlingTransformL2
      ((memLp_two_integrableSimpleApproximation (c • f)
        (integrable_const_smul_complex c f hf) n).toLp
        (integrableSimpleApproximation (c • f)
          (integrable_const_smul_complex c f hf) n)))
    (c • beurlingTransformL2
      ((memLp_two_integrableSimpleApproximation f hf n).toLp
        (integrableSimpleApproximation f hf n))),
    Lp.coeFn_smul c
      (beurlingTransformL2
        ((memLp_two_integrableSimpleApproximation f hf n).toLp
          (integrableSimpleApproximation f hf n)))] with z hsub hsmul
  exact hsub.trans (congrArg
    (fun w ↦ integrableBeurlingApproximation (c • f)
      (integrable_const_smul_complex c f hf) n z - w)
    hsmul)

/--
%%handwave
name:
  Complex homogeneity of the canonical Beurling limit
statement:
  For $f\in L^1(\mathbb C)$ and $c\in\mathbb C$, the canonical limits
  satisfy
  $$
    G_{cf}=cG_f
    \quad\text{almost everywhere on }\mathbb C.
  $$
proof:
  On each closed integer-radius disk, the transformed approximation of $cf$
  converges in measure to $G_{cf}$, while $c$ times the transformed
  approximation of $f$ converges in measure to $cG_f$. Their difference
  tends to zero in measure, so uniqueness gives the identity on each disk.
  The integer disks exhaust the plane.
-/
theorem integrableBeurlingLimit_const_smul
    (c : ℂ) (f : ℂ → ℂ) (hf : Integrable f volume) :
    integrableBeurlingLimit (c • f)
      (integrable_const_smul_complex c f hf) =ᵐ[volume]
      c • integrableBeurlingLimit f hf := by
  have hzero :=
    integrableBeurlingApproximation_const_smul_sub_tendstoInMeasure_zero
      c f hf
  have hpiece : ∀ n : ℕ,
      integrableBeurlingLimit (c • f)
        (integrable_const_smul_complex c f hf) =ᵐ[volume.restrict
        (Metric.closedBall (0 : ℂ) (n : ℝ))]
        c • integrableBeurlingLimit f hf := by
    intro n
    have hcf_local :=
      integrableBeurlingApproximation_tendstoInMeasure_restrict_closedBall
        (c • f) (integrable_const_smul_complex c f hf) n
    have hsmul_local := tendstoInMeasure_const_smul c
      (integrableBeurlingApproximation_tendstoInMeasure_restrict_closedBall
        f hf n)
    have hlimit_sub := tendstoInMeasure_sub hcf_local hsmul_local
    have hzero_local := JJMath.tendstoInMeasure_mono_measure
      (ν := volume.restrict (Metric.closedBall (0 : ℂ) (n : ℝ)))
      Measure.restrict_le_self hzero
    have hsub_zero := tendstoInMeasure_ae_unique hlimit_sub hzero_local
    filter_upwards [hsub_zero] with z hz
    exact sub_eq_zero.mp hz
  have hglobal : integrableBeurlingLimit (c • f)
      (integrable_const_smul_complex c f hf) =ᵐ[
      volume.restrict (⋃ n : ℕ, Metric.closedBall (0 : ℂ) n)]
      c • integrableBeurlingLimit f hf :=
    (ae_eq_restrict_iUnion_iff
      (fun n : ℕ ↦ Metric.closedBall (0 : ℂ) n)
      (integrableBeurlingLimit (c • f)
        (integrable_const_smul_complex c f hf))
      (c • integrableBeurlingLimit f hf)).2 hpiece
  simpa [Metric.iUnion_closedBall_nat, Measure.restrict_univ] using hglobal

/--
%%handwave
name:
  Weak-$L^1$ Beurling transform
statement:
  The Beurling transform of an $L^1(\mathbb C)$ class is the
  almost-everywhere class of the canonical measurable limit of the Beurling
  transforms of its simple approximants. The value is a measurable function
  modulo almost-everywhere equality; it need not itself belong to $L^1$.
-/
def beurlingTransformL1
    (f : ℂ →₁[volume] ℂ) : ℂ →ₘ[volume] ℂ :=
  AEEqFun.mk
    (integrableBeurlingLimit (f : ℂ → ℂ) (L1.integrable_coeFn f))
    (aestronglyMeasurable_integrableBeurlingLimit
      (f : ℂ → ℂ) (L1.integrable_coeFn f))

/--
%%handwave
name:
  Function representative of the weak-$L^1$ Beurling transform
statement:
  For $f\in L^1(\mathbb C)$, the function representative of its weak-$L^1$
  Beurling transform agrees almost everywhere with the canonical measurable
  limit $G_f$.
proof:
  This is the defining representative of the almost-everywhere class.
-/
theorem beurlingTransformL1_coeFn
    (f : ℂ →₁[volume] ℂ) :
    (beurlingTransformL1 f : ℂ → ℂ) =ᵐ[volume]
      integrableBeurlingLimit (f : ℂ → ℂ) (L1.integrable_coeFn f) := by
  exact AEEqFun.coeFn_mk _ _

/--
%%handwave
name:
  Additivity of the weak-$L^1$ Beurling transform
statement:
  For all $F,G\in L^1(\mathbb C)$,
  $$
    \mathcal S(F+G)=\mathcal SF+\mathcal SG
  $$
  as measurable functions modulo almost-everywhere equality.
proof:
  Choose the function representatives of the two $L^1$ classes. The
  representative of their sum agrees almost everywhere with the pointwise
  sum, canonical limits depend only on almost-everywhere classes, and
  [canonical limits are additive](lean:JJMath.Quasiconformal.integrableBeurlingLimit_add).
-/
theorem beurlingTransformL1_add
    (F G : ℂ →₁[volume] ℂ) :
    beurlingTransformL1 (F + G) =
      beurlingTransformL1 F + beurlingTransformL1 G := by
  apply AEEqFun.ext
  have hlimit_congr := integrableBeurlingLimit_congr_ae
    (L1.integrable_coeFn (F + G))
    ((L1.integrable_coeFn F).add (L1.integrable_coeFn G))
    (Lp.coeFn_add F G)
  filter_upwards [beurlingTransformL1_coeFn (F + G),
    beurlingTransformL1_coeFn F, beurlingTransformL1_coeFn G,
    AEEqFun.coeFn_add (beurlingTransformL1 F) (beurlingTransformL1 G),
    hlimit_congr,
    integrableBeurlingLimit_add (F : ℂ → ℂ) (G : ℂ → ℂ)
      (L1.integrable_coeFn F) (L1.integrable_coeFn G)]
    with z hsum hF hG hcoe hcongr hadd
  calc
    (beurlingTransformL1 (F + G) : ℂ → ℂ) z =
        integrableBeurlingLimit ((F + G : ℂ →₁[volume] ℂ) : ℂ → ℂ)
          (L1.integrable_coeFn (F + G)) z := hsum
    _ = integrableBeurlingLimit ((F : ℂ → ℂ) + (G : ℂ → ℂ))
          ((L1.integrable_coeFn F).add (L1.integrable_coeFn G)) z := hcongr
    _ = integrableBeurlingLimit (F : ℂ → ℂ) (L1.integrable_coeFn F) z +
          integrableBeurlingLimit (G : ℂ → ℂ) (L1.integrable_coeFn G) z := hadd
    _ = (beurlingTransformL1 F : ℂ → ℂ) z +
          (beurlingTransformL1 G : ℂ → ℂ) z := congrArg₂ (· + ·) hF.symm hG.symm
    _ = (beurlingTransformL1 F + beurlingTransformL1 G :
          ℂ →ₘ[volume] ℂ) z := hcoe.symm

/--
%%handwave
name:
  Complex homogeneity of the weak-$L^1$ Beurling transform
statement:
  For every $F\in L^1(\mathbb C)$ and $c\in\mathbb C$,
  $$
    \mathcal S(cF)=c\,\mathcal SF
  $$
  as measurable functions modulo almost-everywhere equality.
proof:
  The function representative of $cF$ agrees almost everywhere with $c$
  times the representative of $F$. Canonical limits depend only on that
  class, and [canonical limits are complex homogeneous](lean:JJMath.Quasiconformal.integrableBeurlingLimit_const_smul).
-/
theorem beurlingTransformL1_smul
    (c : ℂ) (F : ℂ →₁[volume] ℂ) :
    beurlingTransformL1 (c • F) = c • beurlingTransformL1 F := by
  apply AEEqFun.ext
  have hlimit_congr := integrableBeurlingLimit_congr_ae
    (L1.integrable_coeFn (c • F))
    (integrable_const_smul_complex c (F : ℂ → ℂ) (L1.integrable_coeFn F))
    (Lp.coeFn_smul c F)
  filter_upwards [beurlingTransformL1_coeFn (c • F),
    beurlingTransformL1_coeFn F,
    AEEqFun.coeFn_smul c (beurlingTransformL1 F),
    hlimit_congr,
    integrableBeurlingLimit_const_smul c (F : ℂ → ℂ)
      (L1.integrable_coeFn F)] with z hscaled hF hcoe hcongr hsmul
  calc
    (beurlingTransformL1 (c • F) : ℂ → ℂ) z =
        integrableBeurlingLimit ((c • F : ℂ →₁[volume] ℂ) : ℂ → ℂ)
          (L1.integrable_coeFn (c • F)) z := hscaled
    _ = integrableBeurlingLimit (c • (F : ℂ → ℂ))
          (integrable_const_smul_complex c (F : ℂ → ℂ)
            (L1.integrable_coeFn F)) z := hcongr
    _ = (c • integrableBeurlingLimit (F : ℂ → ℂ)
          (L1.integrable_coeFn F)) z := hsmul
    _ = (c • (beurlingTransformL1 F : ℂ → ℂ)) z := by
      simp only [Pi.smul_apply, hF]
    _ = (c • beurlingTransformL1 F : ℂ →ₘ[volume] ℂ) z := hcoe.symm

/--
%%handwave
name:
  Weak $(1,1)$ estimate for the canonical Beurling limit
statement:
  If $f\in L^1(\mathbb C)$ and $0<t<\infty$, then its canonical Beurling
  limit satisfies
  $$
    t\,\bigl|\{z:t\leq|G_f(z)|\}\bigr|
      \leq(40+16\pi)\int_{\mathbb C}|f(z)|\,dz.
  $$
proof:
  Along a strictly increasing subsequence, the transformed canonical simple
  approximants converge almost everywhere to $G_f$. Their $L^1$ masses
  converge to that of $f$, and each transformed approximant obeys the
  restricted weak estimate. Apply [stability of weak distribution bounds under almost-everywhere limits](lean:JJMath.HarmonicAnalysis.weak_distribution_bound_of_tendsto_ae).
-/
theorem integrableBeurlingLimit_distribution_le
    (f : ℂ → ℂ) (hf : Integrable f volume)
    {t : ENNReal} (ht0 : t ≠ 0) (httop : t ≠ ∞) :
    t * HarmonicAnalysis.distributionFunction
        (integrableBeurlingLimit f hf) volume t ≤
      ENNReal.ofReal (40 + 16 * Real.pi) * ∫⁻ z, ‖f z‖ₑ ∂volume := by
  rcases exists_strictMono_integrableBeurlingApproximation_tendsto_ae f hf with
    ⟨ns, hns, hlim⟩
  refine HarmonicAnalysis.weak_distribution_bound_of_tendsto_ae
    (F := fun k ↦ integrableBeurlingApproximation f hf (ns k))
    (mass := fun k ↦ ∫⁻ z,
      ‖(integrableSimpleApproximation f hf (ns k) : ℂ → ℂ) z‖ₑ ∂volume)
    ENNReal.ofReal_ne_top hlim ?_ ?_ ht0 httop
  · exact (lintegral_enorm_integrableSimpleApproximation_tendsto f hf).comp
      hns.tendsto_atTop
  · intro k s hs0 hstop
    simpa only [integrableBeurlingApproximation] using
      beurlingTransformL2_distribution_le_lintegral_of_integrable_memLp_two
        (integrable_integrableSimpleApproximation f hf (ns k))
        (memLp_two_integrableSimpleApproximation f hf (ns k)) hs0 hstop

/--
%%handwave
name:
  Sharp inherited weak $(1,1)$ estimate for the $L^1$ Beurling transform
statement:
  If $F\in L^1(\mathbb C)$ and $0<t<\infty$, then
  $$
    t\,\bigl|\{z:t\leq|\mathcal SF(z)|\}\bigr|
      \leq(40+16\pi)\int_{\mathbb C}|F(z)|\,dz.
  $$
  Thus the extension has the same weak-type constant as the restricted
  $L^1\cap L^2$ transform.
proof:
  The function representative of the weak-$L^1$ transform agrees almost
  everywhere with the canonical limit. Distribution functions are unchanged
  by almost-everywhere equality, so apply [the canonical-limit estimate](lean:JJMath.Quasiconformal.integrableBeurlingLimit_distribution_le).
-/
theorem beurlingTransformL1_distribution_le
    (F : ℂ →₁[volume] ℂ)
    {t : ENNReal} (ht0 : t ≠ 0) (httop : t ≠ ∞) :
    t * HarmonicAnalysis.distributionFunction
        (beurlingTransformL1 F : ℂ → ℂ) volume t ≤
      ENNReal.ofReal (40 + 16 * Real.pi) *
        ∫⁻ z, ‖(F : ℂ → ℂ) z‖ₑ ∂volume := by
  have hdist : HarmonicAnalysis.distributionFunction
      (beurlingTransformL1 F : ℂ → ℂ) volume t =
      HarmonicAnalysis.distributionFunction
        (integrableBeurlingLimit (F : ℂ → ℂ) (L1.integrable_coeFn F))
        volume t := by
    simp only [HarmonicAnalysis.distributionFunction]
    apply measure_congr
    filter_upwards [beurlingTransformL1_coeFn F] with z hz
    change (t ≤ ‖(beurlingTransformL1 F : ℂ → ℂ) z‖ₑ) =
      (t ≤ ‖integrableBeurlingLimit (F : ℂ → ℂ)
        (L1.integrable_coeFn F) z‖ₑ)
    rw [hz]
  rw [hdist]
  exact integrableBeurlingLimit_distribution_le
    (F : ℂ → ℂ) (L1.integrable_coeFn F) ht0 httop

/--
%%handwave
name:
  The weak-$L^1$ extension agrees with the $L^2$ Beurling transform
statement:
  Let $f\in L^1(\mathbb C)\cap L^2(\mathbb C)$. Regard $f$ as an $L^1$
  class. Its weak-$L^1$ Beurling transform agrees almost everywhere with the
  Fourier-multiplier $L^2$ Beurling transform of $f$.
proof:
  The function representative of the $L^1$ class equals $f$ almost
  everywhere, so [the canonical limit depends only on that class](lean:JJMath.Quasiconformal.integrableBeurlingLimit_congr_ae). Then apply [compatibility of the canonical limit with the $L^2$ transform](lean:JJMath.Quasiconformal.integrableBeurlingLimit_ae_eq_beurlingTransformL2).
-/
theorem beurlingTransformL1_ae_eq_beurlingTransformL2
    (f : ℂ → ℂ) (hf₁ : Integrable f volume) (hf₂ : MemLp f 2 volume) :
    let hfL1 : MemLp f 1 volume := memLp_one_iff_integrable.mpr hf₁
    (beurlingTransformL1 (hfL1.toLp f) : ℂ → ℂ) =ᵐ[volume]
      (beurlingTransformL2 (hf₂.toLp f) : ℂ → ℂ) := by
  dsimp only
  let hfL1 : MemLp f 1 volume := memLp_one_iff_integrable.mpr hf₁
  let F : ℂ →₁[volume] ℂ := hfL1.toLp f
  have hFf : (F : ℂ → ℂ) =ᵐ[volume] f := by
    simpa only [F] using hfL1.coeFn_toLp
  exact (beurlingTransformL1_coeFn F).trans
    ((integrableBeurlingLimit_congr_ae (L1.integrable_coeFn F) hf₁ hFf).trans
      (integrableBeurlingLimit_ae_eq_beurlingTransformL2 f hf₁ hf₂))

end

end Quasiconformal

end JJMath
