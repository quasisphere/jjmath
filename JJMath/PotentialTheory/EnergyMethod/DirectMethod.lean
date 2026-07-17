import JJMath.PotentialTheory.EnergyMethod.Core

/-!
# Energy method: DirectMethod

Abstract and pure Dirichlet direct-method variational infrastructure.
-/

namespace JJMath

open MeasureTheory
open scoped Manifold Topology ENNReal ContDiff

namespace Uniformization

section PureDirichletH10DirectMethod

variable {V : Type} [NormedAddCommGroup V]

/--
%%handwave
name:
  Pure Dirichlet \(H^1_0\) energy is bounded below
statement:
  An energy functional on a pure Dirichlet \(H^1_0\) Hilbert space is bounded
  below on its finite-energy domain if it admits a real lower bound there.
-/
def IsBoundedBelowGreenSobolevH10Energy
    (energy : V → ℝ) (Finite : V → Prop) : Prop :=
  ∃ B : ℝ, ∀ u : V, Finite u → B ≤ energy u

/--
%%handwave
name:
  Pure Dirichlet \(H^1_0\) energy is coercive
statement:
  An energy functional on a pure Dirichlet \(H^1_0\) Hilbert space is
  coercive if it tends to infinity along finite-energy elements whose
  Dirichlet norm tends to infinity.
-/
def IsCoerciveGreenSobolevH10Energy
    (energy : V → ℝ) (Finite : V → Prop) : Prop :=
  ∀ A : ℝ, ∃ R : ℝ, ∀ u : V,
    Finite u → R ≤ ‖u‖ ^ (2 : ℕ) → A ≤ energy u

/--
%%handwave
name:
  Weak convergence in pure \(H^1_0\)
statement:
  A sequence in a pure \(H^1_0\) Hilbert space converges weakly when every
  continuous linear functional converges on that sequence.
-/
def WeaklyTendstoInGreenSobolevH10 [NormedSpace ℝ V]
    (H : ℕ → V) (u : V) : Prop :=
  ∀ ℓ : V →L[ℝ] ℝ,
    Filter.Tendsto (fun n : ℕ ↦ ℓ (H n)) Filter.atTop (𝓝 (ℓ u))

theorem WeaklyTendstoInGreenSobolevH10.apply [NormedSpace ℝ V]
    {H : ℕ → V} {u : V}
    (hweak : WeaklyTendstoInGreenSobolevH10 H u)
    (ℓ : V →L[ℝ] ℝ) :
    Filter.Tendsto (fun n : ℕ ↦ ℓ (H n)) Filter.atTop (𝓝 (ℓ u)) :=
  hweak ℓ

/--
%%handwave
name:
  Pure \(H^1_0\) energy is weakly lower semicontinuous
statement:
  An energy on a pure \(H^1_0\) Hilbert space is weakly lower
  semicontinuous if weak convergence and convergence of the energy values
  imply that the energy of the weak limit is no larger than the limiting
  value.
-/
def IsWeaklyLowerSemicontinuousGreenSobolevH10Energy [NormedSpace ℝ V]
    (energy : V → ℝ) : Prop :=
  ∀ (H : ℕ → V) (u : V) (a : ℝ),
    WeaklyTendstoInGreenSobolevH10 H u →
      Filter.Tendsto (fun n : ℕ ↦ energy (H n)) Filter.atTop (𝓝 a) →
        energy u ≤ a

/--
%%handwave
name:
  Pure \(H^1_0\) energy minimizer
statement:
  A finite-energy element of a pure \(H^1_0\) Hilbert space minimizes an
  energy if its energy is no larger than that of every finite-energy
  competitor.
-/
def IsGreenSobolevH10EnergyMinimizer
    (energy : V → ℝ) (Finite : V → Prop) (u : V) : Prop :=
  Finite u ∧ ∀ w : V, Finite w → energy u ≤ energy w

omit [NormedAddCommGroup V] in
theorem IsGreenSobolevH10EnergyMinimizer.finite
    {energy : V → ℝ} {Finite : V → Prop} {u : V}
    (hmin : IsGreenSobolevH10EnergyMinimizer energy Finite u) :
    Finite u :=
  hmin.1

omit [NormedAddCommGroup V] in
theorem IsGreenSobolevH10EnergyMinimizer.energy_le
    {energy : V → ℝ} {Finite : V → Prop} {u w : V}
    (hmin : IsGreenSobolevH10EnergyMinimizer energy Finite u)
    (hw : Finite w) :
    energy u ≤ energy w :=
  hmin.2 w hw

/--
%%handwave
name:
  Pure \(H^1_0\) minimizing sequence
statement:
  A minimizing sequence in a pure \(H^1_0\) Hilbert space is a finite-energy
  sequence whose energies converge to a lower bound for all finite-energy
  competitors.
-/
def HasGreenSobolevH10EnergyMinimizingSequence
    (energy : V → ℝ) (Finite : V → Prop) : Prop :=
  ∃ (H : ℕ → V) (a : ℝ),
    (∀ n : ℕ, Finite (H n)) ∧
      Filter.Tendsto (fun n : ℕ ↦ energy (H n)) Filter.atTop (𝓝 a) ∧
      ∀ w : V, Finite w → a ≤ energy w

omit [NormedAddCommGroup V] in
theorem greenSobolevH10Energy_has_minimizing_sequence_of_boundedBelow
    (energy : V → ℝ) (Finite : V → Prop)
    (hbounded : IsBoundedBelowGreenSobolevH10Energy energy Finite)
    (hnonempty : ∃ u : V, Finite u) :
    HasGreenSobolevH10EnergyMinimizingSequence energy Finite := by
  classical
  rcases hbounded with ⟨B, hB⟩
  let C : Type := {u : V // Finite u}
  haveI : Nonempty C := by
    rcases hnonempty with ⟨u, hu⟩
    exact ⟨⟨u, hu⟩⟩
  let a : ℝ := ⨅ w : C, energy w.1
  have hbdd : BddBelow (Set.range fun w : C ↦ energy w.1) := by
    refine ⟨B, ?_⟩
    rintro y ⟨w, rfl⟩
    exact hB w.1 w.2
  have ha_le : ∀ w : C, a ≤ energy w.1 := by
    intro w
    exact ciInf_le hbdd w
  have hexists : ∀ n : ℕ, ∃ w : C,
      energy w.1 < a + 1 / ((n : ℝ) + 1) := by
    intro n
    have hlt : a < a + 1 / ((n : ℝ) + 1) := by
      have hpos : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
      linarith
    exact exists_lt_of_ciInf_lt hlt
  let W : ℕ → C := fun n ↦ Classical.choose (hexists n)
  have hW_lt : ∀ n : ℕ,
      energy (W n).1 < a + 1 / ((n : ℝ) + 1) := by
    intro n
    exact Classical.choose_spec (hexists n)
  have henergy_tendsto :
      Filter.Tendsto (fun n : ℕ ↦ energy (W n).1) Filter.atTop (𝓝 a) := by
    have hlower : ∀ n : ℕ, a ≤ energy (W n).1 := fun n ↦ ha_le (W n)
    have hupper : ∀ n : ℕ, energy (W n).1 ≤ a + 1 / ((n : ℝ) + 1) :=
      fun n ↦ le_of_lt (hW_lt n)
    have hleft : Filter.Tendsto (fun _ : ℕ ↦ a) Filter.atTop (𝓝 a) :=
      tendsto_const_nhds
    have hright :
        Filter.Tendsto (fun n : ℕ ↦ a + 1 / ((n : ℝ) + 1))
          Filter.atTop (𝓝 a) := by
      have hinv :
          Filter.Tendsto (fun n : ℕ ↦ (((n : ℝ) + 1)⁻¹))
            Filter.atTop (𝓝 0) := by
        simpa [one_div] using
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      simpa [one_div] using tendsto_const_nhds.add hinv
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hleft hright
      hlower hupper
  refine ⟨fun n ↦ (W n).1, a, ?_, ?_, ?_⟩
  · intro n
    exact (W n).2
  · simpa using henergy_tendsto
  · intro w hw
    exact ha_le ⟨w, hw⟩

/--
%%handwave
name:
  Weakly convergent pure \(H^1_0\) minimizing sequence
statement:
  A minimizing sequence has a weak pure \(H^1_0\) limit at the bottom of the
  energy if the sequence converges weakly, the limit has finite energy, and
  the energy values converge to the minimizing level.
-/
def HasWeaklyConvergentGreenSobolevH10EnergyMinimizingSequence [NormedSpace ℝ V]
    (energy : V → ℝ) (Finite : V → Prop) : Prop :=
  ∃ (H : ℕ → V) (u : V) (a : ℝ),
    (∀ n : ℕ, Finite (H n)) ∧
      Finite u ∧
      WeaklyTendstoInGreenSobolevH10 H u ∧
      Filter.Tendsto (fun n : ℕ ↦ energy (H n)) Filter.atTop (𝓝 a) ∧
      ∀ w : V, Finite w → a ≤ energy w

theorem HasGreenSobolevH10EnergyMinimizingSequence.hasWeaklyConvergent
    [NormedSpace ℝ V]
    {energy : V → ℝ} {Finite : V → Prop}
    (hseq : HasGreenSobolevH10EnergyMinimizingSequence energy Finite)
    (hcompact : ∀ (H : ℕ → V) (a : ℝ),
      (∀ n : ℕ, Finite (H n)) →
        Filter.Tendsto (fun n : ℕ ↦ energy (H n)) Filter.atTop (𝓝 a) →
          (∀ w : V, Finite w → a ≤ energy w) →
            ∃ u : V, Finite u ∧ WeaklyTendstoInGreenSobolevH10 H u) :
    HasWeaklyConvergentGreenSobolevH10EnergyMinimizingSequence energy Finite := by
  rcases hseq with ⟨H, a, hH_finite, henergy, hlower⟩
  rcases hcompact H a hH_finite henergy hlower with ⟨u, hu_finite, hweak⟩
  exact ⟨H, u, a, hH_finite, hu_finite, hweak, henergy, hlower⟩

theorem greenSobolevH10Energy_has_minimizer_of_weakly_convergent_minimizing_sequence
    [NormedSpace ℝ V]
    (energy : V → ℝ) (Finite : V → Prop)
    (hlsc : IsWeaklyLowerSemicontinuousGreenSobolevH10Energy energy)
    (hcompact :
      HasWeaklyConvergentGreenSobolevH10EnergyMinimizingSequence energy Finite) :
    ∃ u : V, IsGreenSobolevH10EnergyMinimizer energy Finite u := by
  rcases hcompact with ⟨H, u, a, _hH_finite, hu_finite, hweak, henergy, hlower⟩
  refine ⟨u, hu_finite, ?_⟩
  intro w hw
  exact (hlsc H u a hweak henergy).trans (hlower w hw)

/--
%%handwave
name:
  Coercivity bounds pure \(H^1_0\) minimizing sequences
statement:
  If a pure \(H^1_0\) energy is coercive, then every finite-energy
  minimizing sequence whose energies converge to a finite level is
  eventually bounded in the pure Dirichlet norm.
-/
theorem greenSobolevH10Energy_minimizing_sequence_eventually_normSq_le_of_coercive
    (energy : V → ℝ) (Finite : V → Prop)
    (hcoercive : IsCoerciveGreenSobolevH10Energy energy Finite)
    {H : ℕ → V} {a : ℝ}
    (hH_finite : ∀ n : ℕ, Finite (H n))
    (henergy : Filter.Tendsto (fun n : ℕ ↦ energy (H n)) Filter.atTop (𝓝 a)) :
    ∃ R : ℝ, ∀ᶠ n in Filter.atTop, ‖H n‖ ^ (2 : ℕ) ≤ R := by
  rcases hcoercive (a + 1) with ⟨R, hR⟩
  refine ⟨R, ?_⟩
  have hlt_eventually : ∀ᶠ n in Filter.atTop, energy (H n) < a + 1 :=
    henergy.eventually (eventually_lt_nhds (by linarith))
  filter_upwards [hlt_eventually] with n hn_lt
  by_contra hnot
  have hR_le : R ≤ ‖H n‖ ^ (2 : ℕ) := le_of_not_ge hnot
  have hlarge : a + 1 ≤ energy (H n) :=
    hR (H n) (hH_finite n) hR_le
  linarith

/--
%%handwave
name:
  Weak compactness for bounded pure \(H^1_0\) minimizing sequences
statement:
  The compactness input needed by the pure \(H^1_0\) direct method is that
  every finite-energy minimizing sequence that is eventually bounded in the
  pure Dirichlet norm admits a finite-energy weak limit.
-/
def HasWeakCompactnessForEventuallyBoundedGreenSobolevH10MinimizingSequences
    [NormedSpace ℝ V]
    (energy : V → ℝ) (Finite : V → Prop) : Prop :=
  ∀ (H : ℕ → V) (a : ℝ),
    (∀ n : ℕ, Finite (H n)) →
      Filter.Tendsto (fun n : ℕ ↦ energy (H n)) Filter.atTop (𝓝 a) →
        (∀ w : V, Finite w → a ≤ energy w) →
          (∃ R : ℝ, ∀ᶠ n in Filter.atTop, ‖H n‖ ^ (2 : ℕ) ≤ R) →
            ∃ u : V, Finite u ∧ WeaklyTendstoInGreenSobolevH10 H u

theorem greenSobolevH10Energy_has_minimizer_of_boundedBelow_and_weak_compactness
    [NormedSpace ℝ V]
    (energy : V → ℝ) (Finite : V → Prop)
    (hbounded : IsBoundedBelowGreenSobolevH10Energy energy Finite)
    (hnonempty : ∃ u : V, Finite u)
    (hlsc : IsWeaklyLowerSemicontinuousGreenSobolevH10Energy energy)
    (hcompact : ∀ (H : ℕ → V) (a : ℝ),
      (∀ n : ℕ, Finite (H n)) →
        Filter.Tendsto (fun n : ℕ ↦ energy (H n)) Filter.atTop (𝓝 a) →
          (∀ w : V, Finite w → a ≤ energy w) →
            ∃ u : V, Finite u ∧ WeaklyTendstoInGreenSobolevH10 H u) :
    ∃ u : V, IsGreenSobolevH10EnergyMinimizer energy Finite u := by
  have hseq : HasGreenSobolevH10EnergyMinimizingSequence energy Finite :=
    greenSobolevH10Energy_has_minimizing_sequence_of_boundedBelow
      energy Finite hbounded hnonempty
  exact greenSobolevH10Energy_has_minimizer_of_weakly_convergent_minimizing_sequence
    energy Finite hlsc (hseq.hasWeaklyConvergent hcompact)

theorem greenSobolevH10Energy_has_minimizer_of_boundedBelow_coercive_lsc_and_weak_compactness
    [NormedSpace ℝ V]
    (energy : V → ℝ) (Finite : V → Prop)
    (hbounded : IsBoundedBelowGreenSobolevH10Energy energy Finite)
    (hnonempty : ∃ u : V, Finite u)
    (hcoercive : IsCoerciveGreenSobolevH10Energy energy Finite)
    (hlsc : IsWeaklyLowerSemicontinuousGreenSobolevH10Energy energy)
    (hcompact :
      HasWeakCompactnessForEventuallyBoundedGreenSobolevH10MinimizingSequences
        energy Finite) :
    ∃ u : V, IsGreenSobolevH10EnergyMinimizer energy Finite u := by
  refine greenSobolevH10Energy_has_minimizer_of_boundedBelow_and_weak_compactness
    energy Finite hbounded hnonempty hlsc ?_
  intro H a hH_finite henergy hlower
  exact hcompact H a hH_finite henergy hlower
    (greenSobolevH10Energy_minimizing_sequence_eventually_normSq_le_of_coercive
      energy Finite hcoercive hH_finite henergy)

/--
%%handwave
name:
  Weak limits have no larger norm than the limiting norm
statement:
  If a sequence in a real Hilbert space converges weakly to \(u\) and its
  squared norms converge to \(b\), then \(\|u\|^2\le b\).
proof:
  Use the inequality
  \(2\langle u,u_n\rangle-\|u\|^2\le \|u_n\|^2\), obtained by expanding
  \(\|u_n-u\|^2\ge0\), and pass to the limit.
-/
theorem weaklyTendstoInGreenSobolevH10_normSq_le_of_tendsto_normSq
    [InnerProductSpace ℝ V]
    {H : ℕ → V} {u : V} {b : ℝ}
    (hweak : WeaklyTendstoInGreenSobolevH10 H u)
    (hnorm : Filter.Tendsto (fun n : ℕ ↦ ‖H n‖ ^ (2 : ℕ)) Filter.atTop (𝓝 b)) :
    ‖u‖ ^ (2 : ℕ) ≤ b := by
  have hinner : Filter.Tendsto (fun n : ℕ ↦ innerSL ℝ u (H n))
      Filter.atTop (𝓝 (innerSL ℝ u u)) :=
    hweak (innerSL ℝ u)
  have hleft :
      Filter.Tendsto
        (fun n : ℕ ↦ 2 * innerSL ℝ u (H n) - ‖u‖ ^ (2 : ℕ))
        Filter.atTop
        (𝓝 (2 * innerSL ℝ u u - ‖u‖ ^ (2 : ℕ))) :=
    (tendsto_const_nhds.mul hinner).sub tendsto_const_nhds
  have hleft_norm :
      Filter.Tendsto
        (fun n : ℕ ↦ 2 * innerSL ℝ u (H n) - ‖u‖ ^ (2 : ℕ))
        Filter.atTop (𝓝 (‖u‖ ^ (2 : ℕ))) := by
    convert hleft using 1
    rw [innerSL_apply_apply, real_inner_self_eq_norm_sq]
    ring_nf
  refine le_of_tendsto_of_tendsto' hleft_norm hnorm ?_
  intro n
  have hnonneg : 0 ≤ ‖H n - u‖ ^ (2 : ℕ) := sq_nonneg _
  rw [norm_sub_sq_real] at hnonneg
  rw [innerSL_apply_apply]
  have hcomm : inner ℝ u (H n) = inner ℝ (H n) u := real_inner_comm _ _
  nlinarith

/--
%%handwave
name:
  Quadratic-minus-linear pure energy is weakly lower semicontinuous
statement:
  On a real Hilbert space, the energy
  \(u\mapsto\frac12\|u\|^2-L(u)\) associated to a continuous linear
  functional \(L\) is weakly lower semicontinuous.
-/
theorem pureDirichletGreenSobolevH10Energy_weaklyLowerSemicontinuous
    [InnerProductSpace ℝ V]
    {energy : V → ℝ} (source : V →L[ℝ] ℝ)
    (henergy : ∀ u : V,
      energy u = (1 / 2 : ℝ) * ‖u‖ ^ (2 : ℕ) - source u) :
    IsWeaklyLowerSemicontinuousGreenSobolevH10Energy energy := by
  intro H u a hweak henergy_tendsto
  have hsource_tendsto :
      Filter.Tendsto (fun n : ℕ ↦ source (H n)) Filter.atTop (𝓝 (source u)) :=
    hweak source
  have hhalf_tendsto :
      Filter.Tendsto (fun n : ℕ ↦ (1 / 2 : ℝ) * ‖H n‖ ^ (2 : ℕ))
        Filter.atTop (𝓝 (a + source u)) := by
    have hsum := henergy_tendsto.add hsource_tendsto
    refine hsum.congr' ?_
    exact Filter.Eventually.of_forall fun n ↦ by
      change energy (H n) + source (H n) = (1 / 2 : ℝ) * ‖H n‖ ^ (2 : ℕ)
      rw [henergy (H n)]
      ring_nf
  have hnorm_tendsto :
      Filter.Tendsto (fun n : ℕ ↦ ‖H n‖ ^ (2 : ℕ))
        Filter.atTop (𝓝 (2 * (a + source u))) := by
    simpa using hhalf_tendsto.const_mul (2 : ℝ)
  have hnorm_limit :
      ‖u‖ ^ (2 : ℕ) ≤ 2 * (a + source u) :=
    weaklyTendstoInGreenSobolevH10_normSq_le_of_tendsto_normSq
      hweak hnorm_tendsto
  rw [henergy u]
  nlinarith

/--
%%handwave
name:
  Riesz representative of a pure source
statement:
  A continuous linear source functional on a real Hilbert space has a vector
  representative.
-/
noncomputable def greenSobolevH10RieszRepresentative
    [InnerProductSpace ℝ V] [CompleteSpace V]
    (source : V →L[ℝ] ℝ) : V :=
  (InnerProductSpace.toDual ℝ V).symm source

/--
%%handwave
name:
  The Riesz representative evaluates the source
statement:
  The source functional is the inner product with its Riesz representative.
-/
theorem greenSobolevH10RieszRepresentative_source_eq_inner
    [InnerProductSpace ℝ V] [CompleteSpace V]
    (source : V →L[ℝ] ℝ) (η : V) :
    source η = inner ℝ (greenSobolevH10RieszRepresentative source) η := by
  rw [greenSobolevH10RieszRepresentative]
  exact
    (InnerProductSpace.toDual_symm_apply
      (𝕜 := ℝ) (E := V) (x := η) (y := source)).symm

/--
%%handwave
name:
  Completing the square for the pure Dirichlet energy
statement:
  The quadratic-minus-linear pure Dirichlet energy equals a square centered
  at the Riesz representative, up to the constant
  \(-\frac12\|r\|^2\).
-/
theorem pureDirichletGreenSobolevH10Energy_eq_square_sub_const
    [InnerProductSpace ℝ V] [CompleteSpace V]
    (source : V →L[ℝ] ℝ) (u : V) :
    (1 / 2 : ℝ) * ‖u‖ ^ (2 : ℕ) - source u =
      (1 / 2 : ℝ) *
          ‖u - greenSobolevH10RieszRepresentative source‖ ^ (2 : ℕ) -
        (1 / 2 : ℝ) *
          ‖greenSobolevH10RieszRepresentative source‖ ^ (2 : ℕ) := by
  let r : V := greenSobolevH10RieszRepresentative source
  have hsource : source u = inner ℝ r u := by
    simpa [r] using greenSobolevH10RieszRepresentative_source_eq_inner source u
  have hcomm : inner ℝ r u = inner ℝ u r := real_inner_comm _ _
  have hsq : ‖u - r‖ ^ (2 : ℕ) =
      ‖u‖ ^ (2 : ℕ) - 2 * inner ℝ u r + ‖r‖ ^ (2 : ℕ) :=
    norm_sub_sq_real u r
  rw [hsource, hsq, hcomm]
  ring

/--
%%handwave
name:
  Riesz representative minimizes the pure Dirichlet energy
statement:
  The Riesz representative of the source functional minimizes the
  quadratic-minus-linear pure Dirichlet energy on the whole Hilbert space.
-/
theorem pureDirichletGreenSobolevH10Energy_rieszRepresentative_minimizer
    [InnerProductSpace ℝ V] [CompleteSpace V]
    {energy : V → ℝ} (source : V →L[ℝ] ℝ)
    (henergy : ∀ u : V,
      energy u = (1 / 2 : ℝ) * ‖u‖ ^ (2 : ℕ) - source u) :
    IsGreenSobolevH10EnergyMinimizer energy (fun _ : V ↦ True)
      (greenSobolevH10RieszRepresentative source) := by
  refine ⟨trivial, ?_⟩
  intro w _hw
  rw [henergy (greenSobolevH10RieszRepresentative source), henergy w]
  rw [pureDirichletGreenSobolevH10Energy_eq_square_sub_const source w]
  rw [pureDirichletGreenSobolevH10Energy_eq_square_sub_const source
    (greenSobolevH10RieszRepresentative source)]
  have hnonneg :
      0 ≤ ‖w - greenSobolevH10RieszRepresentative source‖ ^ (2 : ℕ) :=
    sq_nonneg _
  simp only [sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    mul_zero]
  nlinarith

/--
%%handwave
name:
  Continuous source gives a pure Dirichlet minimizer
statement:
  A quadratic-minus-linear pure Dirichlet energy with continuous source
  functional has a minimizer on the whole Hilbert space.
-/
theorem pureDirichletGreenSobolevH10Energy_has_minimizer_of_continuous_source
    [InnerProductSpace ℝ V] [CompleteSpace V]
    {energy : V → ℝ} (source : V →L[ℝ] ℝ)
    (henergy : ∀ u : V,
      energy u = (1 / 2 : ℝ) * ‖u‖ ^ (2 : ℕ) - source u) :
    ∃ u : V, IsGreenSobolevH10EnergyMinimizer energy (fun _ : V ↦ True) u :=
  ⟨greenSobolevH10RieszRepresentative source,
    pureDirichletGreenSobolevH10Energy_rieszRepresentative_minimizer
      source henergy⟩

/--
%%handwave
name:
  Euler equation for the pure Dirichlet Riesz minimizer
statement:
  The Riesz minimizer satisfies
  \[
    \langle u,\eta\rangle=L(\eta)
  \]
  for every test direction \(\eta\).
-/
theorem pureDirichletGreenSobolevH10Energy_rieszRepresentative_eulerLagrange
    [InnerProductSpace ℝ V] [CompleteSpace V]
    (source : V →L[ℝ] ℝ) (η : V) :
    inner ℝ (greenSobolevH10RieszRepresentative source) η = source η :=
  (greenSobolevH10RieszRepresentative_source_eq_inner source η).symm

/--
%%handwave
name:
  Pure Dirichlet quadratic energy
statement:
  A pure Dirichlet \(H^1_0\) Green energy has the form
  \[
    E(u)=\frac12\|u\|_{H^1_0}^2-L(u)
  \]
  on its finite-energy domain.
-/
def IsPureDirichletGreenSobolevH10EnergyOnFinite
    (energy source : V → ℝ) (Finite : V → Prop) : Prop :=
  ∀ u : V, Finite u →
    energy u = (1 / 2 : ℝ) * ‖u‖ ^ (2 : ℕ) - source u

/--
%%handwave
name:
  Source bounded by the pure Dirichlet norm
statement:
  The source pairing is bounded on the finite-energy domain by a constant
  times the pure Dirichlet \(H^1_0\) norm.
-/
def IsGreenSobolevH10SourceBoundedByNormOnFinite
    (source : V → ℝ) (Finite : V → Prop) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ u : V, Finite u → source u ≤ C * ‖u‖

/--
%%handwave
name:
  Bounded source gives lower bounded pure Dirichlet energy
statement:
  A pure Dirichlet quadratic energy whose source term is bounded by the
  \(H^1_0\) norm is bounded below.
proof:
  The source bound gives \(L(u)\le C\|u\|\), and Young's inequality gives
  \(C\|u\|\le \frac12\|u\|^2+\frac12C^2\).  Therefore
  \(E(u)\ge-\frac12C^2\).
-/
theorem pureDirichletGreenSobolevH10Energy_boundedBelow_of_source_bound
    {energy source : V → ℝ} {Finite : V → Prop}
    (henergy :
      IsPureDirichletGreenSobolevH10EnergyOnFinite energy source Finite)
    (hsource : IsGreenSobolevH10SourceBoundedByNormOnFinite source Finite) :
    IsBoundedBelowGreenSobolevH10Energy energy Finite := by
  rcases hsource with ⟨C, _hC_nonneg, hC⟩
  refine ⟨-(1 / 2 : ℝ) * C ^ (2 : ℕ), ?_⟩
  intro u hu
  have hsrc : source u ≤ C * ‖u‖ := hC u hu
  have henergy_u := henergy u hu
  have hyoung : C * ‖u‖ ≤ (1 / 2 : ℝ) * ‖u‖ ^ (2 : ℕ) +
      (1 / 2 : ℝ) * C ^ (2 : ℕ) := by
    have hsq : 0 ≤ (‖u‖ - C) ^ (2 : ℕ) := sq_nonneg _
    nlinarith
  rw [henergy_u]
  nlinarith

/--
%%handwave
name:
  Bounded source gives coercive pure Dirichlet energy
statement:
  A pure Dirichlet quadratic energy whose source term is bounded by the
  \(H^1_0\) norm is coercive in the \(H^1_0\) norm.
proof:
  The source bound and Young's inequality give
  \(E(u)\ge\frac14\|u\|^2-C^2\), which tends to infinity with
  \(\|u\|^2\).
-/
theorem pureDirichletGreenSobolevH10Energy_coercive_of_source_bound
    {energy source : V → ℝ} {Finite : V → Prop}
    (henergy :
      IsPureDirichletGreenSobolevH10EnergyOnFinite energy source Finite)
    (hsource : IsGreenSobolevH10SourceBoundedByNormOnFinite source Finite) :
    IsCoerciveGreenSobolevH10Energy energy Finite := by
  rcases hsource with ⟨C, _hC_nonneg, hC⟩
  intro A
  refine ⟨max 0 (4 * (A + C ^ (2 : ℕ))), ?_⟩
  intro u hu hlarge
  have hsrc : source u ≤ C * ‖u‖ := hC u hu
  have henergy_u := henergy u hu
  have hyoung : C * ‖u‖ ≤ (1 / 4 : ℝ) * ‖u‖ ^ (2 : ℕ) +
      C ^ (2 : ℕ) := by
    have hsq : 0 ≤ (‖u‖ - 2 * C) ^ (2 : ℕ) := sq_nonneg _
    nlinarith
  have henergy_lower :
      (1 / 4 : ℝ) * ‖u‖ ^ (2 : ℕ) - C ^ (2 : ℕ) ≤ energy u := by
    rw [henergy_u]
    nlinarith
  have hlarge_norm : 4 * (A + C ^ (2 : ℕ)) ≤ ‖u‖ ^ (2 : ℕ) :=
    (le_max_right (0 : ℝ) (4 * (A + C ^ (2 : ℕ)))).trans hlarge
  have hA : A ≤ (1 / 4 : ℝ) * ‖u‖ ^ (2 : ℕ) - C ^ (2 : ℕ) := by
    nlinarith
  exact hA.trans henergy_lower

/--
%%handwave
name:
  Source functional on completed pure \(H^1_0\)
statement:
  A continuous source pairing on the Dirichlet core determines a linear
  source term on the completed pure \(H^1_0\) space.
-/
noncomputable def greenSobolevH10CompletionSource {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    {g : BackgroundSurfaceMetricOnSurface X}
    (C : GreenSobolevH10DirichletCore g)
    (source : C.Core →L[ℝ] ℝ) :
    GreenSobolevH10DirichletCompletion C → ℝ :=
  C.extendSource source

/--
%%handwave
name:
  Completed pure \(H^1_0\) energy
statement:
  The pure Dirichlet energy on the completed \(H^1_0\) space is
  \[
    E(u)=\frac12\|u\|_{H^1_0}^2-L(u).
  \]
-/
noncomputable def greenSobolevH10CompletionEnergy {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    {g : BackgroundSurfaceMetricOnSurface X}
    (C : GreenSobolevH10DirichletCore g)
    (source : C.Core →L[ℝ] ℝ)
    (u : GreenSobolevH10DirichletCompletion C) : ℝ :=
  (1 / 2 : ℝ) * ‖u‖ ^ (2 : ℕ) - greenSobolevH10CompletionSource C source u

/--
%%handwave
name:
  All completed pure \(H^1_0\) elements have finite energy
statement:
  In the pure Dirichlet Hilbert model, every element has finite quadratic
  Dirichlet energy.
-/
def greenSobolevH10CompletionFinite {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    {g : BackgroundSurfaceMetricOnSurface X}
    (C : GreenSobolevH10DirichletCore g)
    (_u : GreenSobolevH10DirichletCompletion C) : Prop :=
  True

/--
%%handwave
name:
  Completed pure \(H^1_0\) energy is quadratic
statement:
  The completed pure Dirichlet energy has the standard quadratic-minus-linear
  form on its finite-energy domain.
-/
theorem greenSobolevH10CompletionEnergy_isPureDirichlet {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    {g : BackgroundSurfaceMetricOnSurface X}
    (C : GreenSobolevH10DirichletCore g)
    (source : C.Core →L[ℝ] ℝ) :
    IsPureDirichletGreenSobolevH10EnergyOnFinite
      (greenSobolevH10CompletionEnergy C source)
      (greenSobolevH10CompletionSource C source)
      (greenSobolevH10CompletionFinite C) := by
  intro u _hu
  rfl

/--
%%handwave
name:
  Completed source is bounded by the \(H^1_0\) norm
statement:
  The extended source pairing on pure \(H^1_0\) is bounded by its operator
  norm times the \(H^1_0\) norm.
-/
theorem greenSobolevH10CompletionSource_boundedByNorm {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    {g : BackgroundSurfaceMetricOnSurface X}
    (C : GreenSobolevH10DirichletCore g)
    (source : C.Core →L[ℝ] ℝ) :
    IsGreenSobolevH10SourceBoundedByNormOnFinite
      (greenSobolevH10CompletionSource C source)
      (greenSobolevH10CompletionFinite C) := by
  have hnonneg :
      0 ≤ ‖(C.extendSource source :
        GreenSobolevH10DirichletCompletion C →L[ℝ] ℝ)‖ :=
    ContinuousLinearMap.opNorm_nonneg _
  refine ⟨‖C.extendSource source‖, hnonneg, ?_⟩
  intro u _hu
  exact C.extendSource_bound source u

/--
%%handwave
name:
  Completed pure \(H^1_0\) energy is bounded below
statement:
  The pure Dirichlet energy on the completed \(H^1_0\) space is bounded below
  whenever the source pairing is continuous on the Dirichlet core.
-/
theorem greenSobolevH10CompletionEnergy_boundedBelow {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    {g : BackgroundSurfaceMetricOnSurface X}
    (C : GreenSobolevH10DirichletCore g)
    (source : C.Core →L[ℝ] ℝ) :
    IsBoundedBelowGreenSobolevH10Energy
      (greenSobolevH10CompletionEnergy C source)
      (greenSobolevH10CompletionFinite C) :=
  pureDirichletGreenSobolevH10Energy_boundedBelow_of_source_bound
    (greenSobolevH10CompletionEnergy_isPureDirichlet C source)
    (greenSobolevH10CompletionSource_boundedByNorm C source)

/--
%%handwave
name:
  Completed pure \(H^1_0\) energy is coercive
statement:
  The pure Dirichlet energy on the completed \(H^1_0\) space is coercive
  whenever the source pairing is continuous on the Dirichlet core.
-/
theorem greenSobolevH10CompletionEnergy_coercive {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    {g : BackgroundSurfaceMetricOnSurface X}
    (C : GreenSobolevH10DirichletCore g)
    (source : C.Core →L[ℝ] ℝ) :
    IsCoerciveGreenSobolevH10Energy
      (greenSobolevH10CompletionEnergy C source)
      (greenSobolevH10CompletionFinite C) :=
  pureDirichletGreenSobolevH10Energy_coercive_of_source_bound
    (greenSobolevH10CompletionEnergy_isPureDirichlet C source)
    (greenSobolevH10CompletionSource_boundedByNorm C source)

/--
%%handwave
name:
  Completed pure \(H^1_0\) energy is weakly lower semicontinuous
statement:
  The quadratic-minus-linear energy induced by a continuous source functional
  on a completed Dirichlet core is weakly lower semicontinuous.
-/
theorem greenSobolevH10CompletionEnergy_weaklyLowerSemicontinuous {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    {g : BackgroundSurfaceMetricOnSurface X}
    (C : GreenSobolevH10DirichletCore g)
    (source : C.Core →L[ℝ] ℝ) :
    IsWeaklyLowerSemicontinuousGreenSobolevH10Energy
      (greenSobolevH10CompletionEnergy C source) := by
  letI : NormedAddCommGroup C.Core := C.normedAddCommGroup
  letI : InnerProductSpace ℝ C.Core := C.innerProductSpace
  refine pureDirichletGreenSobolevH10Energy_weaklyLowerSemicontinuous
    (V := GreenSobolevH10DirichletCompletion C)
    (source := C.extendSource source) ?_
  intro u
  rfl

/--
%%handwave
name:
  Completed pure \(H^1_0\) weak compactness gives a minimizer
statement:
  If bounded minimizing sequences in the completed pure \(H^1_0\) model have
  weakly convergent finite-energy subsequences, then the completed
  quadratic-minus-linear energy has a minimizer.
-/
theorem greenSobolevH10CompletionEnergy_has_minimizer_of_weak_compactness {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    {g : BackgroundSurfaceMetricOnSurface X}
    (C : GreenSobolevH10DirichletCore g)
    (source : C.Core →L[ℝ] ℝ)
    (hcompact :
      HasWeakCompactnessForEventuallyBoundedGreenSobolevH10MinimizingSequences
        (greenSobolevH10CompletionEnergy C source)
        (greenSobolevH10CompletionFinite C)) :
    ∃ u : GreenSobolevH10DirichletCompletion C,
      IsGreenSobolevH10EnergyMinimizer
        (greenSobolevH10CompletionEnergy C source)
        (greenSobolevH10CompletionFinite C) u := by
  exact
    greenSobolevH10Energy_has_minimizer_of_boundedBelow_coercive_lsc_and_weak_compactness
      (greenSobolevH10CompletionEnergy C source)
      (greenSobolevH10CompletionFinite C)
      (greenSobolevH10CompletionEnergy_boundedBelow C source)
      ⟨0, trivial⟩
      (greenSobolevH10CompletionEnergy_coercive C source)
      (greenSobolevH10CompletionEnergy_weaklyLowerSemicontinuous C source)
      hcompact

/--
%%handwave
name:
  Completed pure \(H^1_0\) Riesz minimizer
statement:
  The Riesz representative of the extended source functional minimizes the
  completed pure Dirichlet energy.
-/
theorem greenSobolevH10CompletionEnergy_rieszRepresentative_minimizer {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    {g : BackgroundSurfaceMetricOnSurface X}
    (C : GreenSobolevH10DirichletCore g)
    (source : C.Core →L[ℝ] ℝ) :
    IsGreenSobolevH10EnergyMinimizer
      (greenSobolevH10CompletionEnergy C source)
      (greenSobolevH10CompletionFinite C)
      (greenSobolevH10RieszRepresentative (C.extendSource source)) := by
  letI : NormedAddCommGroup C.Core := C.normedAddCommGroup
  letI : InnerProductSpace ℝ C.Core := C.innerProductSpace
  exact
    pureDirichletGreenSobolevH10Energy_rieszRepresentative_minimizer
      (V := GreenSobolevH10DirichletCompletion C)
      (source := C.extendSource source)
      (energy := greenSobolevH10CompletionEnergy C source)
      (by
        intro u
        rfl)

/--
%%handwave
name:
  Completed pure \(H^1_0\) energy has a Riesz minimizer
statement:
  The completed pure Dirichlet energy associated to any continuous source
  functional on the core has a minimizer.
-/
theorem greenSobolevH10CompletionEnergy_has_riesz_minimizer {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    {g : BackgroundSurfaceMetricOnSurface X}
    (C : GreenSobolevH10DirichletCore g)
    (source : C.Core →L[ℝ] ℝ) :
    ∃ u : GreenSobolevH10DirichletCompletion C,
      IsGreenSobolevH10EnergyMinimizer
        (greenSobolevH10CompletionEnergy C source)
        (greenSobolevH10CompletionFinite C) u :=
  ⟨greenSobolevH10RieszRepresentative (C.extendSource source),
    greenSobolevH10CompletionEnergy_rieszRepresentative_minimizer C source⟩

/--
%%handwave
name:
  Euler equation for the completed pure \(H^1_0\) Riesz minimizer
statement:
  The completed Riesz minimizer represents the extended source functional by
  the pure Dirichlet inner product.
-/
theorem greenSobolevH10CompletionEnergy_rieszRepresentative_eulerLagrange
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    {g : BackgroundSurfaceMetricOnSurface X}
    (C : GreenSobolevH10DirichletCore g)
    (source : C.Core →L[ℝ] ℝ)
    (η : GreenSobolevH10DirichletCompletion C) :
    inner ℝ (greenSobolevH10RieszRepresentative (C.extendSource source)) η =
      greenSobolevH10CompletionSource C source η := by
  letI : NormedAddCommGroup C.Core := C.normedAddCommGroup
  letI : InnerProductSpace ℝ C.Core := C.innerProductSpace
  exact
    pureDirichletGreenSobolevH10Energy_rieszRepresentative_eulerLagrange
      (V := GreenSobolevH10DirichletCompletion C)
      (source := C.extendSource source) η

/--
%%handwave
name:
  Source functional on concrete pure \(H^1_0\)
statement:
  A continuous source pairing on the smooth compactly supported Dirichlet
  core extends to a source term on the concrete pure \(H^1_0\) completion.
-/
noncomputable def greenSobolevH10SmoothCompactSupportSource {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (source : (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ) :
    GreenSobolevH10SmoothCompactSupport g → ℝ :=
  greenSobolevH10CompletionSource
    (greenSobolevH10SmoothCompactSupportCore g) source

/--
%%handwave
name:
  Restrict a completed source functional to the smooth core
statement:
  A continuous source functional on the completed pure \(H^1_0\) space
  restricts to a continuous functional on the smooth compactly supported
  Dirichlet core.
-/
noncomputable def greenSobolevH10SmoothCompactSupportCoreSourceOfCompletion
    {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (L : GreenSobolevH10SmoothCompactSupport g →L[ℝ] ℝ) :
    (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ := by
  let C := greenSobolevH10SmoothCompactSupportCore g
  exact L.comp
    (UniformSpace.Completion.toComplL :
      C.Core →L[ℝ] UniformSpace.Completion C.Core)

/--
%%handwave
name:
  Extending the restricted completed source recovers the source
statement:
  If a continuous source functional on the completed pure \(H^1_0\) space is
  restricted to the smooth Dirichlet core and then extended by completion, the
  resulting functional is the original one.
proof:
  The core has dense image in its completion and the canonical inclusion is
  uniform inducing, so uniqueness of continuous linear extensions applies.
-/
theorem greenSobolevH10SmoothCompactSupportSource_coreSourceOfCompletion
    {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (L : GreenSobolevH10SmoothCompactSupport g →L[ℝ] ℝ)
    (u : GreenSobolevH10SmoothCompactSupport g) :
    greenSobolevH10SmoothCompactSupportSource
        (greenSobolevH10SmoothCompactSupportCoreSourceOfCompletion L) u =
      L u := by
  let C := greenSobolevH10SmoothCompactSupportCore g
  let e : C.Core →L[ℝ] UniformSpace.Completion C.Core :=
    UniformSpace.Completion.toComplL
  let source : C.Core →L[ℝ] ℝ := L.comp e
  have hdense : DenseRange e := by
    simpa [e, UniformSpace.Completion.coe_toComplL] using
      (UniformSpace.Completion.denseRange_coe : DenseRange
        ((↑) : C.Core → UniformSpace.Completion C.Core))
  have hind : IsUniformInducing e := by
    simpa [e, UniformSpace.Completion.coe_toComplL] using
      (UniformSpace.Completion.isUniformInducing_coe C.Core)
  have hsource_eq :
      greenSobolevH10SmoothCompactSupportCoreSourceOfCompletion L = source := by
    rfl
  change (C.extendSource
      (greenSobolevH10SmoothCompactSupportCoreSourceOfCompletion L)) u = L u
  rw [hsource_eq]
  have h_extend : C.extendSource source = L := by
    dsimp [GreenSobolevH10DirichletCore.extendSource, source, e]
    exact ContinuousLinearMap.extend_unique (f := source) (e := e)
      hdense hind L rfl
  rw [h_extend]

/--
%%handwave
name:
  Energy on concrete pure \(H^1_0\)
statement:
  A continuous source pairing on the smooth compactly supported Dirichlet
  core defines the quadratic-minus-linear energy on the concrete pure
  \(H^1_0\) space.
-/
noncomputable def greenSobolevH10SmoothCompactSupportEnergy {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (source : (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ)
    (u : GreenSobolevH10SmoothCompactSupport g) : ℝ :=
  greenSobolevH10CompletionEnergy
    (greenSobolevH10SmoothCompactSupportCore g) source u

/--
%%handwave
name:
  Finite energy domain for concrete pure \(H^1_0\)
statement:
  In the concrete pure Dirichlet completion, every element has finite
  quadratic Dirichlet energy.
-/
def greenSobolevH10SmoothCompactSupportFinite {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (u : GreenSobolevH10SmoothCompactSupport g) : Prop :=
  greenSobolevH10CompletionFinite
    (greenSobolevH10SmoothCompactSupportCore g) u

/--
%%handwave
name:
  Concrete pure \(H^1_0\) energy is quadratic
statement:
  The energy induced by a continuous source functional on the concrete
  Dirichlet core has the pure quadratic-minus-linear form.
-/
theorem greenSobolevH10SmoothCompactSupportEnergy_isPureDirichlet {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (source : (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ) :
    IsPureDirichletGreenSobolevH10EnergyOnFinite
      (greenSobolevH10SmoothCompactSupportEnergy source)
      (greenSobolevH10SmoothCompactSupportSource source)
      (greenSobolevH10SmoothCompactSupportFinite (g := g)) :=
  greenSobolevH10CompletionEnergy_isPureDirichlet
    (greenSobolevH10SmoothCompactSupportCore g) source

/--
%%handwave
name:
  Concrete pure \(H^1_0\) source is norm-bounded
statement:
  The extended source pairing on the concrete pure \(H^1_0\) space is
  bounded by its operator norm times the \(H^1_0\) norm.
-/
theorem greenSobolevH10SmoothCompactSupportSource_boundedByNorm {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (source : (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ) :
    IsGreenSobolevH10SourceBoundedByNormOnFinite
      (greenSobolevH10SmoothCompactSupportSource source)
      (greenSobolevH10SmoothCompactSupportFinite (g := g)) :=
  greenSobolevH10CompletionSource_boundedByNorm
    (greenSobolevH10SmoothCompactSupportCore g) source

/--
%%handwave
name:
  Concrete pure \(H^1_0\) energy is bounded below
statement:
  The concrete pure Dirichlet energy is bounded below for every continuous
  source functional on the smooth Dirichlet core.
-/
theorem greenSobolevH10SmoothCompactSupportEnergy_boundedBelow {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (source : (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ) :
    IsBoundedBelowGreenSobolevH10Energy
      (greenSobolevH10SmoothCompactSupportEnergy source)
      (greenSobolevH10SmoothCompactSupportFinite (g := g)) :=
  greenSobolevH10CompletionEnergy_boundedBelow
    (greenSobolevH10SmoothCompactSupportCore g) source

/--
%%handwave
name:
  Concrete pure \(H^1_0\) energy is coercive
statement:
  The concrete pure Dirichlet energy is coercive for every continuous source
  functional on the smooth Dirichlet core.
-/
theorem greenSobolevH10SmoothCompactSupportEnergy_coercive {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (source : (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ) :
    IsCoerciveGreenSobolevH10Energy
      (greenSobolevH10SmoothCompactSupportEnergy source)
      (greenSobolevH10SmoothCompactSupportFinite (g := g)) :=
  greenSobolevH10CompletionEnergy_coercive
    (greenSobolevH10SmoothCompactSupportCore g) source

/--
%%handwave
name:
  Concrete pure \(H^1_0\) energy is weakly lower semicontinuous
statement:
  The quadratic-minus-linear energy on the concrete smooth compactly
  supported Dirichlet completion is weakly lower semicontinuous for every
  continuous source functional on the core.
-/
theorem greenSobolevH10SmoothCompactSupportEnergy_weaklyLowerSemicontinuous {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (source : (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ) :
    IsWeaklyLowerSemicontinuousGreenSobolevH10Energy
      (greenSobolevH10SmoothCompactSupportEnergy source) :=
  greenSobolevH10CompletionEnergy_weaklyLowerSemicontinuous
    (greenSobolevH10SmoothCompactSupportCore g) source

/--
%%handwave
name:
  Concrete pure \(H^1_0\) weak compactness gives a minimizer
statement:
  If bounded minimizing sequences in the concrete smooth compactly supported
  Dirichlet completion have weakly convergent subsequences, then the
  quadratic-minus-linear energy on that completion has a minimizer.
-/
theorem greenSobolevH10SmoothCompactSupportEnergy_has_minimizer_of_weak_compactness
    {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (source : (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ)
    (hcompact :
      HasWeakCompactnessForEventuallyBoundedGreenSobolevH10MinimizingSequences
        (greenSobolevH10SmoothCompactSupportEnergy source)
        (greenSobolevH10SmoothCompactSupportFinite (g := g))) :
    ∃ u : GreenSobolevH10SmoothCompactSupport g,
      IsGreenSobolevH10EnergyMinimizer
        (greenSobolevH10SmoothCompactSupportEnergy source)
        (greenSobolevH10SmoothCompactSupportFinite (g := g)) u :=
  greenSobolevH10CompletionEnergy_has_minimizer_of_weak_compactness
    (greenSobolevH10SmoothCompactSupportCore g) source hcompact

/--
%%handwave
name:
  Concrete pure \(H^1_0\) Riesz minimizer
statement:
  The Riesz representative of the extended smooth-core source functional
  minimizes the concrete pure Dirichlet energy.
-/
theorem greenSobolevH10SmoothCompactSupportEnergy_rieszRepresentative_minimizer
    {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (source : (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ) :
    IsGreenSobolevH10EnergyMinimizer
      (greenSobolevH10SmoothCompactSupportEnergy source)
      (greenSobolevH10SmoothCompactSupportFinite (g := g))
      (greenSobolevH10RieszRepresentative
        ((greenSobolevH10SmoothCompactSupportCore g).extendSource source)) :=
  greenSobolevH10CompletionEnergy_rieszRepresentative_minimizer
    (greenSobolevH10SmoothCompactSupportCore g) source

/--
%%handwave
name:
  Concrete pure \(H^1_0\) energy has a Riesz minimizer
statement:
  The concrete pure Dirichlet energy associated to any continuous source
  functional on the smooth compactly supported core has a minimizer.
-/
theorem greenSobolevH10SmoothCompactSupportEnergy_has_riesz_minimizer
    {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (source : (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ) :
    ∃ u : GreenSobolevH10SmoothCompactSupport g,
      IsGreenSobolevH10EnergyMinimizer
        (greenSobolevH10SmoothCompactSupportEnergy source)
        (greenSobolevH10SmoothCompactSupportFinite (g := g)) u :=
  greenSobolevH10CompletionEnergy_has_riesz_minimizer
    (greenSobolevH10SmoothCompactSupportCore g) source

end PureDirichletH10DirectMethod

end Uniformization

end JJMath
