import JJMath.Quasiconformal.CapacitySeparation
import JJMath.Uniformization.RadoSecondCountable
import JJMath.PotentialTheory.EnergyMethod.MazurLemma
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology

/-!
# Compactness of normalized quasiconformal sphere maps

The capacity-separation estimates make every normalized family, and its
inverse family, equicontinuous on the Riemann sphere. This file applies
Arzelà--Ascoli simultaneously to the maps and inverses. The resulting limits
are inverse normalized homeomorphisms.

The analytic part uses the area formula for uniform finite-chart energy
bounds, diagonal Hilbert-space extraction of the two coordinate values of
the weak differential on all integer-radius disks, and compatibility under
restriction. Spherical uniform convergence becomes strong local $L^2$
convergence in finite coordinates. Passing the distributional identities to
the weak limits and gluing the diskwise classes proves that the limiting
finite-chart homeomorphism belongs to $W^{1,2}_{\mathrm{loc}}$. Closure of
an eventually diskwise fixed Beltrami equation is then obtained from weak
continuity of bounded multiplication on $L^2$; the coefficient bound
$|\mu|\leq k<1$ recovers the metric distortion inequality algebraically.
-/

namespace JJMath

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace Quasiconformal

noncomputable section

/--
%%handwave
name:
  Countable diagonal subsequence extraction
statement:
  Let $x_{m,n}$ be a sequence in a topological space $Y_m$ for every
  $m\in\mathbb N$. Suppose that every subsequence and every $m$ admit a
  further subsequence converging in $Y_m$. Then one strictly increasing
  subsequence $\varphi$ makes $x_{m,\varphi(n)}$ converge for every $m$.
proof:
  Recursively refine the subsequence at the $m$th stage so that it converges
  in $Y_m$. The diagonal indices are strictly increasing. For each fixed
  $m$, the diagonal tail factors through the convergent sequence chosen at
  stage $m$, with factor indices tending to infinity.
-/
theorem exists_strictMono_subsequence_tendsto_countably
    {Y : ℕ → Type*} [∀ m, TopologicalSpace (Y m)]
    (x : ∀ m, ℕ → Y m)
    (hextract :
      ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ m : ℕ,
        ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
          ∃ y : Y m,
            Tendsto (fun n ↦ x m (φ (ψ n))) atTop (nhds y)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ y : ∀ m, Y m,
        ∀ m, Tendsto (fun n ↦ x m (φ n)) atTop (nhds (y m)) := by
  classical
  let Step := {φ : ℕ → ℕ // StrictMono φ}
  let next : ℕ → Step → Step := fun m s =>
    let ψ : ℕ → ℕ := Classical.choose (hextract s.1 s.2 m)
    ⟨s.1 ∘ ψ, s.2.comp (Classical.choose_spec (hextract s.1 s.2 m)).1⟩
  let S : ℕ → Step := Nat.rec ⟨id, strictMono_id⟩ (fun m s ↦ next m s)
  let diag : ℕ → ℕ := fun n ↦ (S n).1 n
  have hfactor :
      ∀ {a b : ℕ}, a ≤ b → ∀ i : ℕ,
        ∃ j : ℕ, i ≤ j ∧ (S b).1 i = (S a).1 j := by
    intro a b hab
    induction hab with
    | refl =>
        intro i
        exact ⟨i, le_rfl, rfl⟩
    | @step b hab ih =>
        intro i
        let ψ : ℕ → ℕ := Classical.choose (hextract (S b).1 (S b).2 b)
        have hψ : StrictMono ψ :=
          (Classical.choose_spec (hextract (S b).1 (S b).2 b)).1
        rcases ih (ψ i) with ⟨j, hij, hEq⟩
        refine ⟨j, le_trans (StrictMono.id_le hψ i) hij, ?_⟩
        simpa [S, next, ψ, Function.comp_def] using hEq
  have hdiag_strict : StrictMono diag := by
    refine strictMono_nat_of_lt_succ ?_
    intro n
    rcases hfactor (a := n) (b := n + 1) (Nat.le_succ n) (n + 1) with
      ⟨j, hj_le, hEq⟩
    have hn_lt_j : n < j := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hj_le
    have hlt : (S n).1 n < (S n).1 j := (S n).2 hn_lt_j
    dsimp [diag]
    rw [hEq]
    exact hlt
  have hlocal :
      ∀ m : ℕ, ∃ y : Y m,
        Tendsto (fun n ↦ x m (diag n)) atTop (nhds y) := by
    intro m
    let ψ : ℕ → ℕ := Classical.choose (hextract (S m).1 (S m).2 m)
    let y : Y m :=
      Classical.choose
        (Classical.choose_spec (hextract (S m).1 (S m).2 m)).2
    have hconv_step :
        Tendsto (fun n ↦ x m ((S (m + 1)).1 n)) atTop (nhds y) := by
      have hchosen :
          Tendsto (fun n ↦ x m ((S m).1 (ψ n))) atTop (nhds y) :=
        Classical.choose_spec
          (Classical.choose_spec (hextract (S m).1 (S m).2 m)).2
      simpa [S, next, ψ, y, Function.comp_def] using hchosen
    let shift : ℕ := m + 1
    let idx : ℕ → ℕ := fun n =>
      Classical.choose
        (hfactor (a := shift) (b := shift + n)
          (Nat.le_add_right shift n) (shift + n))
    have hidx_spec : ∀ n : ℕ,
        shift + n ≤ idx n ∧
          (S (shift + n)).1 (shift + n) = (S shift).1 (idx n) := by
      intro n
      exact Classical.choose_spec
        (hfactor (a := shift) (b := shift + n)
          (Nat.le_add_right shift n) (shift + n))
    have hidx_tendsto : Tendsto idx atTop atTop := by
      refine tendsto_atTop_atTop.mpr ?_
      intro b
      refine ⟨b, ?_⟩
      intro n hn
      exact le_trans hn (le_trans (Nat.le_add_left n shift) (hidx_spec n).1)
    have hconv_idx :
        Tendsto (fun n ↦ x m ((S shift).1 (idx n))) atTop (nhds y) :=
      hconv_step.comp hidx_tendsto
    have hconv_tail :
        Tendsto (fun n ↦ x m (diag (n + shift))) atTop (nhds y) := by
      refine hconv_idx.congr' ?_
      filter_upwards with n
      have hEq := (hidx_spec n).2
      have hEq' :
          (S shift).1 (idx n) = (S (n + shift)).1 (n + shift) := by
        simpa [shift, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hEq.symm
      exact congrArg (x m) hEq'
    exact ⟨y, (tendsto_add_atTop_iff_nat
      (f := fun n ↦ x m (diag n)) shift).mp hconv_tail⟩
  choose y hy using hlocal
  exact ⟨diag, hdiag_strict, y, hy⟩

/--
%%handwave
name:
  Uniform subsequence extraction for normalized quasiconformal sphere maps
statement:
  Let $F_n:\widehat{\mathbb C}\to\widehat{\mathbb C}$ be normalized
  $K$-quasiconformal homeomorphisms. There are a strictly increasing map
  $\varphi:\mathbb N\to\mathbb N$ and a continuous map
  $f:\widehat{\mathbb C}\to\widehat{\mathbb C}$ such that
  $$
    F_{\varphi(n)}\longrightarrow f
  $$
  uniformly on the sphere.
proof:
  The normalized family is equicontinuous on the sphere. Its pointwise
  values lie in the compact sphere, so the compact-set Arzelà--Ascoli theorem
  gives a uniformly convergent subsequence. The uniform limit of continuous
  maps is continuous.
-/
theorem normalizedKQuasiconformalRiemannSphere_subsequence_tendstoUniformly
    {K : ℝ}
    (F : ℕ → RiemannSphere ≃ₜ RiemannSphere)
    (hqc : ∀ n, IsKQuasiconformalRiemannSphere K (F n))
    (hnorm : ∀ n, IsNormalizedRiemannSphereHomeomorph (F n)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ f : RiemannSphere → RiemannSphere,
        Continuous f ∧ TendstoUniformly (fun n ↦ F (φ n)) f atTop := by
  have heq : EquicontinuousOn (fun n z ↦ F n z) Set.univ :=
    (equicontinuous_normalizedKQuasiconformalRiemannSphere K F hqc hnorm).equicontinuousOn
      Set.univ
  obtain ⟨φ, hφ, f, hf⟩ :=
    Uniformization.functions_subsequence_tendstoUniformlyOn_of_compact_equicontinuousOn
      (K := (Set.univ : Set RiemannSphere)) isCompact_univ
      (F := fun n z ↦ F n z)
      (fun n ↦ (F n).continuous.continuousOn)
      (fun x _hx ↦ ⟨Set.univ, isCompact_univ, fun n ↦ Set.mem_univ _⟩)
      heq
  have hfuniform : TendstoUniformly (fun n ↦ F (φ n)) f atTop :=
    tendstoUniformlyOn_univ.mp hf
  have hfcont : Continuous f :=
    hfuniform.continuous
      (Filter.Eventually.frequently
        (Filter.Eventually.of_forall fun n ↦ (F (φ n)).continuous))
  exact ⟨φ, hφ, f, hfcont, hfuniform⟩

/--
%%handwave
name:
  Topological compactness of normalized quasiconformal sphere maps
statement:
  Let $F_n:\widehat{\mathbb C}\to\widehat{\mathbb C}$ be normalized
  $K$-quasiconformal homeomorphisms. There are a strictly increasing map
  $\theta:\mathbb N\to\mathbb N$ and a normalized sphere homeomorphism $G$
  such that
  $$
    F_{\theta(n)}\longrightarrow G,
    \qquad
    F_{\theta(n)}^{-1}\longrightarrow G^{-1}
  $$
  uniformly on the sphere.
proof:
  Apply Arzelà--Ascoli first to the maps and then to their normalized
  $K$-quasiconformal inverses. Pass to the resulting diagonal subsequence.
  Uniform convergence of the first family, pointwise convergence of the
  second, and continuity of the first limit show $f\circ g=\mathrm{id}$;
  the symmetric argument gives $g\circ f=\mathrm{id}$. Thus the limits form
  a homeomorphism and its inverse. Pointwise convergence at $0$, $1$, and
  $\infty$ preserves normalization.
-/
theorem normalizedKQuasiconformalRiemannSphere_topological_compactness
    {K : ℝ}
    (F : ℕ → RiemannSphere ≃ₜ RiemannSphere)
    (hqc : ∀ n, IsKQuasiconformalRiemannSphere K (F n))
    (hnorm : ∀ n, IsNormalizedRiemannSphereHomeomorph (F n)) :
    ∃ θ : ℕ → ℕ, StrictMono θ ∧
      ∃ G : RiemannSphere ≃ₜ RiemannSphere,
        IsNormalizedRiemannSphereHomeomorph G ∧
        TendstoUniformly (fun n ↦ F (θ n)) G atTop ∧
        TendstoUniformly (fun n ↦ (F (θ n)).symm) G.symm atTop := by
  obtain ⟨φ, hφ, f, hfcont, hf⟩ :=
    normalizedKQuasiconformalRiemannSphere_subsequence_tendstoUniformly
      F hqc hnorm
  let H : ℕ → RiemannSphere ≃ₜ RiemannSphere := fun n ↦ (F (φ n)).symm
  obtain ⟨ψ, hψ, g, hgcont, hg⟩ :=
    normalizedKQuasiconformalRiemannSphere_subsequence_tendstoUniformly
      H (fun n ↦ (hqc (φ n)).symm) (fun n ↦ (hnorm (φ n)).symm)
  let θ : ℕ → ℕ := φ ∘ ψ
  have hθ : StrictMono θ := hφ.comp hψ
  have hψtop : Tendsto ψ atTop atTop := hψ.tendsto_atTop
  have hf' : TendstoUniformly (fun n ↦ F (θ n)) f atTop := by
    intro U hU
    exact hψtop (hf U hU)
  have hg' : TendstoUniformly (fun n ↦ (F (θ n)).symm) g atTop := by
    simpa [H, θ, Function.comp_def] using hg
  have hfg (x : RiemannSphere) : f (g x) = x := by
    have hcomp := hf'.tendsto_comp hfcont.continuousAt (hg'.tendsto_at x)
    have hconst : Tendsto
        (fun n ↦ F (θ n) ((F (θ n)).symm x)) atTop (𝓝 x) := by
      simpa using (tendsto_const_nhds :
        Tendsto (fun _ : ℕ ↦ x) atTop (𝓝 x))
    exact tendsto_nhds_unique hcomp hconst
  have hgf (x : RiemannSphere) : g (f x) = x := by
    have hcomp := hg'.tendsto_comp hgcont.continuousAt (hf'.tendsto_at x)
    have hconst : Tendsto
        (fun n ↦ (F (θ n)).symm (F (θ n) x)) atTop (𝓝 x) := by
      simpa using (tendsto_const_nhds :
        Tendsto (fun _ : ℕ ↦ x) atTop (𝓝 x))
    exact tendsto_nhds_unique hcomp hconst
  let G : RiemannSphere ≃ₜ RiemannSphere :=
    { toEquiv :=
        { toFun := f
          invFun := g
          left_inv := hgf
          right_inv := hfg }
      continuous_toFun := hfcont
      continuous_invFun := hgcont }
  have hfix (q : RiemannSphere) (hq : ∀ n, F n q = q) : f q = q := by
    have ht := hf'.tendsto_at q
    have heq : (fun n ↦ F (θ n) q) = (fun _ : ℕ ↦ q) := by
      funext n
      exact hq (θ n)
    rw [heq] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds
  have hGnorm : IsNormalizedRiemannSphereHomeomorph G := by
    refine ⟨?_, ?_, ?_⟩
    · exact hfix ((0 : ℂ) : RiemannSphere) (fun n ↦ (hnorm n).1)
    · exact hfix ((1 : ℂ) : RiemannSphere) (fun n ↦ (hnorm n).2.1)
    · exact hfix (OnePoint.infty : RiemannSphere) (fun n ↦ (hnorm n).2.2)
  refine ⟨θ, hθ, G, hGnorm, ?_, ?_⟩
  · simpa [G] using hf'
  · simpa [G] using hg'

/--
%%handwave
name:
  Existence of a whole-plane finite-chart weak differential
statement:
  If $F:\widehat{\mathbb C}\to\widehat{\mathbb C}$ is a normalized
  $K$-quasiconformal homeomorphism and $f:\mathbb C\to\mathbb C$ is its
  finite-chart representative, then there is a field $Df$ such that
  $f\in W^{1,2}_{\mathrm{loc}}(\mathbb C,\mathbb C)$ with weak differential
  $Df$.
proof:
  Use the finite-to-finite chart in the definition of sphere
  quasiconformality. Normalization makes its source all of $\mathbb C$, and
  the ambient chart map agrees pointwise with the finite-chart
  homeomorphism.
-/
theorem IsKQuasiconformalRiemannSphere.exists_finiteChart_weakDifferential
    {K : ℝ} {F : RiemannSphere ≃ₜ RiemannSphere}
    (hqc : IsKQuasiconformalRiemannSphere K F)
    (hF : IsNormalizedRiemannSphereHomeomorph F) :
    ∃ df : ℂ → ℂ →L[ℝ] ℂ,
      IsLocalW12On Set.univ
        (riemannSphereFiniteChartHomeomorph F hF.2.2) df := by
  let H := riemannSphereChartHomeomorph F .finite .finite
  have hsource :=
    riemannSphere_finiteChartRepresentation_source_eq_univ_of_map_infty
      F hF.2.2
  obtain ⟨df, hdf, _hdist⟩ := (hqc .finite .finite).2.2.2
  have hdf_univ : IsLocalW12On Set.univ (ambientMap H) df := by
    simpa only [H, hsource] using hdf
  refine ⟨df, hdf_univ.congr_ae ?_⟩
  filter_upwards with z
  exact (ambientMap_finiteChartHomeomorph_apply F hF.2.2 z).symm

/--
%%handwave
name:
  Punctured finite chart of a normalized sphere map
statement:
  If a sphere homeomorphism $F$ fixes $0$ and $\infty$, its finite-chart
  representative restricts to a homeomorphism
  $\mathbb C^\times\to\mathbb C^\times$.
-/
def normalizedFiniteChartPuncturedHomeomorph
    (F : RiemannSphere ≃ₜ RiemannSphere)
    (hF : IsNormalizedRiemannSphereHomeomorph F) :
    ({0}ᶜ : Set ℂ) ≃ₜ ({0}ᶜ : Set ℂ) where
  toFun z := ⟨riemannSphereFiniteChartHomeomorph F hF.2.2 z,
    hF.finiteChartHomeomorph_ne_zero z.2⟩
  invFun z := ⟨(riemannSphereFiniteChartHomeomorph F hF.2.2).symm z, by
    intro hzero
    apply z.2
    calc
      (z : ℂ) = riemannSphereFiniteChartHomeomorph F hF.2.2
          ((riemannSphereFiniteChartHomeomorph F hF.2.2).symm z) :=
        ((riemannSphereFiniteChartHomeomorph F hF.2.2).apply_symm_apply z).symm
      _ = riemannSphereFiniteChartHomeomorph F hF.2.2 0 := by rw [hzero]
      _ = 0 := hF.finiteChart_fixes_zero_one.1⟩
  left_inv z := Subtype.ext
    ((riemannSphereFiniteChartHomeomorph F hF.2.2).symm_apply_apply z)
  right_inv z := Subtype.ext
    ((riemannSphereFiniteChartHomeomorph F hF.2.2).apply_symm_apply z)
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/--
%%handwave
name:
  Ambient map of the punctured finite chart
statement:
  If $F$ fixes $0$, $1$, and $\infty$, then the ambient representative of
  its finite-chart homeomorphism restricted to $\mathbb C^\times$ agrees on
  all of $\mathbb C$ with the whole-plane finite-chart map $f$.
proof:
  At nonzero points this is the definition of the restricted homeomorphism.
  At $0$, both ambient representatives equal $0$ because $F$ fixes $0$.
-/
@[simp]
theorem ambientMap_normalizedFiniteChartPuncturedHomeomorph
    (F : RiemannSphere ≃ₜ RiemannSphere)
    (hF : IsNormalizedRiemannSphereHomeomorph F) (z : ℂ) :
    ambientMap (normalizedFiniteChartPuncturedHomeomorph F hF) z =
      riemannSphereFiniteChartHomeomorph F hF.2.2 z := by
  by_cases hz : z = 0
  · subst z
    simp [ambientMap, hF.finiteChart_fixes_zero_one.1]
  · let z0 : ({0}ᶜ : Set ℂ) := ⟨z, hz⟩
    rw [ambientMap_apply _ z0]
    rfl

/--
%%handwave
name:
  Quasiconformality of a normalized punctured finite chart from its finite chart
statement:
  Let $F$ fix $0$, $1$, and $\infty$. If its finite-to-finite standard-chart
  homeomorphism is $K$-quasiconformal, then its restriction
  $f:\mathbb C^\times\to\mathbb C^\times$ is $K$-quasiconformal.
proof:
  Normalization makes the finite-to-finite source equal to $\mathbb C$.
  Restrict the given quasiconformality assertion to the open punctured plane
  and identify its ambient representative with the restricted finite chart.
-/
theorem isKQuasiconformalBetween_normalizedFiniteChartPunctured_of_finiteChart
    {K : ℝ} {F : RiemannSphere ≃ₜ RiemannSphere}
    (hF : IsNormalizedRiemannSphereHomeomorph F)
    (hfinite : IsKQuasiconformalBetween K
      (riemannSphereChartHomeomorph F .finite .finite)) :
    IsKQuasiconformalBetween K
      (normalizedFiniteChartPuncturedHomeomorph F hF) := by
  have hsource :=
    riemannSphere_finiteChartRepresentation_source_eq_univ_of_map_infty
      F hF.2.2
  apply hfinite.restrict isOpen_compl_singleton
    isOpen_compl_singleton
    (by rw [hsource]; exact Set.subset_univ _)
  intro z
  change riemannSphereFiniteChartHomeomorph F hF.2.2 z =
    riemannSphereChartHomeomorph F .finite .finite ⟨z, _⟩
  rw [← ambientMap_finiteChartHomeomorph_apply F hF.2.2 z]
  exact ambientMap_apply (riemannSphereChartHomeomorph F .finite .finite)
    ⟨z, by rw [hsource]; exact Set.mem_univ _⟩

/--
%%handwave
name:
  Quasiconformality of the punctured finite chart
statement:
  If a normalized sphere homeomorphism $F$ is $K$-quasiconformal, then its
  finite-chart restriction
  $f:\mathbb C^\times\to\mathbb C^\times$ is $K$-quasiconformal.
proof:
  Normalization makes the full finite-to-finite chart domain equal to
  $\mathbb C$. Restrict that chartwise quasiconformality assertion to the
  open punctured plane and identify its ambient representative with $f$.
-/
theorem IsKQuasiconformalRiemannSphere.normalizedFiniteChartPunctured
    {K : ℝ} {F : RiemannSphere ≃ₜ RiemannSphere}
    (hqc : IsKQuasiconformalRiemannSphere K F)
    (hF : IsNormalizedRiemannSphereHomeomorph F) :
    IsKQuasiconformalBetween K
      (normalizedFiniteChartPuncturedHomeomorph F hF) := by
  exact isKQuasiconformalBetween_normalizedFiniteChartPunctured_of_finiteChart
    hF (hqc .finite .finite)

/--
%%handwave
name:
  Inversion of the punctured plane
statement:
  Complex inversion $z\mapsto z^{-1}$ is an involutive homeomorphism of
  $\mathbb C^\times$.
-/
def puncturedPlaneInversionHomeomorph :
    ({0}ᶜ : Set ℂ) ≃ₜ ({0}ᶜ : Set ℂ) where
  toFun z := ⟨(z : ℂ)⁻¹, inv_ne_zero z.2⟩
  invFun z := ⟨(z : ℂ)⁻¹, inv_ne_zero z.2⟩
  left_inv z := Subtype.ext (inv_inv (z : ℂ))
  right_inv z := Subtype.ext (inv_inv (z : ℂ))
  continuous_toFun := by
    exact continuousOn_inv₀.mapsToRestrict (fun z hz ↦ inv_ne_zero hz)
  continuous_invFun := by
    exact continuousOn_inv₀.mapsToRestrict (fun z hz ↦ inv_ne_zero hz)

/--
%%handwave
name:
  Inversion is conformal on the punctured plane
statement:
  The homeomorphism $\iota:\mathbb C^\times\to\mathbb C^\times$ given by
  $\iota(z)=z^{-1}$ is $1$-quasiconformal.
proof:
  It is the finite fractional-linear homeomorphism associated with
  $\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right)$. Restrict the
  one-quasiconformality of that Möbius formula to its pole-free domain
  $\mathbb C^\times$.
-/
theorem isOneQuasiconformalBetween_puncturedPlaneInversionHomeomorph :
    IsKQuasiconformalBetween 1 puncturedPlaneInversionHomeomorph := by
  have hsub : ({0}ᶜ : Set ℂ) ⊆
      mobiusFiniteDomain standardChartInversionRepresentative := by
    intro z hz
    change 1 * z + 0 ≠ 0
    simpa using hz
  exact (isOneQuasiconformalBetween_mobiusFiniteHomeomorph
    standardChartInversionRepresentative).restrict
      isOpen_compl_singleton isOpen_compl_singleton hsub (fun z ↦ by
        change (z : ℂ)⁻¹ =
          mobiusFiniteFormula standardChartInversionRepresentative z
        simp [mobiusFiniteFormula, mobiusFiniteNum, mobiusFiniteDenom,
          standardChartInversionRepresentative])

set_option maxHeartbeats 2000000 in
/--
%%handwave
name:
  Target inversion preserves quasiconformal distortion
statement:
  If $F:\Omega\to\mathbb C^\times$ is $K$-quasiconformal, then
  $\iota\circ F:\Omega\to\mathbb C^\times$ is $K$-quasiconformal, where
  $\iota(w)=w^{-1}$.
proof:
  Compose the orientation witnesses. The complex Sobolev outer chain rule
  gives $D(\iota\circ F)=D\iota(F)\circ DF$. Since $D\iota(F)$ is
  complex-linear and nonzero, target conformal invariance preserves the
  metric-distortion inequality.
-/
theorem IsKQuasiconformalBetween.postcomp_puncturedPlaneInversion
    {K : ℝ} {Ω : Set ℂ} {F : Ω ≃ₜ ({0}ᶜ : Set ℂ)}
    (hF : IsKQuasiconformalBetween K F) :
    IsKQuasiconformalBetween K
      (F.trans puncturedPlaneInversionHomeomorph) := by
  obtain ⟨df, hdf, hdist⟩ := hF.2.2.2
  let dcomp : ℂ → ℂ →L[ℝ] ℂ := fun z ↦
    (fderiv ℝ (fun w : ℂ ↦ w⁻¹) (ambientMap F z)).comp (df z)
  have hcomp0 := hF.postcomp_continuous_isLocalW12On hdf
    isLocalW12On_inversion (continuousOn_inv₀ :
      ContinuousOn (fun z : ℂ ↦ z⁻¹) ({0}ᶜ : Set ℂ))
  have hcomp : IsLocalW12On Ω
      (ambientMap (F.trans puncturedPlaneInversionHomeomorph)) dcomp := by
    apply hcomp0.congr_ae
    filter_upwards [ae_restrict_mem hdf.1.measurableSet] with z hz
    simp [ambientMap, hz, puncturedPlaneInversionHomeomorph]
  have hdistComp : ∀ᵐ z ∂volume.restrict Ω,
      ‖dcomp z‖ ^ 2 ≤ K * weakJacobian (dcomp z) := by
    filter_upwards [hdist, ae_restrict_mem hdf.1.measurableSet] with z hz hzΩ
    have hFz0 : ambientMap F z ≠ 0 := by
      rw [ambientMap_apply F ⟨z, hzΩ⟩]
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
        (F ⟨z, hzΩ⟩).2
    dsimp only [dcomp]
    rw [fderiv_inversion _ hFz0]
    exact distortion_complexLinear_comp _ _ _ hz
  exact ⟨hF.1, isOpen_compl_singleton,
    hF.2.2.1.trans
      isOneQuasiconformalBetween_puncturedPlaneInversionHomeomorph.2.2.1,
    dcomp, hcomp, hdistComp⟩

set_option maxHeartbeats 2000000 in
/--
%%handwave
name:
  Source inversion preserves quasiconformal distortion
statement:
  If $F:\mathbb C^\times\to\Omega'$ is $K$-quasiconformal, then
  $F\circ\iota:\mathbb C^\times\to\Omega'$ is $K$-quasiconformal, where
  $\iota(z)=z^{-1}$.
proof:
  Compose the orientation witnesses. The Sobolev source-coordinate chain
  rule gives $D(F\circ\iota)=DF(\iota(z))\circ D\iota(z)$, and conformal
  source-coordinate invariance preserves the metric-distortion inequality.
-/
theorem IsKQuasiconformalBetween.precomp_puncturedPlaneInversion
    {K : ℝ} {Ω' : Set ℂ} {F : ({0}ᶜ : Set ℂ) ≃ₜ Ω'}
    (hF : IsKQuasiconformalBetween K F) :
    IsKQuasiconformalBetween K
      (puncturedPlaneInversionHomeomorph.trans F) := by
  obtain ⟨df, hdf, hdist⟩ := hF.2.2.2
  let dcomp : ℂ → ℂ →L[ℝ] ℂ := fun z ↦
    (df z⁻¹).comp (fderiv ℝ (fun w : ℂ ↦ w⁻¹) z)
  have hcomp0 := hdf.comp_inversion
  have hcomp : IsLocalW12On ({0}ᶜ : Set ℂ)
      (ambientMap (puncturedPlaneInversionHomeomorph.trans F)) dcomp := by
    apply hcomp0.congr_ae
    filter_upwards [ae_restrict_mem isOpen_compl_singleton.measurableSet]
      with z hz
    have hz0 : z ≠ 0 := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hz
    simp [ambientMap, hz, hz0, puncturedPlaneInversionHomeomorph]
  exact ⟨hF.1, hF.2.1,
    isOneQuasiconformalBetween_puncturedPlaneInversionHomeomorph.2.2.1.trans
      hF.2.2.1,
    dcomp, hcomp, metricDistortion_comp_inversion hdist⟩

/--
%%handwave
name:
  Reciprocal-chart formula in finite coordinates
statement:
  If $F$ is normalized with finite-chart representative $f$ and
  reciprocal-chart representative $g$, then for every $z\in\mathbb C$,
  $$
    g(z)=\frac{1}{f(1/z)},
  $$
  using the totalized convention $0^{-1}=0$.
proof:
  At $z=0$, both sides vanish by normalization. For $z\ne0$, the inverse
  reciprocal source chart sends $z$ to the finite point $z^{-1}$; return
  from the finite chart after applying $F$, then take its reciprocal target
  coordinate.
-/
theorem riemannSphereInfinityChartHomeomorph_eq_inv_finiteChart_inv
    {F : RiemannSphere ≃ₜ RiemannSphere}
    (hF : IsNormalizedRiemannSphereHomeomorph F) (z : ℂ) :
    riemannSphereInfinityChartHomeomorph F hF.1 z =
      (riemannSphereFiniteChartHomeomorph F hF.2.2 z⁻¹)⁻¹ := by
  by_cases hz : z = 0
  · subst z
    simp [hF.infinityChart_fixes_zero_one.1,
      hF.finiteChart_fixes_zero_one.1]
  · rw [riemannSphereInfinityChartHomeomorph_apply]
    have hsource : riemannSphereInfinityChart.symm z =
        ((z⁻¹ : ℂ) : RiemannSphere) := by
      simp [riemannSphereInfinityChart_symm_apply,
        riemannSphereInv_coe_of_ne_zero hz]
    rw [hsource]
    rw [← coe_riemannSphereFiniteChartHomeomorph_apply F hF.2.2 z⁻¹]
    exact riemannSphereInfinityChart_coe_of_ne_zero
      (hF.finiteChartHomeomorph_ne_zero (inv_ne_zero hz))

/--
%%handwave
name:
  Source of the finite-to-reciprocal chart of a normalized sphere map
statement:
  If $F$ fixes $0$, $1$, and $\infty$, then the source of its
  finite-to-reciprocal standard-chart representation is
  $\mathbb C^\times$.
proof:
  A finite point $z$ is excluded exactly when $F(z)=0$, because reciprocal
  target coordinates exclude $0$. Injectivity and $F(0)=0$ make this
  equivalent to $z=0$.
-/
theorem riemannSphere_finiteInfinityChartRepresentation_source_eq_compl_zero
    {F : RiemannSphere ≃ₜ RiemannSphere}
    (hF : IsNormalizedRiemannSphereHomeomorph F) :
    (riemannSphereChartRepresentation F .finite .infinity).source =
      ({0}ᶜ : Set ℂ) := by
  ext z
  simp [riemannSphereChartRepresentation, riemannSphereStandardChart,
    riemannSphereInfinityChart]
  constructor
  · intro hJ hz
    subst z
    exact hJ (by simp [hF.1])
  · intro hz hJ
    have hback := congrArg riemannSphereInv hJ
    have hFz0 : F (((z : ℂ) : RiemannSphere)) =
        (((0 : ℂ) : ℂ) : RiemannSphere) := by
      simpa only [riemannSphereInv_inv, riemannSphereInv_infty] using hback
    have hzSphere : (((z : ℂ) : RiemannSphere)) =
        (((0 : ℂ) : ℂ) : RiemannSphere) :=
      F.injective (hFz0.trans hF.1.symm)
    exact hz (OnePoint.coe_injective hzSphere)

/--
%%handwave
name:
  Source of the reciprocal-to-finite chart of a normalized sphere map
statement:
  If $F$ fixes $0$, $1$, and $\infty$, then the source of its
  reciprocal-to-finite standard-chart representation is
  $\mathbb C^\times$.
proof:
  Reciprocal coordinate $0$ represents $\infty$, which maps to $\infty$ and
  is excluded by the finite target chart. Conversely, injectivity and
  $F(\infty)=\infty$ show that no nonzero reciprocal coordinate is excluded.
-/
theorem riemannSphere_infinityFiniteChartRepresentation_source_eq_compl_zero
    {F : RiemannSphere ≃ₜ RiemannSphere}
    (hF : IsNormalizedRiemannSphereHomeomorph F) :
    (riemannSphereChartRepresentation F .infinity .finite).source =
      ({0}ᶜ : Set ℂ) := by
  ext z
  simp [riemannSphereChartRepresentation, riemannSphereStandardChart,
    riemannSphereInfinityChart]
  constructor
  · intro hFJ hz
    subst z
    exact hFJ (by
      simpa [riemannSphereInvHomeomorph] using hF.2.2)
  · intro hz hFJ
    have hJInf : riemannSphereInv (((z : ℂ) : RiemannSphere)) =
        OnePoint.infty :=
      F.injective (hFJ.trans hF.2.2.symm)
    have hback := congrArg riemannSphereInv hJInf
    exact hz (OnePoint.coe_injective (by
      simpa only [riemannSphereInv_inv, riemannSphereInv_infty] using hback))

/--
%%handwave
name:
  Finite-to-reciprocal chart as target inversion
statement:
  If $F$ is normalized, then its finite-to-reciprocal standard-chart
  homeomorphism on $\mathbb C^\times$ is
  $$
    z\longmapsto f(z)^{-1},
  $$
  where $f$ is the whole-plane finite-chart representative.
proof:
  The finite source chart represents $z$ by the same finite sphere point.
  Apply $F$, return through the finite chart, and use that the reciprocal
  target chart is inversion of the finite coordinate.
-/
theorem riemannSphere_finiteInfinityChartHomeomorph_apply
    {F : RiemannSphere ≃ₜ RiemannSphere}
    (hF : IsNormalizedRiemannSphereHomeomorph F)
    (z : (riemannSphereChartRepresentation F .finite .infinity).source) :
    (riemannSphereChartHomeomorph F .finite .infinity z : ℂ) =
      ((normalizedFiniteChartPuncturedHomeomorph F hF).trans
        puncturedPlaneInversionHomeomorph
        ⟨(z : ℂ), by
          rw [← riemannSphere_finiteInfinityChartRepresentation_source_eq_compl_zero hF]
          exact z.2⟩ : ℂ) := by
  change riemannSphereInfinityChart (F (((z : ℂ) : RiemannSphere))) =
    (riemannSphereFiniteChartHomeomorph F hF.2.2 (z : ℂ))⁻¹
  rw [← coe_riemannSphereFiniteChartHomeomorph_apply F hF.2.2 (z : ℂ)]
  exact riemannSphereInfinityChart_coe_of_ne_zero
    (hF.finiteChartHomeomorph_ne_zero (by
      have hzmem : (z : ℂ) ∈ ({0}ᶜ : Set ℂ) := by
        rw [← riemannSphere_finiteInfinityChartRepresentation_source_eq_compl_zero hF]
        exact z.2
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hzmem))

/--
%%handwave
name:
  Reciprocal-to-finite chart as source inversion
statement:
  If $F$ is normalized, then its reciprocal-to-finite standard-chart
  homeomorphism on $\mathbb C^\times$ is
  $$
    z\longmapsto f(z^{-1}),
  $$
  where $f$ is the whole-plane finite-chart representative.
proof:
  A nonzero reciprocal source coordinate $z$ represents the finite sphere
  point $z^{-1}$. Apply $F$ and read the result in the finite target chart.
-/
theorem riemannSphere_infinityFiniteChartHomeomorph_apply
    {F : RiemannSphere ≃ₜ RiemannSphere}
    (hF : IsNormalizedRiemannSphereHomeomorph F)
    (z : (riemannSphereChartRepresentation F .infinity .finite).source) :
    (riemannSphereChartHomeomorph F .infinity .finite z : ℂ) =
      (puncturedPlaneInversionHomeomorph.trans
        (normalizedFiniteChartPuncturedHomeomorph F hF)
        ⟨(z : ℂ), by
          rw [← riemannSphere_infinityFiniteChartRepresentation_source_eq_compl_zero hF]
          exact z.2⟩ : ℂ) := by
  change riemannSphereFiniteChart
      (F (riemannSphereInv (((z : ℂ) : RiemannSphere)))) =
    riemannSphereFiniteChartHomeomorph F hF.2.2 ((z : ℂ)⁻¹)
  have hz0 : (z : ℂ) ≠ 0 := by
    have hzmem : (z : ℂ) ∈ ({0}ᶜ : Set ℂ) := by
      rw [← riemannSphere_infinityFiniteChartRepresentation_source_eq_compl_zero hF]
      exact z.2
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hzmem
  rw [riemannSphereInv_coe_of_ne_zero hz0]
  exact (riemannSphereFiniteChartHomeomorph_apply F hF.2.2 _).symm

/--
%%handwave
name:
  Standard-chart criterion from the two diagonal charts
statement:
  Let $F$ be a normalized sphere homeomorphism. If the finite-to-finite
  standard chart of $F$ and the finite-to-finite standard chart of
  $J\circ F\circ J$ are both $K$-quasiconformal, then $F$ is
  $K$-quasiconformal in all four finite or reciprocal standard-chart pairs.
proof:
  The second assumption is exactly the reciprocal-to-reciprocal chart of
  $F$. Restrict the first diagonal chart to $\mathbb C^\times$. The two
  mixed charts are respectively its postcomposition and precomposition by
  inversion, which preserve the same distortion constant.
-/
theorem isKQuasiconformalRiemannSphere_of_finiteChart_and_invConjugate_finiteChart
    {K : ℝ} {F : RiemannSphere ≃ₜ RiemannSphere}
    (hF : IsNormalizedRiemannSphereHomeomorph F)
    (hfinite : IsKQuasiconformalBetween K
      (riemannSphereChartHomeomorph F .finite .finite))
    (hinvfinite : IsKQuasiconformalBetween K
      (riemannSphereChartHomeomorph (riemannSphereInvConjugate F)
        .finite .finite)) :
    IsKQuasiconformalRiemannSphere K F := by
  have hF0 :=
    isKQuasiconformalBetween_normalizedFiniteChartPunctured_of_finiteChart
      hF hfinite
  have hfininf0 := hF0.postcomp_puncturedPlaneInversion
  have hinffin0 := hF0.precomp_puncturedPlaneInversion
  have hfininf : IsKQuasiconformalBetween K
      (riemannSphereChartHomeomorph F .finite .infinity) := by
    let U := (riemannSphereChartRepresentation F .finite .infinity).source
    have hsub : U ⊆ ({0}ᶜ : Set ℂ) := by
      change (riemannSphereChartRepresentation F .finite .infinity).source ⊆
        ({0}ᶜ : Set ℂ)
      rw [riemannSphere_finiteInfinityChartRepresentation_source_eq_compl_zero hF]
    apply hfininf0.restrict
      (riemannSphereChartRepresentation F .finite .infinity).open_source
      (riemannSphereChartRepresentation F .finite .infinity).open_target
      hsub
    intro z
    exact riemannSphere_finiteInfinityChartHomeomorph_apply hF z
  have hinffin : IsKQuasiconformalBetween K
      (riemannSphereChartHomeomorph F .infinity .finite) := by
    let U := (riemannSphereChartRepresentation F .infinity .finite).source
    have hsub : U ⊆ ({0}ᶜ : Set ℂ) := by
      change (riemannSphereChartRepresentation F .infinity .finite).source ⊆
        ({0}ᶜ : Set ℂ)
      rw [riemannSphere_infinityFiniteChartRepresentation_source_eq_compl_zero hF]
    apply hinffin0.restrict
      (riemannSphereChartRepresentation F .infinity .finite).open_source
      (riemannSphereChartRepresentation F .infinity .finite).open_target
      hsub
    intro z
    exact riemannSphere_infinityFiniteChartHomeomorph_apply hF z
  have hinfinf : IsKQuasiconformalBetween K
      (riemannSphereChartHomeomorph F .infinity .infinity) := by
    rw [riemannSphereChartHomeomorph]
    have hrep :=
      riemannSphereChartRepresentation_invConjugate F .finite .finite
    simp only [RiemannSphereChartIndex.swap] at hrep
    rw [← hrep]
    exact hinvfinite
  intro source target
  cases source <;> cases target
  · exact hfinite
  · exact hfininf
  · exact hinffin
  · exact hinfinf

/--
%%handwave
name:
  Uniform convergence under inversion conjugation
statement:
  If sphere maps $F_n$ converge uniformly to $G$, then
  $J\circ F_n\circ J$ converges uniformly to $J\circ G\circ J$, where
  $J$ is spherical inversion.
proof:
  Precomposition preserves uniform convergence. Spherical inversion is
  uniformly continuous because the sphere is compact, so postcomposition by
  $J$ also preserves uniform convergence.
-/
theorem tendstoUniformly_invConjugate
    {F : ℕ → RiemannSphere ≃ₜ RiemannSphere}
    {G : RiemannSphere ≃ₜ RiemannSphere}
    (h : TendstoUniformly (fun n ↦ F n) G atTop) :
    TendstoUniformly (fun n ↦ riemannSphereInvConjugate (F n))
      (riemannSphereInvConjugate G) atTop := by
  have hpre := h.comp riemannSphereInvHomeomorph
  have hJuc : UniformContinuous (riemannSphereInvHomeomorph :
      RiemannSphere → RiemannSphere) :=
    CompactSpace.uniformContinuous_of_continuous riemannSphereInv_continuous
  have hpost := hJuc.comp_tendstoUniformly hpre
  simpa [riemannSphereInvConjugate, Function.comp_def] using hpost

set_option maxHeartbeats 3000000 in
/--
%%handwave
name:
  Beltrami equation for the inversion-conjugate finite chart
statement:
  Let $F$ be a normalized $K$-quasiconformal sphere homeomorphism with
  finite-chart representative $f\in W^{1,2}_{\mathrm{loc}}(\mathbb C)$ and
  weak differential $Df$ satisfying
  $$
    \partial_{\bar z}f=\mu\,\partial_zf
    \quad\text{almost everywhere on }\mathbb C.
  $$
  If $H=J\circ F\circ J$ for spherical inversion $J$, then the finite-chart
  representative of $H$ has a whole-plane weak differential $DH$ satisfying
  $$
    \partial_{\bar z}H=
      \left(\mu(z^{-1})\frac{\overline{-z^{-2}}}{-z^{-2}}\right)
      \partial_zH
  $$
  almost everywhere on $\mathbb C$.
proof:
  Restrict $f$ to the punctured plane. Postcompose it with inversion using
  the [complex Sobolev outer chain rule](lean:JJMath.Quasiconformal.IsKQuasiconformalBetween.postcomp_continuous_isLocalW12On), which leaves the Beltrami coefficient unchanged, then precompose with inversion using the reciprocal source-coordinate formula. This gives the displayed coefficient for $z\mapsto1/f(1/z)$ on $\mathbb C^\times$. The inversion-conjugate sphere map is already globally Sobolev in its finite chart; uniqueness of weak differentials identifies its differential with the chain-rule field off $0$. Since the omitted singleton is null, the equation holds on the whole plane.
-/
theorem IsKQuasiconformalRiemannSphere.exists_invConjugate_finiteChart_weakDifferential_weakBeltrami
    {K : ℝ} {F : RiemannSphere ≃ₜ RiemannSphere}
    (hqc : IsKQuasiconformalRiemannSphere K F)
    (hF : IsNormalizedRiemannSphereHomeomorph F)
    {df : ℂ → ℂ →L[ℝ] ℂ}
    (hdf : IsLocalW12On Set.univ
      (riemannSphereFiniteChartHomeomorph F hF.2.2) df)
    {μ : ℂ → ℂ} (hbel : WeakBeltramiEquationOn Set.univ μ df) :
    ∃ dH : ℂ → ℂ →L[ℝ] ℂ,
      IsLocalW12On Set.univ
        (riemannSphereFiniteChartHomeomorph (riemannSphereInvConjugate F)
          hF.invConjugate.2.2) dH ∧
      WeakBeltramiEquationOn Set.univ
        (inversionPullbackBeltrami μ) dH := by
  let f := riemannSphereFiniteChartHomeomorph F hF.2.2
  let F0 := normalizedFiniteChartPuncturedHomeomorph F hF
  have hF0qc : IsKQuasiconformalBetween K F0 :=
    hqc.normalizedFiniteChartPunctured hF
  have hF0ambient (z : ℂ) : ambientMap F0 z = f z := by
    exact ambientMap_normalizedFiniteChartPuncturedHomeomorph F hF z
  have hdf0 : IsLocalW12On ({0}ᶜ : Set ℂ) (ambientMap F0) df := by
    apply (hdf.mono isOpen_compl_singleton (Set.subset_univ _)).congr_ae
    filter_upwards with z
    simpa only [f] using hF0ambient z
  have hpost := hF0qc.postcomp_continuous_isLocalW12On hdf0
    isLocalW12On_inversion (continuousOn_inv₀ :
      ContinuousOn (fun z : ℂ ↦ z⁻¹) ({0}ᶜ : Set ℂ))
  have hpost' : IsLocalW12On ({0}ᶜ : Set ℂ)
      (fun z ↦ (f z)⁻¹)
      (fun z ↦ (fderiv ℝ (fun w : ℂ ↦ w⁻¹) (f z)).comp (df z)) := by
    simpa only [hF0ambient] using hpost
  have hpostBel : WeakBeltramiEquationOn ({0}ᶜ : Set ℂ) μ
      (fun z ↦ (fderiv ℝ (fun w : ℂ ↦ w⁻¹) (f z)).comp (df z)) := by
    apply (hbel.mono (Set.subset_univ _)).postcomp_inversion
      isOpen_compl_singleton.measurableSet
    intro z hz
    exact hF.finiteChartHomeomorph_ne_zero hz
  have hcandW := hpost'.comp_inversion
  have hcandBel := hpostBel.comp_inversion
  let dcand : ℂ → ℂ →L[ℝ] ℂ := fun z ↦
    ((fderiv ℝ (fun w : ℂ ↦ w⁻¹) (f z⁻¹)).comp (df z⁻¹)).comp
      (fderiv ℝ (fun w : ℂ ↦ w⁻¹) z)
  have hcandW' : IsLocalW12On ({0}ᶜ : Set ℂ)
      (fun z ↦ (f z⁻¹)⁻¹) dcand := hcandW
  have hcandBel' : WeakBeltramiEquationOn ({0}ᶜ : Set ℂ)
      (inversionPullbackBeltrami μ) dcand := hcandBel
  obtain ⟨dH, hH⟩ := hqc.invConjugate.exists_finiteChart_weakDifferential
    hF.invConjugate
  have hvalue (z : ℂ) :
      riemannSphereFiniteChartHomeomorph (riemannSphereInvConjugate F)
          hF.invConjugate.2.2 z = (f z⁻¹)⁻¹ := by
    rw [riemannSphereFiniteChartHomeomorph_invConjugate_apply hF]
    exact riemannSphereInfinityChartHomeomorph_eq_inv_finiteChart_inv hF z
  have hcandAsH : IsLocalW12On ({0}ᶜ : Set ℂ)
      (riemannSphereFiniteChartHomeomorph (riemannSphereInvConjugate F)
        hF.invConjugate.2.2) dcand := by
    apply hcandW'.congr_ae
    filter_upwards with z
    exact hvalue z
  have hHpunct : IsLocalW12On ({0}ᶜ : Set ℂ)
      (riemannSphereFiniteChartHomeomorph (riemannSphereInvConjugate F)
        hF.invConjugate.2.2) dH :=
    hH.mono (U := ({0}ᶜ : Set ℂ)) isOpen_compl_singleton
      (Set.subset_univ _)
  have hdEq : dcand =ᵐ[volume.restrict ({0}ᶜ : Set ℂ)] dH :=
    hcandAsH.weakDifferential_ae_eq hHpunct
  have hbelHpunct : WeakBeltramiEquationOn ({0}ᶜ : Set ℂ)
      (inversionPullbackBeltrami μ) dH :=
    hcandBel'.congr_derivative_ae hdEq
  have hbelH : WeakBeltramiEquationOn Set.univ
      (inversionPullbackBeltrami μ) dH := by
    simpa [WeakBeltramiEquationOn, restrict_compl_singleton] using hbelHpunct
  exact ⟨dH, hH, hbelH⟩

/--
%%handwave
name:
  Uniform finite-chart differential energy on a fixed disk
statement:
  Let $K,R\in\mathbb R$. There is a finite extended nonnegative number $C$
  such that every normalized $K$-quasiconformal sphere homeomorphism has a
  finite-chart weak differential $Df$ on $\mathbb C$ satisfying
  $$
    \int_{\overline B(0,R)}
      \lVert Df(z)\rVert_{\mathrm{op}}^2\,dz\leq C.
  $$
proof:
  The finite-chart images of $\overline B(0,R)$ lie in one fixed bounded
  disk. The [differential energy is at most $K$ times image area](lean:JJMath.Quasiconformal.IsKQuasiconformalBetween.lintegral_norm_weakDifferential_sq_le_volume_image),
  so monotonicity of planar measure bounds every energy by $K$ times the
  finite area of that target disk. Identify the chartwise ambient
  representative with the whole-plane finite-chart homeomorphism.
-/
theorem exists_uniform_finiteChart_weakDifferential_energy_bound
    (K R : ℝ) :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (F : RiemannSphere ≃ₜ RiemannSphere)
        (_hqc : IsKQuasiconformalRiemannSphere K F)
        (hF : IsNormalizedRiemannSphereHomeomorph F),
        ∃ df : ℂ → ℂ →L[ℝ] ℂ,
          IsLocalW12On Set.univ
            (riemannSphereFiniteChartHomeomorph F hF.2.2) df ∧
          (∫⁻ z in Metric.closedBall (0 : ℂ) R,
              ENNReal.ofReal (‖df z‖ ^ 2) ∂volume) ≤ C := by
  obtain ⟨M, hM, hbound⟩ :=
    exists_uniform_finiteChart_norm_bound_on_closedBall K R
  let C : ℝ≥0∞ :=
    ENNReal.ofReal K * volume (Metric.closedBall (0 : ℂ) M)
  have hCtop : C < ∞ := by
    dsimp [C]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top
  refine ⟨C, hCtop, ?_⟩
  intro F hqc hF
  let H := riemannSphereChartHomeomorph F .finite .finite
  have hsource :=
    riemannSphere_finiteChartRepresentation_source_eq_univ_of_map_infty
      F hF.2.2
  have hplanar := hqc .finite .finite
  obtain ⟨df, hdf, hdist⟩ := hplanar.2.2.2
  have hdf_univ : IsLocalW12On Set.univ (ambientMap H) df := by
    simpa only [H, hsource] using hdf
  have hdf_finite : IsLocalW12On Set.univ
      (riemannSphereFiniteChartHomeomorph F hF.2.2) df := by
    apply hdf_univ.congr_ae
    filter_upwards with z
    exact (ambientMap_finiteChartHomeomorph_apply F hF.2.2 z).symm
  refine ⟨df, hdf_finite, ?_⟩
  have hball_source : Metric.closedBall (0 : ℂ) R ⊆
      (riemannSphereChartRepresentation F .finite .finite).source := by
    rw [hsource]
    exact Set.subset_univ _
  have henergy :=
    hplanar.lintegral_norm_weakDifferential_sq_le_volume_image hdf
      (measurableSet_closedBall :
        MeasurableSet (Metric.closedBall (0 : ℂ) R))
      hball_source
  have himage : ambientMap H '' Metric.closedBall (0 : ℂ) R ⊆
      Metric.closedBall (0 : ℂ) M := by
    rintro y ⟨z, hz, rfl⟩
    rw [ambientMap_finiteChartHomeomorph_apply F hF.2.2]
    simp only [Metric.mem_closedBall, dist_zero_right]
    apply (hbound F hqc hF z ?_).le
    simpa [Metric.mem_closedBall, dist_zero_right] using hz
  exact henergy.trans (by
    simpa [C] using
      mul_le_mul_right (measure_mono (μ := volume) himage) (ENNReal.ofReal K))

/--
%%handwave
name:
  Uniform finite-chart energy for every weak differential representative
statement:
  Let $K,R\in\mathbb R$. There is a finite $C\in[0,\infty]$ such that, for
  every normalized $K$-quasiconformal sphere homeomorphism with finite-chart
  representative $f$, every weak differential $Df$ of $f$ satisfies
  $$
    \int_{\overline B(0,R)}\lVert Df(z)\rVert_{\mathrm{op}}^2\,dz\leq C.
  $$
proof:
  Choose the uniformly energy-bounded weak differential supplied by the
  finite-chart area estimate. Weak differentials of the same local Sobolev
  map agree almost everywhere, so the squared-norm integrals agree on the
  disk.
-/
theorem exists_uniform_finiteChart_weakDifferential_energy_bound_of_isLocalW12On
    (K R : ℝ) :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (F : RiemannSphere ≃ₜ RiemannSphere)
        (_hqc : IsKQuasiconformalRiemannSphere K F)
        (hF : IsNormalizedRiemannSphereHomeomorph F)
        (df : ℂ → ℂ →L[ℝ] ℂ),
        IsLocalW12On Set.univ
          (riemannSphereFiniteChartHomeomorph F hF.2.2) df →
          (∫⁻ z in Metric.closedBall (0 : ℂ) R,
              ENNReal.ofReal (‖df z‖ ^ 2) ∂volume) ≤ C := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_uniform_finiteChart_weakDifferential_energy_bound K R
  refine ⟨C, hC, ?_⟩
  intro F hqc hF df hdf
  obtain ⟨dg, hdg, henergy⟩ := hbound F hqc hF
  have heq_univ := hdf.weakDifferential_ae_eq hdg
  have heq : df =ᵐ[volume.restrict (Metric.closedBall (0 : ℂ) R)] dg := by
    apply ae_restrict_of_ae_restrict_of_subset (Set.subset_univ _)
    simpa using heq_univ
  refine (lintegral_congr_ae ?_).trans_le henergy
  filter_upwards [heq] with z hz
  rw [hz]

set_option maxHeartbeats 1000000 in
/--
%%handwave
name:
  An $L^2$ norm bound from a finite squared-energy bound
statement:
  Let $u\in L^2(X,\mu;E)$ and suppose
  $$
    \int_X\lVert u(x)\rVert^2\,d\mu(x)\leq C<\infty.
  $$
  Then the corresponding $L^2$ class satisfies
  $$
    \lVert u\rVert_2\leq\max\{C,1\}.
  $$
proof:
  The square of the $L^2$ seminorm is the displayed integral. If the
  seminorm is at most one the conclusion is immediate; otherwise it is at
  most its square. Convert the resulting finite extended-nonnegative bound
  to a real norm bound.
-/
theorem L2.complex_norm_toLp_le_max_energy_toReal
    {μ : Measure ℂ} {u : ℂ → ℂ} (hmem : MemLp u 2 μ)
    {C : ℝ≥0∞} (hC : C < ∞)
    (henergy : (∫⁻ x, ENNReal.ofReal (‖u x‖ ^ 2) ∂μ) ≤ C) :
    ‖hmem.toLp u‖ ≤ (max C 1).toReal := by
  have hBtop : max C 1 < ∞ := max_lt hC ENNReal.one_lt_top
  rw [Lp.norm_toLp]
  apply ENNReal.toReal_mono hBtop.ne
  have hsq : eLpNorm u 2 μ ^ (2 : ℕ) ≤ C :=
    (eLpNorm_two_pow_two_eq_lintegral_ofReal_norm_sq u μ).trans_le henergy
  by_cases hsmall : eLpNorm u 2 μ ≤ 1
  · exact hsmall.trans (le_max_right C 1)
  · have hone : 1 ≤ eLpNorm u 2 μ := (lt_of_not_ge hsmall).le
    calc
      eLpNorm u 2 μ = eLpNorm u 2 μ * 1 := by simp
      _ ≤ eLpNorm u 2 μ * eLpNorm u 2 μ := mul_le_mul_right hone _
      _ = eLpNorm u 2 μ ^ (2 : ℕ) := by ring
      _ ≤ C := hsq
      _ ≤ max C 1 := le_max_left C 1

set_option maxHeartbeats 1000000 in
/--
%%handwave
name:
  Weak subsequence extraction from a uniform square-integral bound
statement:
  Let $u_n:X\to E$ be square-integrable maps into a real Hilbert space. If
  there is a finite $C\in[0,\infty]$ such that
  $$
    \int_X\lVert u_n(x)\rVert^2\,d\mu(x)\leq C
  $$
  for every $n$, then a subsequence of the corresponding $L^2$ classes
  converges weakly in $L^2(X,\mu;E)$.
proof:
  The integral identity for the squared $L^2$ seminorm gives a common finite
  norm bound. Apply weak sequential compactness of bounded sequences in a
  complete real Hilbert space to the Hilbert space $L^2(X,\mu;E)$.
-/
theorem exists_weakly_convergent_L2_subsequence_of_lintegral_norm_sq_le
    {X E : Type} [MeasurableSpace X] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    {μ : Measure X} (u : ℕ → X → E)
    (hmem : ∀ n, MemLp (u n) 2 μ)
    {C : ℝ≥0∞} (hC : C < ∞)
    (henergy : ∀ n,
      (∫⁻ x, ENNReal.ofReal (‖u n x‖ ^ 2) ∂μ) ≤ C) :
    ∃ uLim : Lp E 2 μ, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
        Tendsto
          (fun n ↦ toWeakSpace ℝ (Lp E 2 μ)
            ((hmem (φ n)).toLp (u (φ n))))
          atTop (𝓝 (toWeakSpace ℝ (Lp E 2 μ) uLim)) := by
  let B : ℝ≥0∞ := max C 1
  have hBtop : B < ∞ := by
    exact max_lt hC ENNReal.one_lt_top
  have hnorm : ∀ n,
      ‖(hmem n).toLp (u n)‖ ≤ B.toReal := by
    intro n
    rw [Lp.norm_toLp]
    apply ENNReal.toReal_mono hBtop.ne
    have hsq : eLpNorm (u n) 2 μ ^ (2 : ℕ) ≤ C := by
      exact (eLpNorm_two_pow_two_eq_lintegral_ofReal_norm_sq (u n) μ).trans_le
        (henergy n)
    by_cases hsmall : eLpNorm (u n) 2 μ ≤ 1
    · exact hsmall.trans (le_max_right C 1)
    · have hone : 1 ≤ eLpNorm (u n) 2 μ :=
        (lt_of_not_ge hsmall).le
      calc
        eLpNorm (u n) 2 μ = eLpNorm (u n) 2 μ * 1 := by simp
        _ ≤ eLpNorm (u n) 2 μ * eLpNorm (u n) 2 μ :=
          mul_le_mul_right hone _
        _ = eLpNorm (u n) 2 μ ^ (2 : ℕ) := by ring
        _ ≤ C := hsq
        _ ≤ B := le_max_left C 1
  exact JJMath.Uniformization.hilbert_bounded_sequence_has_weakly_convergent_subsequence
    (fun n ↦ (hmem n).toLp (u n)) ⟨B.toReal, hnorm⟩

/--
%%handwave
name:
  Algebraic restriction between $L^2$ measures
statement:
  If $\nu\leq\mu$, every class in $L^2(\mu;E)$ determines the class of the
  same representative in $L^2(\nu;E)$, giving a real-linear restriction map.
-/
def L2.monoMeasureLinearMap
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] {μ ν : Measure X} (hνμ : ν ≤ μ) :
    Lp E 2 μ →ₗ[ℝ] Lp E 2 ν where
  toFun f := ((Lp.memLp f).mono_measure hνμ).toLp f
  map_add' f g := by
    apply Lp.ext
    filter_upwards [
      MemLp.coeFn_toLp ((Lp.memLp (f + g)).mono_measure hνμ),
      ae_mono hνμ (Lp.coeFn_add f g),
      MemLp.coeFn_toLp ((Lp.memLp f).mono_measure hνμ),
      MemLp.coeFn_toLp ((Lp.memLp g).mono_measure hνμ),
      Lp.coeFn_add
        (((Lp.memLp f).mono_measure hνμ).toLp f)
        (((Lp.memLp g).mono_measure hνμ).toLp g)] with x hfg hadd hf hg hout
    calc
      _ = (f + g : Lp E 2 μ) x := hfg
      _ = f x + g x := by simpa using hadd
      _ = (((Lp.memLp f).mono_measure hνμ).toLp f) x +
          (((Lp.memLp g).mono_measure hνμ).toLp g) x := by rw [hf, hg]
      _ = _ := by simpa using hout.symm
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [
      MemLp.coeFn_toLp ((Lp.memLp (c • f)).mono_measure hνμ),
      ae_mono hνμ (Lp.coeFn_smul c f),
      MemLp.coeFn_toLp ((Lp.memLp f).mono_measure hνμ),
      Lp.coeFn_smul c (((Lp.memLp f).mono_measure hνμ).toLp f)] with x hcf hsm hf hout
    calc
      _ = (c • f : Lp E 2 μ) x := hcf
      _ = c • f x := by simpa using hsm
      _ = c • (((Lp.memLp f).mono_measure hνμ).toLp f) x := by rw [hf]
      _ = _ := by simpa using hout.symm

/--
%%handwave
name:
  Restriction contraction between $L^2$ measures
statement:
  If $\nu\leq\mu$, restriction of representatives defines a bounded
  real-linear map $L^2(\mu;E)\to L^2(\nu;E)$ of operator norm at most one.
-/
def L2.monoMeasure
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] {μ ν : Measure X} (hνμ : ν ≤ μ) :
    Lp E 2 μ →L[ℝ] Lp E 2 ν :=
  LinearMap.mkContinuous (L2.monoMeasureLinearMap hνμ) 1 (by
    intro f
    rw [one_mul]
    change ‖((Lp.memLp f).mono_measure hνμ).toLp f‖ ≤ ‖f‖
    rw [Lp.norm_toLp, Lp.norm_def]
    exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
      (eLpNorm_mono_measure f hνμ))

/--
%%handwave
name:
  Formula for restriction to a smaller measure
statement:
  If $\nu\leq\mu$ and $u\in L^2(\mu;E)$, its image under the canonical
  contraction $L^2(\mu;E)\to L^2(\nu;E)$ is the $L^2(\nu;E)$ class of the
  same representative.
proof:
  This is the definition of the restriction contraction.
-/
@[simp]
theorem L2.monoMeasure_apply
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] {μ ν : Measure X} (hνμ : ν ≤ μ)
    (f : Lp E 2 μ) :
    L2.monoMeasure hνμ f = ((Lp.memLp f).mono_measure hνμ).toLp f := rfl

/--
%%handwave
name:
  Restriction preserves the represented function
statement:
  Let $\nu\leq\mu$ and let $f:X\to E$ belong to both $L^2(\mu;E)$ and
  $L^2(\nu;E)$. Restricting the $L^2(\mu;E)$ class of $f$ gives exactly its
  $L^2(\nu;E)$ class.
proof:
  The chosen representative of the larger-measure class equals $f$ almost
  everywhere for $\mu$, hence also almost everywhere for $\nu$.
-/
theorem L2.monoMeasure_toLp
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] {μ ν : Measure X} (hνμ : ν ≤ μ)
    (f : X → E) (hfμ : MemLp f 2 μ) (hfν : MemLp f 2 ν) :
    L2.monoMeasure hνμ (hfμ.toLp f) = hfν.toLp f := by
  rw [L2.monoMeasure_apply]
  apply MemLp.toLp_congr
  exact ae_mono hνμ (MemLp.coeFn_toLp hfμ)

/--
%%handwave
name:
  Equality after restriction gives equality of representatives almost everywhere
statement:
  Let $\nu\leq\mu$, let $u\in L^2(\mu;E)$ and $v\in L^2(\nu;E)$, and
  suppose that restricting the class of $u$ from $\mu$ to $\nu$ gives $v$.
  Then
  $$
    u(x)=v(x)
  $$
  for $\nu$-almost every $x$.
proof:
  The restriction contraction is represented by the same measurable
  function as $u$. Its equality with $v$ therefore identifies their chosen
  representatives almost everywhere for the smaller measure.
-/
theorem L2.ae_eq_of_monoMeasure_eq
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] {μ ν : Measure X} (hνμ : ν ≤ μ)
    (u : Lp E 2 μ) (v : Lp E 2 ν)
    (h : L2.monoMeasure hνμ u = v) :
    (fun x ↦ u x) =ᵐ[ν] fun x ↦ v x := by
  have hcoe :
      (fun x ↦ (((Lp.memLp u).mono_measure hνμ).toLp
        (fun x ↦ u x)) x) =ᵐ[ν] fun x ↦ u x :=
    MemLp.coeFn_toLp ((Lp.memLp u).mono_measure hνμ)
  rw [← L2.monoMeasure_apply hνμ u, h] at hcoe
  exact hcoe.symm

/--
%%handwave
name:
  Compatibility of weak limits under measure restriction
statement:
  Suppose $\nu\leq\mu$, $u_n\in L^2(\mu;E)$, and the same sequence converges
  weakly to $u_\mu$ in $L^2(\mu;E)$ and to $u_\nu$ in $L^2(\nu;E)$. Then
  restricting $u_\mu$ to $\nu$ gives $u_\nu$.
proof:
  The restriction contraction is continuous for the weak topologies, so the
  larger-measure convergence also converges after restriction. The
  restricted sequence is the original sequence in $L^2(\nu;E)$; uniqueness
  of weak limits gives the claim.
-/
theorem L2.eq_of_weak_tendsto_monoMeasure
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    {μ ν : Measure X} (hνμ : ν ≤ μ)
    (u : ℕ → X → E) (hmemμ : ∀ n, MemLp (u n) 2 μ)
    (hmemν : ∀ n, MemLp (u n) 2 ν)
    (uLimμ : Lp E 2 μ) (uLimν : Lp E 2 ν)
    (hweakμ : Tendsto
      (fun n ↦ toWeakSpace ℝ (Lp E 2 μ) ((hmemμ n).toLp (u n)))
      atTop (nhds (toWeakSpace ℝ (Lp E 2 μ) uLimμ)))
    (hweakν : Tendsto
      (fun n ↦ toWeakSpace ℝ (Lp E 2 ν) ((hmemν n).toLp (u n)))
      atTop (nhds (toWeakSpace ℝ (Lp E 2 ν) uLimν))) :
    L2.monoMeasure hνμ uLimμ = uLimν := by
  have hmap :
      Tendsto
        (fun n ↦ WeakSpace.map (L2.monoMeasure hνμ)
          (toWeakSpace ℝ (Lp E 2 μ) ((hmemμ n).toLp (u n))))
        atTop
        (nhds (WeakSpace.map (L2.monoMeasure hνμ)
          (toWeakSpace ℝ (Lp E 2 μ) uLimμ))) :=
    ((WeakSpace.map (L2.monoMeasure hνμ)).continuous.tendsto
      (toWeakSpace ℝ (Lp E 2 μ) uLimμ)).comp hweakμ
  have hmap' : Tendsto
      (fun n ↦ toWeakSpace ℝ (Lp E 2 ν) ((hmemν n).toLp (u n)))
      atTop
      (nhds (toWeakSpace ℝ (Lp E 2 ν) (L2.monoMeasure hνμ uLimμ))) := by
    have hsource : ∀ n,
        WeakSpace.map (L2.monoMeasure hνμ)
            (toWeakSpace ℝ (Lp E 2 μ) ((hmemμ n).toLp (u n))) =
          toWeakSpace ℝ (Lp E 2 ν) ((hmemν n).toLp (u n)) := by
      intro n
      change L2.monoMeasure hνμ ((hmemμ n).toLp (u n)) =
        (hmemν n).toLp (u n)
      exact L2.monoMeasure_toLp hνμ (u n) (hmemμ n) (hmemν n)
    have hlimit :
        WeakSpace.map (L2.monoMeasure hνμ)
            (toWeakSpace ℝ (Lp E 2 μ) uLimμ) =
          toWeakSpace ℝ (Lp E 2 ν) (L2.monoMeasure hνμ uLimμ) := by
      rfl
    rw [hlimit] at hmap
    exact hmap.congr' (Filter.Eventually.of_forall hsource)
  exact (toWeakSpace ℝ (Lp E 2 ν)).injective
    (tendsto_nhds_unique hmap' hweakν)

/--
%%handwave
name:
  Weak $L^2$ convergence passes to real test pairings
statement:
  Let $u_n\rightharpoonup u$ weakly in $L^2(\mu;\mathbb C)$ and let
  $\phi\in L^2(\mu;\mathbb R)$. Then
  $$
    \int \phi u_n\,d\mu\longrightarrow\int \phi u\,d\mu.
  $$
proof:
  Integration against $\phi$ is a bounded real-linear map from
  $L^2(\mu;\mathbb C)$ to $\mathbb C$ by H\"older's inequality. Apply weak
  convergence to its real and imaginary parts and recombine them.
-/
theorem L2.tendsto_integral_real_smul_of_weak_tendsto
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (u : ℕ → X → ℂ) (hmem : ∀ n, MemLp (u n) 2 μ)
    (uLim : Lp ℂ 2 μ)
    (hweak : Tendsto
      (fun n ↦ toWeakSpace ℝ (Lp ℂ 2 μ) ((hmem n).toLp (u n)))
      atTop (nhds (toWeakSpace ℝ (Lp ℂ 2 μ) uLim)))
    (φ : X → ℝ) (hφ : MemLp φ 2 μ) :
    Tendsto (fun n ↦ ∫ x, φ x • u n x ∂μ) atTop
      (nhds (∫ x, φ x • uLim x ∂μ)) := by
  let φLp : Lp ℝ 2 μ := hφ.toLp φ
  let B : ℝ →L[ℝ] ℂ →L[ℝ] ℂ :=
    ContinuousLinearMap.lsmul ℝ (E := ℂ) ℝ
  let T : Lp ℂ 2 μ →L[ℝ] ℂ := B.lpPairing μ 2 2 φLp
  have heval (L : (Lp ℂ 2 μ) →L[ℝ] ℝ) :
      Tendsto (fun n ↦ L ((hmem n).toLp (u n))) atTop (nhds (L uLim)) := by
    have ht := ((WeakBilin.eval_continuous
      (topDualPairing ℝ (Lp ℂ 2 μ)).flip L).tendsto
        (toWeakSpace ℝ (Lp ℂ 2 μ) uLim)).comp hweak
    simpa [topDualPairing, toWeakSpace] using ht
  have hre := heval (Complex.reCLM.comp T)
  have him := heval (Complex.imCLM.comp T)
  have hT : Tendsto (fun n ↦ T ((hmem n).toLp (u n))) atTop
      (nhds (T uLim)) := by
    have hp := hre.prodMk_nhds him
    have hs := (Complex.equivRealProdCLM.symm.continuous.tendsto
      (Complex.re (T uLim), Complex.im (T uLim))).comp hp
    simpa [Complex.equivRealProdCLM_symm_apply] using hs
  have hseq (n : ℕ) : T ((hmem n).toLp (u n)) =
      ∫ x, φ x • u n x ∂μ := by
    rw [show T ((hmem n).toLp (u n)) =
      ∫ x, B (φLp x) (((hmem n).toLp (u n)) x) ∂μ by
        exact B.lpPairing_eq_integral φLp ((hmem n).toLp (u n))]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp hφ,
      MemLp.coeFn_toLp (hmem n)] with x hφx hux
    change φLp x = φ x at hφx
    rw [hφx, hux]
    rfl
  have hlim : T uLim = ∫ x, φ x • uLim x ∂μ := by
    rw [show T uLim = ∫ x, B (φLp x) (uLim x) ∂μ by
      exact B.lpPairing_eq_integral φLp uLim]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp hφ] with x hφx
    change φLp x = φ x at hφx
    rw [hφx]
    rfl
  simpa only [hseq, hlim] using hT

/--
%%handwave
name:
  Real-linear map reconstructed from coordinate values
statement:
  For $a,b\in\mathbb C$, the real-linear map having values $a$ at $1$ and
  $b$ at $i$ is
  $$
    L(v)=\operatorname{Re}(v)a+\operatorname{Im}(v)b.
  $$
-/
def realLinearMapOfCoordinateValues (a b : ℂ) : ℂ →L[ℝ] ℂ :=
  Complex.reCLM.smulRight a + Complex.imCLM.smulRight b

/--
%%handwave
name:
  Reconstruction of a real-linear map from its coordinate values
statement:
  If $L:\mathbb C\to\mathbb C$ is real-linear, then the real-linear map
  taking $1$ to $L(1)$ and $i$ to $L(i)$ is $L$ itself. Equivalently,
  $$
    L(v)=\operatorname{Re}(v)L(1)+\operatorname{Im}(v)L(i)
  $$
  for every $v\in\mathbb C$.
proof:
  Write $v=\operatorname{Re}(v)\,1+\operatorname{Im}(v)\,i$ and use real
  linearity.
-/
theorem realLinearMapOfCoordinateValues_apply_eq
    (L : ℂ →L[ℝ] ℂ) :
    realLinearMapOfCoordinateValues (L 1) (L Complex.I) = L := by
  ext v
  have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by
    simpa only [Complex.real_smul, mul_one] using
      (Complex.re_add_im v).symm
  calc
    realLinearMapOfCoordinateValues (L 1) (L Complex.I) v =
        v.re • L 1 + v.im • L Complex.I := rfl
    _ = L (v.re • (1 : ℂ) + v.im • Complex.I) := by
      rw [map_add, map_smul, map_smul]
    _ = L v := by rw [← hv]

/--
%%handwave
name:
  Reconstruction from the first coordinate value
statement:
  The map $a\mapsto(v\mapsto\operatorname{Re}(v)a)$ is a bounded real-linear
  map from $\mathbb C$ to the space of real-linear endomorphisms of
  $\mathbb C$.
-/
def coordinateValueReconstructionReCLM : ℂ →L[ℝ] (ℂ →L[ℝ] ℂ) :=
  ContinuousLinearMap.smulRightL ℝ ℂ ℂ Complex.reCLM

/--
%%handwave
name:
  Reconstruction from the second coordinate value
statement:
  The map $b\mapsto(v\mapsto\operatorname{Im}(v)b)$ is a bounded real-linear
  map from $\mathbb C$ to the space of real-linear endomorphisms of
  $\mathbb C$.
-/
def coordinateValueReconstructionImCLM : ℂ →L[ℝ] (ℂ →L[ℝ] ℂ) :=
  ContinuousLinearMap.smulRightL ℝ ℂ ℂ Complex.imCLM

/--
%%handwave
name:
  Operator norm bound for reconstruction from two coordinate values
statement:
  For $a,b\in\mathbb C$, let
  $$
    L(v)=\operatorname{Re}(v)a+\operatorname{Im}(v)b.
  $$
  Then
  $$
    \lVert L\rVert_{\mathrm{op}}\leq |a|+|b|.
  $$
proof:
  For every $v\in\mathbb C$, the triangle inequality and
  $|\operatorname{Re}v|,|\operatorname{Im}v|\leq|v|$ give
  $|L(v)|\leq(|a|+|b|)|v|$. Take the operator norm.
-/
theorem norm_realLinearMapOfCoordinateValues_le (a b : ℂ) :
    ‖realLinearMapOfCoordinateValues a b‖ ≤ ‖a‖ + ‖b‖ := by
  refine (realLinearMapOfCoordinateValues a b).opNorm_le_bound
    (add_nonneg (norm_nonneg _) (norm_nonneg _)) ?_
  intro z
  calc
    ‖realLinearMapOfCoordinateValues a b z‖ =
        ‖z.re • a + z.im • b‖ := by
      rfl
    _ ≤ ‖z.re • a‖ + ‖z.im • b‖ := norm_add_le _ _
    _ = |z.re| * ‖a‖ + |z.im| * ‖b‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ ‖z‖ * ‖a‖ + ‖z‖ * ‖b‖ :=
      add_le_add
        (mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm z) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm z) (norm_nonneg _))
    _ = (‖a‖ + ‖b‖) * ‖z‖ := by ring

set_option maxHeartbeats 1000000 in
/--
%%handwave
name:
  Square-integrability of a reconstructed planar differential
statement:
  Let $a,b:X\to\mathbb C$ belong to $L^2(\mu)$. Then the real-linear field
  $$
    L_x(v)=\operatorname{Re}(v)a(x)+\operatorname{Im}(v)b(x)
  $$
  belongs to
  $L^2\bigl(\mu;\operatorname{Lin}_{\mathbb R}(\mathbb C,\mathbb C)\bigr)$.
proof:
  The reconstruction maps $a\mapsto\operatorname{Re}(\cdot)a$ and
  $b\mapsto\operatorname{Im}(\cdot)b$ are continuous linear maps, so the
  reconstructed field is measurable. Its operator norm is bounded by
  $|a|+|b|$, which belongs to $L^2$.
-/
theorem realLinearMapOfCoordinateValues_memLp
    {μ : Measure ℂ} {a b : ℂ → ℂ}
    (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
    MemLp (fun z ↦ realLinearMapOfCoordinateValues (a z) (b z)) 2 μ := by
  have hfirst : AEStronglyMeasurable
      (fun z ↦ Complex.reCLM.smulRight (a z)) μ :=
    coordinateValueReconstructionReCLM.continuous.comp_aestronglyMeasurable ha.1
  have hsecond : AEStronglyMeasurable
      (fun z ↦ Complex.imCLM.smulRight (b z)) μ :=
    coordinateValueReconstructionImCLM.continuous.comp_aestronglyMeasurable hb.1
  have hmeas : AEStronglyMeasurable
      (fun z ↦ realLinearMapOfCoordinateValues (a z) (b z)) μ := by
    change AEStronglyMeasurable
      (fun z ↦ Complex.reCLM.smulRight (a z) +
        Complex.imCLM.smulRight (b z)) μ
    exact hfirst.add hsecond
  exact (ha.norm.add hb.norm).of_le hmeas
    (Filter.Eventually.of_forall fun z ↦ by
      simpa only [Pi.add_apply, Real.norm_eq_abs,
        abs_of_nonneg (add_nonneg (norm_nonneg (a z)) (norm_nonneg (b z)))] using
        norm_realLinearMapOfCoordinateValues_le (a z) (b z))

/--
%%handwave
name:
  Beltrami multiplier on $L^2$
statement:
  For $a\in L^\infty(m)$, pointwise multiplication $f\mapsto af$ defines a
  bounded complex-linear operator on $L^2(m)$.
-/
def beltramiL2Multiplier {m : Measure ℂ} (a : Lp ℂ ∞ m) :
    Lp ℂ 2 m →L[ℂ] Lp ℂ 2 m :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL m ∞ 2 2 a

/--
%%handwave
name:
  Almost-everywhere formula for bounded multiplication on $L^2$
statement:
  If $a\in L^\infty(m)$ and $f\in L^2(m)$, then the bounded multiplication
  operator satisfies
  $$
    M_a f(x)=a(x)f(x)
  $$
  for $m$-almost every $x$.
proof:
  This is the pointwise representative formula for the Hölder multiplication
  operator $L^\infty\times L^2\to L^2$.
-/
theorem beltramiL2Multiplier_ae {m : Measure ℂ} (a : Lp ℂ ∞ m)
    (f : Lp ℂ 2 m) :
    (fun z ↦ beltramiL2Multiplier a f z) =ᵐ[m]
      fun z ↦ a z * f z := by
  simpa [beltramiL2Multiplier] using
    (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder a f

/--
%%handwave
name:
  Multiplication by $i$ on $L^2$
statement:
  Pointwise multiplication by $i$ defines a bounded real-linear operator on
  complex-valued $L^2(m)$.
-/
def l2MulI {m : Measure ℂ} : Lp ℂ 2 m →L[ℝ] Lp ℂ 2 m :=
  (realLinearMapOfWirtinger Complex.I 0).compLpL 2 m

/--
%%handwave
name:
  $L^2$ reconstruction of the $z$-Wirtinger component
statement:
  If $a,b\in L^2(m;\mathbb C)$ are the values of a real-linear differential
  on $1$ and $i$, its $z$-Wirtinger component is $(a-ib)/2$.
-/
def l2WeakDZOfCoordinateValues {m : Measure ℂ} (a b : Lp ℂ 2 m) :
    Lp ℂ 2 m :=
  (2 : ℝ)⁻¹ • (a - l2MulI b)

/--
%%handwave
name:
  $L^2$ reconstruction of the $\bar z$-Wirtinger component
statement:
  If $a,b\in L^2(m;\mathbb C)$ are the values of a real-linear differential
  on $1$ and $i$, its $\bar z$-Wirtinger component is $(a+ib)/2$.
-/
def l2WeakDBarOfCoordinateValues {m : Measure ℂ} (a b : Lp ℂ 2 m) :
    Lp ℂ 2 m :=
  (2 : ℝ)⁻¹ • (a + l2MulI b)

/--
%%handwave
name:
  Norm bound for the reconstructed $z$ Wirtinger derivative
statement:
  For $a,b\in L^2(m;\mathbb C)$, the reconstructed field
  $$
    \frac12(a-ib)
  $$
  satisfies
  $$
    \left\lVert\frac12(a-ib)\right\rVert_2
      \leq\lVert a\rVert_2+\lVert b\rVert_2.
  $$
proof:
  Multiplication by $i$ is a contraction on $L^2$. Apply the triangle
  inequality and use $1/2\leq1$.
-/
theorem norm_l2WeakDZOfCoordinateValues_le
    {m : Measure ℂ} (a b : Lp ℂ 2 m) :
    ‖l2WeakDZOfCoordinateValues a b‖ ≤ ‖a‖ + ‖b‖ := by
  have hIop : ‖l2MulI (m := m)‖ ≤ 1 := by
    change ‖(realLinearMapOfWirtinger Complex.I 0).compLpL 2 m‖ ≤ 1
    calc
      _ ≤ ‖realLinearMapOfWirtinger Complex.I 0‖ :=
        ContinuousLinearMap.norm_compLpL_le _
      _ = 1 := by simp [norm_realLinearMapOfWirtinger]
  have hIb : ‖l2MulI b‖ ≤ ‖b‖ := by
    calc
      ‖l2MulI b‖ ≤ ‖l2MulI (m := m)‖ * ‖b‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖b‖ := mul_le_mul_of_nonneg_right hIop (norm_nonneg _)
      _ = ‖b‖ := one_mul _
  rw [l2WeakDZOfCoordinateValues, norm_smul]
  calc
    ‖(2 : ℝ)⁻¹‖ * ‖a - l2MulI b‖ ≤ 1 * ‖a - l2MulI b‖ := by
      gcongr
      norm_num
    _ ≤ ‖a‖ + ‖l2MulI b‖ := by simpa using norm_sub_le a (l2MulI b)
    _ ≤ ‖a‖ + ‖b‖ := add_le_add le_rfl hIb

/--
%%handwave
name:
  $L^2$ reconstruction of the $z$ Wirtinger derivative
statement:
  Let $a,b\in L^2(m;\mathbb C)$ and define the real-linear field
  $L_x(v)=\operatorname{Re}(v)a(x)+\operatorname{Im}(v)b(x)$. The $L^2$
  reconstruction
  $$
    \frac12(a-ib)
  $$
  equals $\partial_zL$ almost everywhere.
proof:
  Evaluate $L_x$ at $1$ and $i$ in the defining formula
  $\partial_zL_x=\frac12(L_x(1)-iL_x(i))$.
-/
theorem l2WeakDZOfCoordinateValues_ae {m : Measure ℂ}
    (a b : Lp ℂ 2 m) :
    (fun z ↦ l2WeakDZOfCoordinateValues a b z) =ᵐ[m]
      fun z ↦ weakDZ (realLinearMapOfCoordinateValues (a z) (b z)) := by
  filter_upwards [Lp.coeFn_smul (2 : ℝ)⁻¹ (a - l2MulI b),
    Lp.coeFn_sub a (l2MulI b),
    (realLinearMapOfWirtinger Complex.I 0).coeFn_compLpL b] with
      z hsmul hsub hI
  change ((2 : ℝ)⁻¹ • (a - l2MulI b) : Lp ℂ 2 m) z = _
  rw [hsmul]
  simp only [Pi.smul_apply]
  rw [hsub]
  simp only [Pi.sub_apply, l2MulI]
  rw [hI]
  simp [weakDZ, realLinearMapOfCoordinateValues,
    realLinearMapOfWirtinger]

/--
%%handwave
name:
  $L^2$ reconstruction of the $\bar z$ Wirtinger derivative
statement:
  Let $a,b\in L^2(m;\mathbb C)$ and define the real-linear field
  $L_x(v)=\operatorname{Re}(v)a(x)+\operatorname{Im}(v)b(x)$. The $L^2$
  reconstruction
  $$
    \frac12(a+ib)
  $$
  equals $\partial_{\bar z}L$ almost everywhere.
proof:
  Evaluate $L_x$ at $1$ and $i$ in the defining formula
  $\partial_{\bar z}L_x=\frac12(L_x(1)+iL_x(i))$.
-/
theorem l2WeakDBarOfCoordinateValues_ae {m : Measure ℂ}
    (a b : Lp ℂ 2 m) :
    (fun z ↦ l2WeakDBarOfCoordinateValues a b z) =ᵐ[m]
      fun z ↦ weakDBar (realLinearMapOfCoordinateValues (a z) (b z)) := by
  filter_upwards [Lp.coeFn_smul (2 : ℝ)⁻¹ (a + l2MulI b),
    Lp.coeFn_add a (l2MulI b),
    (realLinearMapOfWirtinger Complex.I 0).coeFn_compLpL b] with
      z hsmul hadd hI
  change ((2 : ℝ)⁻¹ • (a + l2MulI b) : Lp ℂ 2 m) z = _
  rw [hsmul]
  simp only [Pi.smul_apply]
  rw [hadd]
  simp only [Pi.add_apply, l2MulI]
  rw [hI]
  simp [weakDBar, realLinearMapOfCoordinateValues,
    realLinearMapOfWirtinger]
  ring

/--
%%handwave
name:
  Weak convergence of reconstructed $z$ Wirtinger derivatives
statement:
  If $a_n\rightharpoonup a$ and $b_n\rightharpoonup b$ weakly in
  $L^2(m;\mathbb C)$, then
  $$
    \frac12(a_n-ib_n)\rightharpoonup\frac12(a-ib)
  $$
  weakly in $L^2(m;\mathbb C)$.
proof:
  Multiplication by $i$ and every fixed real linear combination are bounded
  real-linear operators on $L^2$, hence are weakly continuous.
-/
theorem l2WeakDZOfCoordinateValues_tendsto_of_weak_tendsto
    {m : Measure ℂ} (a b : ℕ → Lp ℂ 2 m) (aLim bLim : Lp ℂ 2 m)
    (ha : Tendsto (fun n ↦ toWeakSpace ℝ _ (a n)) atTop
      (nhds (toWeakSpace ℝ _ aLim)))
    (hb : Tendsto (fun n ↦ toWeakSpace ℝ _ (b n)) atTop
      (nhds (toWeakSpace ℝ _ bLim))) :
    Tendsto
      (fun n ↦ toWeakSpace ℝ _
        (l2WeakDZOfCoordinateValues (a n) (b n))) atTop
      (nhds (toWeakSpace ℝ _
        (l2WeakDZOfCoordinateValues aLim bLim))) := by
  have hbI : Tendsto
      (fun n ↦ toWeakSpace ℝ _ (l2MulI (b n))) atTop
      (nhds (toWeakSpace ℝ _ (l2MulI bLim))) := by
    have h := (WeakSpace.map (l2MulI (m := m))).continuous.continuousAt
      |>.tendsto.comp hb
    simpa only [WeakSpace.map_apply] using h
  have h := (ha.sub hbI).const_smul (2 : ℝ)⁻¹
  simpa only [l2WeakDZOfCoordinateValues, map_smul, map_sub] using h

/--
%%handwave
name:
  Weak convergence of reconstructed $\bar z$ Wirtinger derivatives
statement:
  If $a_n\rightharpoonup a$ and $b_n\rightharpoonup b$ weakly in
  $L^2(m;\mathbb C)$, then
  $$
    \frac12(a_n+ib_n)\rightharpoonup\frac12(a+ib)
  $$
  weakly in $L^2(m;\mathbb C)$.
proof:
  Multiplication by $i$ and every fixed real linear combination are bounded
  real-linear operators on $L^2$, hence are weakly continuous.
-/
theorem l2WeakDBarOfCoordinateValues_tendsto_of_weak_tendsto
    {m : Measure ℂ} (a b : ℕ → Lp ℂ 2 m) (aLim bLim : Lp ℂ 2 m)
    (ha : Tendsto (fun n ↦ toWeakSpace ℝ _ (a n)) atTop
      (nhds (toWeakSpace ℝ _ aLim)))
    (hb : Tendsto (fun n ↦ toWeakSpace ℝ _ (b n)) atTop
      (nhds (toWeakSpace ℝ _ bLim))) :
    Tendsto
      (fun n ↦ toWeakSpace ℝ _
        (l2WeakDBarOfCoordinateValues (a n) (b n))) atTop
      (nhds (toWeakSpace ℝ _
        (l2WeakDBarOfCoordinateValues aLim bLim))) := by
  have hbI : Tendsto
      (fun n ↦ toWeakSpace ℝ _ (l2MulI (b n))) atTop
      (nhds (toWeakSpace ℝ _ (l2MulI bLim))) := by
    have h := (WeakSpace.map (l2MulI (m := m))).continuous.continuousAt
      |>.tendsto.comp hb
    simpa only [WeakSpace.map_apply] using h
  have h := (ha.add hbI).const_smul (2 : ℝ)⁻¹
  simpa only [l2WeakDBarOfCoordinateValues, map_smul, map_add] using h

/--
%%handwave
name:
  Weak continuity of bounded coefficient multiplication
statement:
  Let $a\in L^\infty(m)$ and suppose $f_n\rightharpoonup f$ weakly in
  $L^2(m;\mathbb C)$. Then
  $$
    af_n\rightharpoonup af
  $$
  weakly in $L^2(m;\mathbb C)$.
proof:
  Multiplication by $a$ is a bounded complex-linear, hence bounded
  real-linear, operator on $L^2$ and is therefore weakly continuous.
-/
theorem beltramiL2Multiplier_tendsto_of_weak_tendsto
    {m : Measure ℂ} (a : Lp ℂ ∞ m) (f : ℕ → Lp ℂ 2 m)
    (fLim : Lp ℂ 2 m)
    (hf : Tendsto (fun n ↦ toWeakSpace ℝ _ (f n)) atTop
      (nhds (toWeakSpace ℝ _ fLim))) :
    Tendsto
      (fun n ↦ toWeakSpace ℝ _ (beltramiL2Multiplier a (f n))) atTop
      (nhds (toWeakSpace ℝ _ (beltramiL2Multiplier a fLim))) := by
  have h :=
    (WeakSpace.map ((beltramiL2Multiplier a).restrictScalars ℝ)).continuous
      |>.continuousAt.tendsto.comp hf
  simpa only [WeakSpace.map_apply] using h

/--
%%handwave
name:
  Sequential weak convergence detected by real inner products
statement:
  Let $E$ be a real Hilbert space. A sequence $u_n$ converges weakly to
  $u$ if and only if
  $$
    \langle y,u_n\rangle_{\mathbb R}
      \longrightarrow \langle y,u\rangle_{\mathbb R}
  $$
  for every $y\in E$.
proof:
  The weak topology is induced by the continuous dual. The Riesz
  representation theorem writes every continuous real-linear functional
  uniquely as an inner product against a vector.
-/
theorem tendsto_toWeakSpace_iff_forall_real_inner
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {u : ℕ → E} {v : E} :
    Tendsto (fun n ↦ toWeakSpace ℝ E (u n)) atTop
      (nhds (toWeakSpace ℝ E v)) ↔
      ∀ y : E, Tendsto (fun n ↦ inner ℝ y (u n)) atTop
        (nhds (inner ℝ y v)) := by
  have h := WeakBilin.tendsto_iff_forall_eval_tendsto
    (topDualPairing ℝ E).flip (by
      intro x y hxy
      apply ext_inner_left ℝ
      intro z
      exact congrArg
        (fun L : (E →L[ℝ] ℝ) →ₗ[ℝ] ℝ ↦
          L (InnerProductSpace.toDual ℝ E z)) hxy)
    (l := atTop)
    (f := fun n ↦ toWeakSpace ℝ E (u n))
    (x := toWeakSpace ℝ E v)
  constructor
  · intro hu y
    exact h.mp hu (InnerProductSpace.toDual ℝ E y)
  · intro hu
    apply h.mpr
    intro x
    have hx := hu ((InnerProductSpace.toDual ℝ E).symm x)
    simpa only [InnerProductSpace.toDual_symm_apply] using hx

/--
%%handwave
name:
  Strong convergence of conjugate coefficient-error multipliers
statement:
  Let $a_n,a\in L^\infty(m)$ have representatives such that
  $a_n(z)\to a(z)$ almost everywhere and
  $|a_n(z)|,|a(z)|\leq C$ almost everywhere. Then for every
  $y\in L^2(m)$,
  $$
    \overline{a_n-a}\,y\longrightarrow0
    \quad\text{strongly in }L^2(m).
  $$
proof:
  Pointwise convergence gives convergence of the squared norms of the
  products to zero. They are dominated by the integrable function
  $(2C)^2|y|^2$, so dominated convergence makes their squared $L^2$ norms
  tend to zero.
-/
theorem beltramiL2Multiplier_star_sub_tendsto_zero_of_ae_tendsto
    {m : Measure ℂ} (a : ℕ → Lp ℂ ∞ m) (aLim : Lp ℂ ∞ m)
    (C : ℝ)
    (hae : ∀ᵐ z ∂m, Tendsto (fun n ↦ a n z) atTop (nhds (aLim z)))
    (hbound : ∀ᵐ z ∂m, ∀ n, ‖a n z‖ ≤ C)
    (hboundLim : ∀ᵐ z ∂m, ‖aLim z‖ ≤ C)
    (y : Lp ℂ 2 m) :
    Tendsto
      (fun n ↦ beltramiL2Multiplier (star (a n - aLim)) y)
      atTop (nhds 0) := by
  let q : ℕ → Lp ℂ 2 m := fun n ↦
    beltramiL2Multiplier (star (a n - aLim)) y
  have hqformula : ∀ᵐ z ∂m, ∀ n,
      q n z = starRingEnd ℂ (a n z - aLim z) * y z := by
    rw [ae_all_iff]
    intro n
    filter_upwards [beltramiL2Multiplier_ae (star (a n - aLim)) y,
      Lp.coeFn_star (a n - aLim), Lp.coeFn_sub (a n) aLim] with
      z hmul hstar hsub
    simp only [Pi.sub_apply] at hsub
    rw [hmul, hstar]
    change starRingEnd ℂ ((a n - aLim) z) * y z = _
    rw [hsub]
  let B : ℂ → ℝ := fun z ↦ (2 * C) ^ 2 * ‖y z‖ ^ 2
  have hySq : Integrable (fun z ↦ ‖y z‖ ^ 2) m :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable y)).mp
      (Lp.memLp y)
  have hBint : Integrable B m := by
    simpa only [B] using hySq.const_mul ((2 * C) ^ 2)
  have hFmeas : ∀ n, AEStronglyMeasurable
      (fun z ↦ ‖q n z‖ ^ 2) m := fun n ↦
    (Lp.aestronglyMeasurable (q n)).norm.pow 2
  have hFbound : ∀ n, ∀ᵐ z ∂m, ‖‖q n z‖ ^ 2‖ ≤ B z := by
    intro n
    filter_upwards [hqformula, hbound, hboundLim] with z hqz haz haLimz
    rw [hqz]
    have hdiff : ‖a n z - aLim z‖ ≤ 2 * C := by
      calc
        ‖a n z - aLim z‖ ≤ ‖a n z‖ + ‖aLim z‖ := norm_sub_le _ _
        _ ≤ C + C := add_le_add (haz n) haLimz
        _ = 2 * C := by ring
    calc
      ‖‖starRingEnd ℂ (a n z - aLim z) * y z‖ ^ 2‖ =
          ‖a n z - aLim z‖ ^ 2 * ‖y z‖ ^ 2 := by
            rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_mul]
            change (‖star (a n z - aLim z)‖ * ‖y z‖) ^ 2 = _
            rw [norm_star, mul_pow]
      _ ≤ (2 * C) ^ 2 * ‖y z‖ ^ 2 :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg _) hdiff 2) (sq_nonneg ‖y z‖)
      _ = B z := rfl
  have hFlim : ∀ᵐ z ∂m,
      Tendsto (fun n ↦ ‖q n z‖ ^ 2) atTop (nhds 0) := by
    filter_upwards [hqformula, hae] with z hqz haz
    have hsub : Tendsto (fun n ↦ a n z - aLim z) atTop (nhds 0) := by
      simpa using haz.sub_const (aLim z)
    have hstar : Tendsto
        (fun n ↦ starRingEnd ℂ (a n z - aLim z)) atTop (nhds 0) := by
      change Tendsto
        ((starRingEnd ℂ) ∘ (fun n ↦ a n z - aLim z)) atTop (nhds 0)
      simpa using Complex.continuous_conj.continuousAt.tendsto.comp hsub
    have hq : Tendsto
        (fun n ↦ starRingEnd ℂ (a n z - aLim z) * y z)
        atTop (nhds 0) := by
      simpa using hstar.mul_const (y z)
    have hsquare := hq.norm.pow 2
    simpa only [hqz, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
      using hsquare
  have hintegral : Tendsto (fun n ↦ ∫ z, ‖q n z‖ ^ 2 ∂m)
      atTop (nhds 0) := by
    simpa using tendsto_integral_of_dominated_convergence B hFmeas hBint
      hFbound hFlim
  have hnormsq (n : ℕ) : ‖q n‖ ^ 2 = ∫ z, ‖q n z‖ ^ 2 ∂m := by
    rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards with z
    exact real_inner_self_eq_norm_sq (q n z)
  have hsquares : Tendsto (fun n ↦ ‖q n‖ ^ 2) atTop (nhds 0) := by
    simpa only [hnormsq] using hintegral
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsquares
  have hnorm : Tendsto (fun n ↦ ‖q n‖) atTop (nhds 0) := by
    convert hsqrt using 1
    · funext n
      simp
    · simp
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [q] using hnorm

/--
%%handwave
name:
  Real adjoint identity for Beltrami multiplication
statement:
  For $a\in L^\infty(m)$ and $f,y\in L^2(m)$,
  $$
    \langle y,af\rangle_{\mathbb R}
      =\langle\overline a\,y,f\rangle_{\mathbb R}.
  $$
proof:
  Expand the real $L^2$ inner products as integrals and use complex
  conjugation and commutativity pointwise.
-/
theorem real_inner_beltramiL2Multiplier
    {m : Measure ℂ} (a : Lp ℂ ∞ m) (f y : Lp ℂ 2 m) :
    inner ℝ y (beltramiL2Multiplier a f) =
      inner ℝ (beltramiL2Multiplier (star a) y) f := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [beltramiL2Multiplier_ae a f,
    beltramiL2Multiplier_ae (star a) y, Lp.coeFn_star a] with
      z haf hstar hcoa
  rw [haf, hstar, hcoa]
  rw [real_inner_eq_re_inner, real_inner_eq_re_inner,
    RCLike.inner_apply, RCLike.inner_apply]
  change ((a z * f z) * starRingEnd ℂ (y z)).re =
    (f z * starRingEnd ℂ (starRingEnd ℂ (a z) * y z)).re
  rw [map_mul]
  have haa : starRingEnd ℂ (starRingEnd ℂ (a z)) = a z := by
    change star (star (a z)) = a z
    exact star_star (a z)
  rw [haa]
  congr 1
  ring

/--
%%handwave
name:
  Weak closure of bounded varying multipliers
statement:
  Let $a_n,a\in L^\infty(m)$ have representatives with
  $a_n\to a$ almost everywhere and $|a_n|,|a|\leq C$ almost everywhere.
  If $f_n\rightharpoonup f$ weakly in $L^2(m)$ and
  $\lVert f_n\rVert_2\leq D$, then
  $$
    a_nf_n\rightharpoonup af
    \quad\text{weakly in }L^2(m).
  $$
proof:
  Test against $y\in L^2$. The fixed-coefficient term converges weakly.
  Move the coefficient error to the test vector using
  [the real adjoint identity](lean:JJMath.Quasiconformal.real_inner_beltramiL2Multiplier). Its $L^2$ norm tends to zero by [dominated convergence](lean:JJMath.Quasiconformal.beltramiL2Multiplier_star_sub_tendsto_zero_of_ae_tendsto), while the norms of $f_n$ are uniformly bounded.
-/
theorem beltramiL2Multiplier_tendsto_of_ae_tendsto_of_weak_tendsto
    {m : Measure ℂ} (a : ℕ → Lp ℂ ∞ m) (aLim : Lp ℂ ∞ m)
    (C : ℝ)
    (hae : ∀ᵐ z ∂m, Tendsto (fun n ↦ a n z) atTop (nhds (aLim z)))
    (hbound : ∀ᵐ z ∂m, ∀ n, ‖a n z‖ ≤ C)
    (hboundLim : ∀ᵐ z ∂m, ‖aLim z‖ ≤ C)
    (f : ℕ → Lp ℂ 2 m) (fLim : Lp ℂ 2 m) (D : ℝ)
    (hf : Tendsto (fun n ↦ toWeakSpace ℝ _ (f n)) atTop
      (nhds (toWeakSpace ℝ _ fLim)))
    (hfbound : ∀ n, ‖f n‖ ≤ D) :
    Tendsto
      (fun n ↦ toWeakSpace ℝ _ (beltramiL2Multiplier (a n) (f n)))
      atTop
      (nhds (toWeakSpace ℝ _ (beltramiL2Multiplier aLim fLim))) := by
  apply tendsto_toWeakSpace_iff_forall_real_inner.mpr
  intro y
  let q : ℕ → Lp ℂ 2 m := fun n ↦
    beltramiL2Multiplier (star (a n - aLim)) y
  have hq : Tendsto q atTop (nhds 0) := by
    exact beltramiL2Multiplier_star_sub_tendsto_zero_of_ae_tendsto
      a aLim C hae hbound hboundLim y
  have hqinner : Tendsto (fun n ↦ inner ℝ (q n) (f n)) atTop
      (nhds 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero'
    · filter_upwards with n
      exact norm_nonneg _
    · filter_upwards with n
      exact (abs_real_inner_le_norm (q n) (f n)).trans
        (mul_le_mul_of_nonneg_left (hfbound n) (norm_nonneg (q n)))
    · have hnormq : Tendsto (fun n ↦ ‖q n‖) atTop (nhds 0) :=
        tendsto_zero_iff_norm_tendsto_zero.mp hq
      simpa using hnormq.mul_const D
  have hfixed := (tendsto_toWeakSpace_iff_forall_real_inner.mp
      (beltramiL2Multiplier_tendsto_of_weak_tendsto aLim f fLim hf)) y
  have hsum := hqinner.add hfixed
  convert hsum using 1
  · funext n
    rw [real_inner_beltramiL2Multiplier (a n) (f n) y,
      real_inner_beltramiL2Multiplier aLim (f n) y]
    have hdecomp : beltramiL2Multiplier (star (a n)) y =
        q n + beltramiL2Multiplier (star aLim) y := by
      ext1
      filter_upwards [beltramiL2Multiplier_ae (star (a n - aLim)) y,
        beltramiL2Multiplier_ae (star aLim) y,
        beltramiL2Multiplier_ae (star (a n)) y,
        Lp.coeFn_star (a n - aLim), Lp.coeFn_star aLim,
        Lp.coeFn_star (a n), Lp.coeFn_sub (a n) aLim,
        Lp.coeFn_add (q n) (beltramiL2Multiplier (star aLim) y)] with
          z hqz hlimz hnz hstarsub hstarlim hstarn hsub hadd
      rw [hadd]
      change (beltramiL2Multiplier (star (a n)) y) z =
        (beltramiL2Multiplier (star (a n - aLim)) y) z +
          (beltramiL2Multiplier (star aLim) y) z
      rw [hqz, hlimz, hnz, hstarsub, hstarlim, hstarn]
      change starRingEnd ℂ (a n z) * y z =
        starRingEnd ℂ ((a n - aLim) z) * y z +
          starRingEnd ℂ (aLim z) * y z
      rw [hsub]
      simp only [Pi.sub_apply, map_sub]
      ring
    rw [hdecomp, inner_add_left]
  · simp

/--
%%handwave
name:
  Weak closure of Beltrami equations with varying coefficients
statement:
  Let $\mu_n,\mu:\Omega\to\mathbb C$ be measurable, suppose
  $\mu_n(z)\to\mu(z)$ almost everywhere, and suppose
  $|\mu_n(z)|,|\mu(z)|\leq C$ almost everywhere. For
  $a_n,b_n\in L^2(\Omega)$ form
  $$
    L_n(z)(v)=\operatorname{Re}(v)a_n(z)+\operatorname{Im}(v)b_n(z).
  $$
  If $a_n\rightharpoonup a$, $b_n\rightharpoonup b$, the norms of
  $\partial_zL_n$ are uniformly bounded, and
  $\partial_{\bar z}L_n=\mu_n\partial_zL_n$ almost everywhere, then the
  reconstructed limit field satisfies
  $$
    \partial_{\bar z}L=\mu\partial_zL
  $$
  almost everywhere on $\Omega$.
proof:
  The reconstructed Wirtinger derivatives converge weakly. The
  [varying-multiplier closure theorem](lean:JJMath.Quasiconformal.beltramiL2Multiplier_tendsto_of_ae_tendsto_of_weak_tendsto) shows that $\mu_n\partial_zL_n$ converges weakly to $\mu\partial_zL$. The equations identify this sequence with $\partial_{\bar z}L_n$, so uniqueness of weak limits proves the result.
-/
theorem weakBeltramiEquationOn_of_ae_tendsto_of_weak_tendsto_coordinateValues
    {Ω : Set ℂ} (μ : ℕ → ℂ → ℂ) (μLim : ℂ → ℂ) (C : ℝ)
    (hμmeas : ∀ n, AEStronglyMeasurable (μ n) (volume.restrict Ω))
    (hμLimmeas : AEStronglyMeasurable μLim (volume.restrict Ω))
    (hμtendsto : ∀ᵐ z ∂volume.restrict Ω,
      Tendsto (fun n ↦ μ n z) atTop (nhds (μLim z)))
    (hμbound : ∀ᵐ z ∂volume.restrict Ω, ∀ n, ‖μ n z‖ ≤ C)
    (hμLimBound : ∀ᵐ z ∂volume.restrict Ω, ‖μLim z‖ ≤ C)
    (a b : ℕ → Lp ℂ 2 (volume.restrict Ω))
    (aLim bLim : Lp ℂ 2 (volume.restrict Ω))
    (ha : Tendsto (fun n ↦ toWeakSpace ℝ _ (a n)) atTop
      (nhds (toWeakSpace ℝ _ aLim)))
    (hb : Tendsto (fun n ↦ toWeakSpace ℝ _ (b n)) atTop
      (nhds (toWeakSpace ℝ _ bLim)))
    (D : ℝ)
    (hdzbound : ∀ n, ‖l2WeakDZOfCoordinateValues (a n) (b n)‖ ≤ D)
    (heq : ∀ n, WeakBeltramiEquationOn Ω (μ n)
      (fun z ↦ realLinearMapOfCoordinateValues (a n z) (b n z))) :
    WeakBeltramiEquationOn Ω μLim
      (fun z ↦ realLinearMapOfCoordinateValues (aLim z) (bLim z)) := by
  let mΩ : Measure ℂ := volume.restrict Ω
  let hμmem : ∀ n, MemLp (μ n) ∞ mΩ := fun n ↦
    memLp_top_of_bound (hμmeas n) C (hμbound.mono fun z hz ↦ hz n)
  let hμLimMem : MemLp μLim ∞ mΩ :=
    memLp_top_of_bound hμLimmeas C hμLimBound
  let μLp : ℕ → Lp ℂ ∞ mΩ := fun n ↦ (hμmem n).toLp (μ n)
  let μLimLp : Lp ℂ ∞ mΩ := hμLimMem.toLp μLim
  have hμLpTendsto : ∀ᵐ z ∂mΩ,
      Tendsto (fun n ↦ μLp n z) atTop (nhds (μLimLp z)) := by
    filter_upwards [hμtendsto, hμLimMem.coeFn_toLp,
      ae_all_iff.mpr (fun n ↦ (hμmem n).coeFn_toLp)] with z hconv hlim hn
    simpa only [μLp, μLimLp, hn, hlim] using hconv
  have hμLpBound : ∀ᵐ z ∂mΩ, ∀ n, ‖μLp n z‖ ≤ C := by
    filter_upwards [hμbound,
      ae_all_iff.mpr (fun n ↦ (hμmem n).coeFn_toLp)] with z hbound hn
    intro n
    rw [hn n]
    exact hbound n
  have hμLimLpBound : ∀ᵐ z ∂mΩ, ‖μLimLp z‖ ≤ C := by
    filter_upwards [hμLimBound, hμLimMem.coeFn_toLp] with z hz hcoe
    rwa [hcoe]
  let dz : ℕ → Lp ℂ 2 mΩ := fun n ↦
    l2WeakDZOfCoordinateValues (a n) (b n)
  let dbar : ℕ → Lp ℂ 2 mΩ := fun n ↦
    l2WeakDBarOfCoordinateValues (a n) (b n)
  let dzLim : Lp ℂ 2 mΩ := l2WeakDZOfCoordinateValues aLim bLim
  let dbarLim : Lp ℂ 2 mΩ := l2WeakDBarOfCoordinateValues aLim bLim
  have hdz : Tendsto (fun n ↦ toWeakSpace ℝ _ (dz n)) atTop
      (nhds (toWeakSpace ℝ _ dzLim)) := by
    exact l2WeakDZOfCoordinateValues_tendsto_of_weak_tendsto
      a b aLim bLim ha hb
  have hdbar : Tendsto (fun n ↦ toWeakSpace ℝ _ (dbar n)) atTop
      (nhds (toWeakSpace ℝ _ dbarLim)) := by
    exact l2WeakDBarOfCoordinateValues_tendsto_of_weak_tendsto
      a b aLim bLim ha hb
  have hmul : Tendsto
      (fun n ↦ toWeakSpace ℝ _ (beltramiL2Multiplier (μLp n) (dz n)))
      atTop
      (nhds (toWeakSpace ℝ _ (beltramiL2Multiplier μLimLp dzLim))) := by
    exact beltramiL2Multiplier_tendsto_of_ae_tendsto_of_weak_tendsto
      μLp μLimLp C hμLpTendsto hμLpBound hμLimLpBound
      dz dzLim D hdz (by simpa only [dz] using hdzbound)
  have heqLp : ∀ n, dbar n = beltramiL2Multiplier (μLp n) (dz n) := by
    intro n
    ext1
    filter_upwards [l2WeakDBarOfCoordinateValues_ae (a n) (b n),
      l2WeakDZOfCoordinateValues_ae (a n) (b n),
      beltramiL2Multiplier_ae (μLp n) (dz n),
      (hμmem n).coeFn_toLp, heq n] with z hbar hz hmulz hμz heqz
    rw [hbar, hmulz, hμz, hz]
    exact heqz
  have hmul' : Tendsto (fun n ↦ toWeakSpace ℝ _ (dbar n)) atTop
      (nhds (toWeakSpace ℝ _ (beltramiL2Multiplier μLimLp dzLim))) :=
    hmul.congr' (Filter.Eventually.of_forall fun n ↦
      congrArg (toWeakSpace ℝ (Lp ℂ 2 mΩ)) (heqLp n).symm)
  have hlimWeak : toWeakSpace ℝ _ dbarLim =
      toWeakSpace ℝ _ (beltramiL2Multiplier μLimLp dzLim) :=
    tendsto_nhds_unique hdbar hmul'
  have hlim : dbarLim = beltramiL2Multiplier μLimLp dzLim :=
    (toWeakSpace ℝ _).injective hlimWeak
  unfold WeakBeltramiEquationOn
  filter_upwards [l2WeakDBarOfCoordinateValues_ae aLim bLim,
    l2WeakDZOfCoordinateValues_ae aLim bLim,
    beltramiL2Multiplier_ae μLimLp dzLim, hμLimMem.coeFn_toLp] with
      z hbar hz hmulz hμz
  change weakDBar (realLinearMapOfCoordinateValues (aLim z) (bLim z)) =
    μLim z * weakDZ (realLinearMapOfCoordinateValues (aLim z) (bLim z))
  calc
    weakDBar (realLinearMapOfCoordinateValues (aLim z) (bLim z)) =
        dbarLim z := hbar.symm
    _ = beltramiL2Multiplier μLimLp dzLim z := by rw [hlim]
    _ = μLimLp z * dzLim z := hmulz
    _ = μLim z * weakDZ
        (realLinearMapOfCoordinateValues (aLim z) (bLim z)) := by
      rw [hμz, hz]

/--
%%handwave
name:
  Euclidean weak derivatives are closed under coordinatewise weak $L^2$ convergence
statement:
  Let $u_n:\Omega\to\mathbb C$ have weak differentials $D u_n$. Suppose
  that $u_n\rightharpoonup u$, $D u_n(1)\rightharpoonup A$, and
  $D u_n(i)\rightharpoonup B$ weakly in $L^2(\Omega;\mathbb C)$. Then the
  field
  $$
    D u(z)(v)=\operatorname{Re}(v)A(z)+\operatorname{Im}(v)B(z)
  $$
  is a weak differential of $u$ on $\Omega$.
proof:
  Test the distributional identity against a smooth compactly supported
  scalar function and a fixed direction $v$. Both the test and its
  directional derivative belong to $L^2$. The left pairing therefore passes
  to the limit by weak convergence of $u_n$. Real linearity expresses
  $D u_n(v)$ as the same linear combination of its values at $1$ and $i$,
  so the right pairing passes to the reconstructed limit by
  [weak $L^2$ convergence of test pairings](lean:JJMath.Quasiconformal.L2.tendsto_integral_real_smul_of_weak_tendsto).
-/
theorem isWeakDerivativeOnEuclideanRegionWithValues_of_weak_tendsto_coordinates
    {Ω : Set ℂ} (u : ℕ → ℂ → ℂ)
    (du : ℕ → ℂ → ℂ →L[ℝ] ℂ)
    (hweak : ∀ n,
      JJMath.Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues
        Ω (u n) (du n))
    (hmem_u : ∀ n, MemLp (u n) 2 (volume.restrict Ω))
    (hmem_x : ∀ n, MemLp (fun z ↦ du n z 1) 2 (volume.restrict Ω))
    (hmem_y : ∀ n, MemLp (fun z ↦ du n z Complex.I) 2 (volume.restrict Ω))
    (uLim dxLim dyLim : Lp ℂ 2 (volume.restrict Ω))
    (hu : Tendsto
      (fun n ↦ toWeakSpace ℝ _ ((hmem_u n).toLp (u n))) atTop
      (nhds (toWeakSpace ℝ _ uLim)))
    (hx : Tendsto
      (fun n ↦ toWeakSpace ℝ _ ((hmem_x n).toLp (fun z ↦ du n z 1))) atTop
      (nhds (toWeakSpace ℝ _ dxLim)))
    (hy : Tendsto
      (fun n ↦ toWeakSpace ℝ _ ((hmem_y n).toLp (fun z ↦ du n z Complex.I))) atTop
      (nhds (toWeakSpace ℝ _ dyLim))) :
    JJMath.Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues Ω
      (fun z ↦ uLim z)
      (fun z ↦ realLinearMapOfCoordinateValues (dxLim z) (dyLim z)) := by
  intro φ v
  let μΩ : Measure ℂ := volume.restrict Ω
  let a : ℂ → ℝ := fun z ↦ fderiv ℝ (φ : ℂ → ℝ) z v
  have hφ_mem : MemLp (fun z ↦ φ z) 2 μΩ := by
    exact (φ.smooth.continuous.memLp_of_hasCompactSupport
      (μ := μΩ) φ.compact_support)
  have ha_cont : Continuous a :=
    (φ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have ha_support : HasCompactSupport a := by
    simpa only [a] using
      HasCompactSupport.fderiv_apply ℝ φ.compact_support v
  have ha_mem : MemLp a 2 μΩ :=
    ha_cont.memLp_of_hasCompactSupport (μ := μΩ) ha_support
  have hL := L2.tendsto_integral_real_smul_of_weak_tendsto
    u hmem_u uLim hu a ha_mem
  have hv_formula (n : ℕ) (z : ℂ) : du n z v =
      v.re • du n z 1 + v.im • du n z Complex.I := by
    have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by
      simpa only [Complex.real_smul, mul_one] using
        (Complex.re_add_im v).symm
    calc
      _ = du n z (v.re • (1 : ℂ) + v.im • Complex.I) :=
        congrArg (du n z) hv
      _ = _ := by rw [map_add, map_smul, map_smul]
  let hmem_v : ∀ n, MemLp (fun z ↦ du n z v) 2 μΩ := fun n ↦
    (((hmem_x n).const_smul v.re).add
      ((hmem_y n).const_smul v.im)).ae_eq
        (Filter.Eventually.of_forall fun z ↦ (hv_formula n z).symm)
  let dLimV : Lp ℂ 2 μΩ := v.re • dxLim + v.im • dyLim
  have htoLp_v (n : ℕ) : (hmem_v n).toLp (fun z ↦ du n z v) =
      v.re • (hmem_x n).toLp (fun z ↦ du n z 1) +
        v.im • (hmem_y n).toLp (fun z ↦ du n z Complex.I) := by
    let hxv := (hmem_x n).const_smul v.re
    let hyv := (hmem_y n).const_smul v.im
    have hcongr := MemLp.toLp_congr (hmem_v n) (hxv.add hyv)
      (Filter.Eventually.of_forall fun z ↦ hv_formula n z)
    calc
      _ = (hxv.add hyv).toLp
          (v.re • (fun z ↦ du n z 1) +
            v.im • (fun z ↦ du n z Complex.I)) := hcongr
      _ = _ := by
        rw [MemLp.toLp_add hxv hyv,
          MemLp.toLp_const_smul v.re (hmem_x n),
          MemLp.toLp_const_smul v.im (hmem_y n)]
  have hweak_v : Tendsto
      (fun n ↦ toWeakSpace ℝ (Lp ℂ 2 μΩ)
        ((hmem_v n).toLp (fun z ↦ du n z v))) atTop
      (nhds (toWeakSpace ℝ (Lp ℂ 2 μΩ) dLimV)) := by
    have hcomb := hx.const_smul v.re |>.add (hy.const_smul v.im)
    have hcomb' : Tendsto
        (fun n ↦ toWeakSpace ℝ (Lp ℂ 2 μΩ)
          (v.re • (hmem_x n).toLp (fun z ↦ du n z 1) +
            v.im • (hmem_y n).toLp (fun z ↦ du n z Complex.I))) atTop
        (nhds (toWeakSpace ℝ (Lp ℂ 2 μΩ) dLimV)) := by
      simpa only [map_smul, map_add, dLimV] using hcomb
    exact hcomb'.congr'
      (Filter.Eventually.of_forall fun n ↦ by
        exact congrArg (toWeakSpace ℝ (Lp ℂ 2 μΩ)) (htoLp_v n).symm)
  have hR0 := L2.tendsto_integral_real_smul_of_weak_tendsto
    (fun n z ↦ du n z v) hmem_v dLimV hweak_v
      (fun z ↦ φ z) hφ_mem
  have hdLim_ae : (fun z ↦ dLimV z) =ᵐ[μΩ]
      fun z ↦ realLinearMapOfCoordinateValues (dxLim z) (dyLim z) v := by
    filter_upwards [Lp.coeFn_add (v.re • dxLim) (v.im • dyLim),
      Lp.coeFn_smul v.re dxLim, Lp.coeFn_smul v.im dyLim] with z hadd hxz hyz
    calc
      dLimV z = (v.re • dxLim) z + (v.im • dyLim) z := by
        simpa only [Pi.add_apply] using hadd
      _ = v.re • dxLim z + v.im • dyLim z := by
        rw [hxz, hyz]
        simp only [Pi.smul_apply]
      _ = _ := by
        simp only [realLinearMapOfCoordinateValues,
          ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
          Complex.reCLM_apply, Complex.imCLM_apply]
  have hR' : Tendsto (fun n ↦ ∫ z, φ z • du n z v ∂μΩ) atTop
      (nhds (∫ z, φ z •
        realLinearMapOfCoordinateValues (dxLim z) (dyLim z) v ∂μΩ)) := by
    have hlimEq : (∫ z, φ z • dLimV z ∂μΩ) =
        ∫ z, φ z •
          realLinearMapOfCoordinateValues (dxLim z) (dyLim z) v ∂μΩ := by
      apply integral_congr_ae
      filter_upwards [hdLim_ae] with z hz
      rw [hz]
    rw [hlimEq] at hR0
    exact hR0
  have hLseq (n : ℕ) :
      ∫ z, a z • u n z ∂μΩ = -∫ z, φ z • du n z v ∂μΩ := by
    simpa [a, μΩ] using (hweak n φ v).2.2
  have hEq :
      (∫ z, a z • uLim z ∂μΩ) =
        -∫ z, φ z •
          realLinearMapOfCoordinateValues (dxLim z) (dyLim z) v ∂μΩ := by
    exact tendsto_nhds_unique
      (hL.congr' (Filter.Eventually.of_forall hLseq)) hR'.neg
  refine ⟨?_, ?_, ?_⟩
  · have ha_complex : MemLp (fun z ↦ (a z : ℂ)) 2 μΩ := by
      simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
        Complex.ofRealCLM.comp_memLp' ha_mem
    exact memLp_one_iff_integrable.mp
      ((Lp.memLp uLim).mul ha_complex) |>.congr (by
        filter_upwards [] with z
        simp [a])
  · have hdv_mem : MemLp
        (fun z ↦ realLinearMapOfCoordinateValues (dxLim z) (dyLim z) v)
        2 μΩ := by
      exact (Lp.memLp dLimV).ae_eq hdLim_ae
    have hφ_complex : MemLp (fun z ↦ (φ z : ℂ)) 2 μΩ := by
      simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
        Complex.ofRealCLM.comp_memLp' hφ_mem
    exact memLp_one_iff_integrable.mp (hdv_mem.mul hφ_complex) |>.congr (by
      filter_upwards [] with z
      simp)
  · simpa [a, μΩ] using hEq

/--
%%handwave
name:
  Weak derivative identities glue over the integer disk exhaustion
statement:
  Let $u:\mathbb C\to\mathbb C$ and
  $D u:\mathbb C\to\operatorname{Lin}_{\mathbb R}(\mathbb C,\mathbb C)$.
  If $D u$ is a weak differential of $u$ on every closed disk
  $\overline B(0,m)$ with $m\in\mathbb N$, then it is a weak differential
  of $u$ on all of $\mathbb C$.
proof:
  Every smooth compactly supported test function has support in one
  integer-radius disk. Apply the weak derivative identity on that disk.
  Both test integrands vanish outside it, so their disk integrals and
  whole-plane integrals agree.
-/
theorem isWeakDerivativeOn_univ_of_closedBall_exhaustion
    {u : ℂ → ℂ} {du : ℂ → ℂ →L[ℝ] ℂ}
    (hweak : ∀ m : ℕ,
      JJMath.Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues
        (Metric.closedBall (0 : ℂ) (m : ℝ)) u du) :
    JJMath.Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues
      Set.univ u du := by
  intro φ v
  obtain ⟨R, hR⟩ :=
    φ.compact_support.isBounded.subset_closedBall (0 : ℂ)
  obtain ⟨m : ℕ, hm⟩ := exists_nat_gt R
  have hsupp : tsupport (φ : ℂ → ℝ) ⊆
      Metric.closedBall (0 : ℂ) (m : ℝ) :=
    hR.trans (Metric.closedBall_subset_closedBall hm.le)
  let ψ : JJMath.Uniformization.SmoothCompactlySupportedManifoldCoordinateFunction
      (Metric.closedBall (0 : ℂ) (m : ℝ)) :=
    { toFun := φ
      smooth := φ.smooth
      support_subset := hsupp
      compact_support := φ.compact_support }
  rcases hweak m ψ v with ⟨hleft_disk, hright_disk, heq_disk⟩
  let left : ℂ → ℂ := fun z ↦
    (fderiv ℝ (φ : ℂ → ℝ) z v) • u z
  let right : ℂ → ℂ := fun z ↦ φ z • du z v
  have hleft_support : Function.support left ⊆
      Metric.closedBall (0 : ℂ) (m : ℝ) := by
    intro z hz
    apply hsupp
    apply (tsupport_fderiv_apply_subset (𝕜 := ℝ)
      (f := (φ : ℂ → ℝ)) v)
    apply subset_tsupport
    intro hzero
    exact hz (by simp [left, hzero])
  have hright_support : Function.support right ⊆
      Metric.closedBall (0 : ℂ) (m : ℝ) := by
    intro z hz
    apply hsupp
    apply subset_tsupport
    intro hzero
    exact hz (by simp [right, hzero])
  have hleft_global : Integrable left volume :=
    (integrableOn_iff_integrable_of_support_subset hleft_support).mp
      (by simpa [left, ψ] using hleft_disk)
  have hright_global : Integrable right volume :=
    (integrableOn_iff_integrable_of_support_subset hright_support).mp
      (by simpa [right, ψ] using hright_disk)
  have hleft_eq :
      ∫ z in Metric.closedBall (0 : ℂ) (m : ℝ), left z ∂volume =
        ∫ z, left z ∂volume := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    by_contra hne
    exact hz (hleft_support hne)
  have hright_eq :
      ∫ z in Metric.closedBall (0 : ℂ) (m : ℝ), right z ∂volume =
        ∫ z, right z ∂volume := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    by_contra hne
    exact hz (hright_support hne)
  refine ⟨?_, ?_, ?_⟩
  · simpa [left] using hleft_global
  · simpa [right] using hright_global
  · calc
      ∫ z in Set.univ, (fderiv ℝ (φ : ℂ → ℝ) z v) • u z ∂volume =
          ∫ z, left z ∂volume := by simp [left]
      _ = ∫ z in Metric.closedBall (0 : ℂ) (m : ℝ), left z ∂volume :=
        hleft_eq.symm
      _ = -∫ z in Metric.closedBall (0 : ℂ) (m : ℝ), right z ∂volume := by
        simpa [left, right, ψ] using heq_disk
      _ = -∫ z, right z ∂volume := by rw [hright_eq]
      _ = -∫ z in Set.univ, φ z • du z v ∂volume := by simp [right]

/--
%%handwave
name:
  Finite-chart values are square-integrable on closed disks
statement:
  Let $F:\widehat{\mathbb C}\to\widehat{\mathbb C}$ be a normalized sphere
  homeomorphism and let $f:\mathbb C\to\mathbb C$ be its finite-chart
  representative. For every $R\in\mathbb R$,
  $$
    f\in L^2\bigl(\overline B(0,R);\mathbb C\bigr).
  $$
proof:
  The finite-chart representative is continuous, and every continuous
  function is square-integrable on a compact planar set.
-/
theorem finiteChart_memLp_on_closedBall
    (F : RiemannSphere ≃ₜ RiemannSphere)
    (hF : IsNormalizedRiemannSphereHomeomorph F) (R : ℝ) :
    MemLp (riemannSphereFiniteChartHomeomorph F hF.2.2) 2
      (volume.restrict (Metric.closedBall (0 : ℂ) R)) := by
  exact memLp_restrict_of_isCompact_of_continuousOn
    (isCompact_closedBall (0 : ℂ) R)
    (riemannSphereFiniteChartHomeomorph F hF.2.2).continuous.continuousOn

/--
%%handwave
name:
  Spherical uniform convergence gives compact-uniform finite-coordinate convergence
statement:
  Let $F_n$ be normalized $K$-quasiconformal self-homeomorphisms of the
  Riemann sphere and suppose $F_n\to G$ uniformly on the sphere, where $G$ is
  normalized. If $f_n,g:\mathbb C\to\mathbb C$ are their finite-chart
  representatives, then for every compact $C\subseteq\mathbb C$,
  $$
    f_n\longrightarrow g
    \quad\text{uniformly on }C.
  $$
proof:
  Put $C$ in one source disk. The normalized capacity estimate places every
  $f_n(C)$ in one target disk. Its image in the sphere is compact and avoids
  infinity; spherical uniform convergence and closedness put $G(C)$ there as
  well. The finite chart is uniformly continuous on this compact target set,
  so composing the spherical convergence with it gives uniform convergence
  in finite coordinates.
-/
theorem finiteChart_tendstoUniformlyOn_compact_of_tendstoUniformly
    (K : ℝ) (F : ℕ → RiemannSphere ≃ₜ RiemannSphere)
    (hqc : ∀ n, IsKQuasiconformalRiemannSphere K (F n))
    (hnorm : ∀ n, IsNormalizedRiemannSphereHomeomorph (F n))
    (G : RiemannSphere ≃ₜ RiemannSphere)
    (hGnorm : IsNormalizedRiemannSphereHomeomorph G)
    (hconv : TendstoUniformly (fun n z ↦ F n z) (fun z ↦ G z) atTop)
    (C : Set ℂ) (hC : IsCompact C) :
    TendstoUniformlyOn
      (fun n z ↦ riemannSphereFiniteChartHomeomorph (F n) (hnorm n).2.2 z)
      (riemannSphereFiniteChartHomeomorph G hGnorm.2.2) atTop C := by
  obtain ⟨R, hCR⟩ := hC.isBounded.subset_closedBall (0 : ℂ)
  obtain ⟨M, _hM, hbound⟩ :=
    exists_uniform_finiteChart_norm_bound_on_closedBall K R
  let S : Set RiemannSphere :=
    ((fun z : ℂ ↦ (z : RiemannSphere)) '' Metric.closedBall (0 : ℂ) M)
  have hScompact : IsCompact S :=
    (isCompact_closedBall (0 : ℂ) M).image OnePoint.continuous_coe
  have hFS (n : ℕ) (z : ℂ) (hz : z ∈ C) :
      F n (z : RiemannSphere) ∈ S := by
    let y := riemannSphereFiniteChartHomeomorph (F n) (hnorm n).2.2 z
    have hzR : ‖z‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hCR hz
    have hyM : ‖y‖ ≤ M := (hbound (F n) (hqc n) (hnorm n) z hzR).le
    refine ⟨y, ?_, ?_⟩
    · simpa [Metric.mem_closedBall, dist_zero_right]
    · exact coe_riemannSphereFiniteChartHomeomorph_apply
        (F n) (hnorm n).2.2 z
  have hGS (z : ℂ) (hz : z ∈ C) : G (z : RiemannSphere) ∈ S := by
    apply hScompact.isClosed.mem_of_tendsto (hconv.tendsto_at (z : RiemannSphere))
    exact Filter.Eventually.of_forall fun n ↦ hFS n z hz
  have hSsource : S ⊆ riemannSphereFiniteChart.source := by
    rintro _ ⟨z, _hz, rfl⟩
    simp
  have hchartUC : UniformContinuousOn
      (riemannSphereFiniteChart : RiemannSphere → ℂ) S :=
    hScompact.uniformContinuousOn_of_continuous
      (riemannSphereFiniteChart.continuousOn.mono hSsource)
  have hsphere : TendstoUniformlyOn
      (fun n (z : ℂ) ↦ F n (z : RiemannSphere))
      (fun z : ℂ ↦ G (z : RiemannSphere)) atTop C :=
    (hconv.comp fun z : ℂ ↦ (z : RiemannSphere)).tendstoUniformlyOn
  have hchart := hchartUC.comp_tendstoUniformlyOn_eventually
    (Filter.Eventually.of_forall hFS) hGS hsphere
  simpa only [riemannSphereFiniteChartHomeomorph_apply] using hchart

/--
%%handwave
name:
  Whole-plane homeomorphism between universal domains
statement:
  A homeomorphism $f:\mathbb C\to\mathbb C$ canonically determines a
  homeomorphism between the source and target domains both equal to
  $\mathbb C$.
-/
def univHomeomorphOfHomeomorph (f : ℂ ≃ₜ ℂ) :
    (Set.univ : Set ℂ) ≃ₜ (Set.univ : Set ℂ) where
  toFun z := ⟨f z, Set.mem_univ _⟩
  invFun z := ⟨f.symm z, Set.mem_univ _⟩
  left_inv z := Subtype.ext (f.symm_apply_apply z)
  right_inv z := Subtype.ext (f.apply_symm_apply z)
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/--
%%handwave
name:
  Finite-chart domain homeomorphism of a sphere map
statement:
  If $F:\widehat{\mathbb C}\to\widehat{\mathbb C}$ fixes $\infty$, its
  finite-chart representative is regarded as a homeomorphism from
  $\mathbb C$ to $\mathbb C$.
-/
def riemannSphereFiniteChartSetHomeomorph
    (F : RiemannSphere ≃ₜ RiemannSphere)
    (hInf : F OnePoint.infty = OnePoint.infty) :
    (Set.univ : Set ℂ) ≃ₜ (Set.univ : Set ℂ) :=
  univHomeomorphOfHomeomorph
    (riemannSphereFiniteChartHomeomorph F hInf)

/--
%%handwave
name:
  Finite-chart orientation of a normalized quasiconformal sphere map
statement:
  If $F:\widehat{\mathbb C}\to\widehat{\mathbb C}$ is normalized and
  $K$-quasiconformal, then its whole-plane finite-chart homeomorphism
  $f:\mathbb C\to\mathbb C$, regarded as a map between two copies of
  $\mathbb C$, preserves planar orientation.
proof:
  The finite-to-finite standard chart representation preserves orientation
  by spherical quasiconformality. Normalization makes both chart domains the
  whole plane, and the whole-plane representative agrees pointwise with that
  chart map, so orientation preservation restricts to the canonical copies
  of $\mathbb C$.
-/
theorem IsKQuasiconformalRiemannSphere.preservesPlanarOrientation_finiteChartSetHomeomorph
    {K : ℝ} {F : RiemannSphere ≃ₜ RiemannSphere}
    (hqc : IsKQuasiconformalRiemannSphere K F)
    (hF : IsNormalizedRiemannSphereHomeomorph F) :
    PreservesPlanarOrientation
      (riemannSphereFiniteChartSetHomeomorph F hF.2.2) := by
  let H := riemannSphereChartHomeomorph F .finite .finite
  have hsource :=
    riemannSphere_finiteChartRepresentation_source_eq_univ_of_map_infty
      F hF.2.2
  have horient := (hqc .finite .finite).2.2.1
  apply horient.restrict isOpen_univ
    (by simpa only [hsource] using (Set.subset_univ (Set.univ : Set ℂ)))
  intro z
  change riemannSphereFiniteChartHomeomorph F hF.2.2 z = H ⟨z, _⟩
  rw [← ambientMap_finiteChartHomeomorph_apply F hF.2.2 z]
  exact ambientMap_apply H ⟨z, by rw [hsource]; exact Set.mem_univ _⟩

/--
%%handwave
name:
  Whole-plane finite chart of a normalized quasiconformal sphere map
statement:
  If $F:\widehat{\mathbb C}\to\widehat{\mathbb C}$ is normalized and
  $K$-quasiconformal, then its finite-chart representative, regarded as a
  homeomorphism between two copies of $\mathbb C$, is $K$-quasiconformal.
proof:
  Normalization makes the source of the finite-to-finite standard chart the
  whole plane. Restrict the corresponding chartwise quasiconformality
  assertion to this universal domain and identify its values with the
  whole-plane finite-chart representative.
-/
theorem IsKQuasiconformalRiemannSphere.finiteChartSetHomeomorph
    {K : ℝ} {F : RiemannSphere ≃ₜ RiemannSphere}
    (hqc : IsKQuasiconformalRiemannSphere K F)
    (hF : IsNormalizedRiemannSphereHomeomorph F) :
    IsKQuasiconformalBetween K
      (riemannSphereFiniteChartSetHomeomorph F hF.2.2) := by
  let H := riemannSphereChartHomeomorph F .finite .finite
  have hsource :=
    riemannSphere_finiteChartRepresentation_source_eq_univ_of_map_infty
      F hF.2.2
  apply (hqc .finite .finite).restrict isOpen_univ isOpen_univ
    (by simpa only [hsource] using (Set.subset_univ (Set.univ : Set ℂ)))
  intro z
  change riemannSphereFiniteChartHomeomorph F hF.2.2 z = H ⟨z, _⟩
  rw [← ambientMap_finiteChartHomeomorph_apply F hF.2.2 z]
  exact ambientMap_apply H ⟨z, by rw [hsource]; exact Set.mem_univ _⟩

/--
%%handwave
name:
  Finite-chart orientation of a normalized quasiconformal limit
statement:
  Let $F_n$ be normalized $K$-quasiconformal sphere homeomorphisms converging
  uniformly on the sphere to a normalized homeomorphism $G$. Then the
  whole-plane finite-chart homeomorphism of $G$ preserves planar orientation.
proof:
  Each finite chart preserves orientation. Spherical uniform convergence
  gives [uniform finite-coordinate convergence on every compact planar
  set](lean:JJMath.Quasiconformal.finiteChart_tendstoUniformlyOn_compact_of_tendstoUniformly). Apply [orientation preservation under compact-uniform homeomorphic limits](lean:JJMath.Quasiconformal.preservesPlanarOrientation_of_compactly_tendstoUniformly).
-/
theorem preservesPlanarOrientation_finiteChartSetHomeomorph_of_tendstoUniformly
    (K : ℝ) (F : ℕ → RiemannSphere ≃ₜ RiemannSphere)
    (hqc : ∀ n, IsKQuasiconformalRiemannSphere K (F n))
    (hnorm : ∀ n, IsNormalizedRiemannSphereHomeomorph (F n))
    (G : RiemannSphere ≃ₜ RiemannSphere)
    (hGnorm : IsNormalizedRiemannSphereHomeomorph G)
    (hconv : TendstoUniformly (fun n z ↦ F n z) (fun z ↦ G z) atTop) :
    PreservesPlanarOrientation
      (riemannSphereFiniteChartSetHomeomorph G hGnorm.2.2) := by
  apply preservesPlanarOrientation_of_compactly_tendstoUniformly isOpen_univ
    (fun n ↦ riemannSphereFiniteChartSetHomeomorph (F n) (hnorm n).2.2)
    (riemannSphereFiniteChartSetHomeomorph G hGnorm.2.2)
    (fun n ↦ (hqc n).preservesPlanarOrientation_finiteChartSetHomeomorph
      (hnorm n))
  intro C hC
  let C' : Set ℂ := ((fun z : (Set.univ : Set ℂ) ↦ (z : ℂ)) '' C)
  have hC' : IsCompact C' := hC.image continuous_subtype_val
  have hfinite := finiteChart_tendstoUniformlyOn_compact_of_tendstoUniformly
    K F hqc hnorm G hGnorm hconv C' hC'
  rw [Metric.tendstoUniformlyOn_iff] at hfinite ⊢
  intro ε hε
  filter_upwards [hfinite ε hε] with n hn
  intro z hz
  exact hn z ⟨z, hz, rfl⟩

/--
%%handwave
name:
  Orientation of the finite standard chart of a normalized quasiconformal limit
statement:
  Let $F_n$ be normalized $K$-quasiconformal sphere homeomorphisms converging
  uniformly to a normalized homeomorphism $G$. Then the finite-to-finite
  standard chart representation of $G$ preserves planar orientation.
proof:
  The [whole-plane finite-chart limit preserves orientation](lean:JJMath.Quasiconformal.preservesPlanarOrientation_finiteChartSetHomeomorph_of_tendstoUniformly). Normalization identifies the source of the actual finite standard chart with $\mathbb C$, and its ambient representative agrees with the whole-plane chart, so restrict the orientation statement to that chart homeomorphism.
-/
theorem preservesPlanarOrientation_finiteChart_of_tendstoUniformly
    (K : ℝ) (F : ℕ → RiemannSphere ≃ₜ RiemannSphere)
    (hqc : ∀ n, IsKQuasiconformalRiemannSphere K (F n))
    (hnorm : ∀ n, IsNormalizedRiemannSphereHomeomorph (F n))
    (G : RiemannSphere ≃ₜ RiemannSphere)
    (hGnorm : IsNormalizedRiemannSphereHomeomorph G)
    (hconv : TendstoUniformly (fun n z ↦ F n z) (fun z ↦ G z) atTop) :
    PreservesPlanarOrientation
      (riemannSphereChartHomeomorph G .finite .finite) := by
  have hcanon :=
    preservesPlanarOrientation_finiteChartSetHomeomorph_of_tendstoUniformly
      K F hqc hnorm G hGnorm hconv
  let H := riemannSphereChartHomeomorph G .finite .finite
  have hsource :=
    riemannSphere_finiteChartRepresentation_source_eq_univ_of_map_infty
      G hGnorm.2.2
  apply hcanon.restrict (by rw [hsource]; exact isOpen_univ)
    (Set.subset_univ _)
  intro z
  calc
    (H z : ℂ) = ambientMap H z := (ambientMap_apply H z).symm
    _ = riemannSphereFiniteChartHomeomorph G hGnorm.2.2 z :=
      ambientMap_finiteChartHomeomorph_apply G hGnorm.2.2 z
    _ = riemannSphereFiniteChartSetHomeomorph G hGnorm.2.2
        ⟨z, Set.mem_univ _⟩ := rfl

/--
%%handwave
name:
  The finite chart of a Beltrami limit is quasiconformal
statement:
  Let $F_n:\widehat{\mathbb C}\to\widehat{\mathbb C}$ be normalized
  $K$-quasiconformal homeomorphisms converging uniformly to a normalized
  homeomorphism $G$. Suppose the finite-chart representative $g$ belongs to
  $W^{1,2}_{\mathrm{loc}}(\mathbb C,\mathbb C)$ with weak differential $Dg$
  satisfying
  $$
    \partial_{\bar z}g=\mu\,\partial_zg,
    \qquad |\mu|\leq k<1
  $$
  almost everywhere, where $k\geq0$. Then the finite-to-finite standard
  chart of $G$ is $((1+k)/(1-k))$-quasiconformal.
proof:
  The [finite standard chart preserves orientation](lean:JJMath.Quasiconformal.preservesPlanarOrientation_finiteChart_of_tendstoUniformly). Normalization identifies both finite chart domains with the whole plane, and the ambient chart representative agrees with $g$. Apply [the bounded Beltrami equation criterion](lean:JJMath.Quasiconformal.isKQuasiconformalBetween_of_weakBeltrami).
-/
theorem isKQuasiconformalBetween_finiteChart_of_tendstoUniformly_of_weakBeltrami
    (K k : ℝ) (F : ℕ → RiemannSphere ≃ₜ RiemannSphere)
    (hqc : ∀ n, IsKQuasiconformalRiemannSphere K (F n))
    (hnorm : ∀ n, IsNormalizedRiemannSphereHomeomorph (F n))
    (G : RiemannSphere ≃ₜ RiemannSphere)
    (hGnorm : IsNormalizedRiemannSphereHomeomorph G)
    (hconv : TendstoUniformly (fun n z ↦ F n z) (fun z ↦ G z) atTop)
    (dG : ℂ → ℂ →L[ℝ] ℂ)
    (hlocal : IsLocalW12On Set.univ
      (riemannSphereFiniteChartHomeomorph G hGnorm.2.2) dG)
    (μ : ℂ → ℂ)
    (heq : WeakBeltramiEquationOn Set.univ μ dG)
    (hμ : HasEssentialNormLEOn Set.univ μ k)
    (hk0 : 0 ≤ k) (hk1 : k < 1) :
    IsKQuasiconformalBetween ((1 + k) / (1 - k))
      (riemannSphereChartHomeomorph G .finite .finite) := by
  have hsource :=
    riemannSphere_finiteChartRepresentation_source_eq_univ_of_map_infty
      G hGnorm.2.2
  have htarget :=
    riemannSphere_finiteChartRepresentation_target_eq_univ_of_map_infty
      G hGnorm.2.2
  have hlocal' : IsLocalW12On
      (riemannSphereChartRepresentation G .finite .finite).source
      (ambientMap (riemannSphereChartHomeomorph G .finite .finite)) dG := by
    apply (hlocal.mono
      (riemannSphereChartRepresentation G .finite .finite).open_source
      (Set.subset_univ _)).congr_ae
    exact Filter.Eventually.of_forall fun z ↦
      ambientMap_finiteChartHomeomorph_apply G hGnorm.2.2 z
  apply isKQuasiconformalBetween_of_weakBeltrami
    (by rw [htarget]; exact isOpen_univ)
    (preservesPlanarOrientation_finiteChart_of_tendstoUniformly
      K F hqc hnorm G hGnorm hconv)
    hlocal'
  · rwa [hsource]
  · rwa [hsource]
  · exact hk0
  · exact hk1

/--
%%handwave
name:
  Spherical uniform convergence gives finite-coordinate pointwise convergence
statement:
  Let $F_n$ and $G$ be normalized homeomorphisms of the Riemann sphere, with
  finite-chart representatives $f_n$ and $g$. If $F_n\to G$ uniformly on
  the sphere, then for every $z\in\mathbb C$,
  $$
    f_n(z)\longrightarrow g(z).
  $$
proof:
  Spherical uniform convergence gives convergence at the finite point $z$.
  All values and the limit are finite because the homeomorphisms fix
  infinity. The standard inclusion
  $\mathbb C\hookrightarrow\widehat{\mathbb C}$ is an open embedding, so
  convergence of these finite spherical points is equivalent to convergence
  of their complex coordinates.
-/
theorem finiteChart_tendsto_at_of_tendstoUniformly
    (F : ℕ → RiemannSphere ≃ₜ RiemannSphere)
    (hnorm : ∀ n, IsNormalizedRiemannSphereHomeomorph (F n))
    (G : RiemannSphere ≃ₜ RiemannSphere)
    (hGnorm : IsNormalizedRiemannSphereHomeomorph G)
    (hconv : TendstoUniformly (fun n z ↦ F n z) (fun z ↦ G z) atTop)
    (z : ℂ) :
    Tendsto
      (fun n ↦ riemannSphereFiniteChartHomeomorph (F n) (hnorm n).2.2 z)
      atTop
      (nhds (riemannSphereFiniteChartHomeomorph G hGnorm.2.2 z)) := by
  rw [OnePoint.isOpenEmbedding_coe.tendsto_nhds_iff]
  simpa only [Function.comp_def,
    coe_riemannSphereFiniteChartHomeomorph_apply] using
      hconv.tendsto_at ((z : ℂ) : RiemannSphere)

/--
%%handwave
name:
  Spherical uniform convergence gives local strong $L^2$ convergence in the finite chart
statement:
  Let $F_n:\widehat{\mathbb C}\to\widehat{\mathbb C}$ be normalized
  $K$-quasiconformal homeomorphisms converging uniformly on the sphere to a
  normalized homeomorphism $G$. If $f_n$ and $g$ are their finite-chart
  representatives, then for every $R\in\mathbb R$,
  $$
    f_n\longrightarrow g
    \quad\text{strongly in }L^2\bigl(\overline B(0,R);\mathbb C\bigr).
  $$
proof:
  Finite coordinates converge pointwise. The normalized capacity estimates
  bound all $|f_n|$ uniformly on the disk; passing this closed bound to the
  pointwise limit also bounds $|g|$. Thus $|f_n-g|$ is dominated by a
  constant square-integrable on the finite-area disk. Dominated convergence
  applied to $|f_n-g|^2$ gives the strong $L^2$ convergence.
-/
theorem finiteChart_toLp_tendsto_of_tendstoUniformly
    (K R : ℝ) (F : ℕ → RiemannSphere ≃ₜ RiemannSphere)
    (hqc : ∀ n, IsKQuasiconformalRiemannSphere K (F n))
    (hnorm : ∀ n, IsNormalizedRiemannSphereHomeomorph (F n))
    (G : RiemannSphere ≃ₜ RiemannSphere)
    (hGnorm : IsNormalizedRiemannSphereHomeomorph G)
    (hconv : TendstoUniformly (fun n z ↦ F n z) (fun z ↦ G z) atTop) :
    Tendsto
      (fun n ↦
        (finiteChart_memLp_on_closedBall (F n) (hnorm n) R).toLp
          (riemannSphereFiniteChartHomeomorph (F n) (hnorm n).2.2))
      atTop
      (nhds
        ((finiteChart_memLp_on_closedBall G hGnorm R).toLp
          (riemannSphereFiniteChartHomeomorph G hGnorm.2.2))) := by
  let μR : Measure ℂ :=
    volume.restrict (Metric.closedBall (0 : ℂ) R)
  let f : ℕ → ℂ → ℂ := fun n ↦
    riemannSphereFiniteChartHomeomorph (F n) (hnorm n).2.2
  let g : ℂ → ℂ :=
    riemannSphereFiniteChartHomeomorph G hGnorm.2.2
  let hmem_f : ∀ n, MemLp (f n) 2 μR := fun n ↦
    finiteChart_memLp_on_closedBall (F n) (hnorm n) R
  let hmem_g : MemLp g 2 μR :=
    finiteChart_memLp_on_closedBall G hGnorm R
  obtain ⟨M, _hM, hbound⟩ :=
    exists_uniform_finiteChart_norm_bound_on_closedBall K R
  have hpoint (z : ℂ) : Tendsto (fun n ↦ f n z) atTop (nhds (g z)) := by
    exact finiteChart_tendsto_at_of_tendstoUniformly
      F hnorm G hGnorm hconv z
  have hg_bound {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) R) :
      ‖g z‖ ≤ M := by
    apply le_of_tendsto (hpoint z).norm
    exact Filter.Eventually.of_forall fun n ↦
      (hbound (F n) (hqc n) (hnorm n) z (by
        simpa [Metric.mem_closedBall, dist_zero_right] using hz)).le
  let a : ℂ → ℝ := fun _ ↦ 1
  letI : IsFiniteMeasure μR :=
    isFiniteMeasure_restrict.2 measure_closedBall_lt_top.ne
  have ha : MemLp a 2 μR := by
    apply MemLp.of_bound aestronglyMeasurable_const 1
    filter_upwards with z
    simp
  let b : ℕ → ℂ → ℂ := fun n z ↦ f n z - g z
  have hb_meas : ∀ n, AEStronglyMeasurable (b n) μR := fun n ↦
    (hmem_f n).aestronglyMeasurable.sub hmem_g.aestronglyMeasurable
  have hb_bound : ∀ n, ∀ᵐ z ∂μR, ‖b n z‖ ≤ (2 * M) * ‖a z‖ := by
    intro n
    apply ae_restrict_of_forall_mem measurableSet_closedBall
    intro z hz
    calc
      ‖b n z‖ ≤ ‖f n z‖ + ‖g z‖ := norm_sub_le _ _
      _ ≤ M + M := add_le_add
        (hbound (F n) (hqc n) (hnorm n) z (by
          simpa [Metric.mem_closedBall, dist_zero_right] using hz)).le
        (hg_bound hz)
      _ = (2 * M) * ‖a z‖ := by simp [a]; ring
  have hb_zero : ∀ᵐ z ∂μR,
      Tendsto (fun n ↦ b n z) atTop (nhds 0) := by
    filter_upwards with z
    simpa [b] using (hpoint z).sub_const (g z)
  obtain ⟨hb_mem, hb_norm⟩ :=
    memLp_and_tendsto_zero_of_ae_tendsto_of_norm_le_mul
      ha hb_meas hb_bound hb_zero
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hmem_f g hmem_g).2
  simpa only [Pi.sub_apply, b] using hb_norm

/--
%%handwave
name:
  Weak extraction on one disk for a prescribed differential sequence
statement:
  Let $F_n$ be normalized $K$-quasiconformal sphere homeomorphisms, fix
  $R\in\mathbb R$, and choose one finite-chart weak differential $DF_n$ for
  every $n$. There are a strictly increasing $\varphi:\mathbb N\to\mathbb N$
  and fields $A,B\in L^2(\overline B(0,R);\mathbb C)$ such that
  $$
    DF_{\varphi(n)}(1)\rightharpoonup A,
    \qquad
    DF_{\varphi(n)}(i)\rightharpoonup B.
  $$
proof:
  The uniform disk-energy estimate applies to the prescribed weak
  differentials because such representatives agree almost everywhere.
  Evaluation at $1$ and $i$ is bounded by the operator norm. Extract weakly
  for the first coordinate and then along a further subsequence for the
  second.
-/
theorem normalizedKQuasiconformalRiemannSphere_fixedDisk_weakDifferential_subsequence_of_isLocalW12On
    (K R : ℝ) (F : ℕ → RiemannSphere ≃ₜ RiemannSphere)
    (hqc : ∀ n, IsKQuasiconformalRiemannSphere K (F n))
    (hnorm : ∀ n, IsNormalizedRiemannSphereHomeomorph (F n))
    (df : ℕ → ℂ → ℂ →L[ℝ] ℂ)
    (hdf : ∀ n, IsLocalW12On Set.univ
      (riemannSphereFiniteChartHomeomorph (F n) (hnorm n).2.2) (df n)) :
    ∃ dxLim dyLim : Lp ℂ 2
        (volume.restrict (Metric.closedBall (0 : ℂ) R)),
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto
          (fun n ↦ toWeakSpace ℝ
            (Lp ℂ 2
              (volume.restrict (Metric.closedBall (0 : ℂ) R)))
            (((ContinuousLinearMap.apply ℝ ℂ) 1 |>.comp_memLp'
              (((hdf (φ n)).2.2
                (Metric.closedBall (0 : ℂ) R)
                (isCompact_closedBall (0 : ℂ) R) (Set.subset_univ _)).2)).toLp
                  (fun z ↦ df (φ n) z 1)))
          atTop
            (nhds (toWeakSpace ℝ
              (Lp ℂ 2
                (volume.restrict (Metric.closedBall (0 : ℂ) R))) dxLim)) ∧
        Tendsto
          (fun n ↦ toWeakSpace ℝ
            (Lp ℂ 2
              (volume.restrict (Metric.closedBall (0 : ℂ) R)))
            (((ContinuousLinearMap.apply ℝ ℂ) Complex.I |>.comp_memLp'
              (((hdf (φ n)).2.2
                (Metric.closedBall (0 : ℂ) R)
                (isCompact_closedBall (0 : ℂ) R) (Set.subset_univ _)).2)).toLp
                  (fun z ↦ df (φ n) z Complex.I)))
          atTop
            (nhds (toWeakSpace ℝ
              (Lp ℂ 2
                (volume.restrict (Metric.closedBall (0 : ℂ) R))) dyLim)) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_uniform_finiteChart_weakDifferential_energy_bound_of_isLocalW12On K R
  have henergy : ∀ n,
      (∫⁻ z in Metric.closedBall (0 : ℂ) R,
          ENNReal.ofReal (‖df n z‖ ^ 2) ∂volume) ≤ C := by
    intro n
    exact hbound (F n) (hqc n) (hnorm n) (df n) (hdf n)
  let μR : Measure ℂ := volume.restrict (Metric.closedBall (0 : ℂ) R)
  have hmem : ∀ n, MemLp (df n) 2 μR := by
    intro n
    exact (hdf n).2.2 (Metric.closedBall (0 : ℂ) R)
      (isCompact_closedBall (0 : ℂ) R) (Set.subset_univ _) |>.2
  have hmem_x : ∀ n, MemLp (fun z ↦ df n z 1) 2 μR := by
    intro n
    simpa only [Function.comp_def] using
      ((ContinuousLinearMap.apply ℝ ℂ) 1).comp_memLp' (hmem n)
  have henergy_x : ∀ n,
      (∫⁻ z, ENNReal.ofReal (‖df n z 1‖ ^ 2) ∂μR) ≤ C := by
    intro n
    apply (lintegral_mono fun z ↦ ENNReal.ofReal_mono ?_).trans (henergy n)
    gcongr
    simpa using (df n z).le_opNorm (1 : ℂ)
  obtain ⟨dxLim, φ, hφ, hx⟩ :=
    exists_weakly_convergent_L2_subsequence_of_lintegral_norm_sq_le
      (fun n z ↦ df n z 1) hmem_x hC henergy_x
  have hmem_y : ∀ n, MemLp (fun z ↦ df (φ n) z Complex.I) 2 μR := by
    intro n
    simpa only [Function.comp_def] using
      ((ContinuousLinearMap.apply ℝ ℂ) Complex.I).comp_memLp' (hmem (φ n))
  have henergy_y : ∀ n,
      (∫⁻ z, ENNReal.ofReal (‖df (φ n) z Complex.I‖ ^ 2) ∂μR) ≤ C := by
    intro n
    apply (lintegral_mono fun z ↦ ENNReal.ofReal_mono ?_).trans (henergy (φ n))
    gcongr
    simpa using (df (φ n) z).le_opNorm Complex.I
  obtain ⟨dyLim, θ, hθ, hy⟩ :=
    exists_weakly_convergent_L2_subsequence_of_lintegral_norm_sq_le
      (fun n z ↦ df (φ n) z Complex.I) hmem_y hC henergy_y
  refine ⟨dxLim, dyLim, φ ∘ θ, hφ.comp hθ, ?_, ?_⟩
  · simpa only [Function.comp_apply, μR, hmem, hmem_x] using
      hx.comp hθ.tendsto_atTop
  · simpa only [Function.comp_apply, μR, hmem, hmem_y] using hy

/--
%%handwave
name:
  Weak differential subsequence on one finite-chart disk
statement:
  Let $F_n$ be normalized $K$-quasiconformal self-homeomorphisms of the
  Riemann sphere and fix $R\in\mathbb R$. There are finite-chart weak
  differentials $DF_n$, a strictly increasing $\varphi:\mathbb N\to\mathbb N$,
  and fields $A,B\in L^2(\overline B(0,R);\mathbb C)$ such that
  $$
    DF_{\varphi(n)}(1)\rightharpoonup A,
    \qquad
    DF_{\varphi(n)}(i)\rightharpoonup B
  $$
  weakly in $L^2(\overline B(0,R);\mathbb C)$.
proof:
  Choose the weak differentials supplied by local Sobolev regularity. Their
  operator-norm energies have one finite bound on the disk. Evaluation at
  $1$ and $i$ has norm at most the operator norm, so each coordinate field
  has the same bound. Extract weakly first for the $1$-component and then for
  the $i$-component; the second extraction preserves the first weak limit.
-/
theorem normalizedKQuasiconformalRiemannSphere_fixedDisk_weakDifferential_subsequence
    (K R : ℝ) (F : ℕ → RiemannSphere ≃ₜ RiemannSphere)
    (hqc : ∀ n, IsKQuasiconformalRiemannSphere K (F n))
    (hnorm : ∀ n, IsNormalizedRiemannSphereHomeomorph (F n)) :
    ∃ df : ℕ → ℂ → ℂ →L[ℝ] ℂ,
      ∃ hdf : ∀ n, IsLocalW12On Set.univ
        (riemannSphereFiniteChartHomeomorph (F n) (hnorm n).2.2) (df n),
      ∃ dxLim dyLim : Lp ℂ 2
          (volume.restrict (Metric.closedBall (0 : ℂ) R)),
        ∃ φ : ℕ → ℕ, StrictMono φ ∧
          Tendsto
            (fun n ↦ toWeakSpace ℝ
              (Lp ℂ 2
                (volume.restrict (Metric.closedBall (0 : ℂ) R)))
              (((ContinuousLinearMap.apply ℝ ℂ) 1 |>.comp_memLp'
                (((hdf (φ n)).2.2
                  (Metric.closedBall (0 : ℂ) R)
                  (isCompact_closedBall (0 : ℂ) R) (Set.subset_univ _)).2)).toLp
                    (fun z ↦ df (φ n) z 1)))
            atTop
              (𝓝 (toWeakSpace ℝ
                (Lp ℂ 2
                  (volume.restrict (Metric.closedBall (0 : ℂ) R))) dxLim)) ∧
          Tendsto
            (fun n ↦ toWeakSpace ℝ
              (Lp ℂ 2
                (volume.restrict (Metric.closedBall (0 : ℂ) R)))
              (((ContinuousLinearMap.apply ℝ ℂ) Complex.I |>.comp_memLp'
                (((hdf (φ n)).2.2
                  (Metric.closedBall (0 : ℂ) R)
                  (isCompact_closedBall (0 : ℂ) R) (Set.subset_univ _)).2)).toLp
                    (fun z ↦ df (φ n) z Complex.I)))
            atTop
              (𝓝 (toWeakSpace ℝ
                (Lp ℂ 2
                  (volume.restrict (Metric.closedBall (0 : ℂ) R))) dyLim)) := by
  choose df hdf using fun n ↦
    (hqc n).exists_finiteChart_weakDifferential (hnorm n)
  obtain ⟨dxLim, dyLim, φ, hφ, hx, hy⟩ :=
    normalizedKQuasiconformalRiemannSphere_fixedDisk_weakDifferential_subsequence_of_isLocalW12On
      K R F hqc hnorm df hdf
  exact ⟨df, hdf, dxLim, dyLim, φ, hφ, hx, hy⟩

/--
%%handwave
name:
  Finite-chart disk measure
statement:
  For $m\in\mathbb N$, the finite-chart disk measure is planar Lebesgue
  measure restricted to $\overline B(0,m)$.
-/
def finiteChartDiskMeasure (m : ℕ) : Measure ℂ :=
  volume.restrict (Metric.closedBall (0 : ℂ) (m : ℝ))

/--
%%handwave
name:
  Monotonicity of the finite-chart disk measures
statement:
  If $m\leq M$, then planar volume restricted to $\overline B(0,m)$ is at
  most planar volume restricted to $\overline B(0,M)$.
proof:
  The smaller closed disk is contained in the larger one, and restriction of
  a measure is monotone in the restricting set.
-/
theorem finiteChartDiskMeasure_mono {m M : ℕ} (hmM : m ≤ M) :
    finiteChartDiskMeasure m ≤ finiteChartDiskMeasure M := by
  exact Measure.restrict_mono
    (Metric.closedBall_subset_closedBall (by exact_mod_cast hmM)) le_rfl

/--
%%handwave
name:
  Restriction between finite-chart disks
statement:
  If $m\leq M$, restriction of representatives gives a contraction
  $L^2(\overline B(0,M))\to L^2(\overline B(0,m))$.
-/
def finiteChartDiskRestriction {m M : ℕ} (hmM : m ≤ M) :
    Lp ℂ 2 (finiteChartDiskMeasure M) →L[ℝ]
      Lp ℂ 2 (finiteChartDiskMeasure m) :=
  L2.monoMeasure (finiteChartDiskMeasure_mono hmM)

/--
%%handwave
name:
  Integer disk index
statement:
  For $z\in\mathbb C$, its integer disk index is $\lceil|z|\rceil$, the
  least natural-number radius of a centered closed disk containing $z$.
-/
def finiteChartDiskIndex (z : ℂ) : ℕ := Nat.ceil ‖z‖

/--
%%handwave
name:
  A point lies in its least integer-radius disk
statement:
  For $z\in\mathbb C$, let $m=\lceil |z|\rceil$. Then
  $$
    z\in\overline B(0,m).
  $$
proof:
  This is the defining inequality $|z|\leq\lceil|z|\rceil$ for the ceiling.
-/
theorem mem_closedBall_finiteChartDiskIndex (z : ℂ) :
    z ∈ Metric.closedBall (0 : ℂ) (finiteChartDiskIndex z : ℝ) := by
  simpa [Metric.mem_closedBall, dist_zero_right, finiteChartDiskIndex] using
    Nat.le_ceil ‖z‖

/--
%%handwave
name:
  Global Beltrami equation from the integer-disk exhaustion
statement:
  Let $\mu:\mathbb C\to\mathbb C$ and let $Df$ be a measurable differential
  field. If
  $$
    \partial_{\bar z}f=\mu\,\partial_zf
  $$
  almost everywhere on every closed disk $\overline B(0,m)$ with integer
  radius $m$, then the same equation holds almost everywhere on
  $\mathbb C$.
proof:
  Intersect the countably many full-measure sets on which the diskwise
  equations hold. Every point belongs to the disk of radius
  $\lceil |z|\rceil$, so the equation holds on the intersection everywhere.
-/
theorem weakBeltramiEquationOn_univ_of_closedBall_exhaustion
    {μ : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (h : ∀ m : ℕ, WeakBeltramiEquationOn
      (Metric.closedBall (0 : ℂ) (m : ℝ)) μ df) :
    WeakBeltramiEquationOn Set.univ μ df := by
  unfold WeakBeltramiEquationOn at h ⊢
  rw [Measure.restrict_univ]
  have hm : ∀ m : ℕ, ∀ᵐ z ∂volume,
      z ∈ Metric.closedBall (0 : ℂ) (m : ℝ) →
        weakDBarField df z = μ z * weakDZField df z := by
    intro m
    exact (ae_restrict_iff' measurableSet_closedBall).1 (h m)
  have hall : ∀ᵐ z ∂volume, ∀ m : ℕ,
      z ∈ Metric.closedBall (0 : ℂ) (m : ℝ) →
        weakDBarField df z = μ z * weakDZField df z := by
    exact ae_all_iff.2 hm
  filter_upwards [hall] with z hz
  exact hz (finiteChartDiskIndex z) (mem_closedBall_finiteChartDiskIndex z)

/--
%%handwave
name:
  Gluing fields along the integer-disk exhaustion
statement:
  Given classes $u_m\in L^2(\overline B(0,m))$, define the global field by
  $$
    u(z)=u_{\lceil|z|\rceil}(z).
  $$
  Restriction compatibility later ensures that this represents every local
  class.
-/
def glueFiniteChartDiskLimits
    (u : ∀ m : ℕ, Lp ℂ 2 (finiteChartDiskMeasure m)) : ℂ → ℂ :=
  fun z ↦ u (finiteChartDiskIndex z) z

/--
%%handwave
name:
  The glued disk-exhaustion field represents every local class
statement:
  Let $u_m\in L^2(\overline B(0,m);\mathbb C)$ be compatible under
  restriction whenever $m\leq M$. Define
  $$
    u(z)=u_{\lceil|z|\rceil}(z).
  $$
  Then, for every $m$, the restriction of $u$ to
  $\overline B(0,m)$ equals $u_m$ almost everywhere.
proof:
  On the $k$th radial shell inside the $m$-disk one has $k\leq m$.
  Restriction compatibility identifies the representatives of $u_k$ and
  $u_m$ almost everywhere on the $k$-disk. Intersect these countably many
  full-measure conditions and use
  $|z|\leq\lceil|z|\rceil\leq m$.
-/
theorem glueFiniteChartDiskLimits_ae_eq
    (u : ∀ m : ℕ, Lp ℂ 2 (finiteChartDiskMeasure m))
    (hcompat : ∀ m M : ℕ, ∀ hmM : m ≤ M,
      finiteChartDiskRestriction hmM (u M) = u m)
    (m : ℕ) :
    glueFiniteChartDiskLimits u =ᵐ[finiteChartDiskMeasure m]
      fun z ↦ u m z := by
  have hk : ∀ k : ℕ, ∀ hkm : k ≤ m,
      (fun z ↦ u k z) =ᵐ[finiteChartDiskMeasure k] fun z ↦ u m z := by
    intro k hkm
    exact L2.ae_eq_of_monoMeasure_eq
      (finiteChartDiskMeasure_mono hkm) (u m) (u k)
      (hcompat k m hkm) |>.symm
  have hk_volume : ∀ k : ℕ, ∀ hkm : k ≤ m,
      ∀ᵐ z ∂volume, z ∈ Metric.closedBall (0 : ℂ) (k : ℝ) →
        u k z = u m z := by
    intro k hkm
    exact (ae_restrict_iff' measurableSet_closedBall).1 (hk k hkm)
  have hall : ∀ᵐ z ∂finiteChartDiskMeasure m, ∀ k : ℕ, k ≤ m →
      z ∈ Metric.closedBall (0 : ℂ) (k : ℝ) → u k z = u m z := by
    apply ae_all_iff.2
    intro k
    by_cases hkm : k ≤ m
    · have hres : ∀ᵐ z ∂finiteChartDiskMeasure m,
          z ∈ Metric.closedBall (0 : ℂ) (k : ℝ) → u k z = u m z :=
        ae_mono Measure.restrict_le_self (hk_volume k hkm)
      filter_upwards [hres] with z hz
      exact fun _hkm hzk ↦ hz hzk
    · exact Filter.Eventually.of_forall fun _z hk' ↦ (hkm hk').elim
  filter_upwards [hall, ae_restrict_mem measurableSet_closedBall] with z hz hzm
  have hindex_le : finiteChartDiskIndex z ≤ m := by
    apply Nat.ceil_le.mpr
    simpa [finiteChartDiskIndex, Metric.mem_closedBall, dist_zero_right] using hzm
  exact hz (finiteChartDiskIndex z) hindex_le
    (mem_closedBall_finiteChartDiskIndex z)

/--
%%handwave
name:
  Simultaneous weak extraction of prescribed differentials on the planar disk exhaustion
statement:
  Let $F_n$ be normalized $K$-quasiconformal self-homeomorphisms of the
  Riemann sphere and choose finite-chart weak differentials $DF_n$. There are
  a single strictly increasing $\varphi:\mathbb N\to\mathbb N$ and, for
  every $m\in\mathbb N$, fields
  $A_m,B_m\in L^2(\overline B(0,m);\mathbb C)$ such that
  $$
    DF_{\varphi(n)}(1)\rightharpoonup A_m,
    \qquad
    DF_{\varphi(n)}(i)\rightharpoonup B_m
  $$
  weakly on $\overline B(0,m)$ for every $m$. Whenever $m\leq M$, the
  restrictions of $A_M$ and $B_M$ to $\overline B(0,m)$ are respectively
  $A_m$ and $B_m$.
proof:
  Every subsequence has, on each fixed disk, a further subsequence for which
  both coordinate fields converge weakly. Apply countable diagonal extraction
  to the products of the two weak $L^2$ spaces. Continuity of restriction and
  uniqueness of weak limits give compatibility on nested disks.
-/
theorem normalizedKQuasiconformalRiemannSphere_diskExhaustion_weakDifferential_subsequence_of_isLocalW12On
    (K : ℝ) (F : ℕ → RiemannSphere ≃ₜ RiemannSphere)
    (hqc : ∀ n, IsKQuasiconformalRiemannSphere K (F n))
    (hnorm : ∀ n, IsNormalizedRiemannSphereHomeomorph (F n))
    (df : ℕ → ℂ → ℂ →L[ℝ] ℂ)
    (hdf : ∀ n, IsLocalW12On Set.univ
      (riemannSphereFiniteChartHomeomorph (F n) (hnorm n).2.2) (df n)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∃ dxLim : ∀ m : ℕ, Lp ℂ 2
            (volume.restrict (Metric.closedBall (0 : ℂ) (m : ℝ))),
          ∃ dyLim : ∀ m : ℕ, Lp ℂ 2
              (volume.restrict (Metric.closedBall (0 : ℂ) (m : ℝ))),
            (∀ m : ℕ,
                Tendsto
                  (fun n ↦ toWeakSpace ℝ
                    (Lp ℂ 2
                      (volume.restrict
                        (Metric.closedBall (0 : ℂ) (m : ℝ))))
                    (((ContinuousLinearMap.apply ℝ ℂ) 1 |>.comp_memLp'
                      (((hdf (φ n)).2.2
                        (Metric.closedBall (0 : ℂ) (m : ℝ))
                        (isCompact_closedBall (0 : ℂ) (m : ℝ))
                        (Set.subset_univ _)).2)).toLp
                          (fun z ↦ df (φ n) z 1)))
                  atTop
                    (nhds (toWeakSpace ℝ
                      (Lp ℂ 2
                        (volume.restrict
                          (Metric.closedBall (0 : ℂ) (m : ℝ)))) (dxLim m))) ∧
                Tendsto
                  (fun n ↦ toWeakSpace ℝ
                    (Lp ℂ 2
                      (volume.restrict
                        (Metric.closedBall (0 : ℂ) (m : ℝ))))
                    (((ContinuousLinearMap.apply ℝ ℂ) Complex.I |>.comp_memLp'
                      (((hdf (φ n)).2.2
                        (Metric.closedBall (0 : ℂ) (m : ℝ))
                        (isCompact_closedBall (0 : ℂ) (m : ℝ))
                        (Set.subset_univ _)).2)).toLp
                          (fun z ↦ df (φ n) z Complex.I)))
                  atTop
                    (nhds (toWeakSpace ℝ
                      (Lp ℂ 2
                        (volume.restrict
                          (Metric.closedBall (0 : ℂ) (m : ℝ)))) (dyLim m)))) ∧
              ∀ m M : ℕ, ∀ hmM : m ≤ M,
                finiteChartDiskRestriction hmM (dxLim M) = dxLim m ∧
                finiteChartDiskRestriction hmM (dyLim M) = dyLim m := by
  let μ : ℕ → Measure ℂ := fun m ↦
    volume.restrict (Metric.closedBall (0 : ℂ) (m : ℝ))
  let Y : ℕ → Type := fun m ↦
    WeakSpace ℝ (Lp ℂ 2 (μ m)) × WeakSpace ℝ (Lp ℂ 2 (μ m))
  have hmem (n m : ℕ) : MemLp (df n) 2 (μ m) := by
    exact (hdf n).2.2 (Metric.closedBall (0 : ℂ) (m : ℝ))
      (isCompact_closedBall (0 : ℂ) (m : ℝ)) (Set.subset_univ _) |>.2
  let x : ∀ m, ℕ → Y m := fun m n ↦
    (toWeakSpace ℝ (Lp ℂ 2 (μ m))
        (((ContinuousLinearMap.apply ℝ ℂ) 1 |>.comp_memLp'
          (hmem n m)).toLp (fun z ↦ df n z 1)),
      toWeakSpace ℝ (Lp ℂ 2 (μ m))
        (((ContinuousLinearMap.apply ℝ ℂ) Complex.I |>.comp_memLp'
          (hmem n m)).toLp (fun z ↦ df n z Complex.I)))
  have hextract :
      ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ m : ℕ,
        ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
          ∃ y : Y m,
            Tendsto (fun n ↦ x m (φ (ψ n))) atTop (nhds y) := by
    intro φ hφ m
    obtain ⟨dx, dy, ψ, hψ, hx, hy⟩ :=
      normalizedKQuasiconformalRiemannSphere_fixedDisk_weakDifferential_subsequence_of_isLocalW12On
        K (m : ℝ) (fun n ↦ F (φ n)) (fun n ↦ hqc (φ n))
          (fun n ↦ hnorm (φ n)) (fun n ↦ df (φ n)) (fun n ↦ hdf (φ n))
    refine ⟨ψ, hψ,
      (toWeakSpace ℝ (Lp ℂ 2 (μ m)) dx,
        toWeakSpace ℝ (Lp ℂ 2 (μ m)) dy), ?_⟩
    simpa only [x, Y, μ, hmem, Function.comp_apply] using hx.prodMk_nhds hy
  obtain ⟨φ, hφ, y, hy⟩ :=
    exists_strictMono_subsequence_tendsto_countably x hextract
  let dxLim : ∀ m, Lp ℂ 2 (μ m) := fun m ↦
    (toWeakSpace ℝ (Lp ℂ 2 (μ m))).symm (y m).1
  let dyLim : ∀ m, Lp ℂ 2 (μ m) := fun m ↦
    (toWeakSpace ℝ (Lp ℂ 2 (μ m))).symm (y m).2
  have hconv : ∀ m : ℕ,
      Tendsto
        (fun n ↦ toWeakSpace ℝ
          (Lp ℂ 2
            (volume.restrict (Metric.closedBall (0 : ℂ) (m : ℝ))))
          (((ContinuousLinearMap.apply ℝ ℂ) 1 |>.comp_memLp'
            (((hdf (φ n)).2.2 (Metric.closedBall (0 : ℂ) (m : ℝ))
              (isCompact_closedBall (0 : ℂ) (m : ℝ))
              (Set.subset_univ _)).2)).toLp (fun z ↦ df (φ n) z 1)))
        atTop
          (nhds (toWeakSpace ℝ
            (Lp ℂ 2
              (volume.restrict (Metric.closedBall (0 : ℂ) (m : ℝ))))
            (dxLim m))) ∧
      Tendsto
        (fun n ↦ toWeakSpace ℝ
          (Lp ℂ 2
            (volume.restrict (Metric.closedBall (0 : ℂ) (m : ℝ))))
          (((ContinuousLinearMap.apply ℝ ℂ) Complex.I |>.comp_memLp'
            (((hdf (φ n)).2.2 (Metric.closedBall (0 : ℂ) (m : ℝ))
              (isCompact_closedBall (0 : ℂ) (m : ℝ))
              (Set.subset_univ _)).2)).toLp
                (fun z ↦ df (φ n) z Complex.I)))
        atTop
          (nhds (toWeakSpace ℝ
            (Lp ℂ 2
              (volume.restrict (Metric.closedBall (0 : ℂ) (m : ℝ))))
            (dyLim m))) := by
    intro m
    have hx := (continuous_fst.tendsto (y m)).comp (hy m)
    have hy' := (continuous_snd.tendsto (y m)).comp (hy m)
    constructor
    · simpa only [x, Y, μ, hmem, dxLim, LinearEquiv.apply_symm_apply] using hx
    · simpa only [x, Y, μ, hmem, dyLim, LinearEquiv.apply_symm_apply] using hy'
  refine ⟨φ, hφ, dxLim, dyLim, hconv, ?_⟩
  intro m M hmM
  have hmem_x (n r : ℕ) : MemLp (fun z ↦ df (φ n) z 1) 2
      (finiteChartDiskMeasure r) := by
    simpa only [Function.comp_def] using
      ((ContinuousLinearMap.apply ℝ ℂ) 1).comp_memLp' (hmem (φ n) r)
  have hmem_y (n r : ℕ) : MemLp (fun z ↦ df (φ n) z Complex.I) 2
      (finiteChartDiskMeasure r) := by
    simpa only [Function.comp_def] using
      ((ContinuousLinearMap.apply ℝ ℂ) Complex.I).comp_memLp' (hmem (φ n) r)
  constructor
  · change L2.monoMeasure (finiteChartDiskMeasure_mono hmM) (dxLim M) = dxLim m
    apply L2.eq_of_weak_tendsto_monoMeasure
      (finiteChartDiskMeasure_mono hmM)
      (fun n z ↦ df (φ n) z 1) (fun n ↦ hmem_x n M)
      (fun n ↦ hmem_x n m) (dxLim M) (dxLim m)
    · simpa only [finiteChartDiskMeasure, hmem_x] using (hconv M).1
    · simpa only [finiteChartDiskMeasure, hmem_x] using (hconv m).1
  · change L2.monoMeasure (finiteChartDiskMeasure_mono hmM) (dyLim M) = dyLim m
    apply L2.eq_of_weak_tendsto_monoMeasure
      (finiteChartDiskMeasure_mono hmM)
      (fun n z ↦ df (φ n) z Complex.I) (fun n ↦ hmem_y n M)
      (fun n ↦ hmem_y n m) (dyLim M) (dyLim m)
    · simpa only [finiteChartDiskMeasure, hmem_y] using (hconv M).2
    · simpa only [finiteChartDiskMeasure, hmem_y] using (hconv m).2

/--
%%handwave
name:
  Simultaneous weak differential extraction on the planar disk exhaustion
statement:
  Let $F_n$ be normalized $K$-quasiconformal self-homeomorphisms of the
  Riemann sphere. There are finite-chart weak differentials $DF_n$, a single
  strictly increasing $\varphi:\mathbb N\to\mathbb N$, and, for every
  $m\in\mathbb N$, fields
  $A_m,B_m\in L^2(\overline B(0,m);\mathbb C)$ such that
  $$
    DF_{\varphi(n)}(1)\rightharpoonup A_m,
    \qquad
    DF_{\varphi(n)}(i)\rightharpoonup B_m
  $$
  weakly on $\overline B(0,m)$ for every $m$. Whenever $m\leq M$, the
  restrictions of $A_M$ and $B_M$ to $\overline B(0,m)$ are respectively
  $A_m$ and $B_m$.
proof:
  Choose one whole-plane finite-chart weak differential for each map and
  apply the [simultaneous extraction theorem for prescribed differentials](lean:JJMath.Quasiconformal.normalizedKQuasiconformalRiemannSphere_diskExhaustion_weakDifferential_subsequence_of_isLocalW12On).
-/
theorem normalizedKQuasiconformalRiemannSphere_diskExhaustion_weakDifferential_subsequence
    (K : ℝ) (F : ℕ → RiemannSphere ≃ₜ RiemannSphere)
    (hqc : ∀ n, IsKQuasiconformalRiemannSphere K (F n))
    (hnorm : ∀ n, IsNormalizedRiemannSphereHomeomorph (F n)) :
    ∃ df : ℕ → ℂ → ℂ →L[ℝ] ℂ,
      ∃ hdf : ∀ n, IsLocalW12On Set.univ
        (riemannSphereFiniteChartHomeomorph (F n) (hnorm n).2.2) (df n),
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∃ dxLim : ∀ m : ℕ, Lp ℂ 2
            (volume.restrict (Metric.closedBall (0 : ℂ) (m : ℝ))),
          ∃ dyLim : ∀ m : ℕ, Lp ℂ 2
              (volume.restrict (Metric.closedBall (0 : ℂ) (m : ℝ))),
            (∀ m : ℕ,
                Tendsto
                  (fun n ↦ toWeakSpace ℝ
                    (Lp ℂ 2
                      (volume.restrict
                        (Metric.closedBall (0 : ℂ) (m : ℝ))))
                    (((ContinuousLinearMap.apply ℝ ℂ) 1 |>.comp_memLp'
                      (((hdf (φ n)).2.2
                        (Metric.closedBall (0 : ℂ) (m : ℝ))
                        (isCompact_closedBall (0 : ℂ) (m : ℝ))
                        (Set.subset_univ _)).2)).toLp
                          (fun z ↦ df (φ n) z 1)))
                  atTop
                    (nhds (toWeakSpace ℝ
                      (Lp ℂ 2
                        (volume.restrict
                          (Metric.closedBall (0 : ℂ) (m : ℝ)))) (dxLim m))) ∧
                Tendsto
                  (fun n ↦ toWeakSpace ℝ
                    (Lp ℂ 2
                      (volume.restrict
                        (Metric.closedBall (0 : ℂ) (m : ℝ))))
                    (((ContinuousLinearMap.apply ℝ ℂ) Complex.I |>.comp_memLp'
                      (((hdf (φ n)).2.2
                        (Metric.closedBall (0 : ℂ) (m : ℝ))
                        (isCompact_closedBall (0 : ℂ) (m : ℝ))
                        (Set.subset_univ _)).2)).toLp
                          (fun z ↦ df (φ n) z Complex.I)))
                  atTop
                    (nhds (toWeakSpace ℝ
                      (Lp ℂ 2
                        (volume.restrict
                          (Metric.closedBall (0 : ℂ) (m : ℝ)))) (dyLim m)))) ∧
              ∀ m M : ℕ, ∀ hmM : m ≤ M,
                finiteChartDiskRestriction hmM (dxLim M) = dxLim m ∧
                finiteChartDiskRestriction hmM (dyLim M) = dyLim m := by
  choose df hdf using fun n ↦
    (hqc n).exists_finiteChart_weakDifferential (hnorm n)
  obtain ⟨φ, hφ, dxLim, dyLim, hconv, hcompat⟩ :=
    normalizedKQuasiconformalRiemannSphere_diskExhaustion_weakDifferential_subsequence_of_isLocalW12On
      K F hqc hnorm df hdf
  exact ⟨df, hdf, φ, hφ, dxLim, dyLim, hconv, hcompat⟩

set_option maxHeartbeats 3000000 in
/--
%%handwave
name:
  Diskwise weak-differential compactness with prescribed finite-chart differentials
statement:
  Let $F_n:\widehat{\mathbb C}\to\widehat{\mathbb C}$ be normalized
  $K$-quasiconformal homeomorphisms and choose a local $W^{1,2}$ finite-chart
  weak differential $DF_n$ for every $n$. There are a strictly increasing
  $\psi:\mathbb N\to\mathbb N$, a normalized sphere homeomorphism $G$, a
  field $Dg$, and compatible fields $A_m,B_m\in L^2(\overline B(0,m))$ such
  that
  $$
    F_{\psi(n)}\to G,
    \qquad F_{\psi(n)}^{-1}\to G^{-1}
  $$
  uniformly on the sphere, and the finite-chart representative
  $g:\mathbb C\to\mathbb C$ of $G$ belongs to
  $W^{1,2}_{\mathrm{loc}}(\mathbb C,\mathbb C)$ with weak differential
  $Dg$. On every integer-radius disk,
  $$
    DF_{\psi(n)}(1)\rightharpoonup A_m,
    \qquad DF_{\psi(n)}(i)\rightharpoonup B_m,
  $$
  and $Dg(v)=\operatorname{Re}(v)A_m+\operatorname{Im}(v)B_m$ almost
  everywhere there.
proof:
  First use [simultaneous weak coordinate extraction of the prescribed fields on every integer-radius disk](lean:JJMath.Quasiconformal.normalizedKQuasiconformalRiemannSphere_diskExhaustion_weakDifferential_subsequence_of_isLocalW12On), then pass to the [topologically convergent subsequence](lean:JJMath.Quasiconformal.normalizedKQuasiconformalRiemannSphere_topological_compactness). Spherical uniform convergence gives [strong local $L^2$ convergence of the finite-chart values](lean:JJMath.Quasiconformal.finiteChart_toLp_tendsto_of_tendstoUniformly), while the two differential coordinates still converge weakly. The [weak-derivative closure theorem](lean:JJMath.Quasiconformal.isWeakDerivativeOnEuclideanRegionWithValues_of_weak_tendsto_coordinates) identifies the diskwise weak differential of the limit. Restriction compatibility glues the coordinate limits to one whole-plane field, and the disk identities glue to the global weak derivative identity. The coordinate norm estimate gives local square-integrability of the reconstructed differential.
-/
theorem normalizedKQuasiconformalRiemannSphere_localW12_compactness_with_diskwise_weakDifferential_of_isLocalW12On
    (K : ℝ) (F : ℕ → RiemannSphere ≃ₜ RiemannSphere)
    (hqc : ∀ n, IsKQuasiconformalRiemannSphere K (F n))
    (hnorm : ∀ n, IsNormalizedRiemannSphereHomeomorph (F n))
    (df : ℕ → ℂ → ℂ →L[ℝ] ℂ)
    (hdf : ∀ n, IsLocalW12On Set.univ
      (riemannSphereFiniteChartHomeomorph (F n) (hnorm n).2.2) (df n)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∃ G : RiemannSphere ≃ₜ RiemannSphere,
        ∃ hGnorm : IsNormalizedRiemannSphereHomeomorph G,
          ∃ dG : ℂ → ℂ →L[ℝ] ℂ,
          ∃ dxLim : ∀ m : ℕ, Lp ℂ 2 (finiteChartDiskMeasure m),
          ∃ dyLim : ∀ m : ℕ, Lp ℂ 2 (finiteChartDiskMeasure m),
          TendstoUniformly (fun n ↦ F (ψ n)) G atTop ∧
          TendstoUniformly (fun n ↦ (F (ψ n)).symm) G.symm atTop ∧
          IsLocalW12On Set.univ
            (riemannSphereFiniteChartHomeomorph G hGnorm.2.2) dG ∧
          ∀ m : ℕ,
            Tendsto
              (fun n ↦ toWeakSpace ℝ (Lp ℂ 2 (finiteChartDiskMeasure m))
                (((ContinuousLinearMap.apply ℝ ℂ) 1 |>.comp_memLp'
                  (((hdf (ψ n)).2.2
                    (Metric.closedBall (0 : ℂ) (m : ℝ))
                    (isCompact_closedBall (0 : ℂ) (m : ℝ))
                    (Set.subset_univ _)).2)).toLp
                      (fun z ↦ df (ψ n) z 1)))
              atTop
                (nhds (toWeakSpace ℝ
                  (Lp ℂ 2 (finiteChartDiskMeasure m)) (dxLim m))) ∧
            Tendsto
              (fun n ↦ toWeakSpace ℝ (Lp ℂ 2 (finiteChartDiskMeasure m))
                (((ContinuousLinearMap.apply ℝ ℂ) Complex.I |>.comp_memLp'
                  (((hdf (ψ n)).2.2
                    (Metric.closedBall (0 : ℂ) (m : ℝ))
                    (isCompact_closedBall (0 : ℂ) (m : ℝ))
                    (Set.subset_univ _)).2)).toLp
                      (fun z ↦ df (ψ n) z Complex.I)))
              atTop
                (nhds (toWeakSpace ℝ
                  (Lp ℂ 2 (finiteChartDiskMeasure m)) (dyLim m))) ∧
            dG =ᵐ[finiteChartDiskMeasure m] fun z ↦
              realLinearMapOfCoordinateValues (dxLim m z) (dyLim m z) := by
  obtain ⟨φ, hφ, dxLim, dyLim, hconvD, hcompat⟩ :=
    normalizedKQuasiconformalRiemannSphere_diskExhaustion_weakDifferential_subsequence_of_isLocalW12On
      K F hqc hnorm df hdf
  let Fφ : ℕ → RiemannSphere ≃ₜ RiemannSphere := fun n ↦ F (φ n)
  obtain ⟨θ, hθ, G, hGnorm, hGconv, hGinvconv⟩ :=
    normalizedKQuasiconformalRiemannSphere_topological_compactness
      Fφ (fun n ↦ hqc (φ n)) (fun n ↦ hnorm (φ n))
  let ψ : ℕ → ℕ := φ ∘ θ
  let dx : ℂ → ℂ := glueFiniteChartDiskLimits dxLim
  let dy : ℂ → ℂ := glueFiniteChartDiskLimits dyLim
  let dG : ℂ → ℂ →L[ℝ] ℂ := fun z ↦
    realLinearMapOfCoordinateValues (dx z) (dy z)
  have hcompat_x : ∀ m M : ℕ, ∀ hmM : m ≤ M,
      finiteChartDiskRestriction hmM (dxLim M) = dxLim m :=
    fun m M hmM ↦ (hcompat m M hmM).1
  have hcompat_y : ∀ m M : ℕ, ∀ hmM : m ≤ M,
      finiteChartDiskRestriction hmM (dyLim M) = dyLim m :=
    fun m M hmM ↦ (hcompat m M hmM).2
  have hderiv_disk : ∀ m : ℕ,
      dG =ᵐ[finiteChartDiskMeasure m] fun z ↦
        realLinearMapOfCoordinateValues (dxLim m z) (dyLim m z) := by
    intro m
    filter_upwards [glueFiniteChartDiskLimits_ae_eq dxLim hcompat_x m,
      glueFiniteChartDiskLimits_ae_eq dyLim hcompat_y m] with z hxz hyz
    change realLinearMapOfCoordinateValues
      (glueFiniteChartDiskLimits dxLim z)
      (glueFiniteChartDiskLimits dyLim z) = _
    rw [hxz, hyz]
    rfl
  have hweak_disk : ∀ m : ℕ,
      JJMath.Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues
        (Metric.closedBall (0 : ℂ) (m : ℝ))
        (riemannSphereFiniteChartHomeomorph G hGnorm.2.2) dG := by
    intro m
    let Ωm : Set ℂ := Metric.closedBall (0 : ℂ) (m : ℝ)
    let μm : Measure ℂ := volume.restrict Ωm
    let u : ℕ → ℂ → ℂ := fun n ↦
      riemannSphereFiniteChartHomeomorph (F (ψ n)) (hnorm (ψ n)).2.2
    let du : ℕ → ℂ → ℂ →L[ℝ] ℂ := fun n ↦ df (ψ n)
    let hmem_u : ∀ n, MemLp (u n) 2 μm := fun n ↦
      finiteChart_memLp_on_closedBall (F (ψ n)) (hnorm (ψ n)) (m : ℝ)
    let hmem_x : ∀ n, MemLp (fun z ↦ du n z 1) 2 μm := fun n ↦ by
      simpa only [du, μm, Ωm, Function.comp_def] using
        ((ContinuousLinearMap.apply ℝ ℂ) 1).comp_memLp'
          (((hdf (ψ n)).2.2 Ωm (isCompact_closedBall (0 : ℂ) (m : ℝ))
            (Set.subset_univ _)).2)
    let hmem_y : ∀ n, MemLp (fun z ↦ du n z Complex.I) 2 μm := fun n ↦ by
      simpa only [du, μm, Ωm, Function.comp_def] using
        ((ContinuousLinearMap.apply ℝ ℂ) Complex.I).comp_memLp'
          (((hdf (ψ n)).2.2 Ωm (isCompact_closedBall (0 : ℂ) (m : ℝ))
            (Set.subset_univ _)).2)
    let uLim : Lp ℂ 2 μm :=
      (finiteChart_memLp_on_closedBall G hGnorm (m : ℝ)).toLp
        (riemannSphereFiniteChartHomeomorph G hGnorm.2.2)
    have hweak_seq : ∀ n,
        JJMath.Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues
          Ωm (u n) (du n) := by
      intro n
      exact (hdf (ψ n)).2.1.mono_set (Set.subset_univ _)
    have hu_strong : Tendsto
        (fun n ↦ (hmem_u n).toLp (u n)) atTop (nhds uLim) := by
      simpa only [u, hmem_u, uLim, μm, Ωm, ψ, Fφ,
        Function.comp_apply] using
        finiteChart_toLp_tendsto_of_tendstoUniformly
          K (m : ℝ) (fun n ↦ F (ψ n))
          (fun n ↦ hqc (ψ n)) (fun n ↦ hnorm (ψ n))
          G hGnorm (by simpa [ψ, Fφ, Function.comp_def] using hGconv)
    have hu : Tendsto
        (fun n ↦ toWeakSpace ℝ (Lp ℂ 2 μm) ((hmem_u n).toLp (u n)))
        atTop (nhds (toWeakSpace ℝ (Lp ℂ 2 μm) uLim)) := by
      simpa only [toWeakSpaceCLM_eq_toWeakSpace] using
        ((toWeakSpaceCLM ℝ (Lp ℂ 2 μm)).continuous.tendsto
          (toWeakSpace ℝ (Lp ℂ 2 μm) uLim)).comp hu_strong
    have hx : Tendsto
        (fun n ↦ toWeakSpace ℝ (Lp ℂ 2 μm)
          ((hmem_x n).toLp (fun z ↦ du n z 1))) atTop
        (nhds (toWeakSpace ℝ (Lp ℂ 2 μm) (dxLim m))) := by
      simpa only [ψ, du, hmem_x, μm, Ωm, Function.comp_apply] using
        (hconvD m).1.comp hθ.tendsto_atTop
    have hy : Tendsto
        (fun n ↦ toWeakSpace ℝ (Lp ℂ 2 μm)
          ((hmem_y n).toLp (fun z ↦ du n z Complex.I))) atTop
        (nhds (toWeakSpace ℝ (Lp ℂ 2 μm) (dyLim m))) := by
      simpa only [ψ, du, hmem_y, μm, Ωm, Function.comp_apply] using
        (hconvD m).2.comp hθ.tendsto_atTop
    have hclosed :=
      isWeakDerivativeOnEuclideanRegionWithValues_of_weak_tendsto_coordinates
        u du hweak_seq hmem_u hmem_x hmem_y uLim (dxLim m) (dyLim m)
          hu hx hy
    have hvalue_ae :
        riemannSphereFiniteChartHomeomorph G hGnorm.2.2 =ᵐ[μm]
          fun z ↦ uLim z := by
      exact (MemLp.coeFn_toLp
        (finiteChart_memLp_on_closedBall G hGnorm (m : ℝ))).symm
    exact (hclosed.congr_ae hvalue_ae).congr_derivative_ae (hderiv_disk m)
  have hlocal : IsLocalW12On Set.univ
      (riemannSphereFiniteChartHomeomorph G hGnorm.2.2) dG := by
    refine ⟨isOpen_univ,
      isWeakDerivativeOn_univ_of_closedBall_exhaustion hweak_disk, ?_⟩
    intro C hC _hCuniv
    obtain ⟨R, hCR⟩ := hC.isBounded.subset_closedBall (0 : ℂ)
    obtain ⟨m : ℕ, hm⟩ := exists_nat_gt R
    have hCm : C ⊆ Metric.closedBall (0 : ℂ) (m : ℝ) :=
      hCR.trans (Metric.closedBall_subset_closedBall hm.le)
    have hμ : volume.restrict C ≤ finiteChartDiskMeasure m :=
      Measure.restrict_mono hCm le_rfl
    have hdx_eq : dx =ᵐ[volume.restrict C] fun z ↦ dxLim m z :=
      ae_mono hμ (glueFiniteChartDiskLimits_ae_eq dxLim hcompat_x m)
    have hdy_eq : dy =ᵐ[volume.restrict C] fun z ↦ dyLim m z :=
      ae_mono hμ (glueFiniteChartDiskLimits_ae_eq dyLim hcompat_y m)
    have hdx_mem : MemLp dx 2 (volume.restrict C) :=
      ((Lp.memLp (dxLim m)).mono_measure hμ).ae_eq hdx_eq.symm
    have hdy_mem : MemLp dy 2 (volume.restrict C) :=
      ((Lp.memLp (dyLim m)).mono_measure hμ).ae_eq hdy_eq.symm
    refine ⟨memLp_restrict_of_isCompact_of_continuousOn hC
      (riemannSphereFiniteChartHomeomorph G hGnorm.2.2).continuous.continuousOn,
      ?_⟩
    exact realLinearMapOfCoordinateValues_memLp hdx_mem hdy_mem
  refine ⟨ψ, hφ.comp hθ, G, hGnorm, dG, dxLim, dyLim, ?_, ?_, hlocal, ?_⟩
  · simpa [ψ, Fφ, Function.comp_def] using hGconv
  · simpa [ψ, Fφ, Function.comp_def] using hGinvconv
  · intro m
    refine ⟨?_, ?_, hderiv_disk m⟩
    · simpa only [ψ, finiteChartDiskMeasure, Function.comp_apply] using
        (hconvD m).1.comp hθ.tendsto_atTop
    · simpa only [ψ, finiteChartDiskMeasure, Function.comp_apply] using
        (hconvD m).2.comp hθ.tendsto_atTop

/--
%%handwave
name:
  Local Sobolev compactness with prescribed finite-chart differentials
statement:
  Let $F_n:\widehat{\mathbb C}\to\widehat{\mathbb C}$ be normalized
  $K$-quasiconformal homeomorphisms and choose a local $W^{1,2}$ finite-chart
  weak differential $DF_n$ for every $n$. There are a strictly increasing
  $\psi:\mathbb N\to\mathbb N$, a normalized sphere homeomorphism $G$, and a
  field $Dg$ such that
  $$
    F_{\psi(n)}\to G,
    \qquad F_{\psi(n)}^{-1}\to G^{-1}
  $$
  uniformly on the sphere, and the finite-chart representative
  $g:\mathbb C\to\mathbb C$ of $G$ belongs to
  $W^{1,2}_{\mathrm{loc}}(\mathbb C,\mathbb C)$ with weak differential
  $Dg$.
proof:
  Apply the [diskwise weak-differential compactness theorem](lean:JJMath.Quasiconformal.normalizedKQuasiconformalRiemannSphere_localW12_compactness_with_diskwise_weakDifferential_of_isLocalW12On) and retain its topological and local Sobolev conclusions.
-/
theorem normalizedKQuasiconformalRiemannSphere_localW12_compactness_of_isLocalW12On
    (K : ℝ) (F : ℕ → RiemannSphere ≃ₜ RiemannSphere)
    (hqc : ∀ n, IsKQuasiconformalRiemannSphere K (F n))
    (hnorm : ∀ n, IsNormalizedRiemannSphereHomeomorph (F n))
    (df : ℕ → ℂ → ℂ →L[ℝ] ℂ)
    (hdf : ∀ n, IsLocalW12On Set.univ
      (riemannSphereFiniteChartHomeomorph (F n) (hnorm n).2.2) (df n)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∃ G : RiemannSphere ≃ₜ RiemannSphere,
        ∃ hGnorm : IsNormalizedRiemannSphereHomeomorph G,
          ∃ dG : ℂ → ℂ →L[ℝ] ℂ,
          TendstoUniformly (fun n ↦ F (ψ n)) G atTop ∧
          TendstoUniformly (fun n ↦ (F (ψ n)).symm) G.symm atTop ∧
          IsLocalW12On Set.univ
            (riemannSphereFiniteChartHomeomorph G hGnorm.2.2) dG := by
  obtain ⟨ψ, hψ, G, hGnorm, dG, _dxLim, _dyLim,
      hGconv, hGinvconv, hlocal, _hweak⟩ :=
    normalizedKQuasiconformalRiemannSphere_localW12_compactness_with_diskwise_weakDifferential_of_isLocalW12On
      K F hqc hnorm df hdf
  exact ⟨ψ, hψ, G, hGnorm, dG, hGconv, hGinvconv, hlocal⟩

set_option maxHeartbeats 3000000 in
/--
%%handwave
name:
  Normalized compactness for almost-everywhere convergent Beltrami coefficients
statement:
  Let $F_n:\widehat{\mathbb C}\to\widehat{\mathbb C}$ be normalized
  $K$-quasiconformal homeomorphisms with finite-chart weak differentials
  $DF_n$ satisfying
  $$
    \partial_{\bar z}F_n=\mu_n\partial_zF_n
    \quad\text{almost everywhere on }\mathbb C.
  $$
  Suppose that $\mu_n$ and $\mu$ are measurable,
  $\mu_n(z)\to\mu(z)$ almost everywhere, and
  $|\mu_n(z)|,|\mu(z)|\leq C$ almost everywhere. Then some strictly
  increasing subsequence, together with its inverses, converges uniformly on
  the sphere to a normalized homeomorphism $G$. Its finite-chart
  representative belongs to $W^{1,2}_{\mathrm{loc}}$ and has a weak
  differential $Dg$ satisfying
  $$
    \partial_{\bar z}g=\mu\partial_zg
    \quad\text{almost everywhere on }\mathbb C.
  $$
proof:
  Apply normalized compactness while retaining the weak limits of the two
  differential coordinates on every integer-radius disk. Uniform
  quasiconformality supplies a common finite disk-energy bound and hence
  common $L^2$ bounds for the reconstructed $z$ derivatives. The
  [varying-coefficient weak closure theorem](lean:JJMath.Quasiconformal.weakBeltramiEquationOn_of_ae_tendsto_of_weak_tendsto_coordinateValues) passes the equation to the limit on each disk. Exhausting the plane by these disks gives the global equation.
-/
theorem normalizedKQuasiconformalRiemannSphere_aeTendstoBeltrami_compactness_of_isLocalW12On
    (K C : ℝ) (F : ℕ → RiemannSphere ≃ₜ RiemannSphere)
    (hqc : ∀ n, IsKQuasiconformalRiemannSphere K (F n))
    (hnorm : ∀ n, IsNormalizedRiemannSphereHomeomorph (F n))
    (df : ℕ → ℂ → ℂ →L[ℝ] ℂ)
    (hdf : ∀ n, IsLocalW12On Set.univ
      (riemannSphereFiniteChartHomeomorph (F n) (hnorm n).2.2) (df n))
    (μn : ℕ → ℂ → ℂ)
    (hμnmeas : ∀ n, AEStronglyMeasurable (μn n) volume)
    (hμnbound : ∀ᵐ z ∂volume, ∀ n, ‖μn n z‖ ≤ C)
    (hbel : ∀ n, WeakBeltramiEquationOn Set.univ (μn n) (df n))
    (μ : ℂ → ℂ) (hμmeas : AEStronglyMeasurable μ volume)
    (hμbound : HasEssentialNormLEOn Set.univ μ C)
    (hμtendsto : ∀ᵐ z ∂volume,
      Tendsto (fun n ↦ μn n z) atTop (nhds (μ z))) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∃ G : RiemannSphere ≃ₜ RiemannSphere,
        ∃ hGnorm : IsNormalizedRiemannSphereHomeomorph G,
          ∃ dG : ℂ → ℂ →L[ℝ] ℂ,
          TendstoUniformly (fun n ↦ F (ψ n)) G atTop ∧
          TendstoUniformly (fun n ↦ (F (ψ n)).symm) G.symm atTop ∧
          IsLocalW12On Set.univ
            (riemannSphereFiniteChartHomeomorph G hGnorm.2.2) dG ∧
          WeakBeltramiEquationOn Set.univ μ dG := by
  obtain ⟨ψ, hψ, G, hGnorm, dG, dxLim, dyLim,
      hGconv, hGinvconv, hlocal, hweak⟩ :=
    normalizedKQuasiconformalRiemannSphere_localW12_compactness_with_diskwise_weakDifferential_of_isLocalW12On
      K F hqc hnorm df hdf
  have hμboundGlobal : ∀ᵐ z ∂volume, ‖μ z‖ ≤ C := by
    simpa [HasEssentialNormLEOn] using hμbound
  have hbelDisk : ∀ m : ℕ, WeakBeltramiEquationOn
      (Metric.closedBall (0 : ℂ) (m : ℝ)) μ dG := by
    intro m
    let Ωm : Set ℂ := Metric.closedBall (0 : ℂ) (m : ℝ)
    let μm : Measure ℂ := finiteChartDiskMeasure m
    let hmem_x : ∀ n, MemLp (fun z ↦ df (ψ n) z 1) 2 μm := fun n ↦ by
      simpa only [μm, finiteChartDiskMeasure, Function.comp_def] using
        ((ContinuousLinearMap.apply ℝ ℂ) 1).comp_memLp'
          (((hdf (ψ n)).2.2 Ωm
            (isCompact_closedBall (0 : ℂ) (m : ℝ))
            (Set.subset_univ _)).2)
    let hmem_y : ∀ n, MemLp (fun z ↦ df (ψ n) z Complex.I) 2 μm :=
      fun n ↦ by
        simpa only [μm, finiteChartDiskMeasure, Function.comp_def] using
          ((ContinuousLinearMap.apply ℝ ℂ) Complex.I).comp_memLp'
            (((hdf (ψ n)).2.2 Ωm
              (isCompact_closedBall (0 : ℂ) (m : ℝ))
              (Set.subset_univ _)).2)
    let a : ℕ → Lp ℂ 2 μm := fun n ↦
      (hmem_x n).toLp (fun z ↦ df (ψ n) z 1)
    let b : ℕ → Lp ℂ 2 μm := fun n ↦
      (hmem_y n).toLp (fun z ↦ df (ψ n) z Complex.I)
    have ha : Tendsto (fun n ↦ toWeakSpace ℝ _ (a n)) atTop
        (nhds (toWeakSpace ℝ _ (dxLim m))) := by
      simpa only [a, hmem_x, μm, Ωm, finiteChartDiskMeasure] using
        (hweak m).1
    have hb : Tendsto (fun n ↦ toWeakSpace ℝ _ (b n)) atTop
        (nhds (toWeakSpace ℝ _ (dyLim m))) := by
      simpa only [b, hmem_y, μm, Ωm, finiteChartDiskMeasure] using
        (hweak m).2.1
    have hrec (n : ℕ) :
        (fun z ↦ realLinearMapOfCoordinateValues (a n z) (b n z))
          =ᵐ[μm] df (ψ n) := by
      filter_upwards [MemLp.coeFn_toLp (hmem_x n),
        MemLp.coeFn_toLp (hmem_y n)] with z hxz hyz
      rw [hxz, hyz]
      exact realLinearMapOfCoordinateValues_apply_eq (df (ψ n) z)
    let ν : ℕ → ℂ → ℂ := fun n ↦ μn (ψ n)
    have hνmeas : ∀ n, AEStronglyMeasurable (ν n) μm := fun n ↦
      (hμnmeas (ψ n)).mono_measure Measure.restrict_le_self
    have hνtendsto : ∀ᵐ z ∂μm,
        Tendsto (fun n ↦ ν n z) atTop (nhds (μ z)) := by
      filter_upwards [ae_mono Measure.restrict_le_self hμtendsto] with z hz
      exact hz.comp hψ.tendsto_atTop
    have hνbound : ∀ᵐ z ∂μm, ∀ n, ‖ν n z‖ ≤ C := by
      filter_upwards [ae_mono Measure.restrict_le_self hμnbound] with z hz
      exact fun n ↦ hz (ψ n)
    have hμboundDisk : ∀ᵐ z ∂μm, ‖μ z‖ ≤ C :=
      ae_mono Measure.restrict_le_self hμboundGlobal
    have heq (n : ℕ) : WeakBeltramiEquationOn Ωm (ν n)
        (fun z ↦ realLinearMapOfCoordinateValues (a n z) (b n z)) := by
      exact ((hbel (ψ n)).mono (Set.subset_univ _)).congr_derivative_ae
        (hrec n).symm
    obtain ⟨E, hEtop, hEbound⟩ :=
      exists_uniform_finiteChart_weakDifferential_energy_bound_of_isLocalW12On
        K (m : ℝ)
    let B : ℝ := (max E 1).toReal
    have henergy (n : ℕ) :
        (∫⁻ z in Ωm, ENNReal.ofReal (‖df (ψ n) z‖ ^ 2) ∂volume) ≤ E :=
      hEbound (F (ψ n)) (hqc (ψ n)) (hnorm (ψ n)) (df (ψ n))
        (hdf (ψ n))
    have henergy_x (n : ℕ) :
        (∫⁻ z, ENNReal.ofReal (‖df (ψ n) z 1‖ ^ 2) ∂μm) ≤ E := by
      apply (lintegral_mono fun z ↦ ENNReal.ofReal_mono ?_).trans
        (henergy n)
      gcongr
      simpa using (df (ψ n) z).le_opNorm (1 : ℂ)
    have henergy_y (n : ℕ) :
        (∫⁻ z, ENNReal.ofReal (‖df (ψ n) z Complex.I‖ ^ 2) ∂μm) ≤ E := by
      apply (lintegral_mono fun z ↦ ENNReal.ofReal_mono ?_).trans
        (henergy n)
      gcongr
      simpa using (df (ψ n) z).le_opNorm Complex.I
    have haBound (n : ℕ) : ‖a n‖ ≤ B := by
      simpa only [a, B] using
        L2.complex_norm_toLp_le_max_energy_toReal (hmem_x n) hEtop
          (henergy_x n)
    have hbBound (n : ℕ) : ‖b n‖ ≤ B := by
      simpa only [b, B] using
        L2.complex_norm_toLp_le_max_energy_toReal (hmem_y n) hEtop
          (henergy_y n)
    have hdzBound (n : ℕ) :
        ‖l2WeakDZOfCoordinateValues (a n) (b n)‖ ≤ 2 * B := by
      exact (norm_l2WeakDZOfCoordinateValues_le (a n) (b n)).trans
        (by linarith [haBound n, hbBound n])
    have hclosed :=
      weakBeltramiEquationOn_of_ae_tendsto_of_weak_tendsto_coordinateValues
        ν μ C hνmeas
        (hμmeas.mono_measure Measure.restrict_le_self)
        hνtendsto hνbound hμboundDisk a b (dxLim m) (dyLim m)
        ha hb (2 * B) hdzBound heq
    exact hclosed.congr_derivative_ae (hweak m).2.2.symm
  refine ⟨ψ, hψ, G, hGnorm, dG, hGconv, hGinvconv, hlocal, ?_⟩
  exact weakBeltramiEquationOn_univ_of_closedBall_exhaustion hbelDisk

set_option maxHeartbeats 6000000 in
/--
%%handwave
name:
  Two-chart compactness for almost-everywhere convergent Beltrami coefficients
statement:
  Let $F_n:\widehat{\mathbb C}\to\widehat{\mathbb C}$ be normalized
  $K$-quasiconformal homeomorphisms whose finite-chart weak differentials
  satisfy
  $$
    \partial_{\bar z}F_n=\mu_n\partial_zF_n
  $$
  almost everywhere. Suppose that $\mu_n\to\mu$ almost everywhere and that
  all coefficients have one common essential bound. Then a subsequence,
  together with its inverses, converges uniformly on the sphere to a
  normalized homeomorphism $G$. Both the finite-chart representative $g$ and
  reciprocal-chart representative $g_\infty$ belong to
  $W^{1,2}_{\mathrm{loc}}(\mathbb C)$ and satisfy
  $$
    \partial_{\bar z}g=\mu\,\partial_zg,
    \qquad
    \partial_{\bar z}g_\infty=
      \left(\mu(z^{-1})
        \frac{\overline{-z^{-2}}}{-z^{-2}}\right)
      \partial_zg_\infty
  $$
  almost everywhere.
proof:
  First apply [normalized finite-chart compactness](lean:JJMath.Quasiconformal.normalizedKQuasiconformalRiemannSphere_aeTendstoBeltrami_compactness_of_isLocalW12On). Conjugate that subsequence by spherical inversion. The [reciprocal-coordinate chain rule](lean:JJMath.Quasiconformal.IsKQuasiconformalRiemannSphere.exists_invConjugate_finiteChart_weakDifferential_weakBeltrami) gives its transformed Beltrami equations; measurability, the common bound, and almost-everywhere convergence pass through inversion. Apply finite-chart compactness again. Uniform convergence identifies the second limit with the inversion conjugate of the first, so its finite chart is the reciprocal chart of $G$.
-/
theorem normalizedKQuasiconformalRiemannSphere_aeTendstoBeltrami_twoChart_compactness_of_isLocalW12On
    (K C : ℝ) (F : ℕ → RiemannSphere ≃ₜ RiemannSphere)
    (hqc : ∀ n, IsKQuasiconformalRiemannSphere K (F n))
    (hnorm : ∀ n, IsNormalizedRiemannSphereHomeomorph (F n))
    (df : ℕ → ℂ → ℂ →L[ℝ] ℂ)
    (hdf : ∀ n, IsLocalW12On Set.univ
      (riemannSphereFiniteChartHomeomorph (F n) (hnorm n).2.2) (df n))
    (μn : ℕ → ℂ → ℂ)
    (hμnmeas : ∀ n, AEStronglyMeasurable (μn n) volume)
    (hμnbound : ∀ᵐ z ∂volume, ∀ n, ‖μn n z‖ ≤ C)
    (hbel : ∀ n, WeakBeltramiEquationOn Set.univ (μn n) (df n))
    (μ : ℂ → ℂ) (hμmeas : AEStronglyMeasurable μ volume)
    (hμbound : HasEssentialNormLEOn Set.univ μ C)
    (hμtendsto : ∀ᵐ z ∂volume,
      Tendsto (fun n ↦ μn n z) atTop (nhds (μ z))) :
    ∃ ξ : ℕ → ℕ, StrictMono ξ ∧
      ∃ G : RiemannSphere ≃ₜ RiemannSphere,
        ∃ hGnorm : IsNormalizedRiemannSphereHomeomorph G,
          ∃ dG dGInf : ℂ → ℂ →L[ℝ] ℂ,
          TendstoUniformly (fun n ↦ F (ξ n)) G atTop ∧
          TendstoUniformly (fun n ↦ (F (ξ n)).symm) G.symm atTop ∧
          IsLocalW12On Set.univ
            (riemannSphereFiniteChartHomeomorph G hGnorm.2.2) dG ∧
          WeakBeltramiEquationOn Set.univ μ dG ∧
          IsLocalW12On Set.univ
            (riemannSphereInfinityChartHomeomorph G hGnorm.1) dGInf ∧
          WeakBeltramiEquationOn Set.univ
            (inversionPullbackBeltrami μ) dGInf := by
  classical
  obtain ⟨ψ, hψ, G, hGnorm, dG, hGconv, hGinvconv, hGlocal, hGbel⟩ :=
    normalizedKQuasiconformalRiemannSphere_aeTendstoBeltrami_compactness_of_isLocalW12On
      K C F hqc hnorm df hdf μn hμnmeas hμnbound hbel μ hμmeas
        hμbound hμtendsto
  let Fψ : ℕ → RiemannSphere ≃ₜ RiemannSphere := fun n ↦ F (ψ n)
  let H : ℕ → RiemannSphere ≃ₜ RiemannSphere := fun n ↦
    riemannSphereInvConjugate (Fψ n)
  let νn : ℕ → ℂ → ℂ := fun n ↦
    inversionPullbackBeltrami (μn (ψ n))
  let ν : ℂ → ℂ := inversionPullbackBeltrami μ
  have hex (n : ℕ) : ∃ dH : ℂ → ℂ →L[ℝ] ℂ,
      IsLocalW12On Set.univ
        (riemannSphereFiniteChartHomeomorph (H n)
          (hnorm (ψ n)).invConjugate.2.2) dH ∧
      WeakBeltramiEquationOn Set.univ (νn n) dH := by
    simpa only [H, Fψ, νn] using
      (hqc (ψ n)).exists_invConjugate_finiteChart_weakDifferential_weakBeltrami
        (hnorm (ψ n)) (hdf (ψ n)) (hbel (ψ n))
  let dH : ℕ → ℂ → ℂ →L[ℝ] ℂ := fun n ↦ Classical.choose (hex n)
  have hHdf (n : ℕ) : IsLocalW12On Set.univ
      (riemannSphereFiniteChartHomeomorph (H n)
        (hnorm (ψ n)).invConjugate.2.2) (dH n) :=
    (Classical.choose_spec (hex n)).1
  have hHbel (n : ℕ) : WeakBeltramiEquationOn Set.univ (νn n) (dH n) :=
    (Classical.choose_spec (hex n)).2
  have hνnmeas (n : ℕ) : AEStronglyMeasurable (νn n) volume := by
    exact AEStronglyMeasurable.inversionPullbackBeltrami (hμnmeas (ψ n))
  have hνnbound : ∀ᵐ z ∂volume, ∀ n, ‖νn n z‖ ≤ C := by
    rw [ae_all_iff]
    intro n
    apply ae_norm_inversionPullbackBeltrami_le
    filter_upwards [hμnbound] with z hz
    exact hz (ψ n)
  have hνmeas : AEStronglyMeasurable ν volume :=
    AEStronglyMeasurable.inversionPullbackBeltrami hμmeas
  have hνbound : HasEssentialNormLEOn Set.univ ν C :=
    hμbound.inversionPullbackBeltrami_univ
  have hνtendsto : ∀ᵐ z ∂volume,
      Tendsto (fun n ↦ νn n z) atTop (nhds (ν z)) := by
    apply ae_tendsto_inversionPullbackBeltrami
    filter_upwards [hμtendsto] with z hz
    exact hz.comp hψ.tendsto_atTop
  obtain ⟨θ, hθ, L, hLnorm, dL, hLconv, _hLinvconv, hLlocal, hLbel⟩ :=
    normalizedKQuasiconformalRiemannSphere_aeTendstoBeltrami_compactness_of_isLocalW12On
      K C H (fun n ↦ (hqc (ψ n)).invConjugate)
        (fun n ↦ (hnorm (ψ n)).invConjugate) dH hHdf νn hνnmeas
        hνnbound hHbel ν hνmeas hνbound hνtendsto
  have hJGconv : TendstoUniformly (fun n ↦ H (θ n))
      (riemannSphereInvConjugate G) atTop := by
    apply tendstoUniformly_invConjugate
    intro U hU
    exact hθ.tendsto_atTop (hGconv U hU)
  have hLeq : L = riemannSphereInvConjugate G := by
    apply Homeomorph.ext
    intro z
    exact tendsto_nhds_unique (hLconv.tendsto_at z) (hJGconv.tendsto_at z)
  subst L
  have hlocalInf : IsLocalW12On Set.univ
      (riemannSphereInfinityChartHomeomorph G hGnorm.1) dL := by
    apply hLlocal.congr_ae
    filter_upwards with z
    exact (riemannSphereFiniteChartHomeomorph_invConjugate_apply hGnorm z).symm
  let ξ : ℕ → ℕ := ψ ∘ θ
  refine ⟨ξ, hψ.comp hθ, G, hGnorm, dG, dL, ?_, ?_, hGlocal,
    hGbel, hlocalInf, hLbel⟩
  · intro U hU
    exact hθ.tendsto_atTop (hGconv U hU)
  · intro U hU
    exact hθ.tendsto_atTop (hGinvconv U hU)

set_option maxHeartbeats 6000000 in
/--
%%handwave
name:
  Finite-coordinate spherical compactness for convergent Beltrami coefficients
statement:
  Let $F_n:\widehat{\mathbb C}\to\widehat{\mathbb C}$ be normalized
  $K$-quasiconformal homeomorphisms whose finite-chart weak differentials
  satisfy
  $$
    \partial_{\bar z}F_n=\mu_n\partial_zF_n
  $$
  almost everywhere. Suppose that $\mu_n\to\mu$ almost everywhere and
  $|\mu_n|,|\mu|\leq k<1$, where $k\geq0$. Then a subsequence, together with
  its inverses, converges uniformly on the sphere to a normalized
  $((1+k)/(1-k))$-quasiconformal homeomorphism $G$. Its finite-chart
  representative belongs to $W^{1,2}_{\mathrm{loc}}(\mathbb C)$ and
  satisfies
  $$
    \partial_{\bar z}G=\mu\,\partial_zG
  $$
  almost everywhere.
  This is the affine-coordinate implementation form of spherical Beltrami
  compactness.
proof:
  Apply [two-chart Beltrami compactness](lean:JJMath.Quasiconformal.normalizedKQuasiconformalRiemannSphere_aeTendstoBeltrami_twoChart_compactness_of_isLocalW12On). The bounded Beltrami criterion and orientation preservation under uniform homeomorphic limits make the finite chart of $G$ quasiconformal. Apply the same criterion to the inversion-conjugate sequence and the reciprocal-chart equation to make the finite chart of $J\circ G\circ J$ quasiconformal. The [two-diagonal standard-chart criterion](lean:JJMath.Quasiconformal.isKQuasiconformalRiemannSphere_of_finiteChart_and_invConjugate_finiteChart) supplies all four standard chart pairs.
tags:
  milestone
-/
theorem normalizedKQuasiconformalRiemannSphere_aeTendstoBeltrami_spherical_compactness_of_isLocalW12On
    (K k : ℝ) (F : ℕ → RiemannSphere ≃ₜ RiemannSphere)
    (hqc : ∀ n, IsKQuasiconformalRiemannSphere K (F n))
    (hnorm : ∀ n, IsNormalizedRiemannSphereHomeomorph (F n))
    (df : ℕ → ℂ → ℂ →L[ℝ] ℂ)
    (hdf : ∀ n, IsLocalW12On Set.univ
      (riemannSphereFiniteChartHomeomorph (F n) (hnorm n).2.2) (df n))
    (μn : ℕ → ℂ → ℂ)
    (hμnmeas : ∀ n, AEStronglyMeasurable (μn n) volume)
    (hμnbound : ∀ᵐ z ∂volume, ∀ n, ‖μn n z‖ ≤ k)
    (hbel : ∀ n, WeakBeltramiEquationOn Set.univ (μn n) (df n))
    (μ : ℂ → ℂ) (hμmeas : AEStronglyMeasurable μ volume)
    (hμbound : HasEssentialNormLEOn Set.univ μ k)
    (hμtendsto : ∀ᵐ z ∂volume,
      Tendsto (fun n ↦ μn n z) atTop (nhds (μ z)))
    (hk0 : 0 ≤ k) (hk1 : k < 1) :
    ∃ ξ : ℕ → ℕ, StrictMono ξ ∧
      ∃ G : RiemannSphere ≃ₜ RiemannSphere,
        ∃ hGnorm : IsNormalizedRiemannSphereHomeomorph G,
          ∃ dG : ℂ → ℂ →L[ℝ] ℂ,
          TendstoUniformly (fun n ↦ F (ξ n)) G atTop ∧
          TendstoUniformly (fun n ↦ (F (ξ n)).symm) G.symm atTop ∧
          IsKQuasiconformalRiemannSphere ((1 + k) / (1 - k)) G ∧
          IsLocalW12On Set.univ
            (riemannSphereFiniteChartHomeomorph G hGnorm.2.2) dG ∧
          WeakBeltramiEquationOn Set.univ μ dG := by
  obtain ⟨ξ, hξ, G, hGnorm, dG, dGInf, hGconv, hGinvconv,
      hGlocal, hGbel, hGInfLocal, hGInfBel⟩ :=
    normalizedKQuasiconformalRiemannSphere_aeTendstoBeltrami_twoChart_compactness_of_isLocalW12On
      K k F hqc hnorm df hdf μn hμnmeas hμnbound hbel μ hμmeas
        hμbound hμtendsto
  let Fξ : ℕ → RiemannSphere ≃ₜ RiemannSphere := fun n ↦ F (ξ n)
  have hfinite : IsKQuasiconformalBetween ((1 + k) / (1 - k))
      (riemannSphereChartHomeomorph G .finite .finite) := by
    apply isKQuasiconformalBetween_finiteChart_of_tendstoUniformly_of_weakBeltrami
      K k Fξ (fun n ↦ hqc (ξ n)) (fun n ↦ hnorm (ξ n)) G hGnorm
      hGconv dG hGlocal μ hGbel hμbound hk0 hk1
  let H : ℕ → RiemannSphere ≃ₜ RiemannSphere := fun n ↦
    riemannSphereInvConjugate (Fξ n)
  have hHconv : TendstoUniformly (fun n ↦ H n)
      (riemannSphereInvConjugate G) atTop :=
    tendstoUniformly_invConjugate hGconv
  have hGInfAsInv : IsLocalW12On Set.univ
      (riemannSphereFiniteChartHomeomorph (riemannSphereInvConjugate G)
        hGnorm.invConjugate.2.2) dGInf := by
    apply hGInfLocal.congr_ae
    filter_upwards with z
    exact riemannSphereFiniteChartHomeomorph_invConjugate_apply hGnorm z
  have hνbound : HasEssentialNormLEOn Set.univ
      (inversionPullbackBeltrami μ) k :=
    hμbound.inversionPullbackBeltrami_univ
  have hinvfinite : IsKQuasiconformalBetween ((1 + k) / (1 - k))
      (riemannSphereChartHomeomorph (riemannSphereInvConjugate G)
        .finite .finite) := by
    apply isKQuasiconformalBetween_finiteChart_of_tendstoUniformly_of_weakBeltrami
      K k H (fun n ↦ (hqc (ξ n)).invConjugate)
      (fun n ↦ (hnorm (ξ n)).invConjugate)
      (riemannSphereInvConjugate G) hGnorm.invConjugate hHconv
      dGInf hGInfAsInv (inversionPullbackBeltrami μ) hGInfBel
      hνbound hk0 hk1
  have hGsphere : IsKQuasiconformalRiemannSphere
      ((1 + k) / (1 - k)) G :=
    isKQuasiconformalRiemannSphere_of_finiteChart_and_invConjugate_finiteChart
      hGnorm hfinite hinvfinite
  exact ⟨ξ, hξ, G, hGnorm, dG, hGconv, hGinvconv, hGsphere,
    hGlocal, hGbel⟩

set_option maxHeartbeats 3000000 in
/--
%%handwave
name:
  Local Sobolev compactness for normalized quasiconformal sphere maps
statement:
  Let $F_n:\widehat{\mathbb C}\to\widehat{\mathbb C}$ be normalized
  $K$-quasiconformal homeomorphisms. There are a strictly increasing
  $\psi:\mathbb N\to\mathbb N$, a normalized sphere homeomorphism $G$, and
  a field $Dg$ such that
  $$
    F_{\psi(n)}\to G,
    \qquad F_{\psi(n)}^{-1}\to G^{-1}
  $$
  uniformly on the sphere, and the finite-chart representative
  $g:\mathbb C\to\mathbb C$ of $G$ belongs to
  $W^{1,2}_{\mathrm{loc}}(\mathbb C,\mathbb C)$ with weak differential
  $Dg$.
proof:
  Choose one finite-chart weak differential for every map and apply the
  [local Sobolev compactness theorem for prescribed differentials](lean:JJMath.Quasiconformal.normalizedKQuasiconformalRiemannSphere_localW12_compactness_of_isLocalW12On).
-/
theorem normalizedKQuasiconformalRiemannSphere_localW12_compactness
    (K : ℝ) (F : ℕ → RiemannSphere ≃ₜ RiemannSphere)
    (hqc : ∀ n, IsKQuasiconformalRiemannSphere K (F n))
    (hnorm : ∀ n, IsNormalizedRiemannSphereHomeomorph (F n)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∃ G : RiemannSphere ≃ₜ RiemannSphere,
        ∃ hGnorm : IsNormalizedRiemannSphereHomeomorph G,
          ∃ dG : ℂ → ℂ →L[ℝ] ℂ,
          TendstoUniformly (fun n ↦ F (ψ n)) G atTop ∧
          TendstoUniformly (fun n ↦ (F (ψ n)).symm) G.symm atTop ∧
          IsLocalW12On Set.univ
            (riemannSphereFiniteChartHomeomorph G hGnorm.2.2) dG := by
  choose df hdf using fun n ↦
    (hqc n).exists_finiteChart_weakDifferential (hnorm n)
  exact
    normalizedKQuasiconformalRiemannSphere_localW12_compactness_of_isLocalW12On
      K F hqc hnorm df hdf

end

end Quasiconformal

end JJMath
