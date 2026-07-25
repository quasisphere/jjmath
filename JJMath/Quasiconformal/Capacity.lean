import JJMath.Quasiconformal.ChangeOfVariables
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Planar condenser capacity

This file begins the capacity route to normalized compactness of planar and
spherical quasiconformal maps. It defines continuous real-valued local
$W^{1,2}$ competitors for a two-plate planar condenser, their extended
Dirichlet energy, and the resulting variational capacity.
-/

namespace JJMath

open MeasureTheory Set
open scoped ENNReal Topology

namespace Quasiconformal

noncomputable section
/--
%%handwave
name:
  Real local planar Sobolev regularity
statement:
  A real-valued function $u$ belongs to $W^{1,2}_{\mathrm{loc}}(\Omega)$ with
  weak differential $Du$ if $\Omega$ is open, the distributional
  first-derivative identities hold on $\Omega$, and both $u$ and $Du$ are
  square-integrable on every compact subset of $\Omega$.
-/
def IsLocalW12RealOn (Ω : Set ℂ) (u : ℂ → ℝ)
    (du : ℂ → ℂ →L[ℝ] ℝ) : Prop :=
  IsOpen Ω ∧
    JJMath.Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues Ω u du ∧
    ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      MemLp u 2 (volume.restrict K) ∧ MemLp du 2 (volume.restrict K)

/--
%%handwave
name:
  Adding or subtracting a constant preserves local Sobolev regularity
statement:
  If $u\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb R)$ has weak differential
  $Du$, then for every $a\in\mathbb R$ the function $u-a$ has the same weak
  differential $Du$ and also belongs to
  $W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb R)$.
proof:
  The weak derivative of a constant is zero. On each compact subset of
  $\Omega$, constants belong to $L^2$ because planar area is finite, so the
  local square-integrability bound is preserved.
-/
theorem IsLocalW12RealOn.sub_const
    {Ω : Set ℂ} {u : ℂ → ℝ} {du : ℂ → ℂ →L[ℝ] ℝ}
    (hu : IsLocalW12RealOn Ω u du) (a : ℝ) :
    IsLocalW12RealOn Ω (fun z ↦ u z - a) du := by
  refine ⟨hu.1,
    JJMath.Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues.sub_const_real
      a hu.2.1, ?_⟩
  intro K hK hKΩ
  let μK : Measure ℂ := volume.restrict K
  haveI : IsFiniteMeasure μK :=
    isFiniteMeasure_restrict.2 hK.measure_ne_top
  have huK := hu.2.2 K hK hKΩ
  exact ⟨by
      simpa [μK, Pi.sub_apply] using
        huK.1.sub (memLp_const (α := ℂ) (μ := μK) a),
    huK.2⟩

/--
%%handwave
name:
  Real part of a complex Sobolev map
statement:
  If $f\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb C)$ has weak differential
  $Df$, then $\operatorname{Re}f\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb R)$
  with weak differential $\operatorname{Re}\circ Df$.
proof:
  Apply the real-part functional to the vector-valued weak derivative
  identity and to the compact-local square-integrability bounds.
-/
theorem IsLocalW12On.re
    {Ω : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (h : IsLocalW12On Ω f df) :
    IsLocalW12RealOn Ω (fun z ↦ (f z).re)
      (fun z ↦ Complex.reCLM.comp (df z)) := by
  let postRe : (ℂ →L[ℝ] ℂ) →L[ℝ] (ℂ →L[ℝ] ℝ) :=
    (isBoundedBilinearMap_comp
      (𝕜 := ℝ) (E := ℂ) (F := ℂ) (G := ℝ)).toContinuousLinearMap
        Complex.reCLM
  refine ⟨h.1, weakDerivative_postcomp_continuousLinearMap
    Complex.reCLM h.2.1, ?_⟩
  intro K hK hKΩ
  exact ⟨Complex.reCLM.comp_memLp' (h.2.2 K hK hKΩ).1,
    postRe.comp_memLp' (h.2.2 K hK hKΩ).2⟩

/--
%%handwave
name:
  Imaginary part of a complex Sobolev map
statement:
  If $f\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb C)$ has weak differential
  $Df$, then $\operatorname{Im}f\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb R)$
  with weak differential $\operatorname{Im}\circ Df$.
proof:
  Apply the imaginary-part functional to the vector-valued weak derivative
  identity and to the compact-local square-integrability bounds.
-/
theorem IsLocalW12On.im
    {Ω : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (h : IsLocalW12On Ω f df) :
    IsLocalW12RealOn Ω (fun z ↦ (f z).im)
      (fun z ↦ Complex.imCLM.comp (df z)) := by
  let postIm : (ℂ →L[ℝ] ℂ) →L[ℝ] (ℂ →L[ℝ] ℝ) :=
    (isBoundedBilinearMap_comp
      (𝕜 := ℝ) (E := ℂ) (F := ℂ) (G := ℝ)).toContinuousLinearMap
        Complex.imCLM
  refine ⟨h.1, weakDerivative_postcomp_continuousLinearMap
    Complex.imCLM h.2.1, ?_⟩
  intro K hK hKΩ
  exact ⟨Complex.imCLM.comp_memLp' (h.2.2 K hK hKΩ).1,
    postIm.comp_memLp' (h.2.2 K hK hKΩ).2⟩

/--
%%handwave
name:
  Recombining scalar Sobolev components
statement:
  Let $f:\Omega\to\mathbb C$ and let $Df$ be a field of real-linear maps.
  If the real and imaginary parts of $f$ belong locally to $W^{1,2}$ with
  weak differentials $\operatorname{Re}\circ Df$ and
  $\operatorname{Im}\circ Df$, respectively, then
  $f\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb C)$ with weak differential
  $Df$.
proof:
  Embed each scalar weak derivative identity into the corresponding real or
  imaginary axis of $\mathbb C$ and add them. The same two embeddings
  recombine the compact-local square-integrability bounds.
-/
theorem isLocalW12On_of_re_im
    {Ω : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (hre : IsLocalW12RealOn Ω (fun z ↦ (f z).re)
      (fun z ↦ Complex.reCLM.comp (df z)))
    (him : IsLocalW12RealOn Ω (fun z ↦ (f z).im)
      (fun z ↦ Complex.imCLM.comp (df z))) :
    IsLocalW12On Ω f df := by
  let ofRe : ℝ →L[ℝ] ℂ := Complex.ofRealCLM
  let ofIm : ℝ →L[ℝ] ℂ :=
    (realLinearMapOfWirtinger Complex.I 0).comp Complex.ofRealCLM
  let postRe : (ℂ →L[ℝ] ℝ) →L[ℝ] (ℂ →L[ℝ] ℂ) :=
    (isBoundedBilinearMap_comp
      (𝕜 := ℝ) (E := ℂ) (F := ℝ) (G := ℂ)).toContinuousLinearMap ofRe
  let postIm : (ℂ →L[ℝ] ℝ) →L[ℝ] (ℂ →L[ℝ] ℂ) :=
    (isBoundedBilinearMap_comp
      (𝕜 := ℝ) (E := ℂ) (F := ℝ) (G := ℂ)).toContinuousLinearMap ofIm
  have hweak :=
    (weakDerivative_postcomp_continuousLinearMap ofRe hre.2.1).add
      (weakDerivative_postcomp_continuousLinearMap ofIm him.2.1)
  refine ⟨hre.1, ?_, ?_⟩
  · convert hweak using 1
    · funext z
      apply Complex.ext <;> simp [ofRe, ofIm]
    · funext z
      ext v
      apply Complex.ext <;>
        simp [ofRe, ofIm, ContinuousLinearMap.comp_apply]
  · intro K hK hKΩ
    have hvalue := (ofRe.comp_memLp' (hre.2.2 K hK hKΩ).1).add
      (ofIm.comp_memLp' (him.2.2 K hK hKΩ).1)
    have hderiv := (postRe.comp_memLp' (hre.2.2 K hK hKΩ).2).add
      (postIm.comp_memLp' (him.2.2 K hK hKΩ).2)
    constructor
    · convert hvalue using 1
      funext z
      apply Complex.ext <;> simp [ofRe, ofIm]
    · convert hderiv using 1
      funext z
      ext v
      apply Complex.ext <;>
        simp [postRe, postIm, ofRe, ofIm,
          ContinuousLinearMap.comp_apply]

/--
%%handwave
name:
  Local smooth graph approximation for real planar Sobolev functions
statement:
  Let $Q\Subset P\subseteq\Omega$ be compact planar sets, with a positive
  closed collar of $Q$ contained in $P$. If
  $u\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb R)$ with weak differential
  $Du$, then there are smooth functions $w_n$ such that
  $$
    w_n\longrightarrow u,
    \qquad
    Dw_n\longrightarrow Du
  $$
  in $L^2(Q)$.
proof:
  The local Sobolev hypotheses give $L^2$ control of $u$ and $Du$ on $P$.
  Apply Euclidean smooth graph density across the positive collar between
  $Q$ and $P$.
-/
theorem IsLocalW12RealOn.exists_smoothApproxGraphL2Data_on_compact
    {Ω : Set ℂ} {u : ℂ → ℝ} {du : ℂ → ℂ →L[ℝ] ℝ}
    (hu : IsLocalW12RealOn Ω u du)
    {Q P : Set ℂ} (hQ : IsCompact Q) (hP : IsCompact P)
    (hQP : ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ Q ⊆ P)
    (hPΩ : P ⊆ Ω) :
    Nonempty
      (JJMath.Uniformization.ScalarWeakSobolevSmoothApproxGraphL2Data
        Q u du) := by
  exact JJMath.Uniformization.euclideanSobolev_smooth_graph_density_l2_on_compact
    hQ hP hQP hPΩ hu.1 hu.2.1
      (hu.2.2 P hP hPΩ).1 (hu.2.2 P hP hPΩ).2

/--
%%handwave
name:
  Planar condenser competitor
statement:
  A competitor for the planar condenser with plates $E_0,E_1\subseteq\Omega$
  is a continuous real-valued local $W^{1,2}$ function on the open set
  $\Omega$ which equals $0$ on $E_0$ and $1$ on $E_1$, together with its weak
  differential.
-/
structure PlanarCondenserCompetitor
    (Ω E₀ E₁ : Set ℂ) where
  /-- The real-valued Sobolev representative. -/
  toFun : ℂ → ℝ
  /-- Its weak differential. -/
  weakDifferential : ℂ → ℂ →L[ℝ] ℝ
  /-- The zero plate lies in the energy domain. -/
  zeroPlate_subset : E₀ ⊆ Ω
  /-- The one plate lies in the energy domain. -/
  onePlate_subset : E₁ ⊆ Ω
  /-- The representative and differential form a local $W^{1,2}$ pair. -/
  isLocalW12 : IsLocalW12RealOn Ω toFun weakDifferential
  /-- The chosen representative is continuous on the energy domain. -/
  continuousOn : ContinuousOn toFun Ω
  /-- The representative is zero on the zero plate. -/
  eq_zero_on : ∀ z ∈ E₀, toFun z = 0
  /-- The representative is one on the one plate. -/
  eq_one_on : ∀ z ∈ E₁, toFun z = 1

namespace PlanarCondenserCompetitor

variable {Ω E₀ E₁ : Set ℂ}

instance : CoeFun (PlanarCondenserCompetitor Ω E₀ E₁) (fun _ ↦ ℂ → ℝ) where
  coe u := u.toFun

/--
%%handwave
name:
  Extended planar Dirichlet energy
statement:
  The Dirichlet energy of a planar condenser competitor $u$ is
  $$
    \mathcal E_\Omega(u)=\int_\Omega \lVert Du(z)\rVert^2\,dz,
  $$
  regarded as an extended nonnegative real number.
-/
def dirichletEnergy (u : PlanarCondenserCompetitor Ω E₀ E₁) : ℝ≥0∞ :=
  ∫⁻ z in Ω, ENNReal.ofReal (‖u.weakDifferential z‖ ^ (2 : ℕ)) ∂volume

end PlanarCondenserCompetitor

/--
%%handwave
name:
  Planar condenser capacity
statement:
  The capacity of the two-plate condenser $(E_0,E_1;\Omega)$ is
  $$
    \operatorname{cap}_\Omega(E_0,E_1)
      =\inf_u\int_\Omega\lVert Du(z)\rVert^2\,dz,
  $$
  where the infimum ranges over continuous real-valued local $W^{1,2}$
  competitors equal to $0$ on $E_0$ and $1$ on $E_1$. If there is no
  competitor, the capacity is $\infty$.
-/
def planarCondenserCapacity (Ω E₀ E₁ : Set ℂ) : ℝ≥0∞ :=
  sInf (Set.range
    (PlanarCondenserCompetitor.dirichletEnergy (Ω := Ω) (E₀ := E₀) (E₁ := E₁)))

/--
%%handwave
name:
  Capacity is bounded by every competitor energy
statement:
  For every admissible competitor $u$ for $(E_0,E_1;\Omega)$,
  $$
    \operatorname{cap}_\Omega(E_0,E_1)\leq\mathcal E_\Omega(u).
  $$
proof:
  The capacity is the infimum of all admissible energies, and the energy of
  $u$ is one member of that family.
-/
theorem planarCondenserCapacity_le_dirichletEnergy
    {Ω E₀ E₁ : Set ℂ} (u : PlanarCondenserCompetitor Ω E₀ E₁) :
    planarCondenserCapacity Ω E₀ E₁ ≤ u.dirichletEnergy := by
  apply sInf_le
  exact ⟨u, rfl⟩

/--
%%handwave
name:
  Monotonicity of planar condenser capacity in the plates
statement:
  If $E_0\subseteq A_0\subseteq\Omega$ and
  $E_1\subseteq A_1\subseteq\Omega$, then
  $$
    \operatorname{cap}_{\Omega}(E_0,E_1)
      \leq\operatorname{cap}_{\Omega}(A_0,A_1).
  $$
proof:
  Every competitor which takes the prescribed values on the larger plates
  also takes them on the smaller plates, with unchanged Dirichlet energy.
  Take the infimum over competitors for the larger condenser.
-/
theorem planarCondenserCapacity_mono_plates
    {Ω E₀ E₁ A₀ A₁ : Set ℂ}
    (h₀ : E₀ ⊆ A₀) (h₁ : E₁ ⊆ A₁) :
    planarCondenserCapacity Ω E₀ E₁ ≤
      planarCondenserCapacity Ω A₀ A₁ := by
  simp only [planarCondenserCapacity, sInf_range]
  refine le_iInf fun u ↦ ?_
  let v : PlanarCondenserCompetitor Ω E₀ E₁ :=
    { toFun := u.toFun
      weakDifferential := u.weakDifferential
      zeroPlate_subset := h₀.trans u.zeroPlate_subset
      onePlate_subset := h₁.trans u.onePlate_subset
      isLocalW12 := u.isLocalW12
      continuousOn := u.continuousOn
      eq_zero_on := fun z hz ↦ u.eq_zero_on z (h₀ hz)
      eq_one_on := fun z hz ↦ u.eq_one_on z (h₁ hz) }
  exact iInf_le_of_le v (by
    rfl)

/--
%%handwave
name:
  Quasiconformal pullback energy inequality
statement:
  Let $F:\Omega\to\Omega'$ be $K$-quasiconformal with weak differential
  $Df$, and let $a(y):\mathbb C\to\mathbb R$ be any field of real-linear
  functionals on $\Omega'$. Then
  $$
    \int_\Omega \lVert a(F(z))\circ Df(z)\rVert^2\,dz
      \leq K\int_{\Omega'}\lVert a(y)\rVert^2\,dy.
  $$
proof:
  Pointwise, submultiplicativity of the operator norm and
  $\lVert Df\rVert^2\leq KJ(Df)$ bound the pullback integrand by
  $KJ(Df)\lVert a\circ F\rVert^2$. Integrate and apply [the oriented Sobolev area formula](lean:JJMath.Quasiconformal.IsKQuasiconformalBetween.areaFormula).
-/
theorem IsKQuasiconformalBetween.lintegral_norm_comp_weakDifferential_sq_le
    {K : ℝ} {Ω Ω' : Set ℂ} {F : Ω ≃ₜ Ω'}
    (hF : IsKQuasiconformalBetween K F) {df : ℂ → ℂ →L[ℝ] ℂ}
    (hdf : IsLocalW12On Ω (ambientMap F) df)
    (a : ℂ → ℂ →L[ℝ] ℝ) :
    (∫⁻ z in Ω,
        ENNReal.ofReal
          (‖(a (ambientMap F z)).comp (df z)‖ ^ (2 : ℕ)) ∂volume) ≤
      ENNReal.ofReal K *
        ∫⁻ y in Ω', ENNReal.ofReal (‖a y‖ ^ (2 : ℕ)) ∂volume := by
  have hK : 0 ≤ K := le_trans zero_le_one hF.1
  have hdist := hF.distortion_of_weakDifferential hdf
  have hJ := hF.weakJacobian_nonneg_ae hdf
  have hpoint : ∀ᵐ z ∂volume.restrict Ω,
      ENNReal.ofReal
          (‖(a (ambientMap F z)).comp (df z)‖ ^ (2 : ℕ)) ≤
        ENNReal.ofReal K *
          (ENNReal.ofReal (weakJacobian (df z)) *
            ENNReal.ofReal (‖a (ambientMap F z)‖ ^ (2 : ℕ))) := by
    filter_upwards [hdist, hJ] with z hzdist hzJ
    have hcomp := (a (ambientMap F z)).opNorm_comp_le (df z)
    have hsq :
        ‖(a (ambientMap F z)).comp (df z)‖ ^ (2 : ℕ) ≤
          ‖a (ambientMap F z)‖ ^ (2 : ℕ) * ‖df z‖ ^ (2 : ℕ) := by
      calc
        ‖(a (ambientMap F z)).comp (df z)‖ ^ (2 : ℕ) =
            ‖(a (ambientMap F z)).comp (df z)‖ *
              ‖(a (ambientMap F z)).comp (df z)‖ := by ring
        _ ≤ (‖a (ambientMap F z)‖ * ‖df z‖) *
            (‖a (ambientMap F z)‖ * ‖df z‖) :=
          mul_self_le_mul_self (norm_nonneg _) hcomp
        _ = ‖a (ambientMap F z)‖ ^ (2 : ℕ) *
            ‖df z‖ ^ (2 : ℕ) := by ring
    have hreal :
        ‖(a (ambientMap F z)).comp (df z)‖ ^ (2 : ℕ) ≤
          K * weakJacobian (df z) *
            ‖a (ambientMap F z)‖ ^ (2 : ℕ) := by
      calc
        ‖(a (ambientMap F z)).comp (df z)‖ ^ (2 : ℕ) ≤
            ‖a (ambientMap F z)‖ ^ (2 : ℕ) * ‖df z‖ ^ (2 : ℕ) := hsq
        _ ≤ ‖a (ambientMap F z)‖ ^ (2 : ℕ) *
            (K * weakJacobian (df z)) := by
              exact mul_le_mul_of_nonneg_left hzdist (sq_nonneg _)
        _ = K * weakJacobian (df z) *
            ‖a (ambientMap F z)‖ ^ (2 : ℕ) := by ring
    calc
      ENNReal.ofReal
          (‖(a (ambientMap F z)).comp (df z)‖ ^ (2 : ℕ)) ≤
          ENNReal.ofReal
            (K * weakJacobian (df z) *
              ‖a (ambientMap F z)‖ ^ (2 : ℕ)) :=
        ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal K *
          (ENNReal.ofReal (weakJacobian (df z)) *
            ENNReal.ofReal (‖a (ambientMap F z)‖ ^ (2 : ℕ))) := by
        rw [show K * weakJacobian (df z) *
              ‖a (ambientMap F z)‖ ^ (2 : ℕ) =
            K * (weakJacobian (df z) *
              ‖a (ambientMap F z)‖ ^ (2 : ℕ)) by ring,
          ENNReal.ofReal_mul hK, ENNReal.ofReal_mul hzJ]
  have himage : ambientMap F '' Ω = Ω' := by
    apply Subset.antisymm
    · rintro y ⟨z, hzΩ, rfl⟩
      let zΩ : Ω := ⟨z, hzΩ⟩
      rw [ambientMap_apply F zΩ]
      exact (F zΩ).2
    · intro y hyΩ'
      let yΩ' : Ω' := ⟨y, hyΩ'⟩
      refine ⟨ambientMap F.symm y, ?_, ?_⟩
      · rw [ambientMap_apply F.symm yΩ']
        exact (F.symm yΩ').2
      · simpa only [Homeomorph.symm_symm] using
          (ambientMap_symm_apply_ambientMap F.symm yΩ')
  calc
    (∫⁻ z in Ω,
        ENNReal.ofReal
          (‖(a (ambientMap F z)).comp (df z)‖ ^ (2 : ℕ)) ∂volume) ≤
        ∫⁻ z in Ω, ENNReal.ofReal K *
          (ENNReal.ofReal (weakJacobian (df z)) *
            ENNReal.ofReal (‖a (ambientMap F z)‖ ^ (2 : ℕ))) ∂volume :=
      lintegral_mono_ae hpoint
    _ ≤ ENNReal.ofReal K *
        ∫⁻ z in Ω, ENNReal.ofReal (weakJacobian (df z)) *
          ENNReal.ofReal (‖a (ambientMap F z)‖ ^ (2 : ℕ)) ∂volume :=
      le_of_eq (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top)
    _ = ENNReal.ofReal K *
        ∫⁻ y in ambientMap F '' Ω,
          ENNReal.ofReal (‖a y‖ ^ (2 : ℕ)) ∂volume := by
      rw [hF.areaFormula hdf hdf.1.measurableSet Subset.rfl
        (fun y ↦ ENNReal.ofReal (‖a y‖ ^ (2 : ℕ)))]
    _ = ENNReal.ofReal K *
        ∫⁻ y in Ω', ENNReal.ofReal (‖a y‖ ^ (2 : ℕ)) ∂volume := by
      rw [himage]

/--
%%handwave
name:
  Absolute continuity of pullback measure from Lusin $N^{-1}$
statement:
  Let $F:\Omega\to\Omega'$ be a homeomorphism of measurable planar
  domains with the Lusin $N^{-1}$ property. Then
  $$
    F_*(\mathbf 1_\Omega\,dz)\ll \mathbf 1_{\Omega'}\,dy.
  $$
  Equivalently, the preimage in $\Omega$ of every target null set is null.
proof:
  If $A\subseteq\Omega'$ is null, its image under the ambient inverse is
  null by Lusin $N^{-1}$. The part of $F^{-1}(A)$ lying in $\Omega$ is
  contained in that inverse image. Continuity on the measurable source gives
  the almost-everywhere measurability needed to form the pushforward measure.
-/
theorem HasLusinNInvOn.map_ambientMap_restrict_absolutelyContinuous
    {Ω Ω' : Set ℂ} {F : Ω ≃ₜ Ω'}
    (hN : HasLusinNInvOn F) (hΩ : MeasurableSet Ω) :
    Measure.map (ambientMap F) (volume.restrict Ω) ≪
      volume.restrict Ω' := by
  have hF_aem : AEMeasurable (ambientMap F) (volume.restrict Ω) :=
    ((continuousOn_ambientMap F).aestronglyMeasurable hΩ).aemeasurable
  refine Measure.AbsolutelyContinuous.mk fun s hs hs_zero ↦ ?_
  have hs_inter_zero : volume (s ∩ Ω') = 0 := by
    simpa [Measure.restrict_apply hs] using hs_zero
  have himage_zero : volume (ambientMap F.symm '' (s ∩ Ω')) = 0 :=
    hN (s ∩ Ω') inter_subset_right hs_inter_zero
  have hsubset : ambientMap F ⁻¹' s ∩ Ω ⊆
      ambientMap F.symm '' (s ∩ Ω') := by
    rintro z ⟨hzs, hzΩ⟩
    let zΩ : Ω := ⟨z, hzΩ⟩
    have hFzΩ' : ambientMap F z ∈ Ω' := by
      rw [ambientMap_apply F zΩ]
      exact (F zΩ).2
    refine ⟨ambientMap F z, ⟨hzs, hFzΩ'⟩, ?_⟩
    exact ambientMap_symm_apply_ambientMap F zΩ
  rw [Measure.map_apply_of_aemeasurable hF_aem hs,
    Measure.restrict_apply₀ (hF_aem.nullMeasurableSet_preimage hs)]
  exact measure_mono_null hsubset himage_zero

/--
%%handwave
name:
  Almost-everywhere pullback through a Lusin $N^{-1}$ homeomorphism
statement:
  Let $F:\Omega\to\Omega'$ be a homeomorphism of measurable planar
  domains with the Lusin $N^{-1}$ property. If $P(y)$ holds for almost every
  $y\in\Omega'$, then $P(F(z))$ holds for almost every $z\in\Omega$.
proof:
  The pushforward of planar measure restricted to $\Omega$ is absolutely
  continuous with respect to planar measure restricted to $\Omega'$, so
  almost-everywhere statements pull back through $F$.
-/
theorem ae_comp_ambientMap_of_hasLusinNInvOn
    {Ω Ω' : Set ℂ} {F : Ω ≃ₜ Ω'}
    (hN : HasLusinNInvOn F) (hΩ : MeasurableSet Ω)
    {P : ℂ → Prop} (hP : ∀ᵐ y ∂volume.restrict Ω', P y) :
    ∀ᵐ z ∂volume.restrict Ω, P (ambientMap F z) := by
  have hF_aem : AEMeasurable (ambientMap F) (volume.restrict Ω) :=
    ((continuousOn_ambientMap F).aestronglyMeasurable hΩ).aemeasurable
  exact (Measure.tendsto_ae_map hF_aem).mono_right
    (hN.map_ambientMap_restrict_absolutelyContinuous hΩ).ae_le hP

/--
%%handwave
name:
  Measurability of pullback through a Lusin $N^{-1}$ homeomorphism
statement:
  Let $F:\Omega\to\Omega'$ be a homeomorphism of measurable planar
  domains with the Lusin $N^{-1}$ property. If
  $g:\Omega'\to E$ is almost everywhere strongly measurable, then
  $g\circ F$ is almost everywhere strongly measurable on $\Omega$.
proof:
  The pushforward of planar measure restricted to $\Omega$ is absolutely
  continuous with respect to planar measure restricted to $\Omega'$. Replace
  $g$ by a strongly measurable representative and compose it with the
  almost-everywhere measurable ambient representative of $F$.
-/
theorem AEStronglyMeasurable.comp_ambientMap_of_hasLusinNInvOn
    {E : Type} [NormedAddCommGroup E]
    {Ω Ω' : Set ℂ} {F : Ω ≃ₜ Ω'}
    {g : ℂ → E}
    (hg : AEStronglyMeasurable g (volume.restrict Ω'))
    (hN : HasLusinNInvOn F) (hΩ : MeasurableSet Ω) :
    AEStronglyMeasurable (fun z ↦ g (ambientMap F z))
      (volume.restrict Ω) := by
  have hF_aem : AEMeasurable (ambientMap F) (volume.restrict Ω) :=
    ((continuousOn_ambientMap F).aestronglyMeasurable hΩ).aemeasurable
  exact (hg.mono_ac
    (hN.map_ambientMap_restrict_absolutelyContinuous hΩ)).comp_aemeasurable
      hF_aem

/--
%%handwave
name:
  Extended square integral as the square of the $L^2$ seminorm
statement:
  For every function $g:X\to E$ and measure $\mu$,
  $$
    \lVert g\rVert_{L^2(\mu)}^2
      =\int_X \operatorname{ofReal}(\lVert g(x)\rVert^2)\,d\mu(x).
  $$
  This identity is valid in the extended nonnegative reals, without an
  integrability assumption.
proof:
  Unfold the $L^2$ seminorm as the square root of the extended integral of
  the squared extended norm, square it, and move the square through the
  nonnegative-real embedding.
-/
theorem eLpNorm_two_pow_two_eq_lintegral_ofReal_norm_sq
    {α E : Type} [MeasurableSpace α] [NormedAddCommGroup E]
    (g : α → E) (μ : Measure α) :
    eLpNorm g 2 μ ^ (2 : ℕ) =
      ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ (2 : ℕ)) ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ (∞ : ℝ≥0∞))]
  simp only [ENNReal.toReal_ofNat, one_div]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

set_option maxHeartbeats 2400000 in
/--
%%handwave
name:
  Strong $L^2$ convergence after quasiconformal pullback
statement:
  Let $F:\Omega\to\Omega'$ be $K$-quasiconformal with weak differential
  $Df$, and let $Q\subseteq\Omega'$ be measurable. If covector fields
  $a_n$ satisfy $a_n\to0$ in $L^2(Q)$, then
  $$
    \bigl(\mathbf 1_Qa_n\bigr)(F(z))\circ Df(z)
      \longrightarrow0
      \quad\text{in }L^2(\Omega).
  $$
proof:
  The Lusin $N^{-1}$ property gives measurability of the pulled-back fields.
  The quasiconformal energy inequality bounds the square of each source
  $L^2$ seminorm by $K$ times the square of the corresponding target
  seminorm. The latter tends to zero.
-/
theorem IsKQuasiconformalBetween.indicator_pullback_tendsto_l2
    {K : ℝ} {Ω Ω' Q : Set ℂ} {F : Ω ≃ₜ Ω'}
    (hF : IsKQuasiconformalBetween K F)
    {df : ℂ → ℂ →L[ℝ] ℂ}
    (hdf : IsLocalW12On Ω (ambientMap F) df)
    (hQ : MeasurableSet Q) (hQΩ' : Q ⊆ Ω')
    {a : ℕ → ℂ → ℂ →L[ℝ] ℝ}
    (ha_mem : ∀ n, MemLp (a n) 2 (volume.restrict Q))
    (ha_zero : Filter.Tendsto
      (fun n ↦ eLpNorm (a n) 2 (volume.restrict Q))
      Filter.atTop (𝓝 0)) :
    (∀ n, MemLp
      (fun z ↦ ((Q.indicator (a n)) (ambientMap F z)).comp (df z))
      2 (volume.restrict Ω)) ∧
      Filter.Tendsto
        (fun n ↦ eLpNorm
          (fun z ↦ ((Q.indicator (a n)) (ambientMap F z)).comp (df z))
          2 (volume.restrict Ω))
        Filter.atTop (𝓝 0) := by
  let A : ℕ → ℂ → ℂ →L[ℝ] ℝ := fun n ↦ Q.indicator (a n)
  let b : ℕ → ℂ → ℂ →L[ℝ] ℝ := fun n z ↦
    (A n (ambientMap F z)).comp (df z)
  have hA_mem : ∀ n, MemLp (A n) 2 volume := by
    intro n
    change MemLp (Q.indicator (a n)) 2 volume
    exact (memLp_indicator_iff_restrict
      (μ := (volume : Measure ℂ)) (s := Q) (f := a n)
      (p := (2 : ℝ≥0∞)) hQ).2 (ha_mem n)
  have hA_norm : ∀ n,
      eLpNorm (A n) 2 (volume.restrict Ω') =
        eLpNorm (a n) 2 (volume.restrict Q) := by
    intro n
    calc
      eLpNorm (A n) 2 (volume.restrict Ω') =
          eLpNorm (a n) 2 ((volume.restrict Ω').restrict Q) := by
        simpa [A] using
          (eLpNorm_indicator_eq_eLpNorm_restrict
            (μ := volume.restrict Ω') (f := a n) (p := (2 : ℝ≥0∞)) hQ)
      _ = eLpNorm (a n) 2 (volume.restrict Q) := by
        rw [Measure.restrict_restrict_of_subset hQΩ']
  have hdf_meas : AEStronglyMeasurable df (volume.restrict Ω) :=
    hdf.differential_locallyIntegrableOn.aestronglyMeasurable
  let compCLM :
      (ℂ →L[ℝ] ℝ) →L[ℝ] (ℂ →L[ℝ] ℂ) →L[ℝ] (ℂ →L[ℝ] ℝ) :=
    (isBoundedBilinearMap_comp
      (𝕜 := ℝ) (E := ℂ) (F := ℂ) (G := ℝ)).toContinuousLinearMap
  have hb_meas : ∀ n, AEStronglyMeasurable (b n) (volume.restrict Ω) := by
    intro n
    have hA_target : AEStronglyMeasurable (A n) (volume.restrict Ω') :=
      (hA_mem n).aestronglyMeasurable.restrict
    have hAF_meas : AEStronglyMeasurable
        (fun z ↦ A n (ambientMap F z)) (volume.restrict Ω) :=
      JJMath.Quasiconformal.AEStronglyMeasurable.comp_ambientMap_of_hasLusinNInvOn
        hA_target
        hF.hasLusinNInvOn hdf.1.measurableSet
    simpa [b, compCLM] using compCLM.aestronglyMeasurable_comp₂
      hAF_meas hdf_meas
  have hsq : ∀ n,
      eLpNorm (b n) 2 (volume.restrict Ω) ^ (2 : ℕ) ≤
        ENNReal.ofReal K *
          eLpNorm (a n) 2 (volume.restrict Q) ^ (2 : ℕ) := by
    intro n
    have henergy := hF.lintegral_norm_comp_weakDifferential_sq_le hdf (A n)
    rw [← eLpNorm_two_pow_two_eq_lintegral_ofReal_norm_sq
        (b n) (volume.restrict Ω),
      ← eLpNorm_two_pow_two_eq_lintegral_ofReal_norm_sq
        (A n) (volume.restrict Ω'), hA_norm n] at henergy
    exact henergy
  have hb_mem : ∀ n, MemLp (b n) 2 (volume.restrict Ω) := by
    intro n
    have hrhs_lt : ENNReal.ofReal K *
        eLpNorm (a n) 2 (volume.restrict Q) ^ (2 : ℕ) < ∞ :=
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (ENNReal.pow_lt_top (ha_mem n).eLpNorm_lt_top)
    have hsq_lt : eLpNorm (b n) 2 (volume.restrict Ω) ^ (2 : ℕ) < ∞ :=
      lt_of_le_of_lt (hsq n) hrhs_lt
    have hb_lt : eLpNorm (b n) 2 (volume.restrict Ω) < ∞ :=
      (ENNReal.pow_lt_top_iff.mp hsq_lt).resolve_right (by norm_num)
    exact ⟨hb_meas n, hb_lt⟩
  have hrhs_zero : Filter.Tendsto
      (fun n ↦ ENNReal.ofReal K *
        eLpNorm (a n) 2 (volume.restrict Q) ^ (2 : ℕ))
      Filter.atTop (𝓝 0) := by
    have ha_sq : Filter.Tendsto
        (fun n ↦ eLpNorm (a n) 2 (volume.restrict Q) ^ (2 : ℕ))
        Filter.atTop (𝓝 0) := by
      simpa [pow_two] using ENNReal.Tendsto.mul ha_zero
        (Or.inr ENNReal.zero_ne_top) ha_zero
        (Or.inr ENNReal.zero_ne_top)
    simpa using
      (ENNReal.continuous_const_mul
        (ENNReal.ofReal_ne_top : ENNReal.ofReal K ≠ ∞)).continuousAt.tendsto.comp
          ha_sq
  have hsq_zero : Filter.Tendsto
      (fun n ↦ eLpNorm (b n) 2 (volume.restrict Ω) ^ (2 : ℕ))
      Filter.atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      hrhs_zero (fun _ ↦ zero_le) hsq
  have hb_zero : Filter.Tendsto
      (fun n ↦ eLpNorm (b n) 2 (volume.restrict Ω))
      Filter.atTop (𝓝 0) := by
    rw [ENNReal.tendsto_atTop_zero] at hsq_zero ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hsq_zero (ε ^ (2 : ℕ)) (ENNReal.pow_pos hε 2)
    refine ⟨N, fun n hn ↦ ?_⟩
    exact (ENNReal.pow_le_pow_left_iff (by norm_num : (2 : ℕ) ≠ 0)).mp
      (hN n hn)
  refine ⟨?_, ?_⟩
  · simpa [b, A] using hb_mem
  · simpa [b, A] using hb_zero

/--
%%handwave
name:
  Local $L^2$ control of a quasiconformal covector pullback
statement:
  Let $F:\Omega\to\Omega'$ be quasiconformal with weak differential $Df$.
  If $Q\subseteq\Omega'$ is measurable and a covector field $a$ belongs to
  $L^2(Q)$, then
  $$
    \bigl(\mathbf 1_Qa\bigr)(F(z))\circ Df(z)
  $$
  belongs to $L^2(\Omega)$.
proof:
  Apply strong $L^2$ convergence after quasiconformal pullback to the
  sequence whose zeroth term is $a$ and whose remaining terms vanish. The
  membership conclusion for its zeroth pulled-back term is the claim.
-/
theorem IsKQuasiconformalBetween.indicator_pullback_memLp
    {K : ℝ} {Ω Ω' Q : Set ℂ} {F : Ω ≃ₜ Ω'}
    (hF : IsKQuasiconformalBetween K F)
    {df : ℂ → ℂ →L[ℝ] ℂ}
    (hdf : IsLocalW12On Ω (ambientMap F) df)
    (hQ : MeasurableSet Q) (hQΩ' : Q ⊆ Ω')
    {a : ℂ → ℂ →L[ℝ] ℝ}
    (ha : MemLp a 2 (volume.restrict Q)) :
    MemLp
      (fun z ↦ ((Q.indicator a) (ambientMap F z)).comp (df z))
      2 (volume.restrict Ω) := by
  let aSeq : ℕ → ℂ → ℂ →L[ℝ] ℝ := fun n ↦
    if n = 0 then a else 0
  have haSeq_mem : ∀ n, MemLp (aSeq n) 2 (volume.restrict Q) := by
    intro n
    by_cases hn : n = 0
    · simpa [aSeq, hn] using ha
    · rw [show aSeq n = 0 by simp [aSeq, hn]]
      exact (MemLp.zero' (α := ℂ) (ε := ℂ →L[ℝ] ℝ)
        (p := (2 : ℝ≥0∞)) (μ := volume.restrict Q))
  have haSeq_zero : Filter.Tendsto
      (fun n ↦ eLpNorm (aSeq n) 2 (volume.restrict Q))
      Filter.atTop (𝓝 0) := by
    rw [ENNReal.tendsto_atTop_zero]
    intro ε hε
    refine ⟨1, fun n hn ↦ ?_⟩
    have hn0 : n ≠ 0 := Nat.ne_of_gt hn
    change eLpNorm
      (if n = 0 then a else fun _ : ℂ ↦ (0 : ℂ →L[ℝ] ℝ)) 2
        (volume.restrict Q) ≤ ε
    rw [if_neg hn0]
    exact (eLpNorm_zero'
      (α := ℂ) (ε := ℂ →L[ℝ] ℝ) (p := (2 : ℝ≥0∞))
      (μ := volume.restrict Q)).le.trans zero_le
  have hpull := hF.indicator_pullback_tendsto_l2 hdf hQ hQΩ'
    haSeq_mem haSeq_zero
  simpa [aSeq] using hpull.1 0

/--
%%handwave
name:
  Globally Lipschitz differential of a smooth compactly supported function
statement:
  If $u:\mathbb C\to\mathbb R$ is smooth and compactly supported, then its
  differential field $z\mapsto Du(z)$ is globally Lipschitz.
proof:
  The differential of a smooth function is smooth. Its support is contained
  in the compact support of the function, so a bounded-derivative argument
  gives a global Lipschitz constant.
-/
theorem smoothCompactlySupported_fderiv_lipschitz
    {U : Set ℂ}
    (u : JJMath.Uniformization.SmoothCompactlySupportedManifoldCoordinateFunction U) :
    ∃ C : NNReal, LipschitzWith C (fderiv ℝ (u : ℂ → ℝ)) := by
  have hdu_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fderiv ℝ (u : ℂ → ℝ)) :=
    (contDiff_infty_iff_fderiv.mp u.smooth).2
  have hdu_compact : IsCompact (tsupport (fderiv ℝ (u : ℂ → ℝ))) :=
    u.compact_support.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_fderiv_subset ℝ)
  exact hdu_smooth.lipschitzWith_of_hasCompactSupport hdu_compact (by simp)

/--
%%handwave
name:
  Global bound for a smooth compactly supported function
statement:
  If $u:H\to\mathbb R$ is smooth and compactly supported on a real normed
  space, then there is a nonnegative constant $C$ such that
  $|u(z)|\leq C$ for every $z\in H$.
proof:
  The function is bounded on its compact support by continuity and vanishes
  outside that support.
-/
theorem smoothCompactlySupported_exists_forall_norm_le
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {U : Set H}
    (u : JJMath.Uniformization.SmoothCompactlySupportedManifoldCoordinateFunction U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : H, ‖u z‖ ≤ C := by
  rcases u.compact_support.exists_bound_of_continuousOn
      u.smooth.continuous.continuousOn with ⟨C, hC⟩
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro z
  by_cases hz : z ∈ tsupport (u : H → ℝ)
  · exact (hC z hz).trans (le_max_left _ _)
  · simp [image_eq_zero_of_notMem_tsupport hz]

/--
%%handwave
name:
  Global bound for a smooth Sobolev cutoff
statement:
  If $\chi:H\to\mathbb R$ is a smooth cutoff with compact support, then
  there is a nonnegative constant $C$ such that
  $|\chi(z)|\leq C$ for every $z\in H$.
proof:
  The cutoff is bounded on its compact support by continuity and vanishes
  outside that support.
-/
theorem scalarWeakSobolevCutoff_exists_forall_norm_le
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {Q U : Set H}
    (χ : JJMath.Uniformization.ScalarWeakSobolevCutoff Q U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : H, ‖χ z‖ ≤ C := by
  rcases χ.compact_support.exists_bound_of_continuousOn
      χ.smooth.continuous.continuousOn with ⟨C, hC⟩
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro z
  by_cases hz : z ∈ tsupport (χ : H → ℝ)
  · exact (hC z hz).trans (le_max_left _ _)
  · simp [image_eq_zero_of_notMem_tsupport hz]

/--
%%handwave
name:
  Global bound for the differential of a smooth compactly supported function
statement:
  If $u:H\to\mathbb R$ is smooth and compactly supported on a real normed
  space, then there is a nonnegative constant $C$ such that
  $\lVert Du(z)\rVert\leq C$ for every $z\in H$.
proof:
  The differential is continuous and its support is contained in the compact
  support of $u$. It is therefore bounded on that support and vanishes
  outside it.
-/
theorem smoothCompactlySupported_exists_forall_fderiv_norm_le
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {U : Set H}
    (u : JJMath.Uniformization.SmoothCompactlySupportedManifoldCoordinateFunction U) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : H, ‖fderiv ℝ (u : H → ℝ) z‖ ≤ C := by
  have hdu_cont : Continuous (fderiv ℝ (u : H → ℝ)) :=
    u.smooth.continuous_fderiv (by simp)
  have hdu_compact : IsCompact (tsupport (fderiv ℝ (u : H → ℝ))) :=
    u.compact_support.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_fderiv_subset ℝ)
  rcases hdu_compact.exists_bound_of_continuousOn hdu_cont.continuousOn with
    ⟨C, hC⟩
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro z
  by_cases hz : z ∈ tsupport (fderiv ℝ (u : H → ℝ))
  · exact (hC z hz).trans (le_max_left _ _)
  · simp [image_eq_zero_of_notMem_tsupport hz]

/--
%%handwave
name:
  Bounded smooth scalar retraction on a compact interval
statement:
  For every compact interval $[a,b]\subseteq\mathbb R$, there is a smooth
  compactly supported function $\vartheta:\mathbb R\to\mathbb R$ such that
  for every $t\in[a,b]$,
  $$
    \vartheta(t)=t,
    \qquad
    D\vartheta(t)=\operatorname{id}_{\mathbb R}.
  $$
proof:
  Choose a smooth compactly supported cutoff equal to one, with zero
  differential, on $[a,b]$, and multiply it by the identity function.
-/
theorem exists_smoothCompactlySupported_eq_self_fderiv_eq_id_on_Icc
    (a b : ℝ) :
    ∃ θ : JJMath.Uniformization.SmoothCompactlySupportedManifoldCoordinateFunction
        (Set.univ : Set ℝ),
      (∀ t ∈ Set.Icc a b, θ t = t) ∧
        ∀ t ∈ Set.Icc a b,
          fderiv ℝ (θ : ℝ → ℝ) t = ContinuousLinearMap.id ℝ ℝ := by
  rcases JJMath.Uniformization.exists_scalarWeakSobolevCutoff
      (Q := Set.Icc a b) (Ω := Set.univ)
      isCompact_Icc (Set.subset_univ _) isOpen_univ with ⟨χ⟩
  let θ : JJMath.Uniformization.SmoothCompactlySupportedManifoldCoordinateFunction
      (Set.univ : Set ℝ) :=
    { toFun := fun t ↦ χ t * t
      smooth := χ.smooth.mul contDiff_id
      support_subset := (tsupport_mul_subset_left).trans (Set.subset_univ _)
      compact_support :=
        χ.compact_support.of_isClosed_subset (isClosed_tsupport _)
          tsupport_mul_subset_left }
  refine ⟨θ, ?_, ?_⟩
  · intro t ht
    simp [θ, χ.eq_one_on t ht]
  · intro t ht
    change fderiv ℝ (fun s : ℝ ↦ χ s * s) t =
      ContinuousLinearMap.id ℝ ℝ
    have hid : DifferentiableAt ℝ (fun s : ℝ ↦ s) t := differentiableAt_id
    rw [fderiv_fun_mul ((χ.smooth.differentiable (by simp)) t) hid]
    simp [χ.eq_one_on t ht, χ.fderiv_eq_zero_on t ht]

/--
%%handwave
name:
  Bounded smooth retraction fixing a continuous compact range
statement:
  Let $Q$ be compact and let $u:Q\to\mathbb R$ be continuous. There is a
  smooth compactly supported function $\vartheta:\mathbb R\to\mathbb R$
  such that, for every $z\in Q$,
  $$
    \vartheta(u(z))=u(z),
    \qquad
    D\vartheta(u(z))=\operatorname{id}_{\mathbb R}.
  $$
proof:
  The absolute value of $u$ is bounded by some $M\geq0$ on $Q$. Choose the
  compactly supported smooth scalar retraction which equals the identity,
  with identity differential, on $[-M,M]$.
-/
theorem exists_smoothCompactlySupported_fix_continuousOn_compact_range
    {H : Type} [TopologicalSpace H]
    {Q : Set H} (hQ : IsCompact Q) {u : H → ℝ}
    (hu : ContinuousOn u Q) :
    ∃ θ : JJMath.Uniformization.SmoothCompactlySupportedManifoldCoordinateFunction
        (Set.univ : Set ℝ),
      ∀ z ∈ Q,
        θ (u z) = u z ∧
          fderiv ℝ (θ : ℝ → ℝ) (u z) = ContinuousLinearMap.id ℝ ℝ := by
  rcases hQ.exists_bound_of_continuousOn hu with ⟨C, hC⟩
  let M : ℝ := max C 0
  rcases exists_smoothCompactlySupported_eq_self_fderiv_eq_id_on_Icc
      (-M) M with ⟨θ, hθ_value, hθ_deriv⟩
  refine ⟨θ, fun z hz ↦ ?_⟩
  have huM : |u z| ≤ M := by
    simpa [Real.norm_eq_abs, M] using
      (hC z hz).trans (le_max_left C 0)
  have huz : u z ∈ Set.Icc (-M) M := (abs_le.mp huM)
  exact ⟨hθ_value (u z) huz, hθ_deriv (u z) huz⟩

/--
%%handwave
name:
  Dominated almost-everywhere convergence in $L^2$
statement:
  Let $a\in L^2(X,E)$ and let $b_n:X\to F$ be measurable. Suppose
  $b_n(x)\to0$ almost everywhere and, for one real constant $C$,
  $$
    \lVert b_n(x)\rVert\leq C\lVert a(x)\rVert
  $$
  for every $n$ and almost every $x$. Then every $b_n$ belongs to $L^2$
  and $\lVert b_n\rVert_{L^2}\to0$.
proof:
  The pointwise bound gives $L^2$ membership. Apply dominated convergence
  to $\lVert b_n\rVert^2$, dominated by
  $C^2\lVert a\rVert^2$, and identify the resulting integrals with the
  squares of the finite $L^2$ norms.
-/
theorem memLp_and_tendsto_zero_of_ae_tendsto_of_norm_le_mul
    {α E F : Type} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    {μ : Measure α} {a : α → E} {b : ℕ → α → F} {C : ℝ}
    (ha : MemLp a 2 μ)
    (hb_meas : ∀ n, AEStronglyMeasurable (b n) μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖b n x‖ ≤ C * ‖a x‖)
    (hb_zero : ∀ᵐ x ∂μ,
      Filter.Tendsto (fun n ↦ b n x) Filter.atTop (𝓝 0)) :
    (∀ n, MemLp (b n) 2 μ) ∧
      Filter.Tendsto (fun n ↦ eLpNorm (b n) 2 μ)
        Filter.atTop (𝓝 0) := by
  have hb_mem : ∀ n, MemLp (b n) 2 μ := fun n ↦
    ha.of_le_mul (hb_meas n) (hbound n)
  have ha_sq_int : Integrable (fun x ↦ ‖a x‖ ^ (2 : ℕ)) μ :=
    (memLp_two_iff_integrable_sq_norm ha.aestronglyMeasurable).1 ha
  have hdom_int : Integrable
      (fun x ↦ C ^ (2 : ℕ) * ‖a x‖ ^ (2 : ℕ)) μ :=
    ha_sq_int.const_mul _
  have hsq_meas : ∀ n, AEStronglyMeasurable
      (fun x ↦ ‖b n x‖ ^ (2 : ℕ)) μ := fun n ↦
    (hb_meas n).norm.pow _
  have hsq_bound : ∀ n, ∀ᵐ x ∂μ,
      ‖‖b n x‖ ^ (2 : ℕ)‖ ≤
        C ^ (2 : ℕ) * ‖a x‖ ^ (2 : ℕ) := by
    intro n
    filter_upwards [hbound n] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [norm_nonneg (b n x), norm_nonneg (a x)]
  have hsq_zero : ∀ᵐ x ∂μ,
      Filter.Tendsto (fun n ↦ ‖b n x‖ ^ (2 : ℕ))
        Filter.atTop (𝓝 0) := by
    filter_upwards [hb_zero] with x hx
    simpa using hx.norm.pow 2
  have hint : Filter.Tendsto
      (fun n ↦ ∫ x, ‖b n x‖ ^ (2 : ℕ) ∂μ)
      Filter.atTop (𝓝 0) := by
    simpa using
      (tendsto_integral_of_dominated_convergence
        (μ := μ) (F := fun n x ↦ ‖b n x‖ ^ (2 : ℕ))
        (f := fun _ ↦ (0 : ℝ))
        (fun x ↦ C ^ (2 : ℕ) * ‖a x‖ ^ (2 : ℕ))
        hsq_meas hdom_int hsq_bound hsq_zero)
  have hreal : Filter.Tendsto
      (fun n ↦ (eLpNorm (b n) 2 μ).toReal)
      Filter.atTop (𝓝 0) := by
    have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hint
    simp only [Real.sqrt_zero] at hsqrt
    convert hsqrt using 1
    · funext n
      calc
        (eLpNorm (b n) 2 μ).toReal =
            Real.sqrt ((eLpNorm (b n) 2 μ).toReal ^ (2 : ℕ)) :=
          (Real.sqrt_sq ENNReal.toReal_nonneg).symm
        _ = Real.sqrt (∫ x, ‖b n x‖ ^ (2 : ℕ) ∂μ) := by
          rw [eLpNorm_two_toReal_sq_eq_integral_norm_sq (hb_mem n)]
  refine ⟨hb_mem, ?_⟩
  exact (ENNReal.tendsto_toReal_zero_iff
    (fun n ↦ (hb_mem n).eLpNorm_lt_top.ne)).mp hreal

set_option maxHeartbeats 4800000 in
/--
%%handwave
name:
  Bounded retraction of scalar Sobolev graph approximants
statement:
  Let $w_n\to w$ and $Dw_n\to Dw$ in $L^2(Q)$, where the $w_n$ are
  smooth. Suppose $\vartheta:\mathbb R\to\mathbb R$ is smooth and compactly
  supported, and almost everywhere on $Q$,
  $$
    \vartheta(w)=w,
    \qquad
    D\vartheta(w)=\operatorname{id}_{\mathbb R}.
  $$
  Then some subsequence satisfies
  $\vartheta(w_{n_j})\to w$ almost everywhere and
  $$
    D\vartheta(w_{n_j})\circ Dw_{n_j}\longrightarrow Dw
      \quad\text{in }L^2(Q).
  $$
proof:
  Extract a subsequence for which $w_{n_j}\to w$ almost everywhere. The
  value conclusion follows by continuity. Split the derivative error as
  $$
    D\vartheta(w_{n_j})(Dw_{n_j}-Dw)
      +(D\vartheta(w_{n_j})-D\vartheta(w))Dw.
  $$
  The first term is controlled by the bounded differential of
  $\vartheta$ and graph-norm convergence. The second converges pointwise
  and is dominated by a constant multiple of $\lVert Dw\rVert$, so
  dominated $L^2$ convergence applies.
-/
theorem scalarWeakSobolevSmoothApproxGraphL2Data_exists_retracted_subsequence
    {Q : Set ℂ} {w : ℂ → ℝ} {dw : ℂ → ℂ →L[ℝ] ℝ}
    (hgraph : JJMath.Uniformization.ScalarWeakSobolevSmoothApproxGraphL2Data
      Q w dw)
    (hw_meas : AEStronglyMeasurable w (volume.restrict Q))
    (hdw_mem : MemLp dw 2 (volume.restrict Q))
    {U : Set ℝ}
    (θ : JJMath.Uniformization.SmoothCompactlySupportedManifoldCoordinateFunction U)
    (hθ_value : ∀ᵐ z ∂volume.restrict Q, θ (w z) = w z)
    (hθ_deriv : ∀ᵐ z ∂volume.restrict Q,
      fderiv ℝ (θ : ℝ → ℝ) (w z) = ContinuousLinearMap.id ℝ ℝ) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      (∀ᵐ z ∂volume.restrict Q,
        Filter.Tendsto (fun n ↦ θ (hgraph.approximants (ns n) z))
          Filter.atTop (𝓝 (w z))) ∧
      (∀ n, MemLp
        (fun z ↦
          (fderiv ℝ (θ : ℝ → ℝ) (hgraph.approximants (ns n) z)).comp
              (fderiv ℝ (hgraph.approximants (ns n)) z) - dw z)
        2 (volume.restrict Q)) ∧
      Filter.Tendsto
        (fun n ↦ eLpNorm
          (fun z ↦
            (fderiv ℝ (θ : ℝ → ℝ) (hgraph.approximants (ns n) z)).comp
                (fderiv ℝ (hgraph.approximants (ns n)) z) - dw z)
          2 (volume.restrict Q))
        Filter.atTop (𝓝 0) := by
  let μQ : Measure ℂ := volume.restrict Q
  have hvalue_measure : TendstoInMeasure μQ hgraph.approximants
      Filter.atTop w := by
    apply tendstoInMeasure_of_tendsto_eLpNorm (p := 2)
    · norm_num
    · exact fun n ↦ (hgraph.smooth n).continuous.aestronglyMeasurable
    · exact hw_meas
    · simpa [μQ] using hgraph.value_tendsto_l2
  rcases hvalue_measure.exists_seq_tendsto_ae with
    ⟨ns, hns, hvalue_ae⟩
  have hθvalue_ae : ∀ᵐ z ∂μQ,
      Filter.Tendsto (fun n ↦ θ (hgraph.approximants (ns n) z))
        Filter.atTop (𝓝 (w z)) := by
    filter_upwards [hvalue_ae, hθ_value] with z hz hzθ
    simpa [hzθ] using θ.smooth.continuous.continuousAt.tendsto.comp hz
  obtain ⟨M, hM_nonneg, hM⟩ :=
    smoothCompactlySupported_exists_forall_fderiv_norm_le θ
  have hdθ_cont : Continuous (fderiv ℝ (θ : ℝ → ℝ)) :=
    θ.smooth.continuous_fderiv (by simp)
  let compCLM :
      (ℝ →L[ℝ] ℝ) →L[ℝ] (ℂ →L[ℝ] ℝ) →L[ℝ] (ℂ →L[ℝ] ℝ) :=
    (isBoundedBilinearMap_comp
      (𝕜 := ℝ) (E := ℂ) (F := ℝ) (G := ℝ)).toContinuousLinearMap
  let first : ℕ → ℂ → ℂ →L[ℝ] ℝ := fun n z ↦
    (fderiv ℝ (θ : ℝ → ℝ) (hgraph.approximants (ns n) z)).comp
      (fderiv ℝ (hgraph.approximants (ns n)) z - dw z)
  have hfirst_meas : ∀ n, AEStronglyMeasurable (first n) μQ := by
    intro n
    have hleft : AEStronglyMeasurable
        (fun z ↦ fderiv ℝ (θ : ℝ → ℝ)
          (hgraph.approximants (ns n) z)) μQ :=
      hdθ_cont.comp_aestronglyMeasurable
        (hgraph.smooth (ns n)).continuous.aestronglyMeasurable
    simpa [first, compCLM] using compCLM.aestronglyMeasurable_comp₂
      hleft (hgraph.derivative_error_memLp (ns n)).aestronglyMeasurable
  have hfirst_bound : ∀ n, ∀ᵐ z ∂μQ,
      ‖first n z‖ ≤ M *
        ‖fderiv ℝ (hgraph.approximants (ns n)) z - dw z‖ := by
    intro n
    filter_upwards with z
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right
        (hM (hgraph.approximants (ns n) z)) (norm_nonneg _))
  obtain ⟨hfirst_mem, hfirst_zero⟩ :=
    memLp_and_tendsto_zero_of_norm_le_mul
      (fun n ↦ hgraph.derivative_error_memLp (ns n)) hfirst_meas
      hfirst_bound (hgraph.derivative_tendsto_l2.comp hns.tendsto_atTop)
  let second : ℕ → ℂ → ℂ →L[ℝ] ℝ := fun n z ↦
    (fderiv ℝ (θ : ℝ → ℝ) (hgraph.approximants (ns n) z) -
      fderiv ℝ (θ : ℝ → ℝ) (w z)).comp (dw z)
  have hsecond_meas : ∀ n, AEStronglyMeasurable (second n) μQ := by
    intro n
    have hleft : AEStronglyMeasurable
        (fun z ↦ fderiv ℝ (θ : ℝ → ℝ)
            (hgraph.approximants (ns n) z) -
          fderiv ℝ (θ : ℝ → ℝ) (w z)) μQ :=
      (hdθ_cont.comp_aestronglyMeasurable
          (hgraph.smooth (ns n)).continuous.aestronglyMeasurable).sub
        (hdθ_cont.comp_aestronglyMeasurable hw_meas)
    simpa [second, compCLM] using compCLM.aestronglyMeasurable_comp₂
      hleft hdw_mem.aestronglyMeasurable
  have hsecond_bound : ∀ n, ∀ᵐ z ∂μQ,
      ‖second n z‖ ≤ (2 * M) * ‖dw z‖ := by
    intro n
    filter_upwards with z
    calc
      ‖second n z‖ ≤
          ‖fderiv ℝ (θ : ℝ → ℝ) (hgraph.approximants (ns n) z) -
            fderiv ℝ (θ : ℝ → ℝ) (w z)‖ * ‖dw z‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (2 * M) * ‖dw z‖ := by
        gcongr
        calc
          ‖fderiv ℝ (θ : ℝ → ℝ) (hgraph.approximants (ns n) z) -
              fderiv ℝ (θ : ℝ → ℝ) (w z)‖
              ≤ ‖fderiv ℝ (θ : ℝ → ℝ)
                  (hgraph.approximants (ns n) z)‖ +
                ‖fderiv ℝ (θ : ℝ → ℝ) (w z)‖ := norm_sub_le _ _
          _ ≤ M + M := add_le_add
            (hM (hgraph.approximants (ns n) z)) (hM (w z))
          _ = 2 * M := by ring
  have hsecond_ae : ∀ᵐ z ∂μQ,
      Filter.Tendsto (fun n ↦ second n z) Filter.atTop (𝓝 0) := by
    filter_upwards [hvalue_ae] with z hz
    have hleft : Filter.Tendsto
        (fun n ↦ fderiv ℝ (θ : ℝ → ℝ)
            (hgraph.approximants (ns n) z) -
          fderiv ℝ (θ : ℝ → ℝ) (w z))
        Filter.atTop (𝓝 0) := by
      have hconst : Filter.Tendsto
          (fun _ : ℕ ↦ fderiv ℝ (θ : ℝ → ℝ) (w z))
          Filter.atTop (𝓝 (fderiv ℝ (θ : ℝ → ℝ) (w z))) :=
        tendsto_const_nhds
      simpa using (hdθ_cont.continuousAt.tendsto.comp hz).sub hconst
    simpa [second, compCLM, ContinuousLinearMap.compL_apply] using
      (compCLM.flip (dw z)).continuous.continuousAt.tendsto.comp hleft
  obtain ⟨hsecond_mem, hsecond_zero⟩ :=
    memLp_and_tendsto_zero_of_ae_tendsto_of_norm_le_mul
      hdw_mem hsecond_meas hsecond_bound hsecond_ae
  let total : ℕ → ℂ → ℂ →L[ℝ] ℝ := fun n z ↦
    (fderiv ℝ (θ : ℝ → ℝ) (hgraph.approximants (ns n) z)).comp
        (fderiv ℝ (hgraph.approximants (ns n)) z) - dw z
  have htotal_eq : ∀ n, total n =ᵐ[μQ] first n + second n := by
    intro n
    filter_upwards [hθ_deriv] with z hz
    dsimp [total, first, second]
    rw [hz]
    ext v
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, map_sub]
    ring
  have htotal_mem : ∀ n, MemLp (total n) 2 μQ := by
    intro n
    exact (memLp_congr_ae (htotal_eq n)).mpr
      ((hfirst_mem n).add (hsecond_mem n))
  have htotal_zero : Filter.Tendsto
      (fun n ↦ eLpNorm (total n) 2 μQ) Filter.atTop (𝓝 0) := by
    have hupper : Filter.Tendsto
        (fun n ↦ eLpNorm (first n) 2 μQ + eLpNorm (second n) 2 μQ)
        Filter.atTop (𝓝 0) := by
      simpa using hfirst_zero.add hsecond_zero
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      hupper (fun _ ↦ zero_le) (fun n ↦ ?_)
    calc
      eLpNorm (total n) 2 μQ =
          eLpNorm (first n + second n) 2 μQ :=
        eLpNorm_congr_ae (htotal_eq n)
      _ ≤ eLpNorm (first n) 2 μQ + eLpNorm (second n) 2 μQ :=
        eLpNorm_add_le (μ := μQ) (p := (2 : ℝ≥0∞))
          (f := first n) (g := second n)
          (hfirst_mem n).aestronglyMeasurable
          (hsecond_mem n).aestronglyMeasurable (by norm_num)
  refine ⟨ns, hns, ?_, ?_, ?_⟩
  · simpa [μQ] using hθvalue_ae
  · simpa [total, μQ] using htotal_mem
  · simpa [total, μQ] using htotal_zero

/--
%%handwave
name:
  Strong convergence of smooth outer differentials along graph approximants
statement:
  Suppose smooth maps $T_n:\mathbb C\to\mathbb C$ converge to $f$ in
  $L^2(Q)$. If $u:\mathbb C\to\mathbb R$ is smooth and compactly supported,
  then
  $$
    Du(T_n)-Du(f)\longrightarrow0\quad\text{in }L^2(Q).
  $$
proof:
  By [the differential of a smooth compactly supported function is globally Lipschitz](lean:JJMath.Quasiconformal.smoothCompactlySupported_fderiv_lipschitz). Apply the Lipschitz estimate pointwise and the $L^2$ convergence of $T_n-f$.
-/
theorem PlanarWeakSobolevSmoothApproxGraphL2Data.smoothOuter_fderiv_comp_sub_tendsto_l2
    {Q : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (hgraph : PlanarWeakSobolevSmoothApproxGraphL2Data Q f df)
    (hf_meas : AEStronglyMeasurable f (volume.restrict Q))
    {U : Set ℂ}
    (u : JJMath.Uniformization.SmoothCompactlySupportedManifoldCoordinateFunction U) :
    (∀ n, MemLp
      (fun z ↦ fderiv ℝ (u : ℂ → ℝ) (hgraph.approximants n z) -
        fderiv ℝ (u : ℂ → ℝ) (f z)) 2 (volume.restrict Q)) ∧
      Filter.Tendsto
        (fun n ↦ eLpNorm
          (fun z ↦ fderiv ℝ (u : ℂ → ℝ) (hgraph.approximants n z) -
            fderiv ℝ (u : ℂ → ℝ) (f z)) 2 (volume.restrict Q))
        Filter.atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := smoothCompactlySupported_fderiv_lipschitz u
  exact lipschitz_comp_sub_memLp_and_tendsto_zero hC
    (fun n ↦ (hgraph.smooth n).continuous.aestronglyMeasurable)
    hf_meas hgraph.value_error_memLp hgraph.value_tendsto_l2

/--
%%handwave
name:
  Vanishing of bounded bilinear $L^2$ pairings
statement:
  Let $A_n\to0$ strongly in $L^2(X,E)$ and let $B_n$ be bounded in
  $L^2(X,F)$. If a bilinear operation $\beta:E\times F\to G$ satisfies
  $\lVert\beta(a,b)\rVert\leq c\lVert a\rVert\lVert b\rVert$, then
  $$
    \int_X\beta(A_n(x),B_n(x))\,dx\longrightarrow0.
  $$
proof:
  Hölder's inequality bounds the $L^1$ norm of the bilinear product by
  $c\lVert A_n\rVert_2\lVert B_n\rVert_2$. The first factor tends to zero
  and the second is uniformly bounded, so continuity of the Bochner integral
  in $L^1$ gives the conclusion.
-/
theorem integral_bilinear_tendsto_zero_of_L2_tendsto_zero_of_L2_bounded
    {α E F G : Type} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {μ : Measure α} {A : ℕ → α → E} {B : ℕ → α → F}
    (β : E → F → G) (c : NNReal)
    (hA : ∀ n, MemLp (A n) 2 μ) (hB : ∀ n, MemLp (B n) 2 μ)
    (hβ_meas : ∀ n,
      AEStronglyMeasurable (fun x ↦ β (A n x) (B n x)) μ)
    (hβ_bound : ∀ n, ∀ᵐ x ∂μ,
      ‖β (A n x) (B n x)‖₊ ≤ c * ‖A n x‖₊ * ‖B n x‖₊)
    (hA_zero : Filter.Tendsto (fun n ↦ eLpNorm (A n) 2 μ)
      Filter.atTop (𝓝 0))
    (hB_bounded : ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ n, eLpNorm (B n) 2 μ ≤ C) :
    (∀ n, Integrable (fun x ↦ β (A n x) (B n x)) μ) ∧
      Filter.Tendsto (fun n ↦ ∫ x, β (A n x) (B n x) ∂μ)
        Filter.atTop (𝓝 0) := by
  obtain ⟨C, hCtop, hC⟩ := hB_bounded
  have hprod_mem : ∀ n,
      MemLp (fun x ↦ β (A n x) (B n x)) 1 μ := by
    intro n
    exact MemLp.of_bilin β c (hA n) (hB n) (hβ_meas n) (hβ_bound n)
  have hprod_norm : ∀ n,
      eLpNorm (fun x ↦ β (A n x) (B n x)) 1 μ ≤
        (c : ℝ≥0∞) * eLpNorm (A n) 2 μ * eLpNorm (B n) 2 μ := by
    intro n
    exact eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
      (hA n).aestronglyMeasurable (hB n).aestronglyMeasurable β c
      (hβ_bound n)
  have hupper : Filter.Tendsto
      (fun n ↦ (c : ℝ≥0∞) * eLpNorm (A n) 2 μ * C)
      Filter.atTop (𝓝 0) := by
    have hleft := ENNReal.Tendsto.const_mul hA_zero
      (Or.inr (ENNReal.coe_ne_top : (c : ℝ≥0∞) ≠ ∞))
    simpa using ENNReal.Tendsto.mul_const hleft (Or.inr hCtop)
  have hprod_zero : Filter.Tendsto
      (fun n ↦ eLpNorm (fun x ↦ β (A n x) (B n x)) 1 μ)
      Filter.atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
      (fun _ ↦ zero_le)
      (fun n ↦ (hprod_norm n).trans (by
        gcongr
        exact hC n))
  have hprod_int : ∀ n,
      Integrable (fun x ↦ β (A n x) (B n x)) μ := fun n ↦
    memLp_one_iff_integrable.mp (hprod_mem n)
  have ht := tendsto_integral_of_L1' (μ := μ)
    (F := fun n x ↦ β (A n x) (B n x)) (l := Filter.atTop)
    (f := fun _ : α ↦ (0 : G)) aestronglyMeasurable_zero
    (Filter.Eventually.of_forall hprod_int)
    (by
      convert hprod_zero using 1
      funext n
      congr 1
      funext x
      simp)
  exact ⟨hprod_int, by simpa using ht⟩

/--
%%handwave
name:
  Smooth outer chain-rule pairings along planar graph approximants
statement:
  Let smooth maps $T_n$ converge to $f$ and $DT_n$ converge to $Df$ in
  $L^2(Q)$, where $Q\subseteq\mathbb C$ is compact. For smooth compactly
  supported real functions $u$ and $\varphi$, and every $v\in\mathbb C$,
  $$
    \int_Q \varphi,Du(T_n)[DT_n(v)]
      \longrightarrow
    \int_Q \varphi,Du(f)[Df(v)].
  $$
  The limiting integrand is integrable.
proof:
  Split the difference into
  $(Du(T_n)-Du(f))[Df(v)]$ and
  $Du(T_n)[(DT_n-Df)(v)]$. The first factor in each term converges strongly
  in $L^2$, while the other is $L^2$-bounded; apply [vanishing of bounded bilinear $L^2$ pairings](lean:JJMath.Quasiconformal.integral_bilinear_tendsto_zero_of_L2_tendsto_zero_of_L2_bounded).
-/
theorem PlanarWeakSobolevSmoothApproxGraphL2Data.smoothOuter_chain_integral_tendsto
    {Q : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (hgraph : PlanarWeakSobolevSmoothApproxGraphL2Data Q f df)
    (hQ : IsCompact Q)
    (hf_meas : AEStronglyMeasurable f (volume.restrict Q))
    (hdf_mem : MemLp df 2 (volume.restrict Q))
    {U V : Set ℂ}
    (u : JJMath.Uniformization.SmoothCompactlySupportedManifoldCoordinateFunction U)
    (φ : JJMath.Uniformization.SmoothCompactlySupportedManifoldCoordinateFunction V)
    (v : ℂ) :
    Integrable
        (fun z ↦ φ z •
          ((fderiv ℝ (u : ℂ → ℝ) (f z)).comp (df z)) v)
        (volume.restrict Q) ∧
      Filter.Tendsto
        (fun n ↦ ∫ z,
          φ z •
            ((fderiv ℝ (u : ℂ → ℝ) (hgraph.approximants n z)).comp
              (fderiv ℝ (hgraph.approximants n) z)) v
          ∂volume.restrict Q)
        Filter.atTop
        (𝓝 (∫ z,
          φ z • ((fderiv ℝ (u : ℂ → ℝ) (f z)).comp (df z)) v
          ∂volume.restrict Q)) := by
  let μQ : Measure ℂ := volume.restrict Q
  haveI : IsFiniteMeasure μQ :=
    isFiniteMeasure_restrict.2 hQ.measure_ne_top
  obtain ⟨Mu, hMu_nonneg, hMu⟩ :=
    smoothCompactlySupported_exists_forall_fderiv_norm_le u
  obtain ⟨Mφ, hMφ_nonneg, hMφ⟩ :=
    smoothCompactlySupported_exists_forall_norm_le φ
  have hdu_cont : Continuous (fderiv ℝ (u : ℂ → ℝ)) :=
    u.smooth.continuous_fderiv (by simp)
  have hduf_meas : AEStronglyMeasurable
      (fun z ↦ fderiv ℝ (u : ℂ → ℝ) (f z)) μQ :=
    hdu_cont.comp_aestronglyMeasurable hf_meas
  let compCLM :
      (ℂ →L[ℝ] ℝ) →L[ℝ] (ℂ →L[ℝ] ℂ) →L[ℝ] (ℂ →L[ℝ] ℝ) :=
    (isBoundedBilinearMap_comp
      (𝕜 := ℝ) (E := ℂ) (F := ℂ) (G := ℝ)).toContinuousLinearMap
  have hcand_field_meas : AEStronglyMeasurable
      (fun z ↦ (fderiv ℝ (u : ℂ → ℝ) (f z)).comp (df z)) μQ := by
    simpa [compCLM] using compCLM.aestronglyMeasurable_comp₂
      hduf_meas hdf_mem.aestronglyMeasurable
  have hcand_eval_meas : AEStronglyMeasurable
      (fun z ↦ ((fderiv ℝ (u : ℂ → ℝ) (f z)).comp (df z)) v) μQ :=
    ((ContinuousLinearMap.apply ℝ ℝ) v).continuous.comp_aestronglyMeasurable
      hcand_field_meas
  have hcand_meas : AEStronglyMeasurable
      (fun z ↦ φ z •
        ((fderiv ℝ (u : ℂ → ℝ) (f z)).comp (df z)) v) μQ :=
    φ.smooth.continuous.aestronglyMeasurable.smul hcand_eval_meas
  have hcand_bound : ∀ᵐ z ∂μQ,
      ‖φ z • ((fderiv ℝ (u : ℂ → ℝ) (f z)).comp (df z)) v‖ ≤
        (Mφ * Mu * ‖v‖) * ‖df z‖ := by
    filter_upwards with z
    calc
      ‖φ z • ((fderiv ℝ (u : ℂ → ℝ) (f z)).comp (df z)) v‖ =
          ‖φ z‖ *
            ‖fderiv ℝ (u : ℂ → ℝ) (f z) (df z v)‖ := by
        simp [ContinuousLinearMap.comp_apply]
      _ ≤ Mφ *
          (‖fderiv ℝ (u : ℂ → ℝ) (f z)‖ * ‖df z v‖) := by
        gcongr
        · exact hMφ z
        · exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ Mφ * (Mu * ‖df z v‖) := by
        gcongr
        exact hMu (f z)
      _ ≤ Mφ * (Mu * (‖df z‖ * ‖v‖)) := by
        gcongr
        exact ContinuousLinearMap.le_opNorm _ _
      _ = (Mφ * Mu * ‖v‖) * ‖df z‖ := by ring
  have hcand_mem : MemLp
      (fun z ↦ φ z •
        ((fderiv ℝ (u : ℂ → ℝ) (f z)).comp (df z)) v) 2 μQ :=
    hdf_mem.of_le_mul hcand_meas hcand_bound
  have hcand_int : Integrable
      (fun z ↦ φ z •
        ((fderiv ℝ (u : ℂ → ℝ) (f z)).comp (df z)) v) μQ :=
    hcand_mem.integrable (by norm_num)
  obtain ⟨hdu_error_mem, hdu_error_zero⟩ :=
    hgraph.smoothOuter_fderiv_comp_sub_tendsto_l2 hf_meas u
  let dErr : ℕ → ℂ → ℂ := fun n z ↦
    (fderiv ℝ (hgraph.approximants n) z - df z) v
  have hdErr_meas : ∀ n, AEStronglyMeasurable (dErr n) μQ := by
    intro n
    exact ((ContinuousLinearMap.apply ℝ ℂ) v).continuous.comp_aestronglyMeasurable
      (hgraph.derivative_error_memLp n).aestronglyMeasurable
  have hdErr_bound : ∀ n, ∀ᵐ z ∂μQ,
      ‖dErr n z‖ ≤ ‖v‖ *
        ‖fderiv ℝ (hgraph.approximants n) z - df z‖ := by
    intro n
    filter_upwards with z
    simpa [dErr, mul_comm] using
      ContinuousLinearMap.le_opNorm
        (fderiv ℝ (hgraph.approximants n) z - df z) v
  obtain ⟨hdErr_mem, hdErr_zero⟩ :=
    memLp_and_tendsto_zero_of_norm_le_mul
      hgraph.derivative_error_memLp hdErr_meas hdErr_bound
      hgraph.derivative_tendsto_l2
  let b₁ : ℂ → ℂ := fun z ↦ φ z • df z v
  have hdfv_mem : MemLp (fun z ↦ df z v) 2 μQ :=
    ((ContinuousLinearMap.apply ℝ ℂ) v).comp_memLp' hdf_mem
  have hb₁_meas : AEStronglyMeasurable b₁ μQ :=
    φ.smooth.continuous.aestronglyMeasurable.smul
      hdfv_mem.aestronglyMeasurable
  have hb₁_bound : ∀ᵐ z ∂μQ,
      ‖b₁ z‖ ≤ (Mφ * ‖v‖) * ‖df z‖ := by
    filter_upwards with z
    calc
      ‖b₁ z‖ = ‖φ z‖ * ‖df z v‖ := by simp [b₁]
      _ ≤ Mφ * (‖df z‖ * ‖v‖) := by
        gcongr
        · exact hMφ z
        · exact ContinuousLinearMap.le_opNorm _ _
      _ = (Mφ * ‖v‖) * ‖df z‖ := by ring
  have hb₁_mem : MemLp b₁ 2 μQ :=
    hdf_mem.of_le_mul hb₁_meas hb₁_bound
  let B₁ : ℕ → ℂ → ℂ := fun _ ↦ b₁
  let duErr : ℕ → ℂ → ℂ →L[ℝ] ℝ := fun n z ↦
    fderiv ℝ (u : ℂ → ℝ) (hgraph.approximants n z) -
      fderiv ℝ (u : ℂ → ℝ) (f z)
  let evalCLM : (ℂ →L[ℝ] ℝ) →L[ℝ] ℂ →L[ℝ] ℝ :=
    (isBoundedBilinearMap_apply
      (𝕜 := ℝ) (E := ℂ) (F := ℝ)).toContinuousLinearMap
  have hterm₁_meas : ∀ n, AEStronglyMeasurable
      (fun z ↦ duErr n z (B₁ n z)) μQ := by
    intro n
    exact evalCLM.aestronglyMeasurable_comp₂
      (by simpa [duErr] using (hdu_error_mem n).aestronglyMeasurable)
      (by simpa [B₁] using hb₁_meas)
  have heval_bound (A : ℂ →L[ℝ] ℝ) (w : ℂ) :
      ‖A w‖₊ ≤ (1 : NNReal) * ‖A‖₊ * ‖w‖₊ := by
    apply NNReal.coe_le_coe.mp
    simpa using ContinuousLinearMap.le_opNorm A w
  obtain ⟨hterm₁_int, hterm₁_zero⟩ :=
    integral_bilinear_tendsto_zero_of_L2_tendsto_zero_of_L2_bounded
      (fun (A : ℂ →L[ℝ] ℝ) (w : ℂ) ↦ A w) 1
      (fun n ↦ by simpa [duErr] using hdu_error_mem n)
      (fun n ↦ by simpa [B₁] using hb₁_mem)
      hterm₁_meas (fun n ↦ Filter.Eventually.of_forall fun z ↦
        heval_bound (duErr n z) (B₁ n z))
      (by simpa [duErr] using hdu_error_zero)
      ⟨eLpNorm b₁ 2 μQ, hb₁_mem.eLpNorm_lt_top.ne,
        fun n ↦ by rfl⟩
  let b₂ : ℕ → ℂ → ℂ →L[ℝ] ℝ := fun n z ↦
    φ z • fderiv ℝ (u : ℂ → ℝ) (hgraph.approximants n z)
  have hb₂_meas : ∀ n, AEStronglyMeasurable (b₂ n) μQ := by
    intro n
    exact φ.smooth.continuous.aestronglyMeasurable.smul
      (hdu_cont.comp
        (hgraph.smooth n).continuous).aestronglyMeasurable
  have hb₂_bound : ∀ n, ∀ᵐ z ∂μQ,
      ‖b₂ n z‖ ≤ Mu * ‖φ z‖ := by
    intro n
    filter_upwards with z
    calc
      ‖b₂ n z‖ = ‖φ z‖ *
          ‖fderiv ℝ (u : ℂ → ℝ) (hgraph.approximants n z)‖ := by
        rw [norm_smul]
      _ ≤ ‖φ z‖ * Mu :=
        mul_le_mul_of_nonneg_left (hMu _) (norm_nonneg _)
      _ = Mu * ‖φ z‖ := mul_comm _ _
  have hφ_mem : MemLp (φ : ℂ → ℝ) 2 μQ := by
    simpa [μQ] using
      memLp_restrict_of_isCompact_of_continuousOn hQ
        φ.smooth.continuous.continuousOn
  have hb₂_mem : ∀ n, MemLp (b₂ n) 2 μQ := fun n ↦
    hφ_mem.of_le_mul (hb₂_meas n) (hb₂_bound n)
  have hb₂_norm_bound : ∀ n,
      eLpNorm (b₂ n) 2 μQ ≤ ENNReal.ofReal Mu * eLpNorm φ 2 μQ :=
    fun n ↦ eLpNorm_le_mul_eLpNorm_of_ae_le_mul (hb₂_bound n) 2
  have hterm₂_meas : ∀ n, AEStronglyMeasurable
      (fun z ↦ b₂ n z (dErr n z)) μQ := by
    intro n
    exact evalCLM.flip.aestronglyMeasurable_comp₂
      (hdErr_meas n) (hb₂_meas n)
  obtain ⟨hterm₂_int, hterm₂_zero⟩ :=
    integral_bilinear_tendsto_zero_of_L2_tendsto_zero_of_L2_bounded
      (fun (w : ℂ) (A : ℂ →L[ℝ] ℝ) ↦ A w) 1
      hdErr_mem hb₂_mem hterm₂_meas
      (fun n ↦ Filter.Eventually.of_forall fun z ↦
        by simpa [mul_comm] using heval_bound (b₂ n z) (dErr n z))
      hdErr_zero
      ⟨ENNReal.ofReal Mu * eLpNorm φ 2 μQ,
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top hφ_mem.eLpNorm_lt_top.ne,
        hb₂_norm_bound⟩
  have hsplit (n : ℕ) (z : ℂ) :
      φ z •
          (((fderiv ℝ (u : ℂ → ℝ) (hgraph.approximants n z)).comp
              (fderiv ℝ (hgraph.approximants n) z)) v -
            ((fderiv ℝ (u : ℂ → ℝ) (f z)).comp (df z)) v) =
        duErr n z (B₁ n z) + b₂ n z (dErr n z) := by
    simp only [ContinuousLinearMap.comp_apply, duErr, B₁, b₁, b₂, dErr,
      map_smul, smul_eq_mul]
    simp
    ring
  have hdiff_zero : Filter.Tendsto
      (fun n ↦ ∫ z,
        φ z •
          (((fderiv ℝ (u : ℂ → ℝ) (hgraph.approximants n z)).comp
              (fderiv ℝ (hgraph.approximants n) z)) v -
            ((fderiv ℝ (u : ℂ → ℝ) (f z)).comp (df z)) v)
        ∂μQ) Filter.atTop (𝓝 0) := by
    have hadd := hterm₁_zero.add hterm₂_zero
    convert hadd using 1
    · funext n
      rw [← integral_add (hterm₁_int n) (hterm₂_int n)]
      apply integral_congr_ae
      filter_upwards with z
      exact hsplit n z
    · simp
  have hseq_int : ∀ n, Integrable
      (fun z ↦ φ z •
        ((fderiv ℝ (u : ℂ → ℝ) (hgraph.approximants n z)).comp
          (fderiv ℝ (hgraph.approximants n) z)) v) μQ := by
    intro n
    have hcont : Continuous
        (fun z ↦ φ z •
          ((fderiv ℝ (u : ℂ → ℝ) (hgraph.approximants n z)).comp
            (fderiv ℝ (hgraph.approximants n) z)) v) := by
      exact φ.smooth.continuous.smul
        ((hdu_cont.comp (hgraph.smooth n).continuous).clm_apply
          (((hgraph.smooth n).continuous_fderiv (by simp)).clm_apply
            continuous_const))
    exact (memLp_restrict_of_isCompact_of_continuousOn hQ hcont.continuousOn).integrable
      (by norm_num)
  have hsub_zero : Filter.Tendsto
      (fun n ↦
        (∫ z, φ z •
          ((fderiv ℝ (u : ℂ → ℝ) (hgraph.approximants n z)).comp
            (fderiv ℝ (hgraph.approximants n) z)) v ∂μQ) -
        ∫ z, φ z •
          ((fderiv ℝ (u : ℂ → ℝ) (f z)).comp (df z)) v ∂μQ)
      Filter.atTop (𝓝 0) := by
    apply hdiff_zero.congr'
    filter_upwards with n
    rw [← integral_sub (hseq_int n) hcand_int]
    apply integral_congr_ae
    filter_upwards with z
    module
  have hfinal := hsub_zero.add_const
    (∫ z, φ z •
      ((fderiv ℝ (u : ℂ → ℝ) (f z)).comp (df z)) v ∂μQ)
  refine ⟨hcand_int, ?_⟩
  simpa using hfinal

/--
%%handwave
name:
  Smooth compactly supported postcomposition preserves local planar Sobolev regularity
statement:
  If $f\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb C)$ has weak differential
  $Df$ and $u:\mathbb C\to\mathbb R$ is smooth and compactly supported,
  then $u\circ f\in W^{1,2}_{\mathrm{loc}}(\Omega)$ and
  $$
    D(u\circ f)(z)=Du(f(z))\circ Df(z)
  $$
  almost everywhere.
proof:
  On the compact support of a test function, approximate $f$ and $Df$
  strongly in $L^2$ by a common sequence of smooth maps. Apply the classical
  smooth chain rule and integration by parts to every approximant. The value
  side converges by the Lipschitz continuity of $u$, while the differential
  side converges by [the smooth-outer chain-rule pairing theorem](lean:JJMath.Quasiconformal.PlanarWeakSobolevSmoothApproxGraphL2Data.smoothOuter_chain_integral_tendsto). Global bounds for $u$ and $Du$ give the required local $L^2$ estimates.
-/
theorem IsLocalW12On.postcomp_smoothCompactlySupported
    {Ω : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (hf : IsLocalW12On Ω f df) {U : Set ℂ}
    (u : JJMath.Uniformization.SmoothCompactlySupportedManifoldCoordinateFunction U) :
    IsLocalW12RealOn Ω (fun z ↦ u (f z))
      (fun z ↦ (fderiv ℝ (u : ℂ → ℝ) (f z)).comp (df z)) := by
  classical
  obtain ⟨Mu, hMu_nonneg, hMu⟩ :=
    smoothCompactlySupported_exists_forall_norm_le u
  obtain ⟨Mdu, hMdu_nonneg, hMdu⟩ :=
    smoothCompactlySupported_exists_forall_fderiv_norm_le u
  have hdu_cont : Continuous (fderiv ℝ (u : ℂ → ℝ)) :=
    u.smooth.continuous_fderiv (by simp)
  let compCLM :
      (ℂ →L[ℝ] ℝ) →L[ℝ] (ℂ →L[ℝ] ℂ) →L[ℝ] (ℂ →L[ℝ] ℝ) :=
    (isBoundedBilinearMap_comp
      (𝕜 := ℝ) (E := ℂ) (F := ℂ) (G := ℝ)).toContinuousLinearMap
  have hlocal : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      MemLp (fun z ↦ u (f z)) 2 (volume.restrict K) ∧
        MemLp (fun z ↦ (fderiv ℝ (u : ℂ → ℝ) (f z)).comp (df z)) 2
          (volume.restrict K) := by
    intro K hK hKΩ
    let μK : Measure ℂ := volume.restrict K
    haveI : IsFiniteMeasure μK :=
      isFiniteMeasure_restrict.2 hK.measure_ne_top
    have hfK := hf.2.2 K hK hKΩ
    have huf_meas : AEStronglyMeasurable (fun z ↦ u (f z)) μK :=
      u.smooth.continuous.comp_aestronglyMeasurable
        hfK.1.aestronglyMeasurable
    have huf_mem : MemLp (fun z ↦ u (f z)) 2 μK :=
      MemLp.of_bound huf_meas Mu
        (Filter.Eventually.of_forall fun z ↦ hMu (f z))
    have hduf_meas : AEStronglyMeasurable
        (fun z ↦ fderiv ℝ (u : ℂ → ℝ) (f z)) μK :=
      hdu_cont.comp_aestronglyMeasurable hfK.1.aestronglyMeasurable
    have hcand_meas : AEStronglyMeasurable
        (fun z ↦ (fderiv ℝ (u : ℂ → ℝ) (f z)).comp (df z)) μK := by
      simpa [compCLM] using compCLM.aestronglyMeasurable_comp₂
        hduf_meas hfK.2.aestronglyMeasurable
    have hcand_bound : ∀ᵐ z ∂μK,
        ‖(fderiv ℝ (u : ℂ → ℝ) (f z)).comp (df z)‖ ≤
          Mdu * ‖df z‖ := by
      filter_upwards with z
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right (hMdu (f z)) (norm_nonneg _))
    exact ⟨huf_mem, hfK.2.of_le_mul hcand_meas hcand_bound⟩
  refine ⟨hf.1, ?_, hlocal⟩
  intro φ v
  let Q : Set ℂ := tsupport (φ : ℂ → ℝ)
  have hQ : IsCompact Q := φ.compact_support
  have hQΩ : Q ⊆ Ω := φ.support_subset
  haveI : IsFiniteMeasure (volume.restrict Q) :=
    isFiniteMeasure_restrict.2 hQ.measure_ne_top
  obtain ⟨δ, hδ, hδΩ⟩ :=
    hQ.exists_cthickening_subset_open hf.1 hQΩ
  let P : Set ℂ := Metric.cthickening δ Q
  have hP : IsCompact P := hQ.cthickening
  have hQP : ∃ ε : ℝ, 0 < ε ∧ Metric.cthickening ε Q ⊆ P :=
    ⟨δ, hδ, by rfl⟩
  have hPΩ : P ⊆ Ω := hδΩ
  rcases hf.exists_smoothApproxGraphL2Data_on_compact hQ hP hQP hPΩ with
    ⟨hgraph⟩
  have hfQ := (hf.2.2 Q hQ hQΩ).1
  have hdfQ := (hf.2.2 Q hQ hQΩ).2
  obtain ⟨hrightQ, hright_tendsto⟩ :=
    hgraph.smoothOuter_chain_integral_tendsto hQ
      hfQ.aestronglyMeasurable hdfQ u φ v
  obtain ⟨hvalue_error_mem, hvalue_error_zero⟩ :=
    hgraph.testFunction_comp_sub_tendsto_l2
      hfQ.aestronglyMeasurable u
  let a : ℂ → ℝ := fun z ↦ fderiv ℝ (φ : ℂ → ℝ) z v
  have ha_cont : Continuous a :=
    (φ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have ha_mem : MemLp a 2 (volume.restrict Q) :=
    memLp_restrict_of_isCompact_of_continuousOn hQ ha_cont.continuousOn
  let A : ℕ → ℂ → ℝ := fun _ ↦ a
  let valueError : ℕ → ℂ → ℝ := fun n z ↦
    u (hgraph.approximants n z) - u (f z)
  have hleft_error_zero : Filter.Tendsto
      (fun n ↦ ∫ z, A n z • valueError n z ∂volume.restrict Q)
      Filter.atTop (𝓝 0) := by
    apply integral_smul_tendsto_zero_of_L2_bounded_of_L2_tendsto_zero
    · exact fun n ↦ by simpa [A] using ha_mem
    · exact fun n ↦ by simpa [valueError] using hvalue_error_mem n
    · exact ⟨eLpNorm a 2 (volume.restrict Q), ha_mem.eLpNorm_lt_top.ne,
        fun n ↦ by rfl⟩
    · simpa [valueError] using hvalue_error_zero
  have hufQ := (hlocal Q hQ hQΩ).1
  have hleftQ : Integrable
      (fun z ↦ a z • u (f z)) (volume.restrict Q) := by
    apply memLp_one_iff_integrable.mp
    exact hufQ.smul ha_mem
  have hleftSeqQ : ∀ n, Integrable
      (fun z ↦ a z • u (hgraph.approximants n z))
      (volume.restrict Q) := by
    intro n
    have hcont : Continuous
        (fun z ↦ a z • u (hgraph.approximants n z)) :=
      ha_cont.smul (u.smooth.continuous.comp (hgraph.smooth n).continuous)
    exact (memLp_restrict_of_isCompact_of_continuousOn hQ hcont.continuousOn).integrable
      (by norm_num)
  have hleft_sub_zero : Filter.Tendsto
      (fun n ↦
        (∫ z, a z • u (hgraph.approximants n z) ∂volume.restrict Q) -
          ∫ z, a z • u (f z) ∂volume.restrict Q)
      Filter.atTop (𝓝 0) := by
    apply hleft_error_zero.congr'
    filter_upwards with n
    rw [← integral_sub (hleftSeqQ n) hleftQ]
    apply integral_congr_ae
    filter_upwards with z
    simp only [A, valueError]
    module
  have hleft_tendsto : Filter.Tendsto
      (fun n ↦ ∫ z, a z • u (hgraph.approximants n z)
        ∂volume.restrict Q)
      Filter.atTop
      (𝓝 (∫ z, a z • u (f z) ∂volume.restrict Q)) := by
    simpa using hleft_sub_zero.add_const
      (∫ z, a z • u (f z) ∂volume.restrict Q)
  let leftSeq : ℕ → ℝ := fun n ↦
    ∫ z, a z • u (hgraph.approximants n z) ∂volume.restrict Q
  let rightSeq : ℕ → ℝ := fun n ↦
    ∫ z, φ z •
      ((fderiv ℝ (u : ℂ → ℝ) (hgraph.approximants n z)).comp
        (fderiv ℝ (hgraph.approximants n) z)) v ∂volume.restrict Q
  have hsmooth_eq : ∀ n, leftSeq n = -rightSeq n := by
    intro n
    have hsmooth :=
      JJMath.Uniformization.contDiff_smooth_outer_pullback_test_integral_eq
        hf.1 (hgraph.smooth n) u.smooth φ v
    have hleft_domain :
        (∫ z in Ω, (fderiv ℝ (φ : ℂ → ℝ) z v) •
            u (hgraph.approximants n z) ∂volume) = leftSeq n := by
      change (∫ z in Ω, a z • u (hgraph.approximants n z) ∂volume) = _
      exact setIntegral_eq_of_subset_of_forall_diff_eq_zero
        hf.1.measurableSet hQΩ (by
          intro z hz
          have hdz : fderiv ℝ (φ : ℂ → ℝ) z = 0 :=
            fderiv_of_notMem_tsupport (𝕜 := ℝ)
              (f := (φ : ℂ → ℝ)) hz.2
          simp [a, hdz])
    have hright_domain :
        (∫ z in Ω, φ z •
          ((fderiv ℝ (u : ℂ → ℝ) (hgraph.approximants n z)).comp
            (fderiv ℝ (hgraph.approximants n) z)) v ∂volume) =
          rightSeq n := by
      exact setIntegral_eq_of_subset_of_forall_diff_eq_zero
        hf.1.measurableSet hQΩ (by
          intro z hz
          have hφz : φ z = 0 := image_eq_zero_of_notMem_tsupport hz.2
          simp [hφz])
    rw [hleft_domain, hright_domain] at hsmooth
    exact hsmooth
  have hleft_tendsto' : Filter.Tendsto leftSeq Filter.atTop
      (𝓝 (∫ z, a z • u (f z) ∂volume.restrict Q)) := by
    simpa [leftSeq] using hleft_tendsto
  have hright_tendsto' : Filter.Tendsto rightSeq Filter.atTop
      (𝓝 (∫ z, φ z •
        ((fderiv ℝ (u : ℂ → ℝ) (f z)).comp (df z)) v
        ∂volume.restrict Q)) := by
    simpa [rightSeq] using hright_tendsto
  have hneg_right_tendsto_left : Filter.Tendsto
      (fun n ↦ -rightSeq n) Filter.atTop
      (𝓝 (∫ z, a z • u (f z) ∂volume.restrict Q)) := by
    apply hleft_tendsto'.congr'
    filter_upwards with n
    exact hsmooth_eq n
  have hQidentity :
      (∫ z, a z • u (f z) ∂volume.restrict Q) =
        -∫ z, φ z •
          ((fderiv ℝ (u : ℂ → ℝ) (f z)).comp (df z)) v
          ∂volume.restrict Q :=
    tendsto_nhds_unique hneg_right_tendsto_left hright_tendsto'.neg
  have hleft_support : Function.support (fun z ↦ a z • u (f z)) ⊆ Q := by
    intro z hz
    exact (tsupport_fderiv_apply_subset (𝕜 := ℝ)
      (f := (φ : ℂ → ℝ)) v)
        (subset_tsupport a
          (Function.support_smul_subset_left a (fun z ↦ u (f z)) hz))
  have hright_support : Function.support
      (fun z ↦ φ z •
        ((fderiv ℝ (u : ℂ → ℝ) (f z)).comp (df z)) v) ⊆ Q := by
    intro z hz
    exact subset_tsupport (φ : ℂ → ℝ)
      (Function.support_smul_subset_left (φ : ℂ → ℝ)
        (fun z ↦ ((fderiv ℝ (u : ℂ → ℝ) (f z)).comp (df z)) v) hz)
  have hleft_global : Integrable (fun z ↦ a z • u (f z)) volume :=
    (integrableOn_iff_integrable_of_support_subset hleft_support).mp hleftQ
  have hright_global : Integrable
      (fun z ↦ φ z •
        ((fderiv ℝ (u : ℂ → ℝ) (f z)).comp (df z)) v) volume :=
    (integrableOn_iff_integrable_of_support_subset hright_support).mp hrightQ
  have hleftΩ := hleft_global.mono_measure
    (Measure.restrict_le_self (μ := volume) (s := Ω))
  have hrightΩ := hright_global.mono_measure
    (Measure.restrict_le_self (μ := volume) (s := Ω))
  refine ⟨?_, hrightΩ, ?_⟩
  · simpa [a] using hleftΩ
  have hleft_domain :
      (∫ z in Ω, a z • u (f z) ∂volume) =
        ∫ z, a z • u (f z) ∂volume.restrict Q :=
    setIntegral_eq_of_subset_of_forall_diff_eq_zero
      hf.1.measurableSet hQΩ (by
        intro z hz
        have hdz : fderiv ℝ (φ : ℂ → ℝ) z = 0 :=
          fderiv_of_notMem_tsupport (𝕜 := ℝ)
            (f := (φ : ℂ → ℝ)) hz.2
        simp [a, hdz])
  have hright_domain :
      (∫ z in Ω, φ z •
        ((fderiv ℝ (u : ℂ → ℝ) (f z)).comp (df z)) v ∂volume) =
        ∫ z, φ z •
          ((fderiv ℝ (u : ℂ → ℝ) (f z)).comp (df z)) v
          ∂volume.restrict Q :=
    setIntegral_eq_of_subset_of_forall_diff_eq_zero
      hf.1.measurableSet hQΩ (by
        intro z hz
        have hφz : φ z = 0 := image_eq_zero_of_notMem_tsupport hz.2
        simp [hφz])
  rw [hleft_domain, hright_domain]
  simpa [a] using hQidentity

/--
%%handwave
name:
  Compact-local $L^2$ bounds for a continuous Sobolev pullback
statement:
  Let $F:\Omega\to\Omega'$ be quasiconformal with weak differential $Df$,
  and let $u\in W^{1,2}_{\mathrm{loc}}(\Omega',\mathbb R)$ be continuous
  with weak differential $Du$. For every compact $C\subseteq\Omega$,
  both $u\circ F$ and
  $$
    (Du\circ F)\circ Df
  $$
  belong to $L^2(C)$.
proof:
  Continuity bounds $u\circ F$ on $C$. The image $F(C)$ is compact in
  $\Omega'$, so $Du\in L^2(F(C))$. Apply local quasiconformal covector
  pullback control with the indicator of $F(C)$ and then restrict the source
  field to $C$.
-/
theorem IsKQuasiconformalBetween.postcomp_continuous_local_memLp
    {K : ℝ} {Ω Ω' : Set ℂ} {F : Ω ≃ₜ Ω'}
    (hF : IsKQuasiconformalBetween K F)
    {df : ℂ → ℂ →L[ℝ] ℂ}
    (hdf : IsLocalW12On Ω (ambientMap F) df)
    {u : ℂ → ℝ} {du : ℂ → ℂ →L[ℝ] ℝ}
    (hu : IsLocalW12RealOn Ω' u du)
    (hu_cont : ContinuousOn u Ω') :
    ∀ C : Set ℂ, IsCompact C → C ⊆ Ω →
      MemLp (fun z ↦ u (ambientMap F z)) 2 (volume.restrict C) ∧
        MemLp (fun z ↦ (du (ambientMap F z)).comp (df z))
          2 (volume.restrict C) := by
  intro C hC hCΩ
  have hmaps : MapsTo (ambientMap F) C Ω' := by
    intro z hz
    let zΩ : Ω := ⟨z, hCΩ hz⟩
    rw [ambientMap_apply F zΩ]
    exact (F zΩ).2
  have huF_cont : ContinuousOn (fun z ↦ u (ambientMap F z)) C :=
    hu_cont.comp ((continuousOn_ambientMap F).mono hCΩ) hmaps
  have huF_mem : MemLp (fun z ↦ u (ambientMap F z)) 2
      (volume.restrict C) :=
    memLp_restrict_of_isCompact_of_continuousOn hC huF_cont
  let L : Set ℂ := ambientMap F '' C
  have hL : IsCompact L := hC.image_of_continuousOn
    ((continuousOn_ambientMap F).mono hCΩ)
  have hLΩ' : L ⊆ Ω' := by
    rintro y ⟨z, hzC, rfl⟩
    let zΩ : Ω := ⟨z, hCΩ hzC⟩
    rw [ambientMap_apply F zΩ]
    exact (F zΩ).2
  have hduL : MemLp du 2 (volume.restrict L) :=
    (hu.2.2 L hL hLΩ').2
  have hpull : MemLp
      (fun z ↦ ((L.indicator du) (ambientMap F z)).comp (df z))
      2 (volume.restrict Ω) :=
    hF.indicator_pullback_memLp hdf hL.measurableSet hLΩ' hduL
  have hpullC := hpull.mono_measure
    (Measure.restrict_mono hCΩ le_rfl)
  have hcand : MemLp (fun z ↦ (du (ambientMap F z)).comp (df z))
      2 (volume.restrict C) := by
    refine (memLp_congr_ae ?_).mpr hpullC
    filter_upwards [ae_restrict_mem hC.measurableSet] with z hzC
    have hFzL : ambientMap F z ∈ L := ⟨z, hzC, rfl⟩
    simp [Set.indicator_of_mem hFzL]
  exact ⟨huF_mem, hcand⟩

set_option maxHeartbeats 2400000 in
/--
%%handwave
name:
  Continuous Sobolev outer chain rule under quasiconformal pullback
statement:
  Let $F:\Omega\to\Omega'$ be $K$-quasiconformal with weak differential
  $Df$. If $u:\Omega'\to\mathbb R$ is continuous and belongs to
  $W^{1,2}_{\mathrm{loc}}(\Omega')$ with weak differential $Du$, then
  $u\circ F\in W^{1,2}_{\mathrm{loc}}(\Omega)$ and
  $$
    D(u\circ F)(z)=Du(F(z))\circ Df(z)
  $$
  almost everywhere.
proof:
  On the image of the compact support of a source test function, choose a
  smooth Sobolev graph approximation and retract its values through a fixed
  bounded smooth scalar function which is the identity on the compact range
  of $u$. Multiply by a target cutoff equal to one on that image. The smooth
  outer chain rule applies to every resulting compactly supported function.
  Lusin $N^{-1}$ and dominated convergence pass the value pairing to the
  limit, while the quasiconformal energy inequality sends the retracted
  target differential error to zero after pullback. Compact-local $L^2$
  bounds follow from the same energy inequality.
-/
theorem IsKQuasiconformalBetween.postcomp_continuous_isLocalW12RealOn
    {K : ℝ} {Ω Ω' : Set ℂ} {F : Ω ≃ₜ Ω'}
    (hF : IsKQuasiconformalBetween K F)
    {df : ℂ → ℂ →L[ℝ] ℂ}
    (hdf : IsLocalW12On Ω (ambientMap F) df)
    {u : ℂ → ℝ} {du : ℂ → ℂ →L[ℝ] ℝ}
    (hu : IsLocalW12RealOn Ω' u du)
    (hu_cont : ContinuousOn u Ω') :
    IsLocalW12RealOn Ω (fun z ↦ u (ambientMap F z))
      (fun z ↦ (du (ambientMap F z)).comp (df z)) := by
  classical
  have hlocal := hF.postcomp_continuous_local_memLp hdf hu hu_cont
  refine ⟨hdf.1, ?_, hlocal⟩
  intro φ v
  let C : Set ℂ := tsupport (φ : ℂ → ℝ)
  have hC : IsCompact C := φ.compact_support
  have hCΩ : C ⊆ Ω := φ.support_subset
  let L : Set ℂ := ambientMap F '' C
  have hL : IsCompact L := hC.image_of_continuousOn
    ((continuousOn_ambientMap F).mono hCΩ)
  have hLΩ' : L ⊆ Ω' := by
    rintro y ⟨z, hzC, rfl⟩
    let zΩ : Ω := ⟨z, hCΩ hzC⟩
    rw [ambientMap_apply F zΩ]
    exact (F zΩ).2
  obtain ⟨δ, hδ, hδΩ'⟩ :=
    hL.exists_cthickening_subset_open hu.1 hLΩ'
  let P : Set ℂ := Metric.cthickening δ L
  have hP : IsCompact P := hL.cthickening
  have hLP : ∃ ε : ℝ, 0 < ε ∧ Metric.cthickening ε L ⊆ P :=
    ⟨δ, hδ, by rfl⟩
  have hPΩ' : P ⊆ Ω' := hδΩ'
  rcases hu.exists_smoothApproxGraphL2Data_on_compact
      hL hP hLP hPΩ' with ⟨hgraph⟩
  have huL := hu.2.2 L hL hLΩ'
  have huL_meas : AEStronglyMeasurable u (volume.restrict L) :=
    huL.1.aestronglyMeasurable
  have hduL : MemLp du 2 (volume.restrict L) := huL.2
  rcases exists_smoothCompactlySupported_fix_continuousOn_compact_range
      hL (hu_cont.mono hLΩ') with ⟨θ, hθ⟩
  have hθ_value : ∀ᵐ y ∂volume.restrict L, θ (u y) = u y :=
    ae_restrict_of_forall_mem hL.measurableSet fun y hy ↦ (hθ y hy).1
  have hθ_deriv : ∀ᵐ y ∂volume.restrict L,
      fderiv ℝ (θ : ℝ → ℝ) (u y) = ContinuousLinearMap.id ℝ ℝ :=
    ae_restrict_of_forall_mem hL.measurableSet fun y hy ↦ (hθ y hy).2
  rcases scalarWeakSobolevSmoothApproxGraphL2Data_exists_retracted_subsequence
      hgraph huL_meas hduL θ hθ_value hθ_deriv with
    ⟨ns, hns, hvalue_ae, herror_mem, herror_zero⟩
  rcases JJMath.Uniformization.exists_scalarWeakSobolevCutoff
      hL hLΩ' hu.1 with ⟨η⟩
  let g : ℕ →
      JJMath.Uniformization.SmoothCompactlySupportedManifoldCoordinateFunction Ω' :=
    fun n ↦
      { toFun := fun y ↦ η y * θ (hgraph.approximants (ns n) y)
        smooth := η.smooth.mul (θ.smooth.comp (hgraph.smooth (ns n)))
        support_subset := (tsupport_mul_subset_left).trans η.support_subset
        compact_support :=
          η.compact_support.of_isClosed_subset (isClosed_tsupport _)
            tsupport_mul_subset_left }
  have hg_value : ∀ n y, y ∈ L →
      g n y = θ (hgraph.approximants (ns n) y) := by
    intro n y hy
    simp [g, η.eq_one_on y hy]
  have hg_deriv : ∀ n y, y ∈ L →
      fderiv ℝ (g n : ℂ → ℝ) y =
        (fderiv ℝ (θ : ℝ → ℝ) (hgraph.approximants (ns n) y)).comp
          (fderiv ℝ (hgraph.approximants (ns n)) y) := by
    intro n y hy
    have hηdiff : DifferentiableAt ℝ (η : ℂ → ℝ) y :=
      η.smooth.differentiable (by simp) y
    have hwdiff : DifferentiableAt ℝ (hgraph.approximants (ns n)) y :=
      (hgraph.smooth (ns n)).differentiable (by simp) y
    have hθdiff : DifferentiableAt ℝ (θ : ℝ → ℝ)
        (hgraph.approximants (ns n) y) :=
      θ.smooth.differentiable (by simp) _
    have hcompdiff : DifferentiableAt ℝ
        (fun x ↦ θ (hgraph.approximants (ns n) x)) y :=
      hθdiff.comp y hwdiff
    have hchain : fderiv ℝ
        (fun x ↦ θ (hgraph.approximants (ns n) x)) y =
          (fderiv ℝ (θ : ℝ → ℝ) (hgraph.approximants (ns n) y)).comp
            (fderiv ℝ (hgraph.approximants (ns n)) y) := by
      simpa [Function.comp_def] using fderiv_comp y hθdiff hwdiff
    change fderiv ℝ
      (fun x ↦ η x * θ (hgraph.approximants (ns n) x)) y = _
    rw [fderiv_fun_mul hηdiff hcompdiff, hchain]
    simp [η.eq_one_on y hy, η.fderiv_eq_zero_on y hy]
  let error : ℕ → ℂ → ℂ →L[ℝ] ℝ := fun n y ↦
    (fderiv ℝ (θ : ℝ → ℝ) (hgraph.approximants (ns n) y)).comp
        (fderiv ℝ (hgraph.approximants (ns n)) y) - du y
  have herror_mem' : ∀ n, MemLp (error n) 2 (volume.restrict L) := by
    simpa [error] using herror_mem
  have herror_zero' : Filter.Tendsto
      (fun n ↦ eLpNorm (error n) 2 (volume.restrict L))
      Filter.atTop (𝓝 0) := by
    simpa [error] using herror_zero
  obtain ⟨hpullError_mem, hpullError_zero⟩ :=
    hF.indicator_pullback_tendsto_l2 hdf hL.measurableSet hLΩ'
      herror_mem' herror_zero'
  let μC : Measure ℂ := volume.restrict C
  haveI : IsFiniteMeasure μC :=
    isFiniteMeasure_restrict.2 hC.measure_ne_top
  have hvalue_target : ∀ᵐ y ∂volume.restrict Ω', y ∈ L →
      Filter.Tendsto (fun n ↦ θ (hgraph.approximants (ns n) y))
        Filter.atTop (𝓝 (u y)) :=
    ae_restrict_of_ae (ae_imp_of_ae_restrict hvalue_ae)
  have hvalue_sourceΩ : ∀ᵐ z ∂volume.restrict Ω,
      ambientMap F z ∈ L →
        Filter.Tendsto
          (fun n ↦ θ (hgraph.approximants (ns n) (ambientMap F z)))
          Filter.atTop (𝓝 (u (ambientMap F z))) :=
    ae_comp_ambientMap_of_hasLusinNInvOn hF.hasLusinNInvOn
      hdf.1.measurableSet hvalue_target
  have hvalue_sourceC : ∀ᵐ z ∂μC,
      ambientMap F z ∈ L →
        Filter.Tendsto
          (fun n ↦ θ (hgraph.approximants (ns n) (ambientMap F z)))
          Filter.atTop (𝓝 (u (ambientMap F z))) :=
    ae_mono (by
      dsimp [μC]
      exact Measure.restrict_mono hCΩ le_rfl) hvalue_sourceΩ
  have hg_value_tendsto : ∀ᵐ z ∂μC,
      Filter.Tendsto (fun n ↦ g n (ambientMap F z))
        Filter.atTop (𝓝 (u (ambientMap F z))) := by
    filter_upwards [ae_restrict_mem hC.measurableSet, hvalue_sourceC]
      with z hzC hz
    have hFzL : ambientMap F z ∈ L := ⟨z, hzC, rfl⟩
    have ht := hz hFzL
    apply ht.congr'
    filter_upwards with n
    exact (hg_value n (ambientMap F z) hFzL).symm
  let a : ℂ → ℝ := fun z ↦ fderiv ℝ (φ : ℂ → ℝ) z v
  have ha_cont : Continuous a :=
    (φ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  rcases hC.exists_bound_of_continuousOn ha_cont.continuousOn with
    ⟨Ma, hMa⟩
  let Ma' : ℝ := max Ma 0
  have hMa' : 0 ≤ Ma' := le_max_right _ _
  obtain ⟨Mη, hMη_nonneg, hMη⟩ :=
    scalarWeakSobolevCutoff_exists_forall_norm_le η
  obtain ⟨Mθ, hMθ_nonneg, hMθ⟩ :=
    smoothCompactlySupported_exists_forall_norm_le θ
  have hF_C_meas : AEStronglyMeasurable (ambientMap F) μC :=
    ((continuousOn_ambientMap F).mono hCΩ).aestronglyMeasurable
      hC.measurableSet
  have hleftSeq_meas : ∀ n, AEStronglyMeasurable
      (fun z ↦ a z • g n (ambientMap F z)) μC := by
    intro n
    exact ha_cont.aestronglyMeasurable.smul
      ((g n).smooth.continuous.comp_aestronglyMeasurable hF_C_meas)
  have hleft_bound : ∀ n, ∀ᵐ z ∂μC,
      ‖a z • g n (ambientMap F z)‖ ≤ Ma' * (Mη * Mθ) := by
    intro n
    filter_upwards [ae_restrict_mem hC.measurableSet] with z hzC
    have ha_bound : ‖a z‖ ≤ Ma' :=
      (hMa z hzC).trans (le_max_left _ _)
    calc
      ‖a z • g n (ambientMap F z)‖ =
          ‖a z‖ * ‖η (ambientMap F z) *
            θ (hgraph.approximants (ns n) (ambientMap F z))‖ := by
        simp [g]
      _ = ‖a z‖ * (‖η (ambientMap F z)‖ *
          ‖θ (hgraph.approximants (ns n) (ambientMap F z))‖) := by
        rw [norm_mul]
      _ ≤ Ma' * (Mη * Mθ) := by
        exact mul_le_mul ha_bound
          (mul_le_mul (hMη _) (hMθ _) (norm_nonneg _) hMη_nonneg)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hMa'
  have hleft_pointwise : ∀ᵐ z ∂μC,
      Filter.Tendsto (fun n ↦ a z • g n (ambientMap F z))
        Filter.atTop (𝓝 (a z • u (ambientMap F z))) := by
    filter_upwards [hg_value_tendsto] with z hz
    exact tendsto_const_nhds.smul hz
  have hleft_tendsto : Filter.Tendsto
      (fun n ↦ ∫ z, a z • g n (ambientMap F z) ∂μC)
      Filter.atTop
      (𝓝 (∫ z, a z • u (ambientMap F z) ∂μC)) := by
    letI : IsFiniteMeasure μC :=
      isFiniteMeasure_restrict.2 hC.measure_ne_top
    have hdom_int : Integrable
        (fun _ : ℂ ↦ (Ma' * (Mη * Mθ) : ℝ)) μC :=
      integrable_const _
    exact tendsto_integral_of_dominated_convergence
      (μ := μC) (F := fun n z ↦ a z • g n (ambientMap F z))
      (f := fun z ↦ a z • u (ambientMap F z))
      (fun _ ↦ Ma' * (Mη * Mθ)) hleftSeq_meas hdom_int
      hleft_bound hleft_pointwise
  let pullError : ℕ → ℂ → ℂ →L[ℝ] ℝ := fun n z ↦
    ((L.indicator (error n)) (ambientMap F z)).comp (df z)
  have hpullErrorC_mem : ∀ n, MemLp (pullError n) 2 μC := by
    intro n
    exact (hpullError_mem n).mono_measure (by
      dsimp [μC]
      exact Measure.restrict_mono hCΩ le_rfl)
  have hpullErrorC_zero : Filter.Tendsto
      (fun n ↦ eLpNorm (pullError n) 2 μC)
      Filter.atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      hpullError_zero (fun _ ↦ zero_le) (fun n ↦ ?_)
    exact eLpNorm_mono_measure _ (by
      dsimp [μC]
      exact Measure.restrict_mono hCΩ le_rfl)
  have hφC_mem : MemLp (φ : ℂ → ℝ) 2 μC :=
    memLp_restrict_of_isCompact_of_continuousOn hC
      φ.smooth.continuous.continuousOn
  let B : ℕ → ℂ → ℝ := fun _ z ↦ φ z
  let β : (ℂ →L[ℝ] ℝ) → ℝ → ℝ := fun A r ↦ r • A v
  have hβ_meas : ∀ n, AEStronglyMeasurable
      (fun z ↦ β (pullError n z) (B n z)) μC := by
    intro n
    exact φ.smooth.continuous.aestronglyMeasurable.smul
      (((ContinuousLinearMap.apply ℝ ℝ) v).continuous.comp_aestronglyMeasurable
        (hpullErrorC_mem n).aestronglyMeasurable)
  have hβ_bound : ∀ n, ∀ᵐ z ∂μC,
      ‖β (pullError n z) (B n z)‖₊ ≤
        ‖v‖₊ * ‖pullError n z‖₊ * ‖B n z‖₊ := by
    intro n
    filter_upwards with z
    apply NNReal.coe_le_coe.mp
    calc
      ‖β (pullError n z) (B n z)‖ =
          ‖B n z‖ * ‖pullError n z v‖ := by simp [β]
      _ ≤ ‖B n z‖ * (‖pullError n z‖ * ‖v‖) := by
        gcongr
        exact ContinuousLinearMap.le_opNorm _ _
      _ = ‖v‖ * ‖pullError n z‖ * ‖B n z‖ := by ring
  obtain ⟨hpair_int, hpair_zero⟩ :=
    integral_bilinear_tendsto_zero_of_L2_tendsto_zero_of_L2_bounded
      β ‖v‖₊ hpullErrorC_mem
      (fun n ↦ by simpa [B] using hφC_mem) hβ_meas hβ_bound
      hpullErrorC_zero
      ⟨eLpNorm (φ : ℂ → ℝ) 2 μC, hφC_mem.eLpNorm_lt_top.ne,
        fun n ↦ by rfl⟩
  have hcandC := (hlocal C hC hCΩ).2
  have hcandEvalC : MemLp
      (fun z ↦ ((du (ambientMap F z)).comp (df z)) v) 2 μC :=
    ((ContinuousLinearMap.apply ℝ ℝ) v).comp_memLp' hcandC
  have hrightLimit_int : Integrable
      (fun z ↦ φ z • ((du (ambientMap F z)).comp (df z)) v) μC :=
    memLp_one_iff_integrable.mp (hcandEvalC.smul hφC_mem)
  have hgW : ∀ n, IsLocalW12RealOn Ω
      (fun z ↦ g n (ambientMap F z))
      (fun z ↦ (fderiv ℝ (g n : ℂ → ℝ) (ambientMap F z)).comp (df z)) :=
    fun n ↦ hdf.postcomp_smoothCompactlySupported (g n)
  have hsmooth : ∀ n,
      Integrable
          (fun z ↦ (fderiv ℝ (φ : ℂ → ℝ) z v) •
            g n (ambientMap F z)) (volume.restrict Ω) ∧
        Integrable
          (fun z ↦ φ z •
            ((fderiv ℝ (g n : ℂ → ℝ) (ambientMap F z)).comp (df z)) v)
          (volume.restrict Ω) ∧
        (∫ z in Ω, (fderiv ℝ (φ : ℂ → ℝ) z v) •
            g n (ambientMap F z) ∂volume) =
          -∫ z in Ω, φ z •
            ((fderiv ℝ (g n : ℂ → ℝ) (ambientMap F z)).comp (df z)) v
            ∂volume :=
    fun n ↦ (hgW n).2.1 φ v
  have hrightSeqC_int : ∀ n, Integrable
      (fun z ↦ φ z •
        ((fderiv ℝ (g n : ℂ → ℝ) (ambientMap F z)).comp (df z)) v)
      μC := by
    intro n
    exact (hsmooth n).2.1.mono_measure (by
      dsimp [μC]
      exact Measure.restrict_mono hCΩ le_rfl)
  let leftSeq : ℕ → ℝ := fun n ↦
    ∫ z, a z • g n (ambientMap F z) ∂μC
  let rightSeq : ℕ → ℝ := fun n ↦
    ∫ z, φ z •
      ((fderiv ℝ (g n : ℂ → ℝ) (ambientMap F z)).comp (df z)) v ∂μC
  let rightLimit : ℝ :=
    ∫ z, φ z • ((du (ambientMap F z)).comp (df z)) v ∂μC
  have hright_sub_eq : ∀ n,
      rightSeq n - rightLimit =
        ∫ z, β (pullError n z) (B n z) ∂μC := by
    intro n
    rw [← integral_sub (hrightSeqC_int n) hrightLimit_int]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hC.measurableSet] with z hzC
    have hFzL : ambientMap F z ∈ L := ⟨z, hzC, rfl⟩
    rw [hg_deriv n (ambientMap F z) hFzL]
    simp only [pullError]
    rw [show (L.indicator (error n)) (ambientMap F z) =
        error n (ambientMap F z) by simp [hFzL]]
    simp only [error, B, β, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sub_apply, smul_eq_mul]
    ring
  have hright_sub_zero : Filter.Tendsto
      (fun n ↦ rightSeq n - rightLimit) Filter.atTop (𝓝 0) := by
    apply hpair_zero.congr'
    filter_upwards with n
    exact (hright_sub_eq n).symm
  have hright_tendsto : Filter.Tendsto rightSeq Filter.atTop
      (𝓝 rightLimit) := by
    simpa using hright_sub_zero.add_const rightLimit
  have hsmooth_eq : ∀ n, leftSeq n = -rightSeq n := by
    intro n
    have hleft_domain :
        (∫ z in Ω, (fderiv ℝ (φ : ℂ → ℝ) z v) •
          g n (ambientMap F z) ∂volume) = leftSeq n := by
      change (∫ z in Ω, a z • g n (ambientMap F z) ∂volume) = _
      exact setIntegral_eq_of_subset_of_forall_diff_eq_zero
        hdf.1.measurableSet hCΩ (by
          intro z hz
          have hdz : fderiv ℝ (φ : ℂ → ℝ) z = 0 :=
            fderiv_of_notMem_tsupport (𝕜 := ℝ)
              (f := (φ : ℂ → ℝ)) hz.2
          simp [a, hdz])
    have hright_domain :
        (∫ z in Ω, φ z •
          ((fderiv ℝ (g n : ℂ → ℝ) (ambientMap F z)).comp (df z)) v
          ∂volume) = rightSeq n := by
      exact setIntegral_eq_of_subset_of_forall_diff_eq_zero
        hdf.1.measurableSet hCΩ (by
          intro z hz
          have hφz : φ z = 0 := image_eq_zero_of_notMem_tsupport hz.2
          simp [hφz])
    have hs := (hsmooth n).2.2
    rw [hleft_domain, hright_domain] at hs
    exact hs
  have hleft_tendsto' : Filter.Tendsto leftSeq Filter.atTop
      (𝓝 (∫ z, a z • u (ambientMap F z) ∂μC)) := by
    simpa [leftSeq] using hleft_tendsto
  have hneg_right_tendsto_left : Filter.Tendsto
      (fun n ↦ -rightSeq n) Filter.atTop
      (𝓝 (∫ z, a z • u (ambientMap F z) ∂μC)) := by
    apply hleft_tendsto'.congr'
    filter_upwards with n
    exact hsmooth_eq n
  have hCidentity :
      (∫ z, a z • u (ambientMap F z) ∂μC) = -rightLimit :=
    tendsto_nhds_unique hneg_right_tendsto_left hright_tendsto.neg
  have hleftC_int : Integrable
      (fun z ↦ a z • u (ambientMap F z)) μC := by
    have huFC := (hlocal C hC hCΩ).1
    have haC : MemLp a 2 μC :=
      memLp_restrict_of_isCompact_of_continuousOn hC ha_cont.continuousOn
    exact memLp_one_iff_integrable.mp (huFC.smul haC)
  have hleft_support : Function.support
      (fun z ↦ a z • u (ambientMap F z)) ⊆ C := by
    intro z hz
    exact (tsupport_fderiv_apply_subset (𝕜 := ℝ)
      (f := (φ : ℂ → ℝ)) v)
        (subset_tsupport a
          (Function.support_smul_subset_left a
            (fun z ↦ u (ambientMap F z)) hz))
  have hright_support : Function.support
      (fun z ↦ φ z • ((du (ambientMap F z)).comp (df z)) v) ⊆ C := by
    intro z hz
    exact subset_tsupport (φ : ℂ → ℝ)
      (Function.support_smul_subset_left (φ : ℂ → ℝ)
        (fun z ↦ ((du (ambientMap F z)).comp (df z)) v) hz)
  have hleft_global : Integrable
      (fun z ↦ a z • u (ambientMap F z)) volume :=
    (integrableOn_iff_integrable_of_support_subset hleft_support).mp hleftC_int
  have hright_global : Integrable
      (fun z ↦ φ z • ((du (ambientMap F z)).comp (df z)) v) volume :=
    (integrableOn_iff_integrable_of_support_subset hright_support).mp
      hrightLimit_int
  have hleftΩ := hleft_global.mono_measure
    (Measure.restrict_le_self (μ := volume) (s := Ω))
  have hrightΩ := hright_global.mono_measure
    (Measure.restrict_le_self (μ := volume) (s := Ω))
  refine ⟨?_, hrightΩ, ?_⟩
  · simpa [a] using hleftΩ
  have hleft_domain :
      (∫ z in Ω, a z • u (ambientMap F z) ∂volume) =
        ∫ z, a z • u (ambientMap F z) ∂μC :=
    setIntegral_eq_of_subset_of_forall_diff_eq_zero
      hdf.1.measurableSet hCΩ (by
        intro z hz
        have hdz : fderiv ℝ (φ : ℂ → ℝ) z = 0 :=
          fderiv_of_notMem_tsupport (𝕜 := ℝ)
            (f := (φ : ℂ → ℝ)) hz.2
        simp [a, hdz])
  have hright_domain :
      (∫ z in Ω, φ z • ((du (ambientMap F z)).comp (df z)) v ∂volume) =
        rightLimit :=
    setIntegral_eq_of_subset_of_forall_diff_eq_zero
      hdf.1.measurableSet hCΩ (by
        intro z hz
        have hφz : φ z = 0 := image_eq_zero_of_notMem_tsupport hz.2
        simp [hφz])
  rw [hleft_domain, hright_domain]
  simpa [a] using hCidentity

/--
%%handwave
name:
  Complex continuous Sobolev outer chain rule under quasiconformal pullback
statement:
  Let $F:\Omega\to\Omega'$ be $K$-quasiconformal with weak differential
  $Df$. If $u:\Omega'\to\mathbb C$ is continuous and belongs to
  $W^{1,2}_{\mathrm{loc}}(\Omega',\mathbb C)$ with weak differential $Du$,
  then $u\circ F\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb C)$ and
  $$
    D(u\circ F)(z)=Du(F(z))\circ Df(z)
  $$
  almost everywhere.
proof:
  Apply the [real-valued outer chain rule](lean:JJMath.Quasiconformal.IsKQuasiconformalBetween.postcomp_continuous_isLocalW12RealOn) to the real and imaginary parts of $u$, then recombine their weak differentials and compact-local $L^2$ bounds.
-/
theorem IsKQuasiconformalBetween.postcomp_continuous_isLocalW12On
    {K : ℝ} {Ω Ω' : Set ℂ} {F : Ω ≃ₜ Ω'}
    (hF : IsKQuasiconformalBetween K F)
    {df : ℂ → ℂ →L[ℝ] ℂ}
    (hdf : IsLocalW12On Ω (ambientMap F) df)
    {u : ℂ → ℂ} {du : ℂ → ℂ →L[ℝ] ℂ}
    (hu : IsLocalW12On Ω' u du)
    (hu_cont : ContinuousOn u Ω') :
    IsLocalW12On Ω (fun z ↦ u (ambientMap F z))
      (fun z ↦ (du (ambientMap F z)).comp (df z)) := by
  have hre := hF.postcomp_continuous_isLocalW12RealOn hdf hu.re
    (Complex.continuous_re.comp_continuousOn hu_cont)
  have him := hF.postcomp_continuous_isLocalW12RealOn hdf hu.im
    (Complex.continuous_im.comp_continuousOn hu_cont)
  let dcomp : ℂ → ℂ →L[ℝ] ℂ := fun z ↦
    (du (ambientMap F z)).comp (df z)
  have hre' : IsLocalW12RealOn Ω
      (fun z ↦ (u (ambientMap F z)).re)
      (fun z ↦ Complex.reCLM.comp (dcomp z)) := by
    simpa only [dcomp, ContinuousLinearMap.comp_assoc] using hre
  have him' : IsLocalW12RealOn Ω
      (fun z ↦ (u (ambientMap F z)).im)
      (fun z ↦ Complex.imCLM.comp (dcomp z)) := by
    simpa only [dcomp, ContinuousLinearMap.comp_assoc] using him
  exact isLocalW12On_of_re_im hre' him'

/--
%%handwave
name:
  Smooth condenser competitors pull back with quasiconformal energy control
statement:
  Let $F:\Omega\to\Omega'$ be $K$-quasiconformal with weak differential
  $Df$. Suppose $u:\mathbb C\to\mathbb R$ is smooth and compactly supported,
  $E_0,E_1\subseteq\Omega$, and $u(F(z))=0$ on $E_0$ while $u(F(z))=1$
  on $E_1$. Then $u\circ F$ is a condenser competitor for
  $(E_0,E_1;\Omega)$ and may be chosen with energy satisfying
  $$
    \mathcal E_\Omega(u\circ F)
      \leq K\int_{\Omega'}\lVert Du(y)\rVert^2\,dy.
  $$
proof:
  The [smooth compactly supported postcomposition theorem](lean:JJMath.Quasiconformal.IsLocalW12On.postcomp_smoothCompactlySupported) supplies the weak differential $Du(F(z))\circ Df(z)$, and continuity plus the plate hypotheses give admissibility. The energy estimate is [the quasiconformal pullback energy inequality](lean:JJMath.Quasiconformal.IsKQuasiconformalBetween.lintegral_norm_comp_weakDifferential_sq_le) applied to the covector field $Du$.
-/
theorem IsKQuasiconformalBetween.exists_smoothPullbackCompetitor_energy_le
    {K : ℝ} {Ω Ω' E₀ E₁ : Set ℂ} {F : Ω ≃ₜ Ω'}
    (hF : IsKQuasiconformalBetween K F) {df : ℂ → ℂ →L[ℝ] ℂ}
    (hdf : IsLocalW12On Ω (ambientMap F) df)
    (u : JJMath.Uniformization.SmoothCompactlySupportedManifoldCoordinateFunction Ω')
    (hE₀ : E₀ ⊆ Ω) (hE₁ : E₁ ⊆ Ω)
    (hu₀ : ∀ z ∈ E₀, u (ambientMap F z) = 0)
    (hu₁ : ∀ z ∈ E₁, u (ambientMap F z) = 1) :
    ∃ v : PlanarCondenserCompetitor Ω E₀ E₁,
      v.dirichletEnergy ≤ ENNReal.ofReal K *
        ∫⁻ y in Ω',
          ENNReal.ofReal
            (‖fderiv ℝ (u : ℂ → ℝ) y‖ ^ (2 : ℕ)) ∂volume := by
  let v : PlanarCondenserCompetitor Ω E₀ E₁ :=
    { toFun := fun z ↦ u (ambientMap F z)
      weakDifferential := fun z ↦
        (fderiv ℝ (u : ℂ → ℝ) (ambientMap F z)).comp (df z)
      zeroPlate_subset := hE₀
      onePlate_subset := hE₁
      isLocalW12 := hdf.postcomp_smoothCompactlySupported u
      continuousOn :=
        u.smooth.continuous.comp_continuousOn (continuousOn_ambientMap F)
      eq_zero_on := hu₀
      eq_one_on := hu₁ }
  refine ⟨v, ?_⟩
  simpa [v, PlanarCondenserCompetitor.dirichletEnergy] using
    hF.lintegral_norm_comp_weakDifferential_sq_le hdf
      (fun y ↦ fderiv ℝ (u : ℂ → ℝ) y)

/--
%%handwave
name:
  Continuous Sobolev condenser competitors pull back with energy control
statement:
  Let $F:\Omega\to\Omega'$ be $K$-quasiconformal with weak differential
  $Df$, and let $u$ be a continuous Sobolev competitor on $\Omega'$ for the
  image plates $F(E_0)$ and $F(E_1)$. Then $u\circ F$ is a competitor on
  $\Omega$ for $E_0$ and $E_1$, and
  $$
    \mathcal E_\Omega(u\circ F)
      \leq K\mathcal E_{\Omega'}(u).
  $$
proof:
  The [continuous Sobolev outer chain rule](lean:JJMath.Quasiconformal.IsKQuasiconformalBetween.postcomp_continuous_isLocalW12RealOn) gives weak differential $(Du\circ F)\circ Df$. Continuity preserves the pointwise plate values, and the [quasiconformal pullback energy inequality](lean:JJMath.Quasiconformal.IsKQuasiconformalBetween.lintegral_norm_comp_weakDifferential_sq_le) bounds its Dirichlet energy.
-/
theorem IsKQuasiconformalBetween.exists_pullbackCompetitor_energy_le
    {K : ℝ} {Ω Ω' E₀ E₁ : Set ℂ} {F : Ω ≃ₜ Ω'}
    (hF : IsKQuasiconformalBetween K F)
    {df : ℂ → ℂ →L[ℝ] ℂ}
    (hdf : IsLocalW12On Ω (ambientMap F) df)
    (u : PlanarCondenserCompetitor Ω'
      (ambientMap F '' E₀) (ambientMap F '' E₁))
    (hE₀ : E₀ ⊆ Ω) (hE₁ : E₁ ⊆ Ω) :
    ∃ v : PlanarCondenserCompetitor Ω E₀ E₁,
      v.dirichletEnergy ≤ ENNReal.ofReal K * u.dirichletEnergy := by
  let v : PlanarCondenserCompetitor Ω E₀ E₁ :=
    { toFun := fun z ↦ u (ambientMap F z)
      weakDifferential := fun z ↦
        (u.weakDifferential (ambientMap F z)).comp (df z)
      zeroPlate_subset := hE₀
      onePlate_subset := hE₁
      isLocalW12 := hF.postcomp_continuous_isLocalW12RealOn
        hdf u.isLocalW12 u.continuousOn
      continuousOn := u.continuousOn.comp
        (continuousOn_ambientMap F) (fun z hz ↦ by
          let zΩ : Ω := ⟨z, hz⟩
          rw [ambientMap_apply F zΩ]
          exact (F zΩ).2)
      eq_zero_on := fun z hz ↦ u.eq_zero_on _ ⟨z, hz, rfl⟩
      eq_one_on := fun z hz ↦ u.eq_one_on _ ⟨z, hz, rfl⟩ }
  refine ⟨v, ?_⟩
  simpa [v, PlanarCondenserCompetitor.dirichletEnergy] using
    hF.lintegral_norm_comp_weakDifferential_sq_le hdf u.weakDifferential

/--
%%handwave
name:
  Quasiconformal upper bound for planar condenser capacity
statement:
  Let $F:\Omega\to\Omega'$ be $K$-quasiconformal and let
  $E_0,E_1\subseteq\Omega$. Then
  $$
    \operatorname{cap}_{\Omega}(E_0,E_1)
      \leq K\,
        \operatorname{cap}_{\Omega'}(F(E_0),F(E_1)).
  $$
proof:
  Pull back every continuous Sobolev competitor for the image condenser.
  [Its pullback is admissible and has at most $K$ times the original
  energy](lean:JJMath.Quasiconformal.IsKQuasiconformalBetween.exists_pullbackCompetitor_energy_le). Take the infimum over all target competitors; multiplication by the finite positive number $K$ commutes with this infimum.
-/
theorem IsKQuasiconformalBetween.planarCondenserCapacity_le
    {K : ℝ} {Ω Ω' E₀ E₁ : Set ℂ} {F : Ω ≃ₜ Ω'}
    (hF : IsKQuasiconformalBetween K F)
    (hE₀ : E₀ ⊆ Ω) (hE₁ : E₁ ⊆ Ω) :
    planarCondenserCapacity Ω E₀ E₁ ≤
      ENNReal.ofReal K *
        planarCondenserCapacity Ω'
          (ambientMap F '' E₀) (ambientMap F '' E₁) := by
  obtain ⟨df, hdf, -⟩ := hF.2.2.2
  have hKpos : 0 < K := zero_lt_one.trans_le hF.1
  simp only [planarCondenserCapacity, sInf_range]
  rw [ENNReal.mul_iInf_of_ne
    (ENNReal.ofReal_ne_zero_iff.mpr hKpos) ENNReal.ofReal_ne_top]
  refine le_iInf fun u ↦ ?_
  obtain ⟨v, hv⟩ := hF.exists_pullbackCompetitor_energy_le
    hdf u hE₀ hE₁
  exact (iInf_le_of_le v le_rfl).trans hv

/--
%%handwave
name:
  Quasiconformal distortion of planar condenser capacity
statement:
  Let $F:\Omega\to\Omega'$ be $K$-quasiconformal and let
  $E_0,E_1\subseteq\Omega$. Then
  $$
    \operatorname{cap}_{\Omega'}(F(E_0),F(E_1))
      \leq K\operatorname{cap}_{\Omega}(E_0,E_1)
  $$
  and
  $$
    \operatorname{cap}_{\Omega}(E_0,E_1)
      \leq K\operatorname{cap}_{\Omega'}(F(E_0),F(E_1)).
  $$
proof:
  The second inequality is [the quasiconformal pullback bound](lean:JJMath.Quasiconformal.IsKQuasiconformalBetween.planarCondenserCapacity_le). Apply the same result to [the $K$-quasiconformal inverse](lean:JJMath.Quasiconformal.IsKQuasiconformalBetween.symm) for the first inequality; the inverse image of $F(E_j)$ is $E_j$ because $E_j\subseteq\Omega$.
-/
theorem IsKQuasiconformalBetween.planarCondenserCapacity_distortion
    {K : ℝ} {Ω Ω' E₀ E₁ : Set ℂ} {F : Ω ≃ₜ Ω'}
    (hF : IsKQuasiconformalBetween K F)
    (hE₀ : E₀ ⊆ Ω) (hE₁ : E₁ ⊆ Ω) :
    planarCondenserCapacity Ω'
        (ambientMap F '' E₀) (ambientMap F '' E₁) ≤
        ENNReal.ofReal K * planarCondenserCapacity Ω E₀ E₁ ∧
      planarCondenserCapacity Ω E₀ E₁ ≤
        ENNReal.ofReal K * planarCondenserCapacity Ω'
          (ambientMap F '' E₀) (ambientMap F '' E₁) := by
  have himage_subset : ∀ {E : Set ℂ}, E ⊆ Ω →
      ambientMap F '' E ⊆ Ω' := by
    intro E hE y hy
    obtain ⟨z, hzE, rfl⟩ := hy
    let zΩ : Ω := ⟨z, hE hzE⟩
    rw [ambientMap_apply F zΩ]
    exact (F zΩ).2
  have hinverse_image : ∀ {E : Set ℂ}, E ⊆ Ω →
      ambientMap F.symm '' (ambientMap F '' E) = E := by
    intro E hE
    apply Subset.antisymm
    · rintro z ⟨y, ⟨x, hxE, rfl⟩, rfl⟩
      rw [ambientMap_symm_apply_ambientMap F ⟨x, hE hxE⟩]
      exact hxE
    · intro z hzE
      exact ⟨ambientMap F z, ⟨z, hzE, rfl⟩,
        ambientMap_symm_apply_ambientMap F ⟨z, hE hzE⟩⟩
  refine ⟨?_, hF.planarCondenserCapacity_le hE₀ hE₁⟩
  have hinv := hF.symm.planarCondenserCapacity_le
    (himage_subset hE₀) (himage_subset hE₁)
  rw [hinverse_image hE₀, hinverse_image hE₁] at hinv
  exact hinv

end

end Quasiconformal

end JJMath
