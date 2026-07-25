import JJMath.Analysis.Weyl
import JJMath.Quasiconformal.Capacity
import Mathlib.Analysis.Complex.Conformal

/-!
# Weakly holomorphic planar Sobolev maps

This file proves the Sobolev Weyl lemma for the Cauchy--Riemann operator:
a continuous complex-valued local `W^{1,2}` map whose weak
`∂_{\bar z}` derivative vanishes almost everywhere is holomorphic.
-/

namespace JJMath

open MeasureTheory Set
open scoped ENNReal Topology

namespace Quasiconformal

noncomputable section

/--
%%handwave
name:
  The real part of a weakly holomorphic Sobolev map is weakly harmonic
statement:
  Let $\Omega\subseteq\mathbb C$ be open and let
  $f=u+iv\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb C)$. If
  $\partial_{\bar z}f=0$ almost everywhere on $\Omega$, then $u$ is weakly
  harmonic there.
proof:
  The weak Cauchy--Riemann equations give $u_x=v_y$ and $u_y=-v_x$ almost
  everywhere. For a compactly supported smooth test $\eta$, substitute these
  identities in $\int(u_x\eta_x+u_y\eta_y)$. Apply the weak derivative
  identities for $v$ to the tests $\eta_x$ and $\eta_y$; equality of the
  mixed second derivatives of $\eta$ makes the two resulting terms cancel.
-/
theorem IsLocalW12On.re_isEuclideanWeaklyHarmonicOn_of_weakDBar_eq_zero_ae
    {Ω : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (hW : IsLocalW12On Ω f df)
    (hbar : ∀ᵐ z ∂volume.restrict Ω, weakDBar (df z) = 0) :
    JJMath.Uniformization.IsEuclideanWeaklyHarmonicOn Ω
      (fun z ↦ (f z).re) := by
  let du : ℂ → ℂ →L[ℝ] ℝ := fun z ↦ Complex.reCLM.comp (df z)
  let dv : ℂ → ℂ →L[ℝ] ℝ := fun z ↦ Complex.imCLM.comp (df z)
  have hU := hW.re
  have hV := hW.im
  refine ⟨hW.1, du, hU.2.1, ?_⟩
  intro η
  let ηx := η.directionalDerivative (1 : ℂ)
  let ηy := η.directionalDerivative Complex.I
  have hux_int :
      Integrable
        (fun z ↦ ηx z * du z (1 : ℂ))
        (volume.restrict Ω) := by
    simpa [ηx, du, smul_eq_mul] using (hU.2.1 ηx (1 : ℂ)).2.1
  have huy_int :
      Integrable
        (fun z ↦ ηy z * du z Complex.I)
        (volume.restrict Ω) := by
    simpa [ηy, du, smul_eq_mul] using (hU.2.1 ηy Complex.I).2.1
  have hpair_int :
      Integrable
        (fun z ↦
          JJMath.Uniformization.euclideanCotangentPairing (du z)
            (fderiv ℝ (η : ℂ → ℝ) z))
        (volume.restrict Ω) := by
    convert hux_int.add huy_int using 1
    funext z
    simp [JJMath.Uniformization.euclideanCotangentPairing, ηx, ηy,
      mul_comm]
  refine ⟨hpair_int, ?_⟩
  have hcr :
      ∀ᵐ z ∂volume.restrict Ω,
        du z (1 : ℂ) = dv z Complex.I ∧
          du z Complex.I = -dv z (1 : ℂ) := by
    filter_upwards [hbar] with z hz
    simpa [du, dv] using cauchyRiemann_of_weakDBar_eq_zero (df z) hz
  have hVx := hV.2.1 ηx Complex.I
  have hVy := hV.2.1 ηy (1 : ℂ)
  have hmixed :
      (fun z ↦
          fderiv ℝ (ηx : ℂ → ℝ) z Complex.I * (f z).im) =
        fun z ↦
          fderiv ℝ (ηy : ℂ → ℝ) z (1 : ℂ) * (f z).im := by
    funext z
    rw [JJMath.Uniformization.SmoothCompactlySupportedManifoldCoordinateFunction.fderiv_directionalDerivative_comm
      η (1 : ℂ) Complex.I z]
  have hright_eq :
      ∫ z in Ω, ηx z * dv z Complex.I ∂volume =
        ∫ z in Ω, ηy z * dv z (1 : ℂ) ∂volume := by
    have hx :
        ∫ z in Ω,
              fderiv ℝ (ηx : ℂ → ℝ) z Complex.I * (f z).im
              ∂volume =
            -∫ z in Ω, ηx z * dv z Complex.I ∂volume := by
      simpa [ηx, dv, smul_eq_mul] using hVx.2.2
    have hy :
        ∫ z in Ω,
              fderiv ℝ (ηy : ℂ → ℝ) z (1 : ℂ) * (f z).im
              ∂volume =
            -∫ z in Ω, ηy z * dv z (1 : ℂ) ∂volume := by
      simpa [ηy, dv, smul_eq_mul] using hVy.2.2
    rw [hmixed] at hx
    linarith
  calc
    ∫ z in Ω,
        JJMath.Uniformization.euclideanCotangentPairing (du z)
          (fderiv ℝ (η : ℂ → ℝ) z) ∂volume =
        ∫ z in Ω,
          (ηx z * dv z Complex.I - ηy z * dv z (1 : ℂ)) ∂volume := by
            apply integral_congr_ae
            filter_upwards [hcr] with z hz
            simp [JJMath.Uniformization.euclideanCotangentPairing, ηx, ηy,
              hz.1, hz.2]
            ring
    _ = (∫ z in Ω, ηx z * dv z Complex.I ∂volume) -
          ∫ z in Ω, ηy z * dv z (1 : ℂ) ∂volume := by
            rw [integral_sub]
            · exact hVx.2.1
            · exact hVy.2.1
    _ = 0 := sub_eq_zero.mpr hright_eq

/--
%%handwave
name:
  The imaginary part of a weakly holomorphic Sobolev map is weakly harmonic
statement:
  Let $\Omega\subseteq\mathbb C$ be open and let
  $f=u+iv\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb C)$. If
  $\partial_{\bar z}f=0$ almost everywhere on $\Omega$, then $v$ is weakly
  harmonic there.
proof:
  Apply the corresponding result for the real part to $-if$, whose real part
  is $v$ and whose conjugate Wirtinger derivative is
  $-i\,\partial_{\bar z}f$.
-/
theorem IsLocalW12On.im_isEuclideanWeaklyHarmonicOn_of_weakDBar_eq_zero_ae
    {Ω : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (hW : IsLocalW12On Ω f df)
    (hbar : ∀ᵐ z ∂volume.restrict Ω, weakDBar (df z) = 0) :
    JJMath.Uniformization.IsEuclideanWeaklyHarmonicOn Ω
      (fun z ↦ (f z).im) := by
  have hWrot := hW.postcomp_complexAffine (-Complex.I) 0
  have hbarrot :
      ∀ᵐ z ∂volume.restrict Ω,
        weakDBar
          ((realLinearMapOfWirtinger (-Complex.I) 0).comp (df z)) = 0 := by
    filter_upwards [hbar] with z hz
    rw [weakDBar_complexLinear_comp, hz]
    simp
  simpa [Complex.mul_re, Complex.mul_im] using
    hWrot.re_isEuclideanWeaklyHarmonicOn_of_weakDBar_eq_zero_ae hbarrot

/--
%%handwave
name:
  Sobolev Weyl lemma for the Cauchy--Riemann operator
statement:
  Let $\Omega\subseteq\mathbb C$ be open. Suppose
  $f\in W^{1,2}_{\mathrm{loc}}(\Omega,\mathbb C)$ is continuous and its weak
  differential satisfies
  $$
    \partial_{\bar z}f=0
  $$
  almost everywhere on $\Omega$. Then $f$ is holomorphic on $\Omega$.
proof:
  The real and imaginary parts are weakly harmonic by the weak
  Cauchy--Riemann equations. The Euclidean Weyl lemma and continuity make
  both components classically harmonic, hence continuously differentiable.
  The classical real differential is therefore another weak differential of
  $f$ and agrees almost everywhere with the given one. Its conjugate
  Wirtinger component is continuous and vanishes almost everywhere, so it
  vanishes everywhere on the open region. The pointwise Cauchy--Riemann
  criterion gives complex differentiability.
-/
theorem IsLocalW12On.differentiableOn_complex_of_continuousOn_of_weakDBar_eq_zero_ae
    {Ω : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (hW : IsLocalW12On Ω f df)
    (hcont : ContinuousOn f Ω)
    (hbar : ∀ᵐ z ∂volume.restrict Ω, weakDBar (df z) = 0) :
    DifferentiableOn ℂ f Ω := by
  have hu_harm :
      InnerProductSpace.HarmonicOnNhd (fun z ↦ (f z).re) Ω :=
    (hW.re_isEuclideanWeaklyHarmonicOn_of_weakDBar_eq_zero_ae hbar).harmonicOnNhd_of_continuousOn
      (Complex.reCLM.continuous.continuousOn.comp hcont
        (fun _ _ ↦ Set.mem_univ _))
  have hv_harm :
      InnerProductSpace.HarmonicOnNhd (fun z ↦ (f z).im) Ω :=
    (hW.im_isEuclideanWeaklyHarmonicOn_of_weakDBar_eq_zero_ae hbar).harmonicOnNhd_of_continuousOn
      (Complex.imCLM.continuous.continuousOn.comp hcont
        (fun _ _ ↦ Set.mem_univ _))
  have hrepr :
      (fun z : ℂ ↦
        ((f z).re : ℂ) + Complex.I * ((f z).im : ℂ)) = f := by
    funext z
    apply Complex.ext <;> simp
  have hfC : ContDiffOn ℝ 1 f Ω := by
    rw [← hrepr]
    have huC :
        ContDiffOn ℝ 1 (fun z ↦ ((f z).re : ℂ)) Ω :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn
        (hu_harm.contDiffOn.of_le (by norm_num))
    have hvC :
        ContDiffOn ℝ 1 (fun z ↦ ((f z).im : ℂ)) Ω :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn
        (hv_harm.contDiffOn.of_le (by norm_num))
    exact huC.add (contDiffOn_const.mul hvC)
  have hclass :
      IsLocalW12On Ω f (fun z ↦ fderiv ℝ f z) :=
    isLocalW12On_of_contDiffOn hW.1 hfC
  have heq :
      df =ᵐ[volume.restrict Ω] fun z ↦ fderiv ℝ f z :=
    hW.weakDifferential_ae_eq hclass
  have hzeroae :
      (fun z ↦ weakDBar (fderiv ℝ f z)) =ᵐ[volume.restrict Ω]
        fun _ ↦ 0 := by
    filter_upwards [heq, hbar] with z hz hzb
    rw [← hz, hzb]
  have hanti_cont :
      ContinuousOn (fun z ↦ weakDBar (fderiv ℝ f z)) Ω := by
    exact continuous_weakDBar.continuousOn.comp
      (hfC.continuousOn_fderiv_of_isOpen hW.1 (by norm_num))
      (fun _ _ ↦ Set.mem_univ _)
  have hzero :
      Ω.EqOn (fun z ↦ weakDBar (fderiv ℝ f z)) (fun _ ↦ 0) :=
    Measure.eqOn_open_of_ae_eq hzeroae hW.1 hanti_cont continuousOn_const
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  rw [differentiableAt_complex_iff_differentiableAt_real]
  exact
    ⟨(hfC z hz).contDiffAt (hW.1.mem_nhds hz) |>.differentiableAt
        (by norm_num),
      map_I_eq_I_smul_map_one_of_weakDBar_eq_zero
        (fderiv ℝ f z) (hzero hz)⟩

end

end Quasiconformal

end JJMath
