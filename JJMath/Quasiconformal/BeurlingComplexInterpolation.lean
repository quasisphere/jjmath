import JJMath.Analysis.Harmonic.ComplexInterpolation
import JJMath.Quasiconformal.BeurlingAboveTwo

/-!
# Complex interpolation of the Beurling transform

This file instantiates the simple-core bilinear Riesz--Thorin theorem for
the Beurling transform.  The common core is the space of integrable planar
simple functions.  Each such function belongs to planar (L^2), so the
interpolated bilinear pairing can be defined once using the exact Fourier
multiplier.
-/

namespace JJMath

open MeasureTheory
open scoped ENNReal Topology

namespace Quasiconformal

noncomputable section

attribute [local instance] Lp.simpleFunc.smul Lp.simpleFunc.module
  Lp.simpleFunc.normedSpace Lp.simpleFunc.isBoundedSMul

/--
%%handwave
name:
  Integrable planar simple functions as $L^2$ functions
statement:
  Every integrable simple function on the plane has a canonical
  representative in $L^2(\mathbb C)$.
-/
def integrableSimpleFuncToPlaneL2
    (f : ℂ →₁ₛ[volume] ℂ) : PlaneL2 :=
  (show MemLp (f : ℂ → ℂ) 2 volume from by
    simpa using
      HarmonicAnalysis.memLp_integrableSimpleFunc
        (volume : Measure ℂ) zero_lt_two f).toLp (f : ℂ → ℂ)

/--
%%handwave
name:
  Representative of the $L^2$ inclusion of an integrable simple function
statement:
  The $L^2$ representative of an integrable planar simple function agrees
  almost everywhere with its original representative.
proof:
  The $L^2$ class is constructed from that representative.
-/
theorem integrableSimpleFuncToPlaneL2_coeFn
    (f : ℂ →₁ₛ[volume] ℂ) :
    (integrableSimpleFuncToPlaneL2 f : ℂ → ℂ) =ᵐ[volume]
      (f : ℂ → ℂ) := by
  exact (HarmonicAnalysis.memLp_integrableSimpleFunc
    (volume : Measure ℂ) zero_lt_two f).coeFn_toLp

/--
%%handwave
name:
  Linearity of the $L^2$ inclusion of integrable simple functions
statement:
  Sending an integrable planar simple function to the same
  almost-everywhere class in $L^2(\mathbb C)$ defines a complex-linear map.
-/
def integrableSimpleFuncToPlaneL2LinearMap :
    (ℂ →₁ₛ[volume] ℂ) →ₗ[ℂ] PlaneL2 where
  toFun := integrableSimpleFuncToPlaneL2
  map_add' f g := by
    have hsource :
        ((f + g : ℂ →₁ₛ[volume] ℂ) : ℂ → ℂ) =ᵐ[volume]
          (f : ℂ → ℂ) + (g : ℂ → ℂ) := by
      filter_upwards [
        Lp.simpleFunc.toSimpleFunc_eq_toFun (f + g),
        Lp.simpleFunc.add_toSimpleFunc f g,
        Lp.simpleFunc.toSimpleFunc_eq_toFun f,
        Lp.simpleFunc.toSimpleFunc_eq_toFun g] with z hsum hadd hf hg
      calc
        ((f + g : ℂ →₁ₛ[volume] ℂ) : ℂ → ℂ) z =
            Lp.simpleFunc.toSimpleFunc (f + g) z := hsum.symm
        _ = Lp.simpleFunc.toSimpleFunc f z +
            Lp.simpleFunc.toSimpleFunc g z := by
          simpa only [Pi.add_apply] using hadd
        _ = (f : ℂ → ℂ) z + (g : ℂ → ℂ) z := by rw [hf, hg]
    apply Lp.ext
    filter_upwards [
      integrableSimpleFuncToPlaneL2_coeFn (f + g),
      integrableSimpleFuncToPlaneL2_coeFn f,
      integrableSimpleFuncToPlaneL2_coeFn g,
      hsource,
      Lp.coeFn_add (integrableSimpleFuncToPlaneL2 f)
        (integrableSimpleFuncToPlaneL2 g)] with z hsum hf hg hsource htarget
    calc
      (integrableSimpleFuncToPlaneL2 (f + g) : ℂ → ℂ) z =
          ((f + g : ℂ →₁ₛ[volume] ℂ) : ℂ → ℂ) z := hsum
      _ = (f : ℂ → ℂ) z + (g : ℂ → ℂ) z := by
        simpa only [Pi.add_apply] using hsource
      _ = (integrableSimpleFuncToPlaneL2 f : ℂ → ℂ) z +
          (integrableSimpleFuncToPlaneL2 g : ℂ → ℂ) z := by
        rw [hf, hg]
      _ = (integrableSimpleFuncToPlaneL2 f +
          integrableSimpleFuncToPlaneL2 g : PlaneL2) z := htarget.symm
  map_smul' c f := by
    have hsource :
        ((c • f : ℂ →₁ₛ[volume] ℂ) : ℂ → ℂ) =ᵐ[volume]
          c • (f : ℂ → ℂ) := by
      filter_upwards [
        Lp.simpleFunc.toSimpleFunc_eq_toFun (c • f),
        Lp.simpleFunc.smul_toSimpleFunc c f,
        Lp.simpleFunc.toSimpleFunc_eq_toFun f] with z hscaled hraw hf
      calc
        ((c • f : ℂ →₁ₛ[volume] ℂ) : ℂ → ℂ) z =
            Lp.simpleFunc.toSimpleFunc (c • f) z := hscaled.symm
        _ = c * Lp.simpleFunc.toSimpleFunc f z := by
          simpa only [Pi.smul_apply, smul_eq_mul] using hraw
        _ = c * (f : ℂ → ℂ) z := by rw [hf]
        _ = (c • (f : ℂ → ℂ)) z := by
          simp only [Pi.smul_apply, smul_eq_mul]
    apply Lp.ext
    filter_upwards [
      integrableSimpleFuncToPlaneL2_coeFn (c • f),
      integrableSimpleFuncToPlaneL2_coeFn f,
      hsource,
      Lp.coeFn_smul c (integrableSimpleFuncToPlaneL2 f)] with
        z hscaled hf hsource htarget
    calc
      (integrableSimpleFuncToPlaneL2 (c • f) : ℂ → ℂ) z =
          ((c • f : ℂ →₁ₛ[volume] ℂ) : ℂ → ℂ) z := hscaled
      _ = c * (f : ℂ → ℂ) z := by
        simpa only [Pi.smul_apply, smul_eq_mul] using hsource
      _ = c * (integrableSimpleFuncToPlaneL2 f : ℂ → ℂ) z := by
        rw [hf]
      _ = (c • integrableSimpleFuncToPlaneL2 f : PlaneL2) z := by
        simpa only [Pi.smul_apply, smul_eq_mul] using htarget.symm

/--
%%handwave
name:
  $L^2$ norm of the integrable-simple inclusion
statement:
  If $f$ is an integrable planar simple function and $f_2$ is its canonical
  $L^2$ class, then
  $$
    \|f_2\|_{L^2}=\|f\|_{L^2}.
  $$
proof:
  The two representatives agree almost everywhere.
-/
theorem norm_integrableSimpleFuncToPlaneL2
    (f : ℂ →₁ₛ[volume] ℂ) :
    ‖integrableSimpleFuncToPlaneL2 f‖ =
      lpNorm (f : ℂ → ℂ) 2 volume := by
  calc
    ‖integrableSimpleFuncToPlaneL2 f‖ =
        (eLpNorm (integrableSimpleFuncToPlaneL2 f : ℂ → ℂ)
          2 volume).toReal := Lp.norm_def _
    _ = (eLpNorm (f : ℂ → ℂ) 2 volume).toReal :=
      congrArg ENNReal.toReal
        (eLpNorm_congr_ae (integrableSimpleFuncToPlaneL2_coeFn f))
    _ = lpNorm (f : ℂ → ℂ) 2 volume :=
      toReal_eLpNorm
        (HarmonicAnalysis.memLp_integrableSimpleFunc
          (volume : Measure ℂ) zero_lt_two f).aestronglyMeasurable

/--
%%handwave
name:
  Integrable simple functions at a finite positive exponent
statement:
  If $0<p<\infty$, every integrable planar simple function determines the
  same finite-support simple-function class in $L^p(\mathbb C)$.
-/
def integrableSimpleFuncToLpSimpleFunc
    (p : ℝ) (hp : 0 < p) (f : ℂ →₁ₛ[volume] ℂ) :
    Lp.simpleFunc ℂ (ENNReal.ofReal p) (volume : Measure ℂ) :=
  (Lp.simpleFunc.toSimpleFunc f).toLp <| by
    rw [SimpleFunc.memLp_iff_integrable
      (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top]
    exact L1.SimpleFunc.integrable f

/--
%%handwave
name:
  Representative of an integrable simple function at exponent $p$
statement:
  The $L^p$ simple-function class obtained from an integrable simple
  function has the same representative almost everywhere.
proof:
  Both classes are constructed from the same finite-range representative.
-/
theorem integrableSimpleFuncToLpSimpleFunc_coeFn
    (p : ℝ) (hp : 0 < p) (f : ℂ →₁ₛ[volume] ℂ) :
    ((integrableSimpleFuncToLpSimpleFunc p hp f :
        Lp ℂ (ENNReal.ofReal p) (volume : Measure ℂ)) : ℂ → ℂ) =ᵐ[volume]
      (f : ℂ → ℂ) := by
  let hfp :
      MemLp (Lp.simpleFunc.toSimpleFunc f : ℂ → ℂ)
        (ENNReal.ofReal p) volume := by
    rw [SimpleFunc.memLp_iff_integrable
      (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top]
    exact L1.SimpleFunc.integrable f
  exact (Lp.simpleFunc.toSimpleFunc_eq_toFun
      (integrableSimpleFuncToLpSimpleFunc p hp f)).symm.trans <|
    (Lp.simpleFunc.toSimpleFunc_toLp
      (Lp.simpleFunc.toSimpleFunc f) hfp).trans <|
        Lp.simpleFunc.toSimpleFunc_eq_toFun f

/--
%%handwave
name:
  Norm of an integrable simple function at exponent $p$
statement:
  For $p>0$, the norm of the $L^p$ simple-function class associated with
  $f$ is its $L^p$ seminorm:
  $$
    \|[f]_p\|_{L^p}=\|f\|_{L^p}.
  $$
proof:
  The two representatives agree almost everywhere.
-/
theorem norm_integrableSimpleFuncToLpSimpleFunc
    (p : ℝ) (hp : 0 < p) (f : ℂ →₁ₛ[volume] ℂ) :
    ‖(integrableSimpleFuncToLpSimpleFunc p hp f :
        Lp ℂ (ENNReal.ofReal p) (volume : Measure ℂ))‖ =
      lpNorm (f : ℂ → ℂ) (ENNReal.ofReal p) volume := by
  calc
    ‖(integrableSimpleFuncToLpSimpleFunc p hp f :
        Lp ℂ (ENNReal.ofReal p) (volume : Measure ℂ))‖ =
        (eLpNorm
          ((integrableSimpleFuncToLpSimpleFunc p hp f :
            Lp ℂ (ENNReal.ofReal p) (volume : Measure ℂ)) : ℂ → ℂ)
          (ENNReal.ofReal p) volume).toReal := Lp.norm_def _
    _ = (eLpNorm (f : ℂ → ℂ) (ENNReal.ofReal p) volume).toReal :=
      congrArg ENNReal.toReal
        (eLpNorm_congr_ae
          (integrableSimpleFuncToLpSimpleFunc_coeFn p hp f))
    _ = lpNorm (f : ℂ → ℂ) (ENNReal.ofReal p) volume :=
      toReal_eLpNorm
        (HarmonicAnalysis.memLp_integrableSimpleFunc
          (volume : Measure ℂ) hp f).aestronglyMeasurable

/--
%%handwave
name:
  Reconstruction of the original $L^1$ class
statement:
  Let $p>0$. If an integrable simple function is first regarded as an
  $L^p$ simple function and then included back into $L^1$, the resulting
  $L^1$ class is the original one.
proof:
  Both $L^1$ classes have representatives equal almost everywhere to the
  same integrable simple function.
-/
theorem simpleFuncToL1_integrableSimpleFuncToLpSimpleFunc
    (p : ℝ) (hp : 0 < p) (f : ℂ →₁ₛ[volume] ℂ) :
    simpleFuncToL1LinearMap (volume : Measure ℂ) (ENNReal.ofReal p)
        (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top
        (integrableSimpleFuncToLpSimpleFunc p hp f) =
      (f : ℂ →₁[volume] ℂ) := by
  apply Lp.ext
  filter_upwards [
    (integrable_simpleFunc_toSimpleFunc
      (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top
      (integrableSimpleFuncToLpSimpleFunc p hp f)).coeFn_toL1,
    Lp.simpleFunc.toSimpleFunc_eq_toFun
      (integrableSimpleFuncToLpSimpleFunc p hp f),
    integrableSimpleFuncToLpSimpleFunc_coeFn p hp f] with z hL1 hsimple hfp
  change
    (((integrable_simpleFunc_toSimpleFunc
      (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top
      (integrableSimpleFuncToLpSimpleFunc p hp f)).toL1
        (Lp.simpleFunc.toSimpleFunc
          (integrableSimpleFuncToLpSimpleFunc p hp f))) : ℂ → ℂ) z =
      (f : ℂ → ℂ) z
  rw [hL1, hsimple, hfp]

/--
%%handwave
name:
  Exact Beurling bilinear pairing on the integrable simple core
statement:
  For integrable planar simple functions $f,g$, define
  $$
    B_{\mathcal S}(f,g)
      =\int_{\mathbb C}(\mathcal S_2f)(z)g(z)\,dz,
  $$
  where $\mathcal S_2$ is the exact Fourier-multiplier Beurling transform
  on $L^2$.
-/
def beurlingL2SimpleBilinearPairing :
    (ℂ →₁ₛ[volume] ℂ) →ₗ[ℂ] ((ℂ →₁ₛ[volume] ℂ) →ₗ[ℂ] ℂ) where
  toFun f :=
    { toFun := fun g ↦
        planeL2BilinearPairing
          (beurlingTransformL2
            (integrableSimpleFuncToPlaneL2LinearMap f))
          (integrableSimpleFuncToPlaneL2LinearMap g)
      map_add' := by
        intro g h
        simp
      map_smul' := by
        intro c g
        simp }
  map_add' := by
    intro f g
    ext h
    simp only [map_add, LinearMap.add_apply]
    rfl
  map_smul' := by
    intro c f
    ext g
    simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply]
    rfl

/--
%%handwave
name:
  $L^2$ endpoint bound for the exact Beurling pairing
statement:
  For integrable planar simple functions $f,g$,
  $$
    |B_{\mathcal S}(f,g)|\leq
      \|f\|_{L^2}\|g\|_{L^2}.
  $$
proof:
  The exact Beurling transform is an isometry on $L^2$, and Hölder's
  inequality bounds the bilinear integral pairing.
-/
theorem norm_beurlingL2SimpleBilinearPairing_le
    (f g : ℂ →₁ₛ[volume] ℂ) :
    ‖beurlingL2SimpleBilinearPairing f g‖ ≤
      lpNorm (f : ℂ → ℂ) 2 volume *
        lpNorm (g : ℂ → ℂ) 2 volume := by
  let f₂ : PlaneL2 := integrableSimpleFuncToPlaneL2LinearMap f
  let g₂ : PlaneL2 := integrableSimpleFuncToPlaneL2LinearMap g
  calc
    ‖beurlingL2SimpleBilinearPairing f g‖ =
        ‖∫ z, (beurlingTransformL2 f₂ : ℂ → ℂ) z * g₂ z‖ := by
      change ‖planeL2BilinearPairing
          (beurlingTransformL2 f₂) g₂‖ =
        ‖∫ z, (beurlingTransformL2 f₂ : ℂ → ℂ) z * g₂ z‖
      rw [planeL2BilinearPairing_eq_integral]
    _ ≤ lpNorm (beurlingTransformL2 f₂ : ℂ → ℂ) 2 volume *
          lpNorm (g₂ : ℂ → ℂ) 2 volume :=
      by
        have hTf :
            MemLp (beurlingTransformL2 f₂ : ℂ → ℂ)
              (ENNReal.ofReal 2) volume := by
          simpa using Lp.memLp (beurlingTransformL2 f₂)
        have hg₂ :
            MemLp (g₂ : ℂ → ℂ) (ENNReal.ofReal 2) volume := by
          simpa using Lp.memLp g₂
        simpa using
          norm_integral_mul_le_lpNorm_mul_lpNorm
            Real.HolderConjugate.two_two
            hTf hg₂
    _ = ‖beurlingTransformL2 f₂‖ * ‖g₂‖ := by
      rw [← toReal_eLpNorm
          (Lp.memLp (beurlingTransformL2 f₂)).aestronglyMeasurable,
        ← toReal_eLpNorm (Lp.memLp g₂).aestronglyMeasurable,
        ← Lp.norm_def, ← Lp.norm_def]
    _ = ‖f₂‖ * ‖g₂‖ := by
      rw [norm_beurlingTransformL2_apply]
    _ = lpNorm (f : ℂ → ℂ) 2 volume *
          lpNorm (g : ℂ → ℂ) 2 volume := by
      change ‖integrableSimpleFuncToPlaneL2 f‖ *
          ‖integrableSimpleFuncToPlaneL2 g‖ =
        lpNorm (f : ℂ → ℂ) 2 volume *
          lpNorm (g : ℂ → ℂ) 2 volume
      rw [norm_integrableSimpleFuncToPlaneL2,
        norm_integrableSimpleFuncToPlaneL2]

/--
%%handwave
name:
  Above-two and exact Beurling transforms agree on the integrable simple core
statement:
  Let $p$ and $q$ be Hölder conjugate with $1<p<2\leq q$. If an
  integrable planar simple function $f$ is regarded as an $L^q$ simple
  function, then
  $$
    \mathcal S_qf=\mathcal S_2f
    \quad\text{almost everywhere}.
  $$
proof:
  The existing dense-core compatibility theorem applies to the $L^q$
  simple-function class. Its reconstructed $L^1$ class is the original
  integrable simple function, and the resulting $L^2$ class is the canonical
  $L^2$ inclusion of that same function.
-/
theorem beurlingTransformLpAbove_integrableSimpleFunc_ae_eq_beurlingTransformL2
    (p q : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    [Fact (1 ≤ ENNReal.ofReal q)]
    (hpq : p.HolderConjugate q) (hp2 : p < 2) (hq2 : 2 ≤ q)
    (f : ℂ →₁ₛ[volume] ℂ) :
    (beurlingTransformLpAbove p q hpq hp2 hq2
        (integrableSimpleFuncToLpSimpleFunc q hpq.symm.pos f :
          Lp ℂ (ENNReal.ofReal q) (volume : Measure ℂ)) : ℂ → ℂ)
      =ᵐ[volume]
        (beurlingTransformL2
          (integrableSimpleFuncToPlaneL2LinearMap f) : ℂ → ℂ) := by
  let F : Lp.simpleFunc ℂ (ENNReal.ofReal q) (volume : Measure ℂ) :=
    integrableSimpleFuncToLpSimpleFunc q hpq.symm.pos f
  let F₁ : ℂ →₁[volume] ℂ :=
    simpleFuncToL1LinearMap (volume : Measure ℂ) (ENNReal.ofReal q)
      (ENNReal.ofReal_ne_zero_iff.mpr hpq.symm.pos)
      ENNReal.ofReal_ne_top F
  let hF₂ : MemLp (F₁ : ℂ → ℂ) 2 volume :=
    memLp_two_simpleFuncToL1LinearMap (volume : Measure ℂ)
      (ENNReal.ofReal q)
      (ENNReal.ofReal_ne_zero_iff.mpr hpq.symm.pos)
      ENNReal.ofReal_ne_top F
  have hF₁ : F₁ = (f : ℂ →₁[volume] ℂ) := by
    simpa only [F₁, F] using
      simpleFuncToL1_integrableSimpleFuncToLpSimpleFunc
        q hpq.symm.pos f
  have hF₂class :
      hF₂.toLp (F₁ : ℂ → ℂ) =
        integrableSimpleFuncToPlaneL2LinearMap f := by
    apply Lp.ext
    filter_upwards [hF₂.coeFn_toLp,
      integrableSimpleFuncToPlaneL2_coeFn f] with z htoLp hf
    calc
      (hF₂.toLp (F₁ : ℂ → ℂ) : ℂ → ℂ) z = F₁ z := htoLp
      _ = (f : ℂ → ℂ) z := by rw [hF₁]
      _ = (integrableSimpleFuncToPlaneL2LinearMap f : ℂ → ℂ) z := hf.symm
  have hcompat :=
    beurlingTransformLpAbove_apply_simpleFunc_ae_eq_beurlingTransformL2
      p q hpq hp2 hq2 F
  dsimp only at hcompat
  change
    (beurlingTransformLpAbove p q hpq hp2 hq2
        (F : Lp ℂ (ENNReal.ofReal q) (volume : Measure ℂ)) : ℂ → ℂ)
      =ᵐ[volume]
        (beurlingTransformL2
          (hF₂.toLp (F₁ : ℂ → ℂ)) : ℂ → ℂ) at hcompat
  rw [hF₂class] at hcompat
  exact hcompat

/--
%%handwave
name:
  Above-two endpoint bound for the exact Beurling pairing
statement:
  Let $p$ and $q$ be Hölder conjugate with $1<p<2\leq q$. For integrable
  planar simple functions $f,g$,
  $$
    |B_{\mathcal S}(f,g)|\leq
      A_p\|f\|_{L^q}\|g\|_{L^p},
  $$
  where $A_p$ is the established norm bound for the completed $L^q$
  Beurling transform.
proof:
  On the common simple core the exact $L^2$ transform agrees with the
  completed $L^q$ transform. Replace the first factor in the bilinear
  integral by that completion, apply Hölder's inequality, and use its
  operator norm bound.
-/
theorem norm_beurlingL2SimpleBilinearPairing_above_le
    (p q : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    [Fact (1 ≤ ENNReal.ofReal q)]
    (hpq : p.HolderConjugate q) (hp2 : p < 2) (hq2 : 2 ≤ q)
    (f g : ℂ →₁ₛ[volume] ℂ) :
    ‖beurlingL2SimpleBilinearPairing f g‖ ≤
      (beurlingInterpolationNorm p).toReal *
        lpNorm (f : ℂ → ℂ) (ENNReal.ofReal q) volume *
          lpNorm (g : ℂ → ℂ) (ENNReal.ofReal p) volume := by
  let F : Lp.simpleFunc ℂ (ENNReal.ofReal q) (volume : Measure ℂ) :=
    integrableSimpleFuncToLpSimpleFunc q hpq.symm.pos f
  let f₂ : PlaneL2 := integrableSimpleFuncToPlaneL2LinearMap f
  let g₂ : PlaneL2 := integrableSimpleFuncToPlaneL2LinearMap g
  let TF : Lp ℂ (ENNReal.ofReal q) (volume : Measure ℂ) :=
    beurlingTransformLpAbove p q hpq hp2 hq2
      (F : Lp ℂ (ENNReal.ofReal q) (volume : Measure ℂ))
  have hcompat :
      (TF : ℂ → ℂ) =ᵐ[volume]
        (beurlingTransformL2 f₂ : ℂ → ℂ) := by
    exact
      beurlingTransformLpAbove_integrableSimpleFunc_ae_eq_beurlingTransformL2
        p q hpq hp2 hq2 f
  have hg_mem :
      MemLp (g : ℂ → ℂ) (ENNReal.ofReal p) volume :=
    HarmonicAnalysis.memLp_integrableSimpleFunc
      (volume : Measure ℂ) hpq.pos g
  calc
    ‖beurlingL2SimpleBilinearPairing f g‖ =
        ‖∫ z, (beurlingTransformL2 f₂ : ℂ → ℂ) z * g₂ z‖ := by
      change ‖planeL2BilinearPairing
          (beurlingTransformL2 f₂) g₂‖ =
        ‖∫ z, (beurlingTransformL2 f₂ : ℂ → ℂ) z * g₂ z‖
      rw [planeL2BilinearPairing_eq_integral]
    _ = ‖∫ z, (TF : ℂ → ℂ) z * (g : ℂ → ℂ) z‖ := by
      congr 1
      apply integral_congr_ae
      exact hcompat.symm.mul (integrableSimpleFuncToPlaneL2_coeFn g)
    _ ≤ lpNorm (TF : ℂ → ℂ) (ENNReal.ofReal q) volume *
          lpNorm (g : ℂ → ℂ) (ENNReal.ofReal p) volume :=
      norm_integral_mul_le_lpNorm_mul_lpNorm hpq.symm
        (Lp.memLp TF) hg_mem
    _ = ‖TF‖ * lpNorm (g : ℂ → ℂ) (ENNReal.ofReal p) volume := by
      rw [← toReal_eLpNorm (Lp.memLp TF).aestronglyMeasurable,
        ← Lp.norm_def]
    _ ≤ ((beurlingInterpolationNorm p).toReal *
          ‖(F : Lp ℂ (ENNReal.ofReal q) (volume : Measure ℂ))‖) *
          lpNorm (g : ℂ → ℂ) (ENNReal.ofReal p) volume := by
      apply mul_le_mul_of_nonneg_right
        (norm_beurlingTransformLpAbove_le p q hpq hp2 hq2
          (F : Lp ℂ (ENNReal.ofReal q) (volume : Measure ℂ)))
      exact lpNorm_nonneg
    _ = (beurlingInterpolationNorm p).toReal *
          lpNorm (f : ℂ → ℂ) (ENNReal.ofReal q) volume *
          lpNorm (g : ℂ → ℂ) (ENNReal.ofReal p) volume := by
      rw [norm_integrableSimpleFuncToLpSimpleFunc q hpq.symm.pos f]

/--
%%handwave
name:
  Interpolated Beurling pairing bound on the common simple core
statement:
  Let $p$ and $q$ be Hölder conjugate with $1<p<2\leq q$. Suppose
  $0\leq\theta\leq1$ and
  $$
    \frac1r=\frac{1-\theta}{2}+\frac\theta q,
    \qquad
    \frac1s=\frac{1-\theta}{2}+\frac\theta p.
  $$
  Then integrable planar simple functions satisfy
  $$
    |B_{\mathcal S}(f,g)|\leq
      A_p^\theta\|f\|_{L^r}\|g\|_{L^s}.
  $$
proof:
  Apply the bilinear simple-core Riesz--Thorin theorem to the exact
  $L^2\times L^2$ endpoint with constant one and the
  $L^q\times L^p$ endpoint with constant $A_p$.
-/
theorem norm_beurlingL2SimpleBilinearPairing_interpolation_le
    (p q : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    [Fact (1 ≤ ENNReal.ofReal q)]
    (hpq : p.HolderConjugate q) (hp2 : p < 2) (hq2 : 2 ≤ q)
    {r s θ : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hr_interp : r⁻¹ = (1 - θ) / 2 + θ / q)
    (hs_interp : s⁻¹ = (1 - θ) / 2 + θ / p)
    (f g : ℂ →₁ₛ[volume] ℂ) :
    ‖beurlingL2SimpleBilinearPairing f g‖ ≤
      (beurlingInterpolationNorm p).toReal ^ θ *
        lpNorm (f : ℂ → ℂ) (ENNReal.ofReal r) volume *
          lpNorm (g : ℂ → ℂ) (ENNReal.ofReal s) volume := by
  have hinterp := HarmonicAnalysis.norm_bilinearMap_le
    (volume : Measure ℂ) (volume : Measure ℂ)
    beurlingL2SimpleBilinearPairing
    hr zero_lt_two hpq.symm.pos hs zero_lt_two hpq.pos
    hθ zero_le_one ENNReal.toReal_nonneg
    hr_interp hs_interp
    (fun u v ↦ by
      simpa only [ENNReal.ofReal_ofNat, one_mul] using
        norm_beurlingL2SimpleBilinearPairing_le u v)
    (fun u v ↦
      norm_beurlingL2SimpleBilinearPairing_above_le
        p q hpq hp2 hq2 u v)
    f g
  simpa only [Real.one_rpow, one_mul] using hinterp

/--
%%handwave
name:
  Weak and exact Beurling transforms agree on the integrable simple core
statement:
  For every integrable planar simple function $f$,
  $$
    \mathcal S_1f=\mathcal S_2f
    \quad\text{almost everywhere},
  $$
  where the right side uses the canonical $L^2$ inclusion of $f$.
proof:
  Integrable simple functions are square-integrable. Apply compatibility of
  the weak extension with the Fourier-multiplier transform and identify the
  $L^1$ and $L^2$ classes reconstructed from the representative with the
  original canonical classes.
-/
theorem beurlingTransformL1_integrableSimpleFunc_ae_eq_beurlingTransformL2
    (f : ℂ →₁ₛ[volume] ℂ) :
    (beurlingTransformL1 (f : ℂ →₁[volume] ℂ) : ℂ → ℂ)
      =ᵐ[volume]
        (beurlingTransformL2
          (integrableSimpleFuncToPlaneL2LinearMap f) : ℂ → ℂ) := by
  let hf₂ : MemLp (f : ℂ → ℂ) 2 volume := by
    simpa using
      HarmonicAnalysis.memLp_integrableSimpleFunc
        (volume : Measure ℂ) zero_lt_two f
  let hf₁ : MemLp (f : ℂ → ℂ) 1 volume :=
    memLp_one_iff_integrable.mpr
      (L1.integrable_coeFn (f : ℂ →₁[volume] ℂ))
  have hf₁class :
      hf₁.toLp (f : ℂ → ℂ) = (f : ℂ →₁[volume] ℂ) :=
    Lp.toLp_coeFn (f : ℂ →₁[volume] ℂ) hf₁
  have hf₂class :
      hf₂.toLp (f : ℂ → ℂ) =
        integrableSimpleFuncToPlaneL2LinearMap f := by
    apply Lp.ext
    filter_upwards [hf₂.coeFn_toLp,
      integrableSimpleFuncToPlaneL2_coeFn f] with z htoLp hf
    exact htoLp.trans hf.symm
  have hcompat :=
    beurlingTransformL1_ae_eq_beurlingTransformL2
      (f : ℂ → ℂ)
      (L1.integrable_coeFn (f : ℂ →₁[volume] ℂ)) hf₂
  dsimp only at hcompat
  rw [hf₁class, hf₂class] at hcompat
  exact hcompat

/--
%%handwave
name:
  Interpolated strong Beurling bound for integrable simple inputs
statement:
  Let $p$ and $q$ be Hölder conjugate with $1<p<2\leq q$, let $s$ and
  $r\geq2$ be Hölder conjugate, and suppose
  $$
    \frac1r=\frac{1-\theta}{2}+\frac\theta q,
    \qquad 0\leq\theta\leq1.
  $$
  Then the weak transform of every integrable planar simple function belongs
  to $L^r$ and satisfies
  $$
    \|\mathcal S f\|_{L^r}
      \leq A_p^\theta\|f\|_{L^r}.
  $$
proof:
  The conjugacy identities imply
  $1/s=(1-\theta)/2+\theta/p$. Apply the interpolated bilinear estimate
  against every finite-support $L^s$ simple test and then use quantitative
  $L^r$ duality.
-/
theorem memLp_and_lpNorm_beurlingTransformL1_integrableSimpleFunc_interpolation_le
    (p q : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    [Fact (1 ≤ ENNReal.ofReal q)]
    (hpq : p.HolderConjugate q) (hp2 : p < 2) (hq2 : 2 ≤ q)
    {r s θ : ℝ} (hrs : s.HolderConjugate r) (hr2 : 2 ≤ r)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hr_interp : r⁻¹ = (1 - θ) / 2 + θ / q)
    (f : ℂ →₁ₛ[volume] ℂ) :
    MemLp
        (beurlingTransformL1 (f : ℂ →₁[volume] ℂ) : ℂ → ℂ)
        (ENNReal.ofReal r) volume ∧
      lpNorm
          (beurlingTransformL1 (f : ℂ →₁[volume] ℂ) : ℂ → ℂ)
          (ENNReal.ofReal r) volume ≤
        (beurlingInterpolationNorm p).toReal ^ θ *
          lpNorm (f : ℂ → ℂ) (ENNReal.ofReal r) volume := by
  have hs_interp : s⁻¹ = (1 - θ) / 2 + θ / p := by
    calc
      s⁻¹ = 1 - r⁻¹ := by
        linarith [hrs.inv_add_inv_eq_one]
      _ = 1 - ((1 - θ) / 2 + θ / q) := by rw [hr_interp]
      _ = (1 - θ) / 2 + θ / p := by
        simp only [div_eq_mul_inv]
        rw [← hpq.symm.one_sub_inv]
        ring
  apply HarmonicAnalysis.memLp_and_lpNorm_le_of_simpleFunc_pairing
    hrs hr2
    (beurlingTransformL1
      (f : ℂ →₁[volume] ℂ)).stronglyMeasurable
    (mul_nonneg
      (Real.rpow_nonneg ENNReal.toReal_nonneg θ) lpNorm_nonneg)
  intro t ht
  have ht_integrable : Integrable (t : ℂ → ℂ) volume := by
    rw [← SimpleFunc.memLp_iff_integrable
      (ENNReal.ofReal_ne_zero_iff.mpr hrs.pos)
      ENNReal.ofReal_ne_top]
    exact ht
  let ht₁ : MemLp (t : ℂ → ℂ) 1 volume :=
    memLp_one_iff_integrable.mpr ht_integrable
  let g : ℂ →₁ₛ[volume] ℂ := t.toLp ht₁
  have hgcoe : (g : ℂ → ℂ) =ᵐ[volume] (t : ℂ → ℂ) := by
    exact (Lp.simpleFunc.toSimpleFunc_eq_toFun g).symm.trans <|
      Lp.simpleFunc.toSimpleFunc_toLp t ht₁
  have hgnorm :
      lpNorm (g : ℂ → ℂ) (ENNReal.ofReal s) volume =
        lpNorm (t : ℂ → ℂ) (ENNReal.ofReal s) volume := by
    rw [← toReal_eLpNorm
        (HarmonicAnalysis.memLp_integrableSimpleFunc
          (volume : Measure ℂ) hrs.pos g).aestronglyMeasurable,
      ← toReal_eLpNorm ht.aestronglyMeasurable,
      eLpNorm_congr_ae hgcoe]
  have hpair :
      (∫ z,
        (beurlingTransformL1 (f : ℂ →₁[volume] ℂ) : ℂ → ℂ) z *
          t z) =
        beurlingL2SimpleBilinearPairing f g := by
    change
      (∫ z,
        (beurlingTransformL1 (f : ℂ →₁[volume] ℂ) : ℂ → ℂ) z *
          t z) =
        planeL2BilinearPairing
          (beurlingTransformL2
            (integrableSimpleFuncToPlaneL2LinearMap f))
          (integrableSimpleFuncToPlaneL2LinearMap g)
    rw [planeL2BilinearPairing_eq_integral]
    apply integral_congr_ae
    exact
      (beurlingTransformL1_integrableSimpleFunc_ae_eq_beurlingTransformL2 f).mul
        ((integrableSimpleFuncToPlaneL2_coeFn g).trans hgcoe).symm
  calc
    ‖∫ z,
        (beurlingTransformL1 (f : ℂ →₁[volume] ℂ) : ℂ → ℂ) z *
          t z‖ =
        ‖beurlingL2SimpleBilinearPairing f g‖ :=
      congrArg norm hpair
    _ ≤ (beurlingInterpolationNorm p).toReal ^ θ *
          lpNorm (f : ℂ → ℂ) (ENNReal.ofReal r) volume *
          lpNorm (g : ℂ → ℂ) (ENNReal.ofReal s) volume :=
      norm_beurlingL2SimpleBilinearPairing_interpolation_le
        p q hpq hp2 hq2 hrs.symm.pos hrs.pos hθ
        hr_interp hs_interp f g
    _ = ((beurlingInterpolationNorm p).toReal ^ θ *
          lpNorm (f : ℂ → ℂ) (ENNReal.ofReal r) volume) *
          lpNorm (t : ℂ → ℂ) (ENNReal.ofReal s) volume := by
      rw [hgnorm]

/--
%%handwave
name:
  Finite-support $L^r$ simple functions on the integrable simple core
statement:
  If $r>0$, every finite-support planar $L^r$ simple function determines
  the same simple-function class in $L^1$.
-/
def lpSimpleFuncToIntegrableSimpleFunc
    (r : ℝ) (hr : 0 < r)
    (F : Lp.simpleFunc ℂ (ENNReal.ofReal r) (volume : Measure ℂ)) :
    ℂ →₁ₛ[volume] ℂ :=
  (Lp.simpleFunc.toSimpleFunc F).toLp <|
    memLp_one_iff_integrable.mpr <|
      integrable_simpleFunc_toSimpleFunc
        (ENNReal.ofReal_ne_zero_iff.mpr hr) ENNReal.ofReal_ne_top F

/--
%%handwave
name:
  Representative of the integrable simple-core inclusion
statement:
  The integrable simple-function class associated with a finite-support
  $L^r$ simple function has the same representative almost everywhere.
proof:
  Both classes are constructed from the same chosen simple representative.
-/
theorem lpSimpleFuncToIntegrableSimpleFunc_coeFn
    (r : ℝ) (hr : 0 < r)
    (F : Lp.simpleFunc ℂ (ENNReal.ofReal r) (volume : Measure ℂ)) :
    (lpSimpleFuncToIntegrableSimpleFunc r hr F : ℂ → ℂ) =ᵐ[volume]
      (F : ℂ → ℂ) := by
  let hF₁ : MemLp (Lp.simpleFunc.toSimpleFunc F : ℂ → ℂ) 1 volume :=
    memLp_one_iff_integrable.mpr <|
      integrable_simpleFunc_toSimpleFunc
        (ENNReal.ofReal_ne_zero_iff.mpr hr) ENNReal.ofReal_ne_top F
  exact (Lp.simpleFunc.toSimpleFunc_eq_toFun
      (lpSimpleFuncToIntegrableSimpleFunc r hr F)).symm.trans <|
    (Lp.simpleFunc.toSimpleFunc_toLp
      (Lp.simpleFunc.toSimpleFunc F) hF₁).trans <|
        Lp.simpleFunc.toSimpleFunc_eq_toFun F

/--
%%handwave
name:
  Equality with the standard simple-function inclusion into $L^1$
statement:
  The integrable simple-core inclusion and the standard inclusion of a
  finite-support $L^r$ simple function into $L^1$ determine the same
  $L^1$ class.
proof:
  Their representatives agree almost everywhere with the original
  finite-support simple function.
-/
theorem lpSimpleFuncToIntegrableSimpleFunc_toL1
    (r : ℝ) (hr : 0 < r)
    (F : Lp.simpleFunc ℂ (ENNReal.ofReal r) (volume : Measure ℂ)) :
    (lpSimpleFuncToIntegrableSimpleFunc r hr F : ℂ →₁[volume] ℂ) =
      simpleFuncToL1LinearMap (volume : Measure ℂ) (ENNReal.ofReal r)
        (ENNReal.ofReal_ne_zero_iff.mpr hr) ENNReal.ofReal_ne_top F := by
  apply Lp.ext
  filter_upwards [
    lpSimpleFuncToIntegrableSimpleFunc_coeFn r hr F,
    (integrable_simpleFunc_toSimpleFunc
      (ENNReal.ofReal_ne_zero_iff.mpr hr) ENNReal.ofReal_ne_top F).coeFn_toL1,
    Lp.simpleFunc.toSimpleFunc_eq_toFun F] with z hcore hL1 hF
  exact hcore.trans (hF.symm.trans hL1.symm)

/--
%%handwave
name:
  Interpolated strong Beurling bound on finite-support $L^r$ simple functions
statement:
  Under the interpolation hypotheses, let $F$ be a finite-support planar
  $L^r$ simple function and let $F_1$ be the same function regarded as an
  $L^1$ class. Then
  $$
    \mathcal S_1F_1\in L^r,
    \qquad
    \|\mathcal S_1F_1\|_{L^r}
      \leq A_p^\theta\|F\|_{L^r}.
  $$
proof:
  Regard $F$ as an integrable simple-core function, apply the interpolated
  simple-input estimate, and use preservation of its $L^1$ class and
  $L^r$ norm.
-/
theorem memLp_and_lpNorm_beurlingTransformL1_lpSimpleFunc_interpolation_le
    (p q : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    [Fact (1 ≤ ENNReal.ofReal q)]
    (hpq : p.HolderConjugate q) (hp2 : p < 2) (hq2 : 2 ≤ q)
    (r s θ : ℝ) [Fact (1 ≤ ENNReal.ofReal r)]
    (hrs : s.HolderConjugate r) (hr2 : 2 ≤ r)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hr_interp : r⁻¹ = (1 - θ) / 2 + θ / q)
    (F : Lp.simpleFunc ℂ (ENNReal.ofReal r) (volume : Measure ℂ)) :
    let F₁ : ℂ →₁[volume] ℂ :=
      simpleFuncToL1LinearMap (volume : Measure ℂ) (ENNReal.ofReal r)
        (ENNReal.ofReal_ne_zero_iff.mpr hrs.symm.pos)
        ENNReal.ofReal_ne_top F
    MemLp (beurlingTransformL1 F₁ : ℂ → ℂ)
        (ENNReal.ofReal r) volume ∧
      lpNorm (beurlingTransformL1 F₁ : ℂ → ℂ)
          (ENNReal.ofReal r) volume ≤
        (beurlingInterpolationNorm p).toReal ^ θ * ‖F‖ := by
  dsimp only
  let Fcore : ℂ →₁ₛ[volume] ℂ :=
    lpSimpleFuncToIntegrableSimpleFunc r hrs.symm.pos F
  let F₁ : ℂ →₁[volume] ℂ :=
    simpleFuncToL1LinearMap (volume : Measure ℂ) (ENNReal.ofReal r)
      (ENNReal.ofReal_ne_zero_iff.mpr hrs.symm.pos)
      ENNReal.ofReal_ne_top F
  have hclass : (Fcore : ℂ →₁[volume] ℂ) = F₁ := by
    exact lpSimpleFuncToIntegrableSimpleFunc_toL1
      r hrs.symm.pos F
  have hbound :=
    memLp_and_lpNorm_beurlingTransformL1_integrableSimpleFunc_interpolation_le
      p q hpq hp2 hq2 hrs hr2 hθ hr_interp Fcore
  rw [hclass,
    lpNorm_simpleFuncToL1LinearMap_eq_norm
      (volume : Measure ℂ) (ENNReal.ofReal r)
      (ENNReal.ofReal_ne_zero_iff.mpr hrs.symm.pos)
      ENNReal.ofReal_ne_top F] at hbound
  exact hbound

/--
%%handwave
name:
  Interpolated Beurling transform of a finite-support simple function
statement:
  Under the interpolation hypotheses, regard a finite-support planar
  $L^r$ simple function as an $L^1$ function, apply the weak Beurling
  transform, and take the resulting $L^r$ class.
-/
def beurlingTransformLpInterpolatedSimpleFunc
    (p q : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    [Fact (1 ≤ ENNReal.ofReal q)]
    (hpq : p.HolderConjugate q) (hp2 : p < 2) (hq2 : 2 ≤ q)
    (r s θ : ℝ) [Fact (1 ≤ ENNReal.ofReal r)]
    (hrs : s.HolderConjugate r) (hr2 : 2 ≤ r)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hr_interp : r⁻¹ = (1 - θ) / 2 + θ / q)
    (F : Lp.simpleFunc ℂ (ENNReal.ofReal r) (volume : Measure ℂ)) :
    Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ) :=
  let F₁ : ℂ →₁[volume] ℂ :=
    simpleFuncToL1LinearMap (volume : Measure ℂ) (ENNReal.ofReal r)
      (ENNReal.ofReal_ne_zero_iff.mpr hrs.symm.pos)
      ENNReal.ofReal_ne_top F
  (memLp_and_lpNorm_beurlingTransformL1_lpSimpleFunc_interpolation_le
    p q hpq hp2 hq2 r s θ hrs hr2 hθ hr_interp F).1.toLp
      (beurlingTransformL1 F₁ : ℂ → ℂ)

/--
%%handwave
name:
  Representative of the interpolated simple-function Beurling transform
statement:
  The function representative of the interpolated $L^r$ transform of a
  finite-support simple function agrees almost everywhere with its weak
  $L^1$ Beurling transform.
proof:
  This is the representative used to construct the resulting $L^r$ class.
-/
theorem beurlingTransformLpInterpolatedSimpleFunc_coeFn
    (p q : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    [Fact (1 ≤ ENNReal.ofReal q)]
    (hpq : p.HolderConjugate q) (hp2 : p < 2) (hq2 : 2 ≤ q)
    (r s θ : ℝ) [Fact (1 ≤ ENNReal.ofReal r)]
    (hrs : s.HolderConjugate r) (hr2 : 2 ≤ r)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hr_interp : r⁻¹ = (1 - θ) / 2 + θ / q)
    (F : Lp.simpleFunc ℂ (ENNReal.ofReal r) (volume : Measure ℂ)) :
    (beurlingTransformLpInterpolatedSimpleFunc
      p q hpq hp2 hq2 r s θ hrs hr2 hθ hr_interp F : ℂ → ℂ)
      =ᵐ[volume]
        (beurlingTransformL1
          (simpleFuncToL1LinearMap (volume : Measure ℂ)
            (ENNReal.ofReal r)
            (ENNReal.ofReal_ne_zero_iff.mpr hrs.symm.pos)
            ENNReal.ofReal_ne_top F) : ℂ → ℂ) := by
  dsimp only [beurlingTransformLpInterpolatedSimpleFunc]
  exact MemLp.coeFn_toLp _

/--
%%handwave
name:
  Additivity of the interpolated transform on simple functions
statement:
  Under the interpolation hypotheses, finite-support planar $L^r$ simple
  functions satisfy
  $$
    \mathcal S_r(F+G)=\mathcal S_rF+\mathcal S_rG.
  $$
proof:
  The inclusion into $L^1$ and the weak Beurling transform are additive,
  and the resulting representatives determine the same $L^r$ class.
-/
theorem beurlingTransformLpInterpolatedSimpleFunc_add
    (p q : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    [Fact (1 ≤ ENNReal.ofReal q)]
    (hpq : p.HolderConjugate q) (hp2 : p < 2) (hq2 : 2 ≤ q)
    (r s θ : ℝ) [Fact (1 ≤ ENNReal.ofReal r)]
    (hrs : s.HolderConjugate r) (hr2 : 2 ≤ r)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hr_interp : r⁻¹ = (1 - θ) / 2 + θ / q)
    (F G : Lp.simpleFunc ℂ (ENNReal.ofReal r) (volume : Measure ℂ)) :
    beurlingTransformLpInterpolatedSimpleFunc
        p q hpq hp2 hq2 r s θ hrs hr2 hθ hr_interp (F + G) =
      beurlingTransformLpInterpolatedSimpleFunc
          p q hpq hp2 hq2 r s θ hrs hr2 hθ hr_interp F +
        beurlingTransformLpInterpolatedSimpleFunc
          p q hpq hp2 hq2 r s θ hrs hr2 hθ hr_interp G := by
  let ι := simpleFuncToL1LinearMap (volume : Measure ℂ)
    (ENNReal.ofReal r) (ENNReal.ofReal_ne_zero_iff.mpr hrs.symm.pos)
    ENNReal.ofReal_ne_top
  have hT :
      (beurlingTransformL1 (ι (F + G)) : ℂ → ℂ) =ᵐ[volume]
        (beurlingTransformL1 (ι F) : ℂ → ℂ) +
          (beurlingTransformL1 (ι G) : ℂ → ℂ) := by
    rw [map_add, beurlingTransformL1_add]
    exact AEEqFun.coeFn_add _ _
  apply Lp.ext
  filter_upwards [
    beurlingTransformLpInterpolatedSimpleFunc_coeFn
      p q hpq hp2 hq2 r s θ hrs hr2 hθ hr_interp (F + G),
    beurlingTransformLpInterpolatedSimpleFunc_coeFn
      p q hpq hp2 hq2 r s θ hrs hr2 hθ hr_interp F,
    beurlingTransformLpInterpolatedSimpleFunc_coeFn
      p q hpq hp2 hq2 r s θ hrs hr2 hθ hr_interp G,
    Lp.coeFn_add
      (beurlingTransformLpInterpolatedSimpleFunc
        p q hpq hp2 hq2 r s θ hrs hr2 hθ hr_interp F)
      (beurlingTransformLpInterpolatedSimpleFunc
        p q hpq hp2 hq2 r s θ hrs hr2 hθ hr_interp G),
    hT] with z hsum hF hG hadd hTz
  exact hsum.trans
    (hTz.trans (hadd ▸ congrArg₂ (· + ·) hF.symm hG.symm))

/--
%%handwave
name:
  Complex homogeneity of the interpolated transform on simple functions
statement:
  Under the interpolation hypotheses, every $c\in\mathbb C$ and
  finite-support planar $L^r$ simple function $F$ satisfy
  $$
    \mathcal S_r(cF)=c\,\mathcal S_rF.
  $$
proof:
  The inclusion into $L^1$ and the weak Beurling transform are complex
  homogeneous, and the resulting representatives determine the same
  $L^r$ class.
-/
theorem beurlingTransformLpInterpolatedSimpleFunc_smul
    (p q : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    [Fact (1 ≤ ENNReal.ofReal q)]
    (hpq : p.HolderConjugate q) (hp2 : p < 2) (hq2 : 2 ≤ q)
    (r s θ : ℝ) [Fact (1 ≤ ENNReal.ofReal r)]
    (hrs : s.HolderConjugate r) (hr2 : 2 ≤ r)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hr_interp : r⁻¹ = (1 - θ) / 2 + θ / q)
    (c : ℂ)
    (F : Lp.simpleFunc ℂ (ENNReal.ofReal r) (volume : Measure ℂ)) :
    beurlingTransformLpInterpolatedSimpleFunc
        p q hpq hp2 hq2 r s θ hrs hr2 hθ hr_interp (c • F) =
      c • beurlingTransformLpInterpolatedSimpleFunc
        p q hpq hp2 hq2 r s θ hrs hr2 hθ hr_interp F := by
  let ι := simpleFuncToL1LinearMap (volume : Measure ℂ)
    (ENNReal.ofReal r) (ENNReal.ofReal_ne_zero_iff.mpr hrs.symm.pos)
    ENNReal.ofReal_ne_top
  have hT :
      (beurlingTransformL1 (ι (c • F)) : ℂ → ℂ) =ᵐ[volume]
        c • (beurlingTransformL1 (ι F) : ℂ → ℂ) := by
    rw [map_smul, beurlingTransformL1_smul]
    exact AEEqFun.coeFn_smul _ _
  apply Lp.ext
  filter_upwards [
    beurlingTransformLpInterpolatedSimpleFunc_coeFn
      p q hpq hp2 hq2 r s θ hrs hr2 hθ hr_interp (c • F),
    beurlingTransformLpInterpolatedSimpleFunc_coeFn
      p q hpq hp2 hq2 r s θ hrs hr2 hθ hr_interp F,
    Lp.coeFn_smul c
      (beurlingTransformLpInterpolatedSimpleFunc
        p q hpq hp2 hq2 r s θ hrs hr2 hθ hr_interp F),
    hT] with z hscaled hF hsmul hTz
  rw [hscaled, hTz, Pi.smul_apply, hsmul, Pi.smul_apply, hF]

/--
%%handwave
name:
  Linear interpolated Beurling transform on finite-support simple functions
statement:
  Under the interpolation hypotheses, the Beurling transform defines a
  complex-linear map
  $$
    \mathcal S_r:L^r_{\mathrm{simple}}(\mathbb C)
      \longrightarrow L^r(\mathbb C).
  $$
-/
def beurlingTransformLpInterpolatedSimpleFuncLinearMap
    (p q : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    [Fact (1 ≤ ENNReal.ofReal q)]
    (hpq : p.HolderConjugate q) (hp2 : p < 2) (hq2 : 2 ≤ q)
    (r s θ : ℝ) [Fact (1 ≤ ENNReal.ofReal r)]
    (hrs : s.HolderConjugate r) (hr2 : 2 ≤ r)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hr_interp : r⁻¹ = (1 - θ) / 2 + θ / q) :
    Lp.simpleFunc ℂ (ENNReal.ofReal r) (volume : Measure ℂ) →ₗ[ℂ]
      Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ) where
  toFun := beurlingTransformLpInterpolatedSimpleFunc
    p q hpq hp2 hq2 r s θ hrs hr2 hθ hr_interp
  map_add' := beurlingTransformLpInterpolatedSimpleFunc_add
    p q hpq hp2 hq2 r s θ hrs hr2 hθ hr_interp
  map_smul' := beurlingTransformLpInterpolatedSimpleFunc_smul
    p q hpq hp2 hq2 r s θ hrs hr2 hθ hr_interp

/--
%%handwave
name:
  Norm bound for the interpolated transform on simple functions
statement:
  Under the interpolation hypotheses, every finite-support planar $L^r$
  simple function satisfies
  $$
    \|\mathcal S_rF\|_{L^r}\leq A_p^\theta\|F\|_{L^r}.
  $$
proof:
  The chosen representative is the weak transform of the corresponding
  $L^1$ class. Apply the interpolated strong simple-function estimate and
  identify the norm of the resulting $L^r$ class with its seminorm.
-/
theorem norm_beurlingTransformLpInterpolatedSimpleFunc_le
    (p q : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    [Fact (1 ≤ ENNReal.ofReal q)]
    (hpq : p.HolderConjugate q) (hp2 : p < 2) (hq2 : 2 ≤ q)
    (r s θ : ℝ) [Fact (1 ≤ ENNReal.ofReal r)]
    (hrs : s.HolderConjugate r) (hr2 : 2 ≤ r)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hr_interp : r⁻¹ = (1 - θ) / 2 + θ / q)
    (F : Lp.simpleFunc ℂ (ENNReal.ofReal r) (volume : Measure ℂ)) :
    ‖beurlingTransformLpInterpolatedSimpleFunc
      p q hpq hp2 hq2 r s θ hrs hr2 hθ hr_interp F‖ ≤
        (beurlingInterpolationNorm p).toReal ^ θ * ‖F‖ := by
  let F₁ : ℂ →₁[volume] ℂ :=
    simpleFuncToL1LinearMap (volume : Measure ℂ) (ENNReal.ofReal r)
      (ENNReal.ofReal_ne_zero_iff.mpr hrs.symm.pos)
      ENNReal.ofReal_ne_top F
  have hmem :=
    (memLp_and_lpNorm_beurlingTransformL1_lpSimpleFunc_interpolation_le
      p q hpq hp2 hq2 r s θ hrs hr2 hθ hr_interp F).1
  calc
    ‖beurlingTransformLpInterpolatedSimpleFunc
        p q hpq hp2 hq2 r s θ hrs hr2 hθ hr_interp F‖ =
        lpNorm (beurlingTransformL1 F₁ : ℂ → ℂ)
          (ENNReal.ofReal r) volume := by
      rw [show beurlingTransformLpInterpolatedSimpleFunc
          p q hpq hp2 hq2 r s θ hrs hr2 hθ hr_interp F =
            hmem.toLp (beurlingTransformL1 F₁ : ℂ → ℂ) from rfl,
        Lp.norm_toLp, toReal_eLpNorm hmem.aestronglyMeasurable]
    _ ≤ (beurlingInterpolationNorm p).toReal ^ θ * ‖F‖ :=
      (memLp_and_lpNorm_beurlingTransformL1_lpSimpleFunc_interpolation_le
        p q hpq hp2 hq2 r s θ hrs hr2 hθ hr_interp F).2

/--
%%handwave
name:
  Completed interpolated Beurling transform
statement:
  Under the interpolation hypotheses, the bounded transform on
  finite-support $L^r$ simple functions extends uniquely to a continuous
  complex-linear map
  $$
    \mathcal S_r:L^r(\mathbb C)\longrightarrow L^r(\mathbb C).
  $$
-/
def beurlingTransformLpInterpolated
    (p q : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    [Fact (1 ≤ ENNReal.ofReal q)]
    (hpq : p.HolderConjugate q) (hp2 : p < 2) (hq2 : 2 ≤ q)
    (r s θ : ℝ) [Fact (1 ≤ ENNReal.ofReal r)]
    (hrs : s.HolderConjugate r) (hr2 : 2 ≤ r)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hr_interp : r⁻¹ = (1 - θ) / 2 + θ / q) :
    Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ) →L[ℂ]
      Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ) := by
  let T := beurlingTransformLpInterpolatedSimpleFuncLinearMap
    p q hpq hp2 hq2 r s θ hrs hr2 hθ hr_interp
  let e : Lp.simpleFunc ℂ (ENNReal.ofReal r) (volume : Measure ℂ) →ₗ[ℂ]
      Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ) :=
    (Lp.simpleFunc.coeToLp ℂ ℂ ℂ).toLinearMap
  exact T.extendOfNorm e

/--
%%handwave
name:
  Agreement of the completed interpolated transform on simple functions
statement:
  The completed interpolated $L^r$ Beurling transform agrees with its
  finite-support simple-function construction on every simple input.
proof:
  Extension of a bounded linear map agrees with that map on its dense
  simple-function domain.
-/
theorem beurlingTransformLpInterpolated_apply_simpleFunc
    (p q : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    [Fact (1 ≤ ENNReal.ofReal q)]
    (hpq : p.HolderConjugate q) (hp2 : p < 2) (hq2 : 2 ≤ q)
    (r s θ : ℝ) [Fact (1 ≤ ENNReal.ofReal r)]
    (hrs : s.HolderConjugate r) (hr2 : 2 ≤ r)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hr_interp : r⁻¹ = (1 - θ) / 2 + θ / q)
    (F : Lp.simpleFunc ℂ (ENNReal.ofReal r) (volume : Measure ℂ)) :
    beurlingTransformLpInterpolated
        p q hpq hp2 hq2 r s θ hrs hr2 hθ hr_interp
        (F : Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ)) =
      beurlingTransformLpInterpolatedSimpleFunc
        p q hpq hp2 hq2 r s θ hrs hr2 hθ hr_interp F := by
  let T := beurlingTransformLpInterpolatedSimpleFuncLinearMap
    p q hpq hp2 hq2 r s θ hrs hr2 hθ hr_interp
  let e : Lp.simpleFunc ℂ (ENNReal.ofReal r) (volume : Measure ℂ) →ₗ[ℂ]
      Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ) :=
    (Lp.simpleFunc.coeToLp ℂ ℂ ℂ).toLinearMap
  have hdense : DenseRange e :=
    Lp.simpleFunc.denseRange ENNReal.ofReal_ne_top
  have hbound : ∀ G,
      ‖T G‖ ≤ (beurlingInterpolationNorm p).toReal ^ θ * ‖G‖ :=
    norm_beurlingTransformLpInterpolatedSimpleFunc_le
      p q hpq hp2 hq2 r s θ hrs hr2 hθ hr_interp
  change T.extendOfNorm e (e F) = T F
  exact LinearMap.extendOfNorm_eq hdense
    ⟨(beurlingInterpolationNorm p).toReal ^ θ, hbound⟩ F

/--
%%handwave
name:
  Norm bound for the completed interpolated Beurling transform
statement:
  Under the interpolation hypotheses, every $F\in L^r(\mathbb C)$
  satisfies
  $$
    \|\mathcal S_rF\|_{L^r}
      \leq A_p^\theta\|F\|_{L^r}.
  $$
proof:
  The estimate holds on the dense finite-support simple subspace, and the
  bounded extension preserves the same norm bound.
-/
theorem norm_beurlingTransformLpInterpolated_le
    (p q : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    [Fact (1 ≤ ENNReal.ofReal q)]
    (hpq : p.HolderConjugate q) (hp2 : p < 2) (hq2 : 2 ≤ q)
    (r s θ : ℝ) [Fact (1 ≤ ENNReal.ofReal r)]
    (hrs : s.HolderConjugate r) (hr2 : 2 ≤ r)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hr_interp : r⁻¹ = (1 - θ) / 2 + θ / q)
    (F : Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ)) :
    ‖beurlingTransformLpInterpolated
      p q hpq hp2 hq2 r s θ hrs hr2 hθ hr_interp F‖ ≤
        (beurlingInterpolationNorm p).toReal ^ θ * ‖F‖ := by
  let T := beurlingTransformLpInterpolatedSimpleFuncLinearMap
    p q hpq hp2 hq2 r s θ hrs hr2 hθ hr_interp
  let e : Lp.simpleFunc ℂ (ENNReal.ofReal r) (volume : Measure ℂ) →ₗ[ℂ]
      Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ) :=
    (Lp.simpleFunc.coeToLp ℂ ℂ ℂ).toLinearMap
  have hdense : DenseRange e :=
    Lp.simpleFunc.denseRange ENNReal.ofReal_ne_top
  have hbound : ∀ G,
      ‖T G‖ ≤ (beurlingInterpolationNorm p).toReal ^ θ * ‖G‖ :=
    norm_beurlingTransformLpInterpolatedSimpleFunc_le
      p q hpq hp2 hq2 r s θ hrs hr2 hθ hr_interp
  change ‖T.extendOfNorm e F‖ ≤
    (beurlingInterpolationNorm p).toReal ^ θ * ‖F‖
  exact LinearMap.norm_extendOfNorm_apply_le
    hdense
    ((beurlingInterpolationNorm p).toReal ^ θ)
    hbound F

/--
%%handwave
name:
  Operator norm of the completed interpolated Beurling transform
statement:
  Under the interpolation hypotheses, the completed transform satisfies
  $$
    \|\mathcal S_r\|_{L^r\to L^r}\leq A_p^\theta.
  $$
proof:
  Apply the pointwise $L^r$ estimate to every vector in the domain and use
  the definition of the operator norm.
-/
theorem norm_beurlingTransformLpInterpolated_operator_le
    (p q : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    [Fact (1 ≤ ENNReal.ofReal q)]
    (hpq : p.HolderConjugate q) (hp2 : p < 2) (hq2 : 2 ≤ q)
    (r s θ : ℝ) [Fact (1 ≤ ENNReal.ofReal r)]
    (hrs : s.HolderConjugate r) (hr2 : 2 ≤ r)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hr_interp : r⁻¹ = (1 - θ) / 2 + θ / q) :
    ‖beurlingTransformLpInterpolated
      p q hpq hp2 hq2 r s θ hrs hr2 hθ hr_interp‖ ≤
        (beurlingInterpolationNorm p).toReal ^ θ := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (Real.rpow_nonneg ENNReal.toReal_nonneg θ)
  exact norm_beurlingTransformLpInterpolated_le
    p q hpq hp2 hq2 r s θ hrs hr2 hθ hr_interp

/--
%%handwave
name:
  Interpolated completion agrees with the exact transform on simple data
statement:
  Under the interpolation hypotheses, the completed $L^r$ Beurling
  transform of every finite-support simple function agrees almost everywhere
  with the exact Fourier-multiplier $L^2$ transform of the same function.
proof:
  The completed transform agrees with its simple-function construction,
  whose representative is the weak transform. Apply compatibility of the
  weak and exact transforms on finite-support simple data.
-/
theorem
    beurlingTransformLpInterpolated_apply_simpleFunc_ae_eq_beurlingTransformL2
    (p q : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    [Fact (1 ≤ ENNReal.ofReal q)]
    (hpq : p.HolderConjugate q) (hp2 : p < 2) (hq2 : 2 ≤ q)
    (r s θ : ℝ) [Fact (1 ≤ ENNReal.ofReal r)]
    (hrs : s.HolderConjugate r) (hr2 : 2 ≤ r)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hr_interp : r⁻¹ = (1 - θ) / 2 + θ / q)
    (F : Lp.simpleFunc ℂ (ENNReal.ofReal r) (volume : Measure ℂ)) :
    let F₁ : ℂ →₁[volume] ℂ :=
      simpleFuncToL1LinearMap (volume : Measure ℂ) (ENNReal.ofReal r)
        (ENNReal.ofReal_ne_zero_iff.mpr hrs.symm.pos)
        ENNReal.ofReal_ne_top F
    let hF₂ : MemLp (F₁ : ℂ → ℂ) 2 volume :=
      memLp_two_simpleFuncToL1LinearMap (volume : Measure ℂ)
        (ENNReal.ofReal r) (ENNReal.ofReal_ne_zero_iff.mpr hrs.symm.pos)
        ENNReal.ofReal_ne_top F
    (beurlingTransformLpInterpolated
        p q hpq hp2 hq2 r s θ hrs hr2 hθ hr_interp
        (F : Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ)) : ℂ → ℂ)
      =ᵐ[volume]
        (beurlingTransformL2
          (hF₂.toLp (F₁ : ℂ → ℂ)) : ℂ → ℂ) := by
  dsimp only
  have hcompleted :
      (beurlingTransformLpInterpolated
          p q hpq hp2 hq2 r s θ hrs hr2 hθ hr_interp
          (F : Lp ℂ (ENNReal.ofReal r) (volume : Measure ℂ)) : ℂ → ℂ)
        =ᵐ[volume]
          (beurlingTransformLpInterpolatedSimpleFunc
            p q hpq hp2 hq2 r s θ hrs hr2 hθ hr_interp F : ℂ → ℂ) := by
    rw [beurlingTransformLpInterpolated_apply_simpleFunc]
  exact hcompleted.trans <|
    (beurlingTransformLpInterpolatedSimpleFunc_coeFn
      p q hpq hp2 hq2 r s θ hrs hr2 hθ hr_interp F).trans <|
        beurlingTransformL1_simpleFuncToL1LinearMap_ae_eq_beurlingTransformL2
          (ENNReal.ofReal_ne_zero_iff.mpr hrs.symm.pos)
          ENNReal.ofReal_ne_top F

/--
%%handwave
name:
  Hölder-conjugate endpoints $3/2$ and $3$
statement:
  The exponents $3/2$ and $3$ are Hölder conjugates:
  $$
    \frac{1}{3/2}+\frac13=1.
  $$
proof:
  This is the elementary identity $2/3+1/3=1$.
-/
theorem threeHalves_holderConjugate_three :
    (3 / 2 : ℝ).HolderConjugate 3 := by
  rw [Real.holderConjugate_iff]
  norm_num

/--
%%handwave
name:
  Exponent on the interpolation segment from $2$ to $3$
statement:
  For a real interpolation parameter $\theta$, define $r_\theta$ by
  $$
    \frac1{r_\theta}=\frac{1-\theta}{2}+\frac\theta3.
  $$
-/
def beurlingNearTwoExponent (θ : ℝ) : ℝ :=
  ((1 - θ) / 2 + θ / 3)⁻¹

/--
%%handwave
name:
  The interpolated exponent lies strictly above $2$
statement:
  If $0<\theta<1$ and
  $$
    \frac1{r_\theta}=\frac{1-\theta}{2}+\frac\theta3,
  $$
  then $2<r_\theta$.
proof:
  The reciprocal on the right is
  $1/2-\theta/6<1/2$ and is positive, so taking reciprocals gives the
  claim.
-/
theorem two_lt_beurlingNearTwoExponent
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) 1) :
    2 < beurlingNearTwoExponent θ := by
  let a : ℝ := (1 - θ) / 2 + θ / 3
  have ha : 0 < a := by
    dsimp only [a]
    linarith [hθ.1, hθ.2]
  change 2 < a⁻¹
  rw [show a⁻¹ = 1 * a⁻¹ by simp, lt_mul_inv_iff₀ ha]
  dsimp only [a]
  linarith [hθ.1]

/--
%%handwave
name:
  The interpolated exponent lies strictly below $3$
statement:
  If $0<\theta<1$ and
  $$
    \frac1{r_\theta}=\frac{1-\theta}{2}+\frac\theta3,
  $$
  then $r_\theta<3$.
proof:
  The reciprocal on the right is
  $1/2-\theta/6>1/3$ and is positive, so taking reciprocals gives the
  claim.
-/
theorem beurlingNearTwoExponent_lt_three
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) 1) :
    beurlingNearTwoExponent θ < 3 := by
  let a : ℝ := (1 - θ) / 2 + θ / 3
  have ha : 0 < a := by
    dsimp only [a]
    linarith [hθ.1, hθ.2]
  change a⁻¹ < 3
  rw [inv_lt_iff_one_lt_mul₀ ha]
  dsimp only [a]
  linarith [hθ.2]

/--
%%handwave
name:
  Reciprocal formula for the near-$2$ exponent
statement:
  For every real $\theta$, the exponent $r_\theta$ defined by
  $$
    r_\theta=\left(\frac{1-\theta}{2}+\frac\theta3\right)^{-1}
  $$
  satisfies
  $$
    r_\theta^{-1}=\frac{1-\theta}{2}+\frac\theta3.
  $$
proof:
  This is involutivity of reciprocal.
-/
@[simp]
theorem inv_beurlingNearTwoExponent (θ : ℝ) :
    (beurlingNearTwoExponent θ)⁻¹ = (1 - θ) / 2 + θ / 3 := by
  simp only [beurlingNearTwoExponent, inv_inv]

/--
%%handwave
name:
  A small positive interpolation parameter preserves strict contraction
statement:
  Let $k<1$ and $M\geq0$. There is a parameter
  $0<\theta<1$ such that
  $$
    kM^\theta<1.
  $$
proof:
  If $M=0$, take $\theta=1/2$. Otherwise the function
  $\theta\mapsto kM^\theta$ is continuous and has value $k<1$ at
  $\theta=0$, so the inequality holds for all sufficiently small positive
  $\theta$.
-/
theorem exists_positive_rpow_multiplier_lt_one
    {k M : ℝ} (hk1 : k < 1) (hM0 : 0 ≤ M) :
    ∃ θ ∈ Set.Ioo (0 : ℝ) 1, k * M ^ θ < 1 := by
  by_cases hM : M = 0
  · refine ⟨1 / 2, by norm_num, ?_⟩
    simp [hM]
  · have hMpos : 0 < M := lt_of_le_of_ne hM0 (Ne.symm hM)
    have hcontinuous : Continuous (fun θ : ℝ ↦ k * M ^ θ) :=
      continuous_const.mul (Real.continuous_const_rpow hMpos.ne')
    have hnear : ∀ᶠ θ in 𝓝 (0 : ℝ), k * M ^ θ < 1 := by
      have htendsto : Filter.Tendsto (fun θ : ℝ ↦ k * M ^ θ)
          (𝓝 (0 : ℝ)) (𝓝 k) := by
        have hAt : Filter.Tendsto (fun θ : ℝ ↦ k * M ^ θ)
            (𝓝 (0 : ℝ)) (𝓝 (k * M ^ (0 : ℝ))) :=
          hcontinuous.continuousAt
        simpa only [Real.rpow_zero, mul_one] using hAt
      exact htendsto.eventually (eventually_lt_nhds hk1)
    have hnearRight : ∀ᶠ θ in 𝓝[>] (0 : ℝ), k * M ^ θ < 1 :=
      eventually_nhdsWithin_of_eventually_nhds hnear
    rcases (hnearRight.and (Ioo_mem_nhdsGT zero_lt_one)).exists with
      ⟨θ, hbound, hθ⟩
    exact ⟨θ, hθ, hbound⟩

/--
%%handwave
name:
  Near-$2$ Beurling interpolation parameters giving a contraction
statement:
  For every $k<1$, there are real numbers $\theta,r,s$ such that
  $0<\theta<1$, $2<r<3$, $s$ is Hölder conjugate to $r$,
  $$
    \frac1r=\frac{1-\theta}{2}+\frac\theta3,
  $$
  and
  $$
    k A_{3/2}^{\theta}<1,
  $$
  where $A_{3/2}$ is the explicit below-$2$ Beurling bound.
proof:
  Since $k<1$, continuity at $\theta=0$ gives a small positive parameter
  for which $kA_{3/2}^{\theta}<1$. Put
  $r=((1-\theta)/2+\theta/3)^{-1}$ and take the Hölder conjugate of $r$
  for $s$.
-/
theorem exists_beurlingNearTwo_contraction_parameters
    {k : ℝ} (hk1 : k < 1) :
    ∃ θ r s : ℝ,
      θ ∈ Set.Ioo (0 : ℝ) 1 ∧
      r = beurlingNearTwoExponent θ ∧
      2 < r ∧ r < 3 ∧
      s.HolderConjugate r ∧
      r⁻¹ = (1 - θ) / 2 + θ / 3 ∧
      k * (beurlingInterpolationNorm (3 / 2 : ℝ)).toReal ^ θ < 1 := by
  obtain ⟨θ, hθ, hcontract⟩ :=
    exists_positive_rpow_multiplier_lt_one hk1 ENNReal.toReal_nonneg
  let r := beurlingNearTwoExponent θ
  let s := Real.conjExponent r
  have hr2 : 2 < r := two_lt_beurlingNearTwoExponent hθ
  have hrs : s.HolderConjugate r :=
    (Real.HolderConjugate.conjExponent (lt_trans one_lt_two hr2)).symm
  exact ⟨θ, r, s, hθ, rfl, hr2,
    beurlingNearTwoExponent_lt_three hθ, hrs,
    inv_beurlingNearTwoExponent θ, hcontract⟩

end

end Quasiconformal

end JJMath
