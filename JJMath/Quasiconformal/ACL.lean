import JJMath.Quasiconformal.LocalSobolev

/-!
# Absolute continuity on coordinate lines

This file lifts the scalar product-domain ACL theorem to complex-valued maps.
It is the coordinate-line input for the square-boundary proof of the Lusin
$N$ property.
-/

namespace JJMath

open MeasureTheory
open scoped Topology

namespace Quasiconformal

noncomputable section

/--
%%handwave
name:
  Complex absolute continuity follows from its two real components
statement:
  Let $f:[a,b]\to\mathbb C$. If $\operatorname{Re}f$ and
  $\operatorname{Im}f$ are absolutely continuous on $[a,b]$, then $f$ is
  absolutely continuous on $[a,b]$.
proof:
  For $z,w\in\mathbb C$,
  $|z-w|\leq|\operatorname{Re}z-\operatorname{Re}w|+
  |\operatorname{Im}z-\operatorname{Im}w|$. Apply the
  $\varepsilon$--$\delta$ criteria for the two real components with
  tolerance $\varepsilon/2$, and use the smaller of the two resulting
  length bounds.
-/
theorem absolutelyContinuousOnInterval_complex_of_re_im
    {f : ℝ → ℂ} {a b : ℝ}
    (hre : AbsolutelyContinuousOnInterval (fun r => (f r).re) a b)
    (him : AbsolutelyContinuousOnInterval (fun r => (f r).im) a b) :
    AbsolutelyContinuousOnInterval f a b := by
  rw [absolutelyContinuousOnInterval_iff] at hre him ⊢
  intro ε hε
  rcases hre (ε / 2) (by linarith) with ⟨δre, hδre, hre⟩
  rcases him (ε / 2) (by linarith) with ⟨δim, hδim, him⟩
  refine ⟨min δre δim, lt_min hδre hδim, ?_⟩
  intro E hE hlength
  have hre_bound :=
    hre E hE (lt_of_lt_of_le hlength (min_le_left _ _))
  have him_bound :=
    him E hE (lt_of_lt_of_le hlength (min_le_right _ _))
  calc
    (∑ i ∈ Finset.range E.1,
        dist (f (E.2 i).1) (f (E.2 i).2))
        ≤ ∑ i ∈ Finset.range E.1,
            (dist (f (E.2 i).1).re (f (E.2 i).2).re +
              dist (f (E.2 i).1).im (f (E.2 i).2).im) := by
          gcongr with i hi
          simpa [dist_eq_norm] using
            Complex.norm_le_abs_re_add_abs_im
              (f (E.2 i).1 - f (E.2 i).2)
    _ = (∑ i ∈ Finset.range E.1,
            dist (f (E.2 i).1).re (f (E.2 i).2).re) +
          ∑ i ∈ Finset.range E.1,
            dist (f (E.2 i).1).im (f (E.2 i).2).im := by
          rw [Finset.sum_add_distrib]
    _ < ε / 2 + ε / 2 := add_lt_add hre_bound him_bound
    _ = ε := by ring

/--
%%handwave
name:
  Continuous complex Sobolev functions are locally ACL on protected vertical segments
statement:
  Let $Q$ be a compact subset of an open region
  $\Omega\subset\mathbb R\times E$. Suppose $U:\Omega\to\mathbb C$ is
  continuous, locally integrable, and has weak differential $DU$. For almost
  every $y\in E$, every segment $[a,b]\times\{y\}\subset Q$ with
  $0<a<b<1$ has the following properties: $r\mapsto U(r,y)$ is absolutely
  continuous on $[a,b]$, and its derivative is $DU(r,y)(1,0)$ for almost every
  $r\in(a,b)$.
proof:
  Project the weak differential identity through the real and imaginary
  coordinate functionals. Apply [the scalar function on each protected vertical segment is absolutely continuous with derivative $DU(r,y)(1,0)$](lean:JJMath.Uniformization.scalarWeakSobolev_firstCoordinate_fiberwise_acl_on_compact_of_continuousOn) to both components on a common full-measure set of transverse parameters. Recombine absolute continuity using the componentwise criterion, and recombine the two real derivative identities into the complex derivative identity.
-/
theorem complexWeakSobolev_firstCoordinate_fiberwise_acl_on_compact_of_continuousOn
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)]
    [FiniteDimensional ℝ E]
    {Q Ω : Set (ℝ × E)} (hQ : IsCompact Q) (hQΩ : Q ⊆ Ω)
    (hΩ_open : IsOpen Ω)
    {U : ℝ × E → ℂ} {DU : ℝ × E → (ℝ × E) →L[ℝ] ℂ}
    (hU_cont : ContinuousOn U Ω)
    (hweak :
      JJMath.Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues
        Ω U DU)
    (hU_loc : LocallyIntegrableOn U Ω
      (volume : Measure (ℝ × E))) :
    ∀ᵐ y ∂(volume : Measure E),
      ∀ a b : ℝ, 0 < a → a < b → b < 1 →
        (∀ r ∈ Set.Icc a b, (r, y) ∈ Q) →
          AbsolutelyContinuousOnInterval (fun r : ℝ => U (r, y)) a b ∧
            ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Ioo a b),
              HasDerivAt (fun r : ℝ => U (r, y))
                (DU (t, y) ((1 : ℝ), (0 : E))) t := by
  have hRe_cont : ContinuousOn (fun p => (U p).re) Ω := by
    simpa [Function.comp_def] using
      Complex.reCLM.continuous.comp_continuousOn hU_cont
  have hIm_cont : ContinuousOn (fun p => (U p).im) Ω := by
    simpa [Function.comp_def] using
      Complex.imCLM.continuous.comp_continuousOn hU_cont
  have hRe_weak :=
    weakDerivative_postcomp_continuousLinearMap Complex.reCLM hweak
  have hIm_weak :=
    weakDerivative_postcomp_continuousLinearMap Complex.imCLM hweak
  have hRe_loc : LocallyIntegrableOn (fun p => (U p).re) Ω
      (volume : Measure (ℝ × E)) := by
    simpa [Function.comp_def] using
      Complex.reCLM.locallyIntegrableOn_comp hU_loc
  have hIm_loc : LocallyIntegrableOn (fun p => (U p).im) Ω
      (volume : Measure (ℝ × E)) := by
    simpa [Function.comp_def] using
      Complex.imCLM.locallyIntegrableOn_comp hU_loc
  have hRe :=
    JJMath.Uniformization.scalarWeakSobolev_firstCoordinate_fiberwise_acl_on_compact_of_continuousOn
      (E := E) hQ hQΩ hΩ_open hRe_cont hRe_weak hRe_loc
  have hIm :=
    JJMath.Uniformization.scalarWeakSobolev_firstCoordinate_fiberwise_acl_on_compact_of_continuousOn
      (E := E) hQ hQΩ hΩ_open hIm_cont hIm_weak hIm_loc
  filter_upwards [hRe, hIm] with y hyRe hyIm
  intro a b ha hab hb hsegment
  rcases hyRe a b ha hab hb hsegment with ⟨hRe_ac, hRe_deriv⟩
  rcases hyIm a b ha hab hb hsegment with ⟨hIm_ac, hIm_deriv⟩
  constructor
  · exact absolutelyContinuousOnInterval_complex_of_re_im hRe_ac hIm_ac
  · filter_upwards [hRe_deriv, hIm_deriv] with t htRe htIm
    have htReC := htRe.smul_const (1 : ℂ)
    have htImC := htIm.smul_const Complex.I
    have hsum := htReC.add htImC
    convert hsum using 1
    · funext r
      apply Complex.ext <;> simp
    · apply Complex.ext <;> simp

/--
%%handwave
name:
  Vector-valued weak differentials pull back through volume-preserving linear coordinates
statement:
  Let $e:D\to H$ be a volume-preserving continuous real-linear equivalence.
  If $f:\Omega\to E$ has weak differential $Df$ on
  $\Omega\subset H$, then $f\circ e$ has weak differential
  $$
  D(f\circ e)(x)=Df(e(x))\circ e
  $$
  on $e^{-1}(\Omega)$.
proof:
  Given a smooth compactly supported test $\varphi$ on $e^{-1}(\Omega)$,
  use $\varphi\circ e^{-1}$ in the weak identity for $f$, in the direction
  $e(v)$. The chain rule identifies the differentiated test, and volume
  preservation transports both integrals without a Jacobian factor.
-/
theorem weakDerivative_comp_volumePreservingContinuousLinearEquiv
    {D H : Type}
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [MeasureSpace D] [BorelSpace D]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Set H} (e : D ≃L[ℝ] H)
    (hmp : MeasurePreserving e (volume : Measure D) (volume : Measure H))
    {f : H → E} {df : H → H →L[ℝ] E}
    (hweak :
      JJMath.Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues
        Ω f df) :
    JJMath.Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues
      (e ⁻¹' Ω) (fun x : D => f (e x))
      (fun x : D => (df (e x)).comp (e : D →L[ℝ] H)) := by
  let U : Set D := e ⁻¹' Ω
  have hemb : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have hmpU : MeasurePreserving e
      (volume.restrict U) (volume.restrict Ω) := by
    simpa [U] using hmp.restrict_preimage_emb hemb Ω
  intro φ v
  let ψ :
      JJMath.Uniformization.SmoothCompactlySupportedManifoldCoordinateFunction
        Ω :=
    { toFun := (φ : D → ℝ) ∘ e.symm
      smooth := φ.smooth.comp e.symm.contDiff
      support_subset := by
        intro z hz
        have hzpre : e.symm z ∈ tsupport (φ : D → ℝ) := by
          exact (Set.ext_iff.mp
            (tsupport_comp_eq_preimage (φ : D → ℝ)
              e.symm.toHomeomorph) z).mp hz
        have hzU := φ.support_subset hzpre
        simpa [U] using hzU
      compact_support := by
        change IsCompact (tsupport ((φ : D → ℝ) ∘ e.symm.toHomeomorph))
        rw [tsupport_comp_eq_preimage]
        exact e.symm.toHomeomorph.isCompact_preimage.2 φ.compact_support }
  rcases hweak ψ (e v) with ⟨hleft, hright, heq⟩
  let L : H → E := fun y =>
    (fderiv ℝ (ψ : H → ℝ) y (e v)) • f y
  let R : H → E := fun y => ψ y • df y (e v)
  have hleft_pull : Integrable (L ∘ e) (volume.restrict U) :=
    hmpU.integrable_comp_of_integrable (by simpa [L] using hleft)
  have hright_pull : Integrable (R ∘ e) (volume.restrict U) :=
    hmpU.integrable_comp_of_integrable (by simpa [R] using hright)
  have hψ_fderiv (x : D) :
      fderiv ℝ (ψ : H → ℝ) (e x) (e v) =
        fderiv ℝ (φ : D → ℝ) x v := by
    have hfd :
        fderiv ℝ ((φ : D → ℝ) ∘ (e.symm : H → D)) (e x) =
          (fderiv ℝ (φ : D → ℝ) (e.symm (e x))).comp
            (fderiv ℝ (e.symm : H → D) (e x)) :=
      fderiv_comp (𝕜 := ℝ) (e x)
        (φ.smooth.differentiable (by simp)).differentiableAt
        e.symm.differentiableAt
    simp only [ψ]
    rw [hfd, ContinuousLinearMap.comp_apply]
    rw [e.symm.hasFDerivAt.fderiv]
    simp
  refine ⟨?_, ?_, ?_⟩
  · simpa [L, Function.comp_def, hψ_fderiv] using hleft_pull
  · simpa [R, ψ, Function.comp_def, ContinuousLinearMap.comp_apply] using
      hright_pull
  · calc
      ∫ x in U, (fderiv ℝ (φ : D → ℝ) x v) • f (e x) ∂volume =
          ∫ x in U, L (e x) ∂volume := by
            apply integral_congr_ae
            filter_upwards [] with x
            simp [L, hψ_fderiv]
      _ = ∫ y in Ω, L y ∂volume := hmpU.integral_comp hemb L
      _ = -∫ y in Ω, R y ∂volume := by simpa [L, R] using heq
      _ = -∫ x in U, R (e x) ∂volume := by
            rw [hmpU.integral_comp hemb R]
      _ = -∫ x in U,
          φ x • ((df (e x)).comp (e : D →L[ℝ] H)) v ∂volume := by
            congr 1
            apply integral_congr_ae
            filter_upwards [] with x
            simp [R, ψ, ContinuousLinearMap.comp_apply]

/--
%%handwave
name:
  Continuous complex weak Sobolev functions are ACL in volume-preserving linear coordinates
statement:
  Let $e:\mathbb R^2\to\mathbb C$ be a volume-preserving continuous
  real-linear equivalence, let $Q\subset\Omega\subset\mathbb C$ with $Q$
  compact and $\Omega$ open, and suppose $f$ is continuous on $\Omega$ with
  weak differential $Df$. For almost every $y$, every segment
  $\{e(r,y):a\leq r\leq b\}\subset Q$ with $0<a<b<1$ has absolutely
  continuous restriction $r\mapsto f(e(r,y))$, whose derivative is
  $Df(e(r,y))(e(1,0))$ for almost every $r\in(a,b)$.
proof:
  By [the weak differential pulls back as $D(f\circ e)(x)=Df(e(x))\circ e$](lean:JJMath.Quasiconformal.weakDerivative_comp_volumePreservingContinuousLinearEquiv), the coordinate expression has the expected weak differential. Continuity makes it locally integrable on the pulled-back open region. Apply [the complex function on each protected first-coordinate segment is absolutely continuous with its weak directional derivative](lean:JJMath.Quasiconformal.complexWeakSobolev_firstCoordinate_fiberwise_acl_on_compact_of_continuousOn) to the inverse images of $Q$ and $\Omega$.
-/
theorem complexWeakSobolev_firstCoordinate_comp_volumePreservingEquiv_acl_on_compact_of_continuousOn
    (e : (ℝ × ℝ) ≃L[ℝ] ℂ)
    (hmp : MeasurePreserving e
      (volume : Measure (ℝ × ℝ)) (volume : Measure ℂ))
    {Q Ω : Set ℂ}
    (hQ : IsCompact Q) (hQΩ : Q ⊆ Ω) (hΩ_open : IsOpen Ω)
    {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (hf_cont : ContinuousOn f Ω)
    (hweak :
      JJMath.Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues
        Ω f df) :
    ∀ᵐ y ∂(volume : Measure ℝ),
      ∀ a b : ℝ, 0 < a → a < b → b < 1 →
        (∀ r ∈ Set.Icc a b, e (r, y) ∈ Q) →
          AbsolutelyContinuousOnInterval (fun r : ℝ => f (e (r, y))) a b ∧
            ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Ioo a b),
              HasDerivAt (fun r : ℝ => f (e (r, y)))
                (df (e (t, y)) (e (1, 0))) t := by
  letI : Measure.IsAddHaarMeasure (volume : Measure (ℝ × ℝ)) := by
    rw [Measure.volume_eq_prod]
    infer_instance
  let Qp : Set (ℝ × ℝ) := e ⁻¹' Q
  let Ωp : Set (ℝ × ℝ) := e ⁻¹' Ω
  let F : ℝ × ℝ → ℂ := fun p => f (e p)
  let DF : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℂ :=
    fun p => (df (e p)).comp (e : (ℝ × ℝ) →L[ℝ] ℂ)
  have hΩp_open : IsOpen Ωp := hΩ_open.preimage e.continuous
  have hF_cont : ContinuousOn F Ωp :=
    hf_cont.comp e.continuous.continuousOn (fun _ hp => hp)
  have hF_weak :
      JJMath.Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues
        Ωp F DF := by
    simpa [Ωp, F, DF] using
      weakDerivative_comp_volumePreservingContinuousLinearEquiv e hmp hweak
  have hF_loc : LocallyIntegrableOn F Ωp
      (volume : Measure (ℝ × ℝ)) :=
    hF_cont.locallyIntegrableOn hΩp_open.measurableSet
  have hQp : IsCompact Qp := by
    simpa [Qp] using e.toHomeomorph.isCompact_preimage.2 hQ
  have hQpΩp : Qp ⊆ Ωp := Set.preimage_mono hQΩ
  have hresult :=
    complexWeakSobolev_firstCoordinate_fiberwise_acl_on_compact_of_continuousOn
      (E := ℝ) hQp hQpΩp hΩp_open hF_cont hF_weak hF_loc
  simpa [Qp, F, DF, ContinuousLinearMap.comp_apply] using hresult

/--
%%handwave
name:
  Continuous planar weak Sobolev functions are ACL on protected horizontal segments
statement:
  Let $Q\subset\Omega\subset\mathbb C$, with $Q$ compact and $\Omega$ open,
  and suppose $f$ is continuous on $\Omega$ with weak differential $Df$.
  For almost every $y\in\mathbb R$, every horizontal segment
  $\{r+iy:a\leq r\leq b\}\subset Q$ with $0<a<b<1$ has absolutely
  continuous restriction $r\mapsto f(r+iy)$, whose derivative is
  $Df(r+iy)(1)$ for almost every $r\in(a,b)$.
proof:
  Apply [ACL in volume-preserving linear coordinates](lean:JJMath.Quasiconformal.complexWeakSobolev_firstCoordinate_comp_volumePreservingEquiv_acl_on_compact_of_continuousOn) to the Cartesian identification $(r,y)\mapsto r+iy$, for which the first coordinate direction is $1$.
-/
theorem planarWeakSobolev_horizontal_acl_on_compact_of_continuousOn
    {Q Ω : Set ℂ}
    (hQ : IsCompact Q) (hQΩ : Q ⊆ Ω) (hΩ_open : IsOpen Ω)
    {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (hf_cont : ContinuousOn f Ω)
    (hweak :
      JJMath.Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues
        Ω f df) :
    ∀ᵐ y ∂(volume : Measure ℝ),
      ∀ a b : ℝ, 0 < a → a < b → b < 1 →
        (∀ r ∈ Set.Icc a b,
          Complex.equivRealProdCLM.symm (r, y) ∈ Q) →
          AbsolutelyContinuousOnInterval
              (fun r : ℝ => f (Complex.equivRealProdCLM.symm (r, y))) a b ∧
            ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Ioo a b : Set ℝ),
              HasDerivAt
                (fun r : ℝ => f (Complex.equivRealProdCLM.symm (r, y)))
                (df (Complex.equivRealProdCLM.symm (t, y)) 1) t := by
  letI : Measure.IsAddHaarMeasure (volume : Measure (ℝ × ℝ)) := by
    rw [Measure.volume_eq_prod]
    infer_instance
  simpa [Complex.equivRealProdCLM_symm_apply] using
    complexWeakSobolev_firstCoordinate_comp_volumePreservingEquiv_acl_on_compact_of_continuousOn
      Complex.equivRealProdCLM.symm
      Complex.volume_preserving_equiv_real_prod.symm
      hQ hQΩ hΩ_open hf_cont hweak

private def planarVerticalCoordinates : (ℝ × ℝ) ≃L[ℝ] ℂ :=
  (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ).trans
    Complex.equivRealProdCLM.symm

/--
%%handwave
name:
  Continuous planar weak Sobolev functions are ACL on protected vertical segments
statement:
  Let $Q\subset\Omega\subset\mathbb C$, with $Q$ compact and $\Omega$ open,
  and suppose $f$ is continuous on $\Omega$ with weak differential $Df$.
  For almost every $x\in\mathbb R$, every vertical segment
  $\{x+ir:a\leq r\leq b\}\subset Q$ with $0<a<b<1$ has absolutely
  continuous restriction $r\mapsto f(x+ir)$, whose derivative is
  $Df(x+ir)(i)$ for almost every $r\in(a,b)$.
proof:
  Swap the two Cartesian coordinates and then apply [ACL in volume-preserving linear coordinates](lean:JJMath.Quasiconformal.complexWeakSobolev_firstCoordinate_comp_volumePreservingEquiv_acl_on_compact_of_continuousOn). The swap preserves product Lebesgue measure and sends the first coordinate direction to $i$.
-/
theorem planarWeakSobolev_vertical_acl_on_compact_of_continuousOn
    {Q Ω : Set ℂ}
    (hQ : IsCompact Q) (hQΩ : Q ⊆ Ω) (hΩ_open : IsOpen Ω)
    {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    (hf_cont : ContinuousOn f Ω)
    (hweak :
      JJMath.Uniformization.IsWeakDerivativeOnEuclideanRegionWithValues
        Ω f df) :
    ∀ᵐ x ∂(volume : Measure ℝ),
      ∀ a b : ℝ, 0 < a → a < b → b < 1 →
        (∀ r ∈ Set.Icc a b,
          Complex.ofReal x + Complex.ofReal r * Complex.I ∈ Q) →
          AbsolutelyContinuousOnInterval
              (fun r : ℝ =>
                f (Complex.ofReal x + Complex.ofReal r * Complex.I)) a b ∧
            ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Ioo a b : Set ℝ),
              HasDerivAt
                (fun r : ℝ =>
                  f (Complex.ofReal x + Complex.ofReal r * Complex.I))
                (df (Complex.ofReal x + Complex.ofReal t * Complex.I)
                  Complex.I) t := by
  letI : Measure.IsAddHaarMeasure (volume : Measure (ℝ × ℝ)) := by
    rw [Measure.volume_eq_prod]
    infer_instance
  have hswap : MeasurePreserving
      (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ)
      (volume : Measure (ℝ × ℝ)) (volume : Measure (ℝ × ℝ)) := by
    rw [Measure.volume_eq_prod]
    simpa [ContinuousLinearEquiv.prodComm_apply] using
      (Measure.measurePreserving_swap
        (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)))
  have hstandard : MeasurePreserving Complex.equivRealProdCLM.symm
      (volume : Measure (ℝ × ℝ)) (volume : Measure ℂ) :=
    Complex.volume_preserving_equiv_real_prod.symm
  have hvertical : MeasurePreserving planarVerticalCoordinates
      (volume : Measure (ℝ × ℝ)) (volume : Measure ℂ) :=
    hstandard.comp hswap
  simpa [planarVerticalCoordinates, ContinuousLinearEquiv.prodComm_apply,
    Complex.equivRealProdCLM_symm_apply] using
    complexWeakSobolev_firstCoordinate_comp_volumePreservingEquiv_acl_on_compact_of_continuousOn
      planarVerticalCoordinates hvertical hQ hQΩ hΩ_open hf_cont hweak

end

end Quasiconformal

end JJMath
