import JJMath.Quasiconformal.ACL
import JJMath.Quasiconformal.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable

/-!
# Square-boundary estimates for planar Sobolev homeomorphisms

This file develops the geometric estimate used in the ACL proof of Lusin
$N$.  Absolute continuity controls the diameter of the image of each side of
a rectangle by the line integral of the weak directional derivative.  A
separate compact-set estimate bounds planar area by the square of the
diameter of the frontier.  For homeomorphic images of rectangles these two
facts meet without any Jordan-curve or isoperimetric input.
-/

namespace JJMath

open MeasureTheory Set
open scoped Topology ENNReal

namespace Quasiconformal

noncomputable section

/--
%%handwave
name:
  Coordinate absolute continuity of a complex curve
statement:
  If $f:[a,b]\to\mathbb C$ is absolutely continuous, then its real and
  imaginary coordinate functions are absolutely continuous on $[a,b]$.
proof:
  In each finite disjoint family of subintervals, every real or imaginary coordinate increment is bounded by the norm of the corresponding complex increment. Apply the defining $\varepsilon$-$\delta$ estimate for absolute continuity.
-/
theorem complex_absolutelyContinuousOnInterval_re_im
    {f : ℝ → ℂ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun t => (f t).re) a b ∧
      AbsolutelyContinuousOnInterval (fun t => (f t).im) a b := by
  constructor
  · rw [absolutelyContinuousOnInterval_iff] at hf ⊢
    intro ε hε
    rcases hf ε hε with ⟨δ, hδ, hf⟩
    refine ⟨δ, hδ, ?_⟩
    intro E hE hlength
    calc
      ∑ i ∈ Finset.range E.1,
          dist (f (E.2 i).1).re (f (E.2 i).2).re
          ≤ ∑ i ∈ Finset.range E.1,
              dist (f (E.2 i).1) (f (E.2 i).2) := by
            gcongr with i hi
            simpa [dist_eq_norm] using
              Complex.abs_re_le_norm (f (E.2 i).1 - f (E.2 i).2)
      _ < ε := hf E hE hlength
  · rw [absolutelyContinuousOnInterval_iff] at hf ⊢
    intro ε hε
    rcases hf ε hε with ⟨δ, hδ, hf⟩
    refine ⟨δ, hδ, ?_⟩
    intro E hE hlength
    calc
      ∑ i ∈ Finset.range E.1,
          dist (f (E.2 i).1).im (f (E.2 i).2).im
          ≤ ∑ i ∈ Finset.range E.1,
              dist (f (E.2 i).1) (f (E.2 i).2) := by
            gcongr with i hi
            simpa [dist_eq_norm] using
              Complex.abs_im_le_norm (f (E.2 i).1 - f (E.2 i).2)
      _ < ε := hf E hE hlength

/--
%%handwave
name:
  Integrability of the derivative of an absolutely continuous complex curve
statement:
  Let $a<b$. If $f:[a,b]\to\mathbb C$ is absolutely continuous and
  $f'(t)=g(t)$ for almost every $t\in(a,b)$, then $g$ is
  interval-integrable on $[a,b]$.
proof:
  By [coordinate absolute continuity](lean:JJMath.Quasiconformal.complex_absolutelyContinuousOnInterval_re_im), the real and imaginary parts are absolutely continuous. Their derivatives are interval-integrable and agree almost everywhere with the real and imaginary parts of $g$; coordinatewise integrability is equivalent to complex integrability.
-/
theorem complex_intervalIntegrable_of_absolutelyContinuousOnInterval_of_ae_hasDerivAt
    {f g : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hderiv : ∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt f (g t) t) :
    IntervalIntegrable g volume a b := by
  obtain ⟨hre_ac, him_ac⟩ := complex_absolutelyContinuousOnInterval_re_im hf
  have hderiv_global :
      ∀ᵐ t ∂volume, t ∈ Ioo a b → HasDerivAt f (g t) t :=
    (ae_restrict_iff' measurableSet_Ioo).mp hderiv
  have hne_b : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ b := by
    simp [ae_iff, measure_singleton]
  have hre_ae :
      (fun t => (g t).re) =ᵐ[volume.restrict (uIoc a b)]
        deriv (fun t => (f t).re) := by
    filter_upwards [ae_restrict_of_ae hderiv_global,
      ae_restrict_of_ae hne_b, ae_restrict_mem measurableSet_uIoc] with
      t ht htne htuIoc
    have htIoo : t ∈ Ioo a b := by
      rw [uIoc_of_le hab.le] at htuIoc
      exact ⟨htuIoc.1, lt_of_le_of_ne htuIoc.2 htne⟩
    have htRe := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (ht htIoo)
    exact htRe.deriv.symm
  have him_ae :
      (fun t => (g t).im) =ᵐ[volume.restrict (uIoc a b)]
        deriv (fun t => (f t).im) := by
    filter_upwards [ae_restrict_of_ae hderiv_global,
      ae_restrict_of_ae hne_b, ae_restrict_mem measurableSet_uIoc] with
      t ht htne htuIoc
    have htIoo : t ∈ Ioo a b := by
      rw [uIoc_of_le hab.le] at htuIoc
      exact ⟨htuIoc.1, lt_of_le_of_ne htuIoc.2 htne⟩
    have htIm := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (ht htIoo)
    exact htIm.deriv.symm
  have hre_int : IntervalIntegrable (fun t => (g t).re) volume a b :=
    hre_ac.intervalIntegrable_deriv.congr_ae hre_ae.symm
  have him_int : IntervalIntegrable (fun t => (g t).im) volume a b :=
    him_ac.intervalIntegrable_deriv.congr_ae him_ae.symm
  rw [intervalIntegrable_iff] at hre_int him_int ⊢
  exact Integrable.re_im_iff.mp ⟨hre_int, him_int⟩

/--
%%handwave
name:
  Complex fundamental theorem for absolutely continuous curves
statement:
  Let $a<b$. If $f:[a,b]\to\mathbb C$ is absolutely continuous and
  $f'(t)=g(t)$ for almost every $t\in(a,b)$, then
  $$
  \int_a^b g(t)\,dt=f(b)-f(a).
  $$
proof:
  Apply the real fundamental theorem of calculus to the real and imaginary parts. Their absolute continuity follows by bounding each coordinate increment by the complex increment, and the two scalar integral identities recombine into the complex identity.
-/
theorem complex_intervalIntegral_eq_sub_of_absolutelyContinuousOnInterval
    {f g : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hderiv : ∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt f (g t) t) :
    ∫ t in a..b, g t = f b - f a := by
  have hg : IntervalIntegrable g volume a b :=
    complex_intervalIntegrable_of_absolutelyContinuousOnInterval_of_ae_hasDerivAt
      hab hf hderiv
  obtain ⟨hre_ac, him_ac⟩ := complex_absolutelyContinuousOnInterval_re_im hf
  have hderiv_global :
      ∀ᵐ t ∂volume, t ∈ Ioo a b → HasDerivAt f (g t) t :=
    (ae_restrict_iff' measurableSet_Ioo).mp hderiv
  have hne_b : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ b := by
    simp [ae_iff, measure_singleton]
  have hre_eq :
      ∫ t in a..b, (g t).re = (f b).re - (f a).re := by
    rw [← hre_ac.integral_deriv_eq_sub]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hderiv_global, hne_b] with t ht htne htuIoc
    have htIoo : t ∈ Ioo a b := by
      rw [uIoc_of_le hab.le] at htuIoc
      exact ⟨htuIoc.1, lt_of_le_of_ne htuIoc.2 htne⟩
    have htRe := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (ht htIoo)
    exact htRe.deriv.symm
  have him_eq :
      ∫ t in a..b, (g t).im = (f b).im - (f a).im := by
    rw [← him_ac.integral_deriv_eq_sub]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hderiv_global, hne_b] with t ht htne htuIoc
    have htIoo : t ∈ Ioo a b := by
      rw [uIoc_of_le hab.le] at htuIoc
      exact ⟨htuIoc.1, lt_of_le_of_ne htuIoc.2 htne⟩
    have htIm := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (ht htIoo)
    exact htIm.deriv.symm
  apply Complex.ext
  · calc
      (∫ t in a..b, g t).re = ∫ t in a..b, (g t).re :=
        (Complex.reCLM.intervalIntegral_comp_comm hg).symm
      _ = (f b).re - (f a).re := hre_eq
      _ = (f b - f a).re := by simp
  · calc
      (∫ t in a..b, g t).im = ∫ t in a..b, (g t).im :=
        (Complex.imCLM.intervalIntegral_comp_comm hg).symm
      _ = (f b).im - (f a).im := him_eq
      _ = (f b - f a).im := by simp

/--
%%handwave
name:
  Endpoint distance of an absolutely continuous complex curve
statement:
  Let $a<b$. If $f:[a,b]\to\mathbb C$ is absolutely continuous,
  $f'(t)=g(t)$ almost everywhere on $(a,b)$, then
  $$
  d(f(a),f(b))\leq\int_{(a,b)}\lVert g(t)\rVert\,dt.
  $$
proof:
  By [the complex fundamental theorem of calculus](lean:JJMath.Quasiconformal.complex_intervalIntegral_eq_sub_of_absolutelyContinuousOnInterval), the endpoint difference is the integral of $g$. Apply the norm bound for a Bochner integral.
-/
theorem complex_endpoint_edist_le_lintegral_enorm_of_absolutelyContinuousOnInterval
    {f g : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hderiv : ∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt f (g t) t) :
    edist (f a) (f b) ≤ ∫⁻ t in Ioo a b, ‖g t‖ₑ ∂volume := by
  have hFTC : ∫ t in a..b, g t = f b - f a :=
    complex_intervalIntegral_eq_sub_of_absolutelyContinuousOnInterval
      hab hf hderiv
  have hInterval :
      ∫ t in a..b, g t = ∫ t in Ioo a b, g t ∂volume := by
    rw [intervalIntegral.integral_of_le hab.le]
    simpa using
      (integral_Ioc_eq_integral_Ioo
        (f := g) (μ := volume) (x := a) (y := b))
  calc
    edist (f a) (f b) = ‖f b - f a‖ₑ := by
      rw [edist_dist, ← ofReal_norm]
      simp [dist_eq_norm, norm_sub_rev]
    _ = ‖∫ t in Ioo a b, g t ∂volume‖ₑ := by rw [← hInterval, hFTC]
    _ ≤ ∫⁻ t in Ioo a b, ‖g t‖ₑ ∂volume :=
      MeasureTheory.enorm_integral_le_lintegral_enorm
        (μ := volume.restrict (Ioo a b)) g

/--
%%handwave
name:
  Diameter of an absolutely continuous complex curve
statement:
  Let $a<b$. If $f:[a,b]\to\mathbb C$ is absolutely continuous,
  $f'(t)=g(t)$ almost everywhere on $(a,b)$, then
  $$
  \operatorname{diam} f([a,b])
    \leq\int_{(a,b)}\lVert g(t)\rVert\,dt.
  $$
proof:
  Apply [the endpoint distance estimate](lean:JJMath.Quasiconformal.complex_endpoint_edist_le_lintegral_enorm_of_absolutelyContinuousOnInterval) on every subinterval between two points of $[a,b]$, and enlarge its derivative integral back to $(a,b)$.
-/
theorem complex_image_ediam_le_lintegral_enorm_of_absolutelyContinuousOnInterval
    {f g : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hderiv : ∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt f (g t) t) :
    Metric.ediam (f '' Icc a b) ≤
      ∫⁻ t in Ioo a b, ‖g t‖ₑ ∂volume := by
  rw [Metric.ediam_image_le_iff]
  intro r hr s hs
  rcases lt_trichotomy r s with hrs | rfl | hsr
  · have hclosed : uIcc r s ⊆ uIcc a b := by
      rw [uIcc_of_le hab.le, uIcc_of_le hrs.le]
      exact Icc_subset_Icc hr.1 hs.2
    have hopen : Ioo r s ⊆ Ioo a b := by
      intro t ht
      exact ⟨lt_of_le_of_lt hr.1 ht.1, lt_of_lt_of_le ht.2 hs.2⟩
    calc
      edist (f r) (f s) ≤ ∫⁻ t in Ioo r s, ‖g t‖ₑ ∂volume :=
        complex_endpoint_edist_le_lintegral_enorm_of_absolutelyContinuousOnInterval
          hrs (hf.mono hclosed)
          (ae_restrict_of_ae_restrict_of_subset hopen hderiv)
      _ ≤ ∫⁻ t in Ioo a b, ‖g t‖ₑ ∂volume := lintegral_mono_set hopen
  · simp
  · have hclosed : uIcc s r ⊆ uIcc a b := by
      rw [uIcc_of_le hab.le, uIcc_of_le hsr.le]
      exact Icc_subset_Icc hs.1 hr.2
    have hopen : Ioo s r ⊆ Ioo a b := by
      intro t ht
      exact ⟨lt_of_le_of_lt hs.1 ht.1, lt_of_lt_of_le ht.2 hr.2⟩
    calc
      edist (f r) (f s) = edist (f s) (f r) := edist_comm _ _
      _ ≤ ∫⁻ t in Ioo s r, ‖g t‖ₑ ∂volume :=
        complex_endpoint_edist_le_lintegral_enorm_of_absolutelyContinuousOnInterval
          hsr (hf.mono hclosed)
          (ae_restrict_of_ae_restrict_of_subset hopen hderiv)
      _ ≤ ∫⁻ t in Ioo a b, ‖g t‖ₑ ∂volume := lintegral_mono_set hopen

/--
%%handwave
name:
  Closed axis-parallel rectangle
statement:
  For $a,b,c,d\in\mathbb R$, define
  $$
    R[a,b;c,d]=\{x+iy:a\leq x\leq b,\ c\leq y\leq d\}.
  $$
-/
def closedRectangle (a b c d : ℝ) : Set ℂ :=
  Icc a b ×ℂ Icc c d

/--
%%handwave
name:
  Boundary frame of a closed rectangle
statement:
  For $a,b,c,d\in\mathbb R$, define the rectangular boundary frame as the
  union of the four parametrized segments
  $$
    [a,b]+ic,\quad b+i[c,d],\quad [a,b]+id,\quad a+i[c,d].
  $$
-/
def closedRectangleBoundary (a b c d : ℝ) : Set ℂ :=
  ((fun r : ℝ => Complex.ofReal r + Complex.ofReal c * Complex.I) '' Icc a b ∪
    (fun r : ℝ => Complex.ofReal b + Complex.ofReal r * Complex.I) '' Icc c d) ∪
  ((fun r : ℝ => Complex.ofReal r + Complex.ofReal d * Complex.I) '' Icc a b ∪
    (fun r : ℝ => Complex.ofReal a + Complex.ofReal r * Complex.I) '' Icc c d)

/--
%%handwave
name:
  Frontier of a closed rectangle
statement:
  If $a<b$ and $c<d$, the frontier of the planar rectangle
  $[a,b]\times[c,d]$ is the union of its four closed sides.
proof:
  Use the product formula for frontiers and the fact that the frontier of a nondegenerate closed real interval consists of its two endpoints, then identify the four resulting products with the four side parameterizations.
-/
theorem frontier_closedRectangle
    {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    frontier (closedRectangle a b c d) =
      closedRectangleBoundary a b c d := by
  rw [closedRectangle, Complex.frontier_reProdIm, closure_Icc, closure_Icc,
    frontier_Icc hab.le, frontier_Icc hcd.le]
  ext z
  simp only [closedRectangleBoundary, Complex.mem_reProdIm, mem_union,
    mem_image, mem_Icc, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro (⟨hzre, rfl | rfl⟩ | ⟨rfl | rfl, hzim⟩)
    · left
      left
      exact ⟨z.re, hzre, by apply Complex.ext <;> simp⟩
    · right
      left
      exact ⟨z.re, hzre, by apply Complex.ext <;> simp⟩
    · right
      right
      exact ⟨z.im, hzim, by apply Complex.ext <;> simp⟩
    · left
      right
      exact ⟨z.im, hzim, by apply Complex.ext <;> simp⟩
  · rintro ((⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩) |
      (⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩))
    · exact Or.inl ⟨by simpa using hr, by simp⟩
    · exact Or.inr ⟨Or.inr (by simp), by simpa using hr⟩
    · exact Or.inl ⟨by simpa using hr, by simp⟩
    · exact Or.inr ⟨Or.inl (by simp), by simpa using hr⟩

/--
%%handwave
name:
  Diameter estimate for the image of an ACL rectangle boundary
statement:
  Let $a<b$ and $c<d$. Suppose the restrictions of
  $f:\mathbb C\to\mathbb C$ to all four sides of
  $[a,b]\times[c,d]$ are absolutely continuous, with almost-everywhere
  derivatives $Df(1)$ on the horizontal sides and $Df(i)$ on the vertical
  sides. Then the diameter of the image of the rectangle boundary is at most the sum of
  the four line integrals of the corresponding derivative norms.
proof:
  Apply [the diameter estimate for an absolutely continuous curve](lean:JJMath.Quasiconformal.complex_image_ediam_le_lintegral_enorm_of_absolutelyContinuousOnInterval) to each side. Consecutive side images meet at a corner, so repeated use of the diameter bound for intersecting unions adds the four estimates.
-/
theorem planar_rectangleBoundary_ediam_le_lintegral_enorm
    {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ} {a b c d : ℝ}
    (hab : a < b) (hcd : c < d)
    (hbottom : AbsolutelyContinuousOnInterval
      (fun r : ℝ => f (Complex.ofReal r + Complex.ofReal c * Complex.I)) a b)
    (hright : AbsolutelyContinuousOnInterval
      (fun r : ℝ => f (Complex.ofReal b + Complex.ofReal r * Complex.I)) c d)
    (htop : AbsolutelyContinuousOnInterval
      (fun r : ℝ => f (Complex.ofReal r + Complex.ofReal d * Complex.I)) a b)
    (hleft : AbsolutelyContinuousOnInterval
      (fun r : ℝ => f (Complex.ofReal a + Complex.ofReal r * Complex.I)) c d)
    (hdbottom : ∀ᵐ t ∂volume.restrict (Ioo a b),
      HasDerivAt
        (fun r : ℝ => f (Complex.ofReal r + Complex.ofReal c * Complex.I))
        (df (Complex.ofReal t + Complex.ofReal c * Complex.I) 1) t)
    (hdright : ∀ᵐ t ∂volume.restrict (Ioo c d),
      HasDerivAt
        (fun r : ℝ => f (Complex.ofReal b + Complex.ofReal r * Complex.I))
        (df (Complex.ofReal b + Complex.ofReal t * Complex.I) Complex.I) t)
    (hdtop : ∀ᵐ t ∂volume.restrict (Ioo a b),
      HasDerivAt
        (fun r : ℝ => f (Complex.ofReal r + Complex.ofReal d * Complex.I))
        (df (Complex.ofReal t + Complex.ofReal d * Complex.I) 1) t)
    (hdleft : ∀ᵐ t ∂volume.restrict (Ioo c d),
      HasDerivAt
        (fun r : ℝ => f (Complex.ofReal a + Complex.ofReal r * Complex.I))
        (df (Complex.ofReal a + Complex.ofReal t * Complex.I) Complex.I) t) :
    Metric.ediam (f '' closedRectangleBoundary a b c d) ≤
      (∫⁻ t in Ioo a b,
        ‖df (Complex.ofReal t + Complex.ofReal c * Complex.I) 1‖ₑ ∂volume) +
      (∫⁻ t in Ioo c d,
        ‖df (Complex.ofReal b + Complex.ofReal t * Complex.I) Complex.I‖ₑ ∂volume) +
      (∫⁻ t in Ioo a b,
        ‖df (Complex.ofReal t + Complex.ofReal d * Complex.I) 1‖ₑ ∂volume) +
      (∫⁻ t in Ioo c d,
        ‖df (Complex.ofReal a + Complex.ofReal t * Complex.I) Complex.I‖ₑ ∂volume) := by
  let pbottom := fun r : ℝ => Complex.ofReal r + Complex.ofReal c * Complex.I
  let pright := fun r : ℝ => Complex.ofReal b + Complex.ofReal r * Complex.I
  let ptop := fun r : ℝ => Complex.ofReal r + Complex.ofReal d * Complex.I
  let pleft := fun r : ℝ => Complex.ofReal a + Complex.ofReal r * Complex.I
  let Sbottom := (f ∘ pbottom) '' Icc a b
  let Sright := (f ∘ pright) '' Icc c d
  let Stop := (f ∘ ptop) '' Icc a b
  let Sleft := (f ∘ pleft) '' Icc c d
  have hbottom_right : (Sbottom ∩ Sright).Nonempty := by
    refine ⟨f (pbottom b), ?_, ?_⟩
    · exact ⟨b, right_mem_Icc.mpr hab.le, rfl⟩
    · refine ⟨c, left_mem_Icc.mpr hcd.le, ?_⟩
      simp [pbottom, pright]
  have hbottom_right_top_left :
      ((Sbottom ∪ Sright) ∩ (Stop ∪ Sleft)).Nonempty := by
    refine ⟨f (pright d), ?_, ?_⟩
    · exact Or.inr ⟨d, right_mem_Icc.mpr hcd.le, rfl⟩
    · apply Or.inl
      refine ⟨b, right_mem_Icc.mpr hab.le, ?_⟩
      simp [pright, ptop]
  have htop_left : (Stop ∩ Sleft).Nonempty := by
    refine ⟨f (ptop a), ?_, ?_⟩
    · exact ⟨a, left_mem_Icc.mpr hab.le, rfl⟩
    · refine ⟨d, right_mem_Icc.mpr hcd.le, ?_⟩
      simp [ptop, pleft]
  simp only [closedRectangleBoundary, image_union, image_image]
  change Metric.ediam ((Sbottom ∪ Sright) ∪ (Stop ∪ Sleft)) ≤ _
  calc
    Metric.ediam ((Sbottom ∪ Sright) ∪ (Stop ∪ Sleft)) ≤
        Metric.ediam (Sbottom ∪ Sright) + Metric.ediam (Stop ∪ Sleft) :=
      Metric.ediam_union_le hbottom_right_top_left
    _ ≤ (Metric.ediam Sbottom + Metric.ediam Sright) +
        (Metric.ediam Stop + Metric.ediam Sleft) := by
      gcongr
      · exact Metric.ediam_union_le hbottom_right
      · exact Metric.ediam_union_le htop_left
    _ ≤ ((∫⁻ t in Ioo a b,
            ‖df (Complex.ofReal t + Complex.ofReal c * Complex.I) 1‖ₑ ∂volume) +
          (∫⁻ t in Ioo c d,
            ‖df (Complex.ofReal b + Complex.ofReal t * Complex.I) Complex.I‖ₑ ∂volume)) +
          ((∫⁻ t in Ioo a b,
            ‖df (Complex.ofReal t + Complex.ofReal d * Complex.I) 1‖ₑ ∂volume) +
          (∫⁻ t in Ioo c d,
            ‖df (Complex.ofReal a + Complex.ofReal t * Complex.I) Complex.I‖ₑ ∂volume)) := by
      gcongr
      · exact complex_image_ediam_le_lintegral_enorm_of_absolutelyContinuousOnInterval
          hab hbottom hdbottom
      · exact complex_image_ediam_le_lintegral_enorm_of_absolutelyContinuousOnInterval
          hcd hright hdright
      · exact complex_image_ediam_le_lintegral_enorm_of_absolutelyContinuousOnInterval
          hab htop hdtop
      · exact complex_image_ediam_le_lintegral_enorm_of_absolutelyContinuousOnInterval
          hcd hleft hdleft
    _ = _ := by ac_rfl

/--
%%handwave
name:
  Diameter of a real projection is controlled by the frontier
statement:
  Let $A\subset\mathbb C$ be nonempty and compact. Let
  $u:\mathbb C\to\mathbb R$ be real-linear with $\lVert u\rVert\leq1$, and
  suppose there is a unit vector $v$ with $u(v)=1$. Then
  $$
  \operatorname{diam}u(A)\leq\operatorname{diam}(\partial A).
  $$
proof:
  The function $u$ attains its minimum and maximum on $A$. Neither extremizer can be interior, since a small displacement in the $v$ or $-v$ direction would improve it. Thus both lie on the frontier, their distance bounds the diameter of $u(A)$, and the operator-norm bound compares that distance with their distance in the plane.
-/
theorem ediam_realProjection_image_le_ediam_frontier
    {s : Set ℂ} (hs : IsCompact s) (hne : s.Nonempty)
    (u : ℂ →L[ℝ] ℝ) (v : ℂ) (hu : ‖u‖ ≤ 1)
    (hv : ‖v‖ = 1) (huv : u v = 1) :
    Metric.ediam (u '' s) ≤ Metric.ediam (frontier s) := by
  obtain ⟨pmin, hpmin, hpmin_le⟩ :=
    hs.exists_isMinOn hne u.continuous.continuousOn
  obtain ⟨pmax, hpmax, hpmax_ge⟩ :=
    hs.exists_isMaxOn hne u.continuous.continuousOn
  have hpmax_frontier : pmax ∈ frontier s := by
    rw [frontier, mem_diff]
    refine ⟨subset_closure hpmax, ?_⟩
    intro hpmax_interior
    rcases Metric.mem_nhds_iff.1 (isOpen_interior.mem_nhds hpmax_interior) with
      ⟨ε, hε, hεs⟩
    let w : ℂ := pmax + (ε / 2) • v
    have hwball : w ∈ Metric.ball pmax ε := by
      rw [Metric.mem_ball, dist_eq_norm]
      simp only [w, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, hv]
      rw [mul_one, abs_of_pos (half_pos hε)]
      linarith
    have hw : w ∈ s := interior_subset (hεs hwball)
    have huw : u pmax < u w := by
      simp only [w, map_add, map_smul, huv, smul_eq_mul, mul_one]
      linarith
    exact (not_lt_of_ge (hpmax_ge hw)) huw
  have hpmin_frontier : pmin ∈ frontier s := by
    rw [frontier, mem_diff]
    refine ⟨subset_closure hpmin, ?_⟩
    intro hpmin_interior
    rcases Metric.mem_nhds_iff.1 (isOpen_interior.mem_nhds hpmin_interior) with
      ⟨ε, hε, hεs⟩
    let w : ℂ := pmin - (ε / 2) • v
    have hwball : w ∈ Metric.ball pmin ε := by
      rw [Metric.mem_ball, dist_eq_norm]
      simp only [w, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, hv]
      rw [mul_one, abs_of_pos (half_pos hε)]
      linarith
    have hw : w ∈ s := interior_subset (hεs hwball)
    have huw : u w < u pmin := by
      simp only [w, map_sub, map_smul, huv, smul_eq_mul, mul_one]
      linarith
    exact (not_lt_of_ge (hpmin_le hw)) huw
  rw [Metric.ediam_image_le_iff]
  intro x hx y hy
  have hminmax : u pmin ≤ u pmax := hpmin_le hpmax
  have hxIcc : u x ∈ uIcc (u pmin) (u pmax) := by
    rw [uIcc_of_le hminmax]
    exact ⟨hpmin_le hx, hpmax_ge hx⟩
  have hyIcc : u y ∈ uIcc (u pmin) (u pmax) := by
    rw [uIcc_of_le hminmax]
    exact ⟨hpmin_le hy, hpmax_ge hy⟩
  calc
    edist (u x) (u y) = ENNReal.ofReal |u y - u x| := by
      rw [edist_dist, Real.dist_eq, abs_sub_comm]
    _ ≤ ENNReal.ofReal |u pmax - u pmin| :=
      ENNReal.ofReal_le_ofReal
        (abs_sub_le_of_uIcc_subset_uIcc (uIcc_subset_uIcc hxIcc hyIcc))
    _ = edist (u pmin) (u pmax) := by
      rw [edist_dist, Real.dist_eq, abs_sub_comm]
    _ ≤ edist pmin pmax := by
      rw [edist_dist, edist_dist]
      apply ENNReal.ofReal_le_ofReal
      rw [dist_eq_norm, dist_eq_norm, ← map_sub]
      exact (u.le_opNorm _).trans
        (mul_le_of_le_one_left (norm_nonneg _) hu)
    _ ≤ Metric.ediam (frontier s) :=
      Metric.edist_le_ediam_of_mem hpmin_frontier hpmax_frontier

/--
%%handwave
name:
  Planar volume is controlled by frontier diameter
statement:
  Every nonempty compact set $A\subset\mathbb C$ satisfies
  $$
  |A|\leq\operatorname{diam}(\partial A)^2.
  $$
proof:
  Lebesgue measure is preserved by the real-imaginary coordinate equivalence, and planar volume is at most the square of the diameter in product coordinates. Apply [the frontier estimate for real projections](lean:JJMath.Quasiconformal.ediam_realProjection_image_le_ediam_frontier) to the real and imaginary coordinate maps.
-/
theorem complex_volume_le_ediam_frontier_sq
    {s : Set ℂ} (hs : IsCompact s) (hne : s.Nonempty) :
    volume s ≤ Metric.ediam (frontier s) ^ 2 := by
  have hre : Metric.ediam (Complex.reCLM '' s) ≤ Metric.ediam (frontier s) :=
    ediam_realProjection_image_le_ediam_frontier hs hne
      Complex.reCLM 1 (by rw [Complex.reCLM_norm]) (by simp) (by simp)
  have him : Metric.ediam (Complex.imCLM '' s) ≤ Metric.ediam (frontier s) :=
    ediam_realProjection_image_le_ediam_frontier hs hne
      Complex.imCLM Complex.I (by rw [Complex.imCLM_norm]) (by simp) (by simp)
  have hed :
      Metric.ediam (Complex.measurableEquivPi '' s) ≤
        Metric.ediam (frontier s) := by
    rw [Metric.ediam_image_le_iff]
    intro z hz w hw
    rw [edist_pi_le_iff]
    intro i
    fin_cases i
    · simpa using (Metric.ediam_image_le_iff.mp hre z hz w hw)
    · simpa using (Metric.ediam_image_le_iff.mp him z hz w hw)
  calc
    volume s = volume (Complex.measurableEquivPi '' s) := by
      rw [← Complex.volume_preserving_equiv_pi.symm.measure_preimage
        hs.measurableSet.nullMeasurableSet]
      congr 1
      ext p
      constructor
      · intro hp
        exact ⟨Complex.measurableEquivPi.symm p, hp,
          Complex.measurableEquivPi.apply_symm_apply p⟩
      · rintro ⟨x, hx, rfl⟩
        simpa using hx
    _ ≤ Metric.ediam (Complex.measurableEquivPi '' s) ^ 2 := by
      simpa using Real.volume_pi_le_diam_pow
        (Complex.measurableEquivPi '' s)
    _ ≤ Metric.ediam (frontier s) ^ 2 :=
      pow_le_pow_left₀ (by simp) hed 2

/--
%%handwave
name:
  Area of a domain-homeomorphism rectangle image from its boundary diameter
statement:
  Let $F:\Omega\to\Omega'$ be a homeomorphism with $\Omega'$ open. If
  $a<b$, $c<d$, and the closed rectangle
  $R=[a,b]\times[c,d]$ lies in $\Omega$, then
  $$
  |F(R)|\leq\operatorname{diam}(F(\partial R))^2.
  $$
proof:
  The rectangle image is nonempty and compact by [continuity of the ambient representative on its source](lean:JJMath.Quasiconformal.continuousOn_ambientMap). Apply [the compact-set volume bound](lean:JJMath.Quasiconformal.complex_volume_le_ediam_frontier_sq), use [the compact-image frontier inclusion](lean:JJMath.Quasiconformal.frontier_ambientMap_image_subset), and identify the source frontier with the four rectangle sides.
-/
theorem complex_volume_ambientMap_image_closedRectangle_le_boundary_ediam_sq
    {Ω Ω' : Set ℂ} (F : Ω ≃ₜ Ω') (hΩ' : IsOpen Ω')
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hrectΩ : closedRectangle a b c d ⊆ Ω) :
    volume (ambientMap F '' closedRectangle a b c d) ≤
      Metric.ediam (ambientMap F '' closedRectangleBoundary a b c d) ^ 2 := by
  have hrect_compact : IsCompact (closedRectangle a b c d) := by
    rw [closedRectangle, ← Complex.preimage_equivRealProd_prod]
    exact Complex.equivRealProdCLM.toHomeomorph.isCompact_preimage.2
      (isCompact_Icc.prod isCompact_Icc)
  have hrect_nonempty : (closedRectangle a b c d).Nonempty := by
    refine ⟨Complex.ofReal a + Complex.ofReal c * Complex.I, ?_⟩
    rw [closedRectangle, Complex.mem_reProdIm]
    constructor
    · simpa using (show a ∈ Icc a b from ⟨le_rfl, hab.le⟩)
    · simpa using (show c ∈ Icc c d from ⟨le_rfl, hcd.le⟩)
  have himage_compact : IsCompact (ambientMap F '' closedRectangle a b c d) :=
    hrect_compact.image_of_continuousOn
      ((continuousOn_ambientMap F).mono hrectΩ)
  have himage_nonempty :
      (ambientMap F '' closedRectangle a b c d).Nonempty :=
    hrect_nonempty.image (ambientMap F)
  have hfrontier :
      frontier (ambientMap F '' closedRectangle a b c d) ⊆
        ambientMap F '' closedRectangleBoundary a b c d := by
    rw [← frontier_closedRectangle hab hcd]
    exact frontier_ambientMap_image_subset F hΩ' hrect_compact hrectΩ
  calc
    volume (ambientMap F '' closedRectangle a b c d) ≤
        Metric.ediam
            (frontier (ambientMap F '' closedRectangle a b c d)) ^ 2 :=
      complex_volume_le_ediam_frontier_sq himage_compact himage_nonempty
    _ ≤ Metric.ediam
          (ambientMap F '' closedRectangleBoundary a b c d) ^ 2 :=
      pow_le_pow_left₀ (by simp) (Metric.ediam_mono hfrontier) 2

/--
%%handwave
name:
  Good product fiber with at most average energy
statement:
  Let $H:\mathbb R^2\to[0,\infty]$ be measurable on
  $(a,b)\times(c,d)$, where $c<d$, and suppose a property $P(y)$ holds for
  almost every $y\in(c,d)$. Then there is $y\in(c,d)$ satisfying $P(y)$ and
  $$
  \int_a^b H(x,y)\,dx
    \leq\frac{1}{d-c}
      \int_{(a,b)\times(c,d)}H(x,y)\,dx\,dy.
  $$
proof:
  Tonelli's theorem identifies the integral of the fiber energies with the product integral. The first-moment principle supplies a fiber whose energy is no larger than their average; choose it outside the null set where either $P$ fails or the coordinate lies outside $(c,d)$.
-/
theorem exists_good_horizontal_fiber_le_average
    {H : ℝ × ℝ → ℝ≥0∞} {a b c d : ℝ}
    (hcd : c < d)
    (hH : AEMeasurable H
      (((volume : Measure ℝ).prod volume).restrict
        (Ioo a b ×ˢ Ioo c d)))
    {P : ℝ → Prop}
    (hP : ∀ᵐ y ∂(volume : Measure ℝ).restrict (Ioo c d), P y) :
    ∃ y ∈ Ioo c d, P y ∧
      (∫⁻ x in Ioo a b, H (x, y) ∂volume) ≤
        (∫⁻ z in Ioo a b ×ˢ Ioo c d, H z ∂(volume.prod volume)) /
          ENNReal.ofReal (d - c) := by
  let μx : Measure ℝ := volume.restrict (Ioo a b)
  let μy : Measure ℝ := volume.restrict (Ioo c d)
  let fiber : ℝ → ℝ≥0∞ := fun y => ∫⁻ x in Ioo a b, H (x, y) ∂volume
  have hHprod : AEMeasurable H (μx.prod μy) := by
    simpa [μx, μy, Measure.prod_restrict] using hH
  have hfiber : AEMeasurable fiber μy := by
    simpa [fiber, μx] using hHprod.lintegral_prod_left'
  have hμy : μy ≠ 0 := by
    change (volume : Measure ℝ).restrict (Ioo c d) ≠ 0
    intro hzero
    have hvolzero := Measure.restrict_eq_zero.mp hzero
    rw [Real.volume_Ioo] at hvolzero
    exact (ENNReal.ofReal_ne_zero_iff.mpr (sub_pos.mpr hcd)) hvolzero
  have hmem : ∀ᵐ y ∂μy, y ∈ Ioo c d :=
    ae_restrict_mem measurableSet_Ioo
  have hgood : ∀ᵐ y ∂μy, y ∈ Ioo c d ∧ P y := by
    filter_upwards [hmem, hP] with y hy hPy
    exact ⟨hy, hPy⟩
  let N : Set ℝ := {y | ¬(y ∈ Ioo c d ∧ P y)}
  have hN : μy N = 0 := ae_iff.mp hgood
  obtain ⟨y, hyN, hyavg⟩ :=
    exists_notMem_null_le_laverage hμy hfiber hN
  refine ⟨y, (not_not.mp hyN).1, (not_not.mp hyN).2, ?_⟩
  rw [laverage_eq] at hyavg
  simp only [μy, Measure.restrict_apply_univ, Real.volume_Ioo] at hyavg
  rw [← setLIntegral_prod_symm H hH] at hyavg
  exact hyavg

/--
%%handwave
name:
  Good vertical product fiber with at most average energy
statement:
  Let $H:\mathbb R^2\to[0,\infty]$ be measurable on
  $(a,b)\times(c,d)$, where $a<b$, and suppose a property $P(x)$ holds for
  almost every $x\in(a,b)$. Then there is $x\in(a,b)$ satisfying $P(x)$ and
  $$
  \int_c^d H(x,y)\,dy
    \leq\frac{1}{b-a}
      \int_{(a,b)\times(c,d)}H(x,y)\,dx\,dy.
  $$
proof:
  Tonelli's theorem writes the product integral as the integral of the vertical fiber energies. Apply the first-moment principle while avoiding the null set where either $P$ fails or the coordinate lies outside $(a,b)$.
-/
theorem exists_good_vertical_fiber_le_average
    {H : ℝ × ℝ → ℝ≥0∞} {a b c d : ℝ}
    (hab : a < b)
    (hH : AEMeasurable H
      (((volume : Measure ℝ).prod volume).restrict
        (Ioo a b ×ˢ Ioo c d)))
    {P : ℝ → Prop}
    (hP : ∀ᵐ x ∂(volume : Measure ℝ).restrict (Ioo a b), P x) :
    ∃ x ∈ Ioo a b, P x ∧
      (∫⁻ y in Ioo c d, H (x, y) ∂volume) ≤
        (∫⁻ z in Ioo a b ×ˢ Ioo c d, H z ∂(volume.prod volume)) /
          ENNReal.ofReal (b - a) := by
  let μx : Measure ℝ := volume.restrict (Ioo a b)
  let μy : Measure ℝ := volume.restrict (Ioo c d)
  let fiber : ℝ → ℝ≥0∞ := fun x => ∫⁻ y in Ioo c d, H (x, y) ∂volume
  have hHprod : AEMeasurable H (μx.prod μy) := by
    simpa [μx, μy, Measure.prod_restrict] using hH
  have hfiber : AEMeasurable fiber μx := by
    simpa [fiber, μy] using hHprod.lintegral_prod_right'
  have hμx : μx ≠ 0 := by
    change (volume : Measure ℝ).restrict (Ioo a b) ≠ 0
    intro hzero
    have hvolzero := Measure.restrict_eq_zero.mp hzero
    rw [Real.volume_Ioo] at hvolzero
    exact (ENNReal.ofReal_ne_zero_iff.mpr (sub_pos.mpr hab)) hvolzero
  have hmem : ∀ᵐ x ∂μx, x ∈ Ioo a b :=
    ae_restrict_mem measurableSet_Ioo
  have hgood : ∀ᵐ x ∂μx, x ∈ Ioo a b ∧ P x := by
    filter_upwards [hmem, hP] with x hx hPx
    exact ⟨hx, hPx⟩
  let N : Set ℝ := {x | ¬(x ∈ Ioo a b ∧ P x)}
  have hN : μx N = 0 := ae_iff.mp hgood
  obtain ⟨x, hxN, hxavg⟩ :=
    exists_notMem_null_le_laverage hμx hfiber hN
  refine ⟨x, (not_not.mp hxN).1, (not_not.mp hxN).2, ?_⟩
  rw [laverage_eq] at hxavg
  simp only [μx, Measure.restrict_apply_univ, Real.volume_Ioo] at hxavg
  rw [← setLIntegral_prod H hH] at hxavg
  exact hxavg

/--
%%handwave
name:
  Four good sides surrounding a rectangle
statement:
  Let $A<a<b<B$ and $C<c<d<D$. Let
  $H:\mathbb R^2\to[0,\infty]$ be measurable on
  $(A,B)\times(C,D)$, and suppose horizontal and vertical good-line
  properties hold almost everywhere. There are
  $$
  x_\ell\in(A,a),\quad x_r\in(b,B),\quad
  y_b\in(C,c),\quad y_t\in(d,D)
  $$
  satisfying the appropriate good-line properties, such that the energy on
  each selected side is at most the energy in its corresponding outer strip
  divided by the width of that strip.
proof:
  Restrict the product density to the left, right, bottom, and top strips. Apply [the vertical first-moment selector](lean:JJMath.Quasiconformal.exists_good_vertical_fiber_le_average) to the first two strips and [the horizontal first-moment selector](lean:JJMath.Quasiconformal.exists_good_horizontal_fiber_le_average) to the last two.
-/
theorem exists_good_rectangle_frame_le_average
    {H : ℝ × ℝ → ℝ≥0∞} {A a b B C c d D : ℝ}
    (hAa : A < a) (hab : a < b) (hbB : b < B)
    (hCc : C < c) (hcd : c < d) (hdD : d < D)
    (hH : AEMeasurable H
      (((volume : Measure ℝ).prod volume).restrict
        (Ioo A B ×ˢ Ioo C D)))
    {Ph Pv : ℝ → Prop}
    (hPh : ∀ᵐ y ∂(volume : Measure ℝ), Ph y)
    (hPv : ∀ᵐ x ∂(volume : Measure ℝ), Pv x) :
    ∃ xl ∈ Ioo A a, ∃ xr ∈ Ioo b B,
      ∃ yb ∈ Ioo C c, ∃ yt ∈ Ioo d D,
        Pv xl ∧ Pv xr ∧ Ph yb ∧ Ph yt ∧
        (∫⁻ y in Ioo C D, H (xl, y) ∂volume) ≤
          (∫⁻ z in Ioo A a ×ˢ Ioo C D, H z ∂(volume.prod volume)) /
            ENNReal.ofReal (a - A) ∧
        (∫⁻ y in Ioo C D, H (xr, y) ∂volume) ≤
          (∫⁻ z in Ioo b B ×ˢ Ioo C D, H z ∂(volume.prod volume)) /
            ENNReal.ofReal (B - b) ∧
        (∫⁻ x in Ioo A B, H (x, yb) ∂volume) ≤
          (∫⁻ z in Ioo A B ×ˢ Ioo C c, H z ∂(volume.prod volume)) /
            ENNReal.ofReal (c - C) ∧
        (∫⁻ x in Ioo A B, H (x, yt) ∂volume) ≤
          (∫⁻ z in Ioo A B ×ˢ Ioo d D, H z ∂(volume.prod volume)) /
            ENNReal.ofReal (D - d) := by
  have hleft_subset : Ioo A a ×ˢ Ioo C D ⊆ Ioo A B ×ˢ Ioo C D := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact ⟨⟨hx.1, lt_trans hx.2 (lt_trans hab hbB)⟩, hy⟩
  have hright_subset : Ioo b B ×ˢ Ioo C D ⊆ Ioo A B ×ˢ Ioo C D := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact ⟨⟨lt_trans (lt_trans hAa hab) hx.1, hx.2⟩, hy⟩
  have hbottom_subset : Ioo A B ×ˢ Ioo C c ⊆ Ioo A B ×ˢ Ioo C D := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact ⟨hx, ⟨hy.1, lt_trans hy.2 (lt_trans hcd hdD)⟩⟩
  have htop_subset : Ioo A B ×ˢ Ioo d D ⊆ Ioo A B ×ˢ Ioo C D := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact ⟨hx, ⟨lt_trans (lt_trans hCc hcd) hy.1, hy.2⟩⟩
  have hHleft := hH.mono_measure
    (Measure.restrict_mono hleft_subset le_rfl)
  have hHright := hH.mono_measure
    (Measure.restrict_mono hright_subset le_rfl)
  have hHbottom := hH.mono_measure
    (Measure.restrict_mono hbottom_subset le_rfl)
  have hHtop := hH.mono_measure
    (Measure.restrict_mono htop_subset le_rfl)
  obtain ⟨xl, hxl, hPxl, hExl⟩ :=
    exists_good_vertical_fiber_le_average
      (a := A) (b := a) (c := C) (d := D) hAa hHleft
        (ae_restrict_of_ae hPv)
  obtain ⟨xr, hxr, hPxr, hExr⟩ :=
    exists_good_vertical_fiber_le_average
      (a := b) (b := B) (c := C) (d := D) hbB hHright
        (ae_restrict_of_ae hPv)
  obtain ⟨yb, hyb, hPyb, hEyb⟩ :=
    exists_good_horizontal_fiber_le_average
      (a := A) (b := B) (c := C) (d := c) hCc hHbottom
        (ae_restrict_of_ae hPh)
  obtain ⟨yt, hyt, hPyt, hEyt⟩ :=
    exists_good_horizontal_fiber_le_average
      (a := A) (b := B) (c := d) (d := D) hdD hHtop
        (ae_restrict_of_ae hPh)
  exact ⟨xl, hxl, xr, hxr, yb, hyb, yt, hyt,
    hPxl, hPxr, hPyb, hPyt, hExl, hExr, hEyb, hEyt⟩

/--
%%handwave
name:
  Horizontally ACL-good line
statement:
  A horizontal line of height $y$ is ACL-good for $(f,Df)$ in
  $Q\subseteq\mathbb C$ when, on every interval
  $[a,b]\subset(0,1)$ whose segment $\{t+iy:a\leq t\leq b\}$ lies in $Q$,
  the function $t\mapsto f(t+iy)$ is absolutely continuous and has derivative
  $$
    \frac d{dt}f(t+iy)=Df(t+iy)(1)
  $$
  almost everywhere.
-/
def IsHorizontalACLLineOn
    (Q : Set ℂ) (f : ℂ → ℂ) (df : ℂ → ℂ →L[ℝ] ℂ) (y : ℝ) : Prop :=
  ∀ a b : ℝ, 0 < a → a < b → b < 1 →
    (∀ r ∈ Icc a b, Complex.equivRealProdCLM.symm (r, y) ∈ Q) →
      AbsolutelyContinuousOnInterval
          (fun r : ℝ => f (Complex.equivRealProdCLM.symm (r, y))) a b ∧
        ∀ᵐ t ∂(volume : Measure ℝ).restrict (Ioo a b),
          HasDerivAt
            (fun r : ℝ => f (Complex.equivRealProdCLM.symm (r, y)))
            (df (Complex.equivRealProdCLM.symm (t, y)) 1) t

/--
%%handwave
name:
  Vertically ACL-good line
statement:
  A vertical line of real coordinate $x$ is ACL-good for $(f,Df)$ in
  $Q\subseteq\mathbb C$ when, on every interval
  $[a,b]\subset(0,1)$ whose segment $\{x+it:a\leq t\leq b\}$ lies in $Q$,
  the function $t\mapsto f(x+it)$ is absolutely continuous and has derivative
  $$
    \frac d{dt}f(x+it)=Df(x+it)(i)
  $$
  almost everywhere.
-/
def IsVerticalACLLineOn
    (Q : Set ℂ) (f : ℂ → ℂ) (df : ℂ → ℂ →L[ℝ] ℂ) (x : ℝ) : Prop :=
  ∀ a b : ℝ, 0 < a → a < b → b < 1 →
    (∀ r ∈ Icc a b,
      Complex.ofReal x + Complex.ofReal r * Complex.I ∈ Q) →
      AbsolutelyContinuousOnInterval
          (fun r : ℝ => f (Complex.ofReal x + Complex.ofReal r * Complex.I)) a b ∧
        ∀ᵐ t ∂(volume : Measure ℝ).restrict (Ioo a b),
          HasDerivAt
            (fun r : ℝ => f (Complex.ofReal x + Complex.ofReal r * Complex.I))
            (df (Complex.ofReal x + Complex.ofReal t * Complex.I) Complex.I) t

/--
%%handwave
name:
  ACL rectangle frame with controlled weak energy
statement:
  Let $A<a<b<B$ and $C<c<d<D$, and suppose the closed outer rectangle lies
  in an open planar region where a continuous map $f$ is locally
  $W^{1,2}$ with weak differential $Df$. There are
  $$
  x_\ell\in(A,a),\quad x_r\in(b,B),\quad
  y_b\in(C,c),\quad y_t\in(d,D)
  $$
  such that both selected vertical lines and both selected horizontal lines
  are ACL-good on every protected subsegment of the outer rectangle. Moreover,
  the integral of $\lVert Df\rVert^2$ on each selected line is at most the
  integral over its corresponding outer strip divided by the strip width.
proof:
  By [planar horizontal ACL](lean:JJMath.Quasiconformal.planarWeakSobolev_horizontal_acl_on_compact_of_continuousOn) and [planar vertical ACL](lean:JJMath.Quasiconformal.planarWeakSobolev_vertical_acl_on_compact_of_continuousOn), the required good-line properties hold almost everywhere. Pull the measurable squared operator norm of $Df$ into product coordinates using the volume-preserving real-imaginary equivalence, then apply [the four-strip first-moment selector](lean:JJMath.Quasiconformal.exists_good_rectangle_frame_le_average).
-/
theorem IsLocalW12On.exists_acl_rectangle_frame_le_average
    {Ω : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    {A a b B C c d D : ℝ}
    (hAa : A < a) (hab : a < b) (hbB : b < B)
    (hCc : C < c) (hcd : c < d) (hdD : d < D)
    (hQΩ : closedRectangle A B C D ⊆ Ω)
    (hf_cont : ContinuousOn f Ω)
    (hW : IsLocalW12On Ω f df) :
    ∃ xl ∈ Ioo A a, ∃ xr ∈ Ioo b B,
      ∃ yb ∈ Ioo C c, ∃ yt ∈ Ioo d D,
        IsVerticalACLLineOn (closedRectangle A B C D) f df xl ∧
        IsVerticalACLLineOn (closedRectangle A B C D) f df xr ∧
        IsHorizontalACLLineOn (closedRectangle A B C D) f df yb ∧
        IsHorizontalACLLineOn (closedRectangle A B C D) f df yt ∧
        (∫⁻ y in Ioo C D,
          ‖df (Complex.ofReal xl + Complex.ofReal y * Complex.I)‖ₑ ^ 2 ∂volume) ≤
          (∫⁻ z in Ioo A a ×ˢ Ioo C D,
            ‖df (Complex.equivRealProdCLM.symm z)‖ₑ ^ 2
              ∂(volume.prod volume)) / ENNReal.ofReal (a - A) ∧
        (∫⁻ y in Ioo C D,
          ‖df (Complex.ofReal xr + Complex.ofReal y * Complex.I)‖ₑ ^ 2 ∂volume) ≤
          (∫⁻ z in Ioo b B ×ˢ Ioo C D,
            ‖df (Complex.equivRealProdCLM.symm z)‖ₑ ^ 2
              ∂(volume.prod volume)) / ENNReal.ofReal (B - b) ∧
        (∫⁻ x in Ioo A B,
          ‖df (Complex.equivRealProdCLM.symm (x, yb))‖ₑ ^ 2 ∂volume) ≤
          (∫⁻ z in Ioo A B ×ˢ Ioo C c,
            ‖df (Complex.equivRealProdCLM.symm z)‖ₑ ^ 2
              ∂(volume.prod volume)) / ENNReal.ofReal (c - C) ∧
        (∫⁻ x in Ioo A B,
          ‖df (Complex.equivRealProdCLM.symm (x, yt))‖ₑ ^ 2 ∂volume) ≤
          (∫⁻ z in Ioo A B ×ˢ Ioo d D,
            ‖df (Complex.equivRealProdCLM.symm z)‖ₑ ^ 2
              ∂(volume.prod volume)) / ENNReal.ofReal (D - d) := by
  let Q := closedRectangle A B C D
  let Pbox := Ioo A B ×ˢ Ioo C D
  let e : (ℝ × ℝ) ≃L[ℝ] ℂ := Complex.equivRealProdCLM.symm
  let H : ℝ × ℝ → ℝ≥0∞ := fun p => ‖df (e p)‖ₑ ^ 2
  have hQcompact : IsCompact Q := by
    change IsCompact (closedRectangle A B C D)
    rw [closedRectangle, ← Complex.preimage_equivRealProd_prod]
    exact Complex.equivRealProdCLM.toHomeomorph.isCompact_preimage.2
      (isCompact_Icc.prod isCompact_Icc)
  have he_maps : MapsTo e Pbox Q := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    change e (x, y) ∈ closedRectangle A B C D
    rw [closedRectangle, Complex.mem_reProdIm]
    simpa [e, Complex.equivRealProdCLM_symm_apply] using
      (show x ∈ Icc A B ∧ y ∈ Icc C D from
        ⟨⟨hx.1.le, hx.2.le⟩, ⟨hy.1.le, hy.2.le⟩⟩)
  have he_mp : MeasurePreserving e
      ((volume : Measure ℝ).prod volume) (volume : Measure ℂ) := by
    simpa [e, Measure.volume_eq_prod] using
      Complex.volume_preserving_equiv_real_prod.symm
  have he_qmp : Measure.QuasiMeasurePreserving e
      (((volume : Measure ℝ).prod volume).restrict Pbox)
      ((volume : Measure ℂ).restrict Q) :=
    he_mp.quasiMeasurePreserving.restrict he_maps
  have hdfLp : MemLp df 2 ((volume : Measure ℂ).restrict Q) :=
    (hW.2.2 Q hQcompact hQΩ).2
  have hH : AEMeasurable H
      (((volume : Measure ℝ).prod volume).restrict Pbox) := by
    exact
      (hdfLp.aestronglyMeasurable.comp_quasiMeasurePreserving he_qmp).enorm.pow_const 2
  have hPh : ∀ᵐ y ∂(volume : Measure ℝ),
      IsHorizontalACLLineOn Q f df y := by
    simpa [IsHorizontalACLLineOn, Q] using
      planarWeakSobolev_horizontal_acl_on_compact_of_continuousOn
        hQcompact hQΩ hW.1 hf_cont hW.2.1
  have hPv : ∀ᵐ x ∂(volume : Measure ℝ),
      IsVerticalACLLineOn Q f df x := by
    simpa [IsVerticalACLLineOn, Q] using
      planarWeakSobolev_vertical_acl_on_compact_of_continuousOn
        hQcompact hQΩ hW.1 hf_cont hW.2.1
  have hframe := exists_good_rectangle_frame_le_average
    hAa hab hbB hCc hcd hdD hH hPh hPv
  simpa [H, e, Pbox, Q, Complex.equivRealProdCLM_symm_apply] using hframe

/--
%%handwave
name:
  One-dimensional Cauchy--Schwarz estimate in extended values
statement:
  If $h:(a,b)\to[0,\infty]$ is measurable, then
  $$
  \int_a^b h(t)\,dt
    \leq
    \left(\int_a^b h(t)^2\,dt\right)^{1/2}(b-a)_+^{1/2}.
  $$
proof:
  Apply Hölder's inequality with conjugate exponents $2$ and $2$ to $h\cdot1$. The integral of the constant function is the Lebesgue measure of $(a,b)$, namely $(b-a)_+$.
-/
theorem lintegral_le_rpow_two_mul_intervalLength
    {h : ℝ → ℝ≥0∞} {a b : ℝ}
    (hh : AEMeasurable h ((volume : Measure ℝ).restrict (Ioo a b))) :
    (∫⁻ t in Ioo a b, h t ∂volume) ≤
      (∫⁻ t in Ioo a b, h t ^ (2 : ℝ) ∂volume) ^ ((2 : ℝ)⁻¹) *
        ENNReal.ofReal (b - a) ^ ((2 : ℝ)⁻¹) := by
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq
    (μ := (volume : Measure ℝ).restrict (Ioo a b))
    (p := (2 : ℝ)) (q := (2 : ℝ))
    (f := h) (g := fun _ => (1 : ℝ≥0∞))
    Real.HolderConjugate.two_two hh aemeasurable_const
  simpa [Real.volume_Ioo, one_div] using hholder

/--
%%handwave
name:
  Cauchy--Schwarz estimate for an ACL derivative
statement:
  Let $a<b$. If $f:[a,b]\to\mathbb C$ is absolutely continuous and
  $f'(t)=g(t)$ almost everywhere, then
  $$
  \int_a^b\lVert g(t)\rVert\,dt
    \leq
    \left(\int_a^b\lVert g(t)\rVert^2\,dt\right)^{1/2}
      (b-a)^{1/2}.
  $$
proof:
  The derivative field is interval-integrable by [integrability of the derivative of an absolutely continuous complex curve](lean:JJMath.Quasiconformal.complex_intervalIntegrable_of_absolutelyContinuousOnInterval_of_ae_hasDerivAt), hence its norm is measurable on $(a,b)$. Apply [the extended-valued one-dimensional Cauchy--Schwarz estimate](lean:JJMath.Quasiconformal.lintegral_le_rpow_two_mul_intervalLength).
-/
theorem complex_lintegral_enorm_le_rpow_energy_of_absolutelyContinuousOnInterval
    {f g : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hderiv : ∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt f (g t) t) :
    (∫⁻ t in Ioo a b, ‖g t‖ₑ ∂volume) ≤
      (∫⁻ t in Ioo a b, ‖g t‖ₑ ^ 2 ∂volume) ^ ((2 : ℝ)⁻¹) *
        ENNReal.ofReal (b - a) ^ ((2 : ℝ)⁻¹) := by
  have hgint :=
    complex_intervalIntegrable_of_absolutelyContinuousOnInterval_of_ae_hasDerivAt
      hab hf hderiv
  have hgmeas : AEStronglyMeasurable g
      ((volume : Measure ℝ).restrict (Ioo a b)) :=
    (hgint.def'.mono_set (by
      intro t ht
      rw [uIoc_of_le hab.le]
      exact ⟨ht.1, ht.2.le⟩)).aestronglyMeasurable
  simpa [ENNReal.rpow_two] using
    lintegral_le_rpow_two_mul_intervalLength hgmeas.enorm

/--
%%handwave
name:
  Rectangle-boundary diameter from weak line energies
statement:
  Let $a<b$ and $c<d$. Suppose the four side restrictions of
  $f:\mathbb C\to\mathbb C$ are absolutely continuous and have
  almost-everywhere derivatives $Df(1)$ on horizontal sides and $Df(i)$ on
  vertical sides. Then the diameter of the mapped boundary is at most
  $$
  \begin{aligned}
  &\left(\int_a^b\lVert Df(t+ic)\rVert^2dt\right)^{1/2}(b-a)^{1/2}
  +\left(\int_c^d\lVert Df(b+it)\rVert^2dt\right)^{1/2}(d-c)^{1/2}\\
  &+\left(\int_a^b\lVert Df(t+id)\rVert^2dt\right)^{1/2}(b-a)^{1/2}
  +\left(\int_c^d\lVert Df(a+it)\rVert^2dt\right)^{1/2}(d-c)^{1/2}.
  \end{aligned}
  $$
proof:
  Start with [the four-side line-integral estimate](lean:JJMath.Quasiconformal.planar_rectangleBoundary_ediam_le_lintegral_enorm). Apply [Cauchy--Schwarz to each ACL derivative](lean:JJMath.Quasiconformal.complex_lintegral_enorm_le_rpow_energy_of_absolutelyContinuousOnInterval), and use $\lVert Df(v)\rVert\leq\lVert Df\rVert$ for the unit vectors $v=1,i$.
-/
theorem planar_rectangleBoundary_ediam_le_rpow_energy
    {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ} {a b c d : ℝ}
    (hab : a < b) (hcd : c < d)
    (hbottom : AbsolutelyContinuousOnInterval
      (fun r : ℝ => f (Complex.ofReal r + Complex.ofReal c * Complex.I)) a b)
    (hright : AbsolutelyContinuousOnInterval
      (fun r : ℝ => f (Complex.ofReal b + Complex.ofReal r * Complex.I)) c d)
    (htop : AbsolutelyContinuousOnInterval
      (fun r : ℝ => f (Complex.ofReal r + Complex.ofReal d * Complex.I)) a b)
    (hleft : AbsolutelyContinuousOnInterval
      (fun r : ℝ => f (Complex.ofReal a + Complex.ofReal r * Complex.I)) c d)
    (hdbottom : ∀ᵐ t ∂volume.restrict (Ioo a b),
      HasDerivAt
        (fun r : ℝ => f (Complex.ofReal r + Complex.ofReal c * Complex.I))
        (df (Complex.ofReal t + Complex.ofReal c * Complex.I) 1) t)
    (hdright : ∀ᵐ t ∂volume.restrict (Ioo c d),
      HasDerivAt
        (fun r : ℝ => f (Complex.ofReal b + Complex.ofReal r * Complex.I))
        (df (Complex.ofReal b + Complex.ofReal t * Complex.I) Complex.I) t)
    (hdtop : ∀ᵐ t ∂volume.restrict (Ioo a b),
      HasDerivAt
        (fun r : ℝ => f (Complex.ofReal r + Complex.ofReal d * Complex.I))
        (df (Complex.ofReal t + Complex.ofReal d * Complex.I) 1) t)
    (hdleft : ∀ᵐ t ∂volume.restrict (Ioo c d),
      HasDerivAt
        (fun r : ℝ => f (Complex.ofReal a + Complex.ofReal r * Complex.I))
        (df (Complex.ofReal a + Complex.ofReal t * Complex.I) Complex.I) t) :
    Metric.ediam (f '' closedRectangleBoundary a b c d) ≤
      (∫⁻ t in Ioo a b,
        ‖df (Complex.ofReal t + Complex.ofReal c * Complex.I)‖ₑ ^ 2 ∂volume) ^
          ((2 : ℝ)⁻¹) * ENNReal.ofReal (b - a) ^ ((2 : ℝ)⁻¹) +
      (∫⁻ t in Ioo c d,
        ‖df (Complex.ofReal b + Complex.ofReal t * Complex.I)‖ₑ ^ 2 ∂volume) ^
          ((2 : ℝ)⁻¹) * ENNReal.ofReal (d - c) ^ ((2 : ℝ)⁻¹) +
      (∫⁻ t in Ioo a b,
        ‖df (Complex.ofReal t + Complex.ofReal d * Complex.I)‖ₑ ^ 2 ∂volume) ^
          ((2 : ℝ)⁻¹) * ENNReal.ofReal (b - a) ^ ((2 : ℝ)⁻¹) +
      (∫⁻ t in Ioo c d,
        ‖df (Complex.ofReal a + Complex.ofReal t * Complex.I)‖ₑ ^ 2 ∂volume) ^
          ((2 : ℝ)⁻¹) * ENNReal.ofReal (d - c) ^ ((2 : ℝ)⁻¹) := by
  refine (planar_rectangleBoundary_ediam_le_lintegral_enorm
    hab hcd hbottom hright htop hleft hdbottom hdright hdtop hdleft).trans ?_
  have henorm_one (L : ℂ →L[ℝ] ℂ) : ‖L 1‖ₑ ≤ ‖L‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (by simpa using L.le_opNorm (1 : ℂ))
  have henorm_I (L : ℂ →L[ℝ] ℂ) : ‖L Complex.I‖ₑ ≤ ‖L‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (by simpa using L.le_opNorm Complex.I)
  gcongr
  · refine
      (complex_lintegral_enorm_le_rpow_energy_of_absolutelyContinuousOnInterval
        hab hbottom hdbottom).trans ?_
    gcongr
    exact henorm_one _
  · refine
      (complex_lintegral_enorm_le_rpow_energy_of_absolutelyContinuousOnInterval
        hcd hright hdright).trans ?_
    gcongr
    exact henorm_I _
  · refine
      (complex_lintegral_enorm_le_rpow_energy_of_absolutelyContinuousOnInterval
        hab htop hdtop).trans ?_
    gcongr
    exact henorm_one _
  · refine
      (complex_lintegral_enorm_le_rpow_energy_of_absolutelyContinuousOnInterval
        hcd hleft hdleft).trans ?_
    gcongr
    exact henorm_I _

/--
%%handwave
name:
  Weak-differential energy of an open product rectangle
statement:
  For a field $Df$ and real endpoints $A,B,C,D$, define
  $$
    E_{Df}(A,B;C,D)
      =\int_A^B\int_C^D\lVert Df(x+iy)\rVert_{\mathrm{op}}^2\,dy\,dx
      \in[0,\infty].
  $$
-/
def productRectangleEnergy
    (df : ℂ → ℂ →L[ℝ] ℂ) (A B C D : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in Ioo A B ×ˢ Ioo C D,
    ‖df (Complex.equivRealProdCLM.symm z)‖ₑ ^ 2 ∂(volume.prod volume)

/--
%%handwave
name:
  Strip-average bound for a rectangle frame
statement:
  Write $E(A,B;C,D)$ for the product-rectangle energy of $Df$. For outer
  coordinates $A<a<b<B$, $C<c<d<D$ and selected inner frame
  $x_\ell,x_r,y_b,y_t$, define
  $$
  \begin{aligned}
    B_{\mathrm{strip}}={}&
      \sqrt{\frac{E(A,B;C,c)}{c-C}}\sqrt{x_r-x_\ell}
      +\sqrt{\frac{E(b,B;C,D)}{B-b}}\sqrt{y_t-y_b}\\
      &+\sqrt{\frac{E(A,B;d,D)}{D-d}}\sqrt{x_r-x_\ell}
      +\sqrt{\frac{E(A,a;C,D)}{a-A}}\sqrt{y_t-y_b}.
  \end{aligned}
  $$
-/
def rectangleFrameStripBound
    (df : ℂ → ℂ →L[ℝ] ℂ)
    (A a b B C c d D xl xr yb yt : ℝ) : ℝ≥0∞ :=
  (productRectangleEnergy df A B C c / ENNReal.ofReal (c - C)) ^ ((2 : ℝ)⁻¹) *
      ENNReal.ofReal (xr - xl) ^ ((2 : ℝ)⁻¹) +
    (productRectangleEnergy df b B C D / ENNReal.ofReal (B - b)) ^ ((2 : ℝ)⁻¹) *
      ENNReal.ofReal (yt - yb) ^ ((2 : ℝ)⁻¹) +
    (productRectangleEnergy df A B d D / ENNReal.ofReal (D - d)) ^ ((2 : ℝ)⁻¹) *
      ENNReal.ofReal (xr - xl) ^ ((2 : ℝ)⁻¹) +
    (productRectangleEnergy df A a C D / ENNReal.ofReal (a - A)) ^ ((2 : ℝ)⁻¹) *
      ENNReal.ofReal (yt - yb) ^ ((2 : ℝ)⁻¹)

/--
%%handwave
name:
  Line-energy bound for a rectangle frame
statement:
  For a frame with sides $x_\ell,x_r,y_b,y_t$, define
  $B_{\mathrm{line}}$ as the sum over its four sides of
  $$
    \sqrt{\int_{\text{side}}\lVert Df\rVert_{\mathrm{op}}^2}\,
    \sqrt{\operatorname{length}(\text{side})}.
  $$
  The horizontal sides use the direction $x$ and the vertical sides use the
  direction $y$.
-/
def rectangleFrameLineEnergyBound
    (df : ℂ → ℂ →L[ℝ] ℂ) (xl xr yb yt : ℝ) : ℝ≥0∞ :=
  (∫⁻ x in Ioo xl xr,
      ‖df (Complex.ofReal x + Complex.ofReal yb * Complex.I)‖ₑ ^ 2 ∂volume) ^
        ((2 : ℝ)⁻¹) * ENNReal.ofReal (xr - xl) ^ ((2 : ℝ)⁻¹) +
    (∫⁻ y in Ioo yb yt,
      ‖df (Complex.ofReal xr + Complex.ofReal y * Complex.I)‖ₑ ^ 2 ∂volume) ^
        ((2 : ℝ)⁻¹) * ENNReal.ofReal (yt - yb) ^ ((2 : ℝ)⁻¹) +
    (∫⁻ x in Ioo xl xr,
      ‖df (Complex.ofReal x + Complex.ofReal yt * Complex.I)‖ₑ ^ 2 ∂volume) ^
        ((2 : ℝ)⁻¹) * ENNReal.ofReal (xr - xl) ^ ((2 : ℝ)⁻¹) +
    (∫⁻ y in Ioo yb yt,
      ‖df (Complex.ofReal xl + Complex.ofReal y * Complex.I)‖ₑ ^ 2 ∂volume) ^
        ((2 : ℝ)⁻¹) * ENNReal.ofReal (yt - yb) ^ ((2 : ℝ)⁻¹)

/-- Four side coordinates selected from the protected strips around an inner
rectangle. -/
structure ProtectedRectangleFrame
    (A a b B C c d D : ℝ) where
  xl : ℝ
  hxl : xl ∈ Ioo A a
  xr : ℝ
  hxr : xr ∈ Ioo b B
  yb : ℝ
  hyb : yb ∈ Ioo C c
  yt : ℝ
  hyt : yt ∈ Ioo d D

set_option maxHeartbeats 800000 in
/--
%%handwave
name:
  Boundary estimate for a chosen ACL rectangle frame
statement:
  Let $0<A<a<b<B<1$ and $0<C<c<d<D<1$. If
  $x_\ell\in(A,a)$, $x_r\in(b,B)$, $y_b\in(C,c)$, and
  $y_t\in(d,D)$ select four ACL-good lines, then the diameter of the image
  of $[x_\ell,x_r]\times[y_b,y_t]$ is at most the sum of the four
  Cauchy--Schwarz expressions formed from the squared weak-differential
  energies on its sides.
proof:
  Restrict each ACL-good line to the corresponding selected side, then apply [the rectangle-boundary estimate from the four side energies](lean:JJMath.Quasiconformal.planar_rectangleBoundary_ediam_le_rpow_energy).
-/
theorem rectangleBoundary_ediam_le_lineEnergy_of_acl
    {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    {A a b B C c d D xl xr yb yt : ℝ}
    (h0A : 0 < A) (hAa : A < a) (hab : a < b) (hbB : b < B) (hB1 : B < 1)
    (h0C : 0 < C) (hCc : C < c) (hcd : c < d) (hdD : d < D) (hD1 : D < 1)
    (hxl : xl ∈ Ioo A a) (hxr : xr ∈ Ioo b B)
    (hyb : yb ∈ Ioo C c) (hyt : yt ∈ Ioo d D)
    (hvl : IsVerticalACLLineOn (closedRectangle A B C D) f df xl)
    (hvr : IsVerticalACLLineOn (closedRectangle A B C D) f df xr)
    (hhb : IsHorizontalACLLineOn (closedRectangle A B C D) f df yb)
    (hht : IsHorizontalACLLineOn (closedRectangle A B C D) f df yt) :
    Metric.ediam (f '' closedRectangleBoundary xl xr yb yt) ≤
      rectangleFrameLineEnergyBound df xl xr yb yt := by
  have hxlxr : xl < xr := hxl.2.trans (hab.trans hxr.1)
  have hybyt : yb < yt := hyb.2.trans (hcd.trans hyt.1)
  have h0xl : 0 < xl := h0A.trans hxl.1
  have hxr1 : xr < 1 := hxr.2.trans hB1
  have h0yb : 0 < yb := h0C.trans hyb.1
  have hyt1 : yt < 1 := hyt.2.trans hD1
  have hx_outer : ∀ r ∈ Icc xl xr, r ∈ Icc A B := by
    intro r hr
    exact ⟨hxl.1.le.trans hr.1, hr.2.trans hxr.2.le⟩
  have hy_outer : ∀ r ∈ Icc yb yt, r ∈ Icc C D := by
    intro r hr
    exact ⟨hyb.1.le.trans hr.1, hr.2.trans hyt.2.le⟩
  have hbottom := hhb xl xr h0xl hxlxr hxr1 (by
    intro r hr
    rw [closedRectangle, Complex.mem_reProdIm]
    simpa [Complex.equivRealProdCLM_symm_apply] using
      (show r ∈ Icc A B ∧ yb ∈ Icc C D from
        ⟨hx_outer r hr, ⟨hyb.1.le, (hyb.2.trans (hcd.trans hdD)).le⟩⟩))
  have htop := hht xl xr h0xl hxlxr hxr1 (by
    intro r hr
    rw [closedRectangle, Complex.mem_reProdIm]
    simpa [Complex.equivRealProdCLM_symm_apply] using
      (show r ∈ Icc A B ∧ yt ∈ Icc C D from
        ⟨hx_outer r hr, ⟨(hCc.trans (hcd.trans hyt.1)).le, hyt.2.le⟩⟩))
  have hleft := hvl yb yt h0yb hybyt hyt1 (by
    intro r hr
    rw [closedRectangle, Complex.mem_reProdIm]
    simpa using
      (show xl ∈ Icc A B ∧ r ∈ Icc C D from
        ⟨⟨hxl.1.le, (hxl.2.trans (hab.trans hbB)).le⟩, hy_outer r hr⟩))
  have hright := hvr yb yt h0yb hybyt hyt1 (by
    intro r hr
    rw [closedRectangle, Complex.mem_reProdIm]
    simpa using
      (show xr ∈ Icc A B ∧ r ∈ Icc C D from
        ⟨⟨(hAa.trans (hab.trans hxr.1)).le, hxr.2.le⟩, hy_outer r hr⟩))
  have hbottom' := hbottom
  have htop' := htop
  simp only [Complex.equivRealProdCLM_symm_apply] at hbottom' htop'
  unfold rectangleFrameLineEnergyBound
  exact planar_rectangleBoundary_ediam_le_rpow_energy
    hxlxr hybyt hbottom'.1 hright.1 htop'.1 hleft.1
      hbottom'.2 hright.2 htop'.2 hleft.2

/--
%%handwave
name:
  Rectangle line-energy bound dominated by strip averages
statement:
  Suppose the four squared weak-differential energies on a selected rectangle
  frame are bounded by the corresponding outer-strip energies divided by the
  strip widths. Then the sum of the four Cauchy--Schwarz line-energy terms is
  at most the associated sum of square-root strip-average terms.
proof:
  Each selected side interval lies inside the corresponding full outer line.
  Monotonicity of the line integral and of the square root gives the four termwise inequalities, which are then added.
-/
theorem rectangleFrameLineEnergyBound_le_stripBound
    {df : ℂ → ℂ →L[ℝ] ℂ}
    {A a b B C c d D xl xr yb yt : ℝ}
    (hxl : xl ∈ Ioo A a) (hxr : xr ∈ Ioo b B)
    (hyb : yb ∈ Ioo C c) (hyt : yt ∈ Ioo d D)
    (hEl : (∫⁻ y in Ioo C D,
        ‖df (Complex.ofReal xl + Complex.ofReal y * Complex.I)‖ₑ ^ 2 ∂volume) ≤
      productRectangleEnergy df A a C D / ENNReal.ofReal (a - A))
    (hEr : (∫⁻ y in Ioo C D,
        ‖df (Complex.ofReal xr + Complex.ofReal y * Complex.I)‖ₑ ^ 2 ∂volume) ≤
      productRectangleEnergy df b B C D / ENNReal.ofReal (B - b))
    (hEb : (∫⁻ x in Ioo A B,
        ‖df (Complex.equivRealProdCLM.symm (x, yb))‖ₑ ^ 2 ∂volume) ≤
      productRectangleEnergy df A B C c / ENNReal.ofReal (c - C))
    (hEt : (∫⁻ x in Ioo A B,
        ‖df (Complex.equivRealProdCLM.symm (x, yt))‖ₑ ^ 2 ∂volume) ≤
      productRectangleEnergy df A B d D / ENNReal.ofReal (D - d)) :
    rectangleFrameLineEnergyBound df xl xr yb yt ≤
      rectangleFrameStripBound df A a b B C c d D xl xr yb yt := by
  have hxIoo : Ioo xl xr ⊆ Ioo A B := by
    intro x hx
    exact ⟨hxl.1.trans hx.1, hx.2.trans hxr.2⟩
  have hyIoo : Ioo yb yt ⊆ Ioo C D := by
    intro y hy
    exact ⟨hyb.1.trans hy.1, hy.2.trans hyt.2⟩
  have hEbottom :
      (∫⁻ x in Ioo xl xr,
        ‖df (Complex.ofReal x + Complex.ofReal yb * Complex.I)‖ₑ ^ 2 ∂volume) ≤
        productRectangleEnergy df A B C c / ENNReal.ofReal (c - C) := by
    refine (lintegral_mono_set hxIoo).trans ?_
    simpa [Complex.equivRealProdCLM_symm_apply] using hEb
  have hEtop :
      (∫⁻ x in Ioo xl xr,
        ‖df (Complex.ofReal x + Complex.ofReal yt * Complex.I)‖ₑ ^ 2 ∂volume) ≤
        productRectangleEnergy df A B d D / ENNReal.ofReal (D - d) := by
    refine (lintegral_mono_set hxIoo).trans ?_
    simpa [Complex.equivRealProdCLM_symm_apply] using hEt
  have hEleft :
      (∫⁻ y in Ioo yb yt,
        ‖df (Complex.ofReal xl + Complex.ofReal y * Complex.I)‖ₑ ^ 2 ∂volume) ≤
        productRectangleEnergy df A a C D / ENNReal.ofReal (a - A) := by
    exact (lintegral_mono_set hyIoo).trans hEl
  have hEright :
      (∫⁻ y in Ioo yb yt,
        ‖df (Complex.ofReal xr + Complex.ofReal y * Complex.I)‖ₑ ^ 2 ∂volume) ≤
        productRectangleEnergy df b B C D / ENNReal.ofReal (B - b) := by
    exact (lintegral_mono_set hyIoo).trans hEr
  have hbottom_term := mul_le_mul_left
    (ENNReal.rpow_le_rpow hEbottom (by positivity : 0 ≤ (2 : ℝ)⁻¹))
    (ENNReal.ofReal (xr - xl) ^ ((2 : ℝ)⁻¹))
  have hright_term := mul_le_mul_left
    (ENNReal.rpow_le_rpow hEright (by positivity : 0 ≤ (2 : ℝ)⁻¹))
    (ENNReal.ofReal (yt - yb) ^ ((2 : ℝ)⁻¹))
  have htop_term := mul_le_mul_left
    (ENNReal.rpow_le_rpow hEtop (by positivity : 0 ≤ (2 : ℝ)⁻¹))
    (ENNReal.ofReal (xr - xl) ^ ((2 : ℝ)⁻¹))
  have hleft_term := mul_le_mul_left
    (ENNReal.rpow_le_rpow hEleft (by positivity : 0 ≤ (2 : ℝ)⁻¹))
    (ENNReal.ofReal (yt - yb) ^ ((2 : ℝ)⁻¹))
  rw [rectangleFrameLineEnergyBound, rectangleFrameStripBound]
  exact
    add_le_add (add_le_add (add_le_add hbottom_term hright_term) htop_term) hleft_term

/--
%%handwave
name:
  ACL frame boundary controlled by its strip averages
statement:
  Let $0<A<a<b<B<1$ and $0<C<c<d<D<1$. Choose one vertical line in
  each protected horizontal strip and one horizontal line in each protected
  vertical strip. If the four chosen lines are ACL-good and each of their
  squared weak-differential energies is bounded by the corresponding strip
  energy divided by its width, then the image diameter of the selected
  rectangle boundary is bounded by the sum of the four square-root
  strip-average terms.
proof:
  Restrict the four ACL lines to the selected side intervals and apply [the rectangle-boundary estimate from the four line energies](lean:JJMath.Quasiconformal.planar_rectangleBoundary_ediam_le_rpow_energy). Monotonicity of line integrals and square roots replaces each restricted line energy by its strip-average bound.
-/
theorem rectangleBoundary_ediam_le_strip_averages_of_acl
    {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    {A a b B C c d D xl xr yb yt : ℝ}
    (h0A : 0 < A) (hAa : A < a) (hab : a < b) (hbB : b < B) (hB1 : B < 1)
    (h0C : 0 < C) (hCc : C < c) (hcd : c < d) (hdD : d < D) (hD1 : D < 1)
    (hxl : xl ∈ Ioo A a) (hxr : xr ∈ Ioo b B)
    (hyb : yb ∈ Ioo C c) (hyt : yt ∈ Ioo d D)
    (hvl : IsVerticalACLLineOn (closedRectangle A B C D) f df xl)
    (hvr : IsVerticalACLLineOn (closedRectangle A B C D) f df xr)
    (hhb : IsHorizontalACLLineOn (closedRectangle A B C D) f df yb)
    (hht : IsHorizontalACLLineOn (closedRectangle A B C D) f df yt)
    (hEl : (∫⁻ y in Ioo C D,
        ‖df (Complex.ofReal xl + Complex.ofReal y * Complex.I)‖ₑ ^ 2 ∂volume) ≤
      productRectangleEnergy df A a C D / ENNReal.ofReal (a - A))
    (hEr : (∫⁻ y in Ioo C D,
        ‖df (Complex.ofReal xr + Complex.ofReal y * Complex.I)‖ₑ ^ 2 ∂volume) ≤
      productRectangleEnergy df b B C D / ENNReal.ofReal (B - b))
    (hEb : (∫⁻ x in Ioo A B,
        ‖df (Complex.equivRealProdCLM.symm (x, yb))‖ₑ ^ 2 ∂volume) ≤
      productRectangleEnergy df A B C c / ENNReal.ofReal (c - C))
    (hEt : (∫⁻ x in Ioo A B,
        ‖df (Complex.equivRealProdCLM.symm (x, yt))‖ₑ ^ 2 ∂volume) ≤
      productRectangleEnergy df A B d D / ENNReal.ofReal (D - d)) :
    Metric.ediam (f '' closedRectangleBoundary xl xr yb yt) ≤
      rectangleFrameStripBound df A a b B C c d D xl xr yb yt := by
  exact
    (rectangleBoundary_ediam_le_lineEnergy_of_acl
      h0A hAa hab hbB hB1 h0C hCc hcd hdD hD1 hxl hxr hyb hyt
        hvl hvr hhb hht).trans
      (rectangleFrameLineEnergyBound_le_stripBound
        hxl hxr hyb hyt hEl hEr hEb hEt)

/--
%%handwave
name:
  Selected rectangle boundary controlled by four strip averages
statement:
  Let $0<A<a<b<B<1$ and $0<C<c<d<D<1$. Suppose the closed outer
  rectangle lies in a planar region where the continuous map $f$ is locally
  $W^{1,2}$ with weak differential $Df$. There are
  $x_\ell\in(A,a)$, $x_r\in(b,B)$, $y_b\in(C,c)$, and $y_t\in(d,D)$ such
  that, if $E_b,E_r,E_t,E_\ell$ are the integrals of
  $\lVert Df\rVert^2$ over the bottom, right, top, and left outer strips,
  respectively, then
  $$
  \begin{aligned}
  \operatorname{diam} f(\partial R_*)&\leq
  \sqrt{\frac{E_b}{c-C}}\sqrt{x_r-x_\ell}
  +\sqrt{\frac{E_r}{B-b}}\sqrt{y_t-y_b}\\
  &\quad+\sqrt{\frac{E_t}{D-d}}\sqrt{x_r-x_\ell}
  +\sqrt{\frac{E_\ell}{a-A}}\sqrt{y_t-y_b},
  \end{aligned}
  $$
  where $R_*=[x_\ell,x_r]\times[y_b,y_t]$.
proof:
  Take [an ACL frame whose four line energies are bounded by the corresponding strip averages](lean:JJMath.Quasiconformal.IsLocalW12On.exists_acl_rectangle_frame_le_average). Restrict those lines to the selected rectangle and apply [the boundary-diameter estimate from the four line energies](lean:JJMath.Quasiconformal.planar_rectangleBoundary_ediam_le_rpow_energy).
-/
theorem IsLocalW12On.exists_rectangle_frame_ediam_le_strip_averages
    {Ω : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    {A a b B C c d D : ℝ}
    (h0A : 0 < A) (hAa : A < a) (hab : a < b) (hbB : b < B) (hB1 : B < 1)
    (h0C : 0 < C) (hCc : C < c) (hcd : c < d) (hdD : d < D) (hD1 : D < 1)
    (hQΩ : closedRectangle A B C D ⊆ Ω)
    (hf_cont : ContinuousOn f Ω)
    (hW : IsLocalW12On Ω f df) :
    ∃ F : ProtectedRectangleFrame A a b B C c d D,
      Metric.ediam (f '' closedRectangleBoundary F.xl F.xr F.yb F.yt) ≤
        rectangleFrameStripBound df A a b B C c d D F.xl F.xr F.yb F.yt := by
  obtain ⟨xl, hxl, xr, hxr, yb, hyb, yt, hyt,
      hvl, hvr, hhb, hht, hEl, hEr, hEb, hEt⟩ :=
    hW.exists_acl_rectangle_frame_le_average hAa hab hbB hCc hcd hdD
      hQΩ hf_cont
  refine ⟨⟨xl, hxl, xr, hxr, yb, hyb, yt, hyt⟩, ?_⟩
  apply rectangleBoundary_ediam_le_strip_averages_of_acl
    h0A hAa hab hbB hB1 h0C hCc hcd hdD hD1 hxl hxr hyb hyt
    hvl hvr hhb hht
  · simpa [productRectangleEnergy] using hEl
  · simpa [productRectangleEnergy] using hEr
  · simpa [productRectangleEnergy] using hEb
  · simpa [productRectangleEnergy] using hEt

/--
%%handwave
name:
  Cancellation of square-root scale in a protected strip
statement:
  Let $E,r,\ell\in[0,\infty]$, with $0<r<\infty$ and $\ell\leq4r$. Then
  $$
  \sqrt{E/r}\,\sqrt{\ell}\leq2\sqrt E.
  $$
proof:
  Monotonicity reduces to $\ell=4r$. Distribute the square root over products and quotients, cancel the positive finite factor $\sqrt r$, and use $\sqrt4=2$.
-/
theorem ennreal_rpow_half_div_mul_le_two
    {E R L : ℝ≥0∞} (hR0 : R ≠ 0) (hRtop : R ≠ ⊤)
    (hL : L ≤ 4 * R) :
    (E / R) ^ ((2 : ℝ)⁻¹) * L ^ ((2 : ℝ)⁻¹) ≤
      2 * E ^ ((2 : ℝ)⁻¹) := by
  have hp : 0 ≤ (2 : ℝ)⁻¹ := by positivity
  calc
    (E / R) ^ ((2 : ℝ)⁻¹) * L ^ ((2 : ℝ)⁻¹) ≤
        (E / R) ^ ((2 : ℝ)⁻¹) * (4 * R) ^ ((2 : ℝ)⁻¹) := by
      gcongr
    _ = (E ^ ((2 : ℝ)⁻¹) / R ^ ((2 : ℝ)⁻¹)) *
          (4 ^ ((2 : ℝ)⁻¹) * R ^ ((2 : ℝ)⁻¹)) := by
      rw [ENNReal.div_rpow_of_nonneg E R hp,
        ENNReal.mul_rpow_of_nonneg 4 R hp]
    _ = (E ^ ((2 : ℝ)⁻¹) / R ^ ((2 : ℝ)⁻¹) *
          R ^ ((2 : ℝ)⁻¹)) * 4 ^ ((2 : ℝ)⁻¹) := by
      ac_rfl
    _ = E ^ ((2 : ℝ)⁻¹) * 4 ^ ((2 : ℝ)⁻¹) := by
      rw [ENNReal.div_mul_cancel]
      · exact (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hR0) hRtop).ne'
      · exact ENNReal.rpow_ne_top_of_nonneg hp hRtop
    _ = 2 * E ^ ((2 : ℝ)⁻¹) := by
      rw [show (4 : ℝ≥0∞) ^ ((2 : ℝ)⁻¹) = 2 by
        apply (ENNReal.toReal_eq_toReal_iff'
          (ENNReal.rpow_ne_top_of_nonneg (by positivity) (by norm_num))
          (by norm_num)).mp
        rw [← ENNReal.toReal_rpow]
        norm_num only [ENNReal.toReal_ofNat]]
      exact mul_comm _ _

set_option maxHeartbeats 800000 in
/--
%%handwave
name:
  Protected concentric square has a universally controlled image boundary
statement:
  Let $r>0$, let
  $$
  Q_2=[x-2r,x+2r]\times[y-2r,y+2r]\subset(0,1)^2,
  $$
  and suppose $Q_2$ lies in a planar region where the continuous map $f$ is
  locally $W^{1,2}$ with weak differential $Df$. There are
  $$
  x_\ell\in(x-2r,x-r),\quad x_r\in(x+r,x+2r),\quad
  y_b\in(y-2r,y-r),\quad y_t\in(y+r,y+2r)
  $$
  such that, for $R_*=[x_\ell,x_r]\times[y_b,y_t]$,
  $$
  \operatorname{diam}f(\partial R_*)
  \leq8\left(\int_{Q_2}\lVert Df\rVert^2\right)^{1/2}.
  $$
proof:
  Apply [the four-strip selected-frame estimate](lean:JJMath.Quasiconformal.IsLocalW12On.exists_rectangle_frame_ediam_le_strip_averages) with all four strip widths equal to $r$. Each strip energy is at most the energy of $Q_2$, while both selected side lengths are at most $4r$. Apply [square-root scale cancellation](lean:JJMath.Quasiconformal.ennreal_rpow_half_div_mul_le_two) to each of the four boundary terms and add them.
-/
theorem IsLocalW12On.exists_concentricSquare_frame_ediam_le
    {Ω : Set ℂ} {f : ℂ → ℂ} {df : ℂ → ℂ →L[ℝ] ℂ}
    {x y r : ℝ} (hr : 0 < r)
    (hx0 : 0 < x - 2 * r) (hx1 : x + 2 * r < 1)
    (hy0 : 0 < y - 2 * r) (hy1 : y + 2 * r < 1)
    (hQΩ : closedRectangle (x - 2 * r) (x + 2 * r)
      (y - 2 * r) (y + 2 * r) ⊆ Ω)
    (hf_cont : ContinuousOn f Ω)
    (hW : IsLocalW12On Ω f df) :
    ∃ xl ∈ Ioo (x - 2 * r) (x - r),
      ∃ xr ∈ Ioo (x + r) (x + 2 * r),
      ∃ yb ∈ Ioo (y - 2 * r) (y - r),
      ∃ yt ∈ Ioo (y + r) (y + 2 * r),
        Metric.ediam (f '' closedRectangleBoundary xl xr yb yt) ≤
          8 * (∫⁻ z in
            Ioo (x - 2 * r) (x + 2 * r) ×ˢ
              Ioo (y - 2 * r) (y + 2 * r),
            ‖df (Complex.equivRealProdCLM.symm z)‖ₑ ^ 2
              ∂(volume.prod volume)) ^ ((2 : ℝ)⁻¹) := by
  have hAa : x - 2 * r < x - r := by linarith
  have hab : x - r < x + r := by linarith
  have hbB : x + r < x + 2 * r := by linarith
  have hCc : y - 2 * r < y - r := by linarith
  have hcd : y - r < y + r := by linarith
  have hdD : y + r < y + 2 * r := by linarith
  obtain ⟨⟨xl, hxl, xr, hxr, yb, hyb, yt, hyt⟩, hdiam⟩ :=
    IsLocalW12On.exists_rectangle_frame_ediam_le_strip_averages
      hx0 hAa hab hbB hx1 hy0 hCc hcd hdD hy1 hQΩ hf_cont hW
  have hgap_bottom : (y - r) - (y - 2 * r) = r := by ring
  have hgap_right : (x + 2 * r) - (x + r) = r := by ring
  have hgap_top : (y + 2 * r) - (y + r) = r := by ring
  have hgap_left : (x - r) - (x - 2 * r) = r := by ring
  rw [rectangleFrameStripBound, productRectangleEnergy] at hdiam
  simp only [hgap_bottom, hgap_right, hgap_top, hgap_left] at hdiam
  let E : ℝ≥0∞ := ∫⁻ z in
    Ioo (x - 2 * r) (x + 2 * r) ×ˢ Ioo (y - 2 * r) (y + 2 * r),
      ‖df (Complex.equivRealProdCLM.symm z)‖ₑ ^ 2 ∂(volume.prod volume)
  have hbottom_set :
      Ioo (x - 2 * r) (x + 2 * r) ×ˢ Ioo (y - 2 * r) (y - r) ⊆
        Ioo (x - 2 * r) (x + 2 * r) ×ˢ Ioo (y - 2 * r) (y + 2 * r) := by
    rintro ⟨u, v⟩ ⟨hu, hv⟩
    exact ⟨hu, ⟨hv.1, hv.2.trans hcd |>.trans hdD⟩⟩
  have hright_set :
      Ioo (x + r) (x + 2 * r) ×ˢ Ioo (y - 2 * r) (y + 2 * r) ⊆
        Ioo (x - 2 * r) (x + 2 * r) ×ˢ Ioo (y - 2 * r) (y + 2 * r) := by
    rintro ⟨u, v⟩ ⟨hu, hv⟩
    exact ⟨⟨hAa.trans hab |>.trans hu.1, hu.2⟩, hv⟩
  have htop_set :
      Ioo (x - 2 * r) (x + 2 * r) ×ˢ Ioo (y + r) (y + 2 * r) ⊆
        Ioo (x - 2 * r) (x + 2 * r) ×ˢ Ioo (y - 2 * r) (y + 2 * r) := by
    rintro ⟨u, v⟩ ⟨hu, hv⟩
    exact ⟨hu, ⟨hCc.trans hcd |>.trans hv.1, hv.2⟩⟩
  have hleft_set :
      Ioo (x - 2 * r) (x - r) ×ˢ Ioo (y - 2 * r) (y + 2 * r) ⊆
        Ioo (x - 2 * r) (x + 2 * r) ×ˢ Ioo (y - 2 * r) (y + 2 * r) := by
    rintro ⟨u, v⟩ ⟨hu, hv⟩
    exact ⟨⟨hu.1, hu.2.trans hab |>.trans hbB⟩, hv⟩
  have hEbottom :
      (∫⁻ z in Ioo (x - 2 * r) (x + 2 * r) ×ˢ Ioo (y - 2 * r) (y - r),
        ‖df (Complex.equivRealProdCLM.symm z)‖ₑ ^ 2 ∂(volume.prod volume)) ≤ E := by
    exact lintegral_mono_set hbottom_set
  have hEright :
      (∫⁻ z in Ioo (x + r) (x + 2 * r) ×ˢ Ioo (y - 2 * r) (y + 2 * r),
        ‖df (Complex.equivRealProdCLM.symm z)‖ₑ ^ 2 ∂(volume.prod volume)) ≤ E := by
    exact lintegral_mono_set hright_set
  have hEtop :
      (∫⁻ z in Ioo (x - 2 * r) (x + 2 * r) ×ˢ Ioo (y + r) (y + 2 * r),
        ‖df (Complex.equivRealProdCLM.symm z)‖ₑ ^ 2 ∂(volume.prod volume)) ≤ E := by
    exact lintegral_mono_set htop_set
  have hEleft :
      (∫⁻ z in Ioo (x - 2 * r) (x - r) ×ˢ Ioo (y - 2 * r) (y + 2 * r),
        ‖df (Complex.equivRealProdCLM.symm z)‖ₑ ^ 2 ∂(volume.prod volume)) ≤ E := by
    exact lintegral_mono_set hleft_set
  have hR0 : ENNReal.ofReal r ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hr
  have hRtop : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
  have hLx : ENNReal.ofReal (xr - xl) ≤ 4 * ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_ofNat 4,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
    exact ENNReal.ofReal_le_ofReal (by linarith [hxl.1, hxr.2])
  have hLy : ENNReal.ofReal (yt - yb) ≤ 4 * ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_ofNat 4,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
    exact ENNReal.ofReal_le_ofReal (by linarith [hyb.1, hyt.2])
  have hterm_bottom :
      ((∫⁻ z in Ioo (x - 2 * r) (x + 2 * r) ×ˢ Ioo (y - 2 * r) (y - r),
          ‖df (Complex.equivRealProdCLM.symm z)‖ₑ ^ 2 ∂(volume.prod volume)) /
          ENNReal.ofReal r) ^ ((2 : ℝ)⁻¹) *
          ENNReal.ofReal (xr - xl) ^ ((2 : ℝ)⁻¹) ≤
        2 * E ^ ((2 : ℝ)⁻¹) := by
    calc
      _ ≤ (E / ENNReal.ofReal r) ^ ((2 : ℝ)⁻¹) *
          ENNReal.ofReal (xr - xl) ^ ((2 : ℝ)⁻¹) := by gcongr
      _ ≤ _ := ennreal_rpow_half_div_mul_le_two hR0 hRtop hLx
  have hterm_right :
      ((∫⁻ z in Ioo (x + r) (x + 2 * r) ×ˢ Ioo (y - 2 * r) (y + 2 * r),
          ‖df (Complex.equivRealProdCLM.symm z)‖ₑ ^ 2 ∂(volume.prod volume)) /
          ENNReal.ofReal r) ^ ((2 : ℝ)⁻¹) *
          ENNReal.ofReal (yt - yb) ^ ((2 : ℝ)⁻¹) ≤
        2 * E ^ ((2 : ℝ)⁻¹) := by
    calc
      _ ≤ (E / ENNReal.ofReal r) ^ ((2 : ℝ)⁻¹) *
          ENNReal.ofReal (yt - yb) ^ ((2 : ℝ)⁻¹) := by gcongr
      _ ≤ _ := ennreal_rpow_half_div_mul_le_two hR0 hRtop hLy
  have hterm_top :
      ((∫⁻ z in Ioo (x - 2 * r) (x + 2 * r) ×ˢ Ioo (y + r) (y + 2 * r),
          ‖df (Complex.equivRealProdCLM.symm z)‖ₑ ^ 2 ∂(volume.prod volume)) /
          ENNReal.ofReal r) ^ ((2 : ℝ)⁻¹) *
          ENNReal.ofReal (xr - xl) ^ ((2 : ℝ)⁻¹) ≤
        2 * E ^ ((2 : ℝ)⁻¹) := by
    calc
      _ ≤ (E / ENNReal.ofReal r) ^ ((2 : ℝ)⁻¹) *
          ENNReal.ofReal (xr - xl) ^ ((2 : ℝ)⁻¹) := by gcongr
      _ ≤ _ := ennreal_rpow_half_div_mul_le_two hR0 hRtop hLx
  have hterm_left :
      ((∫⁻ z in Ioo (x - 2 * r) (x - r) ×ˢ Ioo (y - 2 * r) (y + 2 * r),
          ‖df (Complex.equivRealProdCLM.symm z)‖ₑ ^ 2 ∂(volume.prod volume)) /
          ENNReal.ofReal r) ^ ((2 : ℝ)⁻¹) *
          ENNReal.ofReal (yt - yb) ^ ((2 : ℝ)⁻¹) ≤
        2 * E ^ ((2 : ℝ)⁻¹) := by
    calc
      _ ≤ (E / ENNReal.ofReal r) ^ ((2 : ℝ)⁻¹) *
          ENNReal.ofReal (yt - yb) ^ ((2 : ℝ)⁻¹) := by gcongr
      _ ≤ _ := ennreal_rpow_half_div_mul_le_two hR0 hRtop hLy
  refine ⟨xl, hxl, xr, hxr, yb, hyb, yt, hyt, hdiam.trans ?_⟩
  change _ ≤ 8 * E ^ ((2 : ℝ)⁻¹)
  calc
    _ ≤ 2 * E ^ ((2 : ℝ)⁻¹) + 2 * E ^ ((2 : ℝ)⁻¹) +
        2 * E ^ ((2 : ℝ)⁻¹) + 2 * E ^ ((2 : ℝ)⁻¹) :=
      add_le_add (add_le_add (add_le_add hterm_bottom hterm_right) hterm_top) hterm_left
    _ = 8 * E ^ ((2 : ℝ)⁻¹) := by ring

set_option maxHeartbeats 800000 in
/--
%%handwave
name:
  Image area of a protected square is controlled by outer-square energy
statement:
  Let $F:\Omega\to\Omega'$ be a homeomorphism with $\Omega'$ open. Suppose
  $r>0$, the outer square
  $$
  Q_2=[x-2r,x+2r]\times[y-2r,y+2r]
  $$
  lies in $\Omega\cap(0,1)^2$, and the ambient representative of $F$ is
  locally $W^{1,2}$ with weak differential $Df$. For the inner square
  $Q_1=[x-r,x+r]\times[y-r,y+r]$,
  $$
  |F(Q_1)|\leq64\int_{Q_2}\lVert Df\rVert^2.
  $$
  The displayed energy integral is written in real-imaginary product
  coordinates.
proof:
  Choose [a rectangle surrounding the inner square whose mapped boundary diameter is at most eight times the square root of the outer energy](lean:JJMath.Quasiconformal.IsLocalW12On.exists_concentricSquare_frame_ediam_le). Monotonicity puts the inner image inside this rectangle image. Apply [the domain-homeomorphism rectangle area estimate](lean:JJMath.Quasiconformal.complex_volume_ambientMap_image_closedRectangle_le_boundary_ediam_sq), square the boundary bound, and use $(8\sqrt E)^2=64E$.
-/
theorem IsLocalW12On.volume_ambientMap_image_concentricSquare_le
    {Ω Ω' : Set ℂ} (F : Ω ≃ₜ Ω') (hΩ' : IsOpen Ω')
    {df : ℂ → ℂ →L[ℝ] ℂ} {x y r : ℝ} (hr : 0 < r)
    (hx0 : 0 < x - 2 * r) (hx1 : x + 2 * r < 1)
    (hy0 : 0 < y - 2 * r) (hy1 : y + 2 * r < 1)
    (hQΩ : closedRectangle (x - 2 * r) (x + 2 * r)
      (y - 2 * r) (y + 2 * r) ⊆ Ω)
    (hW : IsLocalW12On Ω (ambientMap F) df) :
    volume (ambientMap F '' closedRectangle (x - r) (x + r) (y - r) (y + r)) ≤
      64 * (∫⁻ z in
        Ioo (x - 2 * r) (x + 2 * r) ×ˢ Ioo (y - 2 * r) (y + 2 * r),
        ‖df (Complex.equivRealProdCLM.symm z)‖ₑ ^ 2
          ∂(volume.prod volume)) := by
  obtain ⟨xl, hxl, xr, hxr, yb, hyb, yt, hyt, hdiam⟩ :=
    hW.exists_concentricSquare_frame_ediam_le hr hx0 hx1 hy0 hy1 hQΩ
      (continuousOn_ambientMap F)
  have hxlxr : xl < xr := hxl.2.trans (by linarith [hr, hxr.1])
  have hybyt : yb < yt := hyb.2.trans (by linarith [hr, hyt.1])
  have hinner_selected :
      closedRectangle (x - r) (x + r) (y - r) (y + r) ⊆
        closedRectangle xl xr yb yt := by
    intro z hz
    rw [closedRectangle, Complex.mem_reProdIm] at hz ⊢
    exact
      ⟨⟨hxl.2.le.trans hz.1.1, hz.1.2.trans hxr.1.le⟩,
        ⟨hyb.2.le.trans hz.2.1, hz.2.2.trans hyt.1.le⟩⟩
  have hselected_outer :
      closedRectangle xl xr yb yt ⊆
        closedRectangle (x - 2 * r) (x + 2 * r)
          (y - 2 * r) (y + 2 * r) := by
    intro z hz
    rw [closedRectangle, Complex.mem_reProdIm] at hz ⊢
    exact
      ⟨⟨hxl.1.le.trans hz.1.1, hz.1.2.trans hxr.2.le⟩,
        ⟨hyb.1.le.trans hz.2.1, hz.2.2.trans hyt.2.le⟩⟩
  have hselectedΩ : closedRectangle xl xr yb yt ⊆ Ω :=
    hselected_outer.trans hQΩ
  let E : ℝ≥0∞ := ∫⁻ z in
    Ioo (x - 2 * r) (x + 2 * r) ×ˢ Ioo (y - 2 * r) (y + 2 * r),
      ‖df (Complex.equivRealProdCLM.symm z)‖ₑ ^ 2 ∂(volume.prod volume)
  calc
    volume (ambientMap F '' closedRectangle (x - r) (x + r) (y - r) (y + r)) ≤
        volume (ambientMap F '' closedRectangle xl xr yb yt) :=
      measure_mono (image_mono hinner_selected)
    _ ≤ Metric.ediam (ambientMap F '' closedRectangleBoundary xl xr yb yt) ^ 2 :=
      complex_volume_ambientMap_image_closedRectangle_le_boundary_ediam_sq
        F hΩ' hxlxr hybyt hselectedΩ
    _ ≤ (8 * E ^ ((2 : ℝ)⁻¹)) ^ 2 :=
      pow_le_pow_left₀ (by simp) hdiam 2
    _ = 64 * E := by
      have hpow : (E ^ ((2 : ℝ)⁻¹)) ^ 2 = E := by
        simpa using ENNReal.rpow_inv_natCast_pow (n := 2) (by norm_num) E
      rw [mul_pow, hpow]
      norm_num

set_option maxHeartbeats 1200000 in
/--
%%handwave
name:
  Local square image-area estimate in arbitrary planar coordinates
statement:
  Let $F:\Omega\to\Omega'$ be a homeomorphism with $\Omega'$ open, and let
  the ambient representative of $F$ be locally $W^{1,2}$ with weak
  differential $Df$. If $0<r<1/4$ and
  $$
  Q_2=[x-2r,x+2r]\times[y-2r,y+2r]\subseteq\Omega,
  $$
  then, for $Q_1=[x-r,x+r]\times[y-r,y+r]$,
  $$
  |F(Q_1)|\leq64\int_{Q_2}\lVert Df\rVert^2.
  $$
  The energy integral is expressed in real-imaginary product coordinates.
proof:
  Translate the center $(x,y)$ to $(1/2,1/2)$. [Local Sobolev regularity is preserved by source translation](lean:JJMath.Quasiconformal.IsLocalW12On.comp_addRight), and [the translated subtype homeomorphism has the expected ambient representative](lean:JJMath.Quasiconformal.ambientMap_precompAddRightHomeomorph). Apply [the protected unit-square estimate](lean:JJMath.Quasiconformal.IsLocalW12On.volume_ambientMap_image_concentricSquare_le), then use translation invariance of product Lebesgue measure to identify its image set and energy integral with those of the original squares.
-/
theorem IsLocalW12On.volume_ambientMap_image_square_le
    {Ω Ω' : Set ℂ} (F : Ω ≃ₜ Ω') (hΩ' : IsOpen Ω')
    {df : ℂ → ℂ →L[ℝ] ℂ} {x y r : ℝ}
    (hr : 0 < r) (hr4 : r < 1 / 4)
    (hQΩ : closedRectangle (x - 2 * r) (x + 2 * r)
      (y - 2 * r) (y + 2 * r) ⊆ Ω)
    (hW : IsLocalW12On Ω (ambientMap F) df) :
    volume (ambientMap F '' closedRectangle (x - r) (x + r) (y - r) (y + r)) ≤
      64 * (∫⁻ z in
        Ioo (x - 2 * r) (x + 2 * r) ×ˢ Ioo (y - 2 * r) (y + 2 * r),
        ‖df (Complex.equivRealProdCLM.symm z)‖ₑ ^ 2
          ∂(volume.prod volume)) := by
  let sx : ℝ := x - 1 / 2
  let sy : ℝ := y - 1 / 2
  let shift : ℂ := Complex.ofReal sx + Complex.ofReal sy * Complex.I
  let U : Set ℂ := (fun z : ℂ => z + shift) ⁻¹' Ω
  let G : U ≃ₜ Ω' := precompAddRightHomeomorph F shift
  have hWshift0 := hW.comp_addRight shift
  have hWshift : IsLocalW12On U (ambientMap G) (fun z => df (z + shift)) := by
    simpa [U, G, ambientMap_precompAddRightHomeomorph] using hWshift0
  have hunit0 : 0 < (1 / 2 : ℝ) - 2 * r := by linarith
  have hunit1 : (1 / 2 : ℝ) + 2 * r < 1 := by linarith
  have hshift_re (z : ℂ) : (z + shift).re = z.re + sx := by
    simp [shift]
  have hshift_im (z : ℂ) : (z + shift).im = z.im + sy := by
    simp [shift]
  have hsub_shift_re (z : ℂ) : (z - shift).re = z.re - sx := by
    simp [shift]
  have hsub_shift_im (z : ℂ) : (z - shift).im = z.im - sy := by
    simp [shift]
  have hQunitU :
      closedRectangle ((1 / 2 : ℝ) - 2 * r) ((1 / 2 : ℝ) + 2 * r)
        ((1 / 2 : ℝ) - 2 * r) ((1 / 2 : ℝ) + 2 * r) ⊆ U := by
    intro z hz
    apply hQΩ
    rw [closedRectangle, Complex.mem_reProdIm] at hz ⊢
    rw [hshift_re, hshift_im]
    dsimp [sx, sy]
    constructor <;> constructor <;> linarith [hz.1.1, hz.1.2, hz.2.1, hz.2.2]
  have harea := hWshift.volume_ambientMap_image_concentricSquare_le
    G hΩ' hr hunit0 hunit1 hunit0 hunit1 hQunitU
  let Qunit : Set ℂ := closedRectangle
    ((1 / 2 : ℝ) - r) ((1 / 2 : ℝ) + r)
    ((1 / 2 : ℝ) - r) ((1 / 2 : ℝ) + r)
  let Q : Set ℂ := closedRectangle (x - r) (x + r) (y - r) (y + r)
  have hshift_mem_Q (z : ℂ) (hz : z ∈ Qunit) : z + shift ∈ Q := by
    change z ∈ closedRectangle ((1 / 2 : ℝ) - r) ((1 / 2 : ℝ) + r)
      ((1 / 2 : ℝ) - r) ((1 / 2 : ℝ) + r) at hz
    change z + shift ∈ closedRectangle (x - r) (x + r) (y - r) (y + r)
    rw [closedRectangle, Complex.mem_reProdIm] at hz ⊢
    rw [hshift_re, hshift_im]
    dsimp [sx, sy]
    constructor <;> constructor <;> linarith [hz.1.1, hz.1.2, hz.2.1, hz.2.2]
  have hsub_mem_Qunit (z : ℂ) (hz : z ∈ Q) : z - shift ∈ Qunit := by
    change z ∈ closedRectangle (x - r) (x + r) (y - r) (y + r) at hz
    change z - shift ∈ closedRectangle ((1 / 2 : ℝ) - r) ((1 / 2 : ℝ) + r)
      ((1 / 2 : ℝ) - r) ((1 / 2 : ℝ) + r)
    rw [closedRectangle, Complex.mem_reProdIm] at hz ⊢
    rw [hsub_shift_re, hsub_shift_im]
    dsimp [sx, sy]
    constructor <;> constructor <;> linarith [hz.1.1, hz.1.2, hz.2.1, hz.2.2]
  have himage : ambientMap G '' Qunit = ambientMap F '' Q := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨z + shift, hshift_mem_Q z hz, ?_⟩
      exact ambientMap_precompAddRightHomeomorph F shift z
    · rintro ⟨z, hz, rfl⟩
      refine ⟨z - shift, hsub_mem_Qunit z hz, ?_⟩
      rw [ambientMap_precompAddRightHomeomorph]
      simp
  let shiftPair : ℝ × ℝ := (sx, sy)
  let T : ℝ × ℝ → ℝ × ℝ := fun p => p + shiftPair
  let QunitProd : Set (ℝ × ℝ) :=
    Ioo ((1 / 2 : ℝ) - 2 * r) ((1 / 2 : ℝ) + 2 * r) ×ˢ
      Ioo ((1 / 2 : ℝ) - 2 * r) ((1 / 2 : ℝ) + 2 * r)
  let Qprod : Set (ℝ × ℝ) :=
    Ioo (x - 2 * r) (x + 2 * r) ×ˢ Ioo (y - 2 * r) (y + 2 * r)
  have hT_image : T '' QunitProd = Qprod := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      change q + shiftPair ∈ Qprod
      change q.1 + sx ∈ Ioo (x - 2 * r) (x + 2 * r) ∧
        q.2 + sy ∈ Ioo (y - 2 * r) (y + 2 * r)
      change q.1 ∈ Ioo ((1 / 2 : ℝ) - 2 * r) ((1 / 2 : ℝ) + 2 * r) ∧
        q.2 ∈ Ioo ((1 / 2 : ℝ) - 2 * r) ((1 / 2 : ℝ) + 2 * r) at hq
      dsimp [sx, sy] at hq ⊢
      constructor <;> constructor <;> linarith [hq.1.1, hq.1.2, hq.2.1, hq.2.2]
    · intro hp
      let q : ℝ × ℝ := (p.1 - sx, p.2 - sy)
      refine ⟨q, ?_, ?_⟩
      · change q.1 ∈ Ioo ((1 / 2 : ℝ) - 2 * r) ((1 / 2 : ℝ) + 2 * r) ∧
          q.2 ∈ Ioo ((1 / 2 : ℝ) - 2 * r) ((1 / 2 : ℝ) + 2 * r)
        change p.1 ∈ Ioo (x - 2 * r) (x + 2 * r) ∧
          p.2 ∈ Ioo (y - 2 * r) (y + 2 * r) at hp
        dsimp [q, sx, sy] at hp ⊢
        constructor <;> constructor <;> linarith [hp.1.1, hp.1.2, hp.2.1, hp.2.2]
      · ext <;> simp [q, T, shiftPair]
  have hT_mp : MeasurePreserving T
      ((volume : Measure ℝ).prod volume) ((volume : Measure ℝ).prod volume) := by
    have hxmp := JJMath.Uniformization.measurePreserving_add_right_volume
      (H := ℝ) sx
    have hymp := JJMath.Uniformization.measurePreserving_add_right_volume
      (H := ℝ) sy
    simpa [T, shiftPair, Prod.map] using hxmp.prod hymp
  have hT_emb : MeasurableEmbedding T := by
    simpa [T] using
      (JJMath.Uniformization.measurableEmbedding_add_right shiftPair)
  have he_shift (p : ℝ × ℝ) :
      Complex.equivRealProdCLM.symm p + shift =
        Complex.equivRealProdCLM.symm (T p) := by
    apply Complex.ext <;>
      simp [Complex.equivRealProdCLM_symm_apply, T, shiftPair, shift, sx, sy]
  have henergy :
      (∫⁻ z in QunitProd,
        ‖df (Complex.equivRealProdCLM.symm z + shift)‖ₑ ^ 2
          ∂(volume.prod volume)) =
        ∫⁻ z in Qprod,
          ‖df (Complex.equivRealProdCLM.symm z)‖ₑ ^ 2
            ∂(volume.prod volume) := by
    calc
      _ = ∫⁻ z in QunitProd,
          ‖df (Complex.equivRealProdCLM.symm (T z))‖ₑ ^ 2
            ∂(volume.prod volume) := by
        apply setLIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo)
        intro z hz
        change ‖df (Complex.equivRealProdCLM.symm z + shift)‖ₑ ^ 2 =
          ‖df (Complex.equivRealProdCLM.symm (T z))‖ₑ ^ 2
        rw [he_shift]
      _ = ∫⁻ z in T '' QunitProd,
          ‖df (Complex.equivRealProdCLM.symm z)‖ₑ ^ 2
            ∂(volume.prod volume) :=
        hT_mp.setLIntegral_comp_emb hT_emb
          (fun z => ‖df (Complex.equivRealProdCLM.symm z)‖ₑ ^ 2) QunitProd
      _ = _ := by rw [hT_image]
  rw [show closedRectangle ((1 / 2 : ℝ) - r) ((1 / 2 : ℝ) + r)
      ((1 / 2 : ℝ) - r) ((1 / 2 : ℝ) + r) = Qunit by rfl,
    himage] at harea
  change volume (ambientMap F '' Q) ≤ _
  rw [← henergy]
  simpa [QunitProd, Qprod] using harea

/--
%%handwave
name:
  Weak-differential energy on a doubled square
statement:
  For a field $Df$, center $x+iy$, and half-side $r$, define
  $$
    E^{(2)}_{Df}(x,y,r)
      =\int_{x-2r}^{x+2r}\int_{y-2r}^{y+2r}
        \lVert Df(s+it)\rVert_{\mathrm{op}}^2\,dt\,ds.
  $$
-/
def productDoubledSquareEnergy
    (df : ℂ → ℂ →L[ℝ] ℂ) (x y r : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in Ioo (x - 2 * r) (x + 2 * r) ×ˢ Ioo (y - 2 * r) (y + 2 * r),
    ‖df (Complex.equivRealProdCLM.symm z)‖ₑ ^ 2 ∂(volume.prod volume)

/--
%%handwave
name:
  Product-coordinate weak-energy measure
statement:
  For a field $Df$, define the measure on $\mathbb R^2$ by
  $$
    d\nu_{Df}(x,y)=\lVert Df(x+iy)\rVert_{\mathrm{op}}^2\,dx\,dy.
  $$
-/
def productEnergyMeasure (df : ℂ → ℂ →L[ℝ] ℂ) : Measure (ℝ × ℝ) :=
  (volume.prod volume).withDensity
    (fun z => ‖df (Complex.equivRealProdCLM.symm z)‖ₑ ^ 2)

/--
%%handwave
name:
  Product-coordinate energy measure on an open rectangle
statement:
  For a weak differential $Df$ and real intervals $(a,b)$ and $(c,d)$, the
  energy measure of their product is
  $$
    \nu_{Df}((a,b)\times(c,d))
      =\int_{(a,b)\times(c,d)}\lVert Df(x+iy)\rVert^2\,dx\,dy.
  $$
proof:
  This is the defining evaluation formula for a measure obtained by weighting product Lebesgue measure by the squared operator norm.
-/
theorem productEnergyMeasure_apply_prod_Ioo
    (df : ℂ → ℂ →L[ℝ] ℂ) (a b c d : ℝ) :
    productEnergyMeasure df (Ioo a b ×ˢ Ioo c d) =
      ∫⁻ z in Ioo a b ×ˢ Ioo c d,
        ‖df (Complex.equivRealProdCLM.symm z)‖ₑ ^ 2 ∂(volume.prod volume) := by
  rw [productEnergyMeasure, withDensity_apply]
  exact measurableSet_Ioo.prod measurableSet_Ioo

/--
%%handwave
name:
  Finite product-coordinate energy on an $L^2$ set
statement:
  Let $C\subset\mathbb C$ be measurable. If a weak differential $Df$ belongs
  to $L^2(C)$, then its product-coordinate energy measure on the real-imaginary
  image of $C$ is finite.
proof:
  The real-imaginary linear equivalence preserves Lebesgue measure. Change variables through this equivalence and use that membership in $L^2(C)$ makes $\int_C\lVert Df\rVert^2$ finite.
-/
theorem productEnergyMeasure_image_equivRealProd_ne_top_of_memLp
    {df : ℂ → ℂ →L[ℝ] ℂ} {C : Set ℂ} (hC : MeasurableSet C)
    (hdf : MemLp df 2 ((volume : Measure ℂ).restrict C)) :
    productEnergyMeasure df (Complex.equivRealProdCLM '' C) ≠ ⊤ := by
  have hfinite :
      (∫⁻ z in C, ‖df z‖ₑ ^ (2 : ℕ) ∂volume) < ⊤ := by
    simpa [show (2 : ℝ≥0∞).toReal = 2 by norm_num, ENNReal.rpow_two] using
      lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
        (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) hdf.eLpNorm_lt_top
  have hchange := Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_emb
    Complex.equivRealProdCLM.toHomeomorph.measurableEmbedding
      (fun p : ℝ × ℝ => ‖df (Complex.equivRealProdCLM.symm p)‖ₑ ^ 2) C
  have henergy :
      (∫⁻ p in Complex.equivRealProdCLM '' C,
        ‖df (Complex.equivRealProdCLM.symm p)‖ₑ ^ 2 ∂(volume.prod volume)) =
        ∫⁻ z in C, ‖df z‖ₑ ^ 2 ∂volume := by
    simpa using hchange.symm
  rw [productEnergyMeasure, withDensity_apply]
  · rw [henergy]
    exact hfinite.ne
  · exact Complex.equivRealProdCLM.toHomeomorph.measurableEmbedding.measurableSet_image' hC

/--
%%handwave
name:
  Small open energy neighborhood of a compact null set
statement:
  Let $P\subset\mathbb R^2$ be compact and Lebesgue-null, and suppose
  $P\subset\operatorname{int}C$ while the weak-differential energy
  $\nu_{Df}(C)$ is finite. For every $\varepsilon>0$ there is an open set
  $G$ such that
  $$
    P\subset G\subset\operatorname{int}C,
    \qquad \nu_{Df}(G)\leq\varepsilon.
  $$
proof:
  Restrict the energy measure to $C$. It is finite and absolutely continuous with respect to product Lebesgue measure, so it vanishes on $P$ and is outer regular. Approximate $P$ by an open set of restricted energy at most $\varepsilon$, then intersect with $\operatorname{int}C$.
-/
theorem exists_open_productEnergyMeasure_le_of_compact_null
    {df : ℂ → ℂ →L[ℝ] ℂ} {P C : Set (ℝ × ℝ)}
    (hP : IsCompact P) (hPC : P ⊆ interior C)
    (hPzero : (volume.prod volume) P = 0)
    (hCfinite : productEnergyMeasure df C ≠ ⊤)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ G : Set (ℝ × ℝ), IsOpen G ∧ P ⊆ G ∧ G ⊆ interior C ∧
      productEnergyMeasure df G ≤ ε := by
  let μ : Measure (ℝ × ℝ) := productEnergyMeasure df
  let ν : Measure (ℝ × ℝ) := μ.restrict C
  haveI : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 hCfinite
  have hμP : μ P = 0 := by
    exact withDensity_absolutelyContinuous (volume.prod volume)
      (fun z => ‖df (Complex.equivRealProdCLM.symm z)‖ₑ ^ 2) hPzero
  have hPC' : P ⊆ C := hPC.trans interior_subset
  have hνP : ν P = 0 := by
    change μ.restrict C P = 0
    rw [Measure.restrict_apply hP.measurableSet, inter_eq_left.2 hPC', hμP]
  obtain ⟨U, hPU, hUopen, hνU⟩ := P.exists_isOpen_le_add ν hε.ne'
  let G : Set (ℝ × ℝ) := U ∩ interior C
  have hGopen : IsOpen G := hUopen.inter isOpen_interior
  have hPG : P ⊆ G := fun p hp => ⟨hPU hp, hPC hp⟩
  have hGC : G ⊆ C := inter_subset_right.trans interior_subset
  have hμGνG : μ G = ν G := by
    change μ G = μ.restrict C G
    rw [Measure.restrict_apply hGopen.measurableSet, inter_eq_left.2 hGC]
  refine ⟨G, hGopen, hPG, inter_subset_right, ?_⟩
  have hνU' : ν U ≤ ε := by simpa [hνP] using hνU
  change μ G ≤ ε
  rw [hμGνG]
  exact (measure_mono inter_subset_left).trans hνU'

/--
%%handwave
name:
  Doubled-square energy as energy measure
statement:
  The squared weak-differential energy on the doubled square centered at
  $(x,y)$ with inner half-side $r$ equals the product-coordinate energy
  measure of that doubled square.
proof:
  Apply [the energy-measure evaluation formula for product intervals](lean:JJMath.Quasiconformal.productEnergyMeasure_apply_prod_Ioo) to the two coordinate intervals $(x-2r,x+2r)$ and $(y-2r,y+2r)$.
-/
theorem productDoubledSquareEnergy_eq_measure
    (df : ℂ → ℂ →L[ℝ] ℂ) (x y r : ℝ) :
    productDoubledSquareEnergy df x y r =
      productEnergyMeasure df
        (Ioo (x - 2 * r) (x + 2 * r) ×ˢ Ioo (y - 2 * r) (y + 2 * r)) := by
  rw [productDoubledSquareEnergy, productEnergyMeasure_apply_prod_Ioo]

/--
%%handwave
name:
  Energy sum for disjoint doubled squares
statement:
  Let $S$ be a finite family of squares whose open doubled squares $2Q_i$
  are pairwise disjoint and all lie in a set $G$. Then
  $$
    \sum_{i\in S}\int_{2Q_i}\lVert Df\rVert^2
      \leq\nu_{Df}(G),
  $$
  where $\nu_{Df}$ is the product-coordinate energy measure.
proof:
  Rewrite each square energy as [the energy measure of its open doubled square](lean:JJMath.Quasiconformal.productDoubledSquareEnergy_eq_measure). Finite additivity identifies the sum with the energy measure of the disjoint union, and monotonicity uses containment in $G$.
-/
theorem sum_productDoubledSquareEnergy_le_of_pairwiseDisjoint
    {ι : Type*} [DecidableEq ι] (df : ℂ → ℂ →L[ℝ] ℂ)
    (s : Finset ι) (x y r : ι → ℝ) (G : Set (ℝ × ℝ))
    (hdisj : PairwiseDisjoint (↑s : Set ι) fun i =>
      Ioo (x i - 2 * r i) (x i + 2 * r i) ×ˢ
        Ioo (y i - 2 * r i) (y i + 2 * r i))
    (hsub : (⋃ i ∈ s,
      Ioo (x i - 2 * r i) (x i + 2 * r i) ×ˢ
        Ioo (y i - 2 * r i) (y i + 2 * r i)) ⊆ G) :
    (∑ i ∈ s, productDoubledSquareEnergy df (x i) (y i) (r i)) ≤
      productEnergyMeasure df G := by
  rw [show (∑ i ∈ s, productDoubledSquareEnergy df (x i) (y i) (r i)) =
      ∑ i ∈ s, productEnergyMeasure df
        (Ioo (x i - 2 * r i) (x i + 2 * r i) ×ˢ
          Ioo (y i - 2 * r i) (y i + 2 * r i)) by
    apply Finset.sum_congr rfl
    intro i hi
    exact productDoubledSquareEnergy_eq_measure df (x i) (y i) (r i)]
  rw [← measure_biUnion_finset hdisj]
  · exact measure_mono hsub
  · intro i hi
    exact measurableSet_Ioo.prod measurableSet_Ioo

/--
%%handwave
name:
  Energy sum for a finitely colored square family
statement:
  Let $S$ be a finite family of squares whose open doubled squares lie in a
  set $G$. If the squares are colored by a finite set $C$ so that doubled
  squares of the same color are pairwise disjoint, then
  $$
    \sum_{i\in S}\int_{2Q_i}\lVert Df\rVert^2
      \leq |C|\,\nu_{Df}(G).
  $$
proof:
  Partition the sum into color classes, apply [finite additivity for each disjoint class](lean:JJMath.Quasiconformal.sum_productDoubledSquareEnergy_le_of_pairwiseDisjoint), and sum the $|C|$ identical upper bounds.
-/
theorem sum_productDoubledSquareEnergy_le_card_mul_of_coloring
    {ι κ : Type*} [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (df : ℂ → ℂ →L[ℝ] ℂ) (s : Finset ι) (x y r : ι → ℝ)
    (G : Set (ℝ × ℝ)) (color : ι → κ)
    (hdisj : ∀ k : κ,
      PairwiseDisjoint (↑(s.filter fun i => color i = k) : Set ι) fun i =>
        Ioo (x i - 2 * r i) (x i + 2 * r i) ×ˢ
          Ioo (y i - 2 * r i) (y i + 2 * r i))
    (hsub : (⋃ i ∈ s,
      Ioo (x i - 2 * r i) (x i + 2 * r i) ×ˢ
        Ioo (y i - 2 * r i) (y i + 2 * r i)) ⊆ G) :
    (∑ i ∈ s, productDoubledSquareEnergy df (x i) (y i) (r i)) ≤
      (Fintype.card κ : ℝ≥0∞) * productEnergyMeasure df G := by
  classical
  have hclass (k : κ) :
      (∑ i ∈ s.filter fun i => color i = k,
        productDoubledSquareEnergy df (x i) (y i) (r i)) ≤
        productEnergyMeasure df G := by
    apply sum_productDoubledSquareEnergy_le_of_pairwiseDisjoint
      df (s.filter fun i => color i = k) x y r G (hdisj k)
    intro p hp
    apply hsub
    rcases Set.mem_iUnion.mp hp with ⟨i, hp⟩
    rcases Set.mem_iUnion.mp hp with ⟨hi, hp⟩
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨(Finset.mem_filter.mp hi).1, hp⟩⟩
  calc
    (∑ i ∈ s, productDoubledSquareEnergy df (x i) (y i) (r i)) =
        ∑ k : κ, ∑ i ∈ s.filter fun i => color i = k,
          productDoubledSquareEnergy df (x i) (y i) (r i) := by
      simpa using (Finset.sum_fiberwise_eq_sum_filter s Finset.univ color
        (fun i => productDoubledSquareEnergy df (x i) (y i) (r i))).symm
    _ ≤ ∑ _k : κ, productEnergyMeasure df G :=
      Finset.sum_le_sum fun k hk => hclass k
    _ = (Fintype.card κ : ℝ≥0∞) * productEnergyMeasure df G := by
      simp [nsmul_eq_mul]

/--
%%handwave
name:
  Center of a two-sided integer-grid interval
statement:
  For a real grid with origin $a$, mesh $\delta$, and index $i\in\mathbb Z$,
  define
  $$
    c_i=a+\left(i+\frac12\right)\delta.
  $$
-/
def integerGridCenter (a δ : ℝ) (i : ℤ) : ℝ :=
  a + ((i : ℝ) + 1 / 2) * δ

/--
%%handwave
name:
  Open doubled square in an integer grid
statement:
  For origins $a,b$, mesh $\delta$, and $(i,j)\in\mathbb Z^2$, define the
  open square
  $$
    (c_i-\delta,c_i+\delta)\times(c_j-\delta,c_j+\delta),
  $$
  where $c_i=a+(i+\tfrac12)\delta$ and
  $c_j=b+(j+\tfrac12)\delta$.
-/
def integerGridOpenSquare (a b δ : ℝ) (ij : ℤ × ℤ) : Set (ℝ × ℝ) :=
  Ioo (integerGridCenter a δ ij.1 - δ) (integerGridCenter a δ ij.1 + δ) ×ˢ
    Ioo (integerGridCenter b δ ij.2 - δ) (integerGridCenter b δ ij.2 + δ)

/--
%%handwave
name:
  Open integer-grid intervals cover the real line
statement:
  If $\delta>0$, the open intervals of radius $\delta$ centered at
  $a+(i+1/2)\delta$, for $i\in\mathbb Z$, cover $\mathbb R$.
proof:
  For $t\in\mathbb R$, take $i=\lfloor(t-a)/\delta\rfloor$. The defining floor inequalities put $t$ in the smaller half-open grid cell of radius $\delta/2$, hence in the stated open interval.
-/
theorem exists_mem_integerGrid_openInterval
    (a : ℝ) {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    ∃ i : ℤ, t ∈ Ioo (integerGridCenter a δ i - δ)
      (integerGridCenter a δ i + δ) := by
  let q : ℝ := (t - a) / δ
  let i : ℤ := ⌊q⌋
  have hlow : (i : ℝ) ≤ q := by
    exact Int.floor_le q
  have hhigh : q < (i : ℝ) + 1 := by
    exact Int.lt_floor_add_one q
  have hq : t = a + q * δ := by
    dsimp [q]
    field_simp [hδ.ne']
    ring
  refine ⟨i, ?_⟩
  dsimp [integerGridCenter]
  constructor <;> nlinarith [mul_le_mul_of_nonneg_right hlow hδ.le,
    mul_lt_mul_of_pos_right hhigh hδ]

/--
%%handwave
name:
  Open integer-grid squares cover the plane
statement:
  If $\delta>0$, the products of the open integer-grid intervals of radius
  $\delta$ cover $\mathbb R^2$.
proof:
  Choose a covering integer-grid interval independently in each coordinate using [the one-dimensional covering statement](lean:JJMath.Quasiconformal.exists_mem_integerGrid_openInterval), then take the pair of indices.
-/
theorem iUnion_integerGridOpenSquare_eq_univ
    (a b : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    (⋃ ij : ℤ × ℤ, integerGridOpenSquare a b δ ij) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro p
  obtain ⟨i, hi⟩ := exists_mem_integerGrid_openInterval a hδ p.1
  obtain ⟨j, hj⟩ := exists_mem_integerGrid_openInterval b hδ p.2
  exact Set.mem_iUnion.mpr ⟨(i, j), ⟨hi, hj⟩⟩

/--
%%handwave
name:
  Compact set has a finite integer-grid square cover
statement:
  Let $P\subset\mathbb R^2$ be compact and let $\delta>0$. There is a finite
  set of integer grid indices whose open squares of radius $\delta$ cover
  $P$.
proof:
  The open integer-grid squares cover the plane. Apply compactness to extract a finite subcover.
-/
theorem IsCompact.exists_finset_subset_iUnion_integerGridOpenSquare
    {P : Set (ℝ × ℝ)} (hP : IsCompact P) (a b : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ s : Finset (ℤ × ℤ),
      P ⊆ ⋃ ij ∈ s, integerGridOpenSquare a b δ ij := by
  have hopen : ∀ ij : ℤ × ℤ, IsOpen (integerGridOpenSquare a b δ ij) := by
    intro ij
    exact isOpen_Ioo.prod isOpen_Ioo
  have hcover : P ⊆ ⋃ ij : ℤ × ℤ, integerGridOpenSquare a b δ ij := by
    rw [iUnion_integerGridOpenSquare_eq_univ a b hδ]
    exact Set.subset_univ P
  exact hP.elim_finite_subcover (integerGridOpenSquare a b δ) hopen hcover

/--
%%handwave
name:
  Disjoint radius-two intervals in one residue class
statement:
  In an integer grid of positive mesh $\delta$, suppose $i\ne j$ are
  congruent modulo four. Then the open intervals of radius $2\delta$ centered
  at the $i$th and $j$th grid centers are disjoint.
proof:
  Distinct congruent integers differ by at least four. Their centers are therefore separated by at least $4\delta$, the sum of the two radii; openness excludes a common endpoint.
-/
theorem disjoint_integerGrid_radius_two_of_zmod_four_eq
    {a δ : ℝ} {i j : ℤ} (hδ : 0 < δ) (hij : i ≠ j)
    (hmod : (i : ZMod 4) = (j : ZMod 4)) :
    Disjoint
      (Ioo (integerGridCenter a δ i - 2 * δ) (integerGridCenter a δ i + 2 * δ))
      (Ioo (integerGridCenter a δ j - 2 * δ) (integerGridCenter a δ j + 2 * δ)) := by
  have hcong : i ≡ j [ZMOD 4] :=
    (ZMod.intCast_eq_intCast_iff i j 4).mp hmod
  obtain ⟨t, ht⟩ := Int.modEq_iff_add_fac.mp hcong
  have hsep : i + 4 ≤ j ∨ j + 4 ≤ i := by
    omega
  rw [Set.disjoint_left]
  intro z hzi hzj
  rcases hsep with hij_le | hji_le
  · have hij_real : (i : ℝ) + 4 ≤ (j : ℝ) := by exact_mod_cast hij_le
    have hmul := mul_le_mul_of_nonneg_right hij_real hδ.le
    have hend : integerGridCenter a δ i + 2 * δ ≤
        integerGridCenter a δ j - 2 * δ := by
      dsimp [integerGridCenter]
      nlinarith [hmul]
    exact (not_lt_of_ge hend) (hzj.1.trans hzi.2)
  · have hji_real : (j : ℝ) + 4 ≤ (i : ℝ) := by exact_mod_cast hji_le
    have hmul := mul_le_mul_of_nonneg_right hji_real hδ.le
    have hend : integerGridCenter a δ j + 2 * δ ≤
        integerGridCenter a δ i - 2 * δ := by
      dsimp [integerGridCenter]
      nlinarith [hmul]
    exact (not_lt_of_ge hend) (hzi.1.trans hzj.2)

/--
%%handwave
name:
  Sixteen-color disjointness of doubled integer-grid squares
statement:
  Any finite subfamily of integer-grid squares of half-side $\delta$ can be
  colored with sixteen colors so that their open doubled squares are pairwise
  disjoint within each color.
proof:
  Color $(i,j)$ by its two residue classes modulo four. Distinct indices of one color differ by at least four in some coordinate, so [the radius-$2\delta$ intervals in that coordinate are disjoint](lean:JJMath.Quasiconformal.disjoint_integerGrid_radius_two_of_zmod_four_eq).
-/
theorem exists_sixteenColor_pairwiseDisjoint_integerGrid_doubledSquares
    {a b δ : ℝ} (hδ : 0 < δ) (s : Finset (ℤ × ℤ)) :
    ∃ color : (ℤ × ℤ) → Fin 16,
      ∀ k : Fin 16,
        PairwiseDisjoint (↑(s.filter fun ij => color ij = k) : Set (ℤ × ℤ))
          fun ij =>
            Ioo (integerGridCenter a δ ij.1 - 2 * δ)
                (integerGridCenter a δ ij.1 + 2 * δ) ×ˢ
              Ioo (integerGridCenter b δ ij.2 - 2 * δ)
                (integerGridCenter b δ ij.2 + 2 * δ) := by
  classical
  let e : ZMod 4 × ZMod 4 ≃ Fin 16 := by
    simpa using Fintype.equivFin (ZMod 4 × ZMod 4)
  let residue : (ℤ × ℤ) → ZMod 4 × ZMod 4 := fun ij => (ij.1, ij.2)
  let color : (ℤ × ℤ) → Fin 16 := fun ij => e (residue ij)
  refine ⟨color, ?_⟩
  intro k p hp q hq hpq
  have hcolor_p : color p = k := (Finset.mem_filter.mp hp).2
  have hcolor_q : color q = k := (Finset.mem_filter.mp hq).2
  have hresidue : residue p = residue q := by
    apply e.injective
    exact hcolor_p.trans hcolor_q.symm
  have hxmod : (p.1 : ZMod 4) = (q.1 : ZMod 4) :=
    congrArg Prod.fst hresidue
  have hymod : (p.2 : ZMod 4) = (q.2 : ZMod 4) :=
    congrArg Prod.snd hresidue
  have hcoord : p.1 ≠ q.1 ∨ p.2 ≠ q.2 := by
    contrapose! hpq
    exact Prod.ext hpq.1 hpq.2
  rcases hcoord with hxne | hyne
  · exact (disjoint_integerGrid_radius_two_of_zmod_four_eq hδ hxne hxmod).set_prod_left
      (Ioo (integerGridCenter b δ p.2 - 2 * δ)
        (integerGridCenter b δ p.2 + 2 * δ))
      (Ioo (integerGridCenter b δ q.2 - 2 * δ)
        (integerGridCenter b δ q.2 + 2 * δ))
  · exact (disjoint_integerGrid_radius_two_of_zmod_four_eq hδ hyne hymod).set_prod_right
      (Ioo (integerGridCenter a δ p.1 - 2 * δ)
        (integerGridCenter a δ p.1 + 2 * δ))
      (Ioo (integerGridCenter a δ q.1 - 2 * δ)
        (integerGridCenter a δ q.1 + 2 * δ))

/--
%%handwave
name:
  Total doubled-square energy of an integer-grid subfamily
statement:
  Let $S$ be a finite family of integer-grid squares of half-side
  $\delta>0$. If all their open doubled squares lie in $G$, then
  $$
    \sum_{Q\in S}\int_{2Q}\lVert Df\rVert^2
      \leq16\nu_{Df}(G).
  $$
proof:
  Apply [the sixteen-color integer-grid decomposition](lean:JJMath.Quasiconformal.exists_sixteenColor_pairwiseDisjoint_integerGrid_doubledSquares) and then [the finite-color energy estimate](lean:JJMath.Quasiconformal.sum_productDoubledSquareEnergy_le_card_mul_of_coloring).
-/
theorem sum_integerGrid_productDoubledSquareEnergy_le_sixteen_mul
    (df : ℂ → ℂ →L[ℝ] ℂ) (s : Finset (ℤ × ℤ))
    {a b δ : ℝ} (hδ : 0 < δ) (G : Set (ℝ × ℝ))
    (hsub : (⋃ ij ∈ s,
      Ioo (integerGridCenter a δ ij.1 - 2 * δ)
          (integerGridCenter a δ ij.1 + 2 * δ) ×ˢ
        Ioo (integerGridCenter b δ ij.2 - 2 * δ)
          (integerGridCenter b δ ij.2 + 2 * δ)) ⊆ G) :
    (∑ ij ∈ s, productDoubledSquareEnergy df
      (integerGridCenter a δ ij.1) (integerGridCenter b δ ij.2) δ) ≤
      16 * productEnergyMeasure df G := by
  classical
  obtain ⟨color, hcolor⟩ :=
    exists_sixteenColor_pairwiseDisjoint_integerGrid_doubledSquares
      (a := a) (b := b) (δ := δ) hδ s
  simpa using sum_productDoubledSquareEnergy_le_card_mul_of_coloring
    df s (fun ij => integerGridCenter a δ ij.1)
      (fun ij => integerGridCenter b δ ij.2) (fun _ => δ) G color hcolor hsub

/--
%%handwave
name:
  Fine finite grid cover inside an open neighborhood
statement:
  Let $P\subset\mathbb R^2$ be compact, let $G$ be an open neighborhood of
  $P$, and let $\rho>0$. There are $0<\delta<\rho$ and finitely many integer
  grid squares of half-side $\delta$ whose closed squares cover $P$ and whose
  open doubled squares all lie in $G$.
proof:
  Choose a positive metric thickening of $P$ contained in $G$, then take $\delta$ small compared with both its radius and $\rho$. Extract a finite subcover from the open integer-grid squares and discard cells that do not meet $P$. Every point in a retained doubled cell is within $3\delta$ of a point of $P$, hence belongs to the chosen thickening.
-/
theorem IsCompact.exists_fine_integerGrid_squareCover_doubled_subset
    {P G : Set (ℝ × ℝ)} (hP : IsCompact P) (hG : IsOpen G) (hPG : P ⊆ G)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ δ : ℝ, 0 < δ ∧ δ < ρ ∧ ∃ s : Finset (ℤ × ℤ),
      P ⊆ ⋃ ij ∈ s,
        Icc (integerGridCenter 0 δ ij.1 - δ) (integerGridCenter 0 δ ij.1 + δ) ×ˢ
          Icc (integerGridCenter 0 δ ij.2 - δ) (integerGridCenter 0 δ ij.2 + δ) ∧
      (⋃ ij ∈ s,
        Icc (integerGridCenter 0 δ ij.1 - 2 * δ)
            (integerGridCenter 0 δ ij.1 + 2 * δ) ×ˢ
          Icc (integerGridCenter 0 δ ij.2 - 2 * δ)
            (integerGridCenter 0 δ ij.2 + 2 * δ)) ⊆ G := by
  classical
  obtain ⟨η, hη, hthick⟩ := hP.exists_thickening_subset_open hG hPG
  let δ : ℝ := min (ρ / 2) (η / 4)
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hδρ : δ < ρ := by
    exact (min_le_left _ _).trans_lt (by linarith)
  have h3δη : 3 * δ < η := by
    have := min_le_right (ρ / 2) (η / 4)
    dsimp [δ] at this ⊢
    linarith
  obtain ⟨t, ht⟩ :=
    IsCompact.exists_finset_subset_iUnion_integerGridOpenSquare hP 0 0 hδ
  let s : Finset (ℤ × ℤ) :=
    t.filter fun ij => (integerGridOpenSquare 0 0 δ ij ∩ P).Nonempty
  refine ⟨δ, hδ, hδρ, s, ?_, ?_⟩
  · intro p hpP
    rcases Set.mem_iUnion.mp (ht hpP) with ⟨ij, hpUnion⟩
    rcases Set.mem_iUnion.mp hpUnion with ⟨hijt, hpgrid⟩
    have hijs : ij ∈ s := by
      rw [Finset.mem_filter]
      exact ⟨hijt, ⟨p, hpgrid, hpP⟩⟩
    apply Set.mem_iUnion.mpr
    refine ⟨ij, Set.mem_iUnion.mpr ⟨hijs, ?_⟩⟩
    exact ⟨⟨hpgrid.1.1.le, hpgrid.1.2.le⟩, ⟨hpgrid.2.1.le, hpgrid.2.2.le⟩⟩
  · intro z hz
    rcases Set.mem_iUnion.mp hz with ⟨ij, hz⟩
    rcases Set.mem_iUnion.mp hz with ⟨hijs, hzouter⟩
    have hmeet := (Finset.mem_filter.mp hijs).2
    obtain ⟨q, hqinner, hqP⟩ := hmeet
    apply hthick
    rw [Metric.mem_thickening_iff]
    refine ⟨q, hqP, ?_⟩
    rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
    constructor
    · rw [abs_lt]
      constructor <;> linarith [hzouter.1.1, hzouter.1.2, hqinner.1.1, hqinner.1.2]
    · rw [abs_lt]
      constructor <;> linarith [hzouter.2.1, hzouter.2.2, hqinner.2.1, hqinner.2.2]

/--
%%handwave
name:
  Image area under a finite square cover
statement:
  Let $F:\Omega\to\Omega'$ be a homeomorphism with open target, whose
  ambient representative is locally $W^{1,2}$ with weak differential $Df$.
  Suppose a set $K\subset\Omega$ is covered by finitely many closed squares
  $Q_i$ of half-side lengths $0<r_i<1/4$, and every doubled square $2Q_i$
  lies in $\Omega$. Then
  $$
    |F(K)|\leq64\sum_i\int_{2Q_i}\lVert Df\rVert^2.
  $$
proof:
  The image of $K$ is contained in the union of the square images. Subadditivity of volume bounds the measure of that finite union by the sum of the image measures, and [the local arbitrary-center square estimate](lean:JJMath.Quasiconformal.IsLocalW12On.volume_ambientMap_image_square_le) bounds each summand by sixty-four times its doubled-square energy.
-/
theorem IsLocalW12On.volume_ambientMap_image_of_subset_iUnion_squares_le
    {Ω Ω' : Set ℂ} (F : Ω ≃ₜ Ω') (hΩ' : IsOpen Ω')
    {df : ℂ → ℂ →L[ℝ] ℂ} (hW : IsLocalW12On Ω (ambientMap F) df)
    {ι : Type*} [Fintype ι] (x y r : ι → ℝ) (K : Set ℂ)
    (hr : ∀ i, 0 < r i) (hr4 : ∀ i, r i < 1 / 4)
    (hQΩ : ∀ i, closedRectangle (x i - 2 * r i) (x i + 2 * r i)
      (y i - 2 * r i) (y i + 2 * r i) ⊆ Ω)
    (hcover : K ⊆ ⋃ i,
      closedRectangle (x i - r i) (x i + r i) (y i - r i) (y i + r i)) :
    volume (ambientMap F '' K) ≤
      ∑ i, 64 * productDoubledSquareEnergy df (x i) (y i) (r i) := by
  have himage : ambientMap F '' K ⊆ ⋃ i,
      ambientMap F '' closedRectangle
        (x i - r i) (x i + r i) (y i - r i) (y i + r i) := by
    rintro w ⟨z, hz, rfl⟩
    rcases Set.mem_iUnion.mp (hcover hz) with ⟨i, hi⟩
    exact Set.mem_iUnion.mpr ⟨i, ⟨z, hi, rfl⟩⟩
  refine (measure_mono himage).trans ((measure_iUnion_le _).trans ?_)
  rw [tsum_fintype]
  apply Finset.sum_le_sum
  intro i hi
  simpa [productDoubledSquareEnergy] using
    hW.volume_ambientMap_image_square_le F hΩ' (hr i) (hr4 i) (hQΩ i)

set_option maxHeartbeats 1200000 in
/--
%%handwave
name:
  Compact-null Lusin property for planar local $W^{1,2}$ homeomorphisms
statement:
  Let $F:\Omega\to\Omega'$ be a homeomorphism between open planar domains,
  and suppose its ambient representative is locally $W^{1,2}$ with weak
  differential $Df$. If $K\subset\Omega$ is compact and $|K|=0$, then
  $|F(K)|=0$.
proof:
  Choose a compact thickening $C$ of $K$ inside $\Omega$. Its product-coordinate energy is finite by local $L^2$ regularity. For each $n$, [outer regularity gives an open neighborhood $G_n$ of the product-coordinate image of $K$ with energy at most $2^{-n}/16$](lean:JJMath.Quasiconformal.exists_open_productEnergyMeasure_le_of_compact_null). Choose [a fine finite integer-grid cover whose closed doubled squares stay in $G_n$](lean:JJMath.Quasiconformal.IsCompact.exists_fine_integerGrid_squareCover_doubled_subset). The [sixteen-color overlap estimate](lean:JJMath.Quasiconformal.sum_integerGrid_productDoubledSquareEnergy_le_sixteen_mul) bounds the total doubled-square energy by $2^{-n}$, and [the finite square image estimate](lean:JJMath.Quasiconformal.IsLocalW12On.volume_ambientMap_image_of_subset_iUnion_squares_le) gives $|F(K)|\leq64\cdot2^{-n}$. Let $n\to\infty$.
-/
theorem IsLocalW12On.volume_ambientMap_image_eq_zero_of_isCompact_null
    {Ω Ω' : Set ℂ} (F : Ω ≃ₜ Ω') (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω')
    {df : ℂ → ℂ →L[ℝ] ℂ} (hW : IsLocalW12On Ω (ambientMap F) df)
    {K : Set ℂ} (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hKzero : volume K = 0) :
    volume (ambientMap F '' K) = 0 := by
  let e : ℂ ≃L[ℝ] ℝ × ℝ := Complex.equivRealProdCLM
  obtain ⟨η, hη, hCΩ⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  let C₀ : Set ℂ := Metric.cthickening η K
  let P : Set (ℝ × ℝ) := e '' K
  let C : Set (ℝ × ℝ) := e '' C₀
  have hC₀compact : IsCompact C₀ := by
    exact hK.cthickening
  have hKC₀int : K ⊆ interior C₀ := by
    exact (Metric.self_subset_thickening hη K).trans
      (Metric.thickening_subset_interior_cthickening η K)
  have hPcompact : IsCompact P := hK.image e.continuous
  have hCcompact : IsCompact C := hC₀compact.image e.continuous
  have hPC : P ⊆ interior C := by
    change e '' K ⊆ interior (e '' C₀)
    have he : e '' interior C₀ = interior (e '' C₀) := by
      simpa only [ContinuousLinearEquiv.coe_toHomeomorph] using
        e.toHomeomorph.image_interior C₀
    rw [← he]
    exact image_mono hKC₀int
  have hPzero : (volume.prod volume) P = 0 := by
    have himage_preimage :
        Complex.equivRealProdCLM '' K =
          Complex.measurableEquivRealProd.symm ⁻¹' K := by
      ext p
      constructor
      · rintro ⟨z, hz, rfl⟩
        simpa using hz
      · intro hp
        exact ⟨Complex.measurableEquivRealProd.symm p, hp, by ext <;> rfl⟩
    change (volume.prod volume) (Complex.equivRealProdCLM '' K) = 0
    rw [himage_preimage]
    rw [← Measure.volume_eq_prod ℝ ℝ]
    rw [Complex.volume_preserving_equiv_real_prod.symm.measure_preimage]
    · exact hKzero
    · exact hK.measurableSet.nullMeasurableSet
  have hdfC : MemLp df 2 ((volume : Measure ℂ).restrict C₀) :=
    (hW.2.2 C₀ hC₀compact hCΩ).2
  have hCfinite : productEnergyMeasure df C ≠ ⊤ := by
    exact productEnergyMeasure_image_equivRealProd_ne_top_of_memLp
      hC₀compact.measurableSet hdfC
  apply ENNReal.eq_zero_of_le_mul_pow (ε := (64 : NNReal))
    (by norm_num : (1 / 2 : ℝ≥0∞) < 1)
  intro n
  let ε : ℝ≥0∞ := (1 / 2 : ℝ≥0∞) ^ n
  have hε : 0 < ε := by
    exact pos_iff_ne_zero.mpr (pow_ne_zero n (by norm_num))
  have hε16 : 0 < ε / 16 := ENNReal.div_pos hε.ne' (by norm_num)
  obtain ⟨G, hGopen, hPG, hGC, hGenergy⟩ :=
    exists_open_productEnergyMeasure_le_of_compact_null
      hPcompact hPC hPzero hCfinite hε16
  obtain ⟨δ, hδ, hδ4, s, hPcover, hdoubleG⟩ :=
    IsCompact.exists_fine_integerGrid_squareCover_doubled_subset
      hPcompact hGopen hPG (ρ := (1 / 4 : ℝ)) (by norm_num)
  have hdoubleOpenG : (⋃ ij ∈ s,
      Ioo (integerGridCenter 0 δ ij.1 - 2 * δ)
          (integerGridCenter 0 δ ij.1 + 2 * δ) ×ˢ
        Ioo (integerGridCenter 0 δ ij.2 - 2 * δ)
          (integerGridCenter 0 δ ij.2 + 2 * δ)) ⊆ G := by
    intro p hp
    apply hdoubleG
    rcases Set.mem_iUnion.mp hp with ⟨ij, hp⟩
    rcases Set.mem_iUnion.mp hp with ⟨hijs, hp⟩
    exact Set.mem_iUnion.mpr ⟨ij, Set.mem_iUnion.mpr ⟨hijs,
      ⟨⟨hp.1.1.le, hp.1.2.le⟩, ⟨hp.2.1.le, hp.2.2.le⟩⟩⟩⟩
  have hsum0 := sum_integerGrid_productDoubledSquareEnergy_le_sixteen_mul
    df s (a := 0) (b := 0) hδ G hdoubleOpenG
  have hsum : (∑ ij ∈ s, productDoubledSquareEnergy df
      (integerGridCenter 0 δ ij.1) (integerGridCenter 0 δ ij.2) δ) ≤ ε := by
    refine hsum0.trans ?_
    calc
      16 * productEnergyMeasure df G ≤ 16 * (ε / 16) := by
        simpa [mul_comm] using mul_le_mul_left hGenergy 16
      _ = ε := by
        rw [mul_comm, ENNReal.div_mul_cancel]
        · norm_num
        · norm_num
  let x : ↥s → ℝ := fun i => integerGridCenter 0 δ i.1.1
  let y : ↥s → ℝ := fun i => integerGridCenter 0 δ i.1.2
  let r : ↥s → ℝ := fun _ => δ
  have hr : ∀ i : ↥s, 0 < r i := fun _ => hδ
  have hr4 : ∀ i : ↥s, r i < 1 / 4 := fun _ => hδ4
  have hQΩ : ∀ i : ↥s,
      closedRectangle (x i - 2 * r i) (x i + 2 * r i)
        (y i - 2 * r i) (y i + 2 * r i) ⊆ Ω := by
    intro i z hz
    apply hCΩ
    have hpG : e z ∈ G := by
      apply hdoubleG
      apply Set.mem_iUnion.mpr
      refine ⟨i.1, Set.mem_iUnion.mpr ⟨i.2, ?_⟩⟩
      rw [closedRectangle, Complex.mem_reProdIm] at hz
      constructor
      · simpa [e, x, r] using hz.1
      · simpa [e, y, r] using hz.2
    have hpC : e z ∈ C := interior_subset (hGC hpG)
    rcases hpC with ⟨w, hwC, hwz⟩
    exact (e.injective hwz).symm ▸ hwC
  have hcover : K ⊆ ⋃ i : ↥s,
      closedRectangle (x i - r i) (x i + r i) (y i - r i) (y i + r i) := by
    intro z hzK
    have hpP : e z ∈ P := ⟨z, hzK, rfl⟩
    rcases Set.mem_iUnion.mp (hPcover hpP) with ⟨ij, hp⟩
    rcases Set.mem_iUnion.mp hp with ⟨hijs, hp⟩
    apply Set.mem_iUnion.mpr
    refine ⟨⟨ij, hijs⟩, ?_⟩
    rw [closedRectangle, Complex.mem_reProdIm]
    constructor
    · simpa [e, x, r] using hp.1
    · simpa [e, y, r] using hp.2
  have harea :=
    IsLocalW12On.volume_ambientMap_image_of_subset_iUnion_squares_le
      F hΩ' hW x y r K hr hr4 hQΩ hcover
  calc
    volume (ambientMap F '' K) ≤
        ∑ i : ↥s, 64 * productDoubledSquareEnergy df (x i) (y i) (r i) := harea
    _ = 64 * ∑ i : ↥s, productDoubledSquareEnergy df (x i) (y i) (r i) := by
      rw [Finset.mul_sum]
    _ ≤ 64 * ε := by
      have hsum' : (∑ i : ↥s, productDoubledSquareEnergy df (x i) (y i) (r i)) ≤ ε := by
        calc
          (∑ i : ↥s, productDoubledSquareEnergy df (x i) (y i) (r i)) =
              ∑ ij ∈ s, productDoubledSquareEnergy df
                (integerGridCenter 0 δ ij.1) (integerGridCenter 0 δ ij.2) δ := by
            rw [Finset.univ_eq_attach]
            simpa only [x, y, r] using
              (Finset.sum_attach s fun ij => productDoubledSquareEnergy df
                (integerGridCenter 0 δ ij.1) (integerGridCenter 0 δ ij.2) δ)
          _ ≤ ε := hsum
      simpa [mul_comm] using mul_le_mul_left hsum' 64
    _ = ((64 : NNReal) : ℝ≥0∞) * (1 / 2 : ℝ≥0∞) ^ n := by
      rfl

end

end Quasiconformal

end JJMath
