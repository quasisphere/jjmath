import JJMath.Quasiconformal.CauchyLpSobolev
import JJMath.Quasiconformal.BeltramiLpSolver
import JJMath.Topology.PlanarDegree
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-!
# Principal solutions of compactly supported Beltrami equations

This file combines the near-two `Lᵖ` Beltrami solver with the rough Cauchy
potential.  It constructs the continuous normalized Sobolev solution and its
weak Beltrami equation.  Proving that this map is open, discrete, and hence a
global homeomorphism is the next topological layer.
-/

namespace JJMath

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace Quasiconformal

noncomputable section

set_option maxHeartbeats 800000
/--
%%handwave
name:
  Principal map associated with a Beltrami density
statement:
  For a compactly supported density $h$, its principal map is
  $$
    f_h(z)=z+\mathcal C h(z).
  $$
-/
def principalBeltramiMap (h : ℂ → ℂ) (z : ℂ) : ℂ :=
  z + cauchyTransformLp h z

/--
%%handwave
name:
  Candidate weak differential of a principal map
statement:
  If $S$ is the $\partial_z$ derivative of $\mathcal C h$, the candidate
  weak differential of $f_h(z)=z+\mathcal C h(z)$ is
  $$
    Df_h(z)(v)=(1+S(z))v+h(z)\overline v.
  $$
-/
def principalBeltramiWeakDifferential
    (h S : ℂ → ℂ) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  realLinearMapOfWirtinger (1 + S z) (h z)

/--
%%handwave
name:
  Holomorphic derivative of a principal map
statement:
  The $\partial_z$ component of
  $v\mapsto(1+S(z))v+h(z)\overline v$ is $1+S(z)$.
proof:
  This is the defining Wirtinger decomposition of the real-linear map.
-/
@[simp]
theorem weakDZField_principalBeltramiWeakDifferential
    (h S : ℂ → ℂ) (z : ℂ) :
    weakDZField (principalBeltramiWeakDifferential h S) z = 1 + S z := by
  simp [weakDZField, principalBeltramiWeakDifferential]

/--
%%handwave
name:
  Antiholomorphic derivative of a principal map
statement:
  The $\partial_{\bar z}$ component of
  $v\mapsto(1+S(z))v+h(z)\overline v$ is $h(z)$.
proof:
  This is the defining Wirtinger decomposition of the real-linear map.
-/
@[simp]
theorem weakDBarField_principalBeltramiWeakDifferential
    (h S : ℂ → ℂ) (z : ℂ) :
    weakDBarField (principalBeltramiWeakDifferential h S) z = h z := by
  simp [weakDBarField, principalBeltramiWeakDifferential]

/--
%%handwave
name:
  Local Sobolev regularity of a principal map
statement:
  Let $p>2$, let $q$ be its Hölder conjugate, and suppose
  $h\in L^p(\mathbb C)$ vanishes almost everywhere outside a disk. Then
  $f_h(z)=z+\mathcal C_ph(z)$ belongs to
  $W^{1,2}_{\mathrm{loc}}(\mathbb C)$ and has weak differential
  $$
    Df_h(z)(v)=(1+\mathcal S_2h(z))v+h(z)\overline v.
  $$
proof:
  Add the affine identity map, whose differential has Wirtinger components
  $(1,0)$, to the rough Cauchy potential and its weak differential with
  components $(\mathcal S_2h,h)$.
-/
theorem principalBeltramiMap_isLocalW12On
    {p q : ℝ} (hpq : p.HolderConjugate q) (hp2 : 2 < p)
    {h : ℂ → ℂ} (hhp : MemLp h (ENNReal.ofReal p) (volume : Measure ℂ))
    {R : ℝ}
    (hzero : ∀ᵐ z ∂(volume : Measure ℂ), R ≤ ‖z‖ → h z = 0) :
    IsLocalW12On Set.univ (principalBeltramiMap h)
      (principalBeltramiWeakDifferential h
        (beurlingTransformL2
          ((memLp_two_of_memLp_of_ae_zero_outside_closedBall
            hp2.le hhp hzero).toLp h) : ℂ → ℂ)) := by
  let hh2 : MemLp h 2 (volume : Measure ℂ) :=
    memLp_two_of_memLp_of_ae_zero_outside_closedBall hp2.le hhp hzero
  have hid := isLocalW12On_affineMap isOpen_univ 1 0 0
  have hC := cauchyTransformLp_isLocalW12On hpq hp2 hhp hzero
  have hadd := isLocalW12On_add hid hC
  convert hadd using 1
  · funext z
    simp [principalBeltramiMap, affineMap]
  · funext z
    ext v
    simp [principalBeltramiWeakDifferential,
      cauchyTransformLpWeakDifferential, realLinearMapOfWirtinger_apply]
    ring

set_option maxHeartbeats 200000

/--
%%handwave
name:
  Density equation gives the weak Beltrami equation
statement:
  Suppose measurable fields $h,S,\mu:\mathbb C\to\mathbb C$ satisfy
  $$
    h(z)=\mu(z)(1+S(z))
  $$
  almost everywhere. Then the field
  $Df(z)(v)=(1+S(z))v+h(z)\overline v$ satisfies
  $\partial_{\bar z}f=\mu\,\partial_zf$ almost everywhere.
proof:
  The two Wirtinger components of the displayed real-linear map are exactly
  $h$ and $1+S$.
-/
theorem principalBeltramiWeakDifferential_weakBeltramiEquation
    (μ h S : ℂ → ℂ)
    (heq : ∀ᵐ z ∂(volume : Measure ℂ), h z = μ z * (1 + S z)) :
    WeakBeltramiEquationOn Set.univ μ
      (principalBeltramiWeakDifferential h S) := by
  simpa [WeakBeltramiEquationOn] using heq

/--
%%handwave
name:
  Continuity and normalization at infinity of a principal map
statement:
  Let $p>2$, let $q$ be its Hölder conjugate, and suppose
  $h\in L^p(\mathbb C)$ vanishes almost everywhere outside a disk. Then
  $f_h(z)=z+\mathcal C_ph(z)$ is continuous and
  $$
    f_h(z)-z\longrightarrow0
    \quad\text{as }z\to\infty.
  $$
proof:
  The rough Cauchy potential is continuous, and its compact-support
  far-field estimate tends to zero at infinity.
-/
theorem continuous_principalBeltramiMap_and_tendsto_sub_cocompact
    {p q : ℝ} (hpq : p.HolderConjugate q) (hp2 : 2 < p)
    {h : ℂ → ℂ} (hhp : MemLp h (ENNReal.ofReal p) (volume : Measure ℂ))
    {R : ℝ}
    (hzero : ∀ᵐ z ∂(volume : Measure ℂ), R ≤ ‖z‖ → h z = 0) :
    Continuous (principalBeltramiMap h) ∧
      Tendsto (fun z ↦ principalBeltramiMap h z - z)
        (cocompact ℂ) (𝓝 0) := by
  constructor
  · exact continuous_id.add (continuous_cauchyTransformLp hpq hp2 hhp hzero)
  · simpa [principalBeltramiMap] using
      tendsto_cauchyTransformLp_cocompact_zero (by linarith) hhp hzero

/--
%%handwave
name:
  Properness of a continuous asymptotically identity map
statement:
  Suppose $f:\mathbb C\to\mathbb C$ is continuous and
  $$
    f(z)-z\longrightarrow 0
    \quad\text{as }z\to\infty.
  $$
  Then $f$ is proper: the inverse image of every compact set is compact.
proof:
  Outside a sufficiently large disk, $|f(z)-z|<1$.  The reverse triangle
  inequality then gives $|f(z)|\geq |z|-1$, so $f(z)\to\infty$ as
  $z\to\infty$.  A continuous map between the complex planes is proper
  exactly when it tends to infinity along the cocompact filter.
-/
theorem isProperMap_of_continuous_of_tendsto_sub_id_cocompact_zero
    {f : ℂ → ℂ} (hf : Continuous f)
    (hInf : Tendsto (fun z ↦ f z - z) (cocompact ℂ) (𝓝 0)) :
    IsProperMap f := by
  rw [isProperMap_iff_tendsto_cocompact]
  refine ⟨hf, tendsto_cocompact_of_tendsto_dist_comp_atTop (0 : ℂ) ?_⟩
  have herrNorm :
      Tendsto (fun z ↦ ‖f z - z‖) (cocompact ℂ) (𝓝 0) := by
    simpa only [norm_zero, Function.comp_apply] using hInf.norm
  rw [tendsto_atTop]
  intro b
  filter_upwards
      [(tendsto_norm_cocompact_atTop (E := ℂ)).eventually_ge_atTop (b + 1),
        herrNorm.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with z hz he
  simp only [dist_zero_right]
  have htriangle : ‖z‖ ≤ ‖f z‖ + ‖f z - z‖ := by
    calc
      ‖z‖ = ‖f z - (f z - z)‖ := by ring_nf
      _ ≤ ‖f z‖ + ‖f z - z‖ := norm_sub_le _ _
  linarith

/--
%%handwave
name:
  Proper open self-maps of the plane are onto
statement:
  Every proper open map $f:\mathbb C\to\mathbb C$ is surjective.
proof:
  Properness makes the range closed, while openness makes it open. The range
  is nonempty, and the complex plane is connected, so the range is the whole
  plane.
-/
theorem surjective_of_isProperMap_of_isOpenMap
    {f : ℂ → ℂ} (hproper : IsProperMap f) (hopen : IsOpenMap f) :
    Function.Surjective f := by
  have hrangeOpen : IsOpen (Set.range f) := hopen.isOpen_range
  have hrangeClosed : IsClosed (Set.range f) := hproper.isClosed_range
  have hrangeNonempty : (Set.range f).Nonempty := ⟨f 0, ⟨0, rfl⟩⟩
  have hrange : Set.range f = Set.univ :=
    IsClopen.eq_univ ⟨hrangeClosed, hrangeOpen⟩ hrangeNonempty
  rw [← Set.range_eq_univ]
  exact hrange

/--
%%handwave
name:
  Proper maps with a discrete fiber have a finite fiber
statement:
  Let $f:\mathbb C\to\mathbb C$ be proper. If the fiber $f^{-1}(w)$ is a
  discrete subset of the plane, then it is finite.
proof:
  A fiber of a proper map is compact. A compact discrete subset of a
  Hausdorff space is finite.
-/
theorem finite_fiber_of_isProperMap_of_isDiscrete_fiber
    {f : ℂ → ℂ} (hproper : IsProperMap f) (w : ℂ)
    (hdiscrete : IsDiscrete {z : ℂ | f z = w}) :
    {z : ℂ | f z = w}.Finite := by
  have hcompact : IsCompact {z : ℂ | f z = w} := by
    simpa [Set.preimage, Set.mem_singleton_iff] using
      hproper.isCompact_preimage (K := {w}) isCompact_singleton
  exact hcompact.finite hdiscrete

/--
%%handwave
name:
  Global inversion from degree-one positive fibers
statement:
  Let $f:\mathbb C\to\mathbb C$ be continuous, proper, and open, with every
  fiber discrete. Suppose every local index is positive and the sum of local
  indices over every fiber equals $1$. Then $f$ is bijective.
proof:
  Properness and discreteness make every fiber finite, while properness and
  openness make the map surjective. Positive integer local indices summing to
  one force each fiber to contain exactly one point, hence injectivity.
-/
theorem bijective_of_isProperMap_of_isOpenMap_of_planarFiberIndexSum_eq_one
    {f : ℂ → ℂ} (hf : Continuous f) (hproper : IsProperMap f)
    (hopen : IsOpenMap f)
    (hdiscrete : ∀ w, IsDiscrete {z : ℂ | f z = w})
    (hpos : ∀ w (z : {z : ℂ | f z = w}),
      0 < planarLocalIndex f hf z w z.2 (hdiscrete w))
    (hsum : ∀ w,
      planarFiberIndexSum f hf w (hdiscrete w)
        (finite_fiber_of_isProperMap_of_isDiscrete_fiber
          hproper w (hdiscrete w)) = 1) :
    Function.Bijective f := by
  have hunique (w : ℂ) : ∃! z : ℂ, f z = w :=
    existsUnique_preimage_of_planarFiberIndexSum_eq_one_of_pos
      f hf w (hdiscrete w)
        (finite_fiber_of_isProperMap_of_isDiscrete_fiber
          hproper w (hdiscrete w))
        (hpos w) (hsum w)
  constructor
  · intro x y hxy
    obtain ⟨z, hz, huniq⟩ := hunique (f x)
    have hx : x = z := huniq x rfl
    have hy : y = z := huniq y hxy.symm
    exact hx.trans hy.symm
  · exact surjective_of_isProperMap_of_isOpenMap hproper hopen

/--
%%handwave
name:
  Degree-one circle enclosing a fiber of an asymptotically identity map
statement:
  Suppose $f:\mathbb C\to\mathbb C$ is continuous and
  $f(z)-z\to0$ as $z\to\infty$. For every $w\in\mathbb C$, there is a radius
  $r>0$ such that the whole fiber $f^{-1}(w)$ lies in $|z|<r$, the image of
  $|z|=r$ avoids $w$, and its planar circle index about $w$ equals $1$.
proof:
  Choose $r>|w|+2$ beyond a region where $|f(z)-z|<1$. A point with
  $f(z)=w$ and $|z|\geq r$ would satisfy both
  $|w-z|<1$ and $|w-z|\geq |z|-|w|\geq2$, a contradiction. The same estimate
  makes the image circle a close perturbation of the positive circle, whose
  index around the enclosed target is one.
-/
theorem exists_large_planarCircleIndex_eq_one_and_fiber_subset_ball
    {f : ℂ → ℂ} (hf : Continuous f)
    (hInf : Tendsto (fun z ↦ f z - z) (cocompact ℂ) (𝓝 0)) (w : ℂ) :
    ∃ r : ℝ, ∃ hr : 0 < r,
      {z : ℂ | f z = w} ⊆ Metric.ball 0 r ∧
      ∃ hne : ∀ t, imageCircleLoop f hf 0 r t ≠ w,
        planarCircleIndex f hf 0 w r hr hne = 1 := by
  have herrNorm :
      Tendsto (fun z ↦ ‖f z - z‖) (cocompact ℂ) (𝓝 0) := by
    simpa only [norm_zero, Function.comp_apply] using hInf.norm
  have herr : ∀ᶠ z in cocompact ℂ, ‖f z - z‖ < 1 :=
    herrNorm.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  rw [← Metric.cobounded_eq_cocompact] at herr
  rcases Filter.hasBasis_cobounded_norm.mem_iff.mp herr with
    ⟨a, _ha, ha⟩
  let r : ℝ := max a (‖w‖ + 2)
  have hra : a ≤ r := le_max_left _ _
  have hrw : ‖w‖ + 2 ≤ r := le_max_right _ _
  have hr : 0 < r := by
    have : 0 ≤ ‖w‖ := norm_nonneg w
    linarith
  have hnormCircle (t : unitInterval) : ‖complexCircleLoop 0 r t‖ = r := by
    simpa [Complex.dist_eq] using dist_circlePoint_center (0 : ℂ) hr t
  have herror (t : unitInterval) :
      ‖f (complexCircleLoop 0 r t) - complexCircleLoop 0 r t‖ < 1 := by
    apply ha
    change a ≤ ‖complexCircleLoop 0 r t‖
    rw [hnormCircle]
    exact hra
  have hfiber : {z : ℂ | f z = w} ⊆ Metric.ball 0 r := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right]
    by_contra hzr
    have hge : r ≤ ‖z‖ := le_of_not_gt hzr
    have herrz : ‖f z - z‖ < 1 := ha (hra.trans hge)
    rw [hz] at herrz
    have htri : ‖z‖ ≤ ‖w‖ + ‖w - z‖ := by
      calc
        ‖z‖ = ‖w - (w - z)‖ := by ring_nf
        _ ≤ ‖w‖ + ‖w - z‖ := norm_sub_le _ _
    linarith
  have hw : dist w (0 : ℂ) < r := by
    rw [Complex.dist_eq, sub_zero]
    linarith
  have hclose (t : unitInterval) :
      ‖f (complexCircleLoop 0 r t) - complexCircleLoop 0 r t‖ <
        r - dist w (0 : ℂ) := by
    have he := herror t
    rw [Complex.dist_eq, sub_zero]
    linarith
  obtain ⟨hne, hhom⟩ :=
    exists_imageCircleLoop_avoids_and_homotopic_positive_of_close
      f hf 0 w hr hw hclose
  refine ⟨r, hr, hfiber, hne, ?_⟩
  exact puncturedLoopWindingNumber_eq_one_of_homotopic_positive hhom

/--
%%handwave
name:
  Total fiber index of an asymptotically identity map
statement:
  Let $f:\mathbb C\to\mathbb C$ be continuous and satisfy
  $f(z)-z\to0$ at infinity. If $f^{-1}(w)$ is finite and discrete, then
  $$
    \sum_{z\in f^{-1}(w)} i(f,z;w)=1.
  $$
proof:
  Choose a large circle enclosing the whole fiber and having boundary index
  one. The planar boundary-additivity theorem identifies this boundary index
  with the sum of the local indices.
-/
theorem planarFiberIndexSum_eq_one_of_tendsto_sub_id_cocompact_zero
    {f : ℂ → ℂ} (hf : Continuous f)
    (hInf : Tendsto (fun z ↦ f z - z) (cocompact ℂ) (𝓝 0)) (w : ℂ)
    (hdiscrete : IsDiscrete {z : ℂ | f z = w})
    (hfinite : {z : ℂ | f z = w}.Finite) :
    planarFiberIndexSum f hf w hdiscrete hfinite = 1 := by
  obtain ⟨r, hr, hfiber, hne, hindex⟩ :=
    exists_large_planarCircleIndex_eq_one_and_fiber_subset_ball hf hInf w
  calc
    planarFiberIndexSum f hf w hdiscrete hfinite =
        planarCircleIndex f hf 0 w r hr
          (imageCircleLoop_ne_of_fiber_subset_ball
            f hf 0 w hr hfiber) :=
      (planarCircleIndex_eq_planarFiberIndexSum_of_fiber_subset_ball
        f hf 0 w hr hdiscrete hfinite hfiber).symm
    _ = 1 := hindex

/--
%%handwave
name:
  Global inversion for an asymptotically identity positive-index map
statement:
  Suppose $f:\mathbb C\to\mathbb C$ is continuous and open,
  $f(z)-z\to0$ at infinity, every fiber is discrete, and every local index is
  positive. Then $f$ is bijective.
proof:
  The asymptotic identity makes $f$ proper. Properness makes every discrete
  fiber finite, and the boundary-degree theorem makes its total local index
  one. The positive-index global inversion criterion then gives bijectivity.
-/
theorem bijective_of_tendsto_sub_id_cocompact_zero_of_isOpenMap_of_localIndex_pos
    {f : ℂ → ℂ} (hf : Continuous f)
    (hInf : Tendsto (fun z ↦ f z - z) (cocompact ℂ) (𝓝 0))
    (hopen : IsOpenMap f)
    (hdiscrete : ∀ w, IsDiscrete {z : ℂ | f z = w})
    (hpos : ∀ w (z : {z : ℂ | f z = w}),
      0 < planarLocalIndex f hf z w z.2 (hdiscrete w)) :
    Function.Bijective f := by
  let hproper : IsProperMap f :=
    isProperMap_of_continuous_of_tendsto_sub_id_cocompact_zero hf hInf
  apply bijective_of_isProperMap_of_isOpenMap_of_planarFiberIndexSum_eq_one
    hf hproper hopen hdiscrete hpos
  intro w
  exact planarFiberIndexSum_eq_one_of_tendsto_sub_id_cocompact_zero
    hf hInf w (hdiscrete w)
      (finite_fiber_of_isProperMap_of_isDiscrete_fiber
        hproper w (hdiscrete w))

/--
%%handwave
name:
  Local index one for an asymptotically identity positive-index map
statement:
  Suppose $f:\mathbb C\to\mathbb C$ is continuous and open,
  $f(z)-z\to0$ at infinity, every fiber is discrete, and every local index is
  positive. Then the local index of $f$ at every $z$ over $f(z)$ is exactly
  $1$.
proof:
  [The map is bijective](lean:JJMath.Quasiconformal.bijective_of_tendsto_sub_id_cocompact_zero_of_isOpenMap_of_localIndex_pos), so the fiber over $f(z)$ is the singleton $\{z\}$. Its total index is $1$ by the boundary-degree argument, and the singleton fiber sum is the local index at $z$.
-/
theorem planarLocalIndex_eq_one_of_tendsto_sub_id_cocompact_zero
    {f : ℂ → ℂ} (hf : Continuous f)
    (hInf : Tendsto (fun z ↦ f z - z) (cocompact ℂ) (𝓝 0))
    (hopen : IsOpenMap f)
    (hdiscrete : ∀ w, IsDiscrete {z : ℂ | f z = w})
    (hpos : ∀ w (z : {z : ℂ | f z = w}),
      0 < planarLocalIndex f hf z w z.2 (hdiscrete w))
    (z : ℂ) :
    planarLocalIndex f hf z (f z) rfl (hdiscrete (f z)) = 1 := by
  have hbij : Function.Bijective f :=
    bijective_of_tendsto_sub_id_cocompact_zero_of_isOpenMap_of_localIndex_pos
      hf hInf hopen hdiscrete hpos
  let hproper : IsProperMap f :=
    isProperMap_of_continuous_of_tendsto_sub_id_cocompact_zero hf hInf
  let hfinite : {x : ℂ | f x = f z}.Finite :=
    finite_fiber_of_isProperMap_of_isDiscrete_fiber
      hproper (f z) (hdiscrete (f z))
  have hsum :
      planarFiberIndexSum f hf (f z) (hdiscrete (f z)) hfinite = 1 :=
    planarFiberIndexSum_eq_one_of_tendsto_sub_id_cocompact_zero
      hf hInf (f z) (hdiscrete (f z)) hfinite
  rw [planarFiberIndexSum_eq_planarLocalIndex_of_unique_preimage
    f hf z (f z) rfl (hdiscrete (f z)) hfinite
      (fun x hx ↦ hbij.1 hx)] at hsum
  exact hsum

/--
%%handwave
name:
  Plane homeomorphism from asymptotic identity and positive local indices
statement:
  Under the preceding hypotheses, $f$ is the forward map of a homeomorphism
  of the complex plane.
proof:
  The degree argument proves that $f$ is bijective. A continuous open
  bijection has continuous inverse.
-/
noncomputable def homeomorphOfTendstoSubIdOfIsOpenMapOfLocalIndexPos
    {f : ℂ → ℂ} (hf : Continuous f)
    (hInf : Tendsto (fun z ↦ f z - z) (cocompact ℂ) (𝓝 0))
    (hopen : IsOpenMap f)
    (hdiscrete : ∀ w, IsDiscrete {z : ℂ | f z = w})
    (hpos : ∀ w (z : {z : ℂ | f z = w}),
      0 < planarLocalIndex f hf z w z.2 (hdiscrete w)) :
    ℂ ≃ₜ ℂ :=
  (Equiv.ofBijective f
    (bijective_of_tendsto_sub_id_cocompact_zero_of_isOpenMap_of_localIndex_pos
      hf hInf hopen hdiscrete hpos)).toHomeomorphOfContinuousOpen hf hopen

/--
%%handwave
name:
  Forward map of the asymptotically identity plane homeomorphism
statement:
  The homeomorphism obtained from asymptotic identity, openness, discrete
  fibers, and positive local indices has forward map exactly $f$.
proof:
  Its underlying equivalence is constructed from the proved bijection $f$.
-/
@[simp]
theorem homeomorphOfTendstoSubIdOfIsOpenMapOfLocalIndexPos_apply
    {f : ℂ → ℂ} (hf : Continuous f)
    (hInf : Tendsto (fun z ↦ f z - z) (cocompact ℂ) (𝓝 0))
    (hopen : IsOpenMap f)
    (hdiscrete : ∀ w, IsDiscrete {z : ℂ | f z = w})
    (hpos : ∀ w (z : {z : ℂ | f z = w}),
      0 < planarLocalIndex f hf z w z.2 (hdiscrete w)) (z : ℂ) :
    homeomorphOfTendstoSubIdOfIsOpenMapOfLocalIndexPos
      hf hInf hopen hdiscrete hpos z = f z := rfl

/--
%%handwave
name:
  Analytic principal solution for a compactly supported coefficient
statement:
  Let $\mu:\mathbb C\to\mathbb C$ be measurable, vanish almost everywhere
  outside a disk, and satisfy $|\mu|\leq k<1$ almost everywhere. Then there
  are an exponent $2<p<3$ and a disk-supported density $h\in L^p\cap L^2$
  such that, with
  $$
    f(z)=z+\mathcal C_ph(z),
    \qquad S=\mathcal S_2h,
  $$
  the map $f$ is continuous, belongs to
  $W^{1,2}_{\mathrm{loc}}(\mathbb C)$, has weak differential
  $$
    Df(z)(v)=(1+S(z))v+h(z)\overline v,
  $$
  satisfies $\partial_{\bar z}f=\mu\,\partial_zf$ and
  $$
    |Df|^2\leq\frac{1+k}{1-k}J_f
  $$
  almost everywhere, obeys $f(z)-z\to0$ as $z\to\infty$, and is proper.
proof:
  Choose the near-$2$ interpolation exponent for which
  $M_\mu\mathcal S_p$ is a strict contraction and solve
  $h-\mu\mathcal S_ph=\mu$ by the Neumann resolvent. The solution has the
  same disk support as $\mu$, hence lies in $L^2$, and compatibility identifies
  $\mathcal S_ph$ with $\mathcal S_2h$ almost everywhere. Rearranging the
  equation gives $h=\mu(1+\mathcal S_2h)$. The rough Cauchy Sobolev theorem
  and the far-field estimate supply the remaining analytic conclusions.  The
  asymptotic identity implies $|f(z)|\to\infty$, hence properness.
-/
theorem exists_analyticPrincipalSolution_of_compactSupport
    (μ : ℂ → ℂ)
    (hμmeas : AEStronglyMeasurable μ (volume : Measure ℂ))
    {k R : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hbound : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ k)
    (hzero : ∀ᵐ z ∂(volume : Measure ℂ), R ≤ ‖z‖ → μ z = 0) :
    ∃ P : NearTwoBeurlingParameters
        ‖(memLp_top_of_bound hμmeas k hbound).toLp μ‖,
      ∃ (h : ℂ → ℂ)
        (hhp : MemLp h (ENNReal.ofReal P.exponent)
          (volume : Measure ℂ))
        (hh2 : MemLp h 2 (volume : Measure ℂ)),
        (∀ᵐ z ∂(volume : Measure ℂ), R ≤ ‖z‖ → h z = 0) ∧
        let S : ℂ → ℂ :=
          (beurlingTransformL2 (hh2.toLp h) : ℂ → ℂ)
        let f : ℂ → ℂ := principalBeltramiMap h
        let df : ℂ → ℂ →L[ℝ] ℂ :=
          principalBeltramiWeakDifferential h S
        Continuous f ∧
          IsProperMap f ∧
          IsLocalW12On Set.univ f df ∧
          WeakBeltramiEquationOn Set.univ μ df ∧
          (∀ᵐ z ∂(volume : Measure ℂ),
            ‖df z‖ ^ 2 ≤ ((1 + k) / (1 - k)) * weakJacobian (df z)) ∧
          Tendsto (fun z ↦ f z - z) (cocompact ℂ) (𝓝 0) := by
  let hμTop : MemLp μ ∞ (volume : Measure ℂ) :=
    memLp_top_of_bound hμmeas k hbound
  let μTop : Lp ℂ ∞ (volume : Measure ℂ) := hμTop.toLp μ
  have hμnorm : ‖μTop‖ < 1 := by
    exact (norm_toLp_top_le_of_ae_bound μ hμTop hk0 hbound).trans_lt hk1
  let P : NearTwoBeurlingParameters ‖μTop‖ :=
    chosenNearTwoBeurlingParameters hμnorm
  let hμp : MemLp μ (ENNReal.ofReal P.exponent)
      (volume : Measure ℂ) :=
    memLp_of_ae_bound_of_ae_zero_outside_closedBall
      μ hμmeas hbound hzero (ENNReal.ofReal P.exponent)
  let g : Lp ℂ (ENNReal.ofReal P.exponent) (volume : Measure ℂ) :=
    hμp.toLp μ
  let Sr := beurlingTransformLpNearTwo
    P.exponent P.dualExponent P.theta P.dual_holder
      P.two_lt_exponent.le
      ⟨P.theta_mem.1.le, P.theta_mem.2.le⟩
      P.reciprocal_exponent
  let hpSol : Lp ℂ (ENNReal.ofReal P.exponent) (volume : Measure ℂ) :=
    beltramiLpNearTwoSolution μTop
      P.exponent P.dualExponent P.theta P.dual_holder
        P.two_lt_exponent.le
        ⟨P.theta_mem.1.le, P.theta_mem.2.le⟩
        P.reciprocal_exponent P.contraction g
  have hμTopzero : ∀ᵐ z ∂(volume : Measure ℂ), R ≤ ‖z‖ →
      (μTop : ℂ → ℂ) z = 0 := by
    filter_upwards [hμTop.coeFn_toLp, hzero] with z hμz hzeroz
    intro hz
    rw [hμz, hzeroz hz]
  have hgzero : ∀ᵐ z ∂(volume : Measure ℂ), R ≤ ‖z‖ →
      (g : ℂ → ℂ) z = 0 := by
    filter_upwards [hμp.coeFn_toLp, hzero] with z hgz hμz
    intro hz
    rw [hgz, hμz hz]
  have hsolzero : ∀ᵐ z ∂(volume : Measure ℂ), R ≤ ‖z‖ →
      (hpSol : ℂ → ℂ) z = 0 := by
    exact beltramiLpNearTwoSolution_ae_zero_outside_closedBall μTop
      P.exponent P.dualExponent P.theta P.dual_holder
        P.two_lt_exponent.le
        ⟨P.theta_mem.1.le, P.theta_mem.2.le⟩
        P.reciprocal_exponent P.contraction hμTopzero g hgzero
  have hμ2 : MemLp μ 2 (volume : Measure ℂ) :=
    memLp_of_ae_bound_of_ae_zero_outside_closedBall
      μ hμmeas hbound hzero 2
  have hg2 : MemLp (g : ℂ → ℂ) 2 (volume : Measure ℂ) :=
    MemLp.ae_eq hμp.coeFn_toLp.symm hμ2
  let hh2 : MemLp (hpSol : ℂ → ℂ) 2 (volume : Measure ℂ) :=
    memLp_two_beltramiLpNearTwoSolution μTop
      P.exponent P.dualExponent P.theta P.dual_holder
        P.two_lt_exponent.le
        ⟨P.theta_mem.1.le, P.theta_mem.2.le⟩
        P.reciprocal_exponent P.contraction hμTopzero g hg2
  let S2 : ℂ → ℂ :=
    (beurlingTransformL2 (hh2.toLp (hpSol : ℂ → ℂ)) : ℂ → ℂ)
  have hcompat : (Sr hpSol : ℂ → ℂ) =ᵐ[volume] S2 := by
    simpa only [Sr, S2, Lp.toLp_coeFn] using
      (beurlingTransformLpNearTwo_toLp_ae_eq_beurlingTransformL2
        P.exponent P.dualExponent P.theta P.dual_holder
          P.two_lt_exponent.le
          ⟨P.theta_mem.1.le, P.theta_mem.2.le⟩
          P.reciprocal_exponent (Lp.stronglyMeasurable hpSol)
            (Lp.memLp hpSol) hh2)
  have hspec : hpSol - μTop • Sr hpSol = g := by
    exact beltramiLpNearTwoSolution_spec μTop
      P.exponent P.dualExponent P.theta P.dual_holder
        P.two_lt_exponent.le
        ⟨P.theta_mem.1.le, P.theta_mem.2.le⟩
        P.reciprocal_exponent P.contraction g
  have hclass : ((hpSol - μTop • Sr hpSol :
      Lp ℂ (ENNReal.ofReal P.exponent) (volume : Measure ℂ)) : ℂ → ℂ)
      =ᵐ[volume] (g : ℂ → ℂ) := by
    rw [hspec]
  have hdensity : ∀ᵐ z ∂(volume : Measure ℂ),
      (hpSol : ℂ → ℂ) z = μ z * (1 + S2 z) := by
    filter_upwards [hclass,
      Lp.coeFn_sub hpSol (μTop • Sr hpSol),
      Lp.coeFn_lpSMul (r := ENNReal.ofReal P.exponent) μTop (Sr hpSol),
      hμTop.coeFn_toLp, hμp.coeFn_toLp, hcompat] with
        z hclassz hsub hmul hμtopz hμpz hSz
    rw [hsub] at hclassz
    change (hpSol : ℂ → ℂ) z -
      ((μTop • Sr hpSol :
        Lp ℂ (ENNReal.ofReal P.exponent) (volume : Measure ℂ)) : ℂ → ℂ) z =
        (g : ℂ → ℂ) z at hclassz
    rw [hmul] at hclassz
    change (hpSol : ℂ → ℂ) z -
      (μTop : ℂ → ℂ) z * (Sr hpSol : ℂ → ℂ) z =
        (g : ℂ → ℂ) z at hclassz
    rw [hμtopz, hμpz, hSz] at hclassz
    change (hpSol : ℂ → ℂ) z - μ z * S2 z = μ z at hclassz
    calc
      (hpSol : ℂ → ℂ) z = μ z + μ z * S2 z :=
        (sub_eq_iff_eq_add).mp hclassz
      _ = μ z * (1 + S2 z) := by ring
  refine ⟨P, (hpSol : ℂ → ℂ), Lp.memLp hpSol, hh2, hsolzero, ?_⟩
  dsimp only
  have hcontdecay :=
    continuous_principalBeltramiMap_and_tendsto_sub_cocompact
      P.dual_holder.symm P.two_lt_exponent (Lp.memLp hpSol) hsolzero
  refine ⟨hcontdecay.1,
    isProperMap_of_continuous_of_tendsto_sub_id_cocompact_zero
      hcontdecay.1 hcontdecay.2, ?_, ?_, ?_, hcontdecay.2⟩
  · simpa only [S2] using
      (principalBeltramiMap_isLocalW12On
        P.dual_holder.symm P.two_lt_exponent (Lp.memLp hpSol) hsolzero)
  · exact principalBeltramiWeakDifferential_weakBeltramiEquation
      μ (hpSol : ℂ → ℂ) S2 hdensity
  · have hdist :=
      WeakBeltramiEquationOn.norm_sq_le_distortion_mul_weakJacobian
        (μ := μ)
        (principalBeltramiWeakDifferential_weakBeltramiEquation
          μ (hpSol : ℂ → ℂ) S2 hdensity)
        (by simpa [HasEssentialNormLEOn] using hbound) hk0 hk1
    simpa only [Measure.restrict_univ, S2] using hdist

end

end Quasiconformal

end JJMath
