import JJMath.RiemannianGeometry.Basic
import JJMath.Uniformization.SmoothFrontierOneManifold
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# A global signed coordinate near a smooth frontier

The local product charts of a smooth boundary have compatible signs: their
first coordinates are negative on the domain and positive on the exterior.
This file uses a smooth partition of unity to glue those local first
coordinates.  The result is a single smooth function on the ambient surface
which vanishes precisely on the frontier in an open neighborhood and has the
expected sign on either side.

On an overlap, the transverse derivatives of two local signed coordinates
are positive multiples of one another. Differentiating the locally finite
partition sum on the frontier therefore shows that the glued function has
nonzero differential there. Its normalized gradient flow can now provide the
transverse collar coordinate globally.
-/

open Function Set Filter
open scoped Manifold Topology ContDiff

namespace JJMath.Uniformization

noncomputable section

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
variable [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]

/-- A plane local diffeomorphism which preserves the positive side of a
vertical axis has positive normal derivative along that axis. -/
private theorem first_deriv_pos_of_bijective_fderiv
    {T : (ℝ × ℝ) → (ℝ × ℝ)} {z : ℝ × ℝ}
    (hT : DifferentiableAt ℝ T z)
    (hbij : Function.Bijective (fderiv ℝ T z))
    (hzero : (T z).1 = 0)
    (hvertical : deriv (fun s : ℝ => (T (z + (0, s))).1) 0 = 0)
    (hpositive : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < (T (z + (s, 0))).1) :
    0 < deriv (fun s : ℝ => (T (z + (s, 0))).1) 0 := by
  let L := fderiv ℝ T z
  let e1 : ℝ × ℝ := (1, 0)
  let e2 : ℝ × ℝ := (0, 1)
  let h : ℝ → ℝ := fun s => (T (z + (s, 0))).1
  let k : ℝ → ℝ := fun s => (T (z + (0, s))).1
  have hcurve : HasDerivAt (fun s : ℝ => z + (s, 0)) e1 0 := by
    convert hasDerivAt_const (x := (0 : ℝ)) z |>.add
      ((hasDerivAt_id (x := (0 : ℝ))).prodMk
        (hasDerivAt_const (x := (0 : ℝ)) 0)) using 1
    all_goals simp [e1]
  have kcurve : HasDerivAt (fun s : ℝ => z + (0, s)) e2 0 := by
    convert hasDerivAt_const (x := (0 : ℝ)) z |>.add
      ((hasDerivAt_const (x := (0 : ℝ)) 0).prodMk
        (hasDerivAt_id (x := (0 : ℝ)))) using 1
    all_goals simp [e2]
  have hh : HasDerivAt h (L e1).1 0 := by
    have hcomp : HasDerivAt (T ∘ fun s : ℝ => z + (s, 0)) (L e1) 0 := by
      simpa [L] using hT.hasFDerivAt.comp_hasDerivAt_of_eq 0 hcurve (by
        ext <;> simp)
    simpa [h, Function.comp_def] using
      hasFDerivAt_fst.comp_hasDerivAt 0 hcomp
  have hk : HasDerivAt k (L e2).1 0 := by
    have hcomp : HasDerivAt (T ∘ fun s : ℝ => z + (0, s)) (L e2) 0 := by
      simpa [L] using hT.hasFDerivAt.comp_hasDerivAt_of_eq 0 kcurve (by
        ext <;> simp)
    simpa [k, Function.comp_def] using
      hasFDerivAt_fst.comp_hasDerivAt 0 hcomp
  have hderiv : deriv h 0 = (L e1).1 := hh.deriv
  have hkzero : (L e2).1 = 0 := by
    rw [← hk.deriv]
    exact hvertical
  have hhne : deriv h 0 ≠ 0 := by
    rw [hderiv]
    intro hLzero
    obtain ⟨v, hv⟩ := hbij.2 (1, 0)
    have hvdecomp : v = v.1 • e1 + v.2 • e2 := by
      ext <;> simp [e1, e2]
    have hfirstzero : (L v).1 = 0 := by
      rw [hvdecomp, map_add, map_smul, map_smul]
      simp [hLzero, hkzero]
    rw [hv] at hfirstzero
    norm_num at hfirstzero
  rcases lt_or_gt_of_ne hhne with hneg | hpos
  · have hzero' : h 0 = 0 := by
      change (T (z + (0, 0))).1 = 0
      have hp : z + (0, 0) = z := by ext <;> simp
      rw [hp]
      exact hzero
    have hsign := eventually_nhdsWithin_sign_eq_of_deriv_neg hneg hzero'
    have hfalse : ∀ᶠ s : ℝ in 𝓝[>] 0, False := by
      filter_upwards [hsign.filter_mono inf_le_left, hpositive,
        self_mem_nhdsWithin] with s hs hhs hspos
      have hsneg : 0 - s < 0 := sub_neg.mpr hspos
      have hhs' : 0 < h s := by simpa [h] using hhs
      rw [sign_pos hhs', sign_neg hsneg] at hs
      norm_num at hs
    rcases Filter.Eventually.exists hfalse with ⟨s, hs⟩
    exact hs.elim
  · exact hpos

/-- A smooth partition of unity near the compact frontier, subordinate to the
centered product-ball coordinates. -/
theorem exists_smoothBoundaryProductBall_partitionOfUnity
    (D : SmoothBoundaryDomain X) :
    ∃ rho : SmoothPartitionOfUnity (frontier D.carrier)
        SurfaceRealModel X (frontier D.carrier),
      rho.IsSubordinate (fun p => smoothBoundaryProductBallSource D p) := by
  letI : SecondCountableTopology X :=
    rado_secondCountableTopology_riemannSurface X
  letI : SigmaCompactSpace X := inferInstance
  apply SmoothPartitionOfUnity.exists_isSubordinate
      SurfaceRealModel isClosed_frontier
      (fun p => smoothBoundaryProductBallSource D p)
  · exact fun p => smoothBoundaryProductBallSource_isOpen D p
  · intro x hx
    let p : frontier D.carrier := ⟨x, hx⟩
    exact mem_iUnion.mpr
      ⟨p, smoothBoundaryProductBallSource_point_mem D p⟩

/-- A fixed smooth partition of unity used to glue the signed boundary
coordinates. -/
noncomputable def smoothBoundaryProductBallPartitionOfUnity
    (D : SmoothBoundaryDomain X) :
    SmoothPartitionOfUnity (frontier D.carrier)
      SurfaceRealModel X (frontier D.carrier) :=
  Classical.choose (exists_smoothBoundaryProductBall_partitionOfUnity D)

theorem smoothBoundaryProductBallPartitionOfUnity_isSubordinate
    (D : SmoothBoundaryDomain X) :
    (smoothBoundaryProductBallPartitionOfUnity D).IsSubordinate
      (fun p => smoothBoundaryProductBallSource D p) :=
  Classical.choose_spec (exists_smoothBoundaryProductBall_partitionOfUnity D)

/-- The first coordinate of the centered product chart at a frontier point.
Outside the chart source the underlying partial equivalence has an arbitrary
value; the subordinate partition of unity makes that value irrelevant. -/
noncomputable def smoothBoundaryLocalSignedCoordinate
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) (x : X) : ℝ :=
  ((smoothBoundaryProductChartAt D p).coordinate x).1

omit [RiemannSurface X] in
theorem smoothBoundaryLocalSignedCoordinate_contMDiffOn
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) :
    ContMDiffOn SurfaceRealModel 𝓘(ℝ) ∞
      (smoothBoundaryLocalSignedCoordinate D p)
      (smoothBoundaryProductBallSource D p) := by
  have hcoordinate :
      ContMDiffOn SurfaceRealModel 𝓘(ℝ, ℝ × ℝ) ∞
        (smoothBoundaryProductChartAt D p).coordinate
        (smoothBoundaryProductBallSource D p) :=
    ((smoothBoundaryProductChartAt D p).coordinate.contMDiffOn_toFun.mono
      inter_subset_left).of_le (by exact WithTop.coe_le_coe.mpr le_top)
  intro x hx
  simpa only [smoothBoundaryLocalSignedCoordinate, Function.comp_apply] using
    (contDiffAt_fst.comp_contMDiffWithinAt (hcoordinate x hx))

/-- The partition-of-unity sum of the local signed first coordinates. -/
noncomputable def smoothBoundaryGlobalSignedCoordinate
    (D : SmoothBoundaryDomain X) (x : X) : ℝ :=
  ∑ᶠ p : frontier D.carrier,
    smoothBoundaryProductBallPartitionOfUnity D p x •
      smoothBoundaryLocalSignedCoordinate D p x

/--
%%handwave
name:
  Smoothness of the global signed boundary coordinate
statement:
  If \((\rho_p)_p\) is a smooth partition of unity subordinate to boundary
  product-ball charts and \(s_p\) is the signed first coordinate in the
  \(p\)-chart, then
  \[
    s(x)=\sum_p\rho_p(x)s_p(x)
  \]
  defines a smooth function on the entire surface.
proof:
  Each \(s_p\) is smooth on the source supporting \(\rho_p\).  Subordination
  and local finiteness make the weighted sum locally finite, so the standard
  partition-of-unity gluing theorem gives smoothness.
-/
theorem smoothBoundaryGlobalSignedCoordinate_contMDiff
    (D : SmoothBoundaryDomain X) :
    ContMDiff SurfaceRealModel 𝓘(ℝ) ∞
      (smoothBoundaryGlobalSignedCoordinate D) := by
  let rho := smoothBoundaryProductBallPartitionOfUnity D
  have hrho : rho.IsSubordinate
      (fun p => smoothBoundaryProductBallSource D p) :=
    smoothBoundaryProductBallPartitionOfUnity_isSubordinate D
  simpa only [smoothBoundaryGlobalSignedCoordinate, rho] using
    hrho.contMDiff_finsum_smul
      (fun p => smoothBoundaryProductBallSource_isOpen D p)
      (fun p => smoothBoundaryLocalSignedCoordinate_contMDiffOn D p)

/-- The sum of the partition functions.  It equals one on the frontier and is
positive throughout a neighborhood of it. -/
noncomputable def smoothBoundaryPartitionSum
    (D : SmoothBoundaryDomain X) (x : X) : ℝ :=
  ∑ᶠ p : frontier D.carrier,
    smoothBoundaryProductBallPartitionOfUnity D p x

theorem smoothBoundaryPartitionSum_contMDiff
    (D : SmoothBoundaryDomain X) :
    ContMDiff SurfaceRealModel 𝓘(ℝ) ∞
      (smoothBoundaryPartitionSum D) := by
  exact (smoothBoundaryProductBallPartitionOfUnity D).contMDiff_sum

@[simp]
theorem smoothBoundaryPartitionSum_eq_one_of_mem_frontier
    (D : SmoothBoundaryDomain X) {x : X} (hx : x ∈ frontier D.carrier) :
    smoothBoundaryPartitionSum D x = 1 := by
  exact (smoothBoundaryProductBallPartitionOfUnity D).sum_eq_one hx

/-- The open neighborhood on which the subordinate partition is definitely
nonzero. -/
def smoothBoundaryGlobalCoordinateNeighborhood
    (D : SmoothBoundaryDomain X) : Set X :=
  {x | (1 / 2 : ℝ) < smoothBoundaryPartitionSum D x}

theorem smoothBoundaryGlobalCoordinateNeighborhood_isOpen
    (D : SmoothBoundaryDomain X) :
    IsOpen (smoothBoundaryGlobalCoordinateNeighborhood D) := by
  exact isOpen_lt continuous_const
    (smoothBoundaryPartitionSum_contMDiff D).continuous

theorem frontier_subset_smoothBoundaryGlobalCoordinateNeighborhood
    (D : SmoothBoundaryDomain X) :
    frontier D.carrier ⊆ smoothBoundaryGlobalCoordinateNeighborhood D := by
  intro x hx
  change (1 / 2 : ℝ) < smoothBoundaryPartitionSum D x
  rw [smoothBoundaryPartitionSum_eq_one_of_mem_frontier D hx]
  norm_num

theorem smoothBoundaryGlobalSignedCoordinate_eq_zero_of_mem_frontier
    (D : SmoothBoundaryDomain X) {x : X} (hx : x ∈ frontier D.carrier) :
    smoothBoundaryGlobalSignedCoordinate D x = 0 := by
  classical
  let rho := smoothBoundaryProductBallPartitionOfUnity D
  have hrho : rho.IsSubordinate
      (fun p => smoothBoundaryProductBallSource D p) :=
    smoothBoundaryProductBallPartitionOfUnity_isSubordinate D
  rw [smoothBoundaryGlobalSignedCoordinate]
  apply finsum_eq_zero_of_forall_eq_zero
  intro p
  by_cases hp : rho p x = 0
  · simp [rho, hp]
  · have hx_support : x ∈ support (rho p) := hp
    have hx_tsupport : x ∈ tsupport (rho p) :=
      subset_tsupport _ hx_support
    have hx_ball : x ∈ smoothBoundaryProductBallSource D p :=
      hrho p hx_tsupport
    have hx_zero : smoothBoundaryLocalSignedCoordinate D p x = 0 := by
      exact (smoothBoundaryProductChartAt D p).frontier_iff_zero x
        hx_ball.1 |>.mp hx
    simp [hx_zero]

omit [RiemannSurface X] in
theorem smoothBoundaryLocalSignedCoordinate_neg
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) {x : X}
    (hxD : x ∈ D.carrier)
    (hxBall : x ∈ smoothBoundaryProductBallSource D p) :
    smoothBoundaryLocalSignedCoordinate D p x < 0 := by
  exact (smoothBoundaryProductChartAt D p).domain_iff_negative x
    hxBall.1 |>.mp hxD

omit [RiemannSurface X] in
theorem smoothBoundaryLocalSignedCoordinate_pos
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) {x : X}
    (hxExterior : x ∉ closure D.carrier)
    (hxBall : x ∈ smoothBoundaryProductBallSource D p) :
    0 < smoothBoundaryLocalSignedCoordinate D p x := by
  have hnot_neg : ¬ smoothBoundaryLocalSignedCoordinate D p x < 0 := by
    intro hneg
    exact hxExterior (subset_closure
      ((smoothBoundaryProductChartAt D p).domain_iff_negative x
        hxBall.1 |>.mpr hneg))
  have hne : smoothBoundaryLocalSignedCoordinate D p x ≠ 0 := by
    intro hzero
    have hxFrontier : x ∈ frontier D.carrier :=
      (smoothBoundaryProductChartAt D p).frontier_iff_zero x
        hxBall.1 |>.mpr hzero
    exact hxExterior (frontier_subset_closure hxFrontier)
  exact lt_of_le_of_ne (le_of_not_gt hnot_neg) hne.symm

/-- On the domain side of the collar neighborhood, the glued coordinate is
strictly negative. -/
theorem smoothBoundaryGlobalSignedCoordinate_neg
    (D : SmoothBoundaryDomain X) {x : X}
    (hxD : x ∈ D.carrier)
    (hxN : x ∈ smoothBoundaryGlobalCoordinateNeighborhood D) :
    smoothBoundaryGlobalSignedCoordinate D x < 0 := by
  classical
  let rho := smoothBoundaryProductBallPartitionOfUnity D
  let g : frontier D.carrier → X → ℝ :=
    fun p => smoothBoundaryLocalSignedCoordinate D p
  have hrho : rho.IsSubordinate
      (fun p => smoothBoundaryProductBallSource D p) :=
    smoothBoundaryProductBallPartitionOfUnity_isSubordinate D
  have hsum_pos : 0 < ∑ᶠ p : frontier D.carrier, rho p x := by
    have hxN' : (1 / 2 : ℝ) < smoothBoundaryPartitionSum D x := hxN
    have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
    exact hhalf.trans (by simpa [smoothBoundaryPartitionSum, rho] using hxN')
  have hex : ∃ p : frontier D.carrier, 0 < rho p x := by
    by_contra h
    push Not at h
    have hzero : ∀ p : frontier D.carrier, rho p x = 0 := fun p =>
      le_antisymm (h p) (rho.nonneg p x)
    simp only [hzero, finsum_zero] at hsum_pos
    exact (lt_irrefl 0) hsum_pos
  have hterm_nonneg : ∀ p : frontier D.carrier, 0 ≤ -(rho p x * g p x) := by
    intro p
    by_cases hp : rho p x = 0
    · simp [hp]
    · have hxBall : x ∈ smoothBoundaryProductBallSource D p := by
        apply hrho p
        exact subset_tsupport _ hp
      exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos
        (rho.nonneg p x) (smoothBoundaryLocalSignedCoordinate_neg D p hxD hxBall).le)
  have hterm_pos : ∃ p : frontier D.carrier, 0 < -(rho p x * g p x) := by
    rcases hex with ⟨p, hp⟩
    have hxBall : x ∈ smoothBoundaryProductBallSource D p := by
      apply hrho p
      exact subset_tsupport _ hp.ne'
    refine ⟨p, neg_pos.mpr ?_⟩
    exact mul_neg_of_pos_of_neg hp
      (smoothBoundaryLocalSignedCoordinate_neg D p hxD hxBall)
  have hfinite : HasFiniteSupport (fun p : frontier D.carrier => -(rho p x * g p x)) := by
    apply (rho.locallyFinite.point_finite x).subset
    apply compl_subset_compl.2
    rintro p (hp : rho p x = 0)
    simpa only [neg_eq_zero, mul_eq_zero] using Or.inl hp
  have hpositive : 0 < ∑ᶠ p : frontier D.carrier, -(rho p x * g p x) :=
    finsum_pos hterm_nonneg hterm_pos hfinite
  rw [show smoothBoundaryGlobalSignedCoordinate D x =
      ∑ᶠ p : frontier D.carrier, rho p x * g p x by
        simp only [smoothBoundaryGlobalSignedCoordinate, rho, g, smul_eq_mul]]
  rw [← neg_pos]
  change 0 < (AddEquiv.neg ℝ)
    (∑ᶠ p : frontier D.carrier, rho p x * g p x)
  rw [(AddEquiv.neg ℝ).map_finsum]
  exact hpositive

/-- On the exterior side of the collar neighborhood, the glued coordinate is
strictly positive. -/
theorem smoothBoundaryGlobalSignedCoordinate_pos
    (D : SmoothBoundaryDomain X) {x : X}
    (hxExterior : x ∉ closure D.carrier)
    (hxN : x ∈ smoothBoundaryGlobalCoordinateNeighborhood D) :
    0 < smoothBoundaryGlobalSignedCoordinate D x := by
  classical
  let rho := smoothBoundaryProductBallPartitionOfUnity D
  let g : frontier D.carrier → X → ℝ :=
    fun p => smoothBoundaryLocalSignedCoordinate D p
  have hrho : rho.IsSubordinate
      (fun p => smoothBoundaryProductBallSource D p) :=
    smoothBoundaryProductBallPartitionOfUnity_isSubordinate D
  have hsum_pos : 0 < ∑ᶠ p : frontier D.carrier, rho p x := by
    have hxN' : (1 / 2 : ℝ) < smoothBoundaryPartitionSum D x := hxN
    have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
    exact hhalf.trans (by simpa [smoothBoundaryPartitionSum, rho] using hxN')
  have hex : ∃ p : frontier D.carrier, 0 < rho p x := by
    by_contra h
    push Not at h
    have hzero : ∀ p : frontier D.carrier, rho p x = 0 := fun p =>
      le_antisymm (h p) (rho.nonneg p x)
    simp only [hzero, finsum_zero] at hsum_pos
    exact (lt_irrefl 0) hsum_pos
  have hterm_nonneg : ∀ p : frontier D.carrier, 0 ≤ rho p x * g p x := by
    intro p
    by_cases hp : rho p x = 0
    · simp [hp]
    · have hxBall : x ∈ smoothBoundaryProductBallSource D p := by
        apply hrho p
        exact subset_tsupport _ hp
      exact mul_nonneg (rho.nonneg p x)
        (smoothBoundaryLocalSignedCoordinate_pos D p hxExterior hxBall).le
  have hterm_pos : ∃ p : frontier D.carrier, 0 < rho p x * g p x := by
    rcases hex with ⟨p, hp⟩
    have hxBall : x ∈ smoothBoundaryProductBallSource D p := by
      apply hrho p
      exact subset_tsupport _ hp.ne'
    exact ⟨p, mul_pos hp
      (smoothBoundaryLocalSignedCoordinate_pos D p hxExterior hxBall)⟩
  have hfinite : HasFiniteSupport (fun p : frontier D.carrier => rho p x * g p x) := by
    apply (rho.locallyFinite.point_finite x).subset
    apply compl_subset_compl.2
    rintro p (hp : rho p x = 0)
    simpa only [mul_eq_zero] using Or.inl hp
  have hpositive : 0 < ∑ᶠ p : frontier D.carrier, rho p x * g p x :=
    finsum_pos hterm_nonneg hterm_pos hfinite
  simpa only [smoothBoundaryGlobalSignedCoordinate, rho, g, smul_eq_mul] using hpositive

/--
%%handwave
name:
  Zero locus of the global signed coordinate
statement:
  On the open neighborhood where \(\sum_p\rho_p>1/2\), the global signed
  coordinate \(s=\sum_p\rho_p s_p\) satisfies
  \[
    s(x)=0\quad\Longleftrightarrow\quad x\in\partial D.
  \]
proof:
  Every local signed coordinate is zero on the frontier, so their weighted
  sum is zero there.  Inside \(D\) all active coordinates are negative, while
  outside \(\overline D\) they are positive; the positive partition sum makes
  the corresponding weighted sum strictly nonzero.
-/
theorem smoothBoundaryGlobalSignedCoordinate_eq_zero_iff_mem_frontier
    (D : SmoothBoundaryDomain X) {x : X}
    (hxN : x ∈ smoothBoundaryGlobalCoordinateNeighborhood D) :
    smoothBoundaryGlobalSignedCoordinate D x = 0 ↔
      x ∈ frontier D.carrier := by
  constructor
  · intro hzero
    rw [frontier, D.isOpen.interior_eq]
    constructor
    · by_contra hxClosure
      have hpos := smoothBoundaryGlobalSignedCoordinate_pos D hxClosure hxN
      rw [hzero] at hpos
      exact (lt_irrefl 0) hpos
    · intro hxD
      have hneg := smoothBoundaryGlobalSignedCoordinate_neg D hxD hxN
      rw [hzero] at hneg
      exact (lt_irrefl 0) hneg
  · exact smoothBoundaryGlobalSignedCoordinate_eq_zero_of_mem_frontier D

/-- In the global coordinate neighborhood, the negative side of the signed
coordinate is exactly the domain. -/
theorem smoothBoundaryGlobalSignedCoordinate_lt_zero_iff_mem_carrier
    (D : SmoothBoundaryDomain X) {x : X}
    (hxN : x ∈ smoothBoundaryGlobalCoordinateNeighborhood D) :
    smoothBoundaryGlobalSignedCoordinate D x < 0 ↔ x ∈ D.carrier := by
  constructor
  · intro hxneg
    by_contra hxD
    by_cases hxclosure : x ∈ closure D.carrier
    · have hxfrontier : x ∈ frontier D.carrier := by
        rw [frontier, D.isOpen.interior_eq]
        exact ⟨hxclosure, hxD⟩
      have hxzero :=
        smoothBoundaryGlobalSignedCoordinate_eq_zero_of_mem_frontier D hxfrontier
      linarith
    · have hxpos := smoothBoundaryGlobalSignedCoordinate_pos D hxclosure hxN
      linarith
  · exact fun hxD => smoothBoundaryGlobalSignedCoordinate_neg D hxD hxN

/-- In the global coordinate neighborhood, the positive side of the signed
coordinate is exactly the complement of the domain closure. -/
theorem smoothBoundaryGlobalSignedCoordinate_pos_iff_not_mem_closure
    (D : SmoothBoundaryDomain X) {x : X}
    (hxN : x ∈ smoothBoundaryGlobalCoordinateNeighborhood D) :
    0 < smoothBoundaryGlobalSignedCoordinate D x ↔ x ∉ closure D.carrier := by
  constructor
  · intro hxpos hxclosure
    by_cases hxD : x ∈ D.carrier
    · have hxneg := smoothBoundaryGlobalSignedCoordinate_neg D hxD hxN
      linarith
    · have hxfrontier : x ∈ frontier D.carrier := by
        rw [frontier, D.isOpen.interior_eq]
        exact ⟨hxclosure, hxD⟩
      have hxzero :=
        smoothBoundaryGlobalSignedCoordinate_eq_zero_of_mem_frontier D hxfrontier
      linarith
  · exact fun hx => smoothBoundaryGlobalSignedCoordinate_pos D hx hxN

omit [RiemannSurface X] in
/--
%%handwave
name:
  Positive transverse derivative of boundary-chart transitions
statement:
  Let \(\Phi_p,\Phi_q\) be overlapping signed boundary product charts at
  \(x\in\partial D\), and put \(z=\Phi_p(x)\).  For the transition
  \(T=\Phi_q\circ\Phi_p^{-1}\),
  \[
    \frac{d}{ds}\Big|_{s=0}\operatorname{pr}_1T(z+(s,0))>0.
  \]
proof:
  The transition sends the central diameter to itself, so the derivative of
  its first component in the tangential direction is zero.  Its derivative
  is invertible, hence the transverse derivative is nonzero.  Both signed
  charts put the domain on the negative side and the exterior on the positive
  side, forcing this nonzero derivative to be positive.
-/
theorem smoothBoundaryProductChart_transition_first_deriv_pos
    (D : SmoothBoundaryDomain X) (p q : frontier D.carrier) {x : X}
    (hxfrontier : x ∈ frontier D.carrier)
    (hxp : x ∈ (smoothBoundaryProductChartAt D p).coordinate.source)
    (hxq : x ∈ (smoothBoundaryProductChartAt D q).coordinate.source) :
    let Cp := smoothBoundaryProductChartAt D p
    let Cq := smoothBoundaryProductChartAt D q
    let T := JJMath.Manifold.PartialDiffeomorph.trans
      Cp.coordinate.symm Cq.coordinate
    let z := Cp.coordinate x
    0 < deriv (fun s : ℝ => (T (z + (s, 0))).1) 0 := by
  dsimp only
  let Cp := smoothBoundaryProductChartAt D p
  let Cq := smoothBoundaryProductChartAt D q
  let T := JJMath.Manifold.PartialDiffeomorph.trans
    Cp.coordinate.symm Cq.coordinate
  let z := Cp.coordinate x
  have hinv : Cp.coordinate.symm z = x := by
    exact Cp.coordinate.left_inv hxp
  have hzsource : z ∈ T.source := by
    rw [show T.source = Cp.coordinate.target ∩
        Cp.coordinate.symm ⁻¹' Cq.coordinate.source from
      PartialEquiv.trans_source Cp.coordinate.symm.toPartialEquiv
        Cq.coordinate.toPartialEquiv]
    exact ⟨Cp.coordinate.map_source hxp, by simpa [hinv] using hxq⟩
  have hzfirst : z.1 = 0 := by
    exact (Cp.frontier_iff_zero x hxp).mp hxfrontier
  have hTzero : (T z).1 = 0 := by
    change (Cq.coordinate (Cp.coordinate.symm z)).1 = 0
    rw [hinv]
    exact (Cq.frontier_iff_zero x hxq).mp hxfrontier
  have hTdiff : DifferentiableAt ℝ T z := by
    exact (T.contMDiffOn_toFun.contMDiffAt
      (T.open_source.mem_nhds hzsource)).mdifferentiableAt (by norm_num)
      |>.differentiableAt
  have hTbij : Function.Bijective (fderiv ℝ T z) := by
    have he : T.toOpenPartialHomeomorph.MDifferentiable
        𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) := by
      exact ⟨T.mdifferentiableOn (by norm_num),
        T.symm.mdifferentiableOn (by norm_num)⟩
    simpa only [mfderiv_eq_fderiv] using he.mfderiv_bijective hzsource
  have hzero_on_vertical : ∀ w ∈ T.source, w.1 = 0 → (T w).1 = 0 := by
    intro w hw hwfirst
    have hw' : w ∈ Cp.coordinate.target ∧
        Cp.coordinate.symm w ∈ Cq.coordinate.source := by
      simpa only [T, PartialEquiv.trans_source] using hw
    have hsymm_source : Cp.coordinate.symm w ∈ Cp.coordinate.source :=
      Cp.coordinate.symm.map_source hw'.1
    have hright : Cp.coordinate (Cp.coordinate.symm w) = w :=
      Cp.coordinate.right_inv hw'.1
    have hfrontier : Cp.coordinate.symm w ∈ frontier D.carrier :=
      (Cp.frontier_iff_zero _ hsymm_source).mpr (by
        rw [hright]
        exact hwfirst)
    change (Cq.coordinate (Cp.coordinate.symm w)).1 = 0
    exact (Cq.frontier_iff_zero _ hw'.2).mp hfrontier
  have kcurve_cont : ContinuousAt (fun s : ℝ => z + (0, s)) 0 := by
    fun_prop
  have kbase : z + (0, (0 : ℝ)) ∈ T.source := by
    have hzadd : z + (0, (0 : ℝ)) = z := by ext <;> simp
    rwa [hzadd]
  have ksource : ∀ᶠ s : ℝ in 𝓝 0, z + (0, s) ∈ T.source :=
    kcurve_cont.eventually (T.open_source.mem_nhds kbase)
  have kzero : (fun s : ℝ => (T (z + (0, s))).1) =ᶠ[𝓝 0]
      (fun _ : ℝ => 0) := by
    filter_upwards [ksource] with s hs
    exact hzero_on_vertical _ hs (by simp [hzfirst])
  have hvertical : deriv (fun s : ℝ => (T (z + (0, s))).1) 0 = 0 := by
    rw [Filter.EventuallyEq.deriv_eq kzero]
    simp
  have hcurve_cont : ContinuousAt (fun s : ℝ => z + (s, 0)) 0 := by
    fun_prop
  have hbase : z + ((0 : ℝ), 0) ∈ T.source := by
    have hzadd : z + ((0 : ℝ), 0) = z := by ext <;> simp
    rwa [hzadd]
  have hsource : ∀ᶠ s : ℝ in 𝓝 0, z + (s, 0) ∈ T.source :=
    hcurve_cont.eventually (T.open_source.mem_nhds hbase)
  have hpositive : ∀ᶠ s : ℝ in 𝓝[>] 0,
      0 < (T (z + (s, 0))).1 := by
    filter_upwards [hsource.filter_mono inf_le_left,
      self_mem_nhdsWithin] with s hs hspos
    let w : ℝ × ℝ := z + (s, 0)
    let y : X := Cp.coordinate.symm w
    have hw' : w ∈ Cp.coordinate.target ∧ y ∈ Cq.coordinate.source := by
      simpa only [T, PartialEquiv.trans_source] using hs
    have hyCp : y ∈ Cp.coordinate.source := Cp.coordinate.symm.map_source hw'.1
    have hcoord : Cp.coordinate y = w := Cp.coordinate.right_inv hw'.1
    have hwpos : 0 < w.1 := by
      change 0 < z.1 + s
      rw [hzfirst, zero_add]
      exact hspos
    have hy_not_D : y ∉ D.carrier := by
      intro hyD
      have hneg := (Cp.domain_iff_negative y hyCp).mp hyD
      rw [hcoord] at hneg
      exact (not_lt_of_ge hwpos.le) hneg
    have hy_not_frontier : y ∉ frontier D.carrier := by
      intro hyfrontier
      have hzero := (Cp.frontier_iff_zero y hyCp).mp hyfrontier
      rw [hcoord] at hzero
      exact hwpos.ne' hzero
    have hnotneg : ¬ (Cq.coordinate y).1 < 0 := by
      intro hneg
      exact hy_not_D ((Cq.domain_iff_negative y hw'.2).mpr hneg)
    have hne : (Cq.coordinate y).1 ≠ 0 := by
      intro hzero
      exact hy_not_frontier ((Cq.frontier_iff_zero y hw'.2).mpr hzero)
    change 0 < (Cq.coordinate y).1
    exact lt_of_le_of_ne (le_of_not_gt hnotneg) hne.symm
  exact first_deriv_pos_of_bijective_fderiv hTdiff hTbij hTzero
    hvertical hpositive

/-- At every frontier point, some chosen product-chart normal sees a strictly
positive derivative of the glued signed coordinate. -/
theorem exists_smoothBoundaryGlobalSignedCoordinate_productChart_deriv_pos
    (D : SmoothBoundaryDomain X) {x : X}
    (hxfrontier : x ∈ frontier D.carrier) :
    ∃ p : frontier D.carrier,
      let Cp := smoothBoundaryProductChartAt D p
      let z := Cp.coordinate x
      x ∈ Cp.coordinate.source ∧
        0 < deriv (fun s : ℝ =>
          smoothBoundaryGlobalSignedCoordinate D
            (Cp.coordinate.symm (z + (s, 0)))) 0 := by
  classical
  let rho := smoothBoundaryProductBallPartitionOfUnity D
  have hrho : rho.IsSubordinate
      (fun q => smoothBoundaryProductBallSource D q) :=
    smoothBoundaryProductBallPartitionOfUnity_isSubordinate D
  obtain ⟨p, hp⟩ := rho.exists_pos_of_mem hxfrontier
  refine ⟨p, ?_⟩
  dsimp only
  let Cp := smoothBoundaryProductChartAt D p
  let z := Cp.coordinate x
  let c : ℝ → X := fun s => Cp.coordinate.symm (z + (s, 0))
  let S := rho.fintsupport x
  have hxpBall : x ∈ smoothBoundaryProductBallSource D p := by
    apply hrho p
    exact subset_tsupport _ hp.ne'
  have hxp : x ∈ Cp.coordinate.source := hxpBall.1
  refine ⟨hxp, ?_⟩
  have hzTarget : z ∈ Cp.coordinate.target := Cp.coordinate.map_source hxp
  have hc0 : c 0 = x := by
    change Cp.coordinate.symm (z + (0, 0)) = x
    have hzadd : z + (0, 0) = z := by ext <;> simp
    rw [hzadd]
    exact Cp.coordinate.left_inv hxp
  have hline : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, ℝ × ℝ) 2
      (fun s : ℝ => z + (s, 0)) 0 := by
    exact (by fun_prop : ContDiffAt ℝ 2
      (fun s : ℝ => z + (s, 0)) 0).contMDiffAt
  have hc_smooth : ContMDiffAt 𝓘(ℝ) SurfaceRealModel 2 c 0 := by
    have hsymm : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) SurfaceRealModel 2
        Cp.coordinate.symm z :=
      (Cp.coordinate.contMDiffOn_invFun.contMDiffAt
        (Cp.coordinate.open_target.mem_nhds hzTarget)).of_le
          (by exact WithTop.coe_le_coe.mpr le_top)
    have hcomp := hsymm.comp_of_eq hline (by
      ext <;> simp)
    simpa only [c, Function.comp_def] using hcomp
  have hc_cont : ContinuousAt c 0 := hc_smooth.continuousAt
  have hsupport : ∀ᶠ s : ℝ in 𝓝 0,
      rho.finsupport (c s) ⊆ S := by
    have hev : ∀ᶠ y in 𝓝 (c 0),
        rho.finsupport y ⊆ rho.fintsupport x := by
      simpa only [hc0] using rho.eventually_finsupport_subset x
    simpa only [S] using hc_cont.eventually hev
  have hfinite_eq :
      (fun s : ℝ => smoothBoundaryGlobalSignedCoordinate D (c s)) =ᶠ[𝓝 0]
        (fun s : ℝ => ∑ q ∈ S,
          rho q (c s) * smoothBoundaryLocalSignedCoordinate D q (c s)) := by
    filter_upwards [hsupport] with s hs
    rw [smoothBoundaryGlobalSignedCoordinate]
    simp only [rho, smul_eq_mul]
    apply finsum_eq_sum_of_support_subset
    intro q hq
    change rho q (c s) * smoothBoundaryLocalSignedCoordinate D q (c s) ≠ 0 at hq
    have hqrho : rho q (c s) ≠ 0 := by
      intro hzero
      exact hq (by rw [hzero, zero_mul])
    have hqfin : q ∈ rho.finsupport (c s) := by
      simpa only [rho.mem_finsupport, mem_support] using hqrho
    exact hs hqfin
  let bderiv : frontier D.carrier → ℝ := fun q =>
    deriv (fun s : ℝ =>
      smoothBoundaryLocalSignedCoordinate D q (c s)) 0
  have hbderiv_pos : ∀ q ∈ S, 0 < bderiv q := by
    intro q hq
    have hx_tsupport : x ∈ tsupport (rho q) :=
      (rho.mem_fintsupport_iff x q).mp hq
    have hxqBall : x ∈ smoothBoundaryProductBallSource D q :=
      hrho q hx_tsupport
    let Cq := smoothBoundaryProductChartAt D q
    let Tq := JJMath.Manifold.PartialDiffeomorph.trans
      Cp.coordinate.symm Cq.coordinate
    have htransition :=
      smoothBoundaryProductChart_transition_first_deriv_pos D p q
        hxfrontier hxp hxqBall.1
    simpa only [bderiv, c, smoothBoundaryLocalSignedCoordinate,
      Cp, Cq, Tq] using htransition
  have hterm : ∀ q ∈ S,
      HasDerivAt
        (fun s : ℝ => rho q (c s) *
          smoothBoundaryLocalSignedCoordinate D q (c s))
        (rho q x * bderiv q) 0 := by
    intro q hq
    let a : ℝ → ℝ := fun s => rho q (c s)
    let b : ℝ → ℝ := fun s => smoothBoundaryLocalSignedCoordinate D q (c s)
    have ha_smooth : ContDiffAt ℝ 2 a 0 := by
      have hcomp : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ) 2 a 0 :=
        ((rho q).contMDiff.of_le (by
          exact WithTop.coe_le_coe.2 le_top)).contMDiffAt.comp 0 hc_smooth
      exact hcomp.contDiffAt
    have ha : HasDerivAt a (deriv a 0) 0 :=
      (ha_smooth.differentiableAt (by norm_num)).hasDerivAt
    have hbpos : 0 < deriv b 0 := by
      exact hbderiv_pos q hq
    have hb : HasDerivAt b (deriv b 0) 0 :=
      (differentiableAt_of_deriv_ne_zero hbpos.ne').hasDerivAt
    have hbzero : b 0 = 0 := by
      rw [show b 0 = smoothBoundaryLocalSignedCoordinate D q x by
        simp only [b, hc0]]
      have hx_tsupport : x ∈ tsupport (rho q) :=
        (rho.mem_fintsupport_iff x q).mp hq
      have hxqBall : x ∈ smoothBoundaryProductBallSource D q :=
        hrho q hx_tsupport
      exact (smoothBoundaryProductChartAt D q).frontier_iff_zero x
        hxqBall.1 |>.mp hxfrontier
    have ha0 : a 0 = rho q x := by simp only [a, hc0]
    convert ha.mul hb using 1
    all_goals simp [a, b, hbzero, ha0, bderiv]
  have hsum : HasDerivAt
      (fun s : ℝ => ∑ q ∈ S,
        rho q (c s) * smoothBoundaryLocalSignedCoordinate D q (c s))
      (∑ q ∈ S, rho q x * bderiv q) 0 := by
    convert (HasDerivAt.sum fun q hq => hterm q hq) using 1
    funext s
    simp
  have hsum_pos : 0 < ∑ q ∈ S, rho q x * bderiv q := by
    apply Finset.sum_pos'
    · intro q hq
      exact mul_nonneg (rho.nonneg q x) (hbderiv_pos q hq).le
    · refine ⟨p, ?_, mul_pos hp ?_⟩
      · apply rho.finsupport_subset_fintsupport
        simpa only [rho.mem_finsupport, mem_support] using hp.ne'
      · apply hbderiv_pos
        apply rho.finsupport_subset_fintsupport
        simpa only [rho.mem_finsupport, mem_support] using hp.ne'
  have hglobal : HasDerivAt
      (fun s : ℝ => smoothBoundaryGlobalSignedCoordinate D (c s))
      (∑ q ∈ S, rho q x * bderiv q) 0 :=
    hsum.congr_of_eventuallyEq hfinite_eq
  rw [hglobal.deriv]
  exact hsum_pos

/--
%%handwave
name:
  Nonvanishing differential of the global signed coordinate
statement:
  For every \(x\in\partial D\), the global signed coordinate
  \(s=\sum_p\rho_p s_p\) satisfies
  \[
    ds_x\neq0.
  \]
proof:
  Choose an active boundary chart at \(x\) and differentiate in its positive
  transverse direction.  Terms involving derivatives of the weights vanish
  because every \(s_p(x)=0\); the remaining terms are nonnegative weighted
  transverse derivatives, and at least one weight and derivative are strictly
  positive.  Thus the directional derivative of \(s\) is positive.
-/
theorem smoothBoundaryGlobalSignedCoordinate_mfderiv_ne_zero
    (D : SmoothBoundaryDomain X) {x : X}
    (hxfrontier : x ∈ frontier D.carrier) :
    mfderiv SurfaceRealModel 𝓘(ℝ)
      (smoothBoundaryGlobalSignedCoordinate D) x ≠ 0 := by
  intro hzero
  obtain ⟨p, hxp, hp⟩ :=
    exists_smoothBoundaryGlobalSignedCoordinate_productChart_deriv_pos
      D hxfrontier
  let Cp := smoothBoundaryProductChartAt D p
  let z := Cp.coordinate x
  let c : ℝ → X := fun s => Cp.coordinate.symm (z + (s, 0))
  have hzTarget : z ∈ Cp.coordinate.target := Cp.coordinate.map_source hxp
  have hc0 : c 0 = x := by
    change Cp.coordinate.symm (z + (0, 0)) = x
    have hzadd : z + (0, 0) = z := by ext <;> simp
    rw [hzadd]
    exact Cp.coordinate.left_inv hxp
  have hline : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, ℝ × ℝ) 2
      (fun s : ℝ => z + (s, 0)) 0 := by
    exact (by fun_prop : ContDiffAt ℝ 2
      (fun s : ℝ => z + (s, 0)) 0).contMDiffAt
  have hc_smooth : ContMDiffAt 𝓘(ℝ) SurfaceRealModel 2 c 0 := by
    have hsymm : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) SurfaceRealModel 2
        Cp.coordinate.symm z :=
      (Cp.coordinate.contMDiffOn_invFun.contMDiffAt
        (Cp.coordinate.open_target.mem_nhds hzTarget)).of_le
          (by exact WithTop.coe_le_coe.mpr le_top)
    have hcomp := hsymm.comp_of_eq hline (by
      ext <;> simp)
    simpa only [c, Function.comp_def] using hcomp
  have hc_mdiff : MDifferentiableAt 𝓘(ℝ) SurfaceRealModel c 0 :=
    hc_smooth.mdifferentiableAt (by norm_num)
  have hg_mdiff : MDifferentiableAt SurfaceRealModel 𝓘(ℝ)
      (smoothBoundaryGlobalSignedCoordinate D) x :=
    (smoothBoundaryGlobalSignedCoordinate_contMDiff D).contMDiffAt
      |>.mdifferentiableAt (by norm_num)
  have hg_zero : HasMFDerivAt SurfaceRealModel 𝓘(ℝ)
      (smoothBoundaryGlobalSignedCoordinate D) x 0 := by
    convert hg_mdiff.hasMFDerivAt using 1
    exact hzero.symm
  have hg_zero_at_c : HasMFDerivAt SurfaceRealModel 𝓘(ℝ)
      (smoothBoundaryGlobalSignedCoordinate D) (c 0) 0 := by
    rw [hc0]
    exact hg_zero
  have hcomp_zero : HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ)
      (smoothBoundaryGlobalSignedCoordinate D ∘ c) 0 0 := by
    simpa using hg_zero_at_c.comp 0 hc_mdiff.hasMFDerivAt
  have hderiv_zero : deriv
      (fun s : ℝ => smoothBoundaryGlobalSignedCoordinate D (c s)) 0 = 0 := by
    have hordinary : HasFDerivAt
        (smoothBoundaryGlobalSignedCoordinate D ∘ c) 0 0 :=
      hcomp_zero.hasFDerivAt
    change fderiv ℝ (smoothBoundaryGlobalSignedCoordinate D ∘ c) 0 1 = 0
    rw [fderiv, fderivWithin]
    split_ifs with h
    · rfl
    all_goals exact (h (hordinary.hasFDerivWithinAt (s := Set.univ))).elim
  have hp' : 0 < deriv
      (fun s : ℝ => smoothBoundaryGlobalSignedCoordinate D (c s)) 0 := by
    simpa only [Cp, z, c] using hp
  rw [hderiv_zero] at hp'
  exact (lt_irrefl 0) hp'

end

end JJMath.Uniformization
