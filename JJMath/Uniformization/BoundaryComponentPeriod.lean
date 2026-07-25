import JJMath.Uniformization.SignedBoundaryNeighborhood

/-!
# Period forms around smooth boundary components

This file constructs the smooth transition data needed for Hubbard's period
argument.  It does not identify a boundary component with a circle.  Instead,
a continuous signed coordinate isolates a compact transition core, while a
smooth Urysohn function supplies the local primitive whose differential will
be extended by zero.
-/

open Set
open scoped Manifold ContDiff Topology

namespace JJMath
namespace Uniformization

noncomputable section

open JJMath.Manifold

/-- The transition data around one connected component of a smooth frontier. -/
structure BoundaryComponentTransition
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X]
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) where
  /-- A precompact signed neighborhood of the component. -/
  signed : SignedFrontierComponentNeighborhood D p
  /-- A smaller open band around the component. -/
  band : TopologicalSpace.Opens X
  /-- The chosen component lies in the band. -/
  component_subset : frontierComponentCarrier D.carrier p ⊆ band
  /-- The band has compact closure. -/
  compact_closure : IsCompact (closure (band : Set X))
  /-- The closed band remains inside the signed neighborhood. -/
  closure_subset_signed : closure (band : Set X) ⊆ signed.neighborhood
  /-- Half-width of the transition strip. -/
  epsilon : ℝ
  /-- The half-width is positive. -/
  epsilon_pos : 0 < epsilon
  /-- The coordinate is uniformly outside the transition strip at the band frontier. -/
  frontier_gap : ∀ x ∈ frontier (band : Set X),
    2 * epsilon ≤ |signed.coordinate x|
  /-- A smooth local primitive changing from zero to one across the component. -/
  step : C^∞⟮SurfaceRealModel, band; ℝ⟯
  /-- The primitive is zero on the negative strip. -/
  step_eq_zero : ∀ x : band,
    signed.coordinate x ≤ -epsilon → step x = 0
  /-- The primitive is one on the positive strip. -/
  step_eq_one : ∀ x : band,
    epsilon ≤ signed.coordinate x → step x = 1

/--
%%handwave
name:
  Smooth transition data around a boundary component
statement:
  On a noncompact Riemann surface, every connected component of the
  boundary of a smooth relatively compact domain admits a precompact open band,
  a positive transition width, and a smooth function which is zero on the
  negative side and one on the positive side; the function is locally constant
  near the frontier of the band.
proof:
  First glue the local signed defining coordinates by a normalized partition
  of unity.  Shrink around their compact zero component so that the absolute
  value of the signed coordinate has a positive lower bound on the new
  frontier.  Smooth Urysohn separation of the two closed sign strips gives the
  desired function.
-/
theorem exists_boundaryComponentTransition
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    (hnoncompact : ¬ CompactSpace X)
    (D : SmoothBoundaryDomain X) (p : frontier D.carrier) :
    Nonempty (BoundaryComponentTransition D p) := by
  classical
  rcases exists_signedFrontierComponentNeighborhood D p with ⟨S⟩
  rcases S.exists_band_gap hnoncompact with
    ⟨V, hVopen, hcomponent, hclosure, hcompact, ε, hε, hgap⟩
  let U : TopologicalSpace.Opens X := ⟨V, hVopen⟩
  have hUN : (U : Set X) ⊆ S.neighborhood :=
    subset_closure.trans hclosure
  rcases S.exists_smoothStep_on_open U hUN hε with
    ⟨f, hfzero, hfone⟩
  exact ⟨{
    signed := S
    band := U
    component_subset := hcomponent
    compact_closure := hcompact
    closure_subset_signed := hclosure
    epsilon := ε
    epsilon_pos := hε
    frontier_gap := hgap
    step := f
    step_eq_zero := hfzero
    step_eq_one := hfone }⟩

/--
%%handwave
name: The compact middle of a boundary-component transition band
statement:
  For a signed boundary coordinate $s$ on a transition band $B$ and
  $\varepsilon>0$, define the middle core
  $K=\{x\in\overline B:|s(x)|\le\varepsilon\}$.
-/
def BoundaryComponentTransition.core
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X]
    {D : SmoothBoundaryDomain X} {p : frontier D.carrier}
    (T : BoundaryComponentTransition D p) : Set X :=
  {x | x ∈ closure (T.band : Set X) ∧
    |T.signed.coordinate x| ≤ T.epsilon}

/--
%%handwave
name:
  Compactness of the middle boundary-transition strip
statement:
  The set of points in the closed transition band where the absolute signed
  boundary coordinate is at most \(\varepsilon\) is compact.
proof:
  On the compact closure of the band, the absolute signed coordinate is
  continuous.  Its sublevel set \(( -\infty,\varepsilon]\) is closed there,
  hence compact, and its image in the ambient surface is the transition core.
-/
theorem BoundaryComponentTransition.core_isCompact
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    {D : SmoothBoundaryDomain X} {p : frontier D.carrier}
    (T : BoundaryComponentTransition D p) :
    IsCompact T.core := by
  let K : Set (closure (T.band : Set X)) :=
    {x | |T.signed.coordinate (x : X)| ≤ T.epsilon}
  have hcoord : Continuous
      (fun x : closure (T.band : Set X) => |T.signed.coordinate (x : X)|) := by
    exact (T.signed.coordinate_continuous.comp_continuous
      continuous_subtype_val (fun x => T.closure_subset_signed x.2)).abs
  have hKclosed : IsClosed K := isClosed_le hcoord continuous_const
  letI : CompactSpace (closure (T.band : Set X)) :=
    isCompact_iff_compactSpace.mp T.compact_closure
  have hKcompact : IsCompact K := hKclosed.isCompact
  have himage : ((fun x : closure (T.band : Set X) => (x : X)) '' K) = T.core := by
    ext x
    constructor
    · rintro ⟨z, hzK, rfl⟩
      change |T.signed.coordinate (z : X)| ≤ T.epsilon at hzK
      exact ⟨z.2, hzK⟩
    · intro hx
      exact ⟨⟨x, hx.1⟩, hx.2, rfl⟩
  rw [← himage]
  exact hKcompact.image continuous_subtype_val

/--
%%handwave
name:
  The compact transition core lies inside its open band
statement:
  Every point of the closed band with signed-coordinate magnitude at most
  \(\varepsilon\) actually belongs to the open transition band.
proof:
  Otherwise it would lie on the frontier of the open band, where the frontier
  gap gives absolute coordinate at least \(2\varepsilon\), contradicting the
  core bound and \(\varepsilon>0\).
-/
theorem BoundaryComponentTransition.core_subset_band
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    {D : SmoothBoundaryDomain X} {p : frontier D.carrier}
    (T : BoundaryComponentTransition D p) :
    T.core ⊆ (T.band : Set X) := by
  intro x hxcore
  by_contra hxband
  have hxfrontier : x ∈ frontier (T.band : Set X) := by
    rw [frontier, T.band.isOpen.interior_eq]
    exact ⟨hxcore.1, hxband⟩
  have hgap := T.frontier_gap x hxfrontier
  have hcorele := hxcore.2
  linarith [T.epsilon_pos]

/--
%%handwave
name: The local one-form is the differential of the smooth step on the band
statement:
  On the transition band $B$, define the local one-form $d\chi$, where
  $\chi$ is the smooth step from the domain side to the chosen complementary
  side.
-/
noncomputable def BoundaryComponentTransition.localOneForm
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X]
    {D : SmoothBoundaryDomain X} {p : frontier D.carrier}
    (T : BoundaryComponentTransition D p) :
    SmoothForms (I := SurfaceRealModel) (M := T.band) ℝ 1 :=
  deRhamDifferential (I := SurfaceRealModel) (M := T.band) (A := ℝ) 0
    (smoothRealFunctionToZeroForm (I0 := SurfaceRealModel) T.step)

/--
%%handwave
name:
  Closedness of the local boundary-transition form
statement:
  The one-form \(dh\) defined by the smooth transition step on the band is
  closed.
proof:
  Apply \(d^2=0\) to the zero-form defined by \(h\).
-/
theorem BoundaryComponentTransition.localOneForm_closed
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    {D : SmoothBoundaryDomain X} {p : frontier D.carrier}
    (T : BoundaryComponentTransition D p) :
    deRhamDifferential (I := SurfaceRealModel) (M := T.band) (A := ℝ) 1
      T.localOneForm = 0 := by
  exact deRhamDifferential_comp_eq_zero
    (I := SurfaceRealModel) (M := T.band) (A := ℝ)
    (smoothRealFunctionToZeroForm (I0 := SurfaceRealModel) T.step)

/--
%%handwave
name:
  Vanishing of the transition form outside its compact core
statement:
  At every band point outside the compact middle core, the local one-form
  \(dh\) vanishes.
proof:
  Outside the core the signed coordinate is either below
  \(-\varepsilon\) or above \(\varepsilon\).  By continuity the same strict
  inequality holds nearby, where the step is constantly \(0\) or constantly
  \(1\).  Its differential therefore vanishes at the point.
-/
theorem BoundaryComponentTransition.localOneForm_toFun_eq_zero_of_not_mem_core
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    {D : SmoothBoundaryDomain X} {p : frontier D.carrier}
    (T : BoundaryComponentTransition D p)
    (x : T.band) (hxcore : (x : X) ∉ T.core) :
    T.localOneForm.toFun x = 0 := by
  have hxclosure : (x : X) ∈ closure (T.band : Set X) :=
    subset_closure x.2
  have habs : T.epsilon < |T.signed.coordinate (x : X)| := by
    exact lt_of_not_ge (fun hle => hxcore ⟨hxclosure, hle⟩)
  have hcoord_continuous : Continuous
      (fun q : T.band => T.signed.coordinate (q : X)) := by
    exact T.signed.coordinate_continuous.comp_continuous
      continuous_subtype_val
      (fun q => T.closure_subset_signed (subset_closure q.2))
  have hside :
      T.signed.coordinate (x : X) < -T.epsilon ∨
        T.epsilon < T.signed.coordinate (x : X) := by
    by_cases hxnonneg : 0 ≤ T.signed.coordinate (x : X)
    · right
      rw [abs_of_nonneg hxnonneg] at habs
      exact habs
    · left
      have hxnonpos : T.signed.coordinate (x : X) ≤ 0 := le_of_not_ge hxnonneg
      rw [abs_of_nonpos hxnonpos] at habs
      linarith
  rcases hside with hnegative | hpositive
  · have hlocal : ∀ᶠ q in 𝓝 x,
        (smoothRealFunctionToZeroForm (I0 := SurfaceRealModel) T.step).toFun q =
          (smoothRealFunctionToZeroForm (I0 := SurfaceRealModel)
            (smoothRealConstantFunction (I0 := SurfaceRealModel) 0)).toFun q := by
      filter_upwards
        [(isOpen_lt hcoord_continuous continuous_const).mem_nhds hnegative] with q hq
      simp [smoothRealFunctionToZeroForm, T.step_eq_zero q hq.le]
    change
      (deRhamDifferential (I := SurfaceRealModel) (M := T.band) (A := ℝ) 0
        (smoothRealFunctionToZeroForm (I0 := SurfaceRealModel) T.step)).toFun x = 0
    rw [deRhamDifferential_toFun_eq_of_eventuallyEq
      (I := SurfaceRealModel)
      (smoothRealFunctionToZeroForm (I0 := SurfaceRealModel) T.step)
      (smoothRealFunctionToZeroForm (I0 := SurfaceRealModel)
        (smoothRealConstantFunction (I0 := SurfaceRealModel) 0)) hlocal]
    rw [deRhamDifferential_smoothRealFunctionToZeroForm_const]
    rfl
  · have hlocal : ∀ᶠ q in 𝓝 x,
        (smoothRealFunctionToZeroForm (I0 := SurfaceRealModel) T.step).toFun q =
          (smoothRealFunctionToZeroForm (I0 := SurfaceRealModel)
            (smoothRealConstantFunction (I0 := SurfaceRealModel) 1)).toFun q := by
      filter_upwards
        [(isOpen_lt continuous_const hcoord_continuous).mem_nhds hpositive] with q hq
      simp [smoothRealFunctionToZeroForm, T.step_eq_one q hq.le]
    change
      (deRhamDifferential (I := SurfaceRealModel) (M := T.band) (A := ℝ) 0
        (smoothRealFunctionToZeroForm (I0 := SurfaceRealModel) T.step)).toFun x = 0
    rw [deRhamDifferential_toFun_eq_of_eventuallyEq
      (I := SurfaceRealModel)
      (smoothRealFunctionToZeroForm (I0 := SurfaceRealModel) T.step)
      (smoothRealFunctionToZeroForm (I0 := SurfaceRealModel)
        (smoothRealConstantFunction (I0 := SurfaceRealModel) 1)) hlocal]
    rw [deRhamDifferential_smoothRealFunctionToZeroForm_const]
    rfl

/--
%%handwave
name: The open complement of the compact middle transition strip
statement:
  Define the exterior open set $X\setminus K$, where $K$ is the compact
  middle core of the boundary transition band.
-/
noncomputable def BoundaryComponentTransition.exteriorOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    {D : SmoothBoundaryDomain X} {p : frontier D.carrier}
    (T : BoundaryComponentTransition D p) : TopologicalSpace.Opens X :=
  ⟨T.coreᶜ, T.core_isCompact.isClosed.isOpen_compl⟩

/--
%%handwave
name:
  The transition band and core exterior cover the surface
statement:
  The union of the open transition band with the complement of its compact
  middle core is the whole surface.
proof:
  A point in the core lies in the band; a point outside the core lies in its
  open complement.
-/
theorem BoundaryComponentTransition.band_sup_exteriorOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    {D : SmoothBoundaryDomain X} {p : frontier D.carrier}
    (T : BoundaryComponentTransition D p) :
    T.band ⊔ T.exteriorOpen = ⊤ := by
  ext x
  change (x ∈ (T.band : Set X) ∨ x ∈ T.coreᶜ) ↔ True
  rw [iff_true]
  by_cases hxcore : x ∈ T.core
  · exact Or.inl (T.core_subset_band hxcore)
  · exact Or.inr hxcore

/--
%%handwave
name:
  The local transition form vanishes on the band--exterior overlap
statement:
  Restricting \(dh\) to the part of the transition band outside the compact
  core gives the zero one-form.
proof:
  Pointwise on this overlap, the local transition form vanishes outside the
  core.  Evaluate the restricted form and use that pointwise identity.
-/
theorem BoundaryComponentTransition.localOneForm_overlap_eq_zero
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    {D : SmoothBoundaryDomain X} {p : frontier D.carrier}
    (T : BoundaryComponentTransition D p) :
    restrictSmoothFormsOfLE (I := SurfaceRealModel) (A := ℝ)
        (W := (T.band ⊓ T.exteriorOpen : TopologicalSpace.Opens X))
        (V := T.band) inf_le_left 1 T.localOneForm = 0 := by
  apply DifferentialForm.ext
  intro x
  ext v
  let xU : T.band := TopologicalSpace.Opens.inclusion inf_le_left x
  have hxcore : (xU : X) ∉ T.core := x.2.2
  have hzero := T.localOneForm_toFun_eq_zero_of_not_mem_core xU hxcore
  simp only [restrictSmoothFormsOfLE]
  change T.localOneForm.toFun xU (_ ∘ v) = 0
  rw [hzero]
  rfl

/--
%%handwave
name:
  Mayer--Vietoris compatibility of the local transition form and zero
statement:
  For the cover by the transition band and the exterior of its core, the
  Mayer--Vietoris difference of \(dh\) on the band and \(0\) on the exterior
  is zero.
proof:
  The exterior restriction of zero is zero, and the band restriction of
  \(dh\) is zero on the overlap by the preceding vanishing theorem.
-/
theorem BoundaryComponentTransition.localOneForm_mayerVietorisDifference_eq_zero
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    {D : SmoothBoundaryDomain X} {p : frontier D.carrier}
    (T : BoundaryComponentTransition D p) :
    deRhamMayerVietorisSmoothDifference (I := SurfaceRealModel) (A := ℝ)
      T.band T.exteriorOpen 1 (T.localOneForm, 0) = 0 := by
  rw [deRhamMayerVietorisSmoothDifference]
  simp only [map_zero, sub_zero]
  exact T.localOneForm_overlap_eq_zero

/--
%%handwave
name: The compactly supported global one-form associated with a boundary component
statement:
  Glue $d\chi$ on the transition band to the zero one-form on
  $X\setminus K$, obtaining a global one-form supported in the compact
  middle core $K$.
-/
noncomputable def BoundaryComponentTransition.globalOneForm
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    {D : SmoothBoundaryDomain X} {p : frontier D.carrier}
    (T : BoundaryComponentTransition D p) :
    SmoothForms (I := SurfaceRealModel) (M := X) ℝ 1 :=
  smoothFormsTwoOpenGlue (I := SurfaceRealModel) (A := ℝ)
    T.band T.exteriorOpen T.band_sup_exteriorOpen
    T.localOneForm 0 T.localOneForm_mayerVietorisDifference_eq_zero

/--
%%handwave
name:
  Closedness of the global boundary-component form
statement:
  The one-form \(\omega_B\) obtained by gluing the exact transition form
  \(dh\) on the boundary band to \(0\) outside its compact core satisfies
  \[
    d\omega_B=0
  \]
  on the entire surface.
proof:
  Restriction to the transition band is \(dh\), hence has derivative
  \(d^2h=0\); restriction to the exterior region is zero.  Since these two
  open sets cover the surface, the global exterior derivative vanishes.
-/
theorem BoundaryComponentTransition.globalOneForm_closed
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    {D : SmoothBoundaryDomain X} {p : frontier D.carrier}
    (T : BoundaryComponentTransition D p) :
    deRhamDifferential (I := SurfaceRealModel) (M := X) (A := ℝ) 1
      T.globalOneForm = 0 := by
  apply smoothForms_eq_zero_of_restrictions_eq_zero
    (I := SurfaceRealModel) (A := ℝ)
    T.band T.exteriorOpen T.band_sup_exteriorOpen 2
  · rw [← deRhamDifferential_restrictSmoothFormsToOpen,
      BoundaryComponentTransition.globalOneForm,
      restrictSmoothFormsToOpen_smoothFormsTwoOpenGlue_left,
      T.localOneForm_closed]
  · rw [← deRhamDifferential_restrictSmoothFormsToOpen,
      BoundaryComponentTransition.globalOneForm,
      restrictSmoothFormsToOpen_smoothFormsTwoOpenGlue_right]
    exact LinearMap.map_zero _

/--
%%handwave
name:
  Restriction of the global boundary-component form to the band
statement:
  The global one-form obtained by gluing equals the local exact form \(dh\)
  when restricted to the transition band.
proof:
  This is the left restriction identity for the two-open gluing construction.
-/
theorem BoundaryComponentTransition.globalOneForm_restrict_band
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    {D : SmoothBoundaryDomain X} {p : frontier D.carrier}
    (T : BoundaryComponentTransition D p) :
    restrictSmoothFormsToOpen (I := SurfaceRealModel) (A := ℝ) T.band 1
        T.globalOneForm = T.localOneForm := by
  rw [BoundaryComponentTransition.globalOneForm,
    restrictSmoothFormsToOpen_smoothFormsTwoOpenGlue_left]

/--
%%handwave
name:
  Restriction of the global boundary-component form outside the core
statement:
  The global boundary-component one-form restricts to zero on the open
  complement of its compact transition core.
proof:
  This is the right restriction identity for the gluing of \(dh\) with the
  zero form.
-/
theorem BoundaryComponentTransition.globalOneForm_restrict_exterior
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    {D : SmoothBoundaryDomain X} {p : frontier D.carrier}
    (T : BoundaryComponentTransition D p) :
    restrictSmoothFormsToOpen (I := SurfaceRealModel) (A := ℝ)
        T.exteriorOpen 1 T.globalOneForm = 0 := by
  rw [BoundaryComponentTransition.globalOneForm,
    restrictSmoothFormsToOpen_smoothFormsTwoOpenGlue_right]

/--
%%handwave
name: The global closed form represented by the boundary-component transition
statement:
  Regard the compactly supported global transition form, equal to $d\chi$
  on the band and zero away from its middle core, as a closed real one-form
  on $X$.
-/
noncomputable def BoundaryComponentTransition.closedOneForm
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    {D : SmoothBoundaryDomain X} {p : frontier D.carrier}
    (T : BoundaryComponentTransition D p) :
    DeRhamClosedForms (I := SurfaceRealModel) (M := X) (A := ℝ) 1 :=
  ⟨T.globalOneForm, T.globalOneForm_closed⟩

end
end Uniformization
end JJMath
