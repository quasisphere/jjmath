import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Topology.MetricSpace.Equicontinuity
import JJMath.Uniformization.Subharmonic

/-!
# Perron method for the Dirichlet problem on Riemann surfaces

This file contains the Perron envelope construction and the Dirichlet problem
statements.  Harmonic, subharmonic, and superharmonic background is kept in
`JJMath.Uniformization.Subharmonic`.
-/

namespace JJMath

open scoped Manifold Topology ContDiff

namespace Uniformization

/--
%%handwave
name:
  Perron open region
statement:
  A Perron open region is a nonempty open subset of a Riemann surface.
  Unlike a Perron domain, it is not required to have compact closure.
-/
structure PerronOpen (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] where
  /-- The underlying open subset. -/
  carrier : Set X
  /-- The region is open. -/
  isOpen : IsOpen carrier
  /-- The region is nonempty. -/
  nonempty : carrier.Nonempty

namespace PerronOpen

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- The boundary of a Perron open region. -/
def boundary (Ω : PerronOpen X) : Set X :=
  frontier Ω.carrier

/--
%%handwave
name:
  The boundary of an open Perron region is disjoint from the region
statement:
  If \(\Omega\) is a Perron open region and
  \(x\in\partial\Omega\), then \(x\notin\Omega\).
proof:
  An open set is disjoint from its frontier.
-/
theorem not_mem_carrier_of_mem_boundary
    (Ω : PerronOpen X) {x : X} (hx : x ∈ Ω.boundary) :
    x ∉ Ω.carrier := by
  intro hxΩ
  have hx_inter : x ∈ Ω.carrier ∩ frontier Ω.carrier := ⟨hxΩ, hx⟩
  simp [Ω.isOpen.inter_frontier_eq] at hx_inter

end PerronOpen

/--
%%handwave
name:
  Boundary data on a Perron open region
statement:
  Boundary data on a Perron open region is a real-valued function, represented
  on the ambient surface, that is continuous along the frontier of the region.
-/
structure PerronOpenBoundaryData {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronOpen X) where
  /-- The prescribed boundary value, represented by an ambient function. -/
  toFun : X → ℝ
  /-- The prescribed value is continuous along the boundary. -/
  continuous_boundary : ContinuousOn toFun Ω.boundary

namespace PerronOpenBoundaryData

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {Ω : PerronOpen X}

instance : CoeFun (PerronOpenBoundaryData Ω) (fun _ ↦ X → ℝ) where
  coe φ := φ.toFun

end PerronOpenBoundaryData

/--
%%handwave
name:
  Perron-open boundary data is eventually below a positive upper margin
statement:
  Along the boundary of a Perron-open region, continuous boundary data is
  eventually less than \(\varphi(p)+\varepsilon\) at a boundary point \(p\).
proof:
  Continuity of $\varphi$ along the boundary gives
  $\varphi(x)\to\varphi(p)$ as $x\to p$ within $\partial\Omega$. The open
  upper interval $(-\infty,\varphi(p)+\varepsilon)$ therefore contains all
  sufficiently near boundary values.
-/
theorem perronOpenBoundaryData_eventually_lt_boundary_add
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {Ω : PerronOpen X} (φ : PerronOpenBoundaryData Ω)
    {p : X} (hp : p ∈ Ω.boundary) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in 𝓝[Ω.boundary] p, φ x < φ p + ε := by
  exact (tendsto_order.mp (φ.continuous_boundary p hp)).2
    (φ p + ε) (by linarith)

/--
%%handwave
name:
  Perron-open boundary data is eventually above a positive lower margin
statement:
  Along the boundary of a Perron-open region, continuous boundary data is
  eventually greater than \(\varphi(p)-\varepsilon\) at a boundary point \(p\).
proof:
  Continuity of $\varphi$ along $\partial\Omega$ gives
  $\varphi(x)\to\varphi(p)$ within the boundary. Hence sufficiently near
  $p$ one has $\varphi(x)>\varphi(p)-\varepsilon$.
-/
theorem perronOpenBoundaryData_eventually_gt_boundary_sub
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {Ω : PerronOpen X} (φ : PerronOpenBoundaryData Ω)
    {p : X} (hp : p ∈ Ω.boundary) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in 𝓝[Ω.boundary] p, φ p - ε < φ x := by
  exact (tendsto_order.mp (φ.continuous_boundary p hp)).1
    (φ p - ε) (by linarith)

/--
%%handwave
name:
  Local barrier for a Perron open region
statement:
  A local Perron barrier at a boundary point of an open region is a
  superharmonic function on a neighborhood of the boundary point inside the
  region, continuous up to the local closed region, vanishing at the marked
  boundary point and positive at every other nearby closed-region point.
-/
def HasLocalPerronOpenBarrierAt {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronOpen X) (p : X) : Prop :=
  p ∈ Ω.boundary ∧
    ∃ N : Set X, IsOpen N ∧ p ∈ N ∧
      ∃ b : X → ℝ,
        ContinuousOn b (closure Ω.carrier ∩ N) ∧
          IsSuperharmonicOnSurface (Ω.carrier ∩ N) b ∧
            b p = 0 ∧
              ∀ x ∈ closure Ω.carrier ∩ N, x ≠ p → 0 < b x

/--
%%handwave
name:
  Local Perron-open barriers have positive compact floors
statement:
  A local Perron-open barrier that is positive away from its marked boundary
  point has a uniform positive lower bound on every compact subset of the
  local closed region that avoids the marked point.
proof:
  If the compact set is empty, any positive constant works.  Otherwise the
  barrier attains its minimum on the compact set, and the pointwise positivity
  assumption makes that minimum positive.
-/
theorem localPerronOpenBarrier_positive_floor_on_compact
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronOpen X) {p : X} {N K : Set X} {b : X → ℝ}
    (hb_cont : ContinuousOn b (closure Ω.carrier ∩ N))
    (hb_pos : ∀ x ∈ closure Ω.carrier ∩ N, x ≠ p → 0 < b x)
    (hK_compact : IsCompact K)
    (hK_subset : K ⊆ closure Ω.carrier ∩ N)
    (hp_not_mem : p ∉ K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, δ ≤ b x := by
  by_cases hK_nonempty : K.Nonempty
  · have hb_cont_K : ContinuousOn b K := hb_cont.mono hK_subset
    rcases hK_compact.exists_isMinOn hK_nonempty hb_cont_K with
      ⟨x₀, hx₀K, hx₀_min⟩
    have hx₀_ne : x₀ ≠ p := by
      intro hx₀p
      exact hp_not_mem (by simpa [hx₀p] using hx₀K)
    refine ⟨b x₀, hb_pos x₀ (hK_subset hx₀K) hx₀_ne, ?_⟩
    intro x hxK
    exact hx₀_min hxK
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x hxK
    exact False.elim (hK_nonempty ⟨x, hxK⟩)

/--
%%handwave
name:
  Local Perron-open barriers have positive floors on shrink frontiers
statement:
  If an open neighborhood of the marked boundary point has compact closure
  contained in the local-barrier neighborhood, then the barrier has a uniform
  positive lower bound on the part of the shrink frontier lying in the closed
  Perron-open region.
proof:
  The relevant frontier is compact because it is a closed subset of the
  compact closure of the shrink, and it avoids the marked point because the
  shrink is open and contains that point.  Apply
  [the compact-floor lemma](lean:JJMath.Uniformization.localPerronOpenBarrier_positive_floor_on_compact).
-/
theorem localPerronOpenBarrier_positive_floor_on_frontier
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronOpen X) {p : X} {N V : Set X} {b : X → ℝ}
    (hb_cont : ContinuousOn b (closure Ω.carrier ∩ N))
    (hb_pos : ∀ x ∈ closure Ω.carrier ∩ N, x ≠ p → 0 < b x)
    (hV_open : IsOpen V) (hpV : p ∈ V)
    (hV_compact : IsCompact (closure V))
    (hV_closure_subset : closure V ⊆ N) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ closure Ω.carrier ∩ frontier V, δ ≤ b x := by
  let K : Set X := closure Ω.carrier ∩ frontier V
  have hfrontier_compact : IsCompact (frontier V) :=
    hV_compact.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hK_compact : IsCompact K := by
    simpa [K, Set.inter_comm] using hfrontier_compact.inter_right isClosed_closure
  have hK_subset : K ⊆ closure Ω.carrier ∩ N := by
    intro x hx
    exact ⟨hx.1, hV_closure_subset (frontier_subset_closure hx.2)⟩
  have hp_not_mem : p ∉ K := by
    intro hpK
    have hp_inter : p ∈ V ∩ frontier V := ⟨hpV, hpK.2⟩
    rw [hV_open.inter_frontier_eq] at hp_inter
    exact hp_inter
  exact localPerronOpenBarrier_positive_floor_on_compact Ω hb_cont hb_pos
    hK_compact hK_subset hp_not_mem

/--
%%handwave
name:
  Local Perron-open barriers tend to zero at the marked point
statement:
  A local Perron-open barrier that is continuous on the local closed region
  and vanishes at the marked boundary point tends to zero along the open
  region.
proof:
  Continuity gives convergence along the local closed region.  Since the
  barrier neighborhood is an ambient neighborhood of the marked point, the
  filter of the open region near the point is unchanged by intersecting with
  that neighborhood.
-/
theorem localPerronOpenBarrier_tendsto_zero
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronOpen X) {p : X} {N : Set X} {b : X → ℝ}
    (hN_open : IsOpen N) (hpN : p ∈ N)
    (hp_closure : p ∈ closure Ω.carrier)
    (hb_cont : ContinuousOn b (closure Ω.carrier ∩ N))
    (hb_zero : b p = 0) :
    Filter.Tendsto b (𝓝[Ω.carrier] p) (𝓝 0) := by
  have hp_closedN : p ∈ closure Ω.carrier ∩ N := ⟨hp_closure, hpN⟩
  have hb_tendsto_closedN :
      Filter.Tendsto b (𝓝[closure Ω.carrier ∩ N] p) (𝓝 (b p)) :=
    hb_cont p hp_closedN
  have hΩN_subset : Ω.carrier ∩ N ⊆ closure Ω.carrier ∩ N := by
    intro x hx
    exact ⟨subset_closure hx.1, hx.2⟩
  have hb_tendsto_ΩN :
      Filter.Tendsto b (𝓝[Ω.carrier ∩ N] p) (𝓝 (b p)) :=
    tendsto_nhdsWithin_mono_left hΩN_subset hb_tendsto_closedN
  have hN_mem : N ∈ 𝓝[Ω.carrier] p :=
    mem_nhdsWithin_of_mem_nhds (hN_open.mem_nhds hpN)
  have hfilter : 𝓝[Ω.carrier ∩ N] p = 𝓝[Ω.carrier] p :=
    nhdsWithin_inter_of_mem' hN_mem
  simpa [hb_zero, hfilter] using hb_tendsto_ΩN

/--
%%handwave
name:
  Truncated local Perron-open barriers patch across a compact shrink
statement:
  A local Perron-open barrier on an open neighborhood can be truncated below
  its positive frontier floor on a compactly contained smaller neighborhood
  and extended by the truncation constant outside.  The patched function is
  continuous on the closed open-region, locally superharmonic in the region,
  vanishes at the marked point, and is positive everywhere else on the closed
  open-region.
proof:
  Use
  [the positive lower bound on the shrink frontier](lean:JJMath.Uniformization.localPerronOpenBarrier_positive_floor_on_frontier)
  and choose a smaller positive truncation constant.  On the shrink the
  patched function is the minimum of the local barrier and that constant;
  outside it is the constant.  Near the frontier, the positive floor makes the
  two descriptions agree locally, so continuity and local superharmonicity
  glue.
-/
theorem localPerronOpenBarrier_truncated_patch_from_compact_shrink
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronOpen X) {p : X} {N V : Set X} {b : X → ℝ}
    (_hN_open : IsOpen N)
    (hb_cont : ContinuousOn b (closure Ω.carrier ∩ N))
    (hb_super : IsSuperharmonicOnSurface (Ω.carrier ∩ N) b)
    (hb_zero : b p = 0)
    (hb_pos : ∀ x ∈ closure Ω.carrier ∩ N, x ≠ p → 0 < b x)
    (hV_open : IsOpen V) (hpV : p ∈ V)
    (hV_closure_subset : closure V ⊆ N)
    (hV_compact : IsCompact (closure V)) :
    ∃ B : X → ℝ,
      ContinuousOn B (closure Ω.carrier) ∧
        (∀ x ∈ Ω.carrier, ∃ M : Set X, IsOpen M ∧ x ∈ M ∧
          IsSuperharmonicOnSurface (Ω.carrier ∩ M) B) ∧
          B p = 0 ∧
            (∀ x ∈ closure Ω.carrier, x ≠ p → 0 < B x) ∧
              ∃ η : ℝ, 0 < η ∧ ∀ x : X, x ∉ V → B x = η := by
  classical
  rcases localPerronOpenBarrier_positive_floor_on_frontier Ω hb_cont hb_pos
      hV_open hpV hV_compact hV_closure_subset with
    ⟨δ, hδpos, hδ_floor⟩
  let η : ℝ := δ / 2
  let B : X → ℝ := fun x ↦ if x ∈ V then b x ⊓ η else η
  have hηpos : 0 < η := by
    dsimp [η]
    linarith
  have hηnonneg : 0 ≤ η := le_of_lt hηpos
  have hηleδ : η ≤ δ := by
    dsimp [η]
    linarith
  have hV_subset_N : V ⊆ N := by
    intro x hxV
    exact hV_closure_subset (subset_closure hxV)
  have htrunc_super_N :
      IsSuperharmonicOnSurface (Ω.carrier ∩ N) (fun x ↦ b x ⊓ η) :=
    superharmonicOnSurface_inf_const η hb_super
  refine ⟨B, ?_, ?_, ?_, ?_, ?_⟩
  · have hb_trunc_cont :
        ContinuousOn (fun x ↦ b x ⊓ η) (closure Ω.carrier ∩ closure V) := by
      have hb_closureV :
          ContinuousOn b (closure Ω.carrier ∩ closure V) :=
        hb_cont.mono (by
          intro x hx
          exact ⟨hx.1, hV_closure_subset hx.2⟩)
      exact hb_closureV.inf continuousOn_const
    have hconst_cont :
        ContinuousOn (fun _ : X ↦ η)
          (closure Ω.carrier ∩ closure {x : X | ¬ x ∈ V}) :=
      continuousOn_const
    have hfront :
        ∀ x ∈ closure Ω.carrier ∩ frontier {x : X | x ∈ V},
          (fun x ↦ b x ⊓ η) x = (fun _ : X ↦ η) x := by
      intro x hx
      have hxfront : x ∈ frontier V := by
        simpa only [Set.setOf_mem_eq] using hx.2
      have hδle : δ ≤ b x := hδ_floor x ⟨hx.1, hxfront⟩
      have hηle : η ≤ b x := le_trans hηleδ hδle
      exact inf_eq_right.mpr hηle
    simpa [B] using
      ContinuousOn.if hfront hb_trunc_cont hconst_cont
  · intro x hxΩ
    by_cases hxV : x ∈ V
    · refine ⟨V, hV_open, hxV, ?_⟩
      have htrunc_super_V :
          IsSuperharmonicOnSurface (Ω.carrier ∩ V) (fun y ↦ b y ⊓ η) :=
        superharmonicOnSurface_mono (by
          intro y hy
          exact ⟨hy.1, hV_subset_N hy.2⟩) htrunc_super_N
      exact subharmonicOnSurface_congr_on htrunc_super_V (by
        intro y hy
        dsimp [B]
        rw [if_pos hy.2])
    · by_cases hx_closureV : x ∈ closure V
      · have hxfront : x ∈ frontier V := by
          rw [frontier_eq_closure_inter_closure]
          exact ⟨hx_closureV, subset_closure hxV⟩
        have hxS : x ∈ closure Ω.carrier ∩ N := by
          exact ⟨subset_closure hxΩ, hV_closure_subset hx_closureV⟩
        have hδle : δ ≤ b x := hδ_floor x ⟨subset_closure hxΩ, hxfront⟩
        have hηlt_bx : η < b x := lt_of_lt_of_le (by dsimp [η]; linarith) hδle
        have hcontx : ContinuousWithinAt b (closure Ω.carrier ∩ N) x :=
          hb_cont.continuousWithinAt hxS
        have hpre :
            b ⁻¹' Set.Ioi η ∈ 𝓝[closure Ω.carrier ∩ N] x :=
          hcontx.preimage_mem_nhdsWithin (Ioi_mem_nhds hηlt_bx)
        rw [mem_nhdsWithin] at hpre
        rcases hpre with ⟨M, hM_open, hxM, hM_sub⟩
        refine ⟨M, hM_open, hxM, ?_⟩
        have hconst_super :
            IsSuperharmonicOnSurface (Ω.carrier ∩ M) (fun _ : X ↦ η) :=
          superharmonicOnSurface_const (Ω.carrier ∩ M) η
        exact subharmonicOnSurface_congr_on hconst_super (by
          intro y hy
          dsimp [B]
          by_cases hyV : y ∈ V
          · have hyS : y ∈ closure Ω.carrier ∩ N :=
              ⟨subset_closure hy.1, hV_subset_N hyV⟩
            have hηlt_by : η < b y :=
              hM_sub ⟨hy.2, hyS⟩
            rw [if_pos hyV]
            have hmin : b y ⊓ η = η := inf_eq_right.mpr (le_of_lt hηlt_by)
            simp [hmin]
          · rw [if_neg hyV])
      · have hx_comp : x ∈ (closure V)ᶜ := by simpa using hx_closureV
        refine ⟨(closure V)ᶜ, isOpen_compl_iff.mpr isClosed_closure, hx_comp, ?_⟩
        have hconst_super :
            IsSuperharmonicOnSurface (Ω.carrier ∩ (closure V)ᶜ)
              (fun _ : X ↦ η) :=
          superharmonicOnSurface_const (Ω.carrier ∩ (closure V)ᶜ) η
        exact subharmonicOnSurface_congr_on hconst_super (by
          intro y hy
          dsimp [B]
          have hy_not_V : y ∉ V := by
            intro hyV
            exact hy.2 (subset_closure hyV)
          rw [if_neg hy_not_V])
  · dsimp [B]
    rw [if_pos hpV, hb_zero]
    exact inf_eq_left.mpr hηnonneg
  · intro x hxcl hxp
    dsimp [B]
    by_cases hxV : x ∈ V
    · have hxN : x ∈ N := hV_subset_N hxV
      have hbpos : 0 < b x := hb_pos x ⟨hxcl, hxN⟩ hxp
      rw [if_pos hxV]
      exact lt_min hbpos hηpos
    · rw [if_neg hxV]
      exact hηpos
  · refine ⟨η, hηpos, ?_⟩
    intro x hxV
    dsimp [B]
    rw [if_neg hxV]

/--
%%handwave
name:
  Local Perron-open barriers have global superharmonic patches
statement:
  A local Perron-open barrier at a boundary point can be patched to a global
  superharmonic barrier on the open region: it is continuous on the closed
  region, superharmonic in the region, vanishes at the marked point, is
  positive elsewhere on the closed region, and tends to zero at the marked
  point along the region.
proof:
  Shrink the local barrier neighborhood to a compactly contained open set,
  apply
  [the truncated patch construction](lean:JJMath.Uniformization.localPerronOpenBarrier_truncated_patch_from_compact_shrink),
  and globalize local superharmonicity using the locality theorem for
  superharmonic functions.
-/
theorem localPerronOpenBarrierAt_exists_global_superharmonic_patch
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronOpen X) {p : X}
    (hp : HasLocalPerronOpenBarrierAt Ω p) :
    ∃ B : X → ℝ,
      ContinuousOn B (closure Ω.carrier) ∧
        IsSuperharmonicOnSurface Ω.carrier B ∧
          B p = 0 ∧
            (∀ x ∈ closure Ω.carrier, x ≠ p → 0 < B x) ∧
              Filter.Tendsto B (𝓝[Ω.carrier] p) (𝓝 0) := by
  rcases hp with
    ⟨hp_boundary, N, hN_open, hpN, b, hb_cont, hb_super, hb_zero, hb_pos⟩
  rcases exists_surface_open_nhds_isCompact_closure_subset hN_open hpN with
    ⟨V, hV_open, hpV, hV_closure_subset, hV_compact⟩
  rcases localPerronOpenBarrier_truncated_patch_from_compact_shrink Ω
      hN_open hb_cont hb_super hb_zero hb_pos
      hV_open hpV hV_closure_subset hV_compact with
    ⟨B, hB_cont, hB_local_super, hB_zero, hB_pos, _η, _hηpos, _hB_outside⟩
  have hB_super : IsSuperharmonicOnSurface Ω.carrier B :=
    superharmonicOnSurface_of_locally Ω.isOpen hB_local_super
  have hp_closure : p ∈ closure Ω.carrier := by
    exact frontier_subset_closure hp_boundary
  have hB_tendsto :
      Filter.Tendsto B (𝓝[Ω.carrier] p) (𝓝 0) := by
    have hB_tendsto_closure :
        Filter.Tendsto B (𝓝[closure Ω.carrier] p) (𝓝 (B p)) :=
      hB_cont p hp_closure
    simpa [hB_zero] using
      (tendsto_nhdsWithin_mono_left subset_closure hB_tendsto_closure)
  exact ⟨B, hB_cont, hB_super, hB_zero, hB_pos, hB_tendsto⟩

/--
%%handwave
name:
  Perron-open admissible subfunction
statement:
  An admissible subfunction on a Perron open region is continuous up to the
  closed region, subharmonic in the region, and bounded above by the prescribed
  boundary data on the frontier.
-/
def IsPerronOpenAdmissible {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronOpen X) (φ : PerronOpenBoundaryData Ω) (v : X → ℝ) : Prop :=
  ContinuousOn v (closure Ω.carrier) ∧
    IsSubharmonicOnSurface Ω.carrier v ∧
      ∀ x ∈ Ω.boundary, v x ≤ φ x

/--
%%handwave
name:
  Perron-open subfunction
statement:
  A Perron-open subfunction is a function together with the proof that it is
  admissible for the given boundary data on the open region.
-/
def PerronOpenSubfunction {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronOpen X) (φ : PerronOpenBoundaryData Ω) : Type :=
  {v : X → ℝ // IsPerronOpenAdmissible Ω φ v}

/--
%%handwave
name:
  Maximum of Perron-open admissible subfunctions
statement:
  The pointwise maximum of two Perron-open admissible subfunctions is again
  admissible.
proof:
  Finite maxima preserve continuity and
  [subharmonicity](lean:JJMath.Uniformization.subharmonicOnSurface_sup), and
  the boundary inequality is preserved because both functions satisfy it.
-/
theorem perronOpenAdmissible_sup
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronOpen X) (φ : PerronOpenBoundaryData Ω)
    {u v : X → ℝ}
    (hu : IsPerronOpenAdmissible Ω φ u)
    (hv : IsPerronOpenAdmissible Ω φ v) :
    IsPerronOpenAdmissible Ω φ (fun x ↦ u x ⊔ v x) := by
  exact ⟨
    hu.1.sup hv.1,
    subharmonicOnSurface_sup hu.2.1 hv.2.1,
    by
      intro x hx
      exact sup_le (hu.2.2 x hx) (hv.2.2 x hx)⟩

/--
%%handwave
name:
  Perron-open values at a point
statement:
  The Perron-open value set at a point is the set of all values taken there by
  admissible subfunctions.
-/
def perronOpenValueSet {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronOpen X) (φ : PerronOpenBoundaryData Ω) (x : X) : Set ℝ :=
  {a : ℝ | ∃ v : X → ℝ, IsPerronOpenAdmissible Ω φ v ∧ a = v x}

/--
%%handwave
name:
  Perron-open values are directed
statement:
  At a fixed point, any two Perron-open values are dominated by another
  Perron-open value.
proof:
  Given two admissible subfunctions, take their pointwise maximum.  The
  maximum is again admissible and its value at the point dominates both
  original values.
-/
theorem perronOpenValueSet_directedOn
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronOpen X) (φ : PerronOpenBoundaryData Ω) (x : X) :
    DirectedOn (· ≤ ·) (perronOpenValueSet Ω φ x) := by
  intro a ha b hb
  rcases ha with ⟨u, hu, rfl⟩
  rcases hb with ⟨v, hv, rfl⟩
  refine ⟨(u x ⊔ v x), ?_, le_sup_left, le_sup_right⟩
  exact ⟨fun y ↦ u y ⊔ v y, perronOpenAdmissible_sup Ω φ hu hv, rfl⟩

/--
%%handwave
name:
  Perron-open envelope
statement:
  The Perron-open envelope is the pointwise supremum of all admissible
  subfunctions on the open region.
-/
noncomputable def perronOpenEnvelope {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronOpen X) (φ : PerronOpenBoundaryData Ω) : X → ℝ :=
  fun x ↦ sSup (perronOpenValueSet Ω φ x)

/--
%%handwave
name:
  Perron-open envelope as a pointwise supremum
statement:
  The value of the Perron-open envelope at a point is the supremum of the
  Perron-open value set at that point.
proof:
  This is the defining formula for the Perron-open envelope.
-/
theorem perronOpenEnvelope_eq_sSup_valueSet
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronOpen X) (φ : PerronOpenBoundaryData Ω) (x : X) :
    perronOpenEnvelope Ω φ x = sSup (perronOpenValueSet Ω φ x) := rfl

/--
%%handwave
name:
  Perron-open envelope as supremum over subfunctions
statement:
  The Perron-open envelope is the indexed supremum of all admissible
  subfunctions.
proof:
  The Perron-open value set at a point is exactly the range of the evaluation
  map on the type of admissible subfunctions.
-/
theorem perronOpenEnvelope_eq_iSup_subfunctions
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronOpen X) (φ : PerronOpenBoundaryData Ω) (x : X) :
    perronOpenEnvelope Ω φ x =
      ⨆ v : PerronOpenSubfunction Ω φ, v.val x := by
  rw [perronOpenEnvelope_eq_sSup_valueSet]
  have hset :
      perronOpenValueSet Ω φ x =
        Set.range (fun v : PerronOpenSubfunction Ω φ ↦ v.val x) := by
    ext a
    constructor
    · intro ha
      rcases ha with ⟨v, hv, rfl⟩
      exact ⟨⟨v, hv⟩, rfl⟩
    · intro ha
      rcases ha with ⟨v, rfl⟩
      exact ⟨v.val, v.property, rfl⟩
  rw [hset]
  rfl

/--
%%handwave
name:
  Locally bounded Perron-open family
statement:
  A Perron-open family is locally bounded above if every compact subset of the
  region has a common upper bound for all admissible subfunctions.
-/
def PerronOpenFamilyLocallyBoundedAbove
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronOpen X) (φ : PerronOpenBoundaryData Ω) : Prop :=
  ∀ K : Set X, IsCompact K → K ⊆ Ω.carrier →
    ∃ M : ℝ,
      ∀ v : X → ℝ, IsPerronOpenAdmissible Ω φ v → ∀ x ∈ K, v x ≤ M

/--
%%handwave
name:
  Constants below Perron-open boundary data are admissible
statement:
  Any constant lying below the prescribed boundary data is a Perron-open
  admissible subfunction.
proof:
  Constants are continuous and subharmonic.  The boundary inequality is exactly
  the assumed lower bound.
-/
theorem constant_below_boundary_is_perronOpen_admissible
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronOpen X) (φ : PerronOpenBoundaryData Ω)
    {c : ℝ} (hc : ∀ x ∈ Ω.boundary, c ≤ φ x) :
    IsPerronOpenAdmissible Ω φ (fun _ : X ↦ c) := by
  exact ⟨
    continuousOn_const,
    subharmonicOnSurface_const Ω.carrier c,
    hc⟩

/--
%%handwave
name:
  Explicit lower bounds make Perron-open families nonempty
statement:
  If the boundary data has a global lower bound, then the Perron-open family
  is nonempty.
proof:
  The constant function at that lower bound is admissible.
-/
theorem perronOpen_family_nonempty_of_boundary_lower_bound
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronOpen X) (φ : PerronOpenBoundaryData Ω)
    {m : ℝ} (hm : ∀ x ∈ Ω.boundary, m ≤ φ x) :
    ∃ v : X → ℝ, IsPerronOpenAdmissible Ω φ v := by
  exact ⟨fun _ : X ↦ m, constant_below_boundary_is_perronOpen_admissible Ω φ hm⟩

/--
%%handwave
name:
  Perron-open value sets are nonempty from a nonempty family
statement:
  If the Perron-open family is nonempty, then every Perron-open value set is
  nonempty.
proof:
  Any admissible subfunction supplies one value at the chosen point.
-/
theorem perronOpenValueSet_nonempty_of_family_nonempty
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronOpen X) (φ : PerronOpenBoundaryData Ω)
    (hfamily_nonempty : ∃ v : X → ℝ, IsPerronOpenAdmissible Ω φ v)
    (x : X) :
    (perronOpenValueSet Ω φ x).Nonempty := by
  rcases hfamily_nonempty with ⟨v, hv⟩
  exact ⟨v x, v, hv, rfl⟩

/--
%%handwave
name:
  A pointwise family bound bounds Perron-open values
statement:
  If all Perron-open admissible subfunctions are bounded above by a common
  constant at a point, then the value set at that point is bounded above by
  the same constant.
proof:
  Every element of the value set is the value of an admissible subfunction,
  so the assumed common bound applies to it.
-/
theorem perronOpenValueSet_bddAbove_of_family_bound
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronOpen X) (φ : PerronOpenBoundaryData Ω) {x : X} {M : ℝ}
    (hbound : ∀ v : X → ℝ, IsPerronOpenAdmissible Ω φ v → v x ≤ M) :
    BddAbove (perronOpenValueSet Ω φ x) := by
  refine ⟨M, ?_⟩
  intro a ha
  rcases ha with ⟨v, hv, rfl⟩
  exact hbound v hv

/--
%%handwave
name:
  A pointwise family bound bounds the Perron-open envelope
statement:
  If all Perron-open admissible subfunctions are bounded above by a common
  constant at a point and the value set is nonempty there, then the envelope
  is bounded above by that constant.
proof:
  This is the order-theoretic property of the supremum of a nonempty bounded
  set of real numbers.
-/
theorem perronOpenEnvelope_le_of_family_bound
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronOpen X) (φ : PerronOpenBoundaryData Ω) {x : X} {M : ℝ}
    (hne : (perronOpenValueSet Ω φ x).Nonempty)
    (hbound : ∀ v : X → ℝ, IsPerronOpenAdmissible Ω φ v → v x ≤ M) :
    perronOpenEnvelope Ω φ x ≤ M := by
  rw [perronOpenEnvelope_eq_sSup_valueSet]
  exact csSup_le hne (by
    intro a ha
    rcases ha with ⟨v, hv, rfl⟩
    exact hbound v hv)

/--
%%handwave
name:
  Perron-open admissible subfunctions lie below the envelope from boundedness
statement:
  If the Perron-open value set is bounded above at a point, then every
  admissible subfunction is bounded above by the envelope at that point.
proof:
  The value of the subfunction belongs to the value set, so it lies below the
  supremum of that set.
-/
theorem perronOpenAdmissible_le_envelope_of_bddAbove
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronOpen X) (φ : PerronOpenBoundaryData Ω) {v : X → ℝ}
    (hv : IsPerronOpenAdmissible Ω φ v) {x : X}
    (hbdd : BddAbove (perronOpenValueSet Ω φ x)) :
    v x ≤ perronOpenEnvelope Ω φ x := by
  rw [perronOpenEnvelope_eq_sSup_valueSet]
  exact le_csSup hbdd ⟨v, hv, rfl⟩

/--
%%handwave
name:
  Locally bounded Perron-open families lie below the envelope
statement:
  If the Perron-open family is locally bounded above in the region, then every
  admissible subfunction is bounded above by the envelope at each point of the
  region.
proof:
  Apply the local bound to the compact singleton containing the point.  This
  gives a pointwise upper bound for the value set, and then the supremum
  property gives the desired inequality.
-/
theorem perronOpenAdmissible_le_envelope_of_locally_bounded
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronOpen X) (φ : PerronOpenBoundaryData Ω)
    (hfamily_locally_bounded : PerronOpenFamilyLocallyBoundedAbove Ω φ)
    {v : X → ℝ} (hv : IsPerronOpenAdmissible Ω φ v) :
    ∀ x ∈ Ω.carrier, v x ≤ perronOpenEnvelope Ω φ x := by
  intro x hxΩ
  have hsingleton_subset : ({x} : Set X) ⊆ Ω.carrier := by
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    simpa [hy] using hxΩ
  rcases hfamily_locally_bounded ({x} : Set X) isCompact_singleton
      hsingleton_subset with
    ⟨M, hM⟩
  have hbdd : BddAbove (perronOpenValueSet Ω φ x) :=
    perronOpenValueSet_bddAbove_of_family_bound Ω φ (x := x) (M := M)
      (by
        intro w hw
        exact hM w hw x (by simp))
  exact perronOpenAdmissible_le_envelope_of_bddAbove Ω φ hv hbdd

/--
%%handwave
name:
  Perron-open subfunctions approximate the envelope at a point
statement:
  If \(a\) is strictly below the Perron-open envelope at a point of the region,
  then some admissible subfunction has value greater than \(a\) there.
proof:
  Local boundedness at the singleton gives boundedness of the value set.  Since
  the family is nonempty, the defining property of the supremum supplies an
  admissible value above \(a\).
-/
theorem exists_perronOpenAdmissible_gt_of_lt_envelope
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronOpen X) (φ : PerronOpenBoundaryData Ω)
    (hfamily_nonempty : ∃ v : X → ℝ, IsPerronOpenAdmissible Ω φ v)
    (hfamily_locally_bounded : PerronOpenFamilyLocallyBoundedAbove Ω φ)
    {x : X} (hxΩ : x ∈ Ω.carrier) {a : ℝ}
    (ha : a < perronOpenEnvelope Ω φ x) :
    ∃ v : X → ℝ, IsPerronOpenAdmissible Ω φ v ∧ a < v x := by
  have hsingleton_subset : ({x} : Set X) ⊆ Ω.carrier := by
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    simpa [hy] using hxΩ
  rcases hfamily_locally_bounded ({x} : Set X) isCompact_singleton
      hsingleton_subset with
    ⟨M, hM⟩
  have hbdd : BddAbove (perronOpenValueSet Ω φ x) :=
    perronOpenValueSet_bddAbove_of_family_bound Ω φ (x := x) (M := M)
      (by
        intro v hv
        exact hM v hv x (by simp))
  rw [perronOpenEnvelope_eq_sSup_valueSet] at ha
  rcases (lt_csSup_iff hbdd
      (perronOpenValueSet_nonempty_of_family_nonempty Ω φ hfamily_nonempty x)).1 ha with
    ⟨b, hb, hab⟩
  rcases hb with ⟨v, hv, rfl⟩
  exact ⟨v, hv, hab⟩

/--
%%handwave
name:
  Perron-open subfunctions approximate the envelope within epsilon
statement:
  At each point of the region and for every positive epsilon, some admissible
  subfunction has value within epsilon of the Perron-open envelope from below.
proof:
  [Every number strictly below the Perron envelope at an interior point is exceeded there by an admissible subfunction](lean:JJMath.Uniformization.exists_perronOpenAdmissible_gt_of_lt_envelope). Apply this with $a=P_\Omega\varphi(x)-\varepsilon$.
-/
theorem exists_perronOpenAdmissible_envelope_sub_lt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronOpen X) (φ : PerronOpenBoundaryData Ω)
    (hfamily_nonempty : ∃ v : X → ℝ, IsPerronOpenAdmissible Ω φ v)
    (hfamily_locally_bounded : PerronOpenFamilyLocallyBoundedAbove Ω φ)
    {x : X} (hxΩ : x ∈ Ω.carrier) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : X → ℝ,
      IsPerronOpenAdmissible Ω φ v ∧ perronOpenEnvelope Ω φ x - ε < v x := by
  exact exists_perronOpenAdmissible_gt_of_lt_envelope Ω φ hfamily_nonempty
    hfamily_locally_bounded hxΩ (by linarith)

/--
%%handwave
name:
  Perron-open envelope is lower semicontinuous
statement:
  If the Perron-open family is locally bounded above in the region, then the
  Perron-open envelope is lower semicontinuous in the region.
proof:
  The envelope is the supremum of the admissible subfunctions.  Each
  admissible subfunction is continuous on the closed region, hence lower
  semicontinuous in the region.  Mathlib's theorem that locally bounded
  suprema of lower semicontinuous functions are lower semicontinuous then
  applies.
-/
theorem perronOpenEnvelope_lowerSemicontinuousOn
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronOpen X) (φ : PerronOpenBoundaryData Ω)
    (hfamily_locally_bounded : PerronOpenFamilyLocallyBoundedAbove Ω φ) :
    LowerSemicontinuousOn (perronOpenEnvelope Ω φ) Ω.carrier := by
  have hbdd :
      ∀ x ∈ Ω.carrier,
        BddAbove (Set.range fun v : PerronOpenSubfunction Ω φ ↦ v.val x) := by
    intro x hxΩ
    have hsingleton_subset : ({x} : Set X) ⊆ Ω.carrier := by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      simpa [hy] using hxΩ
    rcases hfamily_locally_bounded ({x} : Set X) isCompact_singleton
        hsingleton_subset with
      ⟨M, hM⟩
    refine ⟨M, ?_⟩
    intro a ha
    rcases ha with ⟨v, rfl⟩
    exact hM v.val v.property x (by simp)
  have hsub_lsc :
      ∀ v : PerronOpenSubfunction Ω φ,
        LowerSemicontinuousOn v.val Ω.carrier := by
    intro v
    exact (v.property.1.mono subset_closure).lowerSemicontinuousOn
  have hlsup :
      LowerSemicontinuousOn
        (fun x ↦ ⨆ v : PerronOpenSubfunction Ω φ, v.val x) Ω.carrier :=
    lowerSemicontinuousOn_ciSup hbdd hsub_lsc
  have henv_eq :
      perronOpenEnvelope Ω φ =
        fun x ↦ ⨆ v : PerronOpenSubfunction Ω φ, v.val x := by
    funext x
    exact perronOpenEnvelope_eq_iSup_subfunctions Ω φ x
  rw [henv_eq]
  exact hlsup

/--
%%handwave
name:
  Locally bounded Perron-open families give locally bounded envelopes
statement:
  If the Perron-open family is nonempty and locally bounded above in the
  region, then the Perron-open envelope is locally bounded above in the region.
proof:
  The common bound for all admissible subfunctions on a compact set is a
  pointwise bound for each value set, hence also for its supremum.
-/
theorem perronOpenEnvelope_locally_bounded_above_of_family_locally_bounded
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronOpen X) (φ : PerronOpenBoundaryData Ω)
    (hfamily_nonempty : ∃ v : X → ℝ, IsPerronOpenAdmissible Ω φ v)
    (hfamily_locally_bounded : PerronOpenFamilyLocallyBoundedAbove Ω φ) :
    ∀ K : Set X, IsCompact K → K ⊆ Ω.carrier →
      ∃ M : ℝ, ∀ x ∈ K, perronOpenEnvelope Ω φ x ≤ M := by
  intro K hK hKΩ
  rcases hfamily_locally_bounded K hK hKΩ with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro x hxK
  exact perronOpenEnvelope_le_of_family_bound Ω φ
    (perronOpenValueSet_nonempty_of_family_nonempty Ω φ hfamily_nonempty x)
    (by
      intro v hv
      exact hM v hv x hxK)

/--
%%handwave
name:
  Bounded Perron-open admissible subfunction
statement:
  A bounded Perron-open admissible subfunction is a Perron-open admissible
  subfunction that is bounded above by a fixed constant throughout the open
  region.
-/
def IsBoundedPerronOpenAdmissible
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronOpen X) (φ : PerronOpenBoundaryData Ω) (M : ℝ)
    (v : X → ℝ) : Prop :=
  IsPerronOpenAdmissible Ω φ v ∧
    ∀ x ∈ Ω.carrier, v x ≤ M

/--
%%handwave
name:
  Bounded Perron-open subfunction
statement:
  A bounded Perron-open subfunction is a function together with the proof that
  it is admissible and lies below the fixed upper bound in the open region.
-/
def BoundedPerronOpenSubfunction
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronOpen X) (φ : PerronOpenBoundaryData Ω) (M : ℝ) : Type :=
  {v : X → ℝ // IsBoundedPerronOpenAdmissible Ω φ M v}

/--
%%handwave
name:
  Maximum of bounded Perron-open subfunctions
statement:
  The pointwise maximum of two bounded Perron-open admissible subfunctions is
  again bounded Perron-open admissible.
proof:
  Maxima preserve Perron-open admissibility, and the fixed upper bound is
  preserved because both original subfunctions lie below it.
-/
theorem boundedPerronOpenAdmissible_sup
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronOpen X) (φ : PerronOpenBoundaryData Ω) (M : ℝ)
    {u v : X → ℝ}
    (hu : IsBoundedPerronOpenAdmissible Ω φ M u)
    (hv : IsBoundedPerronOpenAdmissible Ω φ M v) :
    IsBoundedPerronOpenAdmissible Ω φ M (fun x ↦ u x ⊔ v x) := by
  exact ⟨
    perronOpenAdmissible_sup Ω φ hu.1 hv.1,
    by
      intro x hxΩ
      exact sup_le (hu.2 x hxΩ) (hv.2 x hxΩ)⟩

/--
%%handwave
name:
  Bounded Perron-open values at a point
statement:
  The bounded Perron-open value set at a point consists of all values taken
  there by bounded Perron-open admissible subfunctions.
-/
def boundedPerronOpenValueSet
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronOpen X) (φ : PerronOpenBoundaryData Ω) (M : ℝ)
    (x : X) : Set ℝ :=
  {a : ℝ | ∃ v : X → ℝ, IsBoundedPerronOpenAdmissible Ω φ M v ∧ a = v x}

/--
%%handwave
name:
  Bounded Perron-open envelope
statement:
  The bounded Perron-open envelope is the pointwise supremum of the values of
  bounded admissible subfunctions.
-/
noncomputable def boundedPerronOpenEnvelope
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronOpen X) (φ : PerronOpenBoundaryData Ω) (M : ℝ) : X → ℝ :=
  fun x ↦ sSup (boundedPerronOpenValueSet Ω φ M x)

/--
%%handwave
name:
  Bounded Perron-open envelope as a supremum over subfunctions
statement:
  The bounded Perron-open envelope is the indexed supremum of all bounded
  admissible subfunctions.
proof:
  The bounded value set is exactly the range of evaluation on the type of
  bounded admissible subfunctions, and the supremum of that range is the
  corresponding indexed supremum.
-/
theorem boundedPerronOpenEnvelope_eq_iSup_subfunctions
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronOpen X) (φ : PerronOpenBoundaryData Ω) (M : ℝ) (x : X) :
    boundedPerronOpenEnvelope Ω φ M x =
      ⨆ v : BoundedPerronOpenSubfunction Ω φ M, v.val x := by
  have hset :
      boundedPerronOpenValueSet Ω φ M x =
        Set.range (fun v : BoundedPerronOpenSubfunction Ω φ M ↦ v.val x) := by
    ext a
    constructor
    · intro ha
      rcases ha with ⟨v, hv, rfl⟩
      exact ⟨⟨v, hv⟩, rfl⟩
    · intro ha
      rcases ha with ⟨v, rfl⟩
      exact ⟨v.val, v.property, rfl⟩
  rw [boundedPerronOpenEnvelope, hset]
  rfl

/--
%%handwave
name:
  Constants give nonempty bounded Perron-open families
statement:
  A constant below the boundary data and below the fixed upper bound gives a
  bounded Perron-open admissible subfunction.
proof:
  Constants are Perron-open admissible when they lie below the boundary data,
  and the interior upper bound is exactly the second hypothesis.
-/
theorem constant_below_boundary_is_boundedPerronOpen_admissible
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronOpen X) (φ : PerronOpenBoundaryData Ω) (M : ℝ)
    {c : ℝ} (hc_boundary : ∀ x ∈ Ω.boundary, c ≤ φ x) (hcM : c ≤ M) :
    IsBoundedPerronOpenAdmissible Ω φ M (fun _ : X ↦ c) := by
  exact ⟨
    constant_below_boundary_is_perronOpen_admissible Ω φ hc_boundary,
    by
      intro x _hx
      exact hcM⟩

/--
%%handwave
name:
  Bounded Perron-open value sets are nonempty
statement:
  If the bounded Perron-open family is nonempty, then every value set is
  nonempty.
proof:
  Choose one bounded admissible subfunction; its value at the given point is
  an element of the value set.
-/
theorem boundedPerronOpenValueSet_nonempty_of_family_nonempty
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronOpen X) (φ : PerronOpenBoundaryData Ω) (M : ℝ)
    (hfamily_nonempty :
      ∃ v : X → ℝ, IsBoundedPerronOpenAdmissible Ω φ M v)
    (x : X) :
    (boundedPerronOpenValueSet Ω φ M x).Nonempty := by
  rcases hfamily_nonempty with ⟨v, hv⟩
  exact ⟨v x, v, hv, rfl⟩

/--
%%handwave
name:
  Bounded Perron-open values are bounded above in the region
statement:
  At points of the open region, every bounded Perron-open value set is bounded
  above by the fixed bound.
proof:
  By bounded admissibility, every contributing subfunction has value at most
  the fixed bound at each point of the region.
-/
theorem boundedPerronOpenValueSet_bddAbove
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronOpen X) (φ : PerronOpenBoundaryData Ω) (M : ℝ)
    {x : X} (hxΩ : x ∈ Ω.carrier) :
    BddAbove (boundedPerronOpenValueSet Ω φ M x) := by
  refine ⟨M, ?_⟩
  intro a ha
  rcases ha with ⟨v, hv, rfl⟩
  exact hv.2 x hxΩ

/--
%%handwave
name:
  Bounded Perron-open subfunctions lie below the envelope
statement:
  At a point where the bounded value set is bounded above, every bounded
  Perron-open admissible subfunction lies below the bounded Perron-open
  envelope.
proof:
  The value of the subfunction is an element of the value set, and the
  envelope is the supremum of that value set.
-/
theorem boundedPerronOpenAdmissible_le_boundedPerronOpenEnvelope_of_bddAbove
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronOpen X) (φ : PerronOpenBoundaryData Ω) (M : ℝ)
    {v : X → ℝ} (hv : IsBoundedPerronOpenAdmissible Ω φ M v)
    {x : X} (hbdd : BddAbove (boundedPerronOpenValueSet Ω φ M x)) :
    v x ≤ boundedPerronOpenEnvelope Ω φ M x := by
  rw [boundedPerronOpenEnvelope]
  exact le_csSup hbdd ⟨v, hv, rfl⟩

/--
%%handwave
name:
  A pointwise family bound bounds the bounded Perron-open envelope
statement:
  If all bounded Perron-open admissible subfunctions have value at most \(A\)
  at a point, and the bounded value set is nonempty there, then the bounded
  Perron-open envelope is at most \(A\) at that point.
proof:
  The bounded envelope is the supremum of the bounded value set, and every
  element of that set is bounded by \(A\).
-/
theorem boundedPerronOpenEnvelope_le_of_family_bound
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronOpen X) (φ : PerronOpenBoundaryData Ω) (M : ℝ)
    {x : X} {A : ℝ}
    (hne : (boundedPerronOpenValueSet Ω φ M x).Nonempty)
    (hbound :
      ∀ v : X → ℝ, IsBoundedPerronOpenAdmissible Ω φ M v → v x ≤ A) :
    boundedPerronOpenEnvelope Ω φ M x ≤ A := by
  rw [boundedPerronOpenEnvelope]
  exact csSup_le hne (by
    intro a ha
    rcases ha with ⟨v, hv, rfl⟩
    exact hbound v hv)

/--
%%handwave
name:
  The bounded Perron-open envelope lies below the bound
statement:
  At points of the open region, the bounded Perron-open envelope is at most
  the fixed upper bound.
proof:
  It is the supremum of a nonempty value set whose elements are all at most
  the fixed bound.
-/
theorem boundedPerronOpenEnvelope_le_bound
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronOpen X) (φ : PerronOpenBoundaryData Ω) (M : ℝ)
    (hfamily_nonempty :
      ∃ v : X → ℝ, IsBoundedPerronOpenAdmissible Ω φ M v)
    {x : X} (hxΩ : x ∈ Ω.carrier) :
    boundedPerronOpenEnvelope Ω φ M x ≤ M := by
  exact csSup_le
    (boundedPerronOpenValueSet_nonempty_of_family_nonempty Ω φ M
      hfamily_nonempty x)
    (by
      intro a ha
      rcases ha with ⟨v, hv, rfl⟩
      exact hv.2 x hxΩ)

/--
%%handwave
name:
  A calibrated affine lower barrier is bounded Perron-open admissible
statement:
  Let \(B\) be a nonnegative superharmonic function on a Perron-open region.
  If \(c\) is a global lower admissible constant and
  \(A-CB\) lies below the boundary data, with \(C\ge0\) and \(A\le M\), then
  \(\max(c,A-CB)\) is bounded Perron-open admissible with upper bound \(M\).
proof:
  The affine expression \(A-CB\) is subharmonic because \(-B\) is subharmonic
  and \(C\ge0\).  Taking the maximum with the constant \(c\) preserves
  subharmonicity and continuity.  The two boundary inequalities give the
  Perron-open boundary condition, while nonnegativity of \(B\) gives
  \(A-CB\le A\le M\) in the region.
-/
theorem boundedPerronOpenAdmissible_sup_const_affine_negative_barrier
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexOneManifold X]
    (Ω : PerronOpen X) (φ : PerronOpenBoundaryData Ω) (M : ℝ)
    {B : X → ℝ} {c A C : ℝ}
    (hc_boundary : ∀ x ∈ Ω.boundary, c ≤ φ x)
    (hcM : c ≤ M)
    (hAM : A ≤ M)
    (hC : 0 ≤ C)
    (hB_cont : ContinuousOn B (closure Ω.carrier))
    (hB_super : IsSuperharmonicOnSurface Ω.carrier B)
    (hB_nonneg : ∀ x ∈ Ω.carrier, 0 ≤ B x)
    (hboundary_affine : ∀ x ∈ Ω.boundary, A - C * B x ≤ φ x) :
    IsBoundedPerronOpenAdmissible Ω φ M
      (fun x ↦ c ⊔ (A - C * B x)) := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · exact continuousOn_const.sup
        (continuousOn_const.sub (continuousOn_const.mul hB_cont))
    · have hscaled :
          IsSubharmonicOnSurface Ω.carrier (fun x ↦ C * (-B x)) :=
        subharmonicOnSurface_const_mul_nonneg hC hB_super
      have haffine :
          IsSubharmonicOnSurface Ω.carrier
            (fun x ↦ A + C * (-B x)) :=
        subharmonicOnSurface_const_add A hscaled
      have hconst : IsSubharmonicOnSurface Ω.carrier (fun _ : X ↦ c) :=
        subharmonicOnSurface_const Ω.carrier c
      simpa [sub_eq_add_neg, mul_neg] using
        subharmonicOnSurface_sup hconst haffine
    · intro x hx
      exact sup_le (hc_boundary x hx) (hboundary_affine x hx)
  · intro x hxΩ
    have hCB_nonneg : 0 ≤ C * B x := mul_nonneg hC (hB_nonneg x hxΩ)
    have haffine_le_M : A - C * B x ≤ M := by linarith
    exact sup_le hcM haffine_le_M

/--
%%handwave
name:
  Local lower barriers can be calibrated against Perron-open boundary data
statement:
  Suppose the Perron-open boundary data has a global lower bound \(c\).  At a
  boundary point admitting a local barrier, and for every positive
  \(\varepsilon\), there is a nonnegative global superharmonic barrier \(B\)
  and a constant \(C\ge0\) such that
  \(\varphi(p)-\varepsilon/2-CB\) lies below the boundary data on the whole
  boundary, while \(B\) tends to zero at \(p\).
proof:
  Patch the local barrier by truncating it to a positive constant outside a
  compact shrink.  Near \(p\), boundary continuity gives
  \(\varphi(p)-\varepsilon/2\le\varphi\).  On the remaining boundary, the
  patched barrier has a positive floor, so a sufficiently large \(C\) pushes
  the affine expression below the global lower bound \(c\).
-/
theorem boundedPerronOpenBarrier_lower_calibration_of_local_barrier
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexOneManifold X]
    (Ω : PerronOpen X) (φ : PerronOpenBoundaryData Ω)
    {c : ℝ} (hc_boundary : ∀ x ∈ Ω.boundary, c ≤ φ x)
    {p : X} (hp : HasLocalPerronOpenBarrierAt Ω p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ B : X → ℝ, ∃ C : ℝ,
      0 ≤ C ∧
        ContinuousOn B (closure Ω.carrier) ∧
          IsSuperharmonicOnSurface Ω.carrier B ∧
            (∀ x ∈ Ω.carrier, 0 ≤ B x) ∧
              Filter.Tendsto B (𝓝[Ω.carrier] p) (𝓝 0) ∧
                ∀ x ∈ Ω.boundary, φ p - ε / 2 - C * B x ≤ φ x := by
  let A : ℝ := φ p - ε / 2
  have hnear_lt :
      ∀ᶠ x in 𝓝[Ω.boundary] p, A < φ x := by
    simpa [A] using
      perronOpenBoundaryData_eventually_gt_boundary_sub φ hp.1
        (by linarith : 0 < ε / 2)
  have hnear_le :
      {x : X | A ≤ φ x} ∈ 𝓝[Ω.boundary] p :=
    hnear_lt.mono (fun _ hx ↦ le_of_lt hx)
  rcases mem_nhdsWithin.mp hnear_le with
    ⟨U, hU_open, hpU, hU_boundary⟩
  rcases hp with
    ⟨hp_boundary, N, hN_open, hpN, b, hb_cont, hb_super, hb_zero, hb_pos⟩
  have hNU_open : IsOpen (N ∩ U) := hN_open.inter hU_open
  have hpNU : p ∈ N ∩ U := ⟨hpN, hpU⟩
  rcases exists_surface_open_nhds_isCompact_closure_subset hNU_open hpNU with
    ⟨V, hV_open, hpV, hV_closure_subset_NU, hV_compact⟩
  have hV_closure_subset_N : closure V ⊆ N := by
    intro x hx
    exact (hV_closure_subset_NU hx).1
  have hV_subset_U : V ⊆ U := by
    intro x hx
    exact (hV_closure_subset_NU (subset_closure hx)).2
  rcases localPerronOpenBarrier_truncated_patch_from_compact_shrink Ω
      hN_open hb_cont hb_super hb_zero hb_pos
      hV_open hpV hV_closure_subset_N hV_compact with
    ⟨B, hB_cont, hB_local_super, hB_zero, hB_pos,
      η, hηpos, hB_eq_η_of_not_mem_V⟩
  have hB_super : IsSuperharmonicOnSurface Ω.carrier B :=
    superharmonicOnSurface_of_locally Ω.isOpen hB_local_super
  have hp_closure : p ∈ closure Ω.carrier :=
    frontier_subset_closure hp_boundary
  have hB_tendsto :
      Filter.Tendsto B (𝓝[Ω.carrier] p) (𝓝 0) := by
    have hB_tendsto_closure :
        Filter.Tendsto B (𝓝[closure Ω.carrier] p) (𝓝 (B p)) :=
      hB_cont p hp_closure
    simpa [hB_zero] using
      (tendsto_nhdsWithin_mono_left subset_closure hB_tendsto_closure)
  have hp_not_carrier : p ∉ Ω.carrier :=
    Ω.not_mem_carrier_of_mem_boundary hp_boundary
  have hB_nonneg_carrier : ∀ x ∈ Ω.carrier, 0 ≤ B x := by
    intro x hxΩ
    have hxp : x ≠ p := by
      intro hxp
      exact hp_not_carrier (by simpa [hxp] using hxΩ)
    exact le_of_lt (hB_pos x (subset_closure hxΩ) hxp)
  let C : ℝ := max 0 ((A - c) / η)
  have hC_nonneg : 0 ≤ C := le_max_left 0 ((A - c) / η)
  have hgap_le_Cη : A - c ≤ C * η := by
    have hdiv_le_C : (A - c) / η ≤ C := le_max_right 0 ((A - c) / η)
    calc
      A - c = ((A - c) / η) * η := by
        exact (div_mul_cancel₀ (A - c) hηpos.ne').symm
      _ ≤ C * η := mul_le_mul_of_nonneg_right hdiv_le_C hηpos.le
  refine ⟨B, C, hC_nonneg, hB_cont, hB_super, hB_nonneg_carrier, hB_tendsto, ?_⟩
  intro x hx_boundary
  by_cases hxU : x ∈ U
  · have hA_le : A ≤ φ x := hU_boundary ⟨hxU, hx_boundary⟩
    have hx_closure : x ∈ closure Ω.carrier :=
      frontier_subset_closure hx_boundary
    have hB_nonneg_boundary : 0 ≤ B x := by
      by_cases hxp : x = p
      · simp [hxp, hB_zero]
      · exact le_of_lt (hB_pos x hx_closure hxp)
    have hCB_nonneg : 0 ≤ C * B x :=
      mul_nonneg hC_nonneg hB_nonneg_boundary
    dsimp [A] at hA_le ⊢
    linarith
  · have hx_not_V : x ∉ V := fun hxV ↦ hxU (hV_subset_U hxV)
    have hB_eq : B x = η := hB_eq_η_of_not_mem_V x hx_not_V
    have hc_le : c ≤ φ x := hc_boundary x hx_boundary
    dsimp [C]
    rw [hB_eq]
    dsimp [A] at hgap_le_Cη ⊢
    linarith

/--
%%handwave
name:
  Local lower barrier subfunction for bounded Perron-open envelopes
statement:
  Suppose the boundary data has a global lower bound \(c\), the bounded
  Perron-open family has upper bound \(M\), and \(\varphi(p)\le M\).  At a
  boundary point admitting a local Perron-open barrier, there is a bounded
  admissible subfunction that is eventually larger than
  \(\varphi(p)-\varepsilon\).
proof:
  On a compactly contained shrink, use the affine barrier
  \(\varphi(p)-\varepsilon/2-CB\).  The constant \(C\) is chosen so that this
  affine expression is below the global lower admissible constant \(c\) on the
  artificial boundary of the shrink.  Taking the maximum with \(c\) patches the
  local expression to a global bounded admissible subfunction.  Since \(B\)
  tends to zero at \(p\), this subfunction is eventually above
  \(\varphi(p)-\varepsilon\).
-/
theorem boundedPerronOpenBarrier_lower_subfunction_eventually_gt_of_local_barrier
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexOneManifold X]
    (Ω : PerronOpen X) (φ : PerronOpenBoundaryData Ω) (M : ℝ)
    {c : ℝ} (hc_boundary : ∀ x ∈ Ω.boundary, c ≤ φ x)
    (hcM : c ≤ M)
    {p : X} (hp : HasLocalPerronOpenBarrierAt Ω p)
    (hpM : φ p ≤ M)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ v : X → ℝ,
      IsBoundedPerronOpenAdmissible Ω φ M v ∧
        ∀ᶠ x in 𝓝[Ω.carrier] p, φ p - ε < v x := by
  rcases boundedPerronOpenBarrier_lower_calibration_of_local_barrier
      Ω φ hc_boundary hp hε with
    ⟨B, C, hC, hB_cont, hB_super, hB_nonneg, hB_tendsto, hboundary_affine⟩
  let A : ℝ := φ p - ε / 2
  have hAM : A ≤ M := by
    dsimp [A]
    linarith
  let v : X → ℝ := fun x ↦ c ⊔ (A - C * B x)
  have hv : IsBoundedPerronOpenAdmissible Ω φ M v := by
    dsimp [v, A]
    exact boundedPerronOpenAdmissible_sup_const_affine_negative_barrier
      Ω φ M hc_boundary hcM hAM hC hB_cont hB_super hB_nonneg
      hboundary_affine
  refine ⟨v, hv, ?_⟩
  have hCB_tendsto :
      Filter.Tendsto (fun x ↦ C * B x) (𝓝[Ω.carrier] p) (𝓝 0) := by
    simpa using (Filter.Tendsto.const_mul C hB_tendsto)
  have hsmall :
      ∀ᶠ x in 𝓝[Ω.carrier] p, C * B x < ε / 2 := by
    exact (tendsto_order.mp hCB_tendsto).2 (ε / 2) (by linarith)
  filter_upwards [hsmall] with x hxsmall
  have haffine : φ p - ε < A - C * B x := by
    dsimp [A]
    linarith
  exact haffine.trans_le le_sup_right

/--
%%handwave
name:
  Bounded Perron-open barriers give lower boundary estimates
statement:
  Suppose the boundary data has a global lower bound \(c\), the bounded
  Perron-open family is bounded above by \(M\), and \(\varphi(p)\le M\).  At a
  boundary point admitting a local Perron-open barrier, the bounded
  Perron-open envelope is eventually greater than
  \(\varphi(p)-\varepsilon\) for every positive \(\varepsilon\).
proof:
  Near \(p\), continuity of the boundary data and the local barrier give an
  affine barrier subfunction
  \(\varphi(p)-\varepsilon/2-Cb\).  On the edge of a small shrink this affine
  function is pushed below the global lower admissible constant \(c\); taking
  the maximum with \(c\) therefore patches it to a global bounded admissible
  subfunction.  The bounded envelope dominates this subfunction, and the
  barrier tends to zero at \(p\).
-/
theorem boundedPerronOpenEnvelope_eventually_gt_boundary_sub_of_local_barrier
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexOneManifold X]
    (Ω : PerronOpen X) (φ : PerronOpenBoundaryData Ω) (M : ℝ)
    {c : ℝ} (hc_boundary : ∀ x ∈ Ω.boundary, c ≤ φ x)
    (hcM : c ≤ M)
    {p : X} (hp : HasLocalPerronOpenBarrierAt Ω p)
    (hpM : φ p ≤ M)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in 𝓝[Ω.carrier] p,
      φ p - ε < boundedPerronOpenEnvelope Ω φ M x := by
  rcases boundedPerronOpenBarrier_lower_subfunction_eventually_gt_of_local_barrier
      Ω φ M hc_boundary hcM hp hpM hε with
    ⟨v, hv, hv_eventually⟩
  filter_upwards [hv_eventually, self_mem_nhdsWithin] with x hvx hxΩ
  have hbdd : BddAbove (boundedPerronOpenValueSet Ω φ M x) :=
    boundedPerronOpenValueSet_bddAbove Ω φ M hxΩ
  exact hvx.trans_le
    (boundedPerronOpenAdmissible_le_boundedPerronOpenEnvelope_of_bddAbove
      Ω φ M hv hbdd)

/--
%%handwave
name:
  The bounded Perron-open envelope is lower semicontinuous
statement:
  The bounded Perron-open envelope is lower semicontinuous in the open region.
proof:
  It is the supremum of continuous admissible subfunctions restricted to the
  open region, and the fixed upper bound gives the pointwise boundedness
  needed for lower semicontinuity of a supremum.
-/
theorem boundedPerronOpenEnvelope_lowerSemicontinuousOn
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronOpen X) (φ : PerronOpenBoundaryData Ω) (M : ℝ) :
    LowerSemicontinuousOn (boundedPerronOpenEnvelope Ω φ M) Ω.carrier := by
  have hbdd :
      ∀ x ∈ Ω.carrier,
        BddAbove
          (Set.range fun v : BoundedPerronOpenSubfunction Ω φ M ↦ v.val x) := by
    intro x hxΩ
    refine ⟨M, ?_⟩
    intro a ha
    rcases ha with ⟨v, rfl⟩
    exact v.property.2 x hxΩ
  have hsub_lsc :
      ∀ v : BoundedPerronOpenSubfunction Ω φ M,
        LowerSemicontinuousOn v.val Ω.carrier := by
    intro v
    exact (v.property.1.1.mono subset_closure).lowerSemicontinuousOn
  have hlsup :
      LowerSemicontinuousOn
        (fun x ↦ ⨆ v : BoundedPerronOpenSubfunction Ω φ M, v.val x)
        Ω.carrier :=
    lowerSemicontinuousOn_ciSup hbdd hsub_lsc
  have henv_eq :
      boundedPerronOpenEnvelope Ω φ M =
        fun x ↦ ⨆ v : BoundedPerronOpenSubfunction Ω φ M, v.val x := by
    funext x
    exact boundedPerronOpenEnvelope_eq_iSup_subfunctions Ω φ M x
  rw [henv_eq]
  exact hlsup

/--
%%handwave
name:
  Bounded Perron-open subfunctions approximate the envelope
statement:
  At a point in the open region, bounded admissible subfunctions approximate
  the bounded Perron-open envelope from below.
proof:
  This is the defining property of the supremum of the nonempty bounded value
  set at the point.
-/
theorem exists_boundedPerronOpenAdmissible_envelope_sub_lt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronOpen X) (φ : PerronOpenBoundaryData Ω) (M : ℝ)
    (hfamily_nonempty :
      ∃ v : X → ℝ, IsBoundedPerronOpenAdmissible Ω φ M v)
    {x : X} (hxΩ : x ∈ Ω.carrier) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : X → ℝ,
      IsBoundedPerronOpenAdmissible Ω φ M v ∧
        boundedPerronOpenEnvelope Ω φ M x - ε < v x := by
  have hbdd : BddAbove (boundedPerronOpenValueSet Ω φ M x) :=
    boundedPerronOpenValueSet_bddAbove Ω φ M hxΩ
  have hne : (boundedPerronOpenValueSet Ω φ M x).Nonempty :=
    boundedPerronOpenValueSet_nonempty_of_family_nonempty Ω φ M
      hfamily_nonempty x
  have hlt :
      boundedPerronOpenEnvelope Ω φ M x - ε <
        sSup (boundedPerronOpenValueSet Ω φ M x) := by
    rw [boundedPerronOpenEnvelope]
    linarith
  rcases (lt_csSup_iff hbdd hne).1 hlt with ⟨a, ha, hlt_a⟩
  rcases ha with ⟨v, hv, rfl⟩
  exact ⟨v, hv, hlt_a⟩

/--
%%handwave
name:
  Perron domain
statement:
  A Perron domain is a nonempty relatively compact open subset of a Riemann
  surface.
-/
structure PerronDomain (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] where
  /-- The underlying open subset. -/
  carrier : Set X
  /-- The domain is open. -/
  isOpen : IsOpen carrier
  /-- The domain is nonempty. -/
  nonempty : carrier.Nonempty
  /-- The closure is compact. -/
  compact_closure : IsCompact (closure carrier)

namespace PerronDomain

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- The boundary of a Perron domain. -/
def boundary (Ω : PerronDomain X) : Set X :=
  frontier Ω.carrier

/--
%%handwave
name:
  A Perron domain as a Perron open region
statement:
  Every relatively compact Perron domain has an underlying Perron open region.
-/
def toPerronOpen (Ω : PerronDomain X) : PerronOpen X where
  carrier := Ω.carrier
  isOpen := Ω.isOpen
  nonempty := Ω.nonempty

/--
%%handwave
name:
  Forgetting relative compactness preserves the carrier
statement:
  The open region underlying a Perron domain has exactly the same carrier as
  the original domain.
proof:
  This is immediate from the construction, which changes only the stored
  geometric data and leaves the underlying set unchanged.
-/
@[simp]
theorem toPerronOpen_carrier (Ω : PerronDomain X) :
    Ω.toPerronOpen.carrier = Ω.carrier := rfl

/--
%%handwave
name:
  Forgetting relative compactness preserves the boundary
statement:
  The boundary of the open region underlying a Perron domain equals the
  boundary of the original domain.
proof:
  Both boundaries are the frontier of the common carrier.
-/
@[simp]
theorem toPerronOpen_boundary (Ω : PerronDomain X) :
    Ω.toPerronOpen.boundary = Ω.boundary := rfl

/--
%%handwave
name:
  The Perron boundary is compact
statement:
  The boundary of a Perron domain is compact.
proof:
  The boundary is a closed subset of the compact closure of the domain.
-/
theorem compact_boundary (Ω : PerronDomain X) :
    IsCompact Ω.boundary := by
  exact Ω.compact_closure.of_isClosed_subset isClosed_frontier
    (by
      intro x hx
      exact frontier_subset_closure hx)

/--
%%handwave
name:
  Open relatively compact sets are Perron domains
statement:
  Every nonempty open set with compact closure determines a Perron domain by
  taking that set as the carrier.
proof:
  This is just the data required in the definition of a Perron domain.
-/
def ofOpenCompactClosure (U : Set X)
    (hU_open : IsOpen U) (hU_nonempty : U.Nonempty)
    (hU_compact_closure : IsCompact (closure U)) : PerronDomain X where
  carrier := U
  isOpen := hU_open
  nonempty := hU_nonempty
  compact_closure := hU_compact_closure

/--
%%handwave
name:
  Carrier of the Perron domain constructed from an open set
statement:
  The Perron domain constructed from a nonempty open set \(U\) with compact
  closure has carrier \(U\).
proof:
  The construction stores \(U\) itself as the carrier.
-/
@[simp]
theorem ofOpenCompactClosure_carrier
    (U : Set X) (hU_open : IsOpen U) (hU_nonempty : U.Nonempty)
    (hU_compact_closure : IsCompact (closure U)) :
    (ofOpenCompactClosure U hU_open hU_nonempty hU_compact_closure).carrier =
      U := rfl

/--
%%handwave
name:
  Boundary of the Perron domain constructed from an open set
statement:
  The boundary of the Perron domain constructed from a nonempty open set \(U\)
  with compact closure is \(\partial U\).
proof:
  Its carrier is \(U\), and the boundary of a Perron domain is defined as the
  frontier of its carrier.
-/
@[simp]
theorem ofOpenCompactClosure_boundary
    (U : Set X) (hU_open : IsOpen U) (hU_nonempty : U.Nonempty)
    (hU_compact_closure : IsCompact (closure U)) :
    (ofOpenCompactClosure U hU_open hU_nonempty hU_compact_closure).boundary =
      frontier U := rfl

/--
%%handwave
name:
  Smooth domains are Perron domains
statement:
  Every smooth boundary domain is a Perron domain after forgetting smoothness
  of the boundary.
-/
def ofSmoothBoundaryDomain (Ω : SmoothBoundaryDomain X) : PerronDomain X where
  carrier := Ω.carrier
  isOpen := Ω.isOpen
  nonempty := Ω.nonempty
  compact_closure := Ω.compact_closure

/--
%%handwave
name:
  Forgetting boundary smoothness preserves the carrier
statement:
  The Perron domain obtained from a smooth boundary domain has the same carrier
  as the original domain.
proof:
  The construction forgets the smooth-boundary data without changing the
  underlying set.
-/
@[simp]
theorem ofSmoothBoundaryDomain_carrier (Ω : SmoothBoundaryDomain X) :
    (ofSmoothBoundaryDomain Ω).carrier = Ω.carrier := rfl

/--
%%handwave
name:
  Forgetting boundary smoothness preserves the boundary
statement:
  The Perron domain obtained from a smooth boundary domain has the same
  boundary as the original domain.
proof:
  Both boundaries are the frontier of their common carrier.
-/
@[simp]
theorem ofSmoothBoundaryDomain_boundary (Ω : SmoothBoundaryDomain X) :
    (ofSmoothBoundaryDomain Ω).boundary = Ω.boundary := rfl

end PerronDomain

/--
%%handwave
name:
  Perron boundary data
statement:
  Boundary data for the harmonic Dirichlet problem is a real-valued function,
  represented on the ambient surface, that is continuous on the boundary of
  the Perron domain.
-/
structure PerronBoundaryData {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronDomain X) where
  /-- The prescribed boundary value, represented by an ambient function. -/
  toFun : X → ℝ
  /-- The prescribed value is continuous along the boundary. -/
  continuous_boundary : ContinuousOn toFun Ω.boundary

namespace PerronBoundaryData

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {Ω : PerronDomain X}

instance : CoeFun (PerronBoundaryData Ω) (fun _ ↦ X → ℝ) where
  coe φ := φ.toFun

/--
%%handwave
name:
  Boundary data on the underlying Perron open region
statement:
  Boundary data on a Perron domain restricts to boundary data on its underlying
  Perron open region.
-/
def toPerronOpenBoundaryData (φ : PerronBoundaryData Ω) :
    PerronOpenBoundaryData Ω.toPerronOpen where
  toFun := φ.toFun
  continuous_boundary := by
    simpa [PerronDomain.toPerronOpen_boundary] using φ.continuous_boundary

/--
%%handwave
name:
  Boundary data has a lower bound
statement:
  Continuous real-valued boundary data on a Perron boundary has a lower bound.
proof:
  The boundary is compact, and a continuous real-valued function on a compact
  set is bounded below.
-/
theorem exists_lower_bound (φ : PerronBoundaryData Ω) :
    ∃ m : ℝ, ∀ x ∈ Ω.boundary, m ≤ φ x := by
  have hbdd : BddBelow ((φ : X → ℝ) '' Ω.boundary) :=
    LowerSemicontinuousOn.bddBelow_of_isCompact
      (PerronDomain.compact_boundary Ω)
      φ.continuous_boundary.lowerSemicontinuousOn
  rcases hbdd with ⟨m, hm⟩
  exact ⟨m, by
    intro x hx
    exact hm ⟨x, hx, rfl⟩⟩

/--
%%handwave
name:
  Boundary data has an upper bound
statement:
  Continuous real-valued boundary data on a Perron boundary has an upper bound.
proof:
  The boundary is compact, and a continuous real-valued function on a compact
  set is bounded above.
-/
theorem exists_upper_bound (φ : PerronBoundaryData Ω) :
    ∃ M : ℝ, ∀ x ∈ Ω.boundary, φ x ≤ M := by
  have hbdd : BddAbove ((φ : X → ℝ) '' Ω.boundary) :=
    UpperSemicontinuousOn.bddAbove_of_isCompact
      (PerronDomain.compact_boundary Ω)
      φ.continuous_boundary.upperSemicontinuousOn
  rcases hbdd with ⟨M, hM⟩
  exact ⟨M, by
    intro x hx
    exact hM ⟨x, hx, rfl⟩⟩

end PerronBoundaryData

/--
%%handwave
name:
  Perron-admissible subfunction
statement:
  A Perron-admissible subfunction is continuous up to the closed domain,
  subharmonic in the interior, and bounded above by the prescribed boundary
  data on the boundary.
-/
def IsPerronAdmissible {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronDomain X) (φ : PerronBoundaryData Ω) (v : X → ℝ) : Prop :=
  ContinuousOn v (closure Ω.carrier) ∧
    IsSubharmonicOnSurface Ω.carrier v ∧
      ∀ x ∈ Ω.boundary, v x ≤ φ x

/--
%%handwave
name:
  Perron subfunction
statement:
  A Perron subfunction is a function together with the proof that it is
  admissible for the given boundary data.
-/
def PerronSubfunction {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronDomain X) (φ : PerronBoundaryData Ω) : Type :=
  {v : X → ℝ // IsPerronAdmissible Ω φ v}

/--
%%handwave
name:
  Maximum of Perron-admissible subfunctions
statement:
  The pointwise maximum of two Perron-admissible subfunctions is again
  Perron-admissible.
proof:
  Finite maxima preserve continuity and
  [subharmonicity](lean:JJMath.Uniformization.subharmonicOnSurface_sup), and
  the boundary inequality is preserved because both functions satisfy it.
-/
theorem perronAdmissible_sup
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronDomain X) (φ : PerronBoundaryData Ω)
    {u v : X → ℝ}
    (hu : IsPerronAdmissible Ω φ u)
    (hv : IsPerronAdmissible Ω φ v) :
    IsPerronAdmissible Ω φ (fun x ↦ u x ⊔ v x) := by
  exact ⟨
    hu.1.sup hv.1,
    subharmonicOnSurface_sup hu.2.1 hv.2.1,
    by
      intro x hx
      exact sup_le (hu.2.2 x hx) (hv.2.2 x hx)⟩

/--
%%handwave
name:
  Perron values at a point
statement:
  The Perron value set at a point is the set of all values taken there by
  Perron-admissible subfunctions.
-/
def perronValueSet {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronDomain X) (φ : PerronBoundaryData Ω) (x : X) : Set ℝ :=
  {a : ℝ | ∃ v : X → ℝ, IsPerronAdmissible Ω φ v ∧ a = v x}

/--
%%handwave
name:
  Perron values are directed
statement:
  At a fixed point, any two Perron values are dominated by another Perron
  value.
proof:
  Given two admissible subfunctions, take their pointwise maximum.  The
  maximum is again admissible and its value at the point dominates both
  original values.
-/
theorem perronValueSet_directedOn
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronDomain X) (φ : PerronBoundaryData Ω) (x : X) :
    DirectedOn (· ≤ ·) (perronValueSet Ω φ x) := by
  intro a ha b hb
  rcases ha with ⟨u, hu, rfl⟩
  rcases hb with ⟨v, hv, rfl⟩
  refine ⟨(u x ⊔ v x), ?_, le_sup_left, le_sup_right⟩
  exact ⟨fun y ↦ u y ⊔ v y, perronAdmissible_sup Ω φ hu hv, rfl⟩

/--
%%handwave
name:
  Perron envelope
statement:
  The Perron envelope is the pointwise supremum of all Perron-admissible
  subfunctions.
-/
noncomputable def perronEnvelope {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronDomain X) (φ : PerronBoundaryData Ω) : X → ℝ :=
  fun x ↦ sSup (perronValueSet Ω φ x)

/--
%%handwave
name:
  Perron envelope as a pointwise supremum
statement:
  The value of the Perron envelope at a point is the supremum of the Perron
  value set at that point.
proof:
  This is the defining formula for the Perron envelope.
-/
theorem perronEnvelope_eq_sSup_perronValueSet
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronDomain X) (φ : PerronBoundaryData Ω) (x : X) :
    perronEnvelope Ω φ x = sSup (perronValueSet Ω φ x) := rfl

/--
%%handwave
name:
  Perron envelope as supremum over subfunctions
statement:
  The Perron envelope is the indexed supremum of all admissible subfunctions.
proof:
  The Perron value set at a point is exactly the range of the evaluation map
  on the type of admissible subfunctions.
-/
theorem perronEnvelope_eq_iSup_subfunctions
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronDomain X) (φ : PerronBoundaryData Ω) (x : X) :
    perronEnvelope Ω φ x =
      ⨆ v : PerronSubfunction Ω φ, v.val x := by
  rw [perronEnvelope_eq_sSup_perronValueSet]
  have hset :
      perronValueSet Ω φ x =
        Set.range (fun v : PerronSubfunction Ω φ ↦ v.val x) := by
    ext a
    constructor
    · intro ha
      rcases ha with ⟨v, hv, rfl⟩
      exact ⟨⟨v, hv⟩, rfl⟩
    · intro ha
      rcases ha with ⟨v, rfl⟩
      exact ⟨v.val, v.property, rfl⟩
  rw [hset]
  rfl

/--
%%handwave
name:
  Perron Dirichlet candidate
statement:
  The Perron Dirichlet candidate is the Perron envelope inside the domain and
  the prescribed boundary function outside the domain.
-/
noncomputable def perronDirichletCandidate {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronDomain X) (φ : PerronBoundaryData Ω) : X → ℝ :=
  by
    classical
    exact fun x ↦ if x ∈ Ω.carrier then perronEnvelope Ω φ x else φ x

/--
%%handwave
name:
  The Perron Dirichlet candidate equals the envelope inside the domain
statement:
  For every \(x\in\Omega\),
  \[
    U_\varphi(x)=\mathcal P_\varphi(x),
  \]
  where \(U_\varphi\) is the Perron Dirichlet candidate and
  \(\mathcal P_\varphi\) the Perron envelope.
proof:
  This is the interior branch of the piecewise definition of
  \(U_\varphi\).
-/
theorem perronDirichletCandidate_eq_envelope_of_mem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronDomain X) (φ : PerronBoundaryData Ω) {x : X}
    (hx : x ∈ Ω.carrier) :
    perronDirichletCandidate Ω φ x = perronEnvelope Ω φ x := by
  simp [perronDirichletCandidate, hx]

/--
%%handwave
name:
  The Perron Dirichlet candidate equals the boundary data outside the domain
statement:
  For every \(x\notin\Omega\),
  \[
    U_\varphi(x)=\varphi(x).
  \]
proof:
  This is the exterior branch of the piecewise definition of the Dirichlet
  candidate.
-/
theorem perronDirichletCandidate_eq_boundaryData_of_not_mem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronDomain X) (φ : PerronBoundaryData Ω) {x : X}
    (hx : x ∉ Ω.carrier) :
    perronDirichletCandidate Ω φ x = φ x := by
  simp [perronDirichletCandidate, hx]

/--
%%handwave
name:
  A Perron domain is disjoint from its boundary
statement:
  If \(x\in\partial\Omega\) for a Perron domain \(\Omega\), then
  \(x\notin\Omega\).
proof:
  The carrier of a Perron domain is open, and every open set is disjoint
  from its frontier.
-/
theorem PerronDomain.not_mem_carrier_of_mem_boundary
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronDomain X) {x : X} (hx : x ∈ Ω.boundary) :
    x ∉ Ω.carrier := by
  intro hxΩ
  have hx_inter : x ∈ Ω.carrier ∩ frontier Ω.carrier := ⟨hxΩ, hx⟩
  simp [Ω.isOpen.inter_frontier_eq] at hx_inter

/--
%%handwave
name:
  Harmonic Dirichlet problem
statement:
  A function solves the harmonic Dirichlet problem on a Perron domain when it
  is harmonic in the domain, continuous on the closed domain, and assumes the
  prescribed boundary values.
-/
def SolvesHarmonicDirichletProblem {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronDomain X) (φ : PerronBoundaryData Ω) (u : X → ℝ) : Prop :=
  IsHarmonicOnSurface Ω.carrier u ∧
    ContinuousOn u (closure Ω.carrier) ∧
      ∀ x ∈ Ω.boundary, u x = φ x

/--
%%handwave
name:
  Dirichlet solutions obey upper boundary bounds
statement:
  If a solution of the harmonic Dirichlet problem has boundary values bounded
  above by a constant \(M\), then the solution is bounded above by \(M\) on
  the domain.
proof:
  Apply the componentwise harmonic maximum principle to \(u-M\).  On the
  boundary this difference is nonpositive because the solution assumes the
  prescribed boundary values.
-/
theorem solvesHarmonicDirichletProblem_le_of_boundary_le
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] {Ω : PerronDomain X} {φ : PerronBoundaryData Ω}
    {u : X → ℝ} (hu : SolvesHarmonicDirichletProblem Ω φ u)
    (hΩ_geometry : HasComponentwiseMaximumPrincipleGeometry Ω.carrier)
    {M : ℝ} (hM : ∀ x ∈ Ω.boundary, φ x ≤ M) :
    ∀ x ∈ Ω.carrier, u x ≤ M := by
  have hdiff_harmonic :
      IsHarmonicOnSurface Ω.carrier (fun x ↦ u x - M) :=
    harmonicOnSurface_sub hu.1 (harmonicOnSurface_const Ω.carrier M)
  have hdiff_continuous :
      ContinuousOn (fun x ↦ u x - M) (closure Ω.carrier) :=
    hu.2.1.sub continuousOn_const
  have hdiff_boundary : ∀ x ∈ frontier Ω.carrier, u x - M ≤ 0 := by
    intro x hx
    have hx_boundary : x ∈ Ω.boundary := by
      simpa [PerronDomain.boundary] using hx
    have hux : u x = φ x := hu.2.2 x hx_boundary
    linarith [hM x hx_boundary]
  have hdiff_nonpositive :
      ∀ x ∈ Ω.carrier, u x - M ≤ 0 :=
    harmonic_nonpositive_of_boundary_nonpositive_componentwise
      hΩ_geometry hdiff_harmonic hdiff_continuous hdiff_boundary
  intro x hx
  linarith [hdiff_nonpositive x hx]

/--
%%handwave
name:
  Dirichlet solutions obey lower boundary bounds
statement:
  If a solution of the harmonic Dirichlet problem has boundary values bounded
  below by a constant \(m\), then the solution is bounded below by \(m\) on
  the domain.
proof:
  Apply the harmonic maximum principle to \(m-u\).  On the boundary this
  difference is nonpositive because the solution assumes the prescribed
  boundary values.
-/
theorem le_solvesHarmonicDirichletProblem_of_boundary_le
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] {Ω : PerronDomain X} {φ : PerronBoundaryData Ω}
    {u : X → ℝ} (hu : SolvesHarmonicDirichletProblem Ω φ u)
    (hΩ_geometry : HasComponentwiseMaximumPrincipleGeometry Ω.carrier)
    {m : ℝ} (hm : ∀ x ∈ Ω.boundary, m ≤ φ x) :
    ∀ x ∈ Ω.carrier, m ≤ u x := by
  have hdiff_harmonic :
      IsHarmonicOnSurface Ω.carrier (fun x ↦ m - u x) :=
    harmonicOnSurface_sub (harmonicOnSurface_const Ω.carrier m) hu.1
  have hdiff_continuous :
      ContinuousOn (fun x ↦ m - u x) (closure Ω.carrier) :=
    continuousOn_const.sub hu.2.1
  have hdiff_boundary : ∀ x ∈ frontier Ω.carrier, m - u x ≤ 0 := by
    intro x hx
    have hx_boundary : x ∈ Ω.boundary := by
      simpa [PerronDomain.boundary] using hx
    have hux : u x = φ x := hu.2.2 x hx_boundary
    linarith [hm x hx_boundary]
  have hdiff_nonpositive :
      ∀ x ∈ Ω.carrier, m - u x ≤ 0 :=
    harmonic_nonpositive_of_boundary_nonpositive_componentwise
      hΩ_geometry hdiff_harmonic hdiff_continuous hdiff_boundary
  intro x hx
  linarith [hdiff_nonpositive x hx]

/--
%%handwave
name:
  Dirichlet solutions compare below harmonic barriers
statement:
  If a harmonic Dirichlet solution has boundary values at most those of a
  harmonic comparison function, then the solution is at most that comparison
  function throughout the domain.
proof:
  Apply the componentwise harmonic maximum principle to the difference between
  the solution and the harmonic comparison function.  On the boundary, the
  solution assumes the prescribed boundary data, so the assumed boundary
  inequality makes this difference nonpositive.
-/
theorem solvesHarmonicDirichletProblem_le_harmonic_of_boundary_le
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] {Ω : PerronDomain X} {φ : PerronBoundaryData Ω}
    {u h : X → ℝ} (hu : SolvesHarmonicDirichletProblem Ω φ u)
    (hΩ_geometry : HasComponentwiseMaximumPrincipleGeometry Ω.carrier)
    (hharm : IsHarmonicOnSurface Ω.carrier h)
    (hcont : ContinuousOn h (closure Ω.carrier))
    (hboundary : ∀ x ∈ Ω.boundary, φ x ≤ h x) :
    ∀ x ∈ Ω.carrier, u x ≤ h x := by
  have hdiff_harmonic :
      IsHarmonicOnSurface Ω.carrier (fun x ↦ u x - h x) :=
    harmonicOnSurface_sub hu.1 hharm
  have hdiff_continuous :
      ContinuousOn (fun x ↦ u x - h x) (closure Ω.carrier) :=
    hu.2.1.sub hcont
  have hdiff_boundary : ∀ x ∈ frontier Ω.carrier, u x - h x ≤ 0 := by
    intro x hx
    have hx_boundary : x ∈ Ω.boundary := by
      simpa [PerronDomain.boundary] using hx
    have hux : u x = φ x := hu.2.2 x hx_boundary
    linarith [hboundary x hx_boundary]
  have hdiff_nonpositive :
      ∀ x ∈ Ω.carrier, u x - h x ≤ 0 :=
    harmonic_nonpositive_of_boundary_nonpositive_componentwise
      hΩ_geometry hdiff_harmonic hdiff_continuous hdiff_boundary
  intro x hx
  linarith [hdiff_nonpositive x hx]

/--
%%handwave
name:
  Harmonic barriers compare below Dirichlet solutions
statement:
  If a harmonic comparison function is at most the boundary values of a
  harmonic Dirichlet solution, then it is at most that solution throughout the
  domain.
proof:
  Apply the componentwise harmonic maximum principle to the difference between
  the comparison function and the solution.  The boundary inequality and the
  boundary trace of the Dirichlet solution make this difference nonpositive
  on the frontier.
-/
theorem harmonic_le_solvesHarmonicDirichletProblem_of_boundary_le
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] {Ω : PerronDomain X} {φ : PerronBoundaryData Ω}
    {u h : X → ℝ} (hu : SolvesHarmonicDirichletProblem Ω φ u)
    (hΩ_geometry : HasComponentwiseMaximumPrincipleGeometry Ω.carrier)
    (hharm : IsHarmonicOnSurface Ω.carrier h)
    (hcont : ContinuousOn h (closure Ω.carrier))
    (hboundary : ∀ x ∈ Ω.boundary, h x ≤ φ x) :
    ∀ x ∈ Ω.carrier, h x ≤ u x := by
  have hdiff_harmonic :
      IsHarmonicOnSurface Ω.carrier (fun x ↦ h x - u x) :=
    harmonicOnSurface_sub hharm hu.1
  have hdiff_continuous :
      ContinuousOn (fun x ↦ h x - u x) (closure Ω.carrier) :=
    hcont.sub hu.2.1
  have hdiff_boundary : ∀ x ∈ frontier Ω.carrier, h x - u x ≤ 0 := by
    intro x hx
    have hx_boundary : x ∈ Ω.boundary := by
      simpa [PerronDomain.boundary] using hx
    have hux : u x = φ x := hu.2.2 x hx_boundary
    linarith [hboundary x hx_boundary]
  have hdiff_nonpositive :
      ∀ x ∈ Ω.carrier, h x - u x ≤ 0 :=
    harmonic_nonpositive_of_boundary_nonpositive_componentwise
      hΩ_geometry hdiff_harmonic hdiff_continuous hdiff_boundary
  intro x hx
  linarith [hdiff_nonpositive x hx]

/--
%%handwave
name:
  Harmonic Dirichlet solutions are unique on the domain
statement:
  Two harmonic Dirichlet solutions with the same boundary data agree on the
  Perron domain.
proof:
  Compare the first solution below the second using the harmonic comparison
  principle, and then compare the second below the first.  The two boundary
  traces are the same prescribed boundary function.
-/
theorem solvesHarmonicDirichletProblem_eqOn_of_same_boundary
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] {Ω : PerronDomain X} {φ : PerronBoundaryData Ω}
    {u v : X → ℝ}
    (hu : SolvesHarmonicDirichletProblem Ω φ u)
    (hv : SolvesHarmonicDirichletProblem Ω φ v)
    (hΩ_geometry : HasComponentwiseMaximumPrincipleGeometry Ω.carrier) :
    Set.EqOn u v Ω.carrier := by
  have huv : ∀ x ∈ Ω.carrier, u x ≤ v x :=
    solvesHarmonicDirichletProblem_le_harmonic_of_boundary_le
      hu hΩ_geometry hv.1 hv.2.1 (by
        intro x hx
        have hvx : v x = φ x := hv.2.2 x hx
        linarith)
  have hvu : ∀ x ∈ Ω.carrier, v x ≤ u x :=
    solvesHarmonicDirichletProblem_le_harmonic_of_boundary_le
      hv hΩ_geometry hu.1 hu.2.1 (by
        intro x hx
        have hux : u x = φ x := hu.2.2 x hx
        linarith)
  intro x hx
  exact le_antisymm (huv x hx) (hvu x hx)

/--
%%handwave
name:
  Harmonic Dirichlet solution
statement:
  A harmonic Dirichlet solution is a function satisfying the harmonic
  Dirichlet problem on the Perron domain.
-/
structure HarmonicDirichletSolution {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronDomain X) (φ : PerronBoundaryData Ω) where
  /-- The solution function. -/
  potential : X → ℝ
  /-- The solution satisfies the harmonic Dirichlet problem. -/
  solves : SolvesHarmonicDirichletProblem Ω φ potential

/--
%%handwave
name:
  Perron barrier at a boundary point
statement:
  A Perron barrier at a boundary point is a positive superharmonic function on
  the domain, continuous on the closed domain, that vanishes exactly at the
  chosen boundary point.
-/
def HasPerronBarrierAt {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronDomain X) (p : X) : Prop :=
  p ∈ Ω.boundary ∧
    ∃ b : X → ℝ,
      ContinuousOn b (closure Ω.carrier) ∧
        IsSuperharmonicOnSurface Ω.carrier b ∧
          b p = 0 ∧
            ∀ x ∈ closure Ω.carrier, x ≠ p → 0 < b x

/--
%%handwave
name:
  Local Perron barrier at a boundary point
statement:
  A local Perron barrier at a boundary point is a barrier defined on a
  neighborhood of the point: it is continuous up to the local closed domain,
  superharmonic in the local interior, vanishes at the chosen boundary point,
  and is positive at every other nearby closed-domain point.
-/
def HasLocalPerronBarrierAt {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronDomain X) (p : X) : Prop :=
  p ∈ Ω.boundary ∧
    ∃ N : Set X, IsOpen N ∧ p ∈ N ∧
      ∃ b : X → ℝ,
        ContinuousOn b (closure Ω.carrier ∩ N) ∧
          IsSuperharmonicOnSurface (Ω.carrier ∩ N) b ∧
            b p = 0 ∧
              ∀ x ∈ closure Ω.carrier ∩ N, x ≠ p → 0 < b x

/--
%%handwave
name:
  Global barriers are local barriers
statement:
  Every Perron barrier at a boundary point is also a local Perron barrier at
  that point.
proof:
  Take the local neighborhood to be the whole surface and restrict the
  continuity, superharmonicity, zero, and positivity properties of the
  global barrier.
-/
theorem hasLocalPerronBarrierAt_of_hasPerronBarrierAt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronDomain X) {p : X}
    (hp : HasPerronBarrierAt Ω p) :
    HasLocalPerronBarrierAt Ω p := by
  rcases hp with ⟨hp_boundary, b, hb_cont, hb_super, hb_zero, hb_pos⟩
  refine ⟨hp_boundary, Set.univ, isOpen_univ, trivial, b, ?_, ?_, hb_zero, ?_⟩
  · simpa using hb_cont
  · simpa using hb_super
  · intro x hx hxp
    exact hb_pos x (by simpa using hx) hxp

/--
%%handwave
name:
  Local barriers have positive compact floors
statement:
  A local barrier that is positive away from its marked boundary point has a
  uniform positive lower bound on every compact part of the local closed
  domain that avoids that point.
proof:
  If the compact set is empty, any positive constant works.  Otherwise the
  barrier attains its minimum there by compactness and continuity, and the
  assumed pointwise positivity makes that minimum positive.
-/
theorem localPerronBarrier_positive_floor_on_compact
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronDomain X) {p : X} {N K : Set X} {b : X → ℝ}
    (hb_cont : ContinuousOn b (closure Ω.carrier ∩ N))
    (hb_pos : ∀ x ∈ closure Ω.carrier ∩ N, x ≠ p → 0 < b x)
    (hK_compact : IsCompact K)
    (hK_subset : K ⊆ closure Ω.carrier ∩ N)
    (hp_not_mem : p ∉ K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, δ ≤ b x := by
  by_cases hK_nonempty : K.Nonempty
  · have hb_cont_K : ContinuousOn b K := hb_cont.mono hK_subset
    rcases hK_compact.exists_isMinOn hK_nonempty hb_cont_K with
      ⟨x₀, hx₀K, hx₀_min⟩
    have hx₀_ne : x₀ ≠ p := by
      intro hx₀p
      exact hp_not_mem (by simpa [hx₀p] using hx₀K)
    refine ⟨b x₀, hb_pos x₀ (hK_subset hx₀K) hx₀_ne, ?_⟩
    intro x hxK
    exact hx₀_min hxK
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x hxK
    exact False.elim (hK_nonempty ⟨x, hxK⟩)

/--
%%handwave
name:
  Local barriers have positive floors on shrink frontiers
statement:
  If an open neighborhood of the marked boundary point has compact closure
  contained in the local-barrier chart, then the local barrier has a uniform
  positive lower bound on the part of its frontier lying in the closed domain.
proof:
  The frontier is a closed subset of the compact closure of the shrunken
  neighborhood, hence compact.  It does not contain the marked point because
  the shrunken neighborhood is open and contains that point.  Therefore
  [the local barrier has a positive compact floor](lean:JJMath.Uniformization.localPerronBarrier_positive_floor_on_compact).
-/
theorem localPerronBarrier_positive_floor_on_frontier
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronDomain X) {p : X} {N V : Set X} {b : X → ℝ}
    (hb_cont : ContinuousOn b (closure Ω.carrier ∩ N))
    (hb_pos : ∀ x ∈ closure Ω.carrier ∩ N, x ≠ p → 0 < b x)
    (hV_open : IsOpen V) (hpV : p ∈ V)
    (hV_compact : IsCompact (closure V))
    (hV_closure_subset : closure V ⊆ N) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ closure Ω.carrier ∩ frontier V, δ ≤ b x := by
  let K : Set X := closure Ω.carrier ∩ frontier V
  have hfrontier_compact : IsCompact (frontier V) :=
    hV_compact.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hK_compact : IsCompact K := by
    simpa [K, Set.inter_comm] using hfrontier_compact.inter_right isClosed_closure
  have hK_subset : K ⊆ closure Ω.carrier ∩ N := by
    intro x hx
    exact ⟨hx.1, hV_closure_subset (frontier_subset_closure hx.2)⟩
  have hp_not_mem : p ∉ K := by
    intro hpK
    have hp_inter : p ∈ V ∩ frontier V := ⟨hpV, hpK.2⟩
    rw [hV_open.inter_frontier_eq] at hp_inter
    exact hp_inter
  exact localPerronBarrier_positive_floor_on_compact Ω hb_cont hb_pos
    hK_compact hK_subset hp_not_mem

/--
%%handwave
name:
  Truncated local barriers patch across a compact shrink
statement:
  A local Perron barrier on an open neighborhood can be truncated below its
  positive frontier floor on a compactly contained smaller neighborhood and
  extended by the truncation constant outside.  The result is continuous on
  the closed domain, locally superharmonic in the domain, zero at the marked
  point, and positive everywhere else on the closed domain.
proof:
  Use
  [the positive lower bound on the shrink frontier](lean:JJMath.Uniformization.localPerronBarrier_positive_floor_on_frontier)
  and choose a smaller positive truncation constant.  On the shrink the
  patched function is the minimum of the local barrier and that constant;
  outside it is the constant.  Near the frontier, the positive floor makes the
  two descriptions agree locally, so continuity and local superharmonicity
  glue.
-/
theorem localPerronBarrier_truncated_patch_from_compact_shrink
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronDomain X) {p : X} {N V : Set X} {b : X → ℝ}
    (_hN_open : IsOpen N)
    (hb_cont : ContinuousOn b (closure Ω.carrier ∩ N))
    (hb_super : IsSuperharmonicOnSurface (Ω.carrier ∩ N) b)
    (hb_zero : b p = 0)
    (hb_pos : ∀ x ∈ closure Ω.carrier ∩ N, x ≠ p → 0 < b x)
    (hV_open : IsOpen V) (hpV : p ∈ V)
    (hV_closure_subset : closure V ⊆ N)
    (hV_compact : IsCompact (closure V)) :
    ∃ B : X → ℝ,
      ContinuousOn B (closure Ω.carrier) ∧
        (∀ x ∈ Ω.carrier, ∃ M : Set X, IsOpen M ∧ x ∈ M ∧
          IsSuperharmonicOnSurface (Ω.carrier ∩ M) B) ∧
          B p = 0 ∧
            ∀ x ∈ closure Ω.carrier, x ≠ p → 0 < B x := by
  classical
  rcases localPerronBarrier_positive_floor_on_frontier Ω hb_cont hb_pos
      hV_open hpV hV_compact hV_closure_subset with
    ⟨δ, hδpos, hδ_floor⟩
  let η : ℝ := δ / 2
  let B : X → ℝ := fun x ↦ if x ∈ V then b x ⊓ η else η
  have hηpos : 0 < η := by
    dsimp [η]
    linarith
  have hηnonneg : 0 ≤ η := le_of_lt hηpos
  have hηleδ : η ≤ δ := by
    dsimp [η]
    linarith
  have hV_subset_N : V ⊆ N := by
    intro x hxV
    exact hV_closure_subset (subset_closure hxV)
  have htrunc_super_N :
      IsSuperharmonicOnSurface (Ω.carrier ∩ N) (fun x ↦ b x ⊓ η) :=
    superharmonicOnSurface_inf_const η hb_super
  refine ⟨B, ?_, ?_, ?_, ?_⟩
  · have hb_trunc_cont :
        ContinuousOn (fun x ↦ b x ⊓ η) (closure Ω.carrier ∩ closure V) := by
      have hb_closureV :
          ContinuousOn b (closure Ω.carrier ∩ closure V) :=
        hb_cont.mono (by
          intro x hx
          exact ⟨hx.1, hV_closure_subset hx.2⟩)
      exact hb_closureV.inf continuousOn_const
    have hconst_cont :
        ContinuousOn (fun _ : X ↦ η)
          (closure Ω.carrier ∩ closure {x : X | ¬ x ∈ V}) :=
      continuousOn_const
    have hfront :
        ∀ x ∈ closure Ω.carrier ∩ frontier {x : X | x ∈ V},
          (fun x ↦ b x ⊓ η) x = (fun _ : X ↦ η) x := by
      intro x hx
      have hxfront : x ∈ frontier V := by
        simpa only [Set.setOf_mem_eq] using hx.2
      have hδle : δ ≤ b x := hδ_floor x ⟨hx.1, hxfront⟩
      have hηle : η ≤ b x := le_trans hηleδ hδle
      exact inf_eq_right.mpr hηle
    simpa [B] using
      ContinuousOn.if hfront hb_trunc_cont hconst_cont
  · intro x hxΩ
    by_cases hxV : x ∈ V
    · refine ⟨V, hV_open, hxV, ?_⟩
      have htrunc_super_V :
          IsSuperharmonicOnSurface (Ω.carrier ∩ V) (fun y ↦ b y ⊓ η) :=
        superharmonicOnSurface_mono (by
          intro y hy
          exact ⟨hy.1, hV_subset_N hy.2⟩) htrunc_super_N
      exact subharmonicOnSurface_congr_on htrunc_super_V (by
        intro y hy
        dsimp [B]
        rw [if_pos hy.2])
    · by_cases hx_closureV : x ∈ closure V
      · have hxfront : x ∈ frontier V := by
          rw [frontier_eq_closure_inter_closure]
          exact ⟨hx_closureV, subset_closure hxV⟩
        have hxS : x ∈ closure Ω.carrier ∩ N := by
          exact ⟨subset_closure hxΩ, hV_closure_subset hx_closureV⟩
        have hδle : δ ≤ b x := hδ_floor x ⟨subset_closure hxΩ, hxfront⟩
        have hηlt_bx : η < b x := lt_of_lt_of_le (by dsimp [η]; linarith) hδle
        have hcontx : ContinuousWithinAt b (closure Ω.carrier ∩ N) x :=
          hb_cont.continuousWithinAt hxS
        have hpre :
            b ⁻¹' Set.Ioi η ∈ 𝓝[closure Ω.carrier ∩ N] x :=
          hcontx.preimage_mem_nhdsWithin (Ioi_mem_nhds hηlt_bx)
        rw [mem_nhdsWithin] at hpre
        rcases hpre with ⟨M, hM_open, hxM, hM_sub⟩
        refine ⟨M, hM_open, hxM, ?_⟩
        have hconst_super :
            IsSuperharmonicOnSurface (Ω.carrier ∩ M) (fun _ : X ↦ η) :=
          superharmonicOnSurface_const (Ω.carrier ∩ M) η
        exact subharmonicOnSurface_congr_on hconst_super (by
          intro y hy
          dsimp [B]
          by_cases hyV : y ∈ V
          · have hyS : y ∈ closure Ω.carrier ∩ N :=
              ⟨subset_closure hy.1, hV_subset_N hyV⟩
            have hηlt_by : η < b y :=
              hM_sub ⟨hy.2, hyS⟩
            rw [if_pos hyV]
            have hmin : b y ⊓ η = η := inf_eq_right.mpr (le_of_lt hηlt_by)
            simp [hmin]
          · rw [if_neg hyV])
      · have hx_comp : x ∈ (closure V)ᶜ := by simpa using hx_closureV
        refine ⟨(closure V)ᶜ, isOpen_compl_iff.mpr isClosed_closure, hx_comp, ?_⟩
        have hconst_super :
            IsSuperharmonicOnSurface (Ω.carrier ∩ (closure V)ᶜ)
              (fun _ : X ↦ η) :=
          superharmonicOnSurface_const (Ω.carrier ∩ (closure V)ᶜ) η
        exact subharmonicOnSurface_congr_on hconst_super (by
          intro y hy
          dsimp [B]
          have hy_not_V : y ∉ V := by
            intro hyV
            exact hy.2 (subset_closure hyV)
          rw [if_neg hy_not_V])
  · dsimp [B]
    rw [if_pos hpV, hb_zero]
    exact inf_eq_left.mpr hηnonneg
  · intro x hxcl hxp
    dsimp [B]
    by_cases hxV : x ∈ V
    · have hxN : x ∈ N := hV_subset_N hxV
      have hbpos : 0 < b x := hb_pos x ⟨hxcl, hxN⟩ hxp
      rw [if_pos hxV]
      exact lt_min hbpos hηpos
    · rw [if_neg hxV]
      exact hηpos

/--
%%handwave
name:
  A local barrier has a compactly patched representative
statement:
  A local Perron barrier at a boundary point of a relatively compact domain
  can be patched to a function on the closed domain that is continuous there,
  locally superharmonic in the domain, vanishes at the chosen boundary point,
  and is positive at every other point of the closed domain.
proof:
  Shrink the barrier neighborhood around the boundary point.  On the compact
  frontier of the shrunken neighborhood, the local barrier has a
  [positive lower bound](lean:JJMath.Uniformization.localPerronBarrier_positive_floor_on_frontier).
  Truncate the local barrier by a constant below this bound and extend by that
  constant outside the smaller neighborhood.  The patched function is locally
  either the truncated local barrier or the constant function, hence locally
  superharmonic, and the choice of the constant preserves positivity away from
  the boundary point.
-/
theorem localPerronBarrierAt_exists_global_locally_superharmonic_patch
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronDomain X) {p : X}
    (hp : HasLocalPerronBarrierAt Ω p) :
    ∃ B : X → ℝ,
      ContinuousOn B (closure Ω.carrier) ∧
        (∀ x ∈ Ω.carrier, ∃ N : Set X, IsOpen N ∧ x ∈ N ∧
          IsSuperharmonicOnSurface (Ω.carrier ∩ N) B) ∧
          B p = 0 ∧
            ∀ x ∈ closure Ω.carrier, x ≠ p → 0 < B x := by
  rcases hp with
    ⟨_hp_boundary, N, hN_open, hpN, b, hb_cont, hb_super, hb_zero, hb_pos⟩
  rcases exists_surface_open_nhds_isCompact_closure_subset hN_open hpN with
    ⟨V, hV_open, hpV, hV_closure_subset, hV_compact⟩
  exact localPerronBarrier_truncated_patch_from_compact_shrink Ω
    hN_open hb_cont hb_super hb_zero hb_pos
    hV_open hpV hV_closure_subset hV_compact

/--
%%handwave
name:
  Local barriers globalize
statement:
  A local Perron barrier at a boundary point of a relatively compact domain
  extends to a global Perron barrier.
proof:
  First obtain
  [a compactly patched representative](lean:JJMath.Uniformization.localPerronBarrierAt_exists_global_locally_superharmonic_patch)
  of the local barrier.  Its local superharmonicity globalizes because
  [locally superharmonic functions are superharmonic](lean:JJMath.Uniformization.superharmonicOnSurface_of_locally).
-/
theorem localPerronBarrierAt_globalizes
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronDomain X) {p : X}
    (hp : HasLocalPerronBarrierAt Ω p) :
    HasPerronBarrierAt Ω p := by
  rcases localPerronBarrierAt_exists_global_locally_superharmonic_patch Ω hp with
    ⟨B, hB_cont, hB_local_super, hB_zero, hB_pos⟩
  refine ⟨hp.1, B, hB_cont, ?_, hB_zero, hB_pos⟩
  exact superharmonicOnSurface_of_locally Ω.isOpen hB_local_super

/--
%%handwave
name:
  Perron-regular boundary
statement:
  A Perron domain is regular for Perron's method when it has the componentwise
  geometry needed for the maximum principle and every boundary point admits a
  Perron barrier.
-/
def PerronRegularBoundary {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronDomain X) : Prop :=
  HasComponentwiseMaximumPrincipleGeometry Ω.carrier ∧
    ∀ p ∈ Ω.boundary, HasPerronBarrierAt Ω p

/--
%%handwave
name:
  Regular boundaries have local barriers
statement:
  Every boundary point of a Perron-regular domain admits a local Perron
  barrier.
proof:
  Regularity supplies a global Perron barrier at each boundary point, and
  every global barrier is a local one.
-/
theorem perronRegularBoundary_hasLocalBarriers
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronDomain X) (hΩreg : PerronRegularBoundary Ω) :
    ∀ p ∈ Ω.boundary, HasLocalPerronBarrierAt Ω p := by
  intro p hp
  exact hasLocalPerronBarrierAt_of_hasPerronBarrierAt Ω (hΩreg.2 p hp)

/--
%%handwave
name:
  Lower barrier calibration
statement:
  If \(b\) is a Perron barrier at \(p\), then for every \(\varepsilon>0\)
  there is a nonnegative constant \(C\) such that
  \(\varphi(p)-\varepsilon/2-Cb\) lies below the prescribed boundary data on
  the whole boundary.
proof:
  Let \(A=\varphi(p)-\varepsilon/2\).  Near \(p\), boundary-continuity of
  \(\varphi\) gives \(A<\varphi\).  On the compact remainder where
  \(\varphi\le A\), the barrier has a positive minimum and \(A-\varphi\) has
  a finite maximum.  Taking \(C\) to be the quotient of these two extrema gives
  the global boundary inequality.
-/
theorem perronBarrier_lower_boundary_calibration
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronDomain X) (φ : PerronBoundaryData Ω)
    {p : X} (_hp_boundary : p ∈ Ω.boundary)
    {b : X → ℝ}
    (hb_cont : ContinuousOn b (closure Ω.carrier))
    (_hb_super : IsSuperharmonicOnSurface Ω.carrier b)
    (hb_zero : b p = 0)
    (hb_pos : ∀ x ∈ closure Ω.carrier, x ≠ p → 0 < b x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ Ω.boundary, φ p - ε / 2 - C * b x ≤ φ x := by
  let A : ℝ := φ p - ε / 2
  have hA_lt : A < φ p := by
    dsimp [A]
    linarith
  let K : Set X := Ω.boundary ∩ (φ : X → ℝ) ⁻¹' Set.Iic A
  have hK_subset_boundary : K ⊆ Ω.boundary := by
    intro x hx
    exact hx.1
  have hboundary_closed : IsClosed Ω.boundary := by
    simpa [PerronDomain.boundary] using (isClosed_frontier : IsClosed (frontier Ω.carrier))
  have hK_closed : IsClosed K := by
    simpa [K] using
      φ.continuous_boundary.preimage_isClosed_of_isClosed hboundary_closed isClosed_Iic
  have hK_compact : IsCompact K :=
    (PerronDomain.compact_boundary Ω).of_isClosed_subset hK_closed hK_subset_boundary
  by_cases hK_nonempty : K.Nonempty
  · have hφ_cont_K : ContinuousOn (φ : X → ℝ) K :=
      φ.continuous_boundary.mono hK_subset_boundary
    have hK_closure_subset : K ⊆ closure Ω.carrier := by
      intro x hx
      have hx_frontier : x ∈ frontier Ω.carrier := by
        simpa [PerronDomain.boundary] using hx.1
      exact frontier_subset_closure hx_frontier
    have hb_cont_K : ContinuousOn b K := hb_cont.mono hK_closure_subset
    rcases hK_compact.exists_isMinOn hK_nonempty hb_cont_K with
      ⟨xδ, hxδK, hδ_min⟩
    let δ : ℝ := b xδ
    have hxδ_frontier : xδ ∈ frontier Ω.carrier := by
      simpa [PerronDomain.boundary] using hxδK.1
    have hxδ_closure : xδ ∈ closure Ω.carrier :=
      frontier_subset_closure hxδ_frontier
    have hxδ_ne : xδ ≠ p := by
      intro hxδ_eq
      have hp_le_A : φ p ≤ A := by
        simpa [hxδ_eq] using hxδK.2
      linarith
    have hδ_pos : 0 < δ := hb_pos xδ hxδ_closure hxδ_ne
    let gap : X → ℝ := fun x ↦ A - φ x
    have hgap_cont_K : ContinuousOn gap K :=
      continuousOn_const.sub hφ_cont_K
    rcases hK_compact.exists_isMaxOn hK_nonempty hgap_cont_K with
      ⟨xM, hxMK, hM_max⟩
    let M : ℝ := gap xM
    have hM_nonneg : 0 ≤ M := by
      dsimp [M, gap]
      exact sub_nonneg.mpr hxMK.2
    have hC_nonneg : 0 ≤ M / δ := div_nonneg hM_nonneg hδ_pos.le
    refine ⟨M / δ, hC_nonneg, ?_⟩
    intro x hx_boundary
    by_cases hxK : x ∈ K
    · have hδ_le_bx : δ ≤ b x := hδ_min hxK
      have hgap_le_M : A - φ x ≤ M := by
        simpa [gap, M] using hM_max hxK
      have hM_le_scaled : M ≤ (M / δ) * b x := by
        calc
          M = (M / δ) * δ := by
            exact (div_mul_cancel₀ M hδ_pos.ne').symm
          _ ≤ (M / δ) * b x :=
            mul_le_mul_of_nonneg_left hδ_le_bx hC_nonneg
      have hgap_le_scaled : A - φ x ≤ (M / δ) * b x :=
        hgap_le_M.trans hM_le_scaled
      change A - (M / δ) * b x ≤ φ x
      linarith
    · have hnot_le : ¬ φ x ≤ A := by
        intro hle
        exact hxK ⟨hx_boundary, hle⟩
      have hA_le : A ≤ φ x := le_of_lt (lt_of_not_ge hnot_le)
      have hx_frontier : x ∈ frontier Ω.carrier := by
        simpa [PerronDomain.boundary] using hx_boundary
      have hx_closure : x ∈ closure Ω.carrier := frontier_subset_closure hx_frontier
      have hb_nonneg : 0 ≤ b x := by
        by_cases hxp : x = p
        · simp [hxp, hb_zero]
        · exact le_of_lt (hb_pos x hx_closure hxp)
      have hscaled_nonneg : 0 ≤ (M / δ) * b x :=
        mul_nonneg hC_nonneg hb_nonneg
      change A - (M / δ) * b x ≤ φ x
      linarith
  · refine ⟨0, le_rfl, ?_⟩
    intro x hx_boundary
    have hxK : x ∉ K := fun hxK ↦ hK_nonempty ⟨x, hxK⟩
    have hnot_le : ¬ φ x ≤ A := by
      intro hle
      exact hxK ⟨hx_boundary, hle⟩
    have hA_le : A ≤ φ x := le_of_lt (lt_of_not_ge hnot_le)
    change A - 0 * b x ≤ φ x
    linarith

/--
%%handwave
name:
  Calibrated lower barriers are Perron subfunctions
statement:
  If \(b\) is a Perron barrier and
  \(\varphi(p)-\varepsilon/2-Cb\) lies below the prescribed boundary data on
  the boundary, then this affine barrier expression is Perron-admissible.
proof:
  Continuity follows from the continuity of \(b\).  Since \(b\) is
  superharmonic, \(-b\) is subharmonic, hence so is a nonnegative multiple of
  \(-b\) plus a constant.  The boundary inequality is exactly the assumed
  calibration.
-/
theorem perronBarrier_lower_affine_isPerronAdmissible
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronDomain X) (φ : PerronBoundaryData Ω)
    {p : X} {b : X → ℝ} {ε C : ℝ}
    (hb_cont : ContinuousOn b (closure Ω.carrier))
    (hb_super : IsSuperharmonicOnSurface Ω.carrier b)
    (hC : 0 ≤ C)
    (hboundary :
      ∀ x ∈ Ω.boundary, φ p - ε / 2 - C * b x ≤ φ x) :
    IsPerronAdmissible Ω φ (fun x ↦ φ p - ε / 2 - C * b x) := by
  refine ⟨?_, ?_, hboundary⟩
  · exact continuousOn_const.sub (continuousOn_const.mul hb_cont)
  · have hscaled :
        IsSubharmonicOnSurface Ω.carrier (fun x ↦ C * (-b x)) :=
      subharmonicOnSurface_const_mul_nonneg hC hb_super
    have hshifted :
        IsSubharmonicOnSurface Ω.carrier
          (fun x ↦ (φ p - ε / 2) + C * (-b x)) :=
      subharmonicOnSurface_const_add (φ p - ε / 2) hscaled
    simpa [sub_eq_add_neg, mul_neg] using hshifted

/--
%%handwave
name:
  Lower barrier subfunction
statement:
  A Perron barrier at \(p\) produces, for every \(\varepsilon>0\), a
  Perron-admissible subfunction of the form
  \(\varphi(p)-\varepsilon/2-Cb\).
proof:
  Combine the compact lower-barrier calibration with the affine-barrier
  admissibility lemma.
-/
theorem perronBarrier_lower_subfunction
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronDomain X) (φ : PerronBoundaryData Ω)
    {p : X} (hp : HasPerronBarrierAt Ω p) {ε : ℝ} (hε : 0 < ε) :
    ∃ b : X → ℝ, ∃ C : ℝ,
      ContinuousOn b (closure Ω.carrier) ∧
        b p = 0 ∧
          0 ≤ C ∧
            IsPerronAdmissible Ω φ
              (fun x ↦ φ p - ε / 2 - C * b x) := by
  rcases hp with
    ⟨hp_boundary, b, hb_cont, hb_super, hb_zero, hb_pos⟩
  rcases perronBarrier_lower_boundary_calibration Ω φ hp_boundary
      hb_cont hb_super hb_zero hb_pos hε with
    ⟨C, hC, hboundary⟩
  exact ⟨b, C, hb_cont, hb_zero, hC,
    perronBarrier_lower_affine_isPerronAdmissible Ω φ
      hb_cont hb_super hC hboundary⟩

/--
%%handwave
name:
  Upper barrier calibration
statement:
  If \(b\) is a Perron barrier at \(p\), then for every \(\varepsilon>0\)
  there is a nonnegative constant \(C\) such that
  \(\varphi\le \varphi(p)+\varepsilon/2+Cb\) on the whole boundary.
proof:
  Let \(A=\varphi(p)+\varepsilon/2\).  On the part of the boundary where
  \(\varphi\le A\), no barrier term is needed.  On the compact remainder
  where \(A\le\varphi\), the barrier has a positive minimum and
  \(\varphi-A\) has a finite maximum; their quotient gives \(C\).
-/
theorem perronBarrier_upper_boundary_calibration
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronDomain X) (φ : PerronBoundaryData Ω)
    {p : X} (_hp_boundary : p ∈ Ω.boundary)
    {b : X → ℝ}
    (hb_cont : ContinuousOn b (closure Ω.carrier))
    (_hb_super : IsSuperharmonicOnSurface Ω.carrier b)
    (hb_zero : b p = 0)
    (hb_pos : ∀ x ∈ closure Ω.carrier, x ≠ p → 0 < b x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ Ω.boundary, φ x ≤ φ p + ε / 2 + C * b x := by
  let A : ℝ := φ p + ε / 2
  have hp_lt_A : φ p < A := by
    dsimp [A]
    linarith
  let K : Set X := Ω.boundary ∩ (φ : X → ℝ) ⁻¹' Set.Ici A
  have hK_subset_boundary : K ⊆ Ω.boundary := by
    intro x hx
    exact hx.1
  have hboundary_closed : IsClosed Ω.boundary := by
    simpa [PerronDomain.boundary] using (isClosed_frontier : IsClosed (frontier Ω.carrier))
  have hK_closed : IsClosed K := by
    simpa [K] using
      φ.continuous_boundary.preimage_isClosed_of_isClosed hboundary_closed isClosed_Ici
  have hK_compact : IsCompact K :=
    (PerronDomain.compact_boundary Ω).of_isClosed_subset hK_closed hK_subset_boundary
  by_cases hK_nonempty : K.Nonempty
  · have hφ_cont_K : ContinuousOn (φ : X → ℝ) K :=
      φ.continuous_boundary.mono hK_subset_boundary
    have hK_closure_subset : K ⊆ closure Ω.carrier := by
      intro x hx
      have hx_frontier : x ∈ frontier Ω.carrier := by
        simpa [PerronDomain.boundary] using hx.1
      exact frontier_subset_closure hx_frontier
    have hb_cont_K : ContinuousOn b K := hb_cont.mono hK_closure_subset
    rcases hK_compact.exists_isMinOn hK_nonempty hb_cont_K with
      ⟨xδ, hxδK, hδ_min⟩
    let δ : ℝ := b xδ
    have hxδ_frontier : xδ ∈ frontier Ω.carrier := by
      simpa [PerronDomain.boundary] using hxδK.1
    have hxδ_closure : xδ ∈ closure Ω.carrier :=
      frontier_subset_closure hxδ_frontier
    have hxδ_ne : xδ ≠ p := by
      intro hxδ_eq
      have hA_le_p : A ≤ φ p := by
        simpa [hxδ_eq] using hxδK.2
      linarith
    have hδ_pos : 0 < δ := hb_pos xδ hxδ_closure hxδ_ne
    let gap : X → ℝ := fun x ↦ φ x - A
    have hgap_cont_K : ContinuousOn gap K :=
      hφ_cont_K.sub continuousOn_const
    rcases hK_compact.exists_isMaxOn hK_nonempty hgap_cont_K with
      ⟨xM, hxMK, hM_max⟩
    let M : ℝ := gap xM
    have hM_nonneg : 0 ≤ M := by
      dsimp [M, gap]
      exact sub_nonneg.mpr hxMK.2
    have hC_nonneg : 0 ≤ M / δ := div_nonneg hM_nonneg hδ_pos.le
    refine ⟨M / δ, hC_nonneg, ?_⟩
    intro x hx_boundary
    by_cases hxK : x ∈ K
    · have hδ_le_bx : δ ≤ b x := hδ_min hxK
      have hgap_le_M : φ x - A ≤ M := by
        simpa [gap, M] using hM_max hxK
      have hM_le_scaled : M ≤ (M / δ) * b x := by
        calc
          M = (M / δ) * δ := by
            exact (div_mul_cancel₀ M hδ_pos.ne').symm
          _ ≤ (M / δ) * b x :=
            mul_le_mul_of_nonneg_left hδ_le_bx hC_nonneg
      have hgap_le_scaled : φ x - A ≤ (M / δ) * b x :=
        hgap_le_M.trans hM_le_scaled
      change φ x ≤ A + (M / δ) * b x
      linarith
    · have hnot_le : ¬ A ≤ φ x := by
        intro hle
        exact hxK ⟨hx_boundary, hle⟩
      have hφ_le_A : φ x ≤ A := le_of_lt (lt_of_not_ge hnot_le)
      have hx_frontier : x ∈ frontier Ω.carrier := by
        simpa [PerronDomain.boundary] using hx_boundary
      have hx_closure : x ∈ closure Ω.carrier := frontier_subset_closure hx_frontier
      have hb_nonneg : 0 ≤ b x := by
        by_cases hxp : x = p
        · simp [hxp, hb_zero]
        · exact le_of_lt (hb_pos x hx_closure hxp)
      have hscaled_nonneg : 0 ≤ (M / δ) * b x :=
        mul_nonneg hC_nonneg hb_nonneg
      change φ x ≤ A + (M / δ) * b x
      linarith
  · refine ⟨0, le_rfl, ?_⟩
    intro x hx_boundary
    have hxK : x ∉ K := fun hxK ↦ hK_nonempty ⟨x, hxK⟩
    have hnot_le : ¬ A ≤ φ x := by
      intro hle
      exact hxK ⟨hx_boundary, hle⟩
    have hφ_le_A : φ x ≤ A := le_of_lt (lt_of_not_ge hnot_le)
    change φ x ≤ A + 0 * b x
    linarith

/--
%%handwave
name:
  Coordinate Perron disk
statement:
  A coordinate Perron disk is a Perron domain that is the inverse image of a
  Euclidean disk whose closed disk lies in the target of a complex chart.
-/
def IsCoordinatePerronDisk {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (D : PerronDomain X) : Prop :=
  ∃ e : OpenPartialHomeomorph X ℂ, e ∈ atlas ℂ X ∧
    ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧
      Metric.closedBall c r ⊆ e.target ∧
        D.carrier = e.source ∩ e ⁻¹' Metric.ball c r

/--
%%handwave
name:
  Harmonic replacement
statement:
  A harmonic replacement of a subharmonic function on a smaller domain agrees
  with the original function on the smaller boundary, is harmonic inside that
  smaller domain, and is used only on that smaller domain.
-/
def IsHarmonicReplacement {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (V : PerronDomain X) (v h : X → ℝ) : Prop :=
  IsHarmonicOnSurface V.carrier h ∧
    ContinuousOn h (closure V.carrier) ∧
      (∀ x ∈ V.boundary, h x = v x)

/--
%%handwave
name:
  Harmonic replacement patch
statement:
  The patched harmonic replacement is the harmonic replacement inside the
  smaller domain and the original function outside it.
-/
noncomputable def harmonicReplacementPatch {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (V : PerronDomain X) (v h : X → ℝ) : X → ℝ :=
  by
    classical
    exact fun x ↦ if x ∈ V.carrier then h x else v x

/--
%%handwave
name:
  A harmonic replacement patch equals the replacement inside
statement:
  If \(x\in V\), then the patch formed from an original function \(v\) and
  its harmonic replacement \(h\) satisfies
  \[
    \widetilde v(x)=h(x).
  \]
proof:
  This is the interior branch of the patch's piecewise definition.
-/
theorem harmonicReplacementPatch_eq_replacement_of_mem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (V : PerronDomain X) (v h : X → ℝ) {x : X}
    (hx : x ∈ V.carrier) :
    harmonicReplacementPatch V v h x = h x := by
  simp [harmonicReplacementPatch, hx]

/--
%%handwave
name:
  A harmonic replacement patch equals the original function outside
statement:
  If \(x\notin V\), then
  \[
    \widetilde v(x)=v(x).
  \]
proof:
  This is the exterior branch of the patch's piecewise definition.
-/
theorem harmonicReplacementPatch_eq_original_of_not_mem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (V : PerronDomain X) (v h : X → ℝ) {x : X}
    (hx : x ∉ V.carrier) :
    harmonicReplacementPatch V v h x = v x := by
  simp [harmonicReplacementPatch, hx]

/--
%%handwave
name:
  Boundary data pulls back to the Euclidean circle
statement:
  Continuous boundary data on a coordinate Perron disk pulls back through the
  chart to continuous boundary data on the Euclidean circle.
proof:
  The closed Euclidean disk lies inside the chart target, so the inverse chart
  is continuous on the boundary circle and maps that circle to the frontier of
  the surface disk.  Compose this map with the given continuous boundary data.
-/
theorem coordinate_disk_boundary_data_pullback_continuous
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (D : PerronDomain X) (e : OpenPartialHomeomorph X ℂ)
    (c : ℂ) {r : ℝ}
    (hclosed : Metric.closedBall c r ⊆ e.target)
    (hcarrier : D.carrier = e.source ∩ e ⁻¹' Metric.ball c r)
    (ψ : PerronBoundaryData D) :
    ContinuousOn (fun z : ℂ ↦ ψ (e.symm z)) (frontier (Metric.ball c r)) := by
  have hfrontier_target : frontier (Metric.ball c r) ⊆ e.target := by
    intro z hz
    exact hclosed (frontier_subset_closure.trans Metric.closure_ball_subset_closedBall hz)
  have himage : e.IsImage D.carrier (Metric.ball c r) := by
    intro x hx
    rw [hcarrier]
    simp [hx]
  have hmaps : Set.MapsTo e.symm (frontier (Metric.ball c r)) D.boundary := by
    intro z hz
    have hz_target : z ∈ e.target := hfrontier_target hz
    have hz_boundary : e.symm z ∈ frontier D.carrier :=
      (himage.frontier.symm_apply_mem_iff hz_target).2 hz
    simpa [PerronDomain.boundary] using hz_boundary
  simpa [Function.comp_def] using
    ψ.continuous_boundary.comp
      (e.continuousOn_symm.mono hfrontier_target) hmaps

/--
%%handwave
name:
  Closure of a coordinate disk stays in its chart
statement:
  If a coordinate Perron disk is cut out by a Euclidean disk whose closed disk
  lies in the chart target, then the closure of the surface disk lies in the
  chart source.
proof:
  The inverse chart sends the compact closed Euclidean disk to a compact,
  hence closed, subset of the Hausdorff surface.  The surface disk is contained
  in this compact set, so its closure is contained there, and the compact set
  lies in the chart source.
-/
theorem coordinate_disk_closure_subset_chart_source
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [T2Space X]
    (D : PerronDomain X) (e : OpenPartialHomeomorph X ℂ)
    (c : ℂ) {r : ℝ}
    (hclosed : Metric.closedBall c r ⊆ e.target)
    (hcarrier : D.carrier = e.source ∩ e ⁻¹' Metric.ball c r) :
    closure D.carrier ⊆ e.source := by
  let K : Set X := e.symm '' Metric.closedBall c r
  have hD_subset_K : D.carrier ⊆ K := by
    intro x hx
    have hx' : x ∈ e.source ∩ e ⁻¹' Metric.ball c r := by
      simpa [hcarrier] using hx
    refine ⟨e x, Metric.ball_subset_closedBall hx'.2, ?_⟩
    exact e.left_inv hx'.1
  have hK_compact : IsCompact K :=
    (isCompact_closedBall c r).image_of_continuousOn
      (e.continuousOn_symm.mono hclosed)
  have hclosure_subset_K : closure D.carrier ⊆ K :=
    closure_minimal hD_subset_K hK_compact.isClosed
  have hK_subset_source : K ⊆ e.source := by
    intro x hx
    rcases hx with ⟨z, hz, rfl⟩
    exact e.map_target (hclosed hz)
  exact hclosure_subset_K.trans hK_subset_source

/--
%%handwave
name:
  Euclidean disk solutions transport through a coordinate chart
statement:
  A Euclidean disk Dirichlet solution transported through the defining chart
  of a coordinate Perron disk solves the surface Dirichlet problem.
proof:
  Define the surface function by composing the Euclidean solution with the
  chart on the disk.  Harmonicity follows because
  [analytic precomposition preserves harmonicity](lean:JJMath.Uniformization.harmonicAt_comp_analyticAt)
  and [surface coordinate changes are analytic](lean:JJMath.Uniformization.chartTransition_analyticAt).
  Continuity up to the boundary uses that [the closure of the coordinate disk stays in the chart](lean:JJMath.Uniformization.coordinate_disk_closure_subset_chart_source);
  the boundary equality is the transported Euclidean boundary equality.
-/
theorem coordinate_euclidean_solution_solves_surface_dirichlet
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (D : PerronDomain X) (e : OpenPartialHomeomorph X ℂ)
    (he : e ∈ atlas ℂ X) (c : ℂ) {r : ℝ} (_hr : 0 < r)
    (hclosed : Metric.closedBall c r ⊆ e.target)
    (hcarrier : D.carrier = e.source ∩ e ⁻¹' Metric.ball c r)
    (ψ : PerronBoundaryData D) {uC : ℂ → ℝ}
    (huC : SolvesEuclideanDiskDirichletProblem c r
      (fun z : ℂ ↦ ψ (e.symm z)) uC) :
    ∃ u : X → ℝ, SolvesHarmonicDirichletProblem D ψ u := by
  let u : X → ℝ := fun x ↦ uC (e x)
  have himage : e.IsImage D.carrier (Metric.ball c r) := by
    intro x hx
    rw [hcarrier]
    simp [hx]
  have hclosure_source : closure D.carrier ⊆ e.source :=
    coordinate_disk_closure_subset_chart_source D e c hclosed hcarrier
  refine ⟨u, ?_, ?_, ?_⟩
  · intro f hf z hz
    have hz_target : z ∈ f.target := hz.1
    have hxD : f.symm z ∈ D.carrier := hz.2
    have hxD' : f.symm z ∈ e.source ∩ e ⁻¹' Metric.ball c r := by
      simpa [hcarrier] using hxD
    have hu_at :
        InnerProductSpace.HarmonicAt uC (e (f.symm z)) :=
      huC.1 (e (f.symm z)) hxD'.2
    have htransition :
        AnalyticAt ℂ (fun w : ℂ ↦ e (f.symm w)) z :=
      chartTransition_analyticAt f hf e he hz_target hxD'.1
    simpa [u] using harmonicAt_comp_analyticAt hu_at htransition
  · have hmaps_closure :
        Set.MapsTo e (closure D.carrier) (closure (Metric.ball c r)) := by
      intro x hx
      exact (himage.closure.apply_mem_iff (hclosure_source hx)).2 hx
    exact huC.2.1.comp (e.continuousOn.mono hclosure_source) hmaps_closure
  · intro x hx
    have hx_frontier : x ∈ frontier D.carrier := by
      simpa [PerronDomain.boundary] using hx
    have hx_source : x ∈ e.source :=
      hclosure_source (frontier_subset_closure hx_frontier)
    have hex_frontier : e x ∈ frontier (Metric.ball c r) :=
      (himage.frontier.apply_mem_iff hx_source).2 hx_frontier
    calc
      u x = uC (e x) := rfl
      _ = ψ (e.symm (e x)) := huC.2.2 (e x) hex_frontier
      _ = ψ x := by rw [e.left_inv hx_source]

/--
%%handwave
name:
  Coordinate disk Dirichlet solution
statement:
  The classical Poisson integral solves the continuous Dirichlet problem on a
  coordinate disk.
proof:
  In a chart, reduce the domain to an ordinary Euclidean disk.  Use the
  Poisson kernel to define the harmonic extension of the boundary values.
  The analytic work is the constructive existence theorem on the Euclidean
  disk and the transport back through the chart.
-/
theorem coordinate_disk_dirichlet_solution
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (D : PerronDomain X) (hD : IsCoordinatePerronDisk D)
    (ψ : PerronBoundaryData D) :
    ∃ h : X → ℝ, SolvesHarmonicDirichletProblem D ψ h := by
  rcases hD with ⟨e, he, c, r, hr, hclosed, hcarrier⟩
  let φ : ℂ → ℝ := fun z ↦ ψ (e.symm z)
  have hφ : ContinuousOn φ (frontier (Metric.ball c r)) := by
    exact coordinate_disk_boundary_data_pullback_continuous
      D e c hclosed hcarrier ψ
  rcases euclidean_disk_dirichlet_solution_by_poisson c hr φ hφ with ⟨uC, huC⟩
  exact coordinate_euclidean_solution_solves_surface_dirichlet
    D e he c hr hclosed hcarrier ψ huC

/--
%%handwave
name:
  Harmonic replacement exists
statement:
  On a coordinate disk, every continuous boundary value admits a harmonic
  replacement.
proof:
  In the chosen coordinate, solve the Euclidean disk problem by the Poisson
  integral, then transport the solution back to the surface.  The transported
  solution is harmonic in the coordinate disk and agrees with the prescribed
  function on the disk boundary.
-/
theorem harmonic_replacement_exists
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (V : PerronDomain X) (hV : IsCoordinatePerronDisk V)
    (v : X → ℝ) (hv : ContinuousOn v (closure V.carrier)) :
    ∃ h : X → ℝ, IsHarmonicReplacement V v h := by
  let ψ : PerronBoundaryData V :=
    { toFun := v
      continuous_boundary := by
        exact hv.mono frontier_subset_closure }
  rcases coordinate_disk_dirichlet_solution V hV ψ with ⟨h, hh⟩
  rcases hh with ⟨hharm, hcont, hboundary⟩
  refine ⟨h, hharm, hcont, ?_⟩
  intro x hx
  simpa [ψ] using hboundary x hx

/--
%%handwave
name:
  Harmonic replacement dominates the original subfunction
statement:
  If a Perron-admissible subfunction is harmonically replaced on a smaller
  domain compactly contained in the Perron domain, then the original
  subfunction is bounded above by its harmonic replacement inside the smaller
  domain.
proof:
  This is exactly the comparison principle in the definition of
  subharmonicity, applied on the smaller domain.  The boundary inequality is
  equality because the harmonic replacement has the original function as its
  boundary data.
-/
theorem harmonic_replacement_dominates_original
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω V : PerronDomain X) (φ : PerronBoundaryData Ω)
    (hVΩ : closure V.carrier ⊆ Ω.carrier)
    (hV_preconnected : IsPreconnected V.carrier)
    (hV_frontier_nonempty : (frontier V.carrier).Nonempty)
    {v h : X → ℝ}
    (hv : IsPerronAdmissible Ω φ v)
    (hh : IsHarmonicReplacement V v h) :
    ∀ x ∈ V.carrier, v x ≤ h x := by
  rcases hv with ⟨_, hsub, _⟩
  rcases hsub with ⟨_, hcomparison⟩
  rcases hh with ⟨hharm, hcont, hboundary⟩
  have hVΩ_carrier : V.carrier ⊆ Ω.carrier := by
    intro x hx
    exact hVΩ (subset_closure hx)
  exact hcomparison V.carrier V.isOpen hV_preconnected hV_frontier_nonempty
    hVΩ_carrier V.compact_closure hVΩ h hharm hcont
    (by
      intro x hx
      rw [hboundary x hx])

/--
%%handwave
name:
  Harmonic replacement dominates on the whole surface
statement:
  If a subharmonic function is harmonically replaced on a compact coordinate
  domain, then the original function is bounded above by its harmonic
  replacement inside that domain.
proof:
  Apply the harmonic comparison principle for the subharmonic function on the
  replacement domain itself.  The boundary inequality is equality because the
  replacement has the original function as its boundary value.
-/
theorem harmonic_replacement_dominates_original_on_univ
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (V : PerronDomain X)
    (hV_preconnected : IsPreconnected V.carrier)
    (hV_frontier_nonempty : (frontier V.carrier).Nonempty)
    {v h : X → ℝ}
    (hv : IsSubharmonicOnSurface (Set.univ : Set X) v)
    (hh : IsHarmonicReplacement V v h) :
    ∀ x ∈ V.carrier, v x ≤ h x := by
  rcases hv with ⟨_, hcomparison⟩
  rcases hh with ⟨hharm, hcont, hboundary⟩
  exact hcomparison V.carrier V.isOpen hV_preconnected hV_frontier_nonempty
    (by
      intro x _hx
      trivial)
    V.compact_closure
    (by
      intro x _hx
      trivial)
    h hharm hcont
    (by
      intro x hx
      rw [hboundary x (by simpa [PerronDomain.boundary] using hx)])

/--
%%handwave
name:
  Harmonic replacements are monotone in their boundary data
statement:
  If two harmonic replacements on the same connected replacement domain have
  ordered boundary data, then the replacements are ordered throughout the
  domain.
proof:
  Apply the harmonic maximum principle to the difference of the two
  replacements.  The boundary equality in the definition of harmonic
  replacement turns the boundary order of the original data into the boundary
  order of the harmonic functions.
-/
theorem harmonicReplacement_le_of_boundary_original_le
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (V : PerronDomain X)
    (hV_preconnected : IsPreconnected V.carrier)
    (hV_frontier_nonempty : (frontier V.carrier).Nonempty)
    {v₁ h₁ v₂ h₂ : X → ℝ}
    (hh₁ : IsHarmonicReplacement V v₁ h₁)
    (hh₂ : IsHarmonicReplacement V v₂ h₂)
    (hboundary_order : ∀ x ∈ V.boundary, v₁ x ≤ v₂ x) :
    ∀ x ∈ V.carrier, h₁ x ≤ h₂ x := by
  have hdiff_harmonic :
      IsHarmonicOnSurface V.carrier (fun x ↦ h₁ x - h₂ x) :=
    harmonicOnSurface_sub hh₁.1 hh₂.1
  have hdiff_continuous :
      ContinuousOn (fun x ↦ h₁ x - h₂ x) (closure V.carrier) :=
    hh₁.2.1.sub hh₂.2.1
  have hdiff_boundary : ∀ x ∈ frontier V.carrier, h₁ x - h₂ x ≤ 0 := by
    intro x hx
    have hx_boundary : x ∈ V.boundary := by
      simpa [PerronDomain.boundary] using hx
    have h₁_eq : h₁ x = v₁ x := hh₁.2.2 x hx_boundary
    have h₂_eq : h₂ x = v₂ x := hh₂.2.2 x hx_boundary
    have hv : v₁ x ≤ v₂ x := hboundary_order x hx_boundary
    linarith
  have hnonpos : ∀ x ∈ V.carrier, h₁ x - h₂ x ≤ 0 :=
    harmonic_nonpositive_of_boundary_nonpositive V.isOpen hV_preconnected
      V.compact_closure hV_frontier_nonempty hdiff_harmonic
      hdiff_continuous hdiff_boundary
  intro x hx
  linarith [hnonpos x hx]

/--
%%handwave
name:
  Harmonic replacement patch dominates the original subfunction
statement:
  The patched harmonic replacement is pointwise at least the original
  subfunction on the Perron domain.
proof:
  Inside the replacement domain, compare the subharmonic original function
  with its harmonic replacement using their equal boundary values.  Outside,
  the patch equals the original function.
-/
theorem harmonicReplacementPatch_ge_original
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω V : PerronDomain X) (φ : PerronBoundaryData Ω)
    (hVΩ : closure V.carrier ⊆ Ω.carrier)
    (hV_preconnected : IsPreconnected V.carrier)
    (hV_frontier_nonempty : (frontier V.carrier).Nonempty)
    {v h : X → ℝ}
    (hv : IsPerronAdmissible Ω φ v)
    (hh : IsHarmonicReplacement V v h) :
    ∀ x ∈ Ω.carrier, v x ≤ harmonicReplacementPatch V v h x := by
  intro x _hxΩ
  by_cases hxV : x ∈ V.carrier
  · rw [harmonicReplacementPatch_eq_replacement_of_mem V v h hxV]
    exact harmonic_replacement_dominates_original Ω V φ hVΩ
      hV_preconnected hV_frontier_nonempty hv hh x hxV
  · rw [harmonicReplacementPatch_eq_original_of_not_mem V v h hxV]

/--
%%handwave
name:
  Harmonic replacement patch preserves outer boundary bounds
statement:
  The patched harmonic replacement satisfies the same boundary upper bound as
  the original Perron-admissible subfunction on the outer Perron boundary.
proof:
  Since the smaller closed domain lies inside the Perron domain, an outer
  boundary point is not in the smaller domain.  The patch therefore equals the
  original subfunction there.
-/
theorem harmonicReplacementPatch_boundary_le
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω V : PerronDomain X) (φ : PerronBoundaryData Ω)
    (hVΩ : closure V.carrier ⊆ Ω.carrier)
    {v h : X → ℝ}
    (hv : IsPerronAdmissible Ω φ v) :
    ∀ x ∈ Ω.boundary, harmonicReplacementPatch V v h x ≤ φ x := by
  intro x hxΩbd
  have hx_not_V : x ∉ V.carrier := by
    intro hxV
    have hxΩ : x ∈ Ω.carrier := hVΩ (subset_closure hxV)
    exact Ω.not_mem_carrier_of_mem_boundary hxΩbd hxΩ
  rw [harmonicReplacementPatch_eq_original_of_not_mem V v h hx_not_V]
  exact hv.2.2 x hxΩbd

/--
%%handwave
name:
  Harmonic replacement patch is continuous on the closed Perron domain
statement:
  The patched harmonic replacement is continuous on the closed outer domain.
proof:
  Away from the smaller boundary this is local, since the patch is either the
  original continuous subfunction or the harmonic replacement.  On the smaller
  boundary, both functions are continuous up to the boundary and have the same
  boundary values.
-/
theorem harmonicReplacementPatch_continuousOn_closedDomain
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω V : PerronDomain X) (φ : PerronBoundaryData Ω)
    {v h : X → ℝ}
    (hv : IsPerronAdmissible Ω φ v)
    (hh : IsHarmonicReplacement V v h) :
    ContinuousOn (harmonicReplacementPatch V v h) (closure Ω.carrier) := by
  classical
  rcases hv with ⟨hv_cont, _hv_subharmonic, _hv_boundary⟩
  rcases hh with ⟨_hh_harmonic, hh_cont, hh_boundary⟩
  have heq : ∀ x ∈ closure Ω.carrier ∩ frontier V.carrier, h x = v x := by
    intro x hx
    exact hh_boundary x (by simpa [PerronDomain.boundary] using hx.2)
  have hh_cont' : ContinuousOn h (closure Ω.carrier ∩ closure V.carrier) :=
    hh_cont.mono (by
      intro x hx
      exact hx.2)
  have hv_cont' : ContinuousOn v (closure Ω.carrier ∩ closure V.carrierᶜ) :=
    hv_cont.mono (by
      intro x hx
      exact hx.1)
  simpa [harmonicReplacementPatch] using
    (ContinuousOn.piecewise (t := V.carrier) heq hh_cont' hv_cont')

/--
%%handwave
name:
  Harmonic replacement patch is upper semicontinuous on the Perron domain
statement:
  The patched harmonic replacement is upper semicontinuous on the outer
  Perron domain.
proof:
  This follows immediately from
  [continuity on the closed outer domain](lean:JJMath.Uniformization.harmonicReplacementPatch_continuousOn_closedDomain).
-/
theorem harmonicReplacementPatch_upperSemicontinuousOn
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω V : PerronDomain X) (φ : PerronBoundaryData Ω)
    {v h : X → ℝ}
    (hv : IsPerronAdmissible Ω φ v)
    (hh : IsHarmonicReplacement V v h) :
    UpperSemicontinuousOn (harmonicReplacementPatch V v h) Ω.carrier := by
  have hcont_closed :
      ContinuousOn (harmonicReplacementPatch V v h) (closure Ω.carrier) :=
    harmonicReplacementPatch_continuousOn_closedDomain Ω V φ hv hh
  have hcont :
      ContinuousOn (harmonicReplacementPatch V v h) Ω.carrier :=
    hcont_closed.mono subset_closure
  exact hcont.upperSemicontinuousOn

/--
%%handwave
name:
  A patch boundary bound implies the original boundary bound
statement:
  If a harmonic test function bounds the patched replacement on the boundary
  of a test domain contained in the Perron domain, then it also bounds the
  original subfunction on that boundary.
proof:
  The patched replacement dominates the original subfunction throughout the
  outer Perron domain.
-/
theorem harmonicReplacementPatch_frontier_bound_original
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω V : PerronDomain X) (φ : PerronBoundaryData Ω)
    (hVΩ : closure V.carrier ⊆ Ω.carrier)
    (hV_preconnected : IsPreconnected V.carrier)
    (hV_frontier_nonempty : (frontier V.carrier).Nonempty)
    {v h g : X → ℝ} {W : Set X}
    (hv : IsPerronAdmissible Ω φ v)
    (hh : IsHarmonicReplacement V v h)
    (hWΩ : closure W ⊆ Ω.carrier)
    (hbd : ∀ x ∈ frontier W, harmonicReplacementPatch V v h x ≤ g x) :
    ∀ x ∈ frontier W, v x ≤ g x := by
  intro x hxW
  have hxΩ : x ∈ Ω.carrier := hWΩ (frontier_subset_closure hxW)
  exact (harmonicReplacementPatch_ge_original Ω V φ hVΩ
      hV_preconnected hV_frontier_nonempty hv hh x hxΩ).trans
    (hbd x hxW)

/--
%%handwave
name:
  Patch boundary bounds compare the original subfunction inside
statement:
  If a harmonic test function bounds the patched replacement on the boundary
  of a relatively compact test domain, then the original subfunction is bounded
  by that test function throughout the test domain.
proof:
  The boundary hypothesis gives
  [the same boundary bound for the original subfunction](lean:JJMath.Uniformization.harmonicReplacementPatch_frontier_bound_original).
  The result then follows from the subharmonic comparison principle for the
  original Perron-admissible subfunction.
-/
theorem original_le_test_harmonic_of_patch_frontier_bound
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω V : PerronDomain X) (φ : PerronBoundaryData Ω)
    (hVΩ : closure V.carrier ⊆ Ω.carrier)
    (hV_preconnected : IsPreconnected V.carrier)
    (hV_frontier_nonempty : (frontier V.carrier).Nonempty)
    {v h g : X → ℝ} {W : Set X}
    (hv : IsPerronAdmissible Ω φ v)
    (hh : IsHarmonicReplacement V v h)
    (hW_open : IsOpen W)
    (hW_preconnected : IsPreconnected W)
    (hW_frontier_nonempty : (frontier W).Nonempty)
    (hW_subset : W ⊆ Ω.carrier)
    (hW_compact : IsCompact (closure W))
    (hWΩ : closure W ⊆ Ω.carrier)
    (hg_harmonic : IsHarmonicOnSurface W g)
    (hg_continuous : ContinuousOn g (closure W))
    (hbd : ∀ x ∈ frontier W, harmonicReplacementPatch V v h x ≤ g x) :
    ∀ x ∈ W, v x ≤ g x := by
  exact hv.2.1.2 W hW_open hW_preconnected hW_frontier_nonempty
    hW_subset hW_compact hWΩ g hg_harmonic hg_continuous
    (harmonicReplacementPatch_frontier_bound_original Ω V φ hVΩ
      hV_preconnected hV_frontier_nonempty hv hh hWΩ hbd)

/--
%%handwave
name:
  Boundary comparison on the overlap
statement:
  Under the boundary comparison hypothesis for a harmonic test function, the
  harmonic replacement is bounded by the test function on the boundary of the
  overlap between the test domain and the replacement domain.
proof:
  The frontier of the overlap lies in the part inherited from the test-domain
  frontier or the part inherited from the replacement-domain frontier.  On the
  test-domain frontier, the hypothesis gives the estimate where the patch
  equals the replacement, and otherwise equality with the original boundary
  data plus the original boundary comparison gives the estimate.  On the
  replacement-domain frontier, the replacement equals the original subfunction;
  then use the comparison already obtained for the original subfunction inside
  the test domain, or its boundary version if the point lies on the test
  boundary.
-/
theorem harmonicReplacement_overlap_frontier_le
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω V : PerronDomain X) (φ : PerronBoundaryData Ω)
    (hVΩ : closure V.carrier ⊆ Ω.carrier)
    (hV_preconnected : IsPreconnected V.carrier)
    (hV_frontier_nonempty : (frontier V.carrier).Nonempty)
    {v h g : X → ℝ} {W : Set X}
    (hv : IsPerronAdmissible Ω φ v)
    (hh : IsHarmonicReplacement V v h)
    (hW_open : IsOpen W)
    (hW_preconnected : IsPreconnected W)
    (hW_frontier_nonempty : (frontier W).Nonempty)
    (hW_subset : W ⊆ Ω.carrier)
    (hW_compact : IsCompact (closure W))
    (hWΩ : closure W ⊆ Ω.carrier)
    (hg_harmonic : IsHarmonicOnSurface W g)
    (hg_continuous : ContinuousOn g (closure W))
    (hbd : ∀ x ∈ frontier W, harmonicReplacementPatch V v h x ≤ g x) :
    ∀ x ∈ frontier (W ∩ V.carrier), h x ≤ g x := by
  intro x hx
  have horig_frontier :
      ∀ x ∈ frontier W, v x ≤ g x :=
    harmonicReplacementPatch_frontier_bound_original Ω V φ hVΩ
      hV_preconnected hV_frontier_nonempty hv hh hWΩ hbd
  have horig_inside :
      ∀ x ∈ W, v x ≤ g x :=
    original_le_test_harmonic_of_patch_frontier_bound Ω V φ hVΩ
      hV_preconnected hV_frontier_nonempty hv hh
      hW_open hW_preconnected hW_frontier_nonempty
      hW_subset hW_compact hWΩ hg_harmonic hg_continuous hbd
  rcases frontier_inter_subset W V.carrier hx with htest | hreplacement
  · rcases htest with ⟨hxW_frontier, hxV_closure⟩
    by_cases hxV : x ∈ V.carrier
    · have hpatch := hbd x hxW_frontier
      simpa [harmonicReplacementPatch_eq_replacement_of_mem V v h hxV] using hpatch
    · have hxV_boundary : x ∈ V.boundary := by
        have hx_frontier : x ∈ frontier V.carrier := by
          rw [V.isOpen.frontier_eq]
          exact ⟨hxV_closure, hxV⟩
        simpa [PerronDomain.boundary] using hx_frontier
      rw [hh.2.2 x hxV_boundary]
      exact horig_frontier x hxW_frontier
  · rcases hreplacement with ⟨hxW_closure, hxV_frontier⟩
    have hxV_boundary : x ∈ V.boundary := by
      simpa [PerronDomain.boundary] using hxV_frontier
    rw [hh.2.2 x hxV_boundary]
    by_cases hxW : x ∈ W
    · exact horig_inside x hxW
    · have hxW_frontier : x ∈ frontier W := by
        rw [hW_open.frontier_eq]
        exact ⟨hxW_closure, hxW⟩
      exact horig_frontier x hxW_frontier

/--
%%handwave
name:
  The overlap is open
statement:
  The overlap of an open test domain with a replacement domain is open.
proof:
  It is the intersection of two open sets.
-/
theorem harmonicReplacement_overlap_isOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (V : PerronDomain X) {W : Set X}
    (hW_open : IsOpen W) :
    IsOpen (W ∩ V.carrier) := by
  exact hW_open.inter V.isOpen

/--
%%handwave
name:
  The overlap has compact closure
statement:
  If the test domain has compact closure, then its overlap with the
  replacement domain has compact closure.
proof:
  The closure of the overlap is contained in the intersection of the two
  closures.  This intersection is a closed subset of the compact closure of the
  test domain.
-/
theorem harmonicReplacement_overlap_compact_closure
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (V : PerronDomain X) {W : Set X}
    (hW_compact : IsCompact (closure W)) :
    IsCompact (closure (W ∩ V.carrier)) := by
  have hparent : IsCompact (closure W ∩ closure V.carrier) :=
    hW_compact.inter_right isClosed_closure
  exact hparent.of_isClosed_subset isClosed_closure
    (closure_inter_subset_inter_closure W V.carrier)

/--
%%handwave
name:
  The harmonic difference is harmonic on the overlap
statement:
  If one function is harmonic on the replacement domain and another is
  harmonic on the test domain, then their difference is harmonic on the
  overlap.
proof:
  Restrict each harmonicity statement to the overlap and subtract.
-/
theorem harmonicDifference_harmonicOn_overlap
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (V : PerronDomain X) {W : Set X} {h g : X → ℝ}
    (hh_harmonic : IsHarmonicOnSurface V.carrier h)
    (hg_harmonic : IsHarmonicOnSurface W g) :
    IsHarmonicOnSurface (W ∩ V.carrier) (fun x ↦ h x - g x) := by
  exact harmonicOnSurface_sub
    (harmonicOnSurface_mono (by
      intro x hx
      exact hx.2) hh_harmonic)
    (harmonicOnSurface_mono (by
      intro x hx
      exact hx.1) hg_harmonic)

/--
%%handwave
name:
  The harmonic difference is continuous on the closed overlap
statement:
  If the two harmonic comparison functions are continuous up to their original
  closed domains, then their difference is continuous on the closed overlap.
proof:
  The closure of the overlap lies inside the intersection of the original
  closures.
-/
theorem harmonicDifference_continuousOn_overlap_closure
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (V : PerronDomain X) {W : Set X} {h g : X → ℝ}
    (hh_continuous : ContinuousOn h (closure V.carrier))
    (hg_continuous : ContinuousOn g (closure W)) :
    ContinuousOn (fun x ↦ h x - g x) (closure (W ∩ V.carrier)) := by
  have hclosure_subset :
      closure (W ∩ V.carrier) ⊆ closure W ∩ closure V.carrier :=
    closure_inter_subset_inter_closure W V.carrier
  exact (hh_continuous.mono (by
      intro x hx
      exact (hclosure_subset hx).2)).sub
    (hg_continuous.mono (by
      intro x hx
      exact (hclosure_subset hx).1))

/--
%%handwave
name:
  Harmonic comparison on an overlap
statement:
  If two harmonic functions are continuous up to the closures of their domains
  and one is bounded by the other on the boundary of the overlap, then the same
  inequality holds throughout the overlap.
proof:
  Apply the maximum principle to the harmonic function given by their
  difference on the relatively compact open set \(W \cap V\).
-/
theorem harmonicComparison_on_overlap_of_frontier_le
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (V : PerronDomain X) {W : Set X} {h g : X → ℝ}
    (_hW_open : IsOpen W)
    (_hW_compact : IsCompact (closure W))
    (hOverlap_geometry :
      HasComponentwiseMaximumPrincipleGeometry (W ∩ V.carrier))
    (hh_harmonic : IsHarmonicOnSurface V.carrier h)
    (hh_continuous : ContinuousOn h (closure V.carrier))
    (hg_harmonic : IsHarmonicOnSurface W g)
    (hg_continuous : ContinuousOn g (closure W))
    (hbd_overlap : ∀ x ∈ frontier (W ∩ V.carrier), h x ≤ g x) :
    ∀ x ∈ W, x ∈ V.carrier → h x ≤ g x := by
  have hdiff_harmonic :
      IsHarmonicOnSurface (W ∩ V.carrier) (fun x ↦ h x - g x) :=
    harmonicDifference_harmonicOn_overlap V hh_harmonic hg_harmonic
  have hdiff_continuous :
      ContinuousOn (fun x ↦ h x - g x) (closure (W ∩ V.carrier)) :=
    harmonicDifference_continuousOn_overlap_closure V hh_continuous hg_continuous
  have hdiff_boundary :
      ∀ x ∈ frontier (W ∩ V.carrier), h x - g x ≤ 0 := by
    intro x hx
    linarith [hbd_overlap x hx]
  have hdiff_nonpositive :
      ∀ x ∈ W ∩ V.carrier, h x - g x ≤ 0 :=
    harmonic_nonpositive_of_boundary_nonpositive_componentwise
      hOverlap_geometry hdiff_harmonic hdiff_continuous hdiff_boundary
  intro x hxW hxV
  linarith [hdiff_nonpositive x ⟨hxW, hxV⟩]

/--
%%handwave
name:
  Harmonic replacement is below tests on the overlap
statement:
  Under the boundary comparison hypothesis for a harmonic test function, the
  harmonic replacement is bounded by the test function on the part of the test
  domain lying inside the replacement domain.
proof:
  Apply the maximum principle to the difference between the replacement and the
  test harmonic function on the overlap of the two domains.  On the boundary
  inherited from the test domain, the result is exactly the assumed patch
  boundary comparison.  On the boundary inherited from the replacement domain,
  the replacement equals the original subfunction, and the original subfunction
  has already been compared with the test function inside the test domain.
-/
theorem harmonicReplacement_le_test_harmonic_on_overlap
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω V : PerronDomain X) (φ : PerronBoundaryData Ω)
    (hVΩ : closure V.carrier ⊆ Ω.carrier)
    (hV_preconnected : IsPreconnected V.carrier)
    (hV_frontier_nonempty : (frontier V.carrier).Nonempty)
    {v h g : X → ℝ} {W : Set X}
    (hv : IsPerronAdmissible Ω φ v)
    (hh : IsHarmonicReplacement V v h)
    (hW_open : IsOpen W)
    (hW_preconnected : IsPreconnected W)
    (hW_frontier_nonempty : (frontier W).Nonempty)
    (hW_subset : W ⊆ Ω.carrier)
    (hW_compact : IsCompact (closure W))
    (hWΩ : closure W ⊆ Ω.carrier)
    (hOverlap_geometry :
      HasComponentwiseMaximumPrincipleGeometry (W ∩ V.carrier))
    (hg_harmonic : IsHarmonicOnSurface W g)
    (hg_continuous : ContinuousOn g (closure W))
    (hbd : ∀ x ∈ frontier W, harmonicReplacementPatch V v h x ≤ g x) :
    ∀ x ∈ W, x ∈ V.carrier → h x ≤ g x := by
  exact harmonicComparison_on_overlap_of_frontier_le V hW_open hW_compact
    hOverlap_geometry hh.1 hh.2.1 hg_harmonic hg_continuous
    (harmonicReplacement_overlap_frontier_le Ω V φ hVΩ
      hV_preconnected hV_frontier_nonempty hv hh
      hW_open hW_preconnected hW_frontier_nonempty
      hW_subset hW_compact hWΩ hg_harmonic hg_continuous hbd)

/--
%%handwave
name:
  Harmonic replacement patch satisfies harmonic comparison
statement:
  The patched harmonic replacement satisfies the harmonic comparison principle
  on every relatively compact open subregion of the outer Perron domain.
proof:
  First apply the comparison principle for the original subfunction to the
  outer test domain, using
  [the patch boundary bound to compare the original subfunction inside the test domain](lean:JJMath.Uniformization.original_le_test_harmonic_of_patch_frontier_bound).
  This gives the desired comparison away from the smaller replacement domain.
  On the overlap with the replacement domain, compare the harmonic replacement
  with the test harmonic function using the assumed componentwise
  maximum-principle geometry for that overlap.  The boundary controls come
  from the test-domain boundary and from equality of the replacement with the
  original function on the smaller boundary.
-/
theorem harmonicReplacementPatch_comparison_principle
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω V : PerronDomain X) (φ : PerronBoundaryData Ω)
    (hVΩ : closure V.carrier ⊆ Ω.carrier)
    (hV_preconnected : IsPreconnected V.carrier)
    (hV_frontier_nonempty : (frontier V.carrier).Nonempty)
    (hOverlap_geometry :
      ∀ W : Set X,
        IsOpen W →
          IsPreconnected W →
            (frontier W).Nonempty →
              W ⊆ Ω.carrier →
                IsCompact (closure W) →
                  closure W ⊆ Ω.carrier →
                    HasComponentwiseMaximumPrincipleGeometry (W ∩ V.carrier))
    {v h : X → ℝ}
    (hv : IsPerronAdmissible Ω φ v)
    (hh : IsHarmonicReplacement V v h) :
    ∀ W : Set X,
      IsOpen W →
        IsPreconnected W →
          (frontier W).Nonempty →
            W ⊆ Ω.carrier →
              IsCompact (closure W) →
                closure W ⊆ Ω.carrier →
                  ∀ g : X → ℝ,
                    IsHarmonicOnSurface W g →
                      ContinuousOn g (closure W) →
                        (∀ x ∈ frontier W, harmonicReplacementPatch V v h x ≤ g x) →
                          ∀ x ∈ W, harmonicReplacementPatch V v h x ≤ g x := by
  intro W hW_open hW_preconnected hW_frontier_nonempty hW_subset hW_compact
    hWΩ g hg_harmonic hg_continuous hbd x hxW
  by_cases hxV : x ∈ V.carrier
  · rw [harmonicReplacementPatch_eq_replacement_of_mem V v h hxV]
    exact harmonicReplacement_le_test_harmonic_on_overlap (W := W) (g := g)
      Ω V φ hVΩ hV_preconnected hV_frontier_nonempty hv hh
      hW_open hW_preconnected hW_frontier_nonempty hW_subset hW_compact hWΩ
      (hOverlap_geometry W hW_open hW_preconnected hW_frontier_nonempty
        hW_subset hW_compact hWΩ)
      hg_harmonic hg_continuous hbd x hxW hxV
  · rw [harmonicReplacementPatch_eq_original_of_not_mem V v h hxV]
    exact original_le_test_harmonic_of_patch_frontier_bound (W := W) (g := g)
      Ω V φ hVΩ hV_preconnected hV_frontier_nonempty hv hh
      hW_open hW_preconnected hW_frontier_nonempty hW_subset hW_compact hWΩ
      hg_harmonic hg_continuous hbd x hxW

/--
%%handwave
name:
  Harmonic replacement patch is subharmonic on the Perron domain
statement:
  The patched harmonic replacement is subharmonic on the outer Perron domain.
proof:
  Inside the smaller domain it is harmonic, hence subharmonic.  Outside it is
  the original subharmonic function.  Across the smaller boundary, the
  comparison principle, the componentwise maximum-principle geometry of the
  overlaps, and the equality of boundary values give the standard pasting
  lemma for subharmonic functions.
-/
theorem harmonicReplacementPatch_subharmonicOn
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω V : PerronDomain X) (φ : PerronBoundaryData Ω)
    (hVΩ : closure V.carrier ⊆ Ω.carrier)
    (hV_preconnected : IsPreconnected V.carrier)
    (hV_frontier_nonempty : (frontier V.carrier).Nonempty)
    (hOverlap_geometry :
      ∀ W : Set X,
        IsOpen W →
          IsPreconnected W →
            (frontier W).Nonempty →
              W ⊆ Ω.carrier →
                IsCompact (closure W) →
                  closure W ⊆ Ω.carrier →
                    HasComponentwiseMaximumPrincipleGeometry (W ∩ V.carrier))
    {v h : X → ℝ}
    (hv : IsPerronAdmissible Ω φ v)
    (hh : IsHarmonicReplacement V v h) :
    IsSubharmonicOnSurface Ω.carrier (harmonicReplacementPatch V v h) := by
  exact ⟨
    harmonicReplacementPatch_upperSemicontinuousOn Ω V φ hv hh,
    harmonicReplacementPatch_comparison_principle Ω V φ hVΩ
      hV_preconnected hV_frontier_nonempty hOverlap_geometry hv hh⟩

/--
%%handwave
name:
  Harmonic replacement preserves Perron admissibility
statement:
  Replacing a Perron-admissible subfunction by its harmonic replacement on a
  smaller domain gives another Perron-admissible subfunction.
proof:
  The patched function is
  [continuous on the closed outer domain](lean:JJMath.Uniformization.harmonicReplacementPatch_continuousOn_closedDomain),
  [subharmonic on the outer domain](lean:JJMath.Uniformization.harmonicReplacementPatch_subharmonicOn),
  and [satisfies the same outer boundary bound](lean:JJMath.Uniformization.harmonicReplacementPatch_boundary_le).
  The subharmonicity step uses the explicit componentwise maximum-principle
  geometry for overlaps with connected comparison domains.
-/
theorem harmonic_replacement_preserves_admissibility
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω V : PerronDomain X) (φ : PerronBoundaryData Ω)
    (hVΩ : closure V.carrier ⊆ Ω.carrier)
    (hV_preconnected : IsPreconnected V.carrier)
    (hV_frontier_nonempty : (frontier V.carrier).Nonempty)
    (hOverlap_geometry :
      ∀ W : Set X,
        IsOpen W →
          IsPreconnected W →
            (frontier W).Nonempty →
              W ⊆ Ω.carrier →
                IsCompact (closure W) →
                  closure W ⊆ Ω.carrier →
                    HasComponentwiseMaximumPrincipleGeometry (W ∩ V.carrier))
    {v h : X → ℝ}
    (hv : IsPerronAdmissible Ω φ v)
    (hh : IsHarmonicReplacement V v h) :
    IsPerronAdmissible Ω φ (harmonicReplacementPatch V v h) := by
  exact ⟨
    harmonicReplacementPatch_continuousOn_closedDomain Ω V φ hv hh,
    harmonicReplacementPatch_subharmonicOn Ω V φ hVΩ
      hV_preconnected hV_frontier_nonempty hOverlap_geometry hv hh,
    harmonicReplacementPatch_boundary_le Ω V φ hVΩ hv⟩

/--
%%handwave
name:
  Harmonic replacement dominates Perron-open subfunctions
statement:
  If a Perron-open admissible subfunction is harmonically replaced on a
  compact domain contained in the open region, then the original subfunction
  is bounded above by its harmonic replacement inside the smaller domain.
proof:
  Apply the admissible subfunction's comparison principle on the replacement
  domain, using harmonicity and continuity of the replacement and equality
  of the two functions on its boundary.
-/
theorem harmonic_replacement_dominates_original_open
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronOpen X) (V : PerronDomain X) (φ : PerronOpenBoundaryData Ω)
    (hVΩ : closure V.carrier ⊆ Ω.carrier)
    (hV_preconnected : IsPreconnected V.carrier)
    (hV_frontier_nonempty : (frontier V.carrier).Nonempty)
    {v h : X → ℝ}
    (hv : IsPerronOpenAdmissible Ω φ v)
    (hh : IsHarmonicReplacement V v h) :
    ∀ x ∈ V.carrier, v x ≤ h x := by
  rcases hv with ⟨_, hsub, _⟩
  rcases hsub with ⟨_, hcomparison⟩
  rcases hh with ⟨hharm, hcont, hboundary⟩
  have hVΩ_carrier : V.carrier ⊆ Ω.carrier := by
    intro x hx
    exact hVΩ (subset_closure hx)
  exact hcomparison V.carrier V.isOpen hV_preconnected hV_frontier_nonempty
    hVΩ_carrier V.compact_closure hVΩ h hharm hcont
    (by
      intro x hx
      rw [hboundary x hx])

/--
%%handwave
name:
  Harmonic replacement patch dominates Perron-open subfunctions
statement:
  The patched harmonic replacement of a Perron-open admissible subfunction is
  pointwise at least the original subfunction in the open region.
proof:
  Inside the replacement domain, use domination by the harmonic replacement.
  Outside it, the patch equals the original function.
-/
theorem harmonicReplacementPatch_ge_original_open
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronOpen X) (V : PerronDomain X) (φ : PerronOpenBoundaryData Ω)
    (hVΩ : closure V.carrier ⊆ Ω.carrier)
    (hV_preconnected : IsPreconnected V.carrier)
    (hV_frontier_nonempty : (frontier V.carrier).Nonempty)
    {v h : X → ℝ}
    (hv : IsPerronOpenAdmissible Ω φ v)
    (hh : IsHarmonicReplacement V v h) :
    ∀ x ∈ Ω.carrier, v x ≤ harmonicReplacementPatch V v h x := by
  intro x _hxΩ
  by_cases hxV : x ∈ V.carrier
  · rw [harmonicReplacementPatch_eq_replacement_of_mem V v h hxV]
    exact harmonic_replacement_dominates_original_open Ω V φ hVΩ
      hV_preconnected hV_frontier_nonempty hv hh x hxV
  · rw [harmonicReplacementPatch_eq_original_of_not_mem V v h hxV]

/--
%%handwave
name:
  Harmonic replacement patch preserves Perron-open boundary bounds
statement:
  A patched harmonic replacement satisfies the same outer boundary bound as
  the original Perron-open admissible subfunction.
proof:
  The compactly contained replacement domain does not meet the outer
  frontier.  There the patch equals the original function, which already
  satisfies the prescribed boundary inequality.
-/
theorem harmonicReplacementPatch_boundary_le_open
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronOpen X) (V : PerronDomain X) (φ : PerronOpenBoundaryData Ω)
    (hVΩ : closure V.carrier ⊆ Ω.carrier)
    {v h : X → ℝ}
    (hv : IsPerronOpenAdmissible Ω φ v) :
    ∀ x ∈ Ω.boundary, harmonicReplacementPatch V v h x ≤ φ x := by
  intro x hxΩbd
  have hx_not_V : x ∉ V.carrier := by
    intro hxV
    have hxΩ : x ∈ Ω.carrier := hVΩ (subset_closure hxV)
    exact Ω.not_mem_carrier_of_mem_boundary hxΩbd hxΩ
  rw [harmonicReplacementPatch_eq_original_of_not_mem V v h hx_not_V]
  exact hv.2.2 x hxΩbd

/--
%%handwave
name:
  Harmonic replacement patch is continuous on a closed Perron-open region
statement:
  The patched harmonic replacement is continuous on the closure of the outer
  Perron-open region.
proof:
  The replacement and original functions are continuous on the two closed
  pieces cut out by the replacement domain and agree on its frontier.
  The piecewise continuity lemma therefore glues them continuously.
-/
theorem harmonicReplacementPatch_continuousOn_closedOpen
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronOpen X) (V : PerronDomain X) (φ : PerronOpenBoundaryData Ω)
    {v h : X → ℝ}
    (hv : IsPerronOpenAdmissible Ω φ v)
    (hh : IsHarmonicReplacement V v h) :
    ContinuousOn (harmonicReplacementPatch V v h) (closure Ω.carrier) := by
  classical
  rcases hv with ⟨hv_cont, _hv_subharmonic, _hv_boundary⟩
  rcases hh with ⟨_hh_harmonic, hh_cont, hh_boundary⟩
  have heq : ∀ x ∈ closure Ω.carrier ∩ frontier V.carrier, h x = v x := by
    intro x hx
    exact hh_boundary x (by simpa [PerronDomain.boundary] using hx.2)
  have hh_cont' : ContinuousOn h (closure Ω.carrier ∩ closure V.carrier) :=
    hh_cont.mono (by
      intro x hx
      exact hx.2)
  have hv_cont' : ContinuousOn v (closure Ω.carrier ∩ closure V.carrierᶜ) :=
    hv_cont.mono (by
      intro x hx
      exact hx.1)
  simpa [harmonicReplacementPatch] using
    (ContinuousOn.piecewise (t := V.carrier) heq hh_cont' hv_cont')

/--
%%handwave
name:
  Harmonic replacement patch is upper semicontinuous on a Perron-open region
statement:
  The patched harmonic replacement is upper semicontinuous in the outer
  Perron-open region.
proof:
  Its continuity on the closure of the outer region restricts to continuity,
  hence upper semicontinuity, on the region itself.
-/
theorem harmonicReplacementPatch_upperSemicontinuousOn_open
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronOpen X) (V : PerronDomain X) (φ : PerronOpenBoundaryData Ω)
    {v h : X → ℝ}
    (hv : IsPerronOpenAdmissible Ω φ v)
    (hh : IsHarmonicReplacement V v h) :
    UpperSemicontinuousOn (harmonicReplacementPatch V v h) Ω.carrier := by
  have hcont_closed :
      ContinuousOn (harmonicReplacementPatch V v h) (closure Ω.carrier) :=
    harmonicReplacementPatch_continuousOn_closedOpen Ω V φ hv hh
  have hcont :
      ContinuousOn (harmonicReplacementPatch V v h) Ω.carrier :=
    hcont_closed.mono subset_closure
  exact hcont.upperSemicontinuousOn

/--
%%handwave
name:
  A boundary bound for a harmonic patch bounds the original subfunction
statement:
  Let \(V\Subset\Omega\), let \(v\) be Perron-admissible on \(\Omega\), and
  let \(\widetilde v\) be its harmonic-replacement patch on \(V\).  If
  \(\widetilde v\le g\) on \(\partial W\), where
  \(\overline W\subseteq\Omega\), then
  \[
    v\le g\quad\text{on }\partial W.
  \]
proof:
  Harmonic replacement dominates the original admissible subfunction
  throughout \(\Omega\).  Every point of \(\partial W\) lies in \(\Omega\),
  so \(v\le\widetilde v\le g\) there.
-/
theorem harmonicReplacementPatch_frontier_bound_original_open
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronOpen X) (V : PerronDomain X) (φ : PerronOpenBoundaryData Ω)
    (hVΩ : closure V.carrier ⊆ Ω.carrier)
    (hV_preconnected : IsPreconnected V.carrier)
    (hV_frontier_nonempty : (frontier V.carrier).Nonempty)
    {v h g : X → ℝ} {W : Set X}
    (hv : IsPerronOpenAdmissible Ω φ v)
    (hh : IsHarmonicReplacement V v h)
    (hWΩ : closure W ⊆ Ω.carrier)
    (hbd : ∀ x ∈ frontier W, harmonicReplacementPatch V v h x ≤ g x) :
    ∀ x ∈ frontier W, v x ≤ g x := by
  intro x hxW
  have hxΩ : x ∈ Ω.carrier := hWΩ (frontier_subset_closure hxW)
  exact (harmonicReplacementPatch_ge_original_open Ω V φ hVΩ
      hV_preconnected hV_frontier_nonempty hv hh x hxΩ).trans
    (hbd x hxW)

/--
%%handwave
name:
  Comparison of the original subfunction with a harmonic test function
statement:
  In the preceding setting, suppose \(W\Subset\Omega\) is open,
  preconnected, and has nonempty frontier, and \(g\) is harmonic on \(W\)
  and continuous on \(\overline W\).  If the harmonic-replacement patch is
  at most \(g\) on \(\partial W\), then
  \[
    v\le g\quad\text{on }W.
  \]
proof:
  The boundary hypothesis first implies \(v\le g\) on \(\partial W\).
  Apply the comparison property in the Perron admissibility of \(v\).
-/
theorem original_le_test_harmonic_of_patch_frontier_bound_open
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronOpen X) (V : PerronDomain X) (φ : PerronOpenBoundaryData Ω)
    (hVΩ : closure V.carrier ⊆ Ω.carrier)
    (hV_preconnected : IsPreconnected V.carrier)
    (hV_frontier_nonempty : (frontier V.carrier).Nonempty)
    {v h g : X → ℝ} {W : Set X}
    (hv : IsPerronOpenAdmissible Ω φ v)
    (hh : IsHarmonicReplacement V v h)
    (hW_open : IsOpen W)
    (hW_preconnected : IsPreconnected W)
    (hW_frontier_nonempty : (frontier W).Nonempty)
    (hW_subset : W ⊆ Ω.carrier)
    (hW_compact : IsCompact (closure W))
    (hWΩ : closure W ⊆ Ω.carrier)
    (hg_harmonic : IsHarmonicOnSurface W g)
    (hg_continuous : ContinuousOn g (closure W))
    (hbd : ∀ x ∈ frontier W, harmonicReplacementPatch V v h x ≤ g x) :
    ∀ x ∈ W, v x ≤ g x := by
  exact hv.2.1.2 W hW_open hW_preconnected hW_frontier_nonempty
    hW_subset hW_compact hWΩ g hg_harmonic hg_continuous
    (harmonicReplacementPatch_frontier_bound_original_open Ω V φ hVΩ
      hV_preconnected hV_frontier_nonempty hv hh hWΩ hbd)

/--
%%handwave
name:
  Boundary comparison on the overlap of two replacement regions
statement:
  Under the same hypotheses,
  \[
    h\le g\quad\text{on }\partial(W\cap V),
  \]
  where \(h\) is the harmonic replacement on \(V\).
proof:
  A point of \(\partial(W\cap V)\) lies either on \(\partial W\) or on
  \(\partial V\).  On \(\partial W\), use the assumed patch bound when the
  point lies in \(V\), and otherwise use \(h=v\) on \(\partial V\).
  On \(\partial V\), replace \(h\) by \(v\) and use either the interior or
  frontier comparison for \(v\) against \(g\).
-/
theorem harmonicReplacement_overlap_frontier_le_open
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronOpen X) (V : PerronDomain X) (φ : PerronOpenBoundaryData Ω)
    (hVΩ : closure V.carrier ⊆ Ω.carrier)
    (hV_preconnected : IsPreconnected V.carrier)
    (hV_frontier_nonempty : (frontier V.carrier).Nonempty)
    {v h g : X → ℝ} {W : Set X}
    (hv : IsPerronOpenAdmissible Ω φ v)
    (hh : IsHarmonicReplacement V v h)
    (hW_open : IsOpen W)
    (hW_preconnected : IsPreconnected W)
    (hW_frontier_nonempty : (frontier W).Nonempty)
    (hW_subset : W ⊆ Ω.carrier)
    (hW_compact : IsCompact (closure W))
    (hWΩ : closure W ⊆ Ω.carrier)
    (hg_harmonic : IsHarmonicOnSurface W g)
    (hg_continuous : ContinuousOn g (closure W))
    (hbd : ∀ x ∈ frontier W, harmonicReplacementPatch V v h x ≤ g x) :
    ∀ x ∈ frontier (W ∩ V.carrier), h x ≤ g x := by
  intro x hx
  have horig_frontier :
      ∀ x ∈ frontier W, v x ≤ g x :=
    harmonicReplacementPatch_frontier_bound_original_open Ω V φ hVΩ
      hV_preconnected hV_frontier_nonempty hv hh hWΩ hbd
  have horig_inside :
      ∀ x ∈ W, v x ≤ g x :=
    original_le_test_harmonic_of_patch_frontier_bound_open Ω V φ hVΩ
      hV_preconnected hV_frontier_nonempty hv hh
      hW_open hW_preconnected hW_frontier_nonempty
      hW_subset hW_compact hWΩ hg_harmonic hg_continuous hbd
  rcases frontier_inter_subset W V.carrier hx with htest | hreplacement
  · rcases htest with ⟨hxW_frontier, hxV_closure⟩
    by_cases hxV : x ∈ V.carrier
    · have hpatch := hbd x hxW_frontier
      simpa [harmonicReplacementPatch_eq_replacement_of_mem V v h hxV] using hpatch
    · have hxV_boundary : x ∈ V.boundary := by
        have hx_frontier : x ∈ frontier V.carrier := by
          rw [V.isOpen.frontier_eq]
          exact ⟨hxV_closure, hxV⟩
        simpa [PerronDomain.boundary] using hx_frontier
      rw [hh.2.2 x hxV_boundary]
      exact horig_frontier x hxW_frontier
  · rcases hreplacement with ⟨hxW_closure, hxV_frontier⟩
    have hxV_boundary : x ∈ V.boundary := by
      simpa [PerronDomain.boundary] using hxV_frontier
    rw [hh.2.2 x hxV_boundary]
    by_cases hxW : x ∈ W
    · exact horig_inside x hxW
    · have hxW_frontier : x ∈ frontier W := by
        rw [hW_open.frontier_eq]
        exact ⟨hxW_closure, hxW⟩
      exact horig_frontier x hxW_frontier

/--
%%handwave
name:
  Harmonic comparison on the replacement overlap
statement:
  If every component of \(W\cap V\) has the required maximum-principle
  geometry, then the preceding boundary inequality implies
  \[
    h(x)\le g(x)\qquad(x\in W\cap V).
  \]
proof:
  Both \(h\) and \(g\) are harmonic on the overlap and continuous up to the
  relevant boundary.  Apply the componentwise harmonic comparison principle
  using \(h\le g\) on \(\partial(W\cap V)\).
-/
theorem harmonicReplacement_le_test_harmonic_on_overlap_open
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronOpen X) (V : PerronDomain X) (φ : PerronOpenBoundaryData Ω)
    (hVΩ : closure V.carrier ⊆ Ω.carrier)
    (hV_preconnected : IsPreconnected V.carrier)
    (hV_frontier_nonempty : (frontier V.carrier).Nonempty)
    {v h g : X → ℝ} {W : Set X}
    (hv : IsPerronOpenAdmissible Ω φ v)
    (hh : IsHarmonicReplacement V v h)
    (hW_open : IsOpen W)
    (hW_preconnected : IsPreconnected W)
    (hW_frontier_nonempty : (frontier W).Nonempty)
    (hW_subset : W ⊆ Ω.carrier)
    (hW_compact : IsCompact (closure W))
    (hWΩ : closure W ⊆ Ω.carrier)
    (hOverlap_geometry :
      HasComponentwiseMaximumPrincipleGeometry (W ∩ V.carrier))
    (hg_harmonic : IsHarmonicOnSurface W g)
    (hg_continuous : ContinuousOn g (closure W))
    (hbd : ∀ x ∈ frontier W, harmonicReplacementPatch V v h x ≤ g x) :
    ∀ x ∈ W, x ∈ V.carrier → h x ≤ g x := by
  exact harmonicComparison_on_overlap_of_frontier_le V hW_open hW_compact
    hOverlap_geometry hh.1 hh.2.1 hg_harmonic hg_continuous
    (harmonicReplacement_overlap_frontier_le_open Ω V φ hVΩ
      hV_preconnected hV_frontier_nonempty hv hh
      hW_open hW_preconnected hW_frontier_nonempty
      hW_subset hW_compact hWΩ hg_harmonic hg_continuous hbd)

/--
%%handwave
name:
  Comparison principle for a harmonic replacement patch
statement:
  Let \(V\Subset\Omega\), and assume the componentwise maximum-principle
  geometry for \(W\cap V\) whenever \(W\Subset\Omega\) is an admissible test
  region.  If \(g\) is harmonic on \(W\), continuous on \(\overline W\),
  and
  \[
    \widetilde v\le g\quad\text{on }\partial W,
  \]
  then \(\widetilde v\le g\) throughout \(W\).
proof:
  On \(W\cap V\), the patch equals \(h\) and harmonic comparison on the
  overlap applies.  On \(W\setminus V\), it equals \(v\), which is bounded
  by \(g\) by the original Perron comparison property.
-/
theorem harmonicReplacementPatch_comparison_principle_open
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronOpen X) (V : PerronDomain X) (φ : PerronOpenBoundaryData Ω)
    (hVΩ : closure V.carrier ⊆ Ω.carrier)
    (hV_preconnected : IsPreconnected V.carrier)
    (hV_frontier_nonempty : (frontier V.carrier).Nonempty)
    (hOverlap_geometry :
      ∀ W : Set X,
        IsOpen W →
          IsPreconnected W →
            (frontier W).Nonempty →
              W ⊆ Ω.carrier →
                IsCompact (closure W) →
                  closure W ⊆ Ω.carrier →
                    HasComponentwiseMaximumPrincipleGeometry (W ∩ V.carrier))
    {v h : X → ℝ}
    (hv : IsPerronOpenAdmissible Ω φ v)
    (hh : IsHarmonicReplacement V v h) :
    ∀ W : Set X,
      IsOpen W →
        IsPreconnected W →
          (frontier W).Nonempty →
            W ⊆ Ω.carrier →
              IsCompact (closure W) →
                closure W ⊆ Ω.carrier →
                  ∀ g : X → ℝ,
                    IsHarmonicOnSurface W g →
                      ContinuousOn g (closure W) →
                        (∀ x ∈ frontier W, harmonicReplacementPatch V v h x ≤ g x) →
                          ∀ x ∈ W, harmonicReplacementPatch V v h x ≤ g x := by
  intro W hW_open hW_preconnected hW_frontier_nonempty hW_subset hW_compact
    hWΩ g hg_harmonic hg_continuous hbd x hxW
  by_cases hxV : x ∈ V.carrier
  · rw [harmonicReplacementPatch_eq_replacement_of_mem V v h hxV]
    exact harmonicReplacement_le_test_harmonic_on_overlap_open (W := W) (g := g)
      Ω V φ hVΩ hV_preconnected hV_frontier_nonempty hv hh
      hW_open hW_preconnected hW_frontier_nonempty hW_subset hW_compact hWΩ
      (hOverlap_geometry W hW_open hW_preconnected hW_frontier_nonempty
        hW_subset hW_compact hWΩ)
      hg_harmonic hg_continuous hbd x hxW hxV
  · rw [harmonicReplacementPatch_eq_original_of_not_mem V v h hxV]
    exact original_le_test_harmonic_of_patch_frontier_bound_open (W := W) (g := g)
      Ω V φ hVΩ hV_preconnected hV_frontier_nonempty hv hh
      hW_open hW_preconnected hW_frontier_nonempty hW_subset hW_compact hWΩ
      hg_harmonic hg_continuous hbd x hxW

/--
%%handwave
name:
  Subharmonicity of a harmonic replacement patch
statement:
  Under the harmonic-replacement and overlap-geometry hypotheses, the
  patched function \(\widetilde v\) is subharmonic on \(\Omega\).
proof:
  The patch is upper semicontinuous on \(\Omega\), and it satisfies the
  defining comparison inequality against every harmonic test function on
  compactly contained test regions.  These are precisely the two
  subharmonicity conditions.
-/
theorem harmonicReplacementPatch_subharmonicOn_open
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronOpen X) (V : PerronDomain X) (φ : PerronOpenBoundaryData Ω)
    (hVΩ : closure V.carrier ⊆ Ω.carrier)
    (hV_preconnected : IsPreconnected V.carrier)
    (hV_frontier_nonempty : (frontier V.carrier).Nonempty)
    (hOverlap_geometry :
      ∀ W : Set X,
        IsOpen W →
          IsPreconnected W →
            (frontier W).Nonempty →
              W ⊆ Ω.carrier →
                IsCompact (closure W) →
                  closure W ⊆ Ω.carrier →
                    HasComponentwiseMaximumPrincipleGeometry (W ∩ V.carrier))
    {v h : X → ℝ}
    (hv : IsPerronOpenAdmissible Ω φ v)
    (hh : IsHarmonicReplacement V v h) :
    IsSubharmonicOnSurface Ω.carrier (harmonicReplacementPatch V v h) := by
  exact ⟨
    harmonicReplacementPatch_upperSemicontinuousOn_open Ω V φ hv hh,
    harmonicReplacementPatch_comparison_principle_open Ω V φ hVΩ
      hV_preconnected hV_frontier_nonempty hOverlap_geometry hv hh⟩

/--
%%handwave
name:
  Harmonic replacement preserves Perron-open admissibility
statement:
  Replacing a Perron-open admissible subfunction by its harmonic replacement
  on a compactly contained coordinate disk gives another Perron-open
  admissible subfunction.
proof:
  [The patched function is continuous on the closed region](lean:JJMath.Uniformization.harmonicReplacementPatch_continuousOn_closedOpen), [is subharmonic in the open region](lean:JJMath.Uniformization.harmonicReplacementPatch_subharmonicOn_open), and [still lies below the prescribed boundary data](lean:JJMath.Uniformization.harmonicReplacementPatch_boundary_le_open). These are exactly the three admissibility conditions.
-/
theorem harmonic_replacement_preserves_open_admissibility
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronOpen X) (V : PerronDomain X) (φ : PerronOpenBoundaryData Ω)
    (hVΩ : closure V.carrier ⊆ Ω.carrier)
    (hV_preconnected : IsPreconnected V.carrier)
    (hV_frontier_nonempty : (frontier V.carrier).Nonempty)
    (hOverlap_geometry :
      ∀ W : Set X,
        IsOpen W →
          IsPreconnected W →
            (frontier W).Nonempty →
              W ⊆ Ω.carrier →
                IsCompact (closure W) →
                  closure W ⊆ Ω.carrier →
                    HasComponentwiseMaximumPrincipleGeometry (W ∩ V.carrier))
    {v h : X → ℝ}
    (hv : IsPerronOpenAdmissible Ω φ v)
    (hh : IsHarmonicReplacement V v h) :
    IsPerronOpenAdmissible Ω φ (harmonicReplacementPatch V v h) := by
  exact ⟨
    harmonicReplacementPatch_continuousOn_closedOpen Ω V φ hv hh,
    harmonicReplacementPatch_subharmonicOn_open Ω V φ hVΩ
      hV_preconnected hV_frontier_nonempty hOverlap_geometry hv hh,
    harmonicReplacementPatch_boundary_le_open Ω V φ hVΩ hv⟩

/--
%%handwave
name:
  A harmonic replacement preserves an ambient upper bound
statement:
  Let \(V\Subset\Omega\), and suppose \(v\le M\) on \(\Omega\).  If \(h\) is
  the harmonic replacement of \(v\) on \(V\), then
  \[
    h\le M\quad\text{on }V.
  \]
proof:
  The harmonic function \(h-M\) is continuous on \(\overline V\) and is
  nonpositive on \(\partial V\), because \(h=v\) there and
  \(\partial V\subseteq\Omega\).  The maximum principle gives
  \(h-M\le0\) in \(V\).
-/
theorem harmonicReplacement_le_constant_of_boundary_original_le_open
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronOpen X) (V : PerronDomain X)
    (hVΩ : closure V.carrier ⊆ Ω.carrier)
    (hV_preconnected : IsPreconnected V.carrier)
    (hV_frontier_nonempty : (frontier V.carrier).Nonempty)
    {v h : X → ℝ} {M : ℝ}
    (hv_bound : ∀ x ∈ Ω.carrier, v x ≤ M)
    (hh : IsHarmonicReplacement V v h) :
    ∀ x ∈ V.carrier, h x ≤ M := by
  have hdiff_harmonic :
      IsHarmonicOnSurface V.carrier (fun x ↦ h x - M) :=
    harmonicOnSurface_sub hh.1 (harmonicOnSurface_const V.carrier M)
  have hdiff_continuous :
      ContinuousOn (fun x ↦ h x - M) (closure V.carrier) :=
    hh.2.1.sub continuousOn_const
  have hdiff_boundary : ∀ x ∈ frontier V.carrier, h x - M ≤ 0 := by
    intro x hx
    have hx_boundary : x ∈ V.boundary := by
      simpa [PerronDomain.boundary] using hx
    have hxΩ : x ∈ Ω.carrier := hVΩ (frontier_subset_closure hx)
    have hh_eq : h x = v x := hh.2.2 x hx_boundary
    linarith [hv_bound x hxΩ]
  have hnonpos : ∀ x ∈ V.carrier, h x - M ≤ 0 :=
    harmonic_nonpositive_of_boundary_nonpositive V.isOpen hV_preconnected
      V.compact_closure hV_frontier_nonempty hdiff_harmonic
      hdiff_continuous hdiff_boundary
  intro x hx
  linarith [hnonpos x hx]

/--
%%handwave
name:
  A harmonic replacement patch preserves an upper bound
statement:
  Under the preceding hypotheses,
  \[
    \widetilde v\le M\quad\text{on }\Omega.
  \]
proof:
  Inside \(V\), the patch is \(h\le M\) by the maximum principle.  Outside
  \(V\), it is the original function \(v\le M\).
-/
theorem harmonicReplacementPatch_le_constant_open
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronOpen X) (V : PerronDomain X)
    (hVΩ : closure V.carrier ⊆ Ω.carrier)
    (hV_preconnected : IsPreconnected V.carrier)
    (hV_frontier_nonempty : (frontier V.carrier).Nonempty)
    {v h : X → ℝ} {M : ℝ}
    (hv_bound : ∀ x ∈ Ω.carrier, v x ≤ M)
    (hh : IsHarmonicReplacement V v h) :
    ∀ x ∈ Ω.carrier, harmonicReplacementPatch V v h x ≤ M := by
  intro x hxΩ
  by_cases hxV : x ∈ V.carrier
  · rw [harmonicReplacementPatch_eq_replacement_of_mem V v h hxV]
    exact harmonicReplacement_le_constant_of_boundary_original_le_open Ω V
      hVΩ hV_preconnected hV_frontier_nonempty hv_bound hh x hxV
  · rw [harmonicReplacementPatch_eq_original_of_not_mem V v h hxV]
    exact hv_bound x hxΩ
/--
%%handwave
name:
  Harmonic replacement preserves bounded Perron admissibility
statement:
  Let $v$ be Perron-admissible on an open region $\Omega$ and satisfy
  $v\le M$ there. If a coordinate disk $V$ is compactly contained in
  $\Omega$, then patching $v$ with its harmonic replacement on $V$ produces
  another Perron-admissible function which still satisfies $v\le M$ on
  $\Omega$.
proof:
  [Harmonic replacement preserves Perron-open admissibility](lean:JJMath.Uniformization.harmonic_replacement_preserves_open_admissibility). The maximum principle bounds the replacement by $M$ on $V$, while outside $V$ the patched function equals the original $v$.
-/
theorem harmonic_replacement_preserves_bounded_open_admissibility
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronOpen X) (V : PerronDomain X) (φ : PerronOpenBoundaryData Ω)
    (M : ℝ)
    (hVΩ : closure V.carrier ⊆ Ω.carrier)
    (hV_preconnected : IsPreconnected V.carrier)
    (hV_frontier_nonempty : (frontier V.carrier).Nonempty)
    (hOverlap_geometry :
      ∀ W : Set X,
        IsOpen W →
          IsPreconnected W →
            (frontier W).Nonempty →
              W ⊆ Ω.carrier →
                IsCompact (closure W) →
                  closure W ⊆ Ω.carrier →
                    HasComponentwiseMaximumPrincipleGeometry (W ∩ V.carrier))
    {v h : X → ℝ}
    (hv : IsBoundedPerronOpenAdmissible Ω φ M v)
    (hh : IsHarmonicReplacement V v h) :
    IsBoundedPerronOpenAdmissible Ω φ M (harmonicReplacementPatch V v h) := by
  exact ⟨
    harmonic_replacement_preserves_open_admissibility Ω V φ hVΩ
      hV_preconnected hV_frontier_nonempty hOverlap_geometry hv.1 hh,
    harmonicReplacementPatch_le_constant_open Ω V hVΩ
      hV_preconnected hV_frontier_nonempty hv.2 hh⟩

/--
%%handwave
name:
  Constants below the boundary data are Perron-admissible
statement:
  Any constant lying below the prescribed boundary data is a
  Perron-admissible subfunction.
proof:
  Constants are continuous and subharmonic.  The boundary inequality is exactly
  the assumed lower bound.
-/
theorem constant_below_boundary_is_perron_admissible
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronDomain X) (φ : PerronBoundaryData Ω)
    {c : ℝ} (hc : ∀ x ∈ Ω.boundary, c ≤ φ x) :
    IsPerronAdmissible Ω φ (fun _ : X ↦ c) := by
  exact ⟨
    continuousOn_const,
    subharmonicOnSurface_const Ω.carrier c,
    hc⟩

/--
%%handwave
name:
  Explicit lower bounds make Perron families nonempty
statement:
  If the boundary data has a global lower bound, then the Perron family is
  nonempty.
proof:
  The constant function at that lower bound is admissible.
-/
theorem perron_family_nonempty_of_boundary_lower_bound
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronDomain X) (φ : PerronBoundaryData Ω)
    {m : ℝ} (hm : ∀ x ∈ Ω.boundary, m ≤ φ x) :
    ∃ v : X → ℝ, IsPerronAdmissible Ω φ v := by
  exact ⟨fun _ : X ↦ m, constant_below_boundary_is_perron_admissible Ω φ hm⟩

/--
%%handwave
name:
  The Perron family is nonempty
statement:
  The Perron family of a continuous boundary value on a Perron domain is
  nonempty.
proof:
  Choose a lower bound for the boundary data.  The corresponding constant
  function is Perron-admissible.
-/
theorem perron_family_nonempty
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronDomain X) (φ : PerronBoundaryData Ω) :
    ∃ v : X → ℝ, IsPerronAdmissible Ω φ v := by
  rcases PerronBoundaryData.exists_lower_bound φ with ⟨m, hm⟩
  exact perron_family_nonempty_of_boundary_lower_bound Ω φ hm

/--
%%handwave
name:
  Strict superlevel closures stay inside a Perron domain
statement:
  If a continuous function on the closed Perron domain is bounded by \(M\) on
  the boundary, then every strict superlevel set \(\{u>a\}\) with \(M<a\)
  has closure contained in the open domain.
proof:
  The strict superlevel set is contained in the closed set
  \(\overline \Omega \cap \{u\ge a\}\).  A point of its closure is therefore
  either in the domain or on the boundary; the boundary alternative
  contradicts \(u\le M<a\).
-/
theorem strict_superlevel_closure_subset_domain
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronDomain X) {u : X → ℝ} {M a : ℝ}
    (hMa : M < a)
    (hu_continuous : ContinuousOn u (closure Ω.carrier))
    (hbd : ∀ x ∈ Ω.boundary, u x ≤ M) :
    closure (Ω.carrier ∩ {x : X | a < u x}) ⊆ Ω.carrier := by
  let S : Set X := Ω.carrier ∩ {x : X | a < u x}
  let A : Set X := closure Ω.carrier ∩ u ⁻¹' Set.Ici a
  have hA_closed : IsClosed A :=
    hu_continuous.preimage_isClosed_of_isClosed isClosed_closure isClosed_Ici
  have hS_subset_A : S ⊆ A := by
    intro x hx
    exact ⟨subset_closure hx.1, by
      simpa [Set.mem_preimage, Set.mem_Ici] using le_of_lt hx.2⟩
  have hclosure_subset_A : closure S ⊆ A :=
    closure_minimal hS_subset_A hA_closed
  intro x hx
  have hxA : x ∈ A := hclosure_subset_A hx
  have hx_closure : x ∈ closure Ω.carrier := hxA.1
  have hax : a ≤ u x := hxA.2
  have hx_domain_or_boundary : x ∈ Ω.carrier ∪ Ω.boundary := by
    simpa [PerronDomain.boundary, closure_eq_self_union_frontier] using hx_closure
  rcases hx_domain_or_boundary with hxΩ | hx_boundary
  · exact hxΩ
  · have huxM : u x ≤ M := hbd x hx_boundary
    linarith

/--
%%handwave
name:
  Connected components are closed inside the open set
statement:
  If a point of an open set lies in the closure of the connected component of
  another point, then it lies in that same connected component.
proof:
  In the subtype topology on the open set, connected components are closed.
  Pull the ambient closure statement back through the subtype embedding.
-/
theorem mem_connectedComponentIn_of_mem_closure_of_mem
    {X : Type} [TopologicalSpace X] {S : Set X} {x y : X}
    (hxS : x ∈ S) (hyS : y ∈ S)
    (hy_closure : y ∈ closure (connectedComponentIn S x)) :
    y ∈ connectedComponentIn S x := by
  let xS : S := ⟨x, hxS⟩
  let yS : S := ⟨y, hyS⟩
  have hcomponent_eq :
      connectedComponentIn S x =
        ((↑) : S → X) '' connectedComponent xS :=
    connectedComponentIn_eq_image hxS
  have hy_sub_closure : yS ∈ closure (connectedComponent xS) := by
    have hy_preimage :
        yS ∈ ((↑) : S → X) ⁻¹'
          closure (((↑) : S → X) '' connectedComponent xS) := by
      simpa [yS, hcomponent_eq] using hy_closure
    simpa [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
      using hy_preimage
  have hy_sub_component : yS ∈ connectedComponent xS := by
    have hclosed : IsClosed (connectedComponent xS) := isClosed_connectedComponent
    rwa [hclosed.closure_eq] at hy_sub_closure
  rw [hcomponent_eq]
  exact ⟨yS, hy_sub_component, rfl⟩

/--
%%handwave
name:
  Subharmonic maximum principle on a Perron domain
statement:
  A continuous subharmonic function on a closed Perron domain that is bounded
  above by a constant on the boundary is bounded by the same constant
  throughout the domain, provided every component relevant to the maximum
  principle reaches the boundary.
proof:
  This is the maximum principle for upper semicontinuous subharmonic functions
  on a relatively compact domain, applied component by component.
-/
theorem subharmonic_le_constant_of_boundary_le
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronDomain X) {u : X → ℝ} {M : ℝ}
    (hΩ_geometry : HasComponentwiseMaximumPrincipleGeometry Ω.carrier)
    (hu_continuous : ContinuousOn u (closure Ω.carrier))
    (hu_subharmonic : IsSubharmonicOnSurface Ω.carrier u)
    (hbd : ∀ x ∈ Ω.boundary, u x ≤ M) :
    ∀ x ∈ Ω.carrier, u x ≤ M := by
  intro x hxΩ
  by_contra hnot
  have hMx : M < u x := lt_of_not_ge hnot
  let a : ℝ := M + (u x - M) / 2
  have hMa : M < a := by
    dsimp [a]
    linarith
  have hax : a < u x := by
    dsimp [a]
    linarith
  let S : Set X := Ω.carrier ∩ {y : X | a < u y}
  have hxS : x ∈ S := ⟨hxΩ, hax⟩
  have hu_continuous_domain : ContinuousOn u Ω.carrier :=
    hu_continuous.mono subset_closure
  have hS_open : IsOpen S := by
    have hpreimage :=
      hu_continuous_domain.isOpen_inter_preimage Ω.isOpen (isOpen_Ioi : IsOpen (Set.Ioi a))
    simpa [S, Set.preimage, Set.mem_Ioi] using hpreimage
  have hclosureS_subsetΩ : closure S ⊆ Ω.carrier := by
    simpa [S] using
      strict_superlevel_closure_subset_domain Ω hMa hu_continuous hbd
  let C : Set X := connectedComponentIn S x
  haveI : LocallyConnectedSpace X := ChartedSpace.locallyConnectedSpace ℂ X
  have hC_open : IsOpen C := by
    dsimp [C]
    exact hS_open.connectedComponentIn
  have hxC : x ∈ C := by
    dsimp [C]
    exact mem_connectedComponentIn hxS
  have hC_preconnected : IsPreconnected C := by
    dsimp [C]
    exact isPreconnected_connectedComponentIn
  have hC_subsetS : C ⊆ S := by
    dsimp [C]
    exact connectedComponentIn_subset S x
  have hC_subsetΩ : C ⊆ Ω.carrier :=
    hC_subsetS.trans Set.inter_subset_left
  have hclosureC_subsetΩ : closure C ⊆ Ω.carrier :=
    (closure_mono hC_subsetS).trans hclosureS_subsetΩ
  have hC_compact : IsCompact (closure C) :=
    Ω.compact_closure.of_isClosed_subset isClosed_closure
      ((closure_mono hC_subsetΩ))
  have hC_frontier_nonempty : (frontier C).Nonempty := by
    by_contra hfrontier_not_nonempty
    have hfrontier_empty : frontier C = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hfrontier_not_nonempty
    have hC_closed : IsClosed C :=
      (isClopen_iff_frontier_eq_empty.mpr hfrontier_empty).1
    rcases hΩ_geometry x hxΩ with
      ⟨D, hxD, hD_open, hD_preconnected, hD_subsetΩ, _hD_compact,
        hD_frontier_nonempty, hD_frontier_subset⟩
    have hD_subsetC : D ⊆ C := by
      have hcover : D ⊆ C ∪ Cᶜ := by
        intro y _hy
        by_cases hyC : y ∈ C
        · exact Or.inl hyC
        · exact Or.inr hyC
      have hnonempty : (D ∩ C).Nonempty := ⟨x, hxD, hxC⟩
      exact hD_preconnected.subset_left_of_subset_union
        hC_open hC_closed.isOpen_compl disjoint_compl_right hcover hnonempty
    rcases hD_frontier_nonempty with ⟨b, hbD_frontier⟩
    have hbΩ_frontier : b ∈ frontier Ω.carrier :=
      hD_frontier_subset hbD_frontier
    have hb_closureS : b ∈ closure S :=
      closure_mono (hD_subsetC.trans hC_subsetS)
        (frontier_subset_closure hbD_frontier)
    have hbΩ : b ∈ Ω.carrier := hclosureS_subsetΩ hb_closureS
    have hb_impossible : b ∈ Ω.carrier ∩ frontier Ω.carrier :=
      ⟨hbΩ, hbΩ_frontier⟩
    rw [Ω.isOpen.inter_frontier_eq] at hb_impossible
    exact hb_impossible
  have hC_frontier_bound : ∀ y ∈ frontier C, u y ≤ a := by
    intro y hy_frontier
    by_contra hnot_le
    have hay : a < u y := lt_of_not_ge hnot_le
    have hy_closureC : y ∈ closure C := frontier_subset_closure hy_frontier
    have hyΩ : y ∈ Ω.carrier := hclosureC_subsetΩ hy_closureC
    have hyS : y ∈ S := ⟨hyΩ, hay⟩
    have hyC : y ∈ C :=
      mem_connectedComponentIn_of_mem_closure_of_mem hxS hyS hy_closureC
    have hy_notC : y ∉ C := by
      intro hyC'
      have hy_inter : y ∈ C ∩ frontier C := ⟨hyC', hy_frontier⟩
      rw [hC_open.inter_frontier_eq] at hy_inter
      exact hy_inter
    exact hy_notC hyC
  have hux_le_a : u x ≤ a :=
    hu_subharmonic.2 C hC_open hC_preconnected hC_frontier_nonempty
      hC_subsetΩ hC_compact hclosureC_subsetΩ
      (fun _ : X ↦ a) (harmonicOnSurface_const C a) continuousOn_const
      hC_frontier_bound x hxC
  linarith

/--
%%handwave
name:
  Harmonic functions obey upper boundary bounds
statement:
  On a Perron domain with the componentwise maximum-principle geometry, a
  harmonic function continuous on the closed domain and bounded above by
  \(M\) on the boundary is bounded above by \(M\) throughout the domain.
proof:
  A harmonic function is subharmonic, so this is the subharmonic maximum
  principle applied to the same boundary bound.
-/
theorem harmonic_le_constant_of_boundary_le
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronDomain X) {u : X → ℝ} {M : ℝ}
    (hΩ_geometry : HasComponentwiseMaximumPrincipleGeometry Ω.carrier)
    (hu_continuous : ContinuousOn u (closure Ω.carrier))
    (hu_harmonic : IsHarmonicOnSurface Ω.carrier u)
    (hbd : ∀ x ∈ Ω.boundary, u x ≤ M) :
    ∀ x ∈ Ω.carrier, u x ≤ M := by
  exact subharmonic_le_constant_of_boundary_le Ω hΩ_geometry
    hu_continuous
    (harmonicOnSurface_subharmonic Ω.isOpen hu_harmonic)
    hbd

/--
%%handwave
name:
  Harmonic functions obey lower boundary bounds
statement:
  On a Perron domain with the componentwise maximum-principle geometry, a
  harmonic function continuous on the closed domain and bounded below by
  \(m\) on the boundary is bounded below by \(m\) throughout the domain.
proof:
  Apply the upper-bound maximum principle to the harmonic function \(m-u\),
  whose boundary values are nonpositive.
-/
theorem constant_le_harmonic_of_boundary_le
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronDomain X) {u : X → ℝ} {m : ℝ}
    (hΩ_geometry : HasComponentwiseMaximumPrincipleGeometry Ω.carrier)
    (hu_continuous : ContinuousOn u (closure Ω.carrier))
    (hu_harmonic : IsHarmonicOnSurface Ω.carrier u)
    (hbd : ∀ x ∈ Ω.boundary, m ≤ u x) :
    ∀ x ∈ Ω.carrier, m ≤ u x := by
  have hdiff_continuous :
      ContinuousOn (fun x ↦ m - u x) (closure Ω.carrier) :=
    continuousOn_const.sub hu_continuous
  have hdiff_harmonic :
      IsHarmonicOnSurface Ω.carrier (fun x ↦ m - u x) :=
    harmonicOnSurface_sub (harmonicOnSurface_const Ω.carrier m) hu_harmonic
  have hdiff_boundary :
      ∀ x ∈ Ω.boundary, m - u x ≤ 0 := by
    intro x hx
    linarith [hbd x hx]
  have hdiff_nonpositive :
      ∀ x ∈ Ω.carrier, m - u x ≤ 0 :=
    harmonic_le_constant_of_boundary_le Ω hΩ_geometry
      hdiff_continuous hdiff_harmonic hdiff_boundary
  intro x hx
  linarith [hdiff_nonpositive x hx]

/--
%%handwave
name:
  Harmonic functions compare from boundary inequalities
statement:
  On a Perron domain with the componentwise maximum-principle geometry, two
  harmonic functions continuous on the closed domain compare throughout the
  domain if they compare on the boundary.
proof:
  Apply the upper-bound maximum principle to the harmonic difference
  \(u-v\), whose boundary values are nonpositive.
-/
theorem harmonic_le_harmonic_of_boundary_le
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronDomain X) {u v : X → ℝ}
    (hΩ_geometry : HasComponentwiseMaximumPrincipleGeometry Ω.carrier)
    (hu_continuous : ContinuousOn u (closure Ω.carrier))
    (hu_harmonic : IsHarmonicOnSurface Ω.carrier u)
    (hv_continuous : ContinuousOn v (closure Ω.carrier))
    (hv_harmonic : IsHarmonicOnSurface Ω.carrier v)
    (hbd : ∀ x ∈ Ω.boundary, u x ≤ v x) :
    ∀ x ∈ Ω.carrier, u x ≤ v x := by
  have hdiff_continuous :
      ContinuousOn (fun x ↦ u x - v x) (closure Ω.carrier) :=
    hu_continuous.sub hv_continuous
  have hdiff_harmonic :
      IsHarmonicOnSurface Ω.carrier (fun x ↦ u x - v x) :=
    harmonicOnSurface_sub hu_harmonic hv_harmonic
  have hdiff_boundary :
      ∀ x ∈ Ω.boundary, u x - v x ≤ 0 := by
    intro x hx
    linarith [hbd x hx]
  have hdiff_nonpositive :
      ∀ x ∈ Ω.carrier, u x - v x ≤ 0 :=
    harmonic_le_constant_of_boundary_le Ω hΩ_geometry
      hdiff_continuous hdiff_harmonic hdiff_boundary
  intro x hx
  linarith [hdiff_nonpositive x hx]

/--
%%handwave
name:
  Perron-admissible functions obey the boundary maximum principle
statement:
  If a constant bounds the prescribed boundary data from above, then every
  Perron-admissible subfunction is bounded by that constant throughout the
  Perron domain.
proof:
  This is the maximum principle for subharmonic functions on a relatively
  compact domain, using upper semicontinuity on the closed domain and the
  boundary inequality.
-/
theorem perron_admissible_le_boundary_upper_bound
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronDomain X) (φ : PerronBoundaryData Ω)
    (hΩ_geometry : HasComponentwiseMaximumPrincipleGeometry Ω.carrier)
    {M : ℝ} (hM : ∀ x ∈ Ω.boundary, φ x ≤ M)
    {v : X → ℝ} (hv : IsPerronAdmissible Ω φ v) :
    ∀ x ∈ Ω.carrier, v x ≤ M := by
  exact subharmonic_le_constant_of_boundary_le Ω hΩ_geometry hv.1 hv.2.1
    (by
      intro x hx
      exact (hv.2.2 x hx).trans (hM x hx))

/--
%%handwave
name:
  Explicit upper bounds make Perron families locally bounded
statement:
  If a constant bounds the boundary data from above and the region has the
  componentwise maximum-principle geometry, then the Perron-admissible
  subfunctions are uniformly bounded above on each compact subset of the
  domain.
proof:
  The boundary maximum principle bounds every admissible subfunction by that
  same constant throughout the domain.
-/
theorem perron_family_locally_bounded_above_of_boundary_upper_bound
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronDomain X) (φ : PerronBoundaryData Ω)
    (hΩ_geometry : HasComponentwiseMaximumPrincipleGeometry Ω.carrier)
    {M : ℝ} (hM : ∀ x ∈ Ω.boundary, φ x ≤ M) :
    ∀ K : Set X, IsCompact K → K ⊆ Ω.carrier →
      ∃ M : ℝ, ∀ v : X → ℝ, IsPerronAdmissible Ω φ v → ∀ x ∈ K, v x ≤ M := by
  intro K _hK hKΩ
  refine ⟨M, ?_⟩
  intro v hv x hxK
  exact perron_admissible_le_boundary_upper_bound Ω φ hΩ_geometry hM hv x
    (hKΩ hxK)

/--
%%handwave
name:
  The Perron family is locally bounded above
statement:
  On a regular Perron domain, the Perron-admissible subfunctions are uniformly
  bounded above on each compact subset of the domain.
proof:
  A constant above the boundary values is a harmonic majorant.  The comparison
  principle for each Perron-admissible subfunction bounds it by that constant
  on the compact subset.
-/
theorem perron_family_locally_bounded_above
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronDomain X) (hΩreg : PerronRegularBoundary Ω)
    (φ : PerronBoundaryData Ω) :
    ∀ K : Set X, IsCompact K → K ⊆ Ω.carrier →
      ∃ M : ℝ, ∀ v : X → ℝ, IsPerronAdmissible Ω φ v → ∀ x ∈ K, v x ≤ M := by
  rcases PerronBoundaryData.exists_upper_bound φ with ⟨M, hM⟩
  exact perron_family_locally_bounded_above_of_boundary_upper_bound Ω φ
    hΩreg.1 hM

/--
%%handwave
name:
  Explicit boundary bounds make Perron families nonempty and locally bounded
statement:
  If the boundary data has explicit lower and upper bounds, then on a regular
  Perron domain the Perron family is nonempty and locally bounded above.
proof:
  The lower bound gives an admissible constant subfunction, while the upper
  bound gives a constant harmonic majorant by the boundary maximum principle.
-/
theorem perron_family_nonempty_and_locally_bounded_of_boundary_bounds
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronDomain X) (hΩreg : PerronRegularBoundary Ω)
    (φ : PerronBoundaryData Ω)
    {m M : ℝ}
    (hm : ∀ x ∈ Ω.boundary, m ≤ φ x)
    (hM : ∀ x ∈ Ω.boundary, φ x ≤ M) :
    (∃ v : X → ℝ, IsPerronAdmissible Ω φ v) ∧
      ∀ K : Set X, IsCompact K → K ⊆ Ω.carrier →
        ∃ M : ℝ, ∀ v : X → ℝ, IsPerronAdmissible Ω φ v → ∀ x ∈ K, v x ≤ M := by
  exact ⟨
    perron_family_nonempty_of_boundary_lower_bound Ω φ hm,
    perron_family_locally_bounded_above_of_boundary_upper_bound Ω φ hΩreg.1 hM⟩

/--
%%handwave
name:
  Perron family is nonempty and locally bounded
statement:
  For continuous boundary data on a relatively compact regular domain, the
  Perron family is nonempty and locally bounded above.
proof:
  Constants below the minimum boundary value give subfunctions, so the family
  is nonempty.  Constants above the maximum boundary value give harmonic
  majorants by comparison, so the subfunctions are uniformly bounded above on
  compact subsets.  Compactness of the closed domain supplies the needed
  boundary extrema.
-/
theorem perron_family_nonempty_and_locally_bounded
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronDomain X) (hΩreg : PerronRegularBoundary Ω)
    (φ : PerronBoundaryData Ω) :
    (∃ v : X → ℝ, IsPerronAdmissible Ω φ v) ∧
      ∀ K : Set X, IsCompact K → K ⊆ Ω.carrier →
        ∃ M : ℝ, ∀ v : X → ℝ, IsPerronAdmissible Ω φ v → ∀ x ∈ K, v x ≤ M := by
  exact ⟨
    perron_family_nonempty Ω φ,
    perron_family_locally_bounded_above Ω hΩreg φ⟩

/--
%%handwave
name:
  Perron value sets are nonempty from an explicit family
statement:
  At every point, the Perron value set is nonempty.
proof:
  The Perron family is nonempty, so any Perron-admissible subfunction supplies
  one value at the chosen point.
-/
theorem perronValueSet_nonempty_of_family_nonempty
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronDomain X) (φ : PerronBoundaryData Ω)
    (hfamily_nonempty : ∃ v : X → ℝ, IsPerronAdmissible Ω φ v)
    (x : X) :
    (perronValueSet Ω φ x).Nonempty := by
  rcases hfamily_nonempty with ⟨v, hv⟩
  exact ⟨v x, v, hv, rfl⟩

/--
%%handwave
name:
  Perron value sets are nonempty
statement:
  At every point of a relatively compact Perron domain, the Perron value set
  is nonempty.
proof:
  Compactness supplies a lower bound for the boundary data, so the Perron
  family is nonempty.
-/
theorem perronValueSet_nonempty
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronDomain X) (φ : PerronBoundaryData Ω) (x : X) :
    (perronValueSet Ω φ x).Nonempty := by
  exact perronValueSet_nonempty_of_family_nonempty Ω φ
    (perron_family_nonempty Ω φ) x

/--
%%handwave
name:
  A pointwise family bound bounds the Perron value set
statement:
  If all Perron-admissible subfunctions are bounded above by a common constant
  at a point, then the Perron value set at that point is bounded above by the
  same constant.
proof:
  Each member of the value set is the value of some admissible subfunction,
  so it is bounded by the assumed constant.
-/
theorem perronValueSet_bddAbove_of_family_bound
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronDomain X) (φ : PerronBoundaryData Ω) {x : X} {M : ℝ}
    (hbound : ∀ v : X → ℝ, IsPerronAdmissible Ω φ v → v x ≤ M) :
    BddAbove (perronValueSet Ω φ x) := by
  refine ⟨M, ?_⟩
  intro a ha
  rcases ha with ⟨v, hv, rfl⟩
  exact hbound v hv

/--
%%handwave
name:
  A pointwise family bound bounds the Perron envelope
statement:
  If all Perron-admissible subfunctions are bounded above by a common constant
  at a point and the Perron value set is nonempty there, then the Perron
  envelope is bounded above by that constant.
proof:
  This is the order-theoretic property of the supremum of a nonempty bounded
  set of real numbers.
-/
theorem perronEnvelope_le_of_family_bound
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronDomain X) (φ : PerronBoundaryData Ω) {x : X} {M : ℝ}
    (hne : (perronValueSet Ω φ x).Nonempty)
    (hbound : ∀ v : X → ℝ, IsPerronAdmissible Ω φ v → v x ≤ M) :
    perronEnvelope Ω φ x ≤ M := by
  rw [perronEnvelope_eq_sSup_perronValueSet]
  exact csSup_le hne (by
    intro a ha
    rcases ha with ⟨v, hv, rfl⟩
    exact hbound v hv)

/--
%%handwave
name:
  Perron-admissible functions lie below the envelope from boundedness
statement:
  If the Perron value set is bounded above at a point, then every
  Perron-admissible subfunction is bounded above by the Perron envelope at
  that point.
proof:
  The value of the subfunction belongs to the Perron value set, so it lies
  below the supremum of that set.
-/
theorem perronAdmissible_le_perronEnvelope_of_bddAbove
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronDomain X) (φ : PerronBoundaryData Ω) {v : X → ℝ}
    (hv : IsPerronAdmissible Ω φ v) {x : X}
    (hbdd : BddAbove (perronValueSet Ω φ x)) :
    v x ≤ perronEnvelope Ω φ x := by
  rw [perronEnvelope_eq_sSup_perronValueSet]
  exact le_csSup hbdd ⟨v, hv, rfl⟩

/--
%%handwave
name:
  Boundary upper bounds bound the Perron envelope
statement:
  If a constant bounds the boundary data from above, then it bounds the Perron
  envelope throughout the Perron domain.
proof:
  Every Perron-admissible subfunction is bounded by the constant by
  [the boundary maximum principle](lean:JJMath.Uniformization.perron_admissible_le_boundary_upper_bound),
  and then the supremum is bounded by the same constant.
-/
theorem perronEnvelope_le_boundary_upper_bound
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronDomain X) (φ : PerronBoundaryData Ω)
    (hΩ_geometry : HasComponentwiseMaximumPrincipleGeometry Ω.carrier)
    {M : ℝ} (hM : ∀ x ∈ Ω.boundary, φ x ≤ M) :
    ∀ x ∈ Ω.carrier, perronEnvelope Ω φ x ≤ M := by
  intro x hx
  exact perronEnvelope_le_of_family_bound Ω φ
    (perronValueSet_nonempty Ω φ x)
    (by
      intro v hv
      exact perron_admissible_le_boundary_upper_bound Ω φ hΩ_geometry hM hv x hx)

/--
%%handwave
name:
  Perron-admissible functions lie below the envelope
statement:
  On a regular Perron domain, every Perron-admissible subfunction is bounded
  above by the Perron envelope at each interior point.
proof:
  Choose a constant upper bound for the boundary data.  The boundary maximum
  principle bounds all admissible subfunctions by that constant, so the
  Perron value set is bounded above.  Then each admissible value lies below
  the supremum.
-/
theorem perronAdmissible_le_perronEnvelope
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronDomain X) (hΩreg : PerronRegularBoundary Ω)
    (φ : PerronBoundaryData Ω) {v : X → ℝ}
    (hv : IsPerronAdmissible Ω φ v) :
    ∀ x ∈ Ω.carrier, v x ≤ perronEnvelope Ω φ x := by
  rcases PerronBoundaryData.exists_upper_bound φ with ⟨M, hM⟩
  intro x hx
  have hbdd : BddAbove (perronValueSet Ω φ x) :=
    perronValueSet_bddAbove_of_family_bound Ω φ (x := x) (M := M)
      (by
        intro w hw
        exact perron_admissible_le_boundary_upper_bound Ω φ hΩreg.1 hM hw x hx)
  exact perronAdmissible_le_perronEnvelope_of_bddAbove Ω φ hv hbdd

/--
%%handwave
name:
  Locally bounded Perron families lie below the envelope
statement:
  If the Perron family is locally bounded above in the domain, then every
  Perron-admissible subfunction is bounded above by the Perron envelope at
  each interior point.
proof:
  Apply the local bound to the compact singleton containing the point.  This
  gives a pointwise upper bound for the Perron value set, and then the
  order-theoretic supremum property gives the desired inequality.
-/
theorem perronAdmissible_le_perronEnvelope_of_locally_bounded
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronDomain X) (φ : PerronBoundaryData Ω)
    (hfamily_locally_bounded :
      ∀ K : Set X, IsCompact K → K ⊆ Ω.carrier →
        ∃ M : ℝ, ∀ v : X → ℝ, IsPerronAdmissible Ω φ v → ∀ x ∈ K, v x ≤ M)
    {v : X → ℝ} (hv : IsPerronAdmissible Ω φ v) :
    ∀ x ∈ Ω.carrier, v x ≤ perronEnvelope Ω φ x := by
  intro x hxΩ
  have hsingleton_subset : ({x} : Set X) ⊆ Ω.carrier := by
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    simpa [hy] using hxΩ
  rcases hfamily_locally_bounded ({x} : Set X) isCompact_singleton
      hsingleton_subset with
    ⟨M, hM⟩
  have hbdd : BddAbove (perronValueSet Ω φ x) :=
    perronValueSet_bddAbove_of_family_bound Ω φ (x := x) (M := M)
      (by
        intro w hw
        exact hM w hw x (by simp))
  exact perronAdmissible_le_perronEnvelope_of_bddAbove Ω φ hv hbdd

/--
%%handwave
name:
  Admissible subfunctions approximate the envelope from an explicit family
statement:
  If \(a\) is strictly below the Perron envelope at an interior point, then
  some Perron-admissible subfunction has value greater than \(a\) at that
  point.
proof:
  Local boundedness at the singleton gives boundedness of the Perron value
  set at the point.  Since the envelope is the supremum of that value set,
  the defining property of the supremum supplies an admissible value above
  \(a\).
-/
theorem exists_perronAdmissible_gt_of_lt_perronEnvelope_of_family_nonempty
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronDomain X) (φ : PerronBoundaryData Ω)
    (hfamily_nonempty : ∃ v : X → ℝ, IsPerronAdmissible Ω φ v)
    (hfamily_locally_bounded :
      ∀ K : Set X, IsCompact K → K ⊆ Ω.carrier →
        ∃ M : ℝ, ∀ v : X → ℝ, IsPerronAdmissible Ω φ v → ∀ x ∈ K, v x ≤ M)
    {x : X} (hxΩ : x ∈ Ω.carrier) {a : ℝ}
    (ha : a < perronEnvelope Ω φ x) :
    ∃ v : X → ℝ, IsPerronAdmissible Ω φ v ∧ a < v x := by
  have hsingleton_subset : ({x} : Set X) ⊆ Ω.carrier := by
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    simpa [hy] using hxΩ
  rcases hfamily_locally_bounded ({x} : Set X) isCompact_singleton
      hsingleton_subset with
    ⟨M, hM⟩
  have hbdd : BddAbove (perronValueSet Ω φ x) :=
    perronValueSet_bddAbove_of_family_bound Ω φ (x := x) (M := M)
      (by
        intro v hv
        exact hM v hv x (by simp))
  rw [perronEnvelope_eq_sSup_perronValueSet] at ha
  rcases (lt_csSup_iff hbdd
      (perronValueSet_nonempty_of_family_nonempty Ω φ hfamily_nonempty x)).1 ha with
    ⟨b, hb, hab⟩
  rcases hb with ⟨v, hv, rfl⟩
  exact ⟨v, hv, hab⟩

/--
%%handwave
name:
  Admissible subfunctions approximate the envelope at a point
statement:
  If \(a\) is strictly below the Perron envelope at an interior point, then
  some Perron-admissible subfunction has value greater than \(a\) at that
  point.
proof:
  The relatively compact version supplies nonemptiness from the compact
  boundary, then applies the version with an explicit nonempty family.
-/
theorem exists_perronAdmissible_gt_of_lt_perronEnvelope
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronDomain X) (φ : PerronBoundaryData Ω)
    (hfamily_locally_bounded :
      ∀ K : Set X, IsCompact K → K ⊆ Ω.carrier →
        ∃ M : ℝ, ∀ v : X → ℝ, IsPerronAdmissible Ω φ v → ∀ x ∈ K, v x ≤ M)
    {x : X} (hxΩ : x ∈ Ω.carrier) {a : ℝ}
    (ha : a < perronEnvelope Ω φ x) :
    ∃ v : X → ℝ, IsPerronAdmissible Ω φ v ∧ a < v x := by
  exact exists_perronAdmissible_gt_of_lt_perronEnvelope_of_family_nonempty
    Ω φ (perron_family_nonempty Ω φ) hfamily_locally_bounded hxΩ ha

/--
%%handwave
name:
  Admissible subfunctions approximate the envelope within epsilon
statement:
  At each interior point and for every positive epsilon, some
  Perron-admissible subfunction has value within epsilon of the envelope from
  below.
proof:
  Apply the strict approximation property of the supremum to
  \(\mathcal P_\varphi(x)-\varepsilon<\mathcal P_\varphi(x)\), using
  nonemptiness and local boundedness of the admissible family.
-/
theorem exists_perronAdmissible_envelope_sub_lt
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronDomain X) (φ : PerronBoundaryData Ω)
    (hfamily_locally_bounded :
      ∀ K : Set X, IsCompact K → K ⊆ Ω.carrier →
        ∃ M : ℝ, ∀ v : X → ℝ, IsPerronAdmissible Ω φ v → ∀ x ∈ K, v x ≤ M)
    {x : X} (hxΩ : x ∈ Ω.carrier) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : X → ℝ,
      IsPerronAdmissible Ω φ v ∧ perronEnvelope Ω φ x - ε < v x := by
  exact exists_perronAdmissible_gt_of_lt_perronEnvelope Ω φ
    hfamily_locally_bounded hxΩ (by linarith)

/--
%%handwave
name:
  Admissible subfunctions approximate the envelope within epsilon from an explicit family
statement:
  If the Perron family is explicitly nonempty and locally bounded above, then
  at each interior point and for every positive epsilon, some admissible
  subfunction has value within epsilon of the envelope from below.
proof:
  [For a nonempty locally bounded Perron family, every number strictly below the envelope is exceeded by some admissible subfunction](lean:JJMath.Uniformization.exists_perronAdmissible_gt_of_lt_perronEnvelope_of_family_nonempty). Take that number to be $P_\Omega\varphi(x)-\varepsilon$.
-/
theorem exists_perronAdmissible_envelope_sub_lt_of_family_nonempty
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronDomain X) (φ : PerronBoundaryData Ω)
    (hfamily_nonempty : ∃ v : X → ℝ, IsPerronAdmissible Ω φ v)
    (hfamily_locally_bounded :
      ∀ K : Set X, IsCompact K → K ⊆ Ω.carrier →
        ∃ M : ℝ, ∀ v : X → ℝ, IsPerronAdmissible Ω φ v → ∀ x ∈ K, v x ≤ M)
    {x : X} (hxΩ : x ∈ Ω.carrier) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : X → ℝ,
      IsPerronAdmissible Ω φ v ∧ perronEnvelope Ω φ x - ε < v x := by
  exact exists_perronAdmissible_gt_of_lt_perronEnvelope_of_family_nonempty
    Ω φ hfamily_nonempty hfamily_locally_bounded hxΩ (by linarith)

/--
%%handwave
name:
  Perron envelope is lower semicontinuous
statement:
  If the Perron family is locally bounded above in the domain, then the
  Perron envelope is lower semicontinuous in the domain.
proof:
  The envelope is the supremum of the admissible subfunctions.  Each
  admissible subfunction is continuous on the closed domain, hence lower
  semicontinuous in the domain.  Mathlib's theorem that locally bounded
  suprema of lower semicontinuous functions are lower semicontinuous then
  applies.
-/
theorem perronEnvelope_lowerSemicontinuousOn
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronDomain X) (φ : PerronBoundaryData Ω)
    (hfamily_locally_bounded :
      ∀ K : Set X, IsCompact K → K ⊆ Ω.carrier →
        ∃ M : ℝ, ∀ v : X → ℝ, IsPerronAdmissible Ω φ v → ∀ x ∈ K, v x ≤ M) :
    LowerSemicontinuousOn (perronEnvelope Ω φ) Ω.carrier := by
  have hbdd :
      ∀ x ∈ Ω.carrier,
        BddAbove (Set.range fun v : PerronSubfunction Ω φ ↦ v.val x) := by
    intro x hxΩ
    have hsingleton_subset : ({x} : Set X) ⊆ Ω.carrier := by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      simpa [hy] using hxΩ
    rcases hfamily_locally_bounded ({x} : Set X) isCompact_singleton
        hsingleton_subset with
      ⟨M, hM⟩
    refine ⟨M, ?_⟩
    intro a ha
    rcases ha with ⟨v, rfl⟩
    exact hM v.val v.property x (by simp)
  have hsub_lsc :
      ∀ v : PerronSubfunction Ω φ,
        LowerSemicontinuousOn v.val Ω.carrier := by
    intro v
    exact (v.property.1.mono subset_closure).lowerSemicontinuousOn
  have hlsup :
      LowerSemicontinuousOn
        (fun x ↦ ⨆ v : PerronSubfunction Ω φ, v.val x) Ω.carrier :=
    lowerSemicontinuousOn_ciSup hbdd hsub_lsc
  have henv_eq :
      perronEnvelope Ω φ =
        fun x ↦ ⨆ v : PerronSubfunction Ω φ, v.val x := by
    funext x
    exact perronEnvelope_eq_iSup_subfunctions Ω φ x
  rw [henv_eq]
  exact hlsup

/--
%%handwave
name:
  Locally bounded Perron families give locally bounded envelopes
statement:
  If the Perron family is locally bounded above in the domain, then the
  Perron envelope is locally bounded above in the domain.
proof:
  The common bound for all admissible subfunctions on a compact set is a
  pointwise bound for each Perron value set, hence also for its supremum.
-/
theorem perronEnvelope_locally_bounded_above_of_family_locally_bounded
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronDomain X) (φ : PerronBoundaryData Ω)
    (hfamily_locally_bounded :
      ∀ K : Set X, IsCompact K → K ⊆ Ω.carrier →
        ∃ M : ℝ, ∀ v : X → ℝ, IsPerronAdmissible Ω φ v → ∀ x ∈ K, v x ≤ M) :
    ∀ K : Set X, IsCompact K → K ⊆ Ω.carrier →
      ∃ M : ℝ, ∀ x ∈ K, perronEnvelope Ω φ x ≤ M := by
  intro K hK hKΩ
  rcases hfamily_locally_bounded K hK hKΩ with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro x hxK
  exact perronEnvelope_le_of_family_bound Ω φ
    (perronValueSet_nonempty Ω φ x)
    (by
      intro v hv
      exact hM v hv x hxK)

/--
%%handwave
name:
  Nonempty locally bounded Perron families give locally bounded envelopes
statement:
  If the Perron family is explicitly nonempty and locally bounded above in the
  domain, then the Perron envelope is locally bounded above in the domain.
proof:
  The common bound for all admissible subfunctions on a compact set is a
  pointwise bound for each Perron value set, hence also for its supremum.
-/
theorem perronEnvelope_locally_bounded_above_of_family_nonempty_of_family_locally_bounded
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronDomain X) (φ : PerronBoundaryData Ω)
    (hfamily_nonempty : ∃ v : X → ℝ, IsPerronAdmissible Ω φ v)
    (hfamily_locally_bounded :
      ∀ K : Set X, IsCompact K → K ⊆ Ω.carrier →
        ∃ M : ℝ, ∀ v : X → ℝ, IsPerronAdmissible Ω φ v → ∀ x ∈ K, v x ≤ M) :
    ∀ K : Set X, IsCompact K → K ⊆ Ω.carrier →
      ∃ M : ℝ, ∀ x ∈ K, perronEnvelope Ω φ x ≤ M := by
  intro K hK hKΩ
  rcases hfamily_locally_bounded K hK hKΩ with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro x hxK
  exact perronEnvelope_le_of_family_bound Ω φ
    (perronValueSet_nonempty_of_family_nonempty Ω φ hfamily_nonempty x)
    (by
      intro v hv
      exact hM v hv x hxK)

/--
%%handwave
name:
  The Perron envelope is locally bounded above
statement:
  On a regular Perron domain, the Perron envelope is bounded above on every
  compact subset of the domain.
proof:
  Local boundedness of the Perron family gives a common bound for all
  admissible values on the compact set.  Taking the supremum preserves that
  bound pointwise.
-/
theorem perron_envelope_locally_bounded_above
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronDomain X) (hΩreg : PerronRegularBoundary Ω)
    (φ : PerronBoundaryData Ω) :
    ∀ K : Set X, IsCompact K → K ⊆ Ω.carrier →
      ∃ M : ℝ, ∀ x ∈ K, perronEnvelope Ω φ x ≤ M := by
  intro K hK hKΩ
  rcases perron_family_locally_bounded_above Ω hΩreg φ K hK hKΩ with
    ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro x hxK
  exact perronEnvelope_le_of_family_bound Ω φ
    (perronValueSet_nonempty Ω φ x)
    (by
      intro v hv
      exact hM v hv x hxK)

/--
%%handwave
name:
  Compactly contained coordinate Perron disks
statement:
  Every point of a Perron domain lies in a coordinate Perron disk whose closure
  is contained in the domain.
proof:
  Choose a complex coordinate centered at the point and then choose a small
  closed Euclidean disk contained both in the chart target and in the image of
  the domain.  Transport the disk back through the chart.
-/
theorem exists_coordinate_perron_disk_compactly_contained
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronDomain X) {x : X} (hx : x ∈ Ω.carrier) :
    ∃ V : PerronDomain X,
      x ∈ V.carrier ∧
        IsCoordinatePerronDisk V ∧
          closure V.carrier ⊆ Ω.carrier ∧
            IsPreconnected V.carrier ∧
              (frontier V.carrier).Nonempty := by
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ x
  let c : ℂ := e x
  have hx_source : x ∈ e.source := mem_chart_source ℂ x
  have he : e ∈ atlas ℂ X := chart_mem_atlas ℂ x
  have hc_target : c ∈ e.target := e.map_source hx_source
  let N : Set ℂ := e.target ∩ e.symm ⁻¹' Ω.carrier
  have hN_open : IsOpen N :=
    e.isOpen_inter_preimage_symm Ω.isOpen
  have hcN : c ∈ N := by
    refine ⟨hc_target, ?_⟩
    simpa [c, e.left_inv hx_source] using hx
  rcases Metric.mem_nhds_iff.mp (hN_open.mem_nhds hcN) with
    ⟨R, hRpos, hball_subset_N⟩
  let r : ℝ := R / 2
  have hr : 0 < r := by
    dsimp [r]
    linarith
  have hclosed_subset_N : Metric.closedBall c r ⊆ N := by
    intro z hz
    exact hball_subset_N (Metric.closedBall_subset_ball (by
      dsimp [r]
      linarith) hz)
  have hclosed_target : Metric.closedBall c r ⊆ e.target := by
    intro z hz
    exact (hclosed_subset_N hz).1
  have hclosed_domain : ∀ z ∈ Metric.closedBall c r, e.symm z ∈ Ω.carrier := by
    intro z hz
    exact (hclosed_subset_N hz).2
  let carrier : Set X := e.source ∩ e ⁻¹' Metric.ball c r
  have hcarrier_open : IsOpen carrier :=
    e.isOpen_inter_preimage Metric.isOpen_ball
  have hx_ball : e x ∈ Metric.ball c r := by
    simpa [c] using (Metric.mem_ball_self hr : c ∈ Metric.ball c r)
  have hcarrier_nonempty : carrier.Nonempty := by
    refine ⟨x, ?_⟩
    exact ⟨hx_source, hx_ball⟩
  let K : Set X := e.symm '' Metric.closedBall c r
  have hcarrier_subset_K : carrier ⊆ K := by
    intro y hy
    refine ⟨e y, Metric.ball_subset_closedBall hy.2, ?_⟩
    exact e.left_inv hy.1
  have hK_compact : IsCompact K :=
    (isCompact_closedBall c r).image_of_continuousOn
      (e.continuousOn_symm.mono hclosed_target)
  have hclosure_carrier_subset_K : closure carrier ⊆ K :=
    closure_minimal hcarrier_subset_K hK_compact.isClosed
  have hcarrier_compact_closure : IsCompact (closure carrier) :=
    hK_compact.of_isClosed_subset isClosed_closure hclosure_carrier_subset_K
  let V : PerronDomain X :=
    { carrier := carrier
      isOpen := hcarrier_open
      nonempty := hcarrier_nonempty
      compact_closure := hcarrier_compact_closure }
  have hV_mem : x ∈ V.carrier := by
    change x ∈ carrier
    exact ⟨hx_source, hx_ball⟩
  have hV_coord : IsCoordinatePerronDisk V := by
    exact ⟨e, he, c, r, hr, hclosed_target, rfl⟩
  have hV_closure_subset_K : closure V.carrier ⊆ K := by
    change closure carrier ⊆ K
    exact hclosure_carrier_subset_K
  have hVΩ : closure V.carrier ⊆ Ω.carrier := by
    intro y hy
    rcases hV_closure_subset_K hy with ⟨z, hz, rfl⟩
    exact hclosed_domain z hz
  have hball_target : Metric.ball c r ⊆ e.target := by
    intro z hz
    exact hclosed_target (Metric.ball_subset_closedBall hz)
  have himage : e.IsImage V.carrier (Metric.ball c r) := by
    intro y hy_source
    change e y ∈ Metric.ball c r ↔ y ∈ carrier
    exact ⟨fun hy_ball ↦ ⟨hy_source, hy_ball⟩, fun hy ↦ hy.2⟩
  have hV_preconnected : IsPreconnected V.carrier := by
    have hV_subset_source : V.carrier ⊆ e.source := by
      intro y hy
      change y ∈ carrier at hy
      exact hy.1
    have hV_eq : V.carrier = e.symm '' Metric.ball c r := by
      have hsymm := himage.symm_image_eq
      have htarget_inter : e.target ∩ Metric.ball c r = Metric.ball c r :=
        Set.inter_eq_right.mpr hball_target
      have hsource_inter : e.source ∩ V.carrier = V.carrier :=
        Set.inter_eq_right.mpr hV_subset_source
      rw [htarget_inter, hsource_inter] at hsymm
      exact hsymm.symm
    rw [hV_eq]
    exact Metric.isPreconnected_ball.image e.symm
      (e.continuousOn_symm.mono hball_target)
  have hV_frontier_nonempty : (frontier V.carrier).Nonempty := by
    have hfrontier_ball_nonempty : (frontier (Metric.ball c r)).Nonempty := by
      rw [frontier_ball c hr.ne']
      exact NormedSpace.sphere_nonempty.mpr hr.le
    rcases hfrontier_ball_nonempty with ⟨z, hz_frontier⟩
    have hz_target : z ∈ e.target :=
      hclosed_target
        (frontier_subset_closure.trans Metric.closure_ball_subset_closedBall hz_frontier)
    refine ⟨e.symm z, ?_⟩
    exact (himage.frontier.symm_apply_mem_iff hz_target).2 hz_frontier
  exact ⟨V, hV_mem, hV_coord, hVΩ, hV_preconnected, hV_frontier_nonempty⟩

/--
%%handwave
name:
  Surface points lie in compact coordinate Perron disks
statement:
  Every point of a Riemann surface lies in a compact coordinate Perron disk.
proof:
  First choose a relatively compact open neighborhood of the point.  Then use
  the compactly contained coordinate-disk construction inside that
  neighborhood.
-/
theorem exists_coordinate_perron_disk_mem
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X] (x : X) :
    ∃ V : PerronDomain X,
      x ∈ V.carrier ∧
        IsCoordinatePerronDisk V ∧
          IsPreconnected V.carrier ∧
            (frontier V.carrier).Nonempty := by
  rcases exists_surface_open_nhds_isCompact_closure_subset
      (X := X) isOpen_univ (show x ∈ (Set.univ : Set X) from trivial) with
    ⟨Ωcarrier, hΩopen, hxΩ, _hΩclosure_subset, hΩcompact⟩
  let Ω : PerronDomain X :=
    { carrier := Ωcarrier
      isOpen := hΩopen
      nonempty := ⟨x, hxΩ⟩
      compact_closure := hΩcompact }
  rcases exists_coordinate_perron_disk_compactly_contained Ω hxΩ with
    ⟨V, hxV, hV_coord, _hVΩ, hV_preconnected, hV_frontier_nonempty⟩
  exact ⟨V, hxV, hV_coord, hV_preconnected, hV_frontier_nonempty⟩

/--
%%handwave
name:
  Compactly contained coordinate disks in Perron-open regions
statement:
  Every point of a Perron-open region lies in a coordinate Perron disk whose
  closure is contained in the region.
proof:
  First choose a relatively compact open neighborhood of the point inside the
  open region.  Then apply the compactly contained coordinate-disk
  construction to that relatively compact neighborhood.
-/
theorem exists_coordinate_perron_disk_compactly_contained_open
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronOpen X) {x : X} (hx : x ∈ Ω.carrier) :
    ∃ V : PerronDomain X,
      x ∈ V.carrier ∧
        IsCoordinatePerronDisk V ∧
          closure V.carrier ⊆ Ω.carrier ∧
            IsPreconnected V.carrier ∧
              (frontier V.carrier).Nonempty := by
  rcases exists_surface_open_nhds_isCompact_closure_subset
      (X := X) Ω.isOpen hx with
    ⟨U, hU_open, hxU, hU_closure_subset, hU_compact⟩
  let D : PerronDomain X :=
    { carrier := U
      isOpen := hU_open
      nonempty := ⟨x, hxU⟩
      compact_closure := hU_compact }
  rcases exists_coordinate_perron_disk_compactly_contained D hxU with
    ⟨V, hxV, hV_coord, hVD, hV_preconnected, hV_frontier_nonempty⟩
  have hVΩ : closure V.carrier ⊆ Ω.carrier := by
    intro y hy
    exact hU_closure_subset (subset_closure (hVD hy))
  exact ⟨V, hxV, hV_coord, hVΩ, hV_preconnected, hV_frontier_nonempty⟩

/--
%%handwave
name:
  Intersections with open sets have componentwise maximum-principle geometry
statement:
  If a relatively compact connected open set has nonempty boundary, then its
  intersection with any open set has the componentwise geometry needed for
  the maximum principle.
proof:
  Around a point of the intersection, take the connected component of the
  intersection.  Local connectedness of the surface makes this component
  open, and connectedness is built into the definition of connected component.
  Its closure is compact because it lies in the compact closure of the larger
  comparison domain.  Its boundary is nonempty: otherwise it would be clopen
  and would force the whole connected comparison domain into this component,
  contradicting the nonempty boundary of the comparison domain.  Finally,
  because the component is closed relative to the open intersection, any
  boundary point of the component is a boundary point of the intersection.
-/
theorem hasComponentwiseMaximumPrincipleGeometry_inter_open_of_preconnected
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {W U : Set X}
    (hW_open : IsOpen W)
    (hW_preconnected : IsPreconnected W)
    (hW_frontier_nonempty : (frontier W).Nonempty)
    (hW_compact : IsCompact (closure W))
    (hU_open : IsOpen U) :
    HasComponentwiseMaximumPrincipleGeometry (W ∩ U) := by
  intro x hx
  let A : Set X := W ∩ U
  let C : Set X := connectedComponentIn A x
  have hA_open : IsOpen A := hW_open.inter hU_open
  have hxA : x ∈ A := hx
  haveI : LocallyConnectedSpace X := ChartedSpace.locallyConnectedSpace ℂ X
  have hxC : x ∈ C := by
    dsimp [C]
    exact mem_connectedComponentIn hxA
  have hC_open : IsOpen C := by
    dsimp [C]
    exact hA_open.connectedComponentIn
  have hC_preconnected : IsPreconnected C := by
    dsimp [C]
    exact isPreconnected_connectedComponentIn
  have hC_subsetA : C ⊆ A := by
    dsimp [C]
    exact connectedComponentIn_subset A x
  have hC_subsetW : C ⊆ W :=
    hC_subsetA.trans Set.inter_subset_left
  have hC_compact : IsCompact (closure C) :=
    hW_compact.of_isClosed_subset isClosed_closure (closure_mono hC_subsetW)
  have hC_frontier_nonempty : (frontier C).Nonempty := by
    by_contra hfrontier_not_nonempty
    have hfrontier_empty : frontier C = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hfrontier_not_nonempty
    have hC_closed : IsClosed C :=
      (isClopen_iff_frontier_eq_empty.mpr hfrontier_empty).1
    have hW_subsetC : W ⊆ C := by
      have hcover : W ⊆ C ∪ Cᶜ := by
        intro y _hy
        by_cases hyC : y ∈ C
        · exact Or.inl hyC
        · exact Or.inr hyC
      have hnonempty : (W ∩ C).Nonempty := ⟨x, hx.1, hxC⟩
      exact hW_preconnected.subset_left_of_subset_union
        hC_open hC_closed.isOpen_compl disjoint_compl_right hcover hnonempty
    have hC_eqW : C = W :=
      subset_antisymm hC_subsetW hW_subsetC
    have hfrontierW_empty : frontier W = ∅ := by
      rw [← hC_eqW, hfrontier_empty]
    exact hW_frontier_nonempty.ne_empty hfrontierW_empty
  have hC_frontier_subset : frontier C ⊆ frontier A := by
    intro y hy
    have hy_closureA : y ∈ closure A :=
      closure_mono hC_subsetA (frontier_subset_closure hy)
    have hy_notA : y ∉ A := by
      intro hyA
      have hyC : y ∈ C :=
        mem_connectedComponentIn_of_mem_closure_of_mem hxA hyA
          (frontier_subset_closure hy)
      have hy_inter : y ∈ C ∩ frontier C := ⟨hyC, hy⟩
      rw [hC_open.inter_frontier_eq] at hy_inter
      exact hy_inter
    rw [frontier, hA_open.interior_eq]
    exact ⟨hy_closureA, hy_notA⟩
  exact ⟨C, hxC, hC_open, hC_preconnected, hC_subsetA, hC_compact,
    hC_frontier_nonempty, hC_frontier_subset⟩

/--
%%handwave
name:
  Coordinate disk overlaps have maximum-principle geometry
statement:
  The overlap of a compactly contained coordinate Perron disk with a
  connected relatively compact comparison domain has the componentwise
  geometry needed by the maximum principle.
proof:
  In a surface, open subsets are locally connected.  Components of the
  overlap are open connected regions; compact containment gives compact
  closures, and the coordinate disk prevents interior components with empty
  frontier.
-/
theorem coordinate_perron_disk_overlap_geometry
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω V : PerronDomain X)
    (_hV_coord : IsCoordinatePerronDisk V)
    (_hVΩ : closure V.carrier ⊆ Ω.carrier) :
    ∀ W : Set X,
      IsOpen W →
        IsPreconnected W →
          (frontier W).Nonempty →
            W ⊆ Ω.carrier →
              IsCompact (closure W) →
                closure W ⊆ Ω.carrier →
                  HasComponentwiseMaximumPrincipleGeometry (W ∩ V.carrier) := by
  intro W hW_open hW_preconnected hW_frontier_nonempty _hWΩ hW_compact _hW_closureΩ
  exact hasComponentwiseMaximumPrincipleGeometry_inter_open_of_preconnected
    hW_open hW_preconnected hW_frontier_nonempty hW_compact V.isOpen

/--
%%handwave
name:
  Coordinate disk overlaps in Perron-open regions have maximum-principle geometry
statement:
  The overlap of a coordinate Perron disk with a connected relatively compact
  comparison domain inside a Perron-open region has the componentwise geometry
  needed by the maximum principle.
proof:
  The comparison region and coordinate disk are open.  The general
  componentwise-geometry theorem for intersecting a preconnected relatively
  compact open set with another open set applies.
-/
theorem coordinate_perron_disk_overlap_geometry_open
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronOpen X) (V : PerronDomain X)
    (_hV_coord : IsCoordinatePerronDisk V)
    (_hVΩ : closure V.carrier ⊆ Ω.carrier) :
    ∀ W : Set X,
      IsOpen W →
        IsPreconnected W →
          (frontier W).Nonempty →
            W ⊆ Ω.carrier →
              IsCompact (closure W) →
                closure W ⊆ Ω.carrier →
                  HasComponentwiseMaximumPrincipleGeometry (W ∩ V.carrier) := by
  intro W hW_open hW_preconnected hW_frontier_nonempty _hWΩ hW_compact _hW_closureΩ
  exact hasComponentwiseMaximumPrincipleGeometry_inter_open_of_preconnected
    hW_open hW_preconnected hW_frontier_nonempty hW_compact V.isOpen

/--
%%handwave
name:
  Perron subfunctions have admissible harmonic replacements
statement:
  On a compactly contained coordinate disk, every Perron-admissible
  subfunction has a harmonic replacement whose patch is again
  Perron-admissible.
proof:
  The restriction of the subfunction to the closed coordinate disk is
  continuous because the disk closure lies in the outer domain.  Solve the
  coordinate-disk Dirichlet problem to get the harmonic replacement.  The
  patched function stays admissible by [harmonic replacement preserves Perron admissibility](lean:JJMath.Uniformization.harmonic_replacement_preserves_admissibility).
-/
theorem perronAdmissible_has_admissible_harmonic_replacement
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω V : PerronDomain X) (φ : PerronBoundaryData Ω)
    (hV_coord : IsCoordinatePerronDisk V)
    (hVΩ : closure V.carrier ⊆ Ω.carrier)
    (hV_preconnected : IsPreconnected V.carrier)
    (hV_frontier_nonempty : (frontier V.carrier).Nonempty)
    (hOverlap_geometry :
      ∀ W : Set X,
        IsOpen W →
          IsPreconnected W →
            (frontier W).Nonempty →
              W ⊆ Ω.carrier →
                IsCompact (closure W) →
                  closure W ⊆ Ω.carrier →
                    HasComponentwiseMaximumPrincipleGeometry (W ∩ V.carrier))
    {v : X → ℝ}
    (hv : IsPerronAdmissible Ω φ v) :
    ∃ h : X → ℝ,
      IsHarmonicReplacement V v h ∧
        IsPerronAdmissible Ω φ (harmonicReplacementPatch V v h) := by
  have hvV_cont : ContinuousOn v (closure V.carrier) :=
    hv.1.mono (by
      intro x hx
      exact subset_closure (hVΩ hx))
  rcases harmonic_replacement_exists V hV_coord v hvV_cont with ⟨h, hh⟩
  refine ⟨h, hh, ?_⟩
  exact harmonic_replacement_preserves_admissibility Ω V φ hVΩ
    hV_preconnected hV_frontier_nonempty hOverlap_geometry hv hh

/--
%%handwave
name:
  Harmonic replacements lie below the Perron envelope
statement:
  Under local boundedness of the Perron family, the harmonic replacement of a
  Perron-admissible subfunction is bounded above by the Perron envelope on
  the replacement disk whenever the patched replacement is admissible.
proof:
  The patched replacement is admissible, hence lies below the envelope by
  [local boundedness of the Perron family](lean:JJMath.Uniformization.perronAdmissible_le_perronEnvelope_of_locally_bounded).
  Inside the coordinate disk the patch is exactly the harmonic replacement.
-/
theorem harmonicReplacement_le_perronEnvelope_of_patch_admissible
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω V : PerronDomain X) (φ : PerronBoundaryData Ω)
    (hVΩ : closure V.carrier ⊆ Ω.carrier)
    (hfamily_locally_bounded :
      ∀ K : Set X, IsCompact K → K ⊆ Ω.carrier →
        ∃ M : ℝ, ∀ v : X → ℝ, IsPerronAdmissible Ω φ v → ∀ x ∈ K, v x ≤ M)
    {v h : X → ℝ}
    (hpatch :
      IsPerronAdmissible Ω φ (harmonicReplacementPatch V v h)) :
    ∀ x ∈ V.carrier, h x ≤ perronEnvelope Ω φ x := by
  intro x hxV
  have hxΩ : x ∈ Ω.carrier := hVΩ (subset_closure hxV)
  have hle :=
    perronAdmissible_le_perronEnvelope_of_locally_bounded Ω φ
      hfamily_locally_bounded hpatch x hxΩ
  simpa [harmonicReplacementPatch_eq_replacement_of_mem V v h hxV] using hle

/--
%%handwave
name:
  Bounded Perron-open subfunctions have bounded admissible harmonic replacements
statement:
  On a compactly contained coordinate disk, every bounded Perron-open
  admissible subfunction has a harmonic replacement whose patch is again
  bounded Perron-open admissible.
proof:
  Solve the Dirichlet problem on the coordinate disk using the original
  function as boundary data.  Harmonic replacement preserves Perron-open
  admissibility, and the maximum principle preserves the fixed upper bound.
-/
theorem boundedPerronOpenAdmissible_has_admissible_harmonic_replacement
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronOpen X) (V : PerronDomain X)
    (φ : PerronOpenBoundaryData Ω) (M : ℝ)
    (hV_coord : IsCoordinatePerronDisk V)
    (hVΩ : closure V.carrier ⊆ Ω.carrier)
    (hV_preconnected : IsPreconnected V.carrier)
    (hV_frontier_nonempty : (frontier V.carrier).Nonempty)
    (hOverlap_geometry :
      ∀ W : Set X,
        IsOpen W →
          IsPreconnected W →
            (frontier W).Nonempty →
              W ⊆ Ω.carrier →
                IsCompact (closure W) →
                  closure W ⊆ Ω.carrier →
                    HasComponentwiseMaximumPrincipleGeometry (W ∩ V.carrier))
    {v : X → ℝ}
    (hv : IsBoundedPerronOpenAdmissible Ω φ M v) :
    ∃ h : X → ℝ,
      IsHarmonicReplacement V v h ∧
        IsBoundedPerronOpenAdmissible Ω φ M
          (harmonicReplacementPatch V v h) := by
  have hvV_cont : ContinuousOn v (closure V.carrier) :=
    hv.1.1.mono (by
      intro x hx
      exact subset_closure (hVΩ hx))
  rcases harmonic_replacement_exists V hV_coord v hvV_cont with ⟨h, hh⟩
  refine ⟨h, hh, ?_⟩
  exact harmonic_replacement_preserves_bounded_open_admissibility Ω V φ M
    hVΩ hV_preconnected hV_frontier_nonempty hOverlap_geometry hv hh

/--
%%handwave
name:
  Bounded Perron-open harmonic replacements lie below the envelope
statement:
  If the patched harmonic replacement is bounded Perron-open admissible, then
  the harmonic replacement lies below the bounded Perron-open envelope on the
  replacement disk.
proof:
  On the replacement disk the patch is exactly the harmonic replacement, and
  the patched function contributes a value to the bounded Perron-open value
  set.
-/
theorem harmonicReplacement_le_boundedPerronOpenEnvelope_of_patch_admissible
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronOpen X) (V : PerronDomain X)
    (φ : PerronOpenBoundaryData Ω) (M : ℝ)
    (hVΩ : closure V.carrier ⊆ Ω.carrier)
    {v h : X → ℝ}
    (hpatch :
      IsBoundedPerronOpenAdmissible Ω φ M
        (harmonicReplacementPatch V v h)) :
    ∀ x ∈ V.carrier, h x ≤ boundedPerronOpenEnvelope Ω φ M x := by
  intro x hxV
  have hxΩ : x ∈ Ω.carrier := hVΩ (subset_closure hxV)
  rw [boundedPerronOpenEnvelope]
  exact le_csSup (boundedPerronOpenValueSet_bddAbove Ω φ M hxΩ) (by
    refine ⟨harmonicReplacementPatch V v h, hpatch, ?_⟩
    rw [harmonicReplacementPatch_eq_replacement_of_mem V v h hxV])

/--
%%handwave
name:
  Directed harmonic minorant value sets are directed
statement:
  If a family of functions is directed by pointwise domination on a region,
  then its set of values at any point of that region is directed in the real
  line.
proof:
  Given two values, choose functions in the family realizing them.  The
  pointwise directedness hypothesis supplies a third function in the family
  dominating both at the chosen point.
-/
theorem directed_harmonic_minorants_valueSet_directedOn
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (V : PerronDomain X) (H : Set (X → ℝ))
    (hH_directed :
      ∀ h₁ ∈ H, ∀ h₂ ∈ H,
        ∃ h₃ ∈ H, ∀ x ∈ V.carrier, h₁ x ≤ h₃ x ∧ h₂ x ≤ h₃ x)
    {x : X} (hxV : x ∈ V.carrier) :
    DirectedOn (· ≤ ·) {a : ℝ | ∃ h ∈ H, a = h x} := by
  intro a ha b hb
  rcases ha with ⟨h₁, hh₁, rfl⟩
  rcases hb with ⟨h₂, hh₂, rfl⟩
  rcases hH_directed h₁ hh₁ h₂ hh₂ with ⟨h₃, hh₃, hle⟩
  refine ⟨h₃ x, ?_, ?_, ?_⟩
  · exact ⟨h₃, hh₃, rfl⟩
  · exact (hle x hxV).1
  · exact (hle x hxV).2

/--
%%handwave
name:
  Cofinal harmonic minorants have the prescribed pointwise supremum
statement:
  Let \(P\) be a lower semicontinuous function on a coordinate disk.  Suppose
  \(P\) is the pointwise supremum, up to arbitrary epsilon, of a directed
  family below \(P\).  Then at each point the supremum of the values of that
  family is exactly \(P\).
proof:
  The values are directed by
  [pointwise directedness](lean:JJMath.Uniformization.directed_harmonic_minorants_valueSet_directedOn).
  The upper-bound property says their supremum is at most \(P(x)\), while
  epsilon-cofinality gives a family value above every number strictly below
  \(P(x)\).
-/
theorem directed_harmonic_minorants_pointwise_sSup
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (V : PerronDomain X) (P : X → ℝ) (H : Set (X → ℝ))
    (hH_nonempty : H.Nonempty)
    (hH_directed :
      ∀ h₁ ∈ H, ∀ h₂ ∈ H,
        ∃ h₃ ∈ H, ∀ x ∈ V.carrier, h₁ x ≤ h₃ x ∧ h₂ x ≤ h₃ x)
    (hH_le_P : ∀ h ∈ H, ∀ x ∈ V.carrier, h x ≤ P x)
    (hH_cofinal :
      ∀ x ∈ V.carrier, ∀ ε : ℝ, 0 < ε →
        ∃ h ∈ H, P x - ε < h x)
    {x : X} (hxV : x ∈ V.carrier) :
    sSup {a : ℝ | ∃ h ∈ H, a = h x} = P x := by
  have hvalue_nonempty : {a : ℝ | ∃ h ∈ H, a = h x}.Nonempty := by
    rcases hH_nonempty with ⟨h, hh⟩
    exact ⟨h x, h, hh, rfl⟩
  have hvalue_directed :
      DirectedOn (· ≤ ·) {a : ℝ | ∃ h ∈ H, a = h x} :=
    directed_harmonic_minorants_valueSet_directedOn V H hH_directed hxV
  exact hvalue_directed.csSup_eq_of_forall_le_of_forall_lt_exists_gt
    hvalue_nonempty
    (by
      intro a ha
      rcases ha with ⟨h, hh, rfl⟩
      exact hH_le_P h hh x hxV)
    (by
      intro w hw
      have hε : 0 < P x - w := sub_pos.mpr hw
      rcases hH_cofinal x hxV (P x - w) hε with ⟨h, hh, hlt⟩
      refine ⟨h x, ?_, ?_⟩
      · exact ⟨h, hh, rfl⟩
      · linarith)

/--
%%handwave
name:
  Finite directed domination in a harmonic minorant family
statement:
  Every finite subfamily of a nonempty directed family of harmonic minorants is
  dominated on the region by a single member of the family.
proof:
  Induct on the finite subfamily.  The empty family is dominated by any
  member.  For the induction step, use directedness to find a family member
  dominating both the new function and the previously constructed upper
  bound.
-/
theorem directed_harmonic_minorants_finset_upper_bound
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (V : PerronDomain X) (H : Set (X → ℝ))
    (hH_nonempty : H.Nonempty)
    (hH_directed :
      ∀ h₁ ∈ H, ∀ h₂ ∈ H,
        ∃ h₃ ∈ H, ∀ x ∈ V.carrier, h₁ x ≤ h₃ x ∧ h₂ x ≤ h₃ x)
    (F : Finset (X → ℝ)) (hF : ∀ h, h ∈ F → h ∈ H) :
    ∃ h ∈ H, ∀ g ∈ F, ∀ x ∈ V.carrier, g x ≤ h x := by
  classical
  induction F using Finset.induction_on with
  | empty =>
      rcases hH_nonempty with ⟨h, hh⟩
      exact ⟨h, hh, by simp⟩
  | insert f F hf_not_mem ih =>
      have hfH : f ∈ H := hF f (Finset.mem_insert_self f F)
      have hFH : ∀ h, h ∈ F → h ∈ H := by
        intro h hh
        exact hF h (Finset.mem_insert_of_mem hh)
      rcases ih hFH with ⟨hOld, hhOld, hOld_dom⟩
      rcases hH_directed f hfH hOld hhOld with ⟨hTop, hhTop, hTop_dom⟩
      refine ⟨hTop, hhTop, ?_⟩
      intro g hg x hxV
      rw [Finset.mem_insert] at hg
      rcases hg with rfl | hgF
      · exact (hTop_dom x hxV).1
      · exact (hOld_dom g hgF x hxV).trans ((hTop_dom x hxV).2)

/--
%%handwave
name:
  Directed harmonic minorants approximate on finite sets
statement:
  If a directed harmonic minorant family approximates \(P\) from below at each
  point, then for every finite set of points and every positive epsilon there
  is one family member that is within epsilon of \(P\) at all those points.
proof:
  Choose a separate approximating minorant at each point of the finite set.
  Then use
  [finite directed domination](lean:JJMath.Uniformization.directed_harmonic_minorants_finset_upper_bound)
  to dominate all of these choices by one member of the family.
-/
theorem directed_harmonic_minorants_approximate_on_finset
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (V : PerronDomain X) (P : X → ℝ) (H : Set (X → ℝ))
    (hH_nonempty : H.Nonempty)
    (hH_directed :
      ∀ h₁ ∈ H, ∀ h₂ ∈ H,
        ∃ h₃ ∈ H, ∀ x ∈ V.carrier, h₁ x ≤ h₃ x ∧ h₂ x ≤ h₃ x)
    (hH_cofinal :
      ∀ x ∈ V.carrier, ∀ ε : ℝ, 0 < ε →
        ∃ h ∈ H, P x - ε < h x)
    (F : Finset X) (hF : ∀ x, x ∈ F → x ∈ V.carrier)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ h ∈ H, ∀ x ∈ F, P x - ε < h x := by
  classical
  have hchoose :
      ∀ y : {x // x ∈ F}, ∃ h ∈ H, P y.1 - ε < h y.1 := by
    intro y
    exact hH_cofinal y.1 (hF y.1 y.2) ε hε
  choose h hhH hhApprox using hchoose
  let G : Finset (X → ℝ) := F.attach.image (fun y : {x // x ∈ F} ↦ h y)
  have hG : ∀ g, g ∈ G → g ∈ H := by
    intro g hg
    rcases Finset.mem_image.mp hg with ⟨y, _hy, rfl⟩
    exact hhH y
  rcases directed_harmonic_minorants_finset_upper_bound V H hH_nonempty
      hH_directed G hG with
    ⟨hTop, hhTop, hTop_dom⟩
  refine ⟨hTop, hhTop, ?_⟩
  intro x hxF
  let y : {x // x ∈ F} := ⟨x, hxF⟩
  have hyG : h y ∈ G := by
    exact Finset.mem_image.mpr ⟨y, by simp, rfl⟩
  exact (hhApprox y).trans_le (hTop_dom (h y) hyG x (hF x hxF))

/--
%%handwave
name:
  Harmonic minorant family as a directed index type
statement:
  The members of a harmonic minorant family can be used as an index type,
  ordered by pointwise domination on the coordinate region.
-/
structure HarmonicMinorantIndex
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (V : PerronDomain X) (H : Set (X → ℝ)) where
  /-- The indexed harmonic minorant. -/
  toFun : X → ℝ
  /-- The indexed function belongs to the family. -/
  mem : toFun ∈ H

namespace HarmonicMinorantIndex

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
variable {V : PerronDomain X} {H : Set (X → ℝ)}

instance : CoeFun (HarmonicMinorantIndex V H) (fun _ ↦ X → ℝ) where
  coe i := i.toFun

instance : Preorder (HarmonicMinorantIndex V H) where
  le i j := ∀ x ∈ V.carrier, i x ≤ j x
  lt i j := (∀ x ∈ V.carrier, i x ≤ j x) ∧
    ¬ ∀ x ∈ V.carrier, j x ≤ i x
  le_refl i := by
    intro x _hx
    rfl
  le_trans i j k hij hjk := by
    intro x hx
    exact (hij x hx).trans (hjk x hx)
  lt_iff_le_not_ge i j := Iff.rfl

/--
%%handwave
name:
  A nonempty minorant family gives a nonempty index type
statement:
  If the harmonic minorant family is nonempty, then the corresponding index
  type is nonempty.
proof:
  Choose a function in the minorant family and pair it with its membership
  proof.
-/
theorem nonempty (hH_nonempty : H.Nonempty) :
    Nonempty (HarmonicMinorantIndex V H) := by
  rcases hH_nonempty with ⟨h, hh⟩
  exact ⟨⟨h, hh⟩⟩

/--
%%handwave
name:
  Directed minorants give a directed index order
statement:
  If the harmonic minorant family is directed by pointwise domination on the
  coordinate region, then the corresponding index order is directed.
proof:
  Given two indexed minorants, choose a third family member dominating both.
  With its membership proof, it is a common upper bound in the pointwise
  order.
-/
theorem isDirectedOrder
    (hH_directed :
      ∀ h₁ ∈ H, ∀ h₂ ∈ H,
        ∃ h₃ ∈ H, ∀ x ∈ V.carrier, h₁ x ≤ h₃ x ∧ h₂ x ≤ h₃ x) :
    IsDirectedOrder (HarmonicMinorantIndex V H) := by
  refine ⟨?_⟩
  intro i j
  rcases hH_directed i.toFun i.mem j.toFun j.mem with ⟨h, hh, hle⟩
  refine ⟨⟨h, hh⟩, ?_, ?_⟩
  · intro x hx
    exact (hle x hx).1
  · intro x hx
    exact (hle x hx).2

end HarmonicMinorantIndex

/--
%%handwave
name:
  Harmonic minorant nets converge pointwise to the supremum
statement:
  Ordered by pointwise domination, a locally bounded family whose pointwise
  supremum is \(P\) converges pointwise to \(P\) at every point of the
  coordinate region.
proof:
  At a fixed point, the range of the evaluation map is exactly the value set
  of the family.  Local boundedness on the singleton makes this value set
  bounded above, and the assumed supremum identity identifies its least upper
  bound with \(P(x)\).  Monotone convergence for directed nets gives the
  pointwise limit.
-/
theorem harmonicMinorantIndex_tendsto_atTop_pointwise_sSup
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (V : PerronDomain X) (P : X → ℝ) (H : Set (X → ℝ))
    (hH_nonempty : H.Nonempty)
    (hH_locally_bounded :
      ∀ K : Set X, IsCompact K → K ⊆ V.carrier →
        ∃ M : ℝ, ∀ h ∈ H, ∀ x ∈ K, h x ≤ M)
    (hH_pointwise_sSup :
      ∀ x ∈ V.carrier, sSup {a : ℝ | ∃ h ∈ H, a = h x} = P x)
    {x : X} (hxV : x ∈ V.carrier) :
    Filter.Tendsto
      (fun i : HarmonicMinorantIndex V H ↦ i x)
      Filter.atTop
      (𝓝 (P x)) := by
  let I := HarmonicMinorantIndex V H
  haveI : Nonempty I := HarmonicMinorantIndex.nonempty hH_nonempty
  have hmono : Monotone (fun i : I ↦ i x) := by
    intro i j hij
    exact hij x hxV
  have hvalue_nonempty : {a : ℝ | ∃ h ∈ H, a = h x}.Nonempty := by
    rcases hH_nonempty with ⟨h, hh⟩
    exact ⟨h x, h, hh, rfl⟩
  have hsingleton_subset : ({x} : Set X) ⊆ V.carrier := by
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    simpa [hy] using hxV
  rcases hH_locally_bounded ({x} : Set X) isCompact_singleton
      hsingleton_subset with
    ⟨M, hM⟩
  have hvalue_bdd : BddAbove {a : ℝ | ∃ h ∈ H, a = h x} := by
    refine ⟨M, ?_⟩
    intro a ha
    rcases ha with ⟨h, hh, rfl⟩
    exact hM h hh x (by simp)
  have hvalue_lub :
      IsLUB {a : ℝ | ∃ h ∈ H, a = h x} (P x) := by
    have hsSup_lub :
        IsLUB {a : ℝ | ∃ h ∈ H, a = h x}
          (sSup {a : ℝ | ∃ h ∈ H, a = h x}) :=
      isLUB_csSup hvalue_nonempty hvalue_bdd
    simpa [hH_pointwise_sSup x hxV] using hsSup_lub
  have hrange :
      Set.range (fun i : I ↦ i x) =
        {a : ℝ | ∃ h ∈ H, a = h x} := by
    ext a
    constructor
    · intro ha
      rcases ha with ⟨i, rfl⟩
      exact ⟨i.toFun, i.mem, rfl⟩
    · intro ha
      rcases ha with ⟨h, hh, rfl⟩
      exact ⟨⟨h, hh⟩, rfl⟩
  have hrange_lub :
      IsLUB (Set.range (fun i : I ↦ i x)) (P x) := by
    rw [hrange]
    exact hvalue_lub
  exact tendsto_atTop_isLUB hmono hrange_lub

/--
%%handwave
name:
  Real parts of holomorphic functions are harmonic
statement:
  If a real-valued function on an open subset of the complex plane is the real
  part of a holomorphic function there, then it is harmonic there.
proof:
  At each point, the holomorphic function is analytic.  The real part of an
  analytic function is harmonic, and equality on the open set gives equality
  in a neighborhood of the point.
-/
theorem harmonicOnNhd_of_exists_analyticOnNhd_re_eq
    {U : Set ℂ} {f : ℂ → ℝ}
    (hU_open : IsOpen U)
    (h : ∃ G : ℂ → ℂ,
      AnalyticOnNhd ℂ G U ∧ U.EqOn (fun z : ℂ ↦ (G z).re) f) :
    InnerProductSpace.HarmonicOnNhd f U := by
  rcases h with ⟨G, hG, hGre⟩
  intro z hz
  have hGz : AnalyticAt ℂ G z := hG z hz
  have hre_harmonic :
      InnerProductSpace.HarmonicAt (fun w : ℂ ↦ (G w).re) z :=
    hGz.harmonicAt_re
  have heq : (fun w : ℂ ↦ (G w).re) =ᶠ[𝓝 z] f := by
    filter_upwards [hU_open.mem_nhds hz] with w hw
    exact hGre hw
  exact (InnerProductSpace.harmonicAt_congr_nhds heq).1 hre_harmonic

/--
%%handwave
name:
  Interior disks fit inside an open disk
statement:
  Every point of an open disk has a positive-radius closed disk around it that
  is still contained in the original disk.
proof:
  If \(z\in B(c,R)\), take
  \(r=(R-d(z,c))/2>0\).  The triangle inequality shows that every point of
  \(\overline B(z,r)\) remains at distance less than \(R\) from \(c\).
-/
theorem exists_pos_radius_closedBall_subset_ball
    {c z : ℂ} {R : ℝ} (hz : z ∈ Metric.ball c R) :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall z r ⊆ Metric.ball c R := by
  let r : ℝ := (R - dist z c) / 2
  have hdist : dist z c < R := by
    simpa [Metric.mem_ball] using hz
  have hr : 0 < r := by
    dsimp [r]
    linarith
  have hsum : r + dist z c < R := by
    dsimp [r]
    linarith
  exact ⟨r, hr, Metric.closedBall_subset_ball' hsum⟩

/--
%%handwave
name:
  Harmonic limits have the Poisson representation
statement:
  If harmonic functions on a disk converge locally uniformly, then on every
  closed subdisk contained in the disk the limit is equal in the interior to
  the Poisson extension of its own boundary values.
proof:
  The harmonic functions satisfy the Poisson formula on the closed subdisk.
  Local uniform convergence on the ambient disk gives uniform convergence on
  the boundary circle of the subdisk.  Since [Poisson extensions of uniformly close boundary functions are uniformly close](lean:JJMath.Uniformization.abs_poissonDiskExtension_sub_poissonDiskExtension_le_of_boundaryData),
  the Poisson extensions converge to the Poisson extension of the limiting
  boundary values.  The pointwise limit is unique, so the Poisson formula
  passes to the limit.
-/
theorem locallyUniformLimit_harmonicOnNhd_eq_poissonDiskExtension_of_closedBall_subset
    {ι : Type} {l : Filter ι} [l.NeBot]
    {c d : ℂ} {R r : ℝ} (hr : 0 < r)
    {F : ι → ℂ → ℝ} {f : ℂ → ℝ}
    (hclosed : Metric.closedBall d r ⊆ Metric.ball c R)
    (hF : ∀ᶠ i in l,
      InnerProductSpace.HarmonicOnNhd (F i) (Metric.ball c R))
    (hconv : TendstoLocallyUniformlyOn F f l (Metric.ball c R)) :
    (Metric.ball d r).EqOn f (poissonDiskExtension d r f) := by
  have hfrontier_subset : frontier (Metric.ball d r) ⊆ Metric.ball c R := by
    intro y hy
    apply hclosed
    have hy_sphere : y ∈ Metric.sphere d r := by
      simpa [frontier_ball d hr.ne'] using hy
    have hdist : dist y d = r := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hy_sphere
    rw [Metric.mem_closedBall]
    exact le_of_eq hdist
  have hfrontier_compact : IsCompact (frontier (Metric.ball d r)) := by
    rw [frontier_ball d hr.ne']
    exact isCompact_sphere d r
  have hconv_frontier :
      TendstoUniformlyOn F f l (frontier (Metric.ball d r)) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact Metric.isOpen_ball).mp
      hconv (frontier (Metric.ball d r)) hfrontier_subset hfrontier_compact
  have hF_cont_frontier :
      ∀ᶠ i in l, ContinuousOn (F i) (frontier (Metric.ball d r)) := by
    filter_upwards [hF] with i hi
    exact (hi.mono hfrontier_subset).continuousOn
  have hf_boundary : ContinuousOn f (frontier (Metric.ball d r)) :=
    hconv_frontier.continuousOn hF_cont_frontier.frequently
  intro w hw
  have hw_closed : w ∈ Metric.closedBall d r := Metric.ball_subset_closedBall hw
  have hw_big : w ∈ Metric.ball c R := hclosed hw_closed
  have hFw_tendsto : Filter.Tendsto (fun i : ι ↦ F i w) l (𝓝 (f w)) :=
    hconv.tendsto_at hw_big
  have hP_tendsto :
      Filter.Tendsto (fun i : ι ↦ poissonDiskExtension d r (F i) w) l
        (𝓝 (poissonDiskExtension d r f w)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hε2 : 0 < ε / 2 := by positivity
    have hconvε :
        ∀ᶠ i in l,
          ∀ z ∈ frontier (Metric.ball d r), dist (f z) (F i z) < ε / 2 :=
      (Metric.tendstoUniformlyOn_iff.mp hconv_frontier) (ε / 2) hε2
    filter_upwards [hconvε, hF] with i hi_uniform hi_harmonic
    have hFi_boundary : ContinuousOn (F i) (frontier (Metric.ball d r)) :=
      (hi_harmonic.mono hfrontier_subset).continuousOn
    have hclose :
        ∀ z ∈ frontier (Metric.ball d r), |F i z - f z| ≤ ε / 2 := by
      intro z hz
      have hdist : |F i z - f z| < ε / 2 := by
        simpa [Real.dist_eq, abs_sub_comm] using hi_uniform z hz
      exact le_of_lt hdist
    have hbound :
        |poissonDiskExtension d r (F i) w -
          poissonDiskExtension d r f w| ≤ ε / 2 :=
      abs_poissonDiskExtension_sub_poissonDiskExtension_le_of_boundaryData
        d hr hw (F i) f hFi_boundary hf_boundary hclose
    have hdist :
        dist (poissonDiskExtension d r (F i) w)
          (poissonDiskExtension d r f w) ≤ ε / 2 := by
      simpa [Real.dist_eq] using hbound
    exact lt_of_le_of_lt hdist (by linarith)
  have hP_eq_event :
      (fun i : ι ↦ poissonDiskExtension d r (F i) w) =ᶠ[l]
        (fun i : ι ↦ F i w) := by
    filter_upwards [hF] with i hi
    have hi_closed :
        InnerProductSpace.HarmonicOnNhd (F i) (Metric.closedBall d r) :=
      hi.mono hclosed
    simpa [poissonDiskExtension, Pi.mul_apply] using
      (InnerProductSpace.HarmonicOnNhd.circleAverage_poissonKernel_smul
        (f := F i) (c := d) (R := r) hi_closed hw)
  have hFw_tendsto_poisson :
      Filter.Tendsto (fun i : ι ↦ F i w) l
        (𝓝 (poissonDiskExtension d r f w)) :=
    hP_tendsto.congr' hP_eq_event
  exact tendsto_nhds_unique hFw_tendsto hFw_tendsto_poisson

/--
%%handwave
name:
  Poisson limits are harmonic
statement:
  On a disk, a locally uniform limit of harmonic functions is harmonic.
proof:
  Around each point, choose a closed subdisk contained in the original disk.
  By [the limit has the Poisson representation on that subdisk](lean:JJMath.Uniformization.locallyUniformLimit_harmonicOnNhd_eq_poissonDiskExtension_of_closedBall_subset),
  it agrees locally with a Poisson extension.  Since Poisson extensions of
  continuous boundary data are harmonic, the limit is harmonic at the point.
-/
theorem harmonicOnNhd_of_tendstoLocallyUniformlyOn_ball_by_poisson
    {ι : Type} {l : Filter ι} [l.NeBot]
    {c : ℂ} {R : ℝ} (_hR : 0 < R)
    {F : ι → ℂ → ℝ} {f : ℂ → ℝ}
    (hF : ∀ᶠ i in l,
      InnerProductSpace.HarmonicOnNhd (F i) (Metric.ball c R))
    (hconv : TendstoLocallyUniformlyOn F f l (Metric.ball c R)) :
    InnerProductSpace.HarmonicOnNhd f (Metric.ball c R) := by
  have hF_cont :
      ∀ᶠ i in l, ContinuousOn (F i) (Metric.ball c R) := by
    filter_upwards [hF] with i hi
    exact hi.continuousOn
  have hf_cont : ContinuousOn f (Metric.ball c R) :=
    hconv.continuousOn hF_cont.frequently
  intro z hz
  rcases exists_pos_radius_closedBall_subset_ball hz with ⟨r, hr, hclosed⟩
  have hfrontier_subset :
      frontier (Metric.ball z r) ⊆ Metric.ball c R := by
    intro y hy
    apply hclosed
    have hy_sphere : y ∈ Metric.sphere z r := by
      simpa [frontier_ball z hr.ne'] using hy
    have hdist : dist y z = r := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hy_sphere
    rw [Metric.mem_closedBall]
    exact le_of_eq hdist
  have hf_boundary : ContinuousOn f (frontier (Metric.ball z r)) :=
    hf_cont.mono hfrontier_subset
  have hpoisson :
      InnerProductSpace.HarmonicOnNhd
        (poissonDiskExtension z r f) (Metric.ball z r) :=
    poissonDiskExtension_harmonicOn z hr f hf_boundary
  have hrep :
      (Metric.ball z r).EqOn f (poissonDiskExtension z r f) :=
    locallyUniformLimit_harmonicOnNhd_eq_poissonDiskExtension_of_closedBall_subset
      hr hclosed hF hconv
  have heq :
      poissonDiskExtension z r f =ᶠ[𝓝 z] f := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr)] with y hy
    exact (hrep hy).symm
  exact (InnerProductSpace.harmonicAt_congr_nhds heq).1
    (hpoisson z (Metric.mem_ball_self hr))

/--
%%handwave
name:
  Harmonic limits have holomorphic representatives
statement:
  On a disk, if harmonic functions converge locally uniformly, then the limit
  is the real part of a holomorphic function on that disk.
proof:
  First prove harmonicity of the limit using the Poisson representation and
  dominated convergence.  Then apply Mathlib's theorem that every harmonic
  function on a disk is locally the real part of a holomorphic function.
-/
theorem harmonic_conjugates_normalized_tendstoLocallyUniformlyOn
    {ι : Type} {l : Filter ι} [l.NeBot]
    {c : ℂ} {R : ℝ} (hR : 0 < R)
    {F : ι → ℂ → ℝ} {f : ℂ → ℝ}
    (hF : ∀ᶠ i in l,
      InnerProductSpace.HarmonicOnNhd (F i) (Metric.ball c R))
    (hconv : TendstoLocallyUniformlyOn F f l (Metric.ball c R)) :
    ∃ G : ℂ → ℂ,
      AnalyticOnNhd ℂ G (Metric.ball c R) ∧
        (Metric.ball c R).EqOn (fun z : ℂ ↦ (G z).re) f := by
  exact (harmonicOnNhd_of_tendstoLocallyUniformlyOn_ball_by_poisson
    hR hF hconv).exists_analyticOnNhd_ball_re_eq

/--
%%handwave
name:
  Disk harmonic functions are closed under locally uniform limits
statement:
  On a disk, a locally uniform limit of harmonic functions is harmonic.
proof:
  Use the compactness of normalized harmonic conjugates to represent the limit
  as the real part of a holomorphic function on the disk.  The real part of a
  holomorphic function is harmonic.
-/
theorem harmonicOnNhd_of_tendstoLocallyUniformlyOn_ball
    {ι : Type} {l : Filter ι} [l.NeBot]
    {c : ℂ} {R : ℝ} (hR : 0 < R)
    {F : ι → ℂ → ℝ} {f : ℂ → ℝ}
    (hF : ∀ᶠ i in l,
      InnerProductSpace.HarmonicOnNhd (F i) (Metric.ball c R))
    (hconv : TendstoLocallyUniformlyOn F f l (Metric.ball c R)) :
    InnerProductSpace.HarmonicOnNhd f (Metric.ball c R) := by
  exact harmonicOnNhd_of_tendstoLocallyUniformlyOn_ball_by_poisson hR hF hconv

/--
%%handwave
name:
  Plane harmonic functions are closed under locally uniform limits
statement:
  On an open subset of the complex plane, a locally uniform limit of harmonic
  functions is harmonic.
proof:
  Around each point of the open set, choose a disk contained in the open set.
  Restrict the locally uniform convergence and the eventual harmonicity to
  that disk, then apply that [the limit is harmonic on the disk when harmonic functions converge locally uniformly](lean:JJMath.Uniformization.harmonicOnNhd_of_tendstoLocallyUniformlyOn_ball).
-/
theorem harmonicOnNhd_of_tendstoLocallyUniformlyOn
    {ι : Type} {l : Filter ι} [l.NeBot]
    {U : Set ℂ} {F : ι → ℂ → ℝ} {f : ℂ → ℝ}
    (hU_open : IsOpen U)
    (hF : ∀ᶠ i in l, InnerProductSpace.HarmonicOnNhd (F i) U)
    (hconv : TendstoLocallyUniformlyOn F f l U) :
    InnerProductSpace.HarmonicOnNhd f U := by
  intro z hz
  rcases Metric.mem_nhds_iff.mp (hU_open.mem_nhds hz) with ⟨R, hR, hballU⟩
  have hF_ball :
      ∀ᶠ i in l,
        InnerProductSpace.HarmonicOnNhd (F i) (Metric.ball z R) := by
    filter_upwards [hF] with i hi
    exact hi.mono hballU
  have hconv_ball :
      TendstoLocallyUniformlyOn F f l (Metric.ball z R) :=
    hconv.mono hballU
  exact harmonicOnNhd_of_tendstoLocallyUniformlyOn_ball hR hF_ball hconv_ball z
    (Metric.mem_ball_self hR)

/--
%%handwave
name:
  Surface harmonic functions are closed under locally uniform limits
statement:
  On an open surface region, a locally uniform limit of surface-harmonic
  functions is surface-harmonic.
proof:
  Check harmonicity in a complex chart.  Locally uniform convergence on the
  surface composes with the inverse chart to give locally uniform convergence
  on the chart image.  The coordinate functions are harmonic eventually, so
  [plane harmonic functions are closed under locally uniform limits](lean:JJMath.Uniformization.harmonicOnNhd_of_tendstoLocallyUniformlyOn).
-/
theorem harmonicOnSurface_of_tendstoLocallyUniformlyOn
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {ι : Type} {l : Filter ι} [l.NeBot]
    {U : Set X} {F : ι → X → ℝ} {f : X → ℝ}
    (_hU_open : IsOpen U)
    (hF : ∀ᶠ i in l, IsHarmonicOnSurface U (F i))
    (hconv : TendstoLocallyUniformlyOn F f l U) :
    IsHarmonicOnSurface U f := by
  intro e he
  have hcoord_event :
      ∀ᶠ i in l,
        InnerProductSpace.HarmonicOnNhd
          (fun z : ℂ ↦ F i (e.symm z))
          (e.target ∩ e.symm ⁻¹' U) := by
    filter_upwards [hF] with i hi
    exact hi e he
  have hmaps :
      Set.MapsTo e.symm (e.target ∩ e.symm ⁻¹' U) U := by
    intro z hz
    exact hz.2
  have hcont :
      ContinuousOn e.symm (e.target ∩ e.symm ⁻¹' U) :=
    e.continuousOn_symm.mono (by
      intro z hz
      exact hz.1)
  have hcoord_conv :
      TendstoLocallyUniformlyOn
        (fun i : ι ↦ fun z : ℂ ↦ F i (e.symm z))
        (fun z : ℂ ↦ f (e.symm z)) l
        (e.target ∩ e.symm ⁻¹' U) :=
    hconv.comp e.symm hmaps hcont
  have hopen : IsOpen (e.target ∩ e.symm ⁻¹' U) := by
    exact e.isOpen_inter_preimage_symm _hU_open
  exact harmonicOnNhd_of_tendstoLocallyUniformlyOn hopen hcoord_event hcoord_conv

/--
%%handwave
name:
  Surface harmonic functions are closed under compact-local uniform limits
statement:
  On an open surface region, if harmonic functions converge uniformly on
  every compact subset of the region, then their limit is harmonic.
proof:
  Uniform convergence on every compact subset is equivalent, on open subsets
  of locally compact spaces, to locally uniform convergence.  Apply the
  theorem that locally uniform limits of surface-harmonic functions are
  surface-harmonic.
-/
theorem harmonicOnSurface_of_forall_compact_tendstoUniformlyOn
    {X : Type} [TopologicalSpace X] [LocallyCompactSpace X] [ChartedSpace ℂ X]
    {ι : Type} {l : Filter ι} [l.NeBot]
    {U : Set X} {F : ι → X → ℝ} {f : X → ℝ}
    (hU_open : IsOpen U)
    (hF : ∀ᶠ i in l, IsHarmonicOnSurface U (F i))
    (hconv :
      ∀ K : Set X, K ⊆ U → IsCompact K →
        TendstoUniformlyOn F f l K) :
    IsHarmonicOnSurface U f := by
  have hconv_local : TendstoLocallyUniformlyOn F f l U :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hU_open).mpr hconv
  exact harmonicOnSurface_of_tendstoLocallyUniformlyOn hU_open hF hconv_local

/--
%%handwave
name:
  Locally eventually harmonic compact-local limits are harmonic
statement:
  Let \(F_i\) converge uniformly on every compact subset of an open surface
  region \(U\).  If around every point of \(U\) the functions \(F_i\) are
  eventually harmonic on some smaller open neighborhood, then the limit is
  harmonic on \(U\).
proof:
  Around each point choose such a neighborhood \(V\).  The compact-local
  convergence on \(U\) restricts to locally uniform convergence on \(V\), and
  the locally uniform harmonic-limit theorem gives harmonicity on \(V\).
  Since surface harmonicity is local, these neighborhoods patch to \(U\).
-/
theorem harmonicOnSurface_of_local_eventually_harmonic_forall_compact_tendstoUniformlyOn
    {X : Type} [TopologicalSpace X] [LocallyCompactSpace X] [ChartedSpace ℂ X]
    {ι : Type} {l : Filter ι} [l.NeBot]
    {U : Set X} {F : ι → X → ℝ} {f : X → ℝ}
    (hlocal_harm :
      ∀ x ∈ U,
        ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
          ∀ᶠ i in l, IsHarmonicOnSurface V (F i))
    (hconv :
      ∀ K : Set X, K ⊆ U → IsCompact K →
        TendstoUniformlyOn F f l K) :
    IsHarmonicOnSurface U f := by
  refine harmonicOnSurface_of_locally_harmonic ?_
  intro x hxU
  rcases hlocal_harm x hxU with ⟨V, hV_open, hxV, hVU, hV_harm⟩
  have hconvV : TendstoLocallyUniformlyOn F f l V :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hV_open).mpr
      (fun K hKV hK ↦ hconv K (hKV.trans hVU) hK)
  exact ⟨V, hxV, hVU,
    harmonicOnSurface_of_tendstoLocallyUniformlyOn hV_open hV_harm hconvV⟩

/--
%%handwave
name:
  Uniform pointwise upper bounds pass to the limit
statement:
  If functions converge uniformly on a set and, at a point of that set, their
  values are eventually at most \(a\), then the limiting value is at most
  \(a\).
proof:
  Uniform convergence on the set gives ordinary pointwise convergence at the
  chosen point.  Closedness of the order interval \((-\infty,a]\) passes the
  eventual inequality to the limit.
-/
theorem tendstoUniformlyOn_pointwise_le_of_eventually_le
    {ι X : Type} {l : Filter ι} [l.NeBot]
    {K : Set X} {F : ι → X → ℝ} {f : X → ℝ}
    {x : X} (hx : x ∈ K) {a : ℝ}
    (hconv : TendstoUniformlyOn F f l K)
    (hle : ∀ᶠ i in l, F i x ≤ a) :
    f x ≤ a := by
  exact le_of_tendsto (hconv.tendsto_at hx) hle

/--
%%handwave
name:
  Uniform pointwise lower bounds pass to the limit
statement:
  If functions converge uniformly on a set and, at a point of that set, their
  values are eventually at least \(a\), then the limiting value is at least
  \(a\).
proof:
  Apply the upper-bound version to the negated functions, or equivalently use
  closedness of the order interval \([a,\infty)\) under pointwise
  convergence.
-/
theorem tendstoUniformlyOn_pointwise_ge_of_eventually_ge
    {ι X : Type} {l : Filter ι} [l.NeBot]
    {K : Set X} {F : ι → X → ℝ} {f : X → ℝ}
    {x : X} (hx : x ∈ K) {a : ℝ}
    (hconv : TendstoUniformlyOn F f l K)
    (hge : ∀ᶠ i in l, a ≤ F i x) :
    a ≤ f x := by
  exact ge_of_tendsto (hconv.tendsto_at hx) hge

/--
%%handwave
name:
  Euclidean local Harnack estimate with exact ratio
statement:
  If a harmonic function is nonnegative on a closed disk, then its value at
  any interior point is bounded by the standard Poisson ratio times its value
  at the center.
proof:
  The Poisson formula represents the value at the interior point as a
  boundary average.  The Poisson kernel is bounded above on the boundary by
  \((r+\lVert w-c\rVert)/(r-\lVert w-c\rVert)\), and the mean-value property
  identifies the average of the harmonic function with its center value.
-/
theorem harmonicOnNhd_nonnegative_le_ratio_mul_center_of_mem_ball
    {c : ℂ} {r : ℝ} (hr : 0 < r)
    {u : ℂ → ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u (Metric.closedBall c r))
    (hu_nonneg : ∀ z ∈ Metric.closedBall c r, 0 ≤ u z)
    {w : ℂ} (hw : w ∈ Metric.ball c r) :
    u w ≤ ((r + ‖w - c‖) / (r - ‖w - c‖)) * u c := by
  have hfrontier_closed :
      frontier (Metric.ball c r) ⊆ Metric.closedBall c r := by
    intro z hz
    have hz_sphere : z ∈ Metric.sphere c r := by
      simpa [frontier_ball c hr.ne'] using hz
    exact Metric.sphere_subset_closedBall hz_sphere
  have hu_frontier : ContinuousOn u (frontier (Metric.ball c r)) :=
    hu.continuousOn.mono hfrontier_closed
  have hu_sphere : ContinuousOn u (Metric.sphere c r) := by
    rw [← frontier_ball c hr.ne']
    exact hu_frontier
  have hkernel_int :
      CircleIntegrable (fun z : ℂ ↦ poissonKernel c w z * u z) c r :=
    poissonKernel_mul_boundaryData_circleIntegrable c hr hw u hu_frontier
  have hu_int : CircleIntegrable u c r :=
    ContinuousOn.circleIntegrable hr.le hu_sphere
  let C : ℝ := (r + ‖w - c‖) / (r - ‖w - c‖)
  have hC_int : CircleIntegrable (fun z : ℂ ↦ C * u z) c r := by
    simpa [Pi.smul_apply, smul_eq_mul, C] using
      (hu_int.const_smul (a := C))
  have hpoint :
      ∀ z ∈ Metric.sphere c |r|,
        poissonKernel c w z * u z ≤ C * u z := by
    intro z hz
    have hz_sphere : z ∈ Metric.sphere c r := by
      simpa [abs_of_pos hr] using hz
    have hz_closed : z ∈ Metric.closedBall c r :=
      Metric.sphere_subset_closedBall hz_sphere
    have hP_le_C :
        poissonKernel c w z ≤ C := by
      simpa [C] using
        poissonKernel_le_disk_bound_of_mem_sphere_of_mem_ball c hz_sphere hw
    exact mul_le_mul_of_nonneg_right hP_le_C (hu_nonneg z hz_closed)
  calc
    u w
        = Real.circleAverage (fun z : ℂ ↦ poissonKernel c w z * u z) c r := by
            simpa [Pi.smul_apply, smul_eq_mul] using
              (InnerProductSpace.HarmonicOnNhd.circleAverage_poissonKernel_smul
                (f := u) (c := c) (R := r) hu hw).symm
    _ ≤ Real.circleAverage (fun z : ℂ ↦ C * u z) c r :=
        Real.circleAverage_mono hkernel_int hC_int hpoint
    _ = C * Real.circleAverage u c r := by
        simpa [Pi.smul_apply, smul_eq_mul] using
          (Real.circleAverage_fun_smul (a := C) (f := u) (c := c) (R := r))
    _ = C * u c := by
        have hmean :
            Real.circleAverage u c r = u c := by
          have hu_abs :
              InnerProductSpace.HarmonicOnNhd u (Metric.closedBall c |r|) := by
            simpa [abs_of_pos hr] using hu
          simpa [abs_of_pos hr] using
            (HarmonicOnNhd.circleAverage_eq
              (f := u) (c := c) (R := r) hu_abs)
        rw [hmean]

/--
%%handwave
name:
  Bounded harmonic functions are equicontinuous at the center of a disk
statement:
  A family of harmonic functions on a closed Euclidean disk is
  equicontinuous at the center if all functions are uniformly bounded in
  absolute value on that disk.
proof:
  Apply the exact-ratio Harnack estimate to the nonnegative harmonic
  functions \(M+u\) and \(M-u\).  The ratio tends to \(1\) as the point tends
  to the center, giving a common continuity modulus.
-/
theorem harmonicOnNhd_equicontinuousAt_center_of_abs_le_closedBall
    {ι : Type} {c : ℂ} {r M : ℝ} (hr : 0 < r)
    {F : ι → ℂ → ℝ}
    (hF_harm : ∀ i : ι, InnerProductSpace.HarmonicOnNhd (F i) (Metric.closedBall c r))
    (hF_abs : ∀ i : ι, ∀ z ∈ Metric.closedBall c r, |F i z| ≤ M) :
    EquicontinuousAt F c := by
  let ratio : ℂ → ℝ := fun w ↦ (r + ‖w - c‖) / (r - ‖w - c‖)
  let b : ℂ → ℝ := fun w ↦ (2 * M) * |ratio w - 1|
  have hnorm_tendsto :
      Filter.Tendsto (fun w : ℂ ↦ ‖w - c‖) (𝓝 c) (𝓝 0) := by
    have htmp :
        Filter.Tendsto (fun w : ℂ ↦ ‖w - c‖) (𝓝 c) (𝓝 ‖c - c‖) :=
      (continuousAt_id.sub continuousAt_const).norm
    simpa using htmp
  have hratio_tendsto :
      Filter.Tendsto ratio (𝓝 c) (𝓝 1) := by
    have hnum :
        Filter.Tendsto (fun w : ℂ ↦ r + ‖w - c‖) (𝓝 c) (𝓝 (r + 0)) :=
      tendsto_const_nhds.add hnorm_tendsto
    have hden :
        Filter.Tendsto (fun w : ℂ ↦ r - ‖w - c‖) (𝓝 c) (𝓝 (r - 0)) :=
      tendsto_const_nhds.sub hnorm_tendsto
    have hden_ne : r - 0 ≠ 0 := by linarith
    have hdiv := hnum.div hden hden_ne
    simpa [ratio, div_self hr.ne'] using hdiv
  have hb_lim : Filter.Tendsto b (𝓝 c) (𝓝 0) := by
    have hsub :
        Filter.Tendsto (fun w : ℂ ↦ ratio w - 1) (𝓝 c) (𝓝 0) := by
      simpa using hratio_tendsto.sub (tendsto_const_nhds (x := (1 : ℝ)))
    have habs :
        Filter.Tendsto (fun w : ℂ ↦ |ratio w - 1|) (𝓝 c) (𝓝 0) := by
      simpa [Real.norm_eq_abs] using hsub.norm
    simpa [b] using (tendsto_const_nhds.mul habs : Filter.Tendsto
      (fun w : ℂ ↦ (2 * M) * |ratio w - 1|) (𝓝 c) (𝓝 ((2 * M) * 0)))
  refine Metric.equicontinuousAt_of_continuity_modulus b hb_lim F ?_
  filter_upwards [Metric.ball_mem_nhds c hr] with w hw i
  have hc_closed : c ∈ Metric.closedBall c r := Metric.mem_closedBall_self hr.le
  have hw_closed : w ∈ Metric.closedBall c r :=
    Metric.ball_subset_closedBall hw
  have hw_norm_lt : ‖w - c‖ < r := by
    simpa [Metric.mem_ball, dist_eq_norm] using hw
  have hden_pos : 0 < r - ‖w - c‖ := by linarith
  let C : ℝ := ratio w
  have hC_eq : C = (r + ‖w - c‖) / (r - ‖w - c‖) := rfl
  have hC_ge_one : 1 ≤ C := by
    rw [hC_eq]
    rw [le_div_iff₀ hden_pos]
    nlinarith [norm_nonneg (w - c)]
  have hCminus_nonneg : 0 ≤ C - 1 := sub_nonneg.mpr hC_ge_one
  have huc_abs := hF_abs i c hc_closed
  have huc_le : F i c ≤ M := (abs_le.mp huc_abs).2
  have huc_ge : -M ≤ F i c := (abs_le.mp huc_abs).1
  have hplus_harm :
      InnerProductSpace.HarmonicOnNhd
        (fun z : ℂ ↦ M + F i z) (Metric.closedBall c r) := by
    simpa [Pi.add_apply] using
      ((InnerProductSpace.harmonicOnNhd_const (E := ℂ) (F := ℝ) M).add (hF_harm i))
  have hminus_harm :
      InnerProductSpace.HarmonicOnNhd
        (fun z : ℂ ↦ M - F i z) (Metric.closedBall c r) := by
    simpa [Pi.sub_apply] using
      ((InnerProductSpace.harmonicOnNhd_const (E := ℂ) (F := ℝ) M).sub (hF_harm i))
  have hplus_nonneg :
      ∀ z ∈ Metric.closedBall c r, 0 ≤ M + F i z := by
    intro z hz
    have hz_abs := hF_abs i z hz
    have hz_ge : -M ≤ F i z := (abs_le.mp hz_abs).1
    linarith
  have hminus_nonneg :
      ∀ z ∈ Metric.closedBall c r, 0 ≤ M - F i z := by
    intro z hz
    have hz_abs := hF_abs i z hz
    have hz_le : F i z ≤ M := (abs_le.mp hz_abs).2
    linarith
  have hplus :
      M + F i w ≤ C * (M + F i c) := by
    simpa [C, ratio] using
      harmonicOnNhd_nonnegative_le_ratio_mul_center_of_mem_ball
        (c := c) (r := r) hr hplus_harm hplus_nonneg hw
  have hminus :
      M - F i w ≤ C * (M - F i c) := by
    simpa [C, ratio] using
      harmonicOnNhd_nonnegative_le_ratio_mul_center_of_mem_ball
        (c := c) (r := r) hr hminus_harm hminus_nonneg hw
  have hupper :
      F i w - F i c ≤ 2 * M * (C - 1) := by
    calc
      F i w - F i c = (M + F i w) - (M + F i c) := by ring
      _ ≤ C * (M + F i c) - (M + F i c) :=
          sub_le_sub_right hplus (M + F i c)
      _ = (C - 1) * (M + F i c) := by ring
      _ ≤ (C - 1) * (2 * M) :=
          mul_le_mul_of_nonneg_left (by linarith) hCminus_nonneg
      _ = 2 * M * (C - 1) := by ring
  have hlower :
      F i c - F i w ≤ 2 * M * (C - 1) := by
    calc
      F i c - F i w = (M - F i w) - (M - F i c) := by ring
      _ ≤ C * (M - F i c) - (M - F i c) :=
          sub_le_sub_right hminus (M - F i c)
      _ = (C - 1) * (M - F i c) := by ring
      _ ≤ (C - 1) * (2 * M) :=
          mul_le_mul_of_nonneg_left (by linarith) hCminus_nonneg
      _ = 2 * M * (C - 1) := by ring
  have hdist :
      dist (F i c) (F i w) ≤ 2 * M * (C - 1) := by
    rw [Real.dist_eq, abs_sub_le_iff]
    exact ⟨hlower, hupper⟩
  simpa [b, C, ratio, abs_of_nonneg hCminus_nonneg] using hdist

/--
%%handwave
name:
  Locally bounded harmonic families are equicontinuous on compact pieces
statement:
  Let \(F_i\) be a family of harmonic functions on an open surface region
  \(U\).  If near every point of a set \(K\subset U\) the family is uniformly
  bounded in absolute value, then the family is equicontinuous on \(K\).
proof:
  Work in a coordinate chart around each point of \(K\), choose a closed
  Euclidean disk whose image stays inside a neighborhood with a common
  absolute bound, and apply the Euclidean bounded-harmonic equicontinuity
  theorem there.  Pull the resulting neighborhood estimate back through the
  chart.
-/
theorem harmonicOnSurface_equicontinuousOn_of_locally_abs_bound
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexOneManifold X]
    {ι : Type} {U K : Set X}
    {F : ι → X → ℝ}
    (hF_harm : ∀ i : ι, IsHarmonicOnSurface U (F i))
    (hlocal_bound :
      ∀ x ∈ K,
        ∃ N : Set X, N ∈ 𝓝 x ∧ N ⊆ U ∧
          ∃ M : ℝ, ∀ i : ι, ∀ y ∈ N, |F i y| ≤ M) :
    EquicontinuousOn F K := by
  intro x hxK
  rcases hlocal_bound x hxK with ⟨N, hN_nhds, hN_subset, M, hM⟩
  rcases mem_nhds_iff.mp hN_nhds with ⟨O, hON, hO_open, hxO⟩
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ x
  let z : ℂ := e x
  have hxsource : x ∈ e.source := mem_chart_source ℂ x
  have he : e ∈ atlas ℂ X := chart_mem_atlas ℂ x
  let S : Set ℂ := e.target ∩ e.symm ⁻¹' O
  have hS_open : IsOpen S := by
    simpa [S] using e.isOpen_inter_preimage_symm hO_open
  have hzS : z ∈ S := by
    refine ⟨e.map_source hxsource, ?_⟩
    simpa [z, e.left_inv hxsource] using hxO
  rcases Metric.mem_nhds_iff.mp (hS_open.mem_nhds hzS) with
    ⟨R, hR_pos, hR_subset⟩
  let r : ℝ := R / 2
  have hr : 0 < r := by positivity
  have hr_lt_R : r < R := by
    dsimp [r]
    linarith
  have hclosedS : Metric.closedBall z r ⊆ S :=
    (Metric.closedBall_subset_ball (x := z) hr_lt_R).trans hR_subset
  let G : ι → ℂ → ℝ := fun i w ↦ F i (e.symm w)
  have hG_harm :
      ∀ i : ι, InnerProductSpace.HarmonicOnNhd (G i) (Metric.closedBall z r) := by
    intro i
    have hcoord :
        InnerProductSpace.HarmonicOnNhd
          (fun w : ℂ ↦ F i (e.symm w)) (e.target ∩ e.symm ⁻¹' U) :=
      hF_harm i e he
    refine hcoord.mono ?_
    intro w hw
    have hwS : w ∈ S := hclosedS hw
    exact ⟨hwS.1, hN_subset (by
      have hOmem : e.symm w ∈ O := hwS.2
      exact hON hOmem)⟩
  have hG_abs :
      ∀ i : ι, ∀ w ∈ Metric.closedBall z r, |G i w| ≤ M := by
    intro i w hw
    have hwS : w ∈ S := hclosedS hw
    have hOw : e.symm w ∈ O := hwS.2
    exact hM i (e.symm w) (hON hOw)
  have hG_eqcont : EquicontinuousAt G z :=
    harmonicOnNhd_equicontinuousAt_center_of_abs_le_closedBall
      (c := z) (r := r) hr hG_harm hG_abs
  have hF_eqcont_at : EquicontinuousAt F x := by
    intro V hV
    have hG_event : ∀ᶠ w in 𝓝 z, ∀ i : ι, (G i z, G i w) ∈ V :=
      hG_eqcont V hV
    have hpre : ∀ᶠ y in 𝓝 x, ∀ i : ι, (F i x, F i y) ∈ V := by
      filter_upwards
        [e.open_source.mem_nhds hxsource,
         e.continuousAt hxsource hG_event] with y hysource hy i
      simpa [G, z, e.left_inv hxsource, e.left_inv hysource] using hy i
    exact hpre
  exact hF_eqcont_at.equicontinuousWithinAt K

/--
%%handwave
name:
  Eventual local bounds give an equicontinuous harmonic tail
statement:
  Let \(F_n\) be a sequence of harmonic functions on an open surface region
  \(U\), eventually so in \(n\).  If every point of a compact set \(K\) has a
  neighborhood in \(U\) on which the sequence is eventually uniformly bounded
  in absolute value, then some tail of the sequence is equicontinuous on
  \(K\).
proof:
  Choose local neighborhoods with eventual absolute bounds and pass to a
  finite subcover of \(K\).  After discarding finitely many terms, all bounds
  from the finite subcover and harmonicity on \(U\) hold simultaneously.
  The bounded-harmonic equicontinuity theorem then applies to that tail.
-/
theorem harmonicOnSurface_tail_equicontinuousOn_of_eventually_harmonic_locally_eventual_abs_bound
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexOneManifold X]
    {U K : Set X}
    {F : ℕ → X → ℝ}
    (hK_compact : IsCompact K)
    (hF_harm : ∀ᶠ n : ℕ in Filter.atTop, IsHarmonicOnSurface U (F n))
    (hlocal_bound :
      ∀ x ∈ K,
        ∃ N : Set X, N ∈ 𝓝 x ∧ N ⊆ U ∧
          ∃ M : ℝ,
            ∀ᶠ n : ℕ in Filter.atTop, ∀ y ∈ N, |F n y| ≤ M) :
    ∃ N₀ : ℕ,
      EquicontinuousOn (fun n : ℕ ↦ F (N₀ + n)) K := by
  classical
  choose N hN_nhds hN_subset M hM using hlocal_bound
  choose O hO_subset hO_open hxO using
    fun x hxK ↦ mem_nhds_iff.mp (hN_nhds x hxK)
  let V : X → Set X := fun x ↦ if hxK : x ∈ K then O x hxK else ∅
  have hV_open : ∀ x : X, IsOpen (V x) := by
    intro x
    by_cases hxK : x ∈ K
    · simpa [V, hxK] using hO_open x hxK
    · simp [V, hxK]
  have hcover : K ⊆ ⋃ x : X, V x := by
    intro x hxK
    exact Set.mem_iUnion.mpr ⟨x, by simpa [V, hxK] using hxO x hxK⟩
  rcases hK_compact.elim_finite_subcover V hV_open hcover with ⟨t, ht⟩
  have hfinite :
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ x ∈ t, ∀ hxK : x ∈ K,
          ∀ y ∈ O x hxK, |F n y| ≤ M x hxK := by
    rw [Finset.eventually_all]
    intro x hx_t
    by_cases hxK : x ∈ K
    · filter_upwards [hM x hxK] with n hn hxK' y hyO
      have hxK_eq : hxK' = hxK := Subsingleton.elim _ _
      cases hxK_eq
      exact hn y (hO_subset x hxK hyO)
    · exact Filter.Eventually.of_forall (fun n hxK' ↦ False.elim (hxK hxK'))
  rcases Filter.eventually_atTop.mp (hF_harm.and hfinite) with ⟨N₀, hN₀⟩
  refine ⟨N₀, ?_⟩
  refine harmonicOnSurface_equicontinuousOn_of_locally_abs_bound
    (U := U) (K := K) ?_ ?_
  · intro n
    exact (hN₀ (N₀ + n) (Nat.le_add_right N₀ n)).1
  · intro x hxK
    have hxUnion : x ∈ ⋃ z ∈ t, V z := ht hxK
    rcases Set.mem_iUnion.mp hxUnion with ⟨z, hzUnion⟩
    rcases Set.mem_iUnion.mp hzUnion with ⟨hz_t, hxVz⟩
    by_cases hzK : z ∈ K
    · have hxO : x ∈ O z hzK := by
        simpa [V, hzK] using hxVz
      refine ⟨O z hzK, (hO_open z hzK).mem_nhds hxO, ?_, M z hzK, ?_⟩
      · intro y hyO
        exact hN_subset z hzK (hO_subset z hzK hyO)
      · intro n y hyO
        exact (hN₀ (N₀ + n) (Nat.le_add_right N₀ n)).2
          z hz_t hzK y hyO
    · simp [V, hzK] at hxVz

/--
%%handwave
name:
  Euclidean local Harnack estimate
statement:
  If a harmonic function is nonnegative on a closed disk, then on the
  concentric disk of half the radius its values are bounded by three times its
  value at the center.
proof:
  The Poisson formula represents the value at an interior point as the
  boundary average against the Poisson kernel.  On the half-radius disk, the
  Poisson kernel is bounded above by \(3\).  Averaging and using the mean
  value theorem gives the result.
-/
theorem harmonicOnNhd_nonnegative_le_three_mul_center_of_mem_ball_half
    {c : ℂ} {r : ℝ} (hr : 0 < r)
    {u : ℂ → ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u (Metric.closedBall c r))
    (hu_nonneg : ∀ z ∈ Metric.closedBall c r, 0 ≤ u z)
    {w : ℂ} (hw : w ∈ Metric.ball c (r / 2)) :
    u w ≤ 3 * u c := by
  have hhalf_le : r / 2 ≤ r := by linarith
  have hw_big : w ∈ Metric.ball c r :=
    Metric.ball_subset_ball hhalf_le hw
  have hfrontier_closed :
      frontier (Metric.ball c r) ⊆ Metric.closedBall c r := by
    intro z hz
    have hz_sphere : z ∈ Metric.sphere c r := by
      simpa [frontier_ball c hr.ne'] using hz
    exact Metric.sphere_subset_closedBall hz_sphere
  have hu_frontier : ContinuousOn u (frontier (Metric.ball c r)) :=
    hu.continuousOn.mono hfrontier_closed
  have hu_sphere : ContinuousOn u (Metric.sphere c r) := by
    rw [← frontier_ball c hr.ne']
    exact hu_frontier
  have hkernel_int :
      CircleIntegrable (fun z : ℂ ↦ poissonKernel c w z * u z) c r :=
    poissonKernel_mul_boundaryData_circleIntegrable c hr hw_big u hu_frontier
  have hu_int : CircleIntegrable u c r :=
    ContinuousOn.circleIntegrable hr.le hu_sphere
  have hthree_int : CircleIntegrable (fun z : ℂ ↦ 3 * u z) c r := by
    simpa [Pi.smul_apply, smul_eq_mul] using
      (hu_int.const_smul (a := (3 : ℝ)))
  have hpoint :
      ∀ z ∈ Metric.sphere c |r|,
        poissonKernel c w z * u z ≤ 3 * u z := by
    intro z hz
    have hz_sphere : z ∈ Metric.sphere c r := by
      simpa [abs_of_pos hr] using hz
    have hz_closed : z ∈ Metric.closedBall c r :=
      Metric.sphere_subset_closedBall hz_sphere
    have hP_le_ratio :
        poissonKernel c w z ≤ (r + ‖w - c‖) / (r - ‖w - c‖) :=
      poissonKernel_le_disk_bound_of_mem_sphere_of_mem_ball c hz_sphere hw_big
    have hw_norm_lt : ‖w - c‖ < r / 2 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hw
    have hw_norm_le : ‖w - c‖ ≤ r / 2 := le_of_lt hw_norm_lt
    have hden_pos : 0 < r - ‖w - c‖ := by linarith
    have hratio_le_three : (r + ‖w - c‖) / (r - ‖w - c‖) ≤ 3 := by
      rw [div_le_iff₀ hden_pos]
      nlinarith
    have hP_le_three : poissonKernel c w z ≤ 3 :=
      hP_le_ratio.trans hratio_le_three
    exact mul_le_mul_of_nonneg_right hP_le_three (hu_nonneg z hz_closed)
  calc
    u w
        = Real.circleAverage (fun z : ℂ ↦ poissonKernel c w z * u z) c r := by
            simpa [Pi.smul_apply, smul_eq_mul] using
              (InnerProductSpace.HarmonicOnNhd.circleAverage_poissonKernel_smul
                (f := u) (c := c) (R := r) hu hw_big).symm
    _ ≤ Real.circleAverage (fun z : ℂ ↦ 3 * u z) c r :=
        Real.circleAverage_mono hkernel_int hthree_int hpoint
    _ = 3 * Real.circleAverage u c r := by
        simpa [Pi.smul_apply, smul_eq_mul] using
          (Real.circleAverage_fun_smul (a := (3 : ℝ)) (f := u) (c := c) (R := r))
    _ = 3 * u c := by
        have hmean :
            Real.circleAverage u c r = u c := by
          have hu_abs :
              InnerProductSpace.HarmonicOnNhd u (Metric.closedBall c |r|) := by
            simpa [abs_of_pos hr] using hu
          simpa [abs_of_pos hr] using
            (HarmonicOnNhd.circleAverage_eq
              (f := u) (c := c) (R := r) hu_abs)
        rw [hmean]

/--
%%handwave
name:
  Local Harnack control for nonnegative harmonic functions
statement:
  Near every point of a surface region, the values of any nonnegative
  harmonic function are bounded by a fixed constant times its value at that
  point.
proof:
  Choose a coordinate disk around the point with a smaller concentric disk
  still inside the region.  In the coordinate chart, the Euclidean Harnack
  estimate bounds the function on the smaller disk by three times its value
  at the center.  Transport the estimate back through the chart.
-/
theorem local_harnack_control_for_nonnegative_harmonic_function
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    {U : Set X} (hU_open : IsOpen U)
    {x : X} (hxU : x ∈ U) :
    ∃ N : Set X, N ∈ 𝓝 x ∧ N ⊆ U ∧
      ∃ C : ℝ, 0 < C ∧
        ∀ {u : X → ℝ},
          IsHarmonicOnSurface U u →
            (∀ y ∈ U, 0 ≤ u y) →
              ∀ y ∈ N, u y ≤ C * u x := by
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ x
  let z : ℂ := e x
  have hxsource : x ∈ e.source := mem_chart_source ℂ x
  have he : e ∈ atlas ℂ X := chart_mem_atlas ℂ x
  let S : Set ℂ := e.target ∩ e.symm ⁻¹' U
  have hS_open : IsOpen S := by
    simpa [S] using e.isOpen_inter_preimage_symm hU_open
  have hzS : z ∈ S := by
    refine ⟨e.map_source hxsource, ?_⟩
    simpa [z, e.left_inv hxsource] using hxU
  rcases Metric.mem_nhds_iff.mp (hS_open.mem_nhds hzS) with
    ⟨R, hR_pos, hR_subset⟩
  let r : ℝ := R / 2
  have hr : 0 < r := by
    positivity
  have hr_lt_R : r < R := by
    dsimp [r]
    linarith
  have hclosedS : Metric.closedBall z r ⊆ S :=
    (Metric.closedBall_subset_ball (x := z) hr_lt_R).trans hR_subset
  let N : Set X := e.source ∩ e ⁻¹' Metric.ball z (r / 2)
  have hN_nhds : N ∈ 𝓝 x := by
    have hsource : e.source ∈ 𝓝 x := e.open_source.mem_nhds hxsource
    have hball : Metric.ball z (r / 2) ∈ 𝓝 (e x) := by
      simpa [z] using Metric.ball_mem_nhds (x := z) (half_pos hr)
    have hpre : e ⁻¹' Metric.ball z (r / 2) ∈ 𝓝 x :=
      e.continuousAt hxsource hball
    exact Filter.inter_mem hsource hpre
  have hsmall_closed : Metric.ball z (r / 2) ⊆ Metric.closedBall z r := by
    exact Metric.ball_subset_closedBall.trans
      (Metric.closedBall_subset_closedBall (x := z) (by
        dsimp [r]
        linarith : r / 2 ≤ r))
  have hN_subset : N ⊆ U := by
    intro y hy
    have hysource : y ∈ e.source := hy.1
    have hyS : e y ∈ S := hclosedS (hsmall_closed hy.2)
    simpa [e.left_inv hysource] using hyS.2
  refine ⟨N, hN_nhds, hN_subset, 3, by norm_num, ?_⟩
  intro u hu_harm hu_nonneg y hyN
  have hysource : y ∈ e.source := hyN.1
  have hcoord :
      InnerProductSpace.HarmonicOnNhd
        (fun w : ℂ ↦ u (e.symm w)) S := by
    simpa [S] using hu_harm e he
  have hcoord_small :
      InnerProductSpace.HarmonicOnNhd
        (fun w : ℂ ↦ u (e.symm w)) (Metric.closedBall z r) :=
    hcoord.mono hclosedS
  have hcoord_nonneg :
      ∀ w ∈ Metric.closedBall z r, 0 ≤ u (e.symm w) := by
    intro w hw
    have hwS : w ∈ S := hclosedS hw
    exact hu_nonneg (e.symm w) hwS.2
  have hchart :=
    harmonicOnNhd_nonnegative_le_three_mul_center_of_mem_ball_half
      (c := z) (r := r) hr
      (u := fun w : ℂ ↦ u (e.symm w))
      hcoord_small hcoord_nonneg hyN.2
  simpa [z, e.left_inv hysource, e.left_inv hxsource] using hchart

/--
%%handwave
name:
  Pairwise local Harnack control for nonnegative harmonic functions
statement:
  Near every point of a surface region, the values of any nonnegative
  harmonic function at any two nearby points are comparable by a fixed
  constant.
proof:
  Choose a coordinate disk around the point.  A smaller quarter-radius disk
  has the property that each of its points is itself the center of a
  half-radius disk still contained in the original one.  Applying the
  Euclidean Harnack estimate once from a nearby point to the original center
  and once from the original center to another nearby point gives the
  pairwise comparison.
-/
theorem local_harnack_pair_control_for_nonnegative_harmonic_function
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    {U : Set X} (hU_open : IsOpen U)
    {x : X} (hxU : x ∈ U) :
    ∃ N : Set X, N ∈ 𝓝 x ∧ N ⊆ U ∧
      ∃ C : ℝ, 0 < C ∧
        ∀ {u : X → ℝ},
          IsHarmonicOnSurface U u →
            (∀ y ∈ U, 0 ≤ u y) →
              ∀ a ∈ N, ∀ b ∈ N, u a ≤ C * u b := by
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ x
  let z : ℂ := e x
  have hxsource : x ∈ e.source := mem_chart_source ℂ x
  have he : e ∈ atlas ℂ X := chart_mem_atlas ℂ x
  let S : Set ℂ := e.target ∩ e.symm ⁻¹' U
  have hS_open : IsOpen S := by
    simpa [S] using e.isOpen_inter_preimage_symm hU_open
  have hzS : z ∈ S := by
    refine ⟨e.map_source hxsource, ?_⟩
    simpa [z, e.left_inv hxsource] using hxU
  rcases Metric.mem_nhds_iff.mp (hS_open.mem_nhds hzS) with
    ⟨R, hR_pos, hR_subset⟩
  let r : ℝ := R / 2
  have hr : 0 < r := by
    positivity
  have hr_lt_R : r < R := by
    dsimp [r]
    linarith
  have hclosedS : Metric.closedBall z r ⊆ S :=
    (Metric.closedBall_subset_ball (x := z) hr_lt_R).trans hR_subset
  let N : Set X := e.source ∩ e ⁻¹' Metric.ball z (r / 4)
  have hN_nhds : N ∈ 𝓝 x := by
    have hsource : e.source ∈ 𝓝 x := e.open_source.mem_nhds hxsource
    have hball : Metric.ball z (r / 4) ∈ 𝓝 (e x) := by
      simpa [z] using Metric.ball_mem_nhds (x := z) (by positivity : 0 < r / 4)
    have hpre : e ⁻¹' Metric.ball z (r / 4) ∈ 𝓝 x :=
      e.continuousAt hxsource hball
    exact Filter.inter_mem hsource hpre
  have hsmall_closed : Metric.ball z (r / 4) ⊆ Metric.closedBall z r := by
    exact Metric.ball_subset_closedBall.trans
      (Metric.closedBall_subset_closedBall (x := z) (by
        dsimp [r]
        linarith : r / 4 ≤ r))
  have hN_subset : N ⊆ U := by
    intro y hy
    have hysource : y ∈ e.source := hy.1
    have hyS : e y ∈ S := hclosedS (hsmall_closed hy.2)
    simpa [e.left_inv hysource] using hyS.2
  refine ⟨N, hN_nhds, hN_subset, 9, by norm_num, ?_⟩
  intro u hu_harm hu_nonneg a haN b hbN
  have hasource : a ∈ e.source := haN.1
  have hbsource : b ∈ e.source := hbN.1
  have hcoord :
      InnerProductSpace.HarmonicOnNhd
        (fun w : ℂ ↦ u (e.symm w)) S := by
    simpa [S] using hu_harm e he
  have hcoord_small :
      InnerProductSpace.HarmonicOnNhd
        (fun w : ℂ ↦ u (e.symm w)) (Metric.closedBall z r) :=
    hcoord.mono hclosedS
  have hcoord_nonneg :
      ∀ w ∈ Metric.closedBall z r, 0 ≤ u (e.symm w) := by
    intro w hw
    have hwS : w ∈ S := hclosedS hw
    exact hu_nonneg (e.symm w) hwS.2
  have ha_half : e a ∈ Metric.ball z (r / 2) := by
    exact Metric.ball_subset_ball (by linarith : r / 4 ≤ r / 2) haN.2
  have ha_to_center :
      u a ≤ 3 * u x := by
    have hchart :=
      harmonicOnNhd_nonnegative_le_three_mul_center_of_mem_ball_half
        (c := z) (r := r) hr
        (u := fun w : ℂ ↦ u (e.symm w))
        hcoord_small hcoord_nonneg ha_half
    simpa [z, e.left_inv hasource, e.left_inv hxsource] using hchart
  let rb : ℝ := r / 2
  have hrb : 0 < rb := by
    dsimp [rb]
    positivity
  have hclosed_b_subset :
      Metric.closedBall (e b) rb ⊆ Metric.closedBall z r := by
    intro w hw
    rw [Metric.mem_closedBall] at hw ⊢
    have hb_dist : dist (e b) z < r / 4 := by
      simpa [Metric.mem_ball] using hbN.2
    calc
      dist w z ≤ dist w (e b) + dist (e b) z := dist_triangle w (e b) z
      _ ≤ rb + dist (e b) z := add_le_add hw le_rfl
      _ ≤ r := by
        dsimp [rb]
        linarith
  have hcoord_b :
      InnerProductSpace.HarmonicOnNhd
        (fun w : ℂ ↦ u (e.symm w)) (Metric.closedBall (e b) rb) :=
    hcoord_small.mono hclosed_b_subset
  have hcoord_b_nonneg :
      ∀ w ∈ Metric.closedBall (e b) rb, 0 ≤ u (e.symm w) := by
    intro w hw
    exact hcoord_nonneg w (hclosed_b_subset hw)
  have hz_mem_b_half : z ∈ Metric.ball (e b) (rb / 2) := by
    rw [Metric.mem_ball]
    have hrb_half : rb / 2 = r / 4 := by
      dsimp [rb]
      ring
    have hb_dist : dist (e b) z < r / 4 := by
      simpa [Metric.mem_ball] using hbN.2
    rw [hrb_half]
    simpa [dist_comm] using hb_dist
  have hcenter_to_b :
      u x ≤ 3 * u b := by
    have hchart :=
      harmonicOnNhd_nonnegative_le_three_mul_center_of_mem_ball_half
        (c := e b) (r := rb) hrb
        (u := fun w : ℂ ↦ u (e.symm w))
        hcoord_b hcoord_b_nonneg hz_mem_b_half
    simpa [z, e.left_inv hxsource, e.left_inv hbsource] using hchart
  calc
    u a ≤ 3 * u x := ha_to_center
    _ ≤ 3 * (3 * u b) :=
        mul_le_mul_of_nonneg_left hcenter_to_b (by norm_num : (0 : ℝ) ≤ 3)
    _ = 9 * u b := by ring

/--
%%handwave
name:
  Local Harnack bounds propagate on preconnected regions
statement:
  On a preconnected region, if a family of functions has pairwise local
  Harnack control and is eventually bounded above at one point, then it is
  eventually bounded above at every point of the region.
proof:
  In the region, consider the points where the family is eventually bounded.
  The base point makes this set nonempty.  Pairwise local Harnack control
  makes it open, and it also makes its complement open because a nearby
  bounded point would bound the original point.  Preconnectedness forces the
  set to be the whole region.
-/
theorem eventual_upper_bound_propagates_of_local_pair_harnack_control
    {X : Type} [TopologicalSpace X]
    {U : Set X} (hU_preconnected : IsPreconnected U)
    {F : ℕ → X → ℝ}
    (hlocal :
      ∀ x ∈ U,
        ∃ N : Set X, N ∈ 𝓝 x ∧ N ⊆ U ∧
          ∃ C : ℝ, 0 ≤ C ∧
            ∀ᶠ n : ℕ in Filter.atTop,
              ∀ a ∈ N, ∀ b ∈ N, F n a ≤ C * F n b)
    {x₀ : X} (hx₀ : x₀ ∈ U)
    (hbase : ∃ A : ℝ, ∀ᶠ n : ℕ in Filter.atTop, F n x₀ ≤ A) :
    ∀ x ∈ U, ∃ A : ℝ, ∀ᶠ n : ℕ in Filter.atTop, F n x ≤ A := by
  classical
  let S : Set U := {x | ∃ A : ℝ, ∀ᶠ n : ℕ in Filter.atTop, F n x ≤ A}
  have hS_nonempty : S.Nonempty := ⟨⟨x₀, hx₀⟩, hbase⟩
  have hS_open : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro x hxS
    rcases hxS with ⟨A, hA⟩
    rcases hlocal x x.property with ⟨N, hN_nhds, _hN_subset, C, hC_nonneg, hcontrol⟩
    have hxN : (x : X) ∈ N := mem_of_mem_nhds hN_nhds
    let V : Set U := {y | (y : X) ∈ N}
    have hV_mem : V ∈ 𝓝 x :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds hN_nhds
    refine Filter.mem_of_superset hV_mem ?_
    intro y hyV
    refine ⟨C * A, ?_⟩
    filter_upwards [hcontrol, hA] with n hn hAn
    exact (hn y hyV x hxN).trans
      (mul_le_mul_of_nonneg_left hAn hC_nonneg)
  have hS_compl_open : IsOpen Sᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro x hxS
    rcases hlocal x x.property with ⟨N, hN_nhds, _hN_subset, C, hC_nonneg, hcontrol⟩
    have hxN : (x : X) ∈ N := mem_of_mem_nhds hN_nhds
    let V : Set U := {y | (y : X) ∈ N}
    have hV_mem : V ∈ 𝓝 x :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds hN_nhds
    refine Filter.mem_of_superset hV_mem ?_
    intro y hyV hyS
    apply hxS
    rcases hyS with ⟨A, hA⟩
    refine ⟨C * A, ?_⟩
    filter_upwards [hcontrol, hA] with n hn hAn
    exact (hn x hxN y hyV).trans
      (mul_le_mul_of_nonneg_left hAn hC_nonneg)
  have hS_closed : IsClosed S := isOpen_compl_iff.mp hS_compl_open
  haveI : PreconnectedSpace U := Subtype.preconnectedSpace hU_preconnected
  have hS_univ : S = Set.univ :=
    IsClopen.eq_univ ⟨hS_closed, hS_open⟩ hS_nonempty
  intro x hxU
  have hxS : (⟨x, hxU⟩ : U) ∈ S := by
    simp [hS_univ]
  exact hxS

/--
%%handwave
name:
  Pairwise local Harnack control gives local uniform bounds
statement:
  If a family of functions has pairwise local Harnack control and is
  eventually bounded above at each point of a region, then near each point it
  is eventually bounded above uniformly on a neighborhood.
proof:
  At a point, choose a Harnack neighborhood and an eventual bound at the
  center.  Pairwise control with the center as the second point gives a
  uniform bound throughout the neighborhood.
-/
theorem eventual_locally_uniform_upper_bound_of_local_pair_harnack_control
    {X : Type} [TopologicalSpace X]
    {U : Set X} {F : ℕ → X → ℝ}
    (hlocal :
      ∀ x ∈ U,
        ∃ N : Set X, N ∈ 𝓝 x ∧ N ⊆ U ∧
          ∃ C : ℝ, 0 ≤ C ∧
            ∀ᶠ n : ℕ in Filter.atTop,
              ∀ a ∈ N, ∀ b ∈ N, F n a ≤ C * F n b)
    (hpoint :
      ∀ x ∈ U, ∃ A : ℝ, ∀ᶠ n : ℕ in Filter.atTop, F n x ≤ A) :
    ∀ x ∈ U,
      ∃ N : Set X, N ∈ 𝓝 x ∧ N ⊆ U ∧
        ∃ M : ℝ,
          ∀ᶠ n : ℕ in Filter.atTop, ∀ y ∈ N, F n y ≤ M := by
  intro x hxU
  rcases hlocal x hxU with ⟨N, hN_nhds, hN_subset, C, hC_nonneg, hcontrol⟩
  rcases hpoint x hxU with ⟨A, hA⟩
  have hxN : x ∈ N := mem_of_mem_nhds hN_nhds
  refine ⟨N, hN_nhds, hN_subset, C * A, ?_⟩
  filter_upwards [hcontrol, hA] with n hn hAn y hyN
  exact (hn y hyN x hxN).trans
    (mul_le_mul_of_nonneg_left hAn hC_nonneg)

/--
%%handwave
name:
  Base-point Harnack bounds give local uniform bounds on preconnected regions
statement:
  On a preconnected region, if a family of functions has pairwise local
  Harnack control and is eventually bounded above at one point, then near
  every point it is eventually bounded above uniformly on a neighborhood.
proof:
  First propagate the base-point bound to pointwise bounds throughout the
  region.  Then apply the local pairwise Harnack control once more to turn
  the pointwise bound at each center into a uniform bound on a neighborhood.
-/
theorem eventual_locally_uniform_upper_bound_propagates_of_local_pair_harnack_control
    {X : Type} [TopologicalSpace X]
    {U : Set X} (hU_preconnected : IsPreconnected U)
    {F : ℕ → X → ℝ}
    (hlocal :
      ∀ x ∈ U,
        ∃ N : Set X, N ∈ 𝓝 x ∧ N ⊆ U ∧
          ∃ C : ℝ, 0 ≤ C ∧
            ∀ᶠ n : ℕ in Filter.atTop,
              ∀ a ∈ N, ∀ b ∈ N, F n a ≤ C * F n b)
    {x₀ : X} (hx₀ : x₀ ∈ U)
    (hbase : ∃ A : ℝ, ∀ᶠ n : ℕ in Filter.atTop, F n x₀ ≤ A) :
    ∀ x ∈ U,
      ∃ N : Set X, N ∈ 𝓝 x ∧ N ⊆ U ∧
        ∃ M : ℝ,
          ∀ᶠ n : ℕ in Filter.atTop, ∀ y ∈ N, F n y ≤ M := by
  have hpoint :
      ∀ x ∈ U, ∃ A : ℝ, ∀ᶠ n : ℕ in Filter.atTop, F n x ≤ A :=
    eventual_upper_bound_propagates_of_local_pair_harnack_control
      hU_preconnected hlocal hx₀ hbase
  exact eventual_locally_uniform_upper_bound_of_local_pair_harnack_control
    hlocal hpoint

/--
%%handwave
name:
  Local eventual bounds give compact eventual bounds
statement:
  If every point of a region has an open neighborhood on which a sequence is
  eventually bounded above, then every compact subset of the region has a
  single eventual upper bound.
proof:
  Cover the compact set by the local open neighborhoods and pass to a finite
  subcover.  Intersect the finitely many eventual bounds and dominate the
  finitely many constants by their sum of absolute values.
-/
theorem eventual_uniform_upper_bound_on_compact_of_open_local_uniform_upper_bound
    {X : Type} [TopologicalSpace X]
    {K U : Set X} {F : ℕ → X → ℝ}
    {O : X → Set X} {M : X → ℝ}
    (hK_compact : IsCompact K) (hKU : K ⊆ U)
    (hO_open : ∀ x ∈ U, IsOpen (O x))
    (hxO : ∀ x ∈ U, x ∈ O x)
    (hbound :
      ∀ x ∈ U,
        ∀ᶠ n : ℕ in Filter.atTop, ∀ y ∈ O x, F n y ≤ M x) :
    ∃ A : ℝ,
      ∀ᶠ n : ℕ in Filter.atTop, ∀ y ∈ K, F n y ≤ A := by
  classical
  let V : X → Set X := fun x ↦ if x ∈ U then O x else ∅
  have hV_open : ∀ x : X, IsOpen (V x) := by
    intro x
    by_cases hxU : x ∈ U
    · simpa [V, hxU] using hO_open x hxU
    · simp [V, hxU]
  have hcover : K ⊆ ⋃ x : X, V x := by
    intro x hxK
    have hxU : x ∈ U := hKU hxK
    exact Set.mem_iUnion.mpr ⟨x, by simpa [V, hxU] using hxO x hxU⟩
  rcases hK_compact.elim_finite_subcover V hV_open hcover with ⟨t, ht⟩
  let A : ℝ := t.sum (fun x ↦ |M x|)
  refine ⟨A, ?_⟩
  have hfinite :
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ x ∈ t, ∀ y ∈ V x, F n y ≤ M x := by
    rw [Finset.eventually_all]
    intro x hx_t
    by_cases hxU : x ∈ U
    · filter_upwards [hbound x hxU] with n hn y hyV
      exact hn y (by simpa [V, hxU] using hyV)
    · exact Filter.Eventually.of_forall (fun n y hyV ↦ by
        simp [V, hxU] at hyV)
  filter_upwards [hfinite] with n hn y hyK
  have hyUnion : y ∈ ⋃ x ∈ t, V x := ht hyK
  rcases Set.mem_iUnion.mp hyUnion with ⟨x, hxUnion⟩
  rcases Set.mem_iUnion.mp hxUnion with ⟨hx_t, hyV⟩
  have hFy : F n y ≤ M x := hn x hx_t y hyV
  have hMxA : M x ≤ A := by
    exact (le_abs_self (M x)).trans
      (Finset.single_le_sum (fun z _hz ↦ abs_nonneg (M z)) hx_t)
  exact hFy.trans hMxA

/--
%%handwave
name:
  Pairwise Harnack bounds give compact eventual bounds
statement:
  On a preconnected region, if a sequence has pairwise local Harnack control
  and is eventually bounded above at one point, then it has a single eventual
  upper bound on every compact subset of the region.
proof:
  The base-point bound propagates to local uniform bounds throughout the
  region.  A finite subcover of the compact set then gives one eventual
  bound on the whole compact set.
-/
theorem eventual_uniform_upper_bound_on_compact_propagates_of_local_pair_harnack_control
    {X : Type} [TopologicalSpace X]
    {K U : Set X} (hU_preconnected : IsPreconnected U)
    (hK_compact : IsCompact K) (hKU : K ⊆ U)
    {F : ℕ → X → ℝ}
    (hlocal :
      ∀ x ∈ U,
        ∃ N : Set X, N ∈ 𝓝 x ∧ N ⊆ U ∧
          ∃ C : ℝ, 0 ≤ C ∧
            ∀ᶠ n : ℕ in Filter.atTop,
              ∀ a ∈ N, ∀ b ∈ N, F n a ≤ C * F n b)
    {x₀ : X} (hx₀ : x₀ ∈ U)
    (hbase : ∃ A : ℝ, ∀ᶠ n : ℕ in Filter.atTop, F n x₀ ≤ A) :
    ∃ A : ℝ,
      ∀ᶠ n : ℕ in Filter.atTop, ∀ y ∈ K, F n y ≤ A := by
  classical
  have hloc :
      ∀ x ∈ U,
        ∃ N : Set X, N ∈ 𝓝 x ∧ N ⊆ U ∧
          ∃ M : ℝ,
            ∀ᶠ n : ℕ in Filter.atTop, ∀ y ∈ N, F n y ≤ M :=
    eventual_locally_uniform_upper_bound_propagates_of_local_pair_harnack_control
      hU_preconnected hlocal hx₀ hbase
  choose N hN_nhds hN_subset M hM using hloc
  choose O hO_subset hO_open hxO using fun x hxU ↦ mem_nhds_iff.mp (hN_nhds x hxU)
  let O' : X → Set X := fun x ↦ if hxU : x ∈ U then O x hxU else ∅
  let M' : X → ℝ := fun x ↦ if hxU : x ∈ U then M x hxU else 0
  exact eventual_uniform_upper_bound_on_compact_of_open_local_uniform_upper_bound
    (K := K) (U := U) (F := F) (O := O') (M := M')
    hK_compact hKU
    (fun x hxU ↦ by simpa [O', hxU] using hO_open x hxU)
    (fun x hxU ↦ by simpa [O', hxU] using hxO x hxU)
    (fun x hxU ↦ by
      filter_upwards [hM x hxU] with n hn y hyO
      have hyO' : y ∈ O x hxU := by
        simpa [O', hxU] using hyO
      have hny : F n y ≤ M x hxU := hn y (hO_subset x hxU hyO')
      simpa [M', hxU] using hny)

/--
%%handwave
name:
  Local Harnack control for harmonic gaps
statement:
  Near every point of a surface region, positive differences of a monotone
  harmonic family are controlled by their value at that point.
proof:
  Choose a coordinate disk with a smaller concentric disk around the point.
  For a nonnegative harmonic difference \(u\), the Poisson formula and the
  upper bound for the Poisson kernel on the smaller disk give
  \(\sup u \le C u(x)\).  Transport this estimate through the chart.
-/
theorem local_harnack_gap_control_for_directed_harmonic_family
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    {ι : Type} [Preorder ι]
    {U : Set X} (hU_open : IsOpen U)
    {F : ι → X → ℝ}
    (_hF_harmonic : ∀ i, IsHarmonicOnSurface U (F i))
    (_hF_mono : ∀ ⦃i j : ι⦄, i ≤ j → ∀ x ∈ U, F i x ≤ F j x)
    {x : X} (hxU : x ∈ U) :
    ∃ N : Set X, N ∈ 𝓝 x ∧ N ⊆ U ∧
      ∃ C : ℝ, 0 < C ∧
        ∀ ⦃i j : ι⦄, i ≤ j →
          ∀ y ∈ N, F j y - F i y ≤ C * (F j x - F i x) := by
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ x
  let z : ℂ := e x
  have hxsource : x ∈ e.source := mem_chart_source ℂ x
  have he : e ∈ atlas ℂ X := chart_mem_atlas ℂ x
  let S : Set ℂ := e.target ∩ e.symm ⁻¹' U
  have hS_open : IsOpen S := by
    simpa [S] using e.isOpen_inter_preimage_symm hU_open
  have hzS : z ∈ S := by
    refine ⟨e.map_source hxsource, ?_⟩
    simpa [z, e.left_inv hxsource] using hxU
  rcases Metric.mem_nhds_iff.mp (hS_open.mem_nhds hzS) with
    ⟨R, hR_pos, hR_subset⟩
  let r : ℝ := R / 2
  have hr : 0 < r := by
    positivity
  have hr_lt_R : r < R := by
    dsimp [r]
    linarith
  have hclosedS : Metric.closedBall z r ⊆ S :=
    (Metric.closedBall_subset_ball (x := z) hr_lt_R).trans hR_subset
  let N : Set X := e.source ∩ e ⁻¹' Metric.ball z (r / 2)
  have hN_nhds : N ∈ 𝓝 x := by
    have hsource : e.source ∈ 𝓝 x := e.open_source.mem_nhds hxsource
    have hball : Metric.ball z (r / 2) ∈ 𝓝 (e x) := by
      simpa [z] using Metric.ball_mem_nhds (x := z) (half_pos hr)
    have hpre : e ⁻¹' Metric.ball z (r / 2) ∈ 𝓝 x :=
      e.continuousAt hxsource hball
    exact Filter.inter_mem hsource hpre
  have hsmall_closed : Metric.ball z (r / 2) ⊆ Metric.closedBall z r := by
    exact Metric.ball_subset_closedBall.trans
      (Metric.closedBall_subset_closedBall (x := z) (by
        dsimp [r]
        linarith : r / 2 ≤ r))
  have hN_subset : N ⊆ U := by
    intro y hy
    have hysource : y ∈ e.source := hy.1
    have hyS : e y ∈ S := hclosedS (hsmall_closed hy.2)
    simpa [e.left_inv hysource] using hyS.2
  refine ⟨N, hN_nhds, hN_subset, 3, by norm_num, ?_⟩
  intro i j hij y hyN
  have hysource : y ∈ e.source := hyN.1
  have hcoord_j :
      InnerProductSpace.HarmonicOnNhd
        (fun w : ℂ ↦ F j (e.symm w)) S := by
    simpa [S] using _hF_harmonic j e he
  have hcoord_i :
      InnerProductSpace.HarmonicOnNhd
        (fun w : ℂ ↦ F i (e.symm w)) S := by
    simpa [S] using _hF_harmonic i e he
  have hgap_harm :
      InnerProductSpace.HarmonicOnNhd
        (fun w : ℂ ↦ F j (e.symm w) - F i (e.symm w))
        (Metric.closedBall z r) := by
    simpa [Pi.sub_apply] using
      ((hcoord_j.mono hclosedS).sub (hcoord_i.mono hclosedS))
  have hgap_nonneg :
      ∀ w ∈ Metric.closedBall z r,
        0 ≤ F j (e.symm w) - F i (e.symm w) := by
    intro w hw
    have hwS : w ∈ S := hclosedS hw
    exact sub_nonneg.mpr (_hF_mono hij (e.symm w) hwS.2)
  have hchart :=
    harmonicOnNhd_nonnegative_le_three_mul_center_of_mem_ball_half
      (c := z) (r := r) hr
      (u := fun w : ℂ ↦ F j (e.symm w) - F i (e.symm w))
      hgap_harm hgap_nonneg hyN.2
  simpa [z, e.left_inv hysource, e.left_inv hxsource] using hchart

/--
%%handwave
name:
  Harnack gap control gives locally uniform convergence
statement:
  If a directed monotone family has local Harnack control for its positive
  gaps and converges pointwise to its least upper bound, then it converges
  locally uniformly.
proof:
  Fix a point and a Harnack neighborhood \(N\) with constant \(C\).  Pointwise
  convergence at the center gives an index \(i\) with \(P(x)-F_i(x)\) small.
  For any later index \(j\), Harnack controls \(F_j-F_i\) on \(N\).  Since
  \(P\) is the least upper bound of the directed range, the same bound holds
  for \(P-F_i\) on \(N\).  This is exactly local uniform convergence.
-/
theorem tendstoLocallyUniformlyOn_of_local_harnack_gap_control
    {X ι : Type} [TopologicalSpace X] [Preorder ι] [IsDirectedOrder ι]
    {U : Set X} {F : ι → X → ℝ} {P : X → ℝ}
    (hlocal :
      ∀ x ∈ U, ∃ N : Set X, N ∈ 𝓝 x ∧ N ⊆ U ∧
        ∃ C : ℝ, 0 < C ∧
          ∀ ⦃i j : ι⦄, i ≤ j →
            ∀ y ∈ N, F j y - F i y ≤ C * (F j x - F i x))
    (hmono : ∀ ⦃i j : ι⦄, i ≤ j → ∀ x ∈ U, F i x ≤ F j x)
    (hpoint :
      ∀ x ∈ U, Filter.Tendsto (fun i : ι ↦ F i x) Filter.atTop (𝓝 (P x)))
    (hLUB :
      ∀ x ∈ U, IsLUB (Set.range (fun i : ι ↦ F i x)) (P x)) :
    TendstoLocallyUniformlyOn F P Filter.atTop U := by
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  intro ε hε x hxU
  rcases hlocal x hxU with ⟨N, hN_nhds, hN_subset, C, hC_pos, hgap⟩
  refine ⟨N, nhdsWithin_le_nhds hN_nhds, ?_⟩
  have hδ_pos : 0 < ε / C := div_pos hε hC_pos
  have hcenter :
      ∀ᶠ i in Filter.atTop, dist (F i x) (P x) < ε / C :=
    (Metric.tendsto_nhds.mp (hpoint x hxU)) (ε / C) hδ_pos
  filter_upwards [hcenter] with i hi_center y hyN
  have hyU : y ∈ U := hN_subset hyN
  have hFi_le_Px : F i x ≤ P x :=
    (hLUB x hxU).1 ⟨i, rfl⟩
  have hFi_le_Py : F i y ≤ P y :=
    (hLUB y hyU).1 ⟨i, rfl⟩
  have hcenter_gap_lt : P x - F i x < ε / C := by
    rw [Real.dist_eq] at hi_center
    have habs : |F i x - P x| = P x - F i x := by
      rw [abs_of_nonpos (sub_nonpos.mpr hFi_le_Px)]
      ring
    simpa [habs] using hi_center
  have hupper :
      (F i y + C * (P x - F i x)) ∈
        upperBounds (Set.range (fun j : ι ↦ F j y)) := by
    intro a ha
    rcases ha with ⟨j, rfl⟩
    rcases exists_ge_ge i j with ⟨k, hik, hjk⟩
    have hgap_k :
        F k y - F i y ≤ C * (F k x - F i x) :=
      hgap hik y hyN
    have hFk_le_Px : F k x ≤ P x :=
      (hLUB x hxU).1 ⟨k, rfl⟩
    have hx_gap_le : F k x - F i x ≤ P x - F i x := by
      linarith
    have hgap_bound :
        F k y - F i y ≤ C * (P x - F i x) :=
      hgap_k.trans
        (mul_le_mul_of_nonneg_left hx_gap_le (le_of_lt hC_pos))
    have hj_le_k_y : F j y ≤ F k y :=
      hmono hjk y hyU
    linarith
  have hP_le_bound :
      P y ≤ F i y + C * (P x - F i x) :=
    (hLUB y hyU).2 hupper
  have hdiff_le :
      P y - F i y ≤ C * (P x - F i x) := by
    linarith
  have hmul_lt : C * (P x - F i x) < ε := by
    have hC_nonneg : 0 ≤ C := le_of_lt hC_pos
    have hmul := mul_lt_mul_of_pos_left hcenter_gap_lt hC_pos
    field_simp at hmul
    exact hmul
  have hdist_eq : dist (P y) (F i y) = P y - F i y := by
    rw [Real.dist_eq, abs_of_nonneg]
    exact sub_nonneg.mpr hFi_le_Py
  rw [hdist_eq]
  exact lt_of_le_of_lt hdiff_le (lt_of_lt_of_le hmul_lt (le_of_eq rfl))

/--
%%handwave
name:
  Harnack convergence for directed harmonic minorants
statement:
  On a coordinate disk, the directed net of harmonic minorants ordered by
  pointwise domination converges locally uniformly to its pointwise supremum,
  provided the family is locally bounded above.
proof:
  This is the analytic Harnack compactness theorem in net form.  Harnack
  estimates turn local upper bounds and monotonicity into local equicontinuity
  and local uniform Cauchy control.  The already formalized
  [pointwise convergence](lean:JJMath.Uniformization.harmonicMinorantIndex_tendsto_atTop_pointwise_sSup)
  identifies the locally uniform limit with \(P\).
-/
theorem harnack_directed_harmonic_minorants_tendstoLocallyUniformlyOn
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (V : PerronDomain X) (_hV_coord : IsCoordinatePerronDisk V)
    (P : X → ℝ) (H : Set (X → ℝ))
    (hH_nonempty : H.Nonempty)
    (hH_harmonic : ∀ h ∈ H, IsHarmonicOnSurface V.carrier h)
    (hH_directed :
      ∀ h₁ ∈ H, ∀ h₂ ∈ H,
        ∃ h₃ ∈ H, ∀ x ∈ V.carrier, h₁ x ≤ h₃ x ∧ h₂ x ≤ h₃ x)
    (hH_locally_bounded :
      ∀ K : Set X, IsCompact K → K ⊆ V.carrier →
        ∃ M : ℝ, ∀ h ∈ H, ∀ x ∈ K, h x ≤ M)
    (hH_pointwise_sSup :
      ∀ x ∈ V.carrier, sSup {a : ℝ | ∃ h ∈ H, a = h x} = P x) :
    TendstoLocallyUniformlyOn
      (fun i : HarmonicMinorantIndex V H ↦ (i : X → ℝ))
      P Filter.atTop V.carrier := by
  let I := HarmonicMinorantIndex V H
  haveI : Nonempty I := HarmonicMinorantIndex.nonempty hH_nonempty
  haveI : IsDirectedOrder I := HarmonicMinorantIndex.isDirectedOrder hH_directed
  have hlocal :
      ∀ x ∈ V.carrier, ∃ N : Set X, N ∈ 𝓝 x ∧ N ⊆ V.carrier ∧
        ∃ C : ℝ, 0 < C ∧
          ∀ ⦃i j : I⦄, i ≤ j →
            ∀ y ∈ N, j y - i y ≤ C * (j x - i x) := by
    intro x hx
    exact local_harnack_gap_control_for_directed_harmonic_family V.isOpen
      (fun i : I ↦ hH_harmonic i.toFun i.mem)
      (fun {i j : I} hij x hx ↦ by
        have hij' : ∀ x ∈ V.carrier, i x ≤ j x := hij
        exact hij' x hx)
      hx
  have hpoint :
      ∀ x ∈ V.carrier,
        Filter.Tendsto (fun i : I ↦ i x) Filter.atTop (𝓝 (P x)) := by
    intro x hx
    exact harmonicMinorantIndex_tendsto_atTop_pointwise_sSup
      V P H hH_nonempty hH_locally_bounded hH_pointwise_sSup hx
  have hLUB :
      ∀ x ∈ V.carrier,
        IsLUB (Set.range (fun i : I ↦ i x)) (P x) := by
    intro x hxV
    have hvalue_nonempty : {a : ℝ | ∃ h ∈ H, a = h x}.Nonempty := by
      rcases hH_nonempty with ⟨h, hh⟩
      exact ⟨h x, h, hh, rfl⟩
    have hsingleton_subset : ({x} : Set X) ⊆ V.carrier := by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      simpa [hy] using hxV
    rcases hH_locally_bounded ({x} : Set X) isCompact_singleton
        hsingleton_subset with
      ⟨M, hM⟩
    have hvalue_bdd : BddAbove {a : ℝ | ∃ h ∈ H, a = h x} := by
      refine ⟨M, ?_⟩
      intro a ha
      rcases ha with ⟨h, hh, rfl⟩
      exact hM h hh x (by simp)
    have hvalue_lub :
        IsLUB {a : ℝ | ∃ h ∈ H, a = h x} (P x) := by
      have hsSup_lub :
          IsLUB {a : ℝ | ∃ h ∈ H, a = h x}
            (sSup {a : ℝ | ∃ h ∈ H, a = h x}) :=
        isLUB_csSup hvalue_nonempty hvalue_bdd
      simpa [hH_pointwise_sSup x hxV] using hsSup_lub
    have hrange :
        Set.range (fun i : I ↦ i x) =
          {a : ℝ | ∃ h ∈ H, a = h x} := by
      ext a
      constructor
      · intro ha
        rcases ha with ⟨i, rfl⟩
        exact ⟨i.toFun, i.mem, rfl⟩
      · intro ha
        rcases ha with ⟨h, hh, rfl⟩
        exact ⟨⟨h, hh⟩, rfl⟩
    rwa [hrange]
  have hmono :
      ∀ ⦃i j : I⦄, i ≤ j → ∀ x ∈ V.carrier, i x ≤ j x := by
    intro i j hij x hx
    have hij' : ∀ x ∈ V.carrier, i x ≤ j x := hij
    exact hij' x hx
  exact tendstoLocallyUniformlyOn_of_local_harnack_gap_control
    hlocal hmono hpoint hLUB

/--
%%handwave
name:
  Pointwise suprema of directed harmonic families are harmonic
statement:
  On a coordinate disk, the pointwise supremum of a directed family of
  harmonic functions is harmonic, provided the family is locally bounded above
  and the resulting function is lower semicontinuous.
proof:
  The directed harmonic minorants
  [converge locally uniformly to their pointwise supremum](lean:JJMath.Uniformization.harnack_directed_harmonic_minorants_tendstoLocallyUniformlyOn)
  by Harnack compactness.  Since
  [surface harmonic functions are closed under locally uniform limits](lean:JJMath.Uniformization.harmonicOnSurface_of_tendstoLocallyUniformlyOn),
  the supremum is harmonic.
-/
theorem pointwise_sSup_directed_harmonic_family_harmonicOn_coordinate_disk
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (V : PerronDomain X) (hV_coord : IsCoordinatePerronDisk V)
    (P : X → ℝ) (H : Set (X → ℝ))
    (hH_nonempty : H.Nonempty)
    (hH_harmonic : ∀ h ∈ H, IsHarmonicOnSurface V.carrier h)
    (hH_directed :
      ∀ h₁ ∈ H, ∀ h₂ ∈ H,
        ∃ h₃ ∈ H, ∀ x ∈ V.carrier, h₁ x ≤ h₃ x ∧ h₂ x ≤ h₃ x)
    (hH_locally_bounded :
      ∀ K : Set X, IsCompact K → K ⊆ V.carrier →
        ∃ M : ℝ, ∀ h ∈ H, ∀ x ∈ K, h x ≤ M)
    (hH_pointwise_sSup :
      ∀ x ∈ V.carrier, sSup {a : ℝ | ∃ h ∈ H, a = h x} = P x)
    (_hP_lsc : LowerSemicontinuousOn P V.carrier) :
    IsHarmonicOnSurface V.carrier P := by
  let I := HarmonicMinorantIndex V H
  haveI : Nonempty I := HarmonicMinorantIndex.nonempty hH_nonempty
  haveI : IsDirectedOrder I := HarmonicMinorantIndex.isDirectedOrder hH_directed
  have hconv :
      TendstoLocallyUniformlyOn
        (fun i : I ↦ (i : X → ℝ)) P Filter.atTop V.carrier :=
    harnack_directed_harmonic_minorants_tendstoLocallyUniformlyOn
      V hV_coord P H hH_nonempty hH_harmonic hH_directed
      hH_locally_bounded hH_pointwise_sSup
  have hharm_event :
      ∀ᶠ i : I in Filter.atTop, IsHarmonicOnSurface V.carrier (i : X → ℝ) := by
    exact Filter.Eventually.of_forall (fun i ↦ hH_harmonic i.toFun i.mem)
  exact harmonicOnSurface_of_tendstoLocallyUniformlyOn V.isOpen hharm_event hconv

/--
%%handwave
name:
  Directed harmonic minorants have harmonic supremum on a coordinate disk
statement:
  Let \(P\) be a lower semicontinuous function on a coordinate disk.  Suppose
  \(P\) is the pointwise supremum, up to arbitrary epsilon, of a directed
  family of harmonic functions below \(P\), and suppose that family is locally
  bounded above.  Then \(P\) is harmonic on the disk.
proof:
  First identify \(P\) with the pointwise supremum of the family by
  [epsilon-cofinality](lean:JJMath.Uniformization.directed_harmonic_minorants_pointwise_sSup).
  Then apply the Harnack regularity theorem saying that
  [pointwise suprema of directed locally bounded harmonic families are harmonic](lean:JJMath.Uniformization.pointwise_sSup_directed_harmonic_family_harmonicOn_coordinate_disk).
-/
theorem directed_harmonic_minorants_sup_harmonicOn_coordinate_disk
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (V : PerronDomain X) (hV_coord : IsCoordinatePerronDisk V)
    (P : X → ℝ) (H : Set (X → ℝ))
    (hH_nonempty : H.Nonempty)
    (hH_harmonic : ∀ h ∈ H, IsHarmonicOnSurface V.carrier h)
    (hH_directed :
      ∀ h₁ ∈ H, ∀ h₂ ∈ H,
        ∃ h₃ ∈ H, ∀ x ∈ V.carrier, h₁ x ≤ h₃ x ∧ h₂ x ≤ h₃ x)
    (hH_locally_bounded :
      ∀ K : Set X, IsCompact K → K ⊆ V.carrier →
        ∃ M : ℝ, ∀ h ∈ H, ∀ x ∈ K, h x ≤ M)
    (hH_le_P : ∀ h ∈ H, ∀ x ∈ V.carrier, h x ≤ P x)
    (hH_cofinal :
      ∀ x ∈ V.carrier, ∀ ε : ℝ, 0 < ε →
        ∃ h ∈ H, P x - ε < h x)
    (hP_lsc : LowerSemicontinuousOn P V.carrier) :
    IsHarmonicOnSurface V.carrier P := by
  have hpointwise_sSup :
      ∀ x ∈ V.carrier, sSup {a : ℝ | ∃ h ∈ H, a = h x} = P x := by
    intro x hxV
    exact directed_harmonic_minorants_pointwise_sSup V P H
      hH_nonempty hH_directed hH_le_P hH_cofinal hxV
  exact pointwise_sSup_directed_harmonic_family_harmonicOn_coordinate_disk
    V hV_coord P H hH_nonempty hH_harmonic hH_directed
    hH_locally_bounded hpointwise_sSup hP_lsc

/--
%%handwave
name:
  Directed harmonic majorants have harmonic infimum on a coordinate disk
statement:
  Let \(P\) be an upper semicontinuous function on a coordinate disk.  Suppose
  \(P\) is the pointwise infimum, up to arbitrary epsilon, of a downward
  directed family of harmonic functions above \(P\), and suppose that family
  is locally bounded below.  Then \(P\) is harmonic on the disk.
proof:
  Negate the family.  Downward directed harmonic majorants of \(P\) become
  upward directed harmonic minorants of \(-P\), locally bounded above and
  cofinal below \(-P\).  The already-proved directed-minorant theorem makes
  \(-P\) harmonic, hence \(P\) is harmonic as well.
-/
theorem directed_harmonic_majorants_inf_harmonicOn_coordinate_disk
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (V : PerronDomain X) (hV_coord : IsCoordinatePerronDisk V)
    (P : X → ℝ) (H : Set (X → ℝ))
    (hH_nonempty : H.Nonempty)
    (hH_harmonic : ∀ h ∈ H, IsHarmonicOnSurface V.carrier h)
    (hH_directed :
      ∀ h₁ ∈ H, ∀ h₂ ∈ H,
        ∃ h₃ ∈ H, ∀ x ∈ V.carrier, h₃ x ≤ h₁ x ∧ h₃ x ≤ h₂ x)
    (hH_locally_bounded_below :
      ∀ K : Set X, IsCompact K → K ⊆ V.carrier →
        ∃ M : ℝ, ∀ h ∈ H, ∀ x ∈ K, M ≤ h x)
    (hP_le_H : ∀ h ∈ H, ∀ x ∈ V.carrier, P x ≤ h x)
    (hH_cofinal :
      ∀ x ∈ V.carrier, ∀ ε : ℝ, 0 < ε →
        ∃ h ∈ H, h x < P x + ε)
    (hP_usc : UpperSemicontinuousOn P V.carrier) :
    IsHarmonicOnSurface V.carrier P := by
  let Hneg : Set (X → ℝ) := {g | ∃ h ∈ H, g = fun x ↦ -h x}
  have hHneg_nonempty : Hneg.Nonempty := by
    rcases hH_nonempty with ⟨h, hh⟩
    exact ⟨fun x ↦ -h x, h, hh, rfl⟩
  have hHneg_harmonic : ∀ g ∈ Hneg, IsHarmonicOnSurface V.carrier g := by
    intro g hg
    rcases hg with ⟨h, hh, rfl⟩
    exact harmonicOnSurface_neg (hH_harmonic h hh)
  have hHneg_directed :
      ∀ g₁ ∈ Hneg, ∀ g₂ ∈ Hneg,
        ∃ g₃ ∈ Hneg, ∀ x ∈ V.carrier, g₁ x ≤ g₃ x ∧ g₂ x ≤ g₃ x := by
    intro g₁ hg₁ g₂ hg₂
    rcases hg₁ with ⟨h₁, hh₁, rfl⟩
    rcases hg₂ with ⟨h₂, hh₂, rfl⟩
    rcases hH_directed h₁ hh₁ h₂ hh₂ with ⟨h₃, hh₃, hle⟩
    refine ⟨fun x ↦ -h₃ x, ?_, ?_⟩
    · exact ⟨h₃, hh₃, rfl⟩
    · intro x hxV
      rcases hle x hxV with ⟨h31, h32⟩
      exact ⟨neg_le_neg h31, neg_le_neg h32⟩
  have hHneg_locally_bounded :
      ∀ K : Set X, IsCompact K → K ⊆ V.carrier →
        ∃ M : ℝ, ∀ g ∈ Hneg, ∀ x ∈ K, g x ≤ M := by
    intro K hK hKV
    rcases hH_locally_bounded_below K hK hKV with ⟨M, hM⟩
    refine ⟨-M, ?_⟩
    intro g hg x hxK
    rcases hg with ⟨h, hh, rfl⟩
    exact neg_le_neg (hM h hh x hxK)
  have hHneg_le_negP :
      ∀ g ∈ Hneg, ∀ x ∈ V.carrier, g x ≤ (fun x ↦ -P x) x := by
    intro g hg x hxV
    rcases hg with ⟨h, hh, rfl⟩
    exact neg_le_neg (hP_le_H h hh x hxV)
  have hHneg_cofinal :
      ∀ x ∈ V.carrier, ∀ ε : ℝ, 0 < ε →
        ∃ g ∈ Hneg, (fun x ↦ -P x) x - ε < g x := by
    intro x hxV ε hε
    rcases hH_cofinal x hxV ε hε with ⟨h, hh, hlt⟩
    refine ⟨fun y ↦ -h y, ?_, ?_⟩
    · exact ⟨h, hh, rfl⟩
    · dsimp
      linarith
  have hnegP_lsc : LowerSemicontinuousOn (fun x ↦ -P x) V.carrier := by
    exact hP_usc.neg
  have hneg_harm : IsHarmonicOnSurface V.carrier (fun x ↦ -P x) :=
    directed_harmonic_minorants_sup_harmonicOn_coordinate_disk V hV_coord
      (fun x ↦ -P x) Hneg hHneg_nonempty hHneg_harmonic hHneg_directed
      hHneg_locally_bounded hHneg_le_negP hHneg_cofinal hnegP_lsc
  have hdouble : IsHarmonicOnSurface V.carrier (fun x ↦ -(-P x)) :=
    harmonicOnSurface_neg hneg_harm
  simpa using hdouble

/--
%%handwave
name:
  Abstract Perron lifting principle on a coordinate disk
statement:
  Let \(P\) be the envelope of an abstract Perron family near a coordinate
  disk.  If the family is nonempty, closed under finite maxima, locally
  cofinal below \(P\), and harmonic replacement sends family members to
  family members whose replacements lie between the original function and
  \(P\), then \(P\) is harmonic on the coordinate disk.
proof:
  Form the family of harmonic replacements of admissible functions.  It is
  nonempty, directed by replacing maxima, locally bounded because it lies
  below \(P\), and cofinal below \(P\) because admissible functions are
  cofinal and each replacement dominates the original function.  The directed
  harmonic-minorant theorem then gives harmonicity of \(P\).
-/
theorem abstract_perron_lifting_principle_on_coordinate_disk
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (V : PerronDomain X) (P : X → ℝ) (A : (X → ℝ) → Prop)
    (_hV_coord : IsCoordinatePerronDisk V)
    (hV_preconnected : IsPreconnected V.carrier)
    (hV_frontier_nonempty : (frontier V.carrier).Nonempty)
    (hfamily_nonempty : ∃ v : X → ℝ, A v)
    (hP_locally_bounded :
      ∀ K : Set X, IsCompact K → K ⊆ V.carrier →
        ∃ M : ℝ, ∀ x ∈ K, P x ≤ M)
    (hP_lsc : LowerSemicontinuousOn P V.carrier)
    (hA_sup :
      ∀ u v : X → ℝ, A u → A v → A (fun x ↦ u x ⊔ v x))
    (hA_cofinal :
      ∀ x ∈ V.carrier, ∀ ε : ℝ, 0 < ε →
        ∃ v : X → ℝ, A v ∧ P x - ε < v x)
    (hreplacement_closure :
      ∀ v : X → ℝ, A v →
        ∃ h : X → ℝ,
          IsHarmonicReplacement V v h ∧
            A (harmonicReplacementPatch V v h) ∧
              (∀ x ∈ V.carrier, v x ≤ h x) ∧
                ∀ x ∈ V.carrier, h x ≤ P x) :
    IsHarmonicOnSurface V.carrier P := by
  let H : Set (X → ℝ) :=
    {h | ∃ v : X → ℝ,
      A v ∧
        IsHarmonicReplacement V v h ∧
          (∀ x ∈ V.carrier, v x ≤ h x) ∧
            ∀ x ∈ V.carrier, h x ≤ P x}
  have hH_nonempty : H.Nonempty := by
    rcases hfamily_nonempty with ⟨v, hv⟩
    rcases hreplacement_closure v hv with ⟨h, hh, _hpatch, hdom, hle⟩
    exact ⟨h, v, hv, hh, hdom, hle⟩
  have hH_harmonic : ∀ h ∈ H, IsHarmonicOnSurface V.carrier h := by
    intro h hhmem
    rcases hhmem with ⟨v, hv, hh, hdom, hle⟩
    exact hh.1
  have hH_le_P : ∀ h ∈ H, ∀ x ∈ V.carrier, h x ≤ P x := by
    intro h hhmem
    rcases hhmem with ⟨v, hv, hh, hdom, hle⟩
    exact hle
  have hH_locally_bounded :
      ∀ K : Set X, IsCompact K → K ⊆ V.carrier →
        ∃ M : ℝ, ∀ h ∈ H, ∀ x ∈ K, h x ≤ M := by
    intro K hK hKV
    rcases hP_locally_bounded K hK hKV with ⟨M, hM⟩
    refine ⟨M, ?_⟩
    intro h hhmem x hxK
    exact (hH_le_P h hhmem x (hKV hxK)).trans (hM x hxK)
  have hH_cofinal :
      ∀ x ∈ V.carrier, ∀ ε : ℝ, 0 < ε →
        ∃ h ∈ H, P x - ε < h x := by
    intro x hxV ε hε
    rcases hA_cofinal x hxV ε hε with ⟨v, hv, hvx⟩
    rcases hreplacement_closure v hv with ⟨h, hh, _hpatch, hdom, hle⟩
    refine ⟨h, ?_, hvx.trans_le (hdom x hxV)⟩
    exact ⟨v, hv, hh, hdom, hle⟩
  have hH_directed :
      ∀ h₁ ∈ H, ∀ h₂ ∈ H,
        ∃ h₃ ∈ H, ∀ x ∈ V.carrier, h₁ x ≤ h₃ x ∧ h₂ x ≤ h₃ x := by
    intro h₁ hh₁mem h₂ hh₂mem
    rcases hh₁mem with ⟨v₁, hv₁, hrep₁, _hdom₁, _hle₁⟩
    rcases hh₂mem with ⟨v₂, hv₂, hrep₂, _hdom₂, _hle₂⟩
    let w : X → ℝ := fun x ↦ v₁ x ⊔ v₂ x
    have hw : A w := hA_sup v₁ v₂ hv₁ hv₂
    rcases hreplacement_closure w hw with ⟨h₃, hrep₃, _hpatch₃, hdom₃, hle₃⟩
    have h₁_le_h₃ : ∀ x ∈ V.carrier, h₁ x ≤ h₃ x :=
      harmonicReplacement_le_of_boundary_original_le V hV_preconnected
        hV_frontier_nonempty hrep₁ hrep₃
        (by
          intro x hx
          exact le_sup_left)
    have h₂_le_h₃ : ∀ x ∈ V.carrier, h₂ x ≤ h₃ x :=
      harmonicReplacement_le_of_boundary_original_le V hV_preconnected
        hV_frontier_nonempty hrep₂ hrep₃
        (by
          intro x hx
          exact le_sup_right)
    refine ⟨h₃, ?_, ?_⟩
    · exact ⟨w, hw, hrep₃, hdom₃, hle₃⟩
    · intro x hx
      exact ⟨h₁_le_h₃ x hx, h₂_le_h₃ x hx⟩
  exact directed_harmonic_minorants_sup_harmonicOn_coordinate_disk V
    _hV_coord P H hH_nonempty hH_harmonic hH_directed
    hH_locally_bounded hH_le_P hH_cofinal hP_lsc

/--
%%handwave
name:
  Bounded Perron-open envelope is harmonic on coordinate disks
statement:
  On a coordinate Perron disk compactly contained in a Perron-open region, the
  bounded Perron-open envelope is harmonic.
proof:
  Apply the abstract Perron lifting principle to the bounded admissible
  family.  The fixed upper bound gives local boundedness, finite maxima stay
  in the family, and harmonic replacement preserves bounded admissibility.
-/
theorem boundedPerronOpenEnvelope_harmonicOn_coordinate_disk
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronOpen X) (V : PerronDomain X)
    (φ : PerronOpenBoundaryData Ω) (M : ℝ)
    (hV_coord : IsCoordinatePerronDisk V)
    (hVΩ : closure V.carrier ⊆ Ω.carrier)
    (hV_preconnected : IsPreconnected V.carrier)
    (hV_frontier_nonempty : (frontier V.carrier).Nonempty)
    (hOverlap_geometry :
      ∀ W : Set X,
        IsOpen W →
          IsPreconnected W →
            (frontier W).Nonempty →
              W ⊆ Ω.carrier →
                IsCompact (closure W) →
                  closure W ⊆ Ω.carrier →
                    HasComponentwiseMaximumPrincipleGeometry (W ∩ V.carrier))
    (hfamily_nonempty :
      ∃ v : X → ℝ, IsBoundedPerronOpenAdmissible Ω φ M v) :
    IsHarmonicOnSurface V.carrier (boundedPerronOpenEnvelope Ω φ M) := by
  let A : (X → ℝ) → Prop := IsBoundedPerronOpenAdmissible Ω φ M
  have hP_locally_bounded :
      ∀ K : Set X, IsCompact K → K ⊆ V.carrier →
        ∃ B : ℝ, ∀ x ∈ K, boundedPerronOpenEnvelope Ω φ M x ≤ B := by
    intro K _hK hKV
    refine ⟨M, ?_⟩
    intro x hxK
    exact boundedPerronOpenEnvelope_le_bound Ω φ M hfamily_nonempty
      (hVΩ (subset_closure (hKV hxK)))
  have hP_lsc :
      LowerSemicontinuousOn (boundedPerronOpenEnvelope Ω φ M) V.carrier :=
    (boundedPerronOpenEnvelope_lowerSemicontinuousOn Ω φ M).mono (by
      intro x hxV
      exact hVΩ (subset_closure hxV))
  have hA_sup :
      ∀ u v : X → ℝ, A u → A v → A (fun x ↦ u x ⊔ v x) := by
    intro u v hu hv
    exact boundedPerronOpenAdmissible_sup Ω φ M hu hv
  have hA_cofinal :
      ∀ x ∈ V.carrier, ∀ ε : ℝ, 0 < ε →
        ∃ v : X → ℝ, A v ∧
          boundedPerronOpenEnvelope Ω φ M x - ε < v x := by
    intro x hxV ε hε
    exact exists_boundedPerronOpenAdmissible_envelope_sub_lt Ω φ M
      hfamily_nonempty (hVΩ (subset_closure hxV)) hε
  have hreplacement :
      ∀ v : X → ℝ, A v →
        ∃ h : X → ℝ,
          IsHarmonicReplacement V v h ∧
            A (harmonicReplacementPatch V v h) ∧
              (∀ x ∈ V.carrier, v x ≤ h x) ∧
                ∀ x ∈ V.carrier, h x ≤ boundedPerronOpenEnvelope Ω φ M x := by
    intro v hv
    rcases boundedPerronOpenAdmissible_has_admissible_harmonic_replacement
        Ω V φ M hV_coord hVΩ hV_preconnected hV_frontier_nonempty
        hOverlap_geometry hv with
      ⟨h, hh, hpatch⟩
    refine ⟨h, hh, hpatch, ?_, ?_⟩
    · exact harmonic_replacement_dominates_original_open Ω V φ hVΩ
        hV_preconnected hV_frontier_nonempty hv.1 hh
    · exact harmonicReplacement_le_boundedPerronOpenEnvelope_of_patch_admissible
        Ω V φ M hVΩ hpatch
  exact abstract_perron_lifting_principle_on_coordinate_disk V
    (boundedPerronOpenEnvelope Ω φ M) A hV_coord hV_preconnected
    hV_frontier_nonempty hfamily_nonempty hP_locally_bounded hP_lsc
    hA_sup hA_cofinal hreplacement

/--
%%handwave
name:
  Bounded Perron-open envelope is harmonic
statement:
  If the bounded Perron-open family is nonempty, then its envelope is harmonic
  throughout the Perron-open region.
proof:
  Every point has a compactly contained coordinate Perron disk.  On each such
  disk the bounded Perron-open envelope is harmonic by the coordinate-disk
  lifting theorem, and harmonicity is local.
tags:
  milestone
-/
theorem boundedPerronOpenEnvelope_is_harmonic
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronOpen X) (φ : PerronOpenBoundaryData Ω) (M : ℝ)
    (hfamily_nonempty :
      ∃ v : X → ℝ, IsBoundedPerronOpenAdmissible Ω φ M v) :
    IsHarmonicOnSurface Ω.carrier (boundedPerronOpenEnvelope Ω φ M) := by
  apply harmonicOnSurface_of_locally_harmonic
  intro x hxΩ
  rcases exists_coordinate_perron_disk_compactly_contained_open Ω hxΩ with
    ⟨V, hxV, hV_coord, hVΩ, hV_preconnected, hV_frontier_nonempty⟩
  have hOverlap_geometry :
      ∀ W : Set X,
        IsOpen W →
          IsPreconnected W →
            (frontier W).Nonempty →
              W ⊆ Ω.carrier →
                IsCompact (closure W) →
                  closure W ⊆ Ω.carrier →
                    HasComponentwiseMaximumPrincipleGeometry (W ∩ V.carrier) :=
    coordinate_perron_disk_overlap_geometry_open Ω V hV_coord hVΩ
  have hV_harmonic :
      IsHarmonicOnSurface V.carrier (boundedPerronOpenEnvelope Ω φ M) :=
    boundedPerronOpenEnvelope_harmonicOn_coordinate_disk Ω V φ M
      hV_coord hVΩ hV_preconnected hV_frontier_nonempty hOverlap_geometry
      hfamily_nonempty
  refine ⟨V.carrier, hxV, ?_, hV_harmonic⟩
  intro y hy
  exact hVΩ (subset_closure hy)

/--
%%handwave
name:
  Perron lifting principle on a coordinate disk
statement:
  Suppose a Perron family is nonempty, locally bounded above, has a lower
  semicontinuous envelope, and is closed under harmonic replacement on a
  compactly contained coordinate disk, with each replacement bounded above by
  the Perron envelope.  Then its envelope is harmonic on that disk.
proof:
  This is the intrinsic Perron regularity step.  The directedness lets finite
  maxima approximate the envelope from below at finitely many chosen points.
  Lower semicontinuity is the one-sided regularity available directly from
  the supremum construction.  The lifting argument then harmonically replaces
  these approximants on the disk and uses the local boundedness/compactness
  regularity of harmonic functions to identify the resulting harmonic lifting
  with the envelope.
-/
theorem perron_lifting_principle_on_coordinate_disk
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω V : PerronDomain X) (φ : PerronBoundaryData Ω)
    (_hV_coord : IsCoordinatePerronDisk V)
    (hVΩ : closure V.carrier ⊆ Ω.carrier)
    (hV_preconnected : IsPreconnected V.carrier)
    (hV_frontier_nonempty : (frontier V.carrier).Nonempty)
    (hfamily_nonempty : ∃ v : X → ℝ, IsPerronAdmissible Ω φ v)
    (hfamily_locally_bounded :
      ∀ K : Set X, IsCompact K → K ⊆ Ω.carrier →
        ∃ M : ℝ, ∀ v : X → ℝ, IsPerronAdmissible Ω φ v → ∀ x ∈ K, v x ≤ M)
    (henv_lsc : LowerSemicontinuousOn (perronEnvelope Ω φ) V.carrier)
    (hreplacement_closure :
      ∀ v : X → ℝ, IsPerronAdmissible Ω φ v →
        ∃ h : X → ℝ,
          IsHarmonicReplacement V v h ∧
            IsPerronAdmissible Ω φ (harmonicReplacementPatch V v h) ∧
              ∀ x ∈ V.carrier, h x ≤ perronEnvelope Ω φ x) :
    IsHarmonicOnSurface V.carrier (perronEnvelope Ω φ) := by
  let H : Set (X → ℝ) :=
    {h | ∃ v : X → ℝ,
      IsPerronAdmissible Ω φ v ∧
        IsHarmonicReplacement V v h ∧
          (∀ x ∈ V.carrier, v x ≤ h x) ∧
            ∀ x ∈ V.carrier, h x ≤ perronEnvelope Ω φ x}
  have hH_nonempty : H.Nonempty := by
    rcases hfamily_nonempty with ⟨v, hv⟩
    rcases hreplacement_closure v hv with ⟨h, hh, _hpatch, hle⟩
    have hdom : ∀ x ∈ V.carrier, v x ≤ h x :=
      harmonic_replacement_dominates_original Ω V φ hVΩ hV_preconnected
        hV_frontier_nonempty hv hh
    exact ⟨h, v, hv, hh, hdom, hle⟩
  have hH_harmonic : ∀ h ∈ H, IsHarmonicOnSurface V.carrier h := by
    intro h hhmem
    rcases hhmem with ⟨v, hv, hh, hdom, hle⟩
    exact hh.1
  have hH_le_P : ∀ h ∈ H, ∀ x ∈ V.carrier, h x ≤ perronEnvelope Ω φ x := by
    intro h hhmem
    rcases hhmem with ⟨v, hv, hh, hdom, hle⟩
    exact hle
  have hH_locally_bounded :
      ∀ K : Set X, IsCompact K → K ⊆ V.carrier →
        ∃ M : ℝ, ∀ h ∈ H, ∀ x ∈ K, h x ≤ M := by
    intro K hK hKV
    have hKΩ : K ⊆ Ω.carrier := by
      intro x hx
      exact hVΩ (subset_closure (hKV hx))
    rcases perronEnvelope_locally_bounded_above_of_family_locally_bounded
        Ω φ hfamily_locally_bounded K hK hKΩ with
      ⟨M, hM⟩
    refine ⟨M, ?_⟩
    intro h hhmem x hxK
    exact (hH_le_P h hhmem x (hKV hxK)).trans (hM x hxK)
  have hH_cofinal :
      ∀ x ∈ V.carrier, ∀ ε : ℝ, 0 < ε →
        ∃ h ∈ H, perronEnvelope Ω φ x - ε < h x := by
    intro x hxV ε hε
    have hxΩ : x ∈ Ω.carrier := hVΩ (subset_closure hxV)
    rcases exists_perronAdmissible_envelope_sub_lt Ω φ
        hfamily_locally_bounded hxΩ hε with
      ⟨v, hv, hvx⟩
    rcases hreplacement_closure v hv with ⟨h, hh, _hpatch, hle⟩
    have hdom : ∀ y ∈ V.carrier, v y ≤ h y :=
      harmonic_replacement_dominates_original Ω V φ hVΩ hV_preconnected
        hV_frontier_nonempty hv hh
    refine ⟨h, ?_, hvx.trans_le (hdom x hxV)⟩
    exact ⟨v, hv, hh, hdom, hle⟩
  have hH_directed :
      ∀ h₁ ∈ H, ∀ h₂ ∈ H,
        ∃ h₃ ∈ H, ∀ x ∈ V.carrier, h₁ x ≤ h₃ x ∧ h₂ x ≤ h₃ x := by
    intro h₁ hh₁mem h₂ hh₂mem
    rcases hh₁mem with ⟨v₁, hv₁, hrep₁, _hdom₁, _hle₁⟩
    rcases hh₂mem with ⟨v₂, hv₂, hrep₂, _hdom₂, _hle₂⟩
    let w : X → ℝ := fun x ↦ v₁ x ⊔ v₂ x
    have hw : IsPerronAdmissible Ω φ w :=
      perronAdmissible_sup Ω φ hv₁ hv₂
    rcases hreplacement_closure w hw with ⟨h₃, hrep₃, _hpatch₃, hle₃⟩
    have hdom₃ : ∀ x ∈ V.carrier, w x ≤ h₃ x :=
      harmonic_replacement_dominates_original Ω V φ hVΩ hV_preconnected
        hV_frontier_nonempty hw hrep₃
    have h₁_le_h₃ : ∀ x ∈ V.carrier, h₁ x ≤ h₃ x :=
      harmonicReplacement_le_of_boundary_original_le V hV_preconnected
        hV_frontier_nonempty hrep₁ hrep₃
        (by
          intro x hx
          exact le_sup_left)
    have h₂_le_h₃ : ∀ x ∈ V.carrier, h₂ x ≤ h₃ x :=
      harmonicReplacement_le_of_boundary_original_le V hV_preconnected
        hV_frontier_nonempty hrep₂ hrep₃
        (by
          intro x hx
          exact le_sup_right)
    refine ⟨h₃, ?_, ?_⟩
    · exact ⟨w, hw, hrep₃, hdom₃, hle₃⟩
    · intro x hx
      exact ⟨h₁_le_h₃ x hx, h₂_le_h₃ x hx⟩
  exact directed_harmonic_minorants_sup_harmonicOn_coordinate_disk V
    _hV_coord (perronEnvelope Ω φ) H hH_nonempty hH_harmonic hH_directed
    hH_locally_bounded hH_le_P hH_cofinal henv_lsc

/--
%%handwave
name:
  Perron envelope is harmonic on compactly contained coordinate disks
statement:
  On every compactly contained coordinate Perron disk, the Perron envelope is
  harmonic.
proof:
  The admissible subfunctions are closed under finite maxima, so their values
  are directed, and the envelope is
  [lower semicontinuous](lean:JJMath.Uniformization.perronEnvelope_lowerSemicontinuousOn).
  Harmonic replacement on the coordinate disk stays in the Perron family by
  [the harmonic replacement theorem](lean:JJMath.Uniformization.harmonic_replacement_preserves_admissibility).
  The Perron lifting principle combines these regularity facts to identify
  the envelope with its harmonic lifting on the disk.
-/
theorem perronEnvelope_harmonicOn_coordinate_disk
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω V : PerronDomain X) (φ : PerronBoundaryData Ω)
    (hV_coord : IsCoordinatePerronDisk V)
    (hVΩ : closure V.carrier ⊆ Ω.carrier)
    (hV_preconnected : IsPreconnected V.carrier)
    (hV_frontier_nonempty : (frontier V.carrier).Nonempty)
    (hOverlap_geometry :
      ∀ W : Set X,
        IsOpen W →
          IsPreconnected W →
            (frontier W).Nonempty →
              W ⊆ Ω.carrier →
                IsCompact (closure W) →
                  closure W ⊆ Ω.carrier →
                    HasComponentwiseMaximumPrincipleGeometry (W ∩ V.carrier))
    (hfamily_nonempty : ∃ v : X → ℝ, IsPerronAdmissible Ω φ v)
    (hfamily_locally_bounded :
      ∀ K : Set X, IsCompact K → K ⊆ Ω.carrier →
        ∃ M : ℝ, ∀ v : X → ℝ, IsPerronAdmissible Ω φ v → ∀ x ∈ K, v x ≤ M) :
    IsHarmonicOnSurface V.carrier (perronEnvelope Ω φ) := by
  have hreplacement_closure :
      ∀ v : X → ℝ, IsPerronAdmissible Ω φ v →
        ∃ h : X → ℝ,
          IsHarmonicReplacement V v h ∧
            IsPerronAdmissible Ω φ (harmonicReplacementPatch V v h) ∧
              ∀ x ∈ V.carrier, h x ≤ perronEnvelope Ω φ x := by
    intro v hv
    rcases perronAdmissible_has_admissible_harmonic_replacement Ω V φ
        hV_coord hVΩ hV_preconnected hV_frontier_nonempty
        hOverlap_geometry hv with
      ⟨h, hh, hpatch⟩
    refine ⟨h, hh, hpatch, ?_⟩
    exact harmonicReplacement_le_perronEnvelope_of_patch_admissible Ω V φ
      hVΩ hfamily_locally_bounded hpatch
  have hV_subsetΩ : V.carrier ⊆ Ω.carrier := by
    intro x hx
    exact hVΩ (subset_closure hx)
  have henv_lsc : LowerSemicontinuousOn (perronEnvelope Ω φ) V.carrier :=
    (perronEnvelope_lowerSemicontinuousOn Ω φ hfamily_locally_bounded).mono
      hV_subsetΩ
  exact perron_lifting_principle_on_coordinate_disk Ω V φ hV_coord hVΩ
    hV_preconnected hV_frontier_nonempty hfamily_nonempty
    hfamily_locally_bounded henv_lsc hreplacement_closure

/--
%%handwave
name:
  Perron envelope is harmonic
statement:
  The Perron envelope of continuous boundary data is harmonic inside a regular
  Perron domain.
proof:
  Fix a coordinate disk compactly contained in the domain.  Replace admissible
  functions by their harmonic liftings on that disk; this does not leave the
  Perron family.  The Perron lifting principle uses finite maxima, lower
  semicontinuity, and local boundedness to show that the supremum agrees with
  a harmonic function on the disk.  Since the disk was arbitrary, the envelope
  is harmonic throughout the domain.
-/
theorem perron_envelope_is_harmonic
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronDomain X) (hΩreg : PerronRegularBoundary Ω)
    (φ : PerronBoundaryData Ω) :
    IsHarmonicOnSurface Ω.carrier (perronEnvelope Ω φ) := by
  have hfamily := perron_family_nonempty_and_locally_bounded Ω hΩreg φ
  apply harmonicOnSurface_of_locally_harmonic
  intro x hx
  rcases exists_coordinate_perron_disk_compactly_contained Ω hx with
    ⟨V, hxV, hV_coord, hVΩ, hV_preconnected, hV_frontier_nonempty⟩
  have hOverlap_geometry :
      ∀ W : Set X,
        IsOpen W →
          IsPreconnected W →
            (frontier W).Nonempty →
              W ⊆ Ω.carrier →
                IsCompact (closure W) →
                  closure W ⊆ Ω.carrier →
                    HasComponentwiseMaximumPrincipleGeometry (W ∩ V.carrier) :=
    coordinate_perron_disk_overlap_geometry Ω V hV_coord hVΩ
  have hV_harmonic : IsHarmonicOnSurface V.carrier (perronEnvelope Ω φ) :=
    perronEnvelope_harmonicOn_coordinate_disk Ω V φ hV_coord hVΩ
      hV_preconnected hV_frontier_nonempty hOverlap_geometry hfamily.1 hfamily.2
  refine ⟨V.carrier, hxV, ?_, hV_harmonic⟩
  intro y hy
  exact hVΩ (subset_closure hy)

/--
%%handwave
name:
  Perron barriers give lower boundary estimates
statement:
  At a boundary point admitting a Perron barrier, the Perron envelope is
  eventually greater than every value just below the prescribed boundary
  value.
proof:
  Use continuity of the boundary data near the point and compactness away from
  the point to choose a large multiple of the barrier so that
  \(\varphi(p)-\varepsilon-Cb\) lies below the boundary data everywhere.  This
  function is Perron-admissible, hence lies below the envelope, and the barrier
  term tends to zero at the point.
-/
theorem perronEnvelope_eventually_gt_boundary_sub_of_barrier
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronDomain X) (φ : PerronBoundaryData Ω)
    {p : X} (hΩ_geometry : HasComponentwiseMaximumPrincipleGeometry Ω.carrier)
    (hp : HasPerronBarrierAt Ω p) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in 𝓝[Ω.carrier] p, φ p - ε < perronEnvelope Ω φ x := by
  rcases perronBarrier_lower_subfunction Ω φ hp hε with
    ⟨b, C, hb_cont, hb_zero, _hC, hv⟩
  have hp_frontier : p ∈ frontier Ω.carrier := by
    simpa [PerronDomain.boundary] using hp.1
  have hp_closure : p ∈ closure Ω.carrier :=
    frontier_subset_closure hp_frontier
  have hb_tendsto_closure :
      Filter.Tendsto b (𝓝[closure Ω.carrier] p) (𝓝 (b p)) :=
    hb_cont p hp_closure
  have hb_tendsto :
      Filter.Tendsto b (𝓝[Ω.carrier] p) (𝓝 0) := by
    simpa [hb_zero] using
      (tendsto_nhdsWithin_mono_left subset_closure hb_tendsto_closure)
  have hCb_tendsto :
      Filter.Tendsto (fun x ↦ C * b x) (𝓝[Ω.carrier] p) (𝓝 0) := by
    simpa using (Filter.Tendsto.const_mul C hb_tendsto)
  have hsmall :
      ∀ᶠ x in 𝓝[Ω.carrier] p, C * b x < ε / 2 := by
    exact (tendsto_order.mp hCb_tendsto).2 (ε / 2) (by linarith)
  rcases PerronBoundaryData.exists_upper_bound φ with ⟨M, hM⟩
  have hv_le_envelope :
      ∀ x ∈ Ω.carrier,
        φ p - ε / 2 - C * b x ≤ perronEnvelope Ω φ x := by
    intro x hxΩ
    have hbdd : BddAbove (perronValueSet Ω φ x) :=
      perronValueSet_bddAbove_of_family_bound Ω φ (x := x) (M := M)
        (by
          intro w hw
          exact perron_admissible_le_boundary_upper_bound Ω φ
            hΩ_geometry hM hw x hxΩ)
    exact perronAdmissible_le_perronEnvelope_of_bddAbove Ω φ hv hbdd
  filter_upwards [hsmall, self_mem_nhdsWithin] with x hxsmall hxΩ
  have hbelow : φ p - ε < φ p - ε / 2 - C * b x := by
    linarith
  exact hbelow.trans_le (hv_le_envelope x hxΩ)

/--
%%handwave
name:
  Subharmonic minus superharmonic is subharmonic
statement:
  The difference of a subharmonic function and a superharmonic function is
  subharmonic on the same surface region.
proof:
  Since a superharmonic function has subharmonic negative, this is the
  standard closure of subharmonic functions under addition.  It follows either
  from the distributional characterization, where positive Laplacians are
  closed under addition, or from the equivalent harmonic-measure comparison
  formulation.
-/
theorem subharmonicOnSurface_sub_superharmonic
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    {U : Set X} {u s : X → ℝ}
    (hU_open : IsOpen U)
    (hu : IsSubharmonicOnSurface U u)
    (hs : IsSuperharmonicOnSurface U s) :
    IsSubharmonicOnSurface U (fun x ↦ u x - s x) := by
  have hsum :
      IsSubharmonicOnSurface U (fun x ↦ u x + (-s x)) :=
    subharmonicOnSurface_add hU_open hu hs
  simpa [sub_eq_add_neg] using hsum

/--
%%handwave
name:
  Subharmonic functions compare with superharmonic majorants
statement:
  On a Perron domain with the componentwise maximum-principle geometry, a
  continuous subharmonic function that is bounded by a continuous
  superharmonic function on the boundary is bounded by it throughout the
  domain.
proof:
  Apply the usual comparison principle for the difference \(u-s\): the
  difference of a subharmonic function and a superharmonic function is
  subharmonic, and the boundary inequality makes this difference
  nonpositive.  The componentwise subharmonic maximum principle then gives
  nonpositivity in the domain.
-/
theorem subharmonic_le_superharmonic_of_boundary_le
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronDomain X)
    (hΩ_geometry : HasComponentwiseMaximumPrincipleGeometry Ω.carrier)
    {u s : X → ℝ}
    (hu_cont : ContinuousOn u (closure Ω.carrier))
    (hu_sub : IsSubharmonicOnSurface Ω.carrier u)
    (hs_cont : ContinuousOn s (closure Ω.carrier))
    (hs_super : IsSuperharmonicOnSurface Ω.carrier s)
    (hboundary : ∀ x ∈ Ω.boundary, u x ≤ s x) :
    ∀ x ∈ Ω.carrier, u x ≤ s x := by
  have hdiff_cont : ContinuousOn (fun x ↦ u x - s x) (closure Ω.carrier) :=
    hu_cont.sub hs_cont
  have hdiff_sub : IsSubharmonicOnSurface Ω.carrier (fun x ↦ u x - s x) :=
    subharmonicOnSurface_sub_superharmonic Ω.isOpen hu_sub hs_super
  have hdiff_boundary : ∀ x ∈ Ω.boundary, u x - s x ≤ 0 := by
    intro x hx
    linarith [hboundary x hx]
  have hdiff_nonpos : ∀ x ∈ Ω.carrier, u x - s x ≤ 0 :=
    subharmonic_le_constant_of_boundary_le Ω hΩ_geometry
      hdiff_cont hdiff_sub hdiff_boundary
  intro x hx
  linarith [hdiff_nonpos x hx]

/-- The contact paste used by `subharmonicOnSurface_sup_paste_of_boundary_le`. -/
noncomputable def subharmonicSupPaste
    {X : Type} [TopologicalSpace X] (V : Set X) (u v : X → ℝ) : X → ℝ := by
  classical
  exact fun x ↦ if x ∈ V then u x ⊔ v x else u x

/--
%%handwave
name:
  Subharmonic contact pasting
statement:
  Let $U$ and $V$ be open surface regions.  Suppose $u$ is subharmonic
  on $U$, $v$ is subharmonic on $U\cap V$, and both functions are
  continuous up to the part of the boundary of $V$ lying in $U$.  If
  $v\le u$ there, then the function equal to
  $\max\{u,v\}$ on $V$ and to $u$ off $V$ is subharmonic on $U$.
proof:
  Continuity follows because the boundary inequality makes the maximum equal
  to $u$ on the gluing frontier.  For harmonic comparison, first compare
  $u$ with the test function on the whole test region.  Then compare $v$
  on each component of the intersection with $V$; its new boundary is
  either part of the original test boundary or part of the gluing frontier.
-/
theorem subharmonicOnSurface_sup_paste_of_boundary_le
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    {U V : Set X} {u v : X → ℝ}
    (hV_open : IsOpen V)
    (hu_cont : ContinuousOn u U)
    (hv_cont : ContinuousOn v (U ∩ closure V))
    (hu_sub : IsSubharmonicOnSurface U u)
    (hv_sub : IsSubharmonicOnSurface (U ∩ V) v)
    (hcontact : ∀ x ∈ U ∩ frontier V, v x ≤ u x) :
    IsSubharmonicOnSurface U (subharmonicSupPaste V u v) := by
  classical
  let w : X → ℝ := subharmonicSupPaste V u v
  have hw_cont : ContinuousOn w U := by
    have hin_cont :
        ContinuousOn (fun x : X ↦ u x ⊔ v x) (U ∩ closure V) :=
      (hu_cont.mono Set.inter_subset_left).sup hv_cont
    have hout_cont :
        ContinuousOn u (U ∩ closure {x : X | ¬ x ∈ V}) :=
      hu_cont.mono Set.inter_subset_left
    have hfront :
        ∀ x ∈ U ∩ frontier {x : X | x ∈ V},
          (fun y : X ↦ u y ⊔ v y) x = u x := by
      intro x hx
      have hxfront : x ∈ frontier V := by
        simpa only [Set.setOf_mem_eq] using hx.2
      exact sup_eq_left.mpr (hcontact x ⟨hx.1, hxfront⟩)
    simpa [w, subharmonicSupPaste] using
      ContinuousOn.if hfront hin_cont hout_cont
  refine ⟨hw_cont.upperSemicontinuousOn, ?_⟩
  intro W hW_open hW_preconnected hW_frontier_nonempty hWU hW_compact
    hW_closure h hharmonic hcontinuous hboundary x hxW
  have hu_boundary : ∀ y ∈ frontier W, u y ≤ h y := by
    intro y hy
    have hy_closure : y ∈ closure W := frontier_subset_closure hy
    have hyU : y ∈ U := hW_closure hy_closure
    have hu_le_w : u y ≤ w y := by
      dsimp [w, subharmonicSupPaste]
      by_cases hyV : y ∈ V
      · rw [if_pos hyV]
        exact le_sup_left
      · rw [if_neg hyV]
    exact hu_le_w.trans (hboundary y hy)
  have hu_le : ∀ y ∈ W, u y ≤ h y :=
    hu_sub.2 W hW_open hW_preconnected hW_frontier_nonempty hWU
      hW_compact hW_closure h hharmonic hcontinuous hu_boundary
  by_cases hxV : x ∈ V
  · let P : PerronDomain X :=
      { carrier := W ∩ V
        isOpen := hW_open.inter hV_open
        nonempty := ⟨x, hxW, hxV⟩
        compact_closure :=
          hW_compact.of_isClosed_subset isClosed_closure
            (closure_mono Set.inter_subset_left) }
    have hP_geometry :
        HasComponentwiseMaximumPrincipleGeometry P.carrier := by
      dsimp [P]
      exact hasComponentwiseMaximumPrincipleGeometry_inter_open_of_preconnected
        hW_open hW_preconnected hW_frontier_nonempty hW_compact hV_open
    have hP_subset_UV : P.carrier ⊆ U ∩ V := by
      intro y hy
      exact ⟨hWU hy.1, hy.2⟩
    have hv_sub_P : IsSubharmonicOnSurface P.carrier v :=
      subharmonicOnSurface_mono hP_subset_UV hv_sub
    have hclosureP_subset : closure P.carrier ⊆ U ∩ closure V := by
      intro y hy
      have hy' : y ∈ closure W ∩ closure V := closure_inter_subset hy
      exact ⟨hW_closure hy'.1, hy'.2⟩
    have hv_cont_P : ContinuousOn v (closure P.carrier) :=
      hv_cont.mono hclosureP_subset
    have hh_super_P : IsSuperharmonicOnSurface P.carrier h :=
      harmonicOnSurface_superharmonic P.isOpen
        (harmonicOnSurface_mono Set.inter_subset_left hharmonic)
    have hh_cont_P : ContinuousOn h (closure P.carrier) := by
      exact hcontinuous.mono (closure_mono Set.inter_subset_left)
    have hP_boundary : ∀ y ∈ P.boundary, v y ≤ h y := by
      intro y hy
      have hyfront : y ∈ frontier (W ∩ V) := by
        simpa [P, PerronDomain.boundary] using hy
      rcases frontier_inter_subset W V hyfront with hyW | hyVfront
      · have hyU : y ∈ U :=
          hW_closure (frontier_subset_closure hyW.1)
        have hv_le_w : v y ≤ w y := by
          dsimp [w, subharmonicSupPaste]
          by_cases hy_mem_V : y ∈ V
          · rw [if_pos hy_mem_V]
            exact le_sup_right
          · have hy_frontier_V : y ∈ frontier V := by
              rw [frontier_eq_closure_inter_closure]
              exact ⟨hyW.2, subset_closure hy_mem_V⟩
            rw [if_neg hy_mem_V]
            exact hcontact y ⟨hyU, hy_frontier_V⟩
        exact hv_le_w.trans (hboundary y hyW.1)
      · have hyU : y ∈ U := hW_closure hyVfront.1
        have hv_le_u : v y ≤ u y :=
          hcontact y ⟨hyU, hyVfront.2⟩
        have hu_le_h : u y ≤ h y :=
          le_on_closure hu_le
            (hu_cont.mono hW_closure) hcontinuous hyVfront.1
        exact hv_le_u.trans hu_le_h
    have hv_le_h : ∀ y ∈ P.carrier, v y ≤ h y :=
      subharmonic_le_superharmonic_of_boundary_le P hP_geometry
        hv_cont_P hv_sub_P hh_cont_P hh_super_P hP_boundary
    have hux : u x ≤ h x := hu_le x hxW
    have hvx : v x ≤ h x := hv_le_h x ⟨hxW, hxV⟩
    simpa [w, subharmonicSupPaste, hxV] using sup_le hux hvx
  · simpa [w, subharmonicSupPaste, hxV] using hu_le x hxW

/-- The contact paste used by `superharmonicOnSurface_inf_paste_of_boundary_le`. -/
noncomputable def superharmonicInfPaste
    {X : Type} [TopologicalSpace X] (V : Set X) (u v : X → ℝ) : X → ℝ := by
  classical
  exact fun x ↦ if x ∈ V then u x ⊓ v x else u x

/--
%%handwave
name:
  Continuity of minimum contact pasting
statement:
  Suppose $u$ is continuous on a region $U$, $v$ is continuous up to the
  part of the frontier of an open region $V$ lying in $U$, and $u\le v$ on
  that frontier.  Then the function equal to $\min\{u,v\}$ on $V$ and to
  $u$ off $V$ is continuous on $U$.
proof:
  On the gluing frontier the assumed inequality makes the minimum equal to
  $u$, so the ordinary pasting lemma for continuous functions applies.
-/
theorem continuousOn_superharmonicInfPaste_of_boundary_le
    {X : Type} [TopologicalSpace X]
    {U V : Set X} {u v : X → ℝ}
    (hu_cont : ContinuousOn u U)
    (hv_cont : ContinuousOn v (U ∩ closure V))
    (hcontact : ∀ x ∈ U ∩ frontier V, u x ≤ v x) :
    ContinuousOn (superharmonicInfPaste V u v) U := by
  classical
  have hin_cont :
      ContinuousOn (fun x : X ↦ u x ⊓ v x) (U ∩ closure V) :=
    (hu_cont.mono Set.inter_subset_left).inf hv_cont
  have hout_cont :
      ContinuousOn u (U ∩ closure {x : X | ¬ x ∈ V}) :=
    hu_cont.mono Set.inter_subset_left
  have hfront :
      ∀ x ∈ U ∩ frontier {x : X | x ∈ V},
        (fun y : X ↦ u y ⊓ v y) x = u x := by
    intro x hx
    have hxfront : x ∈ frontier V := by
      simpa only [Set.setOf_mem_eq] using hx.2
    exact inf_eq_left.mpr (hcontact x ⟨hx.1, hxfront⟩)
  simpa [superharmonicInfPaste] using
    ContinuousOn.if hfront hin_cont hout_cont

/--
%%handwave
name:
  Superharmonic contact pasting
statement:
  Let $U$ and $V$ be open surface regions.  Suppose $u$ is superharmonic
  on $U$, $v$ is superharmonic on $U\cap V$, and both functions are
  continuous up to the part of the boundary of $V$ lying in $U$.  If
  $u\le v$ there, then the function equal to
  $\min\{u,v\}$ on $V$ and to $u$ off $V$ is superharmonic on $U$.
proof:
  Negate both functions and apply subharmonic contact pasting.  Negation
  exchanges minima with maxima and reverses the contact inequality.
-/
theorem superharmonicOnSurface_inf_paste_of_boundary_le
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    {U V : Set X} {u v : X → ℝ}
    (hV_open : IsOpen V)
    (hu_cont : ContinuousOn u U)
    (hv_cont : ContinuousOn v (U ∩ closure V))
    (hu_super : IsSuperharmonicOnSurface U u)
    (hv_super : IsSuperharmonicOnSurface (U ∩ V) v)
    (hcontact : ∀ x ∈ U ∩ frontier V, u x ≤ v x) :
    IsSuperharmonicOnSurface U (superharmonicInfPaste V u v) := by
  have hneg :=
    subharmonicOnSurface_sup_paste_of_boundary_le hV_open
      hu_cont.neg hv_cont.neg hu_super hv_super
      (fun x hx ↦ neg_le_neg (hcontact x hx))
  have hpaste :
      subharmonicSupPaste V (fun x ↦ -u x) (fun x ↦ -v x) =
        fun x ↦ -superharmonicInfPaste V u v x := by
    funext x
    classical
    by_cases hx : x ∈ V <;>
      simp [subharmonicSupPaste, superharmonicInfPaste, hx, neg_inf]
  change IsSubharmonicOnSurface U (fun x ↦ -superharmonicInfPaste V u v x)
  rw [← hpaste]
  exact hneg

/--
%%handwave
name:
  Affine negative barriers compare below harmonic functions
statement:
  On a Perron domain with the componentwise maximum-principle geometry, an
  affine function \(A-CB\), where \(C\ge0\) and \(B\) is superharmonic, lies
  below a harmonic function throughout the domain if it lies below it on the
  boundary.
proof:
  Since \(B\) is superharmonic, \(-B\) is subharmonic, and multiplying by
  \(C\ge0\) and adding the constant \(A\) preserves subharmonicity.  The
  harmonic function is superharmonic, so the subharmonic-superharmonic
  comparison principle applies.
-/
theorem affine_neg_superharmonic_le_harmonic_of_boundary_le
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronDomain X)
    (hΩ_geometry : HasComponentwiseMaximumPrincipleGeometry Ω.carrier)
    {B u : X → ℝ} {A C : ℝ}
    (hC : 0 ≤ C)
    (hB_cont : ContinuousOn B (closure Ω.carrier))
    (hB_super : IsSuperharmonicOnSurface Ω.carrier B)
    (hu_cont : ContinuousOn u (closure Ω.carrier))
    (hu_harmonic : IsHarmonicOnSurface Ω.carrier u)
    (hboundary : ∀ x ∈ Ω.boundary, A - C * B x ≤ u x) :
    ∀ x ∈ Ω.carrier, A - C * B x ≤ u x := by
  let v : X → ℝ := fun x ↦ A - C * B x
  have hv_cont : ContinuousOn v (closure Ω.carrier) :=
    continuousOn_const.sub (continuousOn_const.mul hB_cont)
  have hv_sub : IsSubharmonicOnSurface Ω.carrier v := by
    have hscaled :
        IsSubharmonicOnSurface Ω.carrier (fun x ↦ C * (-B x)) :=
      subharmonicOnSurface_const_mul_nonneg hC hB_super
    have hshifted :
        IsSubharmonicOnSurface Ω.carrier
          (fun x ↦ A + C * (-B x)) :=
      subharmonicOnSurface_const_add A hscaled
    simpa [v, sub_eq_add_neg, mul_neg] using hshifted
  have hu_super : IsSuperharmonicOnSurface Ω.carrier u :=
    harmonicOnSurface_superharmonic Ω.isOpen hu_harmonic
  exact
    subharmonic_le_superharmonic_of_boundary_le Ω hΩ_geometry
      hv_cont hv_sub hu_cont hu_super hboundary

/--
%%handwave
name:
  Local upper barrier family bound for bounded Perron-open subfunctions
statement:
  At a boundary point admitting a local Perron-open barrier, every bounded
  Perron-open admissible subfunction is locally bounded above by an affine
  superharmonic barrier \( \varphi(p)+\varepsilon/2+CB\), where \(B\) tends to
  zero at \(p\).
proof:
  Choose a compactly contained coordinate shrink of the local barrier
  neighborhood.  On the true boundary near \(p\), continuity of the boundary
  data gives \(v\le \varphi\le \varphi(p)+\varepsilon/2\).  On the artificial
  boundary of the shrink, the fixed bound \(v\le M\) and the positive frontier
  floor of the barrier determine \(C\).  The maximum principle on the shrink
  compares \(v\) with the affine superharmonic barrier.
-/
theorem boundedPerronOpenBarrier_upper_family_bound_of_local_barrier
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexOneManifold X]
    (Ω : PerronOpen X) (φ : PerronOpenBoundaryData Ω) (M : ℝ)
    {p : X} (hp : HasLocalPerronOpenBarrierAt Ω p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ B : X → ℝ, ∃ C : ℝ,
      0 ≤ C ∧
        Filter.Tendsto B (𝓝[Ω.carrier] p) (𝓝 0) ∧
          ∀ᶠ x in 𝓝[Ω.carrier] p,
            ∀ v : X → ℝ, IsBoundedPerronOpenAdmissible Ω φ M v →
              v x ≤ φ p + ε / 2 + C * B x := by
  let A : ℝ := φ p + ε / 2
  have hnear_lt :
      ∀ᶠ x in 𝓝[Ω.boundary] p, φ x < A := by
    simpa [A] using
      perronOpenBoundaryData_eventually_lt_boundary_add φ hp.1
        (by linarith : 0 < ε / 2)
  have hnear_le :
      {x : X | φ x ≤ A} ∈ 𝓝[Ω.boundary] p :=
    hnear_lt.mono (fun _ hx ↦ le_of_lt hx)
  rcases mem_nhdsWithin.mp hnear_le with
    ⟨U, hU_open, hpU, hU_boundary⟩
  rcases hp with
    ⟨hp_boundary, N, hN_open, hpN, b, hb_cont, hb_super, hb_zero, hb_pos⟩
  have hNU_open : IsOpen (N ∩ U) := hN_open.inter hU_open
  have hpNU : p ∈ N ∩ U := ⟨hpN, hpU⟩
  rcases exists_surface_open_nhds_isCompact_closure_subset hNU_open hpNU with
    ⟨O, hO_open, hpO, hO_closure_subset_NU, hO_compact⟩
  let Odom : PerronDomain X :=
    { carrier := O
      isOpen := hO_open
      nonempty := ⟨p, hpO⟩
      compact_closure := hO_compact }
  rcases exists_coordinate_perron_disk_compactly_contained Odom hpO with
    ⟨V, hpV, _hV_coord, hV_subset_O, hV_preconnected,
      hV_frontier_nonempty⟩
  have hV_closure_subset_NU : closure V.carrier ⊆ N ∩ U := by
    intro x hx
    exact hO_closure_subset_NU (subset_closure (hV_subset_O hx))
  have hV_closure_subset_N : closure V.carrier ⊆ N := by
    intro x hx
    exact (hV_closure_subset_NU hx).1
  have hV_closure_subset_U : closure V.carrier ⊆ U := by
    intro x hx
    exact (hV_closure_subset_NU hx).2
  rcases localPerronOpenBarrier_positive_floor_on_frontier Ω hb_cont hb_pos
      V.isOpen hpV V.compact_closure hV_closure_subset_N with
    ⟨δ, hδpos, hδ_floor⟩
  let C : ℝ := max 0 ((M - A) / δ)
  have hC_nonneg : 0 ≤ C := le_max_left 0 ((M - A) / δ)
  have hgap_le_Cδ : M - A ≤ C * δ := by
    have hdiv_le_C : (M - A) / δ ≤ C := le_max_right 0 ((M - A) / δ)
    calc
      M - A = ((M - A) / δ) * δ := by
        exact (div_mul_cancel₀ (M - A) hδpos.ne').symm
      _ ≤ C * δ := mul_le_mul_of_nonneg_right hdiv_le_C hδpos.le
  have hp_closure : p ∈ closure Ω.carrier :=
    frontier_subset_closure hp_boundary
  have hb_tendsto :
      Filter.Tendsto b (𝓝[Ω.carrier] p) (𝓝 0) :=
    localPerronOpenBarrier_tendsto_zero Ω hN_open hpN hp_closure
      hb_cont hb_zero
  have hV_mem_nhdsWithin : V.carrier ∈ 𝓝[Ω.carrier] p :=
    mem_nhdsWithin_of_mem_nhds (V.isOpen.mem_nhds hpV)
  refine ⟨b, C, hC_nonneg, hb_tendsto, ?_⟩
  filter_upwards [hV_mem_nhdsWithin, self_mem_nhdsWithin] with x hxV hxΩ
  intro v hv
  let D : PerronDomain X :=
    { carrier := Ω.carrier ∩ V.carrier
      isOpen := Ω.isOpen.inter V.isOpen
      nonempty := by
        rcases mem_closure_iff_nhds.mp hp_closure V.carrier
            (V.isOpen.mem_nhds hpV) with ⟨y, hyV, hyΩ⟩
        exact ⟨y, hyΩ, hyV⟩
      compact_closure := by
        exact V.compact_closure.of_isClosed_subset isClosed_closure
          (closure_mono
            (Set.inter_subset_right : Ω.carrier ∩ V.carrier ⊆ V.carrier)) }
  have hxD : x ∈ D.carrier := ⟨hxΩ, hxV⟩
  have hD_geometry :
      HasComponentwiseMaximumPrincipleGeometry D.carrier := by
    have hgeom :
        HasComponentwiseMaximumPrincipleGeometry
          (V.carrier ∩ Ω.carrier) :=
      hasComponentwiseMaximumPrincipleGeometry_inter_open_of_preconnected
        V.isOpen hV_preconnected hV_frontier_nonempty V.compact_closure
        Ω.isOpen
    simpa [D, Set.inter_comm] using hgeom
  have hD_closure_subset_closureΩ :
      closure D.carrier ⊆ closure Ω.carrier := by
    exact closure_mono
      (show Ω.carrier ∩ V.carrier ⊆ Ω.carrier from Set.inter_subset_left)
  have hD_closure_subset_N :
      closure D.carrier ⊆ N := by
    intro y hy
    have hyV_closure : y ∈ closure V.carrier :=
      closure_mono
        (show Ω.carrier ∩ V.carrier ⊆ V.carrier from Set.inter_subset_right)
        hy
    exact hV_closure_subset_N hyV_closure
  have hD_closure_subset_closedN :
      closure D.carrier ⊆ closure Ω.carrier ∩ N := by
    intro y hy
    exact ⟨hD_closure_subset_closureΩ hy, hD_closure_subset_N hy⟩
  have hv_cont_D : ContinuousOn v (closure D.carrier) :=
    hv.1.1.mono hD_closure_subset_closureΩ
  have hv_sub_D : IsSubharmonicOnSurface D.carrier v := by
    exact subharmonicOnSurface_mono
      (show D.carrier ⊆ Ω.carrier from Set.inter_subset_left) hv.1.2.1
  let s : X → ℝ := fun y ↦ A + C * b y
  have hb_cont_D : ContinuousOn b (closure D.carrier) :=
    hb_cont.mono hD_closure_subset_closedN
  have hs_cont_D : ContinuousOn s (closure D.carrier) :=
    continuousOn_const.add (continuousOn_const.mul hb_cont_D)
  have hb_super_D : IsSuperharmonicOnSurface D.carrier b := by
    exact superharmonicOnSurface_mono
      (show D.carrier ⊆ Ω.carrier ∩ N from by
        intro y hy
        exact ⟨hy.1, hV_closure_subset_N (subset_closure hy.2)⟩)
      hb_super
  have hs_super_D : IsSuperharmonicOnSurface D.carrier s := by
    have hscaled : IsSuperharmonicOnSurface D.carrier (fun y ↦ C * b y) :=
      superharmonicOnSurface_const_mul_nonneg hC_nonneg hb_super_D
    simpa [s] using superharmonicOnSurface_const_add A hscaled
  have hboundary : ∀ y ∈ D.boundary, v y ≤ s y := by
    intro y hyD_boundary
    have hy_frontier : y ∈ frontier (Ω.carrier ∩ V.carrier) := by
      simpa [PerronDomain.boundary, D] using hyD_boundary
    rcases frontier_inter_subset Ω.carrier V.carrier hy_frontier with
      hΩpart | hVpart
    · rcases hΩpart with ⟨hyΩ_frontier, hyV_closure⟩
      have hyΩ_boundary : y ∈ Ω.boundary := hyΩ_frontier
      have hyU : y ∈ U := hV_closure_subset_U hyV_closure
      have hφ_le_A : φ y ≤ A := hU_boundary ⟨hyU, hyΩ_boundary⟩
      have hy_closureΩ : y ∈ closure Ω.carrier :=
        frontier_subset_closure hyΩ_frontier
      have hb_nonneg : 0 ≤ b y := by
        by_cases hyp : y = p
        · simp [hyp, hb_zero]
        · exact le_of_lt
            (hb_pos y ⟨hy_closureΩ, hV_closure_subset_N hyV_closure⟩ hyp)
      have hscaled_nonneg : 0 ≤ C * b y :=
        mul_nonneg hC_nonneg hb_nonneg
      have hv_boundary : v y ≤ φ y := hv.1.2.2 y hyΩ_boundary
      dsimp [s, A] at hφ_le_A ⊢
      linarith
    · rcases hVpart with ⟨hyΩ_closure, hyV_frontier⟩
      by_cases hyΩ : y ∈ Ω.carrier
      · have hv_bound : v y ≤ M := hv.2 y hyΩ
        have hδ_le : δ ≤ b y :=
          hδ_floor y ⟨hyΩ_closure, hyV_frontier⟩
        have hCδ_le_Cb : C * δ ≤ C * b y :=
          mul_le_mul_of_nonneg_left hδ_le hC_nonneg
        have hM_le : M ≤ A + C * b y := by
          linarith
        dsimp [s]
        linarith
      · have hyΩ_frontier : y ∈ frontier Ω.carrier := by
          rw [Ω.isOpen.frontier_eq]
          exact ⟨hyΩ_closure, hyΩ⟩
        have hyΩ_boundary : y ∈ Ω.boundary := hyΩ_frontier
        have hyV_closure : y ∈ closure V.carrier :=
          frontier_subset_closure hyV_frontier
        have hyU : y ∈ U := hV_closure_subset_U hyV_closure
        have hφ_le_A : φ y ≤ A := hU_boundary ⟨hyU, hyΩ_boundary⟩
        have hb_nonneg : 0 ≤ b y := by
          by_cases hyp : y = p
          · simp [hyp, hb_zero]
          · exact le_of_lt
              (hb_pos y ⟨hyΩ_closure, hV_closure_subset_N hyV_closure⟩ hyp)
        have hscaled_nonneg : 0 ≤ C * b y :=
          mul_nonneg hC_nonneg hb_nonneg
        have hv_boundary : v y ≤ φ y := hv.1.2.2 y hyΩ_boundary
        dsimp [s, A] at hφ_le_A ⊢
        linarith
  exact subharmonic_le_superharmonic_of_boundary_le D hD_geometry
    hv_cont_D hv_sub_D hs_cont_D hs_super_D hboundary x hxD

/--
%%handwave
name:
  Bounded Perron-open barriers give upper boundary estimates
statement:
  At a boundary point admitting a local Perron-open barrier, the bounded
  Perron-open envelope is eventually less than \(\varphi(p)+\varepsilon\) for
  every positive \(\varepsilon\).
proof:
  Shrink the barrier neighborhood so that the boundary data is below
  \(\varphi(p)+\varepsilon/2\) on the nearby boundary.  On the artificial
  boundary of the shrink, positivity of the barrier and the fixed upper bound
  \(M\) allow a multiple of the barrier to dominate every bounded admissible
  subfunction.  The maximum principle compares each subfunction with
  \(\varphi(p)+\varepsilon/2+Cb\) in the shrink, and the barrier tends to
  zero at \(p\).
-/
theorem boundedPerronOpenEnvelope_eventually_lt_boundary_add_of_local_barrier
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexOneManifold X]
    (Ω : PerronOpen X) (φ : PerronOpenBoundaryData Ω) (M : ℝ)
    (hfamily_nonempty :
      ∃ v : X → ℝ, IsBoundedPerronOpenAdmissible Ω φ M v)
    {p : X} (hp : HasLocalPerronOpenBarrierAt Ω p)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in 𝓝[Ω.carrier] p,
      boundedPerronOpenEnvelope Ω φ M x < φ p + ε := by
  rcases boundedPerronOpenBarrier_upper_family_bound_of_local_barrier
      Ω φ M hp hε with
    ⟨B, C, _hC_nonneg, hB_tendsto, hfamily_bound⟩
  have hCB_tendsto :
      Filter.Tendsto (fun x ↦ C * B x) (𝓝[Ω.carrier] p) (𝓝 0) := by
    simpa using (Filter.Tendsto.const_mul C hB_tendsto)
  have hsmall :
      ∀ᶠ x in 𝓝[Ω.carrier] p, C * B x < ε / 2 := by
    exact (tendsto_order.mp hCB_tendsto).2 (ε / 2) (by linarith)
  filter_upwards [hfamily_bound, hsmall] with x hbound_x hsmall_x
  have hne : (boundedPerronOpenValueSet Ω φ M x).Nonempty :=
    boundedPerronOpenValueSet_nonempty_of_family_nonempty Ω φ M
      hfamily_nonempty x
  have henv_le :
      boundedPerronOpenEnvelope Ω φ M x ≤ φ p + ε / 2 + C * B x :=
    boundedPerronOpenEnvelope_le_of_family_bound Ω φ M hne hbound_x
  linarith

/--
%%handwave
name:
  Subharmonic comparison with a superharmonic barrier
statement:
  If \(v\) is Perron-admissible, \(b\) is a nonnegative superharmonic barrier,
  and \(v\le A+Cb\) on the boundary with \(C\ge0\), then
  \(v\le A+Cb\) throughout the domain.
proof:
  The function \(v-Cb-A\) is subharmonic: \(v\) is subharmonic and \(-b\) is
  subharmonic because \(b\) is superharmonic.  The boundary inequality says
  this subharmonic function is nonpositive on the boundary.  The componentwise
  maximum principle then gives nonpositivity in the domain.
-/
theorem perronAdmissible_le_const_add_barrier_of_boundary_le
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronDomain X) (φ : PerronBoundaryData Ω)
    (hΩ_geometry : HasComponentwiseMaximumPrincipleGeometry Ω.carrier)
    {v b : X → ℝ} {A C : ℝ}
    (hv : IsPerronAdmissible Ω φ v)
    (hb_cont : ContinuousOn b (closure Ω.carrier))
    (hb_super : IsSuperharmonicOnSurface Ω.carrier b)
    (hC : 0 ≤ C)
    (hboundary : ∀ x ∈ Ω.boundary, v x ≤ A + C * b x) :
    ∀ x ∈ Ω.carrier, v x ≤ A + C * b x := by
  let s : X → ℝ := fun x ↦ A + C * b x
  have hs_cont : ContinuousOn s (closure Ω.carrier) :=
    continuousOn_const.add (continuousOn_const.mul hb_cont)
  have hs_super : IsSuperharmonicOnSurface Ω.carrier s := by
    have hscaled :
        IsSubharmonicOnSurface Ω.carrier (fun x ↦ C * (-b x)) :=
      subharmonicOnSurface_const_mul_nonneg hC hb_super
    have hshifted :
        IsSubharmonicOnSurface Ω.carrier
          (fun x ↦ (-A) + C * (-b x)) :=
      subharmonicOnSurface_const_add (-A) hscaled
    simpa [IsSuperharmonicOnSurface, s, neg_add, mul_neg, sub_eq_add_neg, add_comm] using
      hshifted
  exact subharmonic_le_superharmonic_of_boundary_le Ω hΩ_geometry
    hv.1 hv.2.1 hs_cont hs_super hboundary

/--
%%handwave
name:
  Upper barrier family bound
statement:
  If \(b\) is a Perron barrier at \(p\), then for every \(\varepsilon>0\)
  there is a nonnegative constant \(C\) such that every Perron-admissible
  subfunction \(v\) satisfies
  \(v\le \varphi(p)+\varepsilon/2+Cb\) throughout the domain.
proof:
  Near \(p\), continuity of the boundary data gives
  \(\varphi\le \varphi(p)+\varepsilon/2\).  Away from \(p\), compactness and
  positivity of the barrier let one choose \(C\) so that
  \(v-Cb\le \varphi(p)+\varepsilon/2\) on the boundary for every admissible
  \(v\).  Since \(v-Cb\) is subharmonic and the right side is constant, the
  componentwise maximum principle gives the same inequality in the interior.
-/
theorem perronBarrier_upper_family_bound
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronDomain X) (φ : PerronBoundaryData Ω)
    (hΩ_geometry : HasComponentwiseMaximumPrincipleGeometry Ω.carrier)
    {p : X} (hp : HasPerronBarrierAt Ω p) {ε : ℝ} (hε : 0 < ε) :
    ∃ b : X → ℝ, ∃ C : ℝ,
      ContinuousOn b (closure Ω.carrier) ∧
        b p = 0 ∧
          0 ≤ C ∧
            ∀ v : X → ℝ, IsPerronAdmissible Ω φ v →
              ∀ x ∈ Ω.carrier, v x ≤ φ p + ε / 2 + C * b x := by
  rcases hp with
    ⟨hp_boundary, b, hb_cont, hb_super, hb_zero, hb_pos⟩
  rcases perronBarrier_upper_boundary_calibration Ω φ hp_boundary
      hb_cont hb_super hb_zero hb_pos hε with
    ⟨C, hC, hboundaryφ⟩
  refine ⟨b, C, hb_cont, hb_zero, hC, ?_⟩
  intro v hv x hxΩ
  exact perronAdmissible_le_const_add_barrier_of_boundary_le Ω φ
    hΩ_geometry hv hb_cont hb_super hC
    (by
      intro y hy
      exact (hv.2.2 y hy).trans (hboundaryφ y hy)) x hxΩ

/--
%%handwave
name:
  Perron barriers give upper boundary estimates
statement:
  At a boundary point admitting a Perron barrier, the Perron envelope is
  eventually less than every value just above the prescribed boundary value.
proof:
  Use continuity of the boundary data near the point and compactness away from
  the point to choose a large multiple of the barrier so that every
  Perron-admissible subfunction \(v\) satisfies \(v-Cb\le \varphi(p)+\varepsilon\)
  on the boundary.  The maximum principle gives the same inequality in the
  domain.  Taking the supremum over \(v\), and then using that the barrier term
  tends to zero at the point, gives the upper estimate.
-/
theorem perronEnvelope_eventually_lt_boundary_add_of_barrier
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronDomain X) (φ : PerronBoundaryData Ω)
    {p : X} (hΩ_geometry : HasComponentwiseMaximumPrincipleGeometry Ω.carrier)
    (hp : HasPerronBarrierAt Ω p) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in 𝓝[Ω.carrier] p, perronEnvelope Ω φ x < φ p + ε := by
  rcases perronBarrier_upper_family_bound Ω φ hΩ_geometry hp hε with
    ⟨b, C, hb_cont, hb_zero, _hC, hfamily_bound⟩
  have hp_frontier : p ∈ frontier Ω.carrier := by
    simpa [PerronDomain.boundary] using hp.1
  have hp_closure : p ∈ closure Ω.carrier :=
    frontier_subset_closure hp_frontier
  have hb_tendsto_closure :
      Filter.Tendsto b (𝓝[closure Ω.carrier] p) (𝓝 (b p)) :=
    hb_cont p hp_closure
  have hb_tendsto :
      Filter.Tendsto b (𝓝[Ω.carrier] p) (𝓝 0) := by
    simpa [hb_zero] using
      (tendsto_nhdsWithin_mono_left subset_closure hb_tendsto_closure)
  have hCb_tendsto :
      Filter.Tendsto (fun x ↦ C * b x) (𝓝[Ω.carrier] p) (𝓝 0) := by
    simpa using (Filter.Tendsto.const_mul C hb_tendsto)
  have hsmall :
      ∀ᶠ x in 𝓝[Ω.carrier] p, C * b x < ε / 2 := by
    exact (tendsto_order.mp hCb_tendsto).2 (ε / 2) (by linarith)
  have henv_bound :
      ∀ x ∈ Ω.carrier,
        perronEnvelope Ω φ x ≤ φ p + ε / 2 + C * b x := by
    intro x hxΩ
    exact perronEnvelope_le_of_family_bound Ω φ
      (perronValueSet_nonempty Ω φ x)
      (by
        intro v hv
        exact hfamily_bound v hv x hxΩ)
  filter_upwards [hsmall, self_mem_nhdsWithin] with x hxsmall hxΩ
  have hle := henv_bound x hxΩ
  linarith

/--
%%handwave
name:
  Perron barriers recover boundary values
statement:
  At a boundary point admitting a barrier, the Perron envelope tends to the
  prescribed continuous boundary value.
proof:
  The lower and upper barrier estimates say that, for every \(\varepsilon>0\),
  the envelope is eventually between \(\varphi(p)-\varepsilon\) and
  \(\varphi(p)+\varepsilon\) along the domain.  This is exactly convergence to
  \(\varphi(p)\) in the order topology on the real line.
-/
theorem perron_envelope_tends_to_boundary_value
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronDomain X) (φ : PerronBoundaryData Ω)
    {p : X} (hΩ_geometry : HasComponentwiseMaximumPrincipleGeometry Ω.carrier)
    (hp : HasPerronBarrierAt Ω p) :
    Filter.Tendsto (perronEnvelope Ω φ) (𝓝[Ω.carrier] p) (𝓝 (φ p)) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    have hε : 0 < φ p - a := by linarith
    filter_upwards [
      perronEnvelope_eventually_gt_boundary_sub_of_barrier Ω φ hΩ_geometry hp hε
    ] with x hx
    simpa [sub_sub_cancel] using hx
  · intro a ha
    have hε : 0 < a - φ p := by linarith
    filter_upwards [
      perronEnvelope_eventually_lt_boundary_add_of_barrier Ω φ hΩ_geometry hp hε
    ] with x hx
    simpa [add_sub_cancel] using hx

/--
%%handwave
name:
  Perron candidate is harmonic in the domain
statement:
  If the Perron envelope is harmonic inside the domain, then the Perron
  Dirichlet candidate is harmonic inside the domain.
proof:
  In the interior, the candidate agrees locally with the envelope.
-/
theorem perronDirichletCandidate_harmonicOn
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronDomain X) (φ : PerronBoundaryData Ω)
    (hharm : IsHarmonicOnSurface Ω.carrier (perronEnvelope Ω φ)) :
    IsHarmonicOnSurface Ω.carrier (perronDirichletCandidate Ω φ) := by
  intro e he
  have hbase := hharm e he
  intro z hz
  have hopen : IsOpen (e.target ∩ e.symm ⁻¹' Ω.carrier) :=
    e.isOpen_inter_preimage_symm Ω.isOpen
  have heq :
      (fun y : ℂ ↦ perronEnvelope Ω φ (e.symm y)) =ᶠ[𝓝 z]
        (fun y : ℂ ↦ perronDirichletCandidate Ω φ (e.symm y)) := by
    filter_upwards [hopen.mem_nhds hz] with y hy
    exact (perronDirichletCandidate_eq_envelope_of_mem Ω φ hy.2).symm
  exact (InnerProductSpace.harmonicAt_congr_nhds heq).1 (hbase z hz)

/--
%%handwave
name:
  Perron candidate is continuous on the closed domain
statement:
  If the Perron envelope is harmonic in the domain and tends to the prescribed
  boundary value at every boundary point, then the Perron Dirichlet candidate
  is continuous on the closed domain.
proof:
  Interior continuity follows from
  [harmonic functions are continuous on surface regions](lean:JJMath.Uniformization.harmonicOnSurface_continuousOn).  At a
  boundary point, the candidate is equal to the boundary data on the boundary
  side and has the prescribed limit from inside the domain; continuity of the
  boundary data combines these two one-sided controls on the closed domain.
-/
theorem perronDirichletCandidate_continuousOn_closedDomain
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronDomain X) (φ : PerronBoundaryData Ω)
    (hharm : IsHarmonicOnSurface Ω.carrier (perronEnvelope Ω φ))
    (hboundary :
      ∀ p ∈ Ω.boundary,
        Filter.Tendsto (perronEnvelope Ω φ) (𝓝[Ω.carrier] p) (𝓝 (φ p))) :
    ContinuousOn (perronDirichletCandidate Ω φ) (closure Ω.carrier) := by
  classical
  have henv_cont : ContinuousOn (perronEnvelope Ω φ) Ω.carrier :=
    harmonicOnSurface_continuousOn Ω.isOpen hharm
  intro x hxcl
  change
    Filter.Tendsto (perronDirichletCandidate Ω φ)
      (𝓝[closure Ω.carrier] x)
      (𝓝 (perronDirichletCandidate Ω φ x))
  by_cases hxΩ : x ∈ Ω.carrier
  · have hx_nhds : Ω.carrier ∈ 𝓝 x := Ω.isOpen.mem_nhds hxΩ
    have henv_at : ContinuousAt (perronEnvelope Ω φ) x :=
      henv_cont.continuousAt hx_nhds
    have heq :
        perronDirichletCandidate Ω φ =ᶠ[𝓝[closure Ω.carrier] x]
          perronEnvelope Ω φ := by
      filter_upwards [
        (show Ω.carrier ∈ 𝓝[closure Ω.carrier] x from
          Filter.mem_inf_of_left hx_nhds)
      ] with y hy
      exact perronDirichletCandidate_eq_envelope_of_mem Ω φ hy
    have htendsto :
        Filter.Tendsto (perronEnvelope Ω φ) (𝓝[closure Ω.carrier] x)
          (𝓝 (perronEnvelope Ω φ x)) :=
      henv_at.continuousWithinAt
    have hx_candidate :
        perronDirichletCandidate Ω φ x = perronEnvelope Ω φ x :=
      perronDirichletCandidate_eq_envelope_of_mem Ω φ hxΩ
    simpa [hx_candidate] using
      (Filter.Tendsto.congr' heq.symm htendsto)
  · have hx_boundary : x ∈ Ω.boundary := by
      rw [PerronDomain.boundary, Ω.isOpen.frontier_eq]
      exact ⟨hxcl, hxΩ⟩
    have hx_candidate : perronDirichletCandidate Ω φ x = φ x :=
      perronDirichletCandidate_eq_boundaryData_of_not_mem Ω φ hxΩ
    have hinside_eq :
        perronDirichletCandidate Ω φ =ᶠ[𝓝[Ω.carrier] x]
          perronEnvelope Ω φ := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact perronDirichletCandidate_eq_envelope_of_mem Ω φ hy
    have hinside :
        Filter.Tendsto (perronDirichletCandidate Ω φ) (𝓝[Ω.carrier] x)
          (𝓝 (φ x)) :=
      Filter.Tendsto.congr' hinside_eq.symm (hboundary x hx_boundary)
    have hboundary_eq :
        perronDirichletCandidate Ω φ =ᶠ[𝓝[Ω.boundary] x] (φ : X → ℝ) := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact perronDirichletCandidate_eq_boundaryData_of_not_mem Ω φ
        (Ω.not_mem_carrier_of_mem_boundary hy)
    have hboundary_tendsto :
        Filter.Tendsto (perronDirichletCandidate Ω φ) (𝓝[Ω.boundary] x)
          (𝓝 (φ x)) :=
      Filter.Tendsto.congr' hboundary_eq.symm
        (φ.continuous_boundary.continuousWithinAt hx_boundary)
    have hclosed_union : closure Ω.carrier = Ω.carrier ∪ Ω.boundary := by
      rw [PerronDomain.boundary, closure_eq_self_union_frontier]
    have hpiece :
        Filter.Tendsto (perronDirichletCandidate Ω φ)
          (𝓝[Ω.carrier ∪ Ω.boundary] x) (𝓝 (φ x)) := by
      rw [nhdsWithin_union]
      exact hinside.sup hboundary_tendsto
    rw [hclosed_union]
    simpa [hx_candidate] using hpiece

/--
%%handwave
name:
  Perron candidate has the prescribed boundary values
statement:
  The Perron Dirichlet candidate agrees with the prescribed boundary data on
  the boundary of the domain.
proof:
  Boundary points do not belong to the open domain, so the exterior branch
  of the candidate's definition applies.
-/
theorem perronDirichletCandidate_boundary_eq
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : PerronDomain X) (φ : PerronBoundaryData Ω) :
    ∀ x ∈ Ω.boundary, perronDirichletCandidate Ω φ x = φ x := by
  intro x hx
  exact perronDirichletCandidate_eq_boundaryData_of_not_mem Ω φ
    (Ω.not_mem_carrier_of_mem_boundary hx)

/--
%%handwave
name:
  Perron candidate solves the Dirichlet problem
statement:
  On a Perron domain with regular boundary, the Perron Dirichlet candidate
  formed from the envelope solves the harmonic Dirichlet problem for every
  continuous boundary value.
proof:
  [The Perron envelope is harmonic](lean:JJMath.Uniformization.perron_envelope_is_harmonic)
  in the interior.  [Perron barriers recover boundary values](lean:JJMath.Uniformization.perron_envelope_tends_to_boundary_value)
  at each boundary point.  Together with the interior continuity of harmonic
  functions and the boundary continuity supplied by the barriers, this gives a
  continuous solution on the closed domain.
tags:
  milestone
-/
theorem perron_envelope_solves_dirichlet
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronDomain X) (hΩreg : PerronRegularBoundary Ω)
    (φ : PerronBoundaryData Ω) :
    SolvesHarmonicDirichletProblem Ω φ (perronDirichletCandidate Ω φ) := by
  have hharm : IsHarmonicOnSurface Ω.carrier (perronEnvelope Ω φ) :=
    perron_envelope_is_harmonic Ω hΩreg φ
  refine ⟨?_, ?_, ?_⟩
  · exact perronDirichletCandidate_harmonicOn Ω φ hharm
  · exact perronDirichletCandidate_continuousOn_closedDomain Ω φ hharm
      (fun p hp ↦ perron_envelope_tends_to_boundary_value Ω φ hΩreg.1
        (hΩreg.2 p hp))
  · exact perronDirichletCandidate_boundary_eq Ω φ

/--
%%handwave
name:
  Logarithmic distance in a chart is harmonic
statement:
  On a region contained in one complex chart and avoiding a fixed plane
  point, the logarithm of the Euclidean distance to that point is harmonic as
  a surface function.
proof:
  In every other chart, the function is the logarithm of the norm of the
  holomorphic transition map minus the fixed point.  Since the center is
  avoided, this is harmonic by the standard logarithmic-potential theorem.
-/
theorem coordinateLogDistance_harmonicOnSurface
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    {U : Set X} {c : ℂ}
    (hU_source : U ⊆ e.source)
    (havoid : ∀ x ∈ U, e x ≠ c) :
    IsHarmonicOnSurface U (fun x : X ↦ Real.log ‖e x - c‖) := by
  intro f hf z hz
  have hztarget : z ∈ f.target := hz.1
  have hxU : f.symm z ∈ U := hz.2
  have hxsource : f.symm z ∈ e.source := hU_source hxU
  have htransition :
      AnalyticAt ℂ (fun w : ℂ ↦ e (f.symm w)) z :=
    chartTransition_analyticAt f hf e he hztarget hxsource
  have hsub :
      AnalyticAt ℂ (fun w : ℂ ↦ e (f.symm w) - c) z := by
    simpa [Pi.sub_apply] using
      htransition.sub (analyticAt_const (𝕜 := ℂ) (x := z) (v := c))
  have hnonzero : e (f.symm z) - c ≠ 0 :=
    sub_ne_zero.mpr (havoid (f.symm z) hxU)
  simpa using hsub.harmonicAt_log_norm hnonzero

/--
%%handwave
name:
  Exterior tangent disks give local Perron barriers
statement:
  Suppose a boundary point has a coordinate neighborhood whose closed local
  domain lies outside a Euclidean disk and touches that disk only at the
  boundary point.  Then the logarithmic potential of the disk is a local
  Perron barrier.
proof:
  The barrier is \(x\mapsto \log |e(x)-c|-\log R\).  The exterior-disk
  inequalities make it continuous up to the local closed domain, zero at the
  touching point, and positive at every other local closed-domain point.
  [Logarithmic distance in the chart is harmonic](lean:JJMath.Uniformization.coordinateLogDistance_harmonicOnSurface),
  hence superharmonic, in the local interior.
-/
theorem exteriorTangentDisk_logPotential_has_local_perron_barrier
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronDomain X) {p : X}
    (hp : p ∈ Ω.boundary)
    {e : OpenPartialHomeomorph X ℂ} (he : e ∈ atlas ℂ X)
    {N : Set X} {c : ℂ} {R : ℝ}
    (hN_open : IsOpen N) (hpN : p ∈ N)
    (hN_source : N ⊆ e.source)
    (hRpos : 0 < R)
    (houtside : ∀ x ∈ closure Ω.carrier ∩ N, R ≤ ‖e x - c‖)
    (htangent :
      ∀ x ∈ closure Ω.carrier ∩ N, ‖e x - c‖ = R ↔ x = p) :
    HasLocalPerronBarrierAt Ω p := by
  let U : Set X := Ω.carrier ∩ N
  let S : Set X := closure Ω.carrier ∩ N
  let b : X → ℝ := fun x ↦ Real.log ‖e x - c‖ - Real.log R
  have hp_frontier : p ∈ frontier Ω.carrier := by
    simpa [PerronDomain.boundary] using hp
  have hp_closure : p ∈ closure Ω.carrier :=
    frontier_subset_closure hp_frontier
  have hpS : p ∈ S := ⟨hp_closure, hpN⟩
  have hp_norm : ‖e p - c‖ = R :=
    (htangent p hpS).2 rfl
  have hS_source : S ⊆ e.source := fun x hx ↦ hN_source hx.2
  have hU_source : U ⊆ e.source := fun x hx ↦ hN_source hx.2
  have hU_open : IsOpen U := Ω.isOpen.inter hN_open
  have havoid_U : ∀ x ∈ U, e x ≠ c := by
    intro x hx
    have hxS : x ∈ S := ⟨subset_closure hx.1, hx.2⟩
    have hnorm_pos : 0 < ‖e x - c‖ :=
      lt_of_lt_of_le hRpos (houtside x hxS)
    exact sub_ne_zero.mp (norm_pos_iff.mp hnorm_pos)
  refine ⟨hp, N, hN_open, hpN, b, ?_, ?_, ?_, ?_⟩
  · have he_cont : ContinuousOn e S :=
      e.continuousOn.mono hS_source
    have hdist_cont : ContinuousOn (fun x : X ↦ ‖e x - c‖) S :=
      (he_cont.sub continuousOn_const).norm
    have hdist_ne : ∀ x ∈ S, ‖e x - c‖ ≠ 0 := by
      intro x hx
      exact ne_of_gt (lt_of_lt_of_le hRpos (houtside x hx))
    have hlog_cont :
        ContinuousOn (fun x : X ↦ Real.log ‖e x - c‖) S :=
      hdist_cont.log hdist_ne
    simpa [S, b] using hlog_cont.sub continuousOn_const
  · have hlog_harm :
        IsHarmonicOnSurface U (fun x : X ↦ Real.log ‖e x - c‖) :=
      coordinateLogDistance_harmonicOnSurface e he hU_source havoid_U
    have hb_harm : IsHarmonicOnSurface U b := by
      simpa [b] using
        harmonicOnSurface_sub hlog_harm
          (harmonicOnSurface_const U (Real.log R))
    simpa [U] using harmonicOnSurface_superharmonic hU_open hb_harm
  · simp [b, hp_norm]
  · intro x hxS hxp
    have hle : R ≤ ‖e x - c‖ := houtside x hxS
    have hne : R ≠ ‖e x - c‖ := by
      intro hRnorm
      exact hxp ((htangent x hxS).1 hRnorm.symm)
    have hlt : R < ‖e x - c‖ := lt_of_le_of_ne hle hne
    exact sub_pos.mpr (Real.log_lt_log hRpos hlt)

/--
%%handwave
name:
  Exterior tangent disks give local Perron-open barriers
statement:
  Suppose a boundary point of a Perron open region has a coordinate
  neighborhood whose local closed region lies outside a Euclidean disk and
  touches that disk only at the boundary point.  Then the logarithmic
  potential of the disk is a local Perron-open barrier.
proof:
  The proof is the same explicit logarithmic-potential construction as for
  relatively compact Perron domains.  The barrier is
  \(x\mapsto \log |e(x)-c|-\log R\).  The exterior-disk inequalities give
  continuity, vanishing, and strict positivity, while
  [logarithmic distance in the chart is harmonic](lean:JJMath.Uniformization.coordinateLogDistance_harmonicOnSurface).
-/
theorem exteriorTangentDisk_logPotential_has_local_perronOpen_barrier
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronOpen X) {p : X}
    (hp : p ∈ Ω.boundary)
    {e : OpenPartialHomeomorph X ℂ} (he : e ∈ atlas ℂ X)
    {N : Set X} {c : ℂ} {R : ℝ}
    (hN_open : IsOpen N) (hpN : p ∈ N)
    (hN_source : N ⊆ e.source)
    (hRpos : 0 < R)
    (houtside : ∀ x ∈ closure Ω.carrier ∩ N, R ≤ ‖e x - c‖)
    (htangent :
      ∀ x ∈ closure Ω.carrier ∩ N, ‖e x - c‖ = R ↔ x = p) :
    HasLocalPerronOpenBarrierAt Ω p := by
  let U : Set X := Ω.carrier ∩ N
  let S : Set X := closure Ω.carrier ∩ N
  let b : X → ℝ := fun x ↦ Real.log ‖e x - c‖ - Real.log R
  have hp_frontier : p ∈ frontier Ω.carrier := by
    simpa [PerronOpen.boundary] using hp
  have hp_closure : p ∈ closure Ω.carrier :=
    frontier_subset_closure hp_frontier
  have hpS : p ∈ S := ⟨hp_closure, hpN⟩
  have hp_norm : ‖e p - c‖ = R :=
    (htangent p hpS).2 rfl
  have hS_source : S ⊆ e.source := fun x hx ↦ hN_source hx.2
  have hU_source : U ⊆ e.source := fun x hx ↦ hN_source hx.2
  have hU_open : IsOpen U := Ω.isOpen.inter hN_open
  have havoid_U : ∀ x ∈ U, e x ≠ c := by
    intro x hx
    have hxS : x ∈ S := ⟨subset_closure hx.1, hx.2⟩
    have hnorm_pos : 0 < ‖e x - c‖ :=
      lt_of_lt_of_le hRpos (houtside x hxS)
    exact sub_ne_zero.mp (norm_pos_iff.mp hnorm_pos)
  refine ⟨hp, N, hN_open, hpN, b, ?_, ?_, ?_, ?_⟩
  · have he_cont : ContinuousOn e S :=
      e.continuousOn.mono hS_source
    have hdist_cont : ContinuousOn (fun x : X ↦ ‖e x - c‖) S :=
      (he_cont.sub continuousOn_const).norm
    have hdist_ne : ∀ x ∈ S, ‖e x - c‖ ≠ 0 := by
      intro x hx
      exact ne_of_gt (lt_of_lt_of_le hRpos (houtside x hx))
    have hlog_cont :
        ContinuousOn (fun x : X ↦ Real.log ‖e x - c‖) S :=
      hdist_cont.log hdist_ne
    simpa [S, b] using hlog_cont.sub continuousOn_const
  · have hlog_harm :
        IsHarmonicOnSurface U (fun x : X ↦ Real.log ‖e x - c‖) :=
      coordinateLogDistance_harmonicOnSurface e he hU_source havoid_U
    have hb_harm : IsHarmonicOnSurface U b := by
      simpa [b] using
        harmonicOnSurface_sub hlog_harm
          (harmonicOnSurface_const U (Real.log R))
    simpa [U] using harmonicOnSurface_superharmonic hU_open hb_harm
  · simp [b, hp_norm]
  · intro x hxS hxp
    have hle : R ≤ ‖e x - c‖ := houtside x hxS
    have hne : R ≠ ‖e x - c‖ := by
      intro hRnorm
      exact hxp ((htangent x hxS).1 hRnorm.symm)
    have hlt : R < ‖e x - c‖ := lt_of_le_of_ne hle hne
    exact sub_pos.mpr (Real.log_lt_log hRpos hlt)

/--
%%handwave
name:
  Exterior circles support quadratically bounded graphs
statement:
  If a point lies below a quadratic graph \(y\le A x^2\), and the circle
  radius \(R\) is small enough that \(2RA\le 1/2\), then the circle centered
  at height \(R\) above the origin gives a quadratic lower bound for squared
  distance.
proof:
  Expanding the squared distance to \((0,R)\), the desired inequality reduces
  to controlling the cross term \(2Ry\).  If \(y\le0\), this term has the
  favorable sign.  If \(y\ge0\), the quadratic graph bound and
  \(2RA\le1/2\) absorb it into the \(x^2\) term.
-/
theorem exteriorCircle_quadraticSupport_of_graphBound
    {A R x y : ℝ}
    (hR_nonneg : 0 ≤ R)
    (hRA : 2 * R * A ≤ 1 / 2)
    (hy : y ≤ A * x ^ 2) :
    R ^ 2 + (1 / 4) * (x ^ 2 + y ^ 2) ≤ x ^ 2 + (y - R) ^ 2 := by
  by_cases hy_nonneg : 0 ≤ y
  · have htwoR_nonneg : 0 ≤ 2 * R := by nlinarith
    have hcross₁ : 2 * R * y ≤ 2 * R * (A * x ^ 2) :=
      mul_le_mul_of_nonneg_left hy htwoR_nonneg
    have hcross₂ : 2 * R * (A * x ^ 2) ≤ (1 / 2) * x ^ 2 := by
      have hx2_nonneg : 0 ≤ x ^ 2 := sq_nonneg x
      nlinarith [mul_le_mul_of_nonneg_right hRA hx2_nonneg]
    nlinarith [sq_nonneg x, sq_nonneg y, hcross₁, hcross₂]
  · have hy_nonpos : y ≤ 0 := le_of_not_ge hy_nonneg
    have hminus : 0 ≤ -2 * R * y := by
      have hneg_y : 0 ≤ -y := neg_nonneg.mpr hy_nonpos
      nlinarith [mul_nonneg hR_nonneg hneg_y]
    nlinarith [sq_nonneg x, sq_nonneg y, hminus]

/--
%%handwave
name:
  Quadratically bounded graph sublevels have quadratic exterior support
statement:
  If a graph \(y=\varphi(x)\) is locally bounded above by \(Ax^2\), then
  the sublevel side \(y\le\varphi(x)\) has quadratic exterior support from a
  sufficiently small circle centered on the positive \(y\)-axis.
proof:
  Work in the vertical strip where the graph bound holds and take the circle
  centered at \(iR\).  The sublevel inequality gives \(y\le Ax^2\), and then
  [the elementary exterior-circle estimate](lean:JJMath.Uniformization.exteriorCircle_quadraticSupport_of_graphBound)
  gives the required squared-distance bound.
-/
theorem quadraticGraphSublevel_has_quadraticExteriorSupport
    {φ : ℝ → ℝ} {A ρ R : ℝ}
    (hρpos : 0 < ρ) (hRpos : 0 < R)
    (hRA : 2 * R * A ≤ 1 / 2)
    (hφ_bound : ∀ x : ℝ, |x| < ρ → φ x ≤ A * x ^ 2) :
    ∃ W : Set ℂ, ∃ c : ℂ, ∃ R : ℝ, ∃ κ : ℝ,
      IsOpen W ∧ (0 : ℂ) ∈ W ∧ 0 < R ∧ 0 < κ ∧
        ‖(0 : ℂ) - c‖ = R ∧
          ∀ z ∈ W, z.im - φ z.re ≤ 0 →
            R ^ 2 + κ * ‖z - (0 : ℂ)‖ ^ 2 ≤ ‖z - c‖ ^ 2 := by
  let W : Set ℂ := {z : ℂ | |z.re| < ρ}
  let c : ℂ := (R : ℂ) * Complex.I
  refine ⟨W, c, R, (1 / 4 : ℝ), ?_, ?_, hRpos, by norm_num, ?_, ?_⟩
  · exact isOpen_lt (Complex.continuous_re.abs) continuous_const
  · simp [W, hρpos]
  · have hR_nonneg : 0 ≤ R := le_of_lt hRpos
    simp [c, Real.norm_of_nonneg hR_nonneg]
  · intro z hzW hz_sublevel
    have hy_graph : z.im ≤ A * z.re ^ 2 := by
      have hφz : φ z.re ≤ A * z.re ^ 2 := hφ_bound z.re hzW
      linarith
    have halg :
        R ^ 2 + (1 / 4 : ℝ) * (z.re ^ 2 + z.im ^ 2) ≤
          z.re ^ 2 + (z.im - R) ^ 2 :=
      exteriorCircle_quadraticSupport_of_graphBound
        (le_of_lt hRpos) hRA hy_graph
    rw [Complex.sq_norm (z - (0 : ℂ)), Complex.sq_norm (z - c)]
    simpa [c, Complex.normSq_apply, pow_two] using halg

/--
%%handwave
name:
  A circle radius can be chosen small enough for a quadratic graph
statement:
  For every real quadratic coefficient, there is a positive circle radius for
  which the exterior-circle estimate applies.
proof:
  If the coefficient is nonpositive, any positive radius works.  If it is
  positive, take a sufficiently small reciprocal multiple.
-/
theorem exists_positive_radius_for_exteriorCircle (A : ℝ) :
    ∃ R : ℝ, 0 < R ∧ 2 * R * A ≤ 1 / 2 := by
  by_cases hA : A ≤ 0
  · refine ⟨1, by norm_num, ?_⟩
    nlinarith
  · have hApos : 0 < A := lt_of_not_ge hA
    refine ⟨1 / (8 * A), ?_, ?_⟩
    · positivity
    · have hA_ne : A ≠ 0 := ne_of_gt hApos
      field_simp [hA_ne]
      nlinarith

/--
%%handwave
name:
  A real linear functional on the plane is determined by its coordinate values
statement:
  A real continuous linear functional on the complex plane is
  \(\ell(1)\operatorname{Re} z+\ell(i)\operatorname{Im} z\).
proof:
  Decompose \(z\) as \(\operatorname{Re} z+\operatorname{Im} z\,i\) and use
  real linearity.
-/
theorem realLinearFunctional_apply_eq_re_im (ℓ : ℂ →L[ℝ] ℝ) (z : ℂ) :
    ℓ z = ℓ 1 * z.re + ℓ Complex.I * z.im := by
  have hreal_apply : ℓ (z.re : ℂ) = z.re * ℓ 1 := by
    have h : (z.re : ℂ) = (z.re : ℝ) • (1 : ℂ) := by
      simp
    rw [h, map_smul]
    rfl
  have him_apply : ℓ (z.im * Complex.I) = z.im * ℓ Complex.I := by
    have h : z.im * Complex.I = (z.im : ℝ) • Complex.I := by
      simp
    rw [h, map_smul]
    rfl
  calc
    ℓ z = ℓ ((z.re : ℂ) + z.im * Complex.I) := by
      rw [Complex.re_add_im]
    _ = ℓ (z.re : ℂ) + ℓ (z.im * Complex.I) := by
      rw [map_add]
    _ = z.re * ℓ 1 + z.im * ℓ Complex.I := by
      rw [hreal_apply, him_apply]
    _ = ℓ 1 * z.re + ℓ Complex.I * z.im := by
      ring

/--
%%handwave
name:
  A nonzero real differential has adapted orthonormal coordinates
statement:
  Every nonzero real continuous linear functional on the complex plane can be
  made into a positive multiple of the vertical coordinate after an orthonormal
  real-linear change of coordinates.
proof:
  Write the functional as \(a x+b y\).  Since it is nonzero,
  \(L=\sqrt{a^2+b^2}\) is positive.  Rotate by the unit complex number
  \(b/L+(a/L)i\); in the inverse rotated coordinates the functional becomes
  \(L y\).
-/
theorem realLinearFunctional_has_adapted_isometry
    (dr : ℂ →L[ℝ] ℝ) (hdr_nonzero : dr ≠ 0) :
    ∃ T : ℂ ≃ₗᵢ[ℝ] ℂ, ∃ L : ℝ,
      0 < L ∧ ∀ w : ℂ, dr (T.symm w) = L * w.im := by
  let a : ℝ := dr 1
  let b : ℝ := dr Complex.I
  let L : ℝ := Real.sqrt (a ^ 2 + b ^ 2)
  have hab_ne : a ^ 2 + b ^ 2 ≠ 0 := by
    intro hsum
    have ha : a = 0 := by
      nlinarith [sq_nonneg a, sq_nonneg b]
    have hb : b = 0 := by
      nlinarith [sq_nonneg a, sq_nonneg b]
    apply hdr_nonzero
    ext z
    rw [realLinearFunctional_apply_eq_re_im]
    simp [a, b, ha, hb]
  have hab_nonneg : 0 ≤ a ^ 2 + b ^ 2 :=
    add_nonneg (sq_nonneg a) (sq_nonneg b)
  have hLpos : 0 < L :=
    Real.sqrt_pos.2 (lt_of_le_of_ne hab_nonneg (Ne.symm hab_ne))
  have hLsq : L ^ 2 = a ^ 2 + b ^ 2 := by
    dsimp [L]
    rw [Real.sq_sqrt hab_nonneg]
  let p : ℂ := ((b / L : ℝ) : ℂ) + ((a / L : ℝ) : ℂ) * Complex.I
  have hp_norm : ‖p‖ = 1 := by
    have hnormsq : Complex.normSq p = 1 := by
      rw [Complex.normSq_apply]
      simp [p, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
      field_simp [hLpos.ne]
      nlinarith
    have hnormsq2 : ‖p‖ ^ 2 = 1 := by
      rw [← Complex.normSq_eq_norm_sq]
      exact hnormsq
    have hnorm_nonneg : 0 ≤ ‖p‖ := norm_nonneg _
    nlinarith
  let q : Circle := ⟨p, by simp [Submonoid.unitSphere, hp_norm]⟩
  refine ⟨rotation q, L, hLpos, ?_⟩
  intro w
  have hp_normSq : Complex.normSq p = 1 := by
    rw [Complex.normSq_apply]
    simp [p, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
    field_simp [hLpos.ne]
    nlinarith
  rw [realLinearFunctional_apply_eq_re_im]
  simp only [rotation_symm, rotation_apply]
  dsimp [q]
  rw [Complex.mul_re, Complex.mul_im, Complex.inv_re, Complex.inv_im, hp_normSq]
  simp [p, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, a, b]
  field_simp [hLpos.ne]
  ring_nf
  rw [hLsq]
  ring

/--
%%handwave
name:
  A smooth real graph with zero tangent has a quadratic upper bound
statement:
  If a smooth real function vanishes at the origin and has derivative zero
  there, then after shrinking it is bounded above by \(A x^2\).
proof:
  Use Taylor's theorem to second order.  Smoothness gives a locally bounded
  second derivative, and the zero value and zero first derivative remove the
  constant and linear terms.
-/
theorem smoothRealFunction_tangent_zero_has_quadratic_upper_bound
    {φ : ℝ → ℝ}
    (hφ_smooth : ContDiffAt ℝ ∞ φ 0)
    (hφ_zero : φ 0 = 0)
    (hφ_deriv : HasDerivAt φ 0 0) :
    ∃ A ρ : ℝ, 0 < ρ ∧
      ∀ x : ℝ, |x| < ρ → φ x ≤ A * x ^ 2 := by
  rcases hφ_smooth.contDiffOn (m := (2 : WithTop ℕ∞))
      (by
        change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
        exact WithTop.coe_le_coe.mpr le_top)
      (by simp) with
    ⟨u, hu_nhds, hu_smooth⟩
  rcases Metric.mem_nhds_iff.mp hu_nhds with ⟨ε, hεpos, hεsub⟩
  let ρ₀ : ℝ := ε / 2
  have hρ₀pos : 0 < ρ₀ := by
    dsimp [ρ₀]
    positivity
  let s : Set ℝ := Set.Icc (-ρ₀) ρ₀
  have hρ₀_lt_ε : ρ₀ < ε := by
    dsimp [ρ₀]
    exact half_lt_self hεpos
  have hs_sub_u : s ⊆ u := by
    intro y hy
    apply hεsub
    rw [Metric.mem_ball, Real.dist_eq]
    have hy_abs : |y| ≤ ρ₀ := abs_le.mpr hy
    have : |y - 0| < ε := by
      simpa using lt_of_le_of_lt hy_abs hρ₀_lt_ε
    simpa using this
  have hleft_lt_right : -ρ₀ < ρ₀ := by nlinarith [hρ₀pos]
  have h0s : (0 : ℝ) ∈ s := by
    dsimp [s]
    constructor <;> nlinarith [hρ₀pos]
  have hsmooth_s : ContDiffOn ℝ (2 : WithTop ℕ∞) φ s := hu_smooth.mono hs_sub_u
  have hudiff : UniqueDiffOn ℝ s := by
    dsimp [s]
    exact uniqueDiffOn_Icc hleft_lt_right
  have hderivWithin : derivWithin φ s 0 = 0 := by
    rw [hφ_deriv.differentiableAt.derivWithin (hudiff.uniqueDiffWithinAt h0s), hφ_deriv.deriv]
  let D : ℝ := (2 : ℝ)⁻¹ * iteratedDerivWithin 2 φ s 0
  have htaylor_eval : ∀ x : ℝ, taylorWithinEval φ 2 s 0 x = D * x ^ 2 := by
    intro x
    rw [taylor_within_apply]
    simp [hφ_zero, hderivWithin, D, Finset.sum_range_succ, pow_succ]
    ring
  have htaylor := taylor_isLittleO (f := φ) (x₀ := (0 : ℝ)) (n := 2) (s := s)
    (convex_Icc (-ρ₀) ρ₀) h0s hsmooth_s
  have hremWithin : ∀ᶠ x in 𝓝[s] (0 : ℝ),
      ‖φ x - taylorWithinEval φ 2 s 0 x‖ ≤ (1 : ℝ) * ‖(x - 0) ^ 2‖ :=
    htaylor.def zero_lt_one
  have hremN : ∀ᶠ x in 𝓝 (0 : ℝ), x ∈ s →
      ‖φ x - taylorWithinEval φ 2 s 0 x‖ ≤ (1 : ℝ) * ‖(x - 0) ^ 2‖ :=
    eventually_nhdsWithin_iff.mp hremWithin
  rcases Metric.eventually_nhds_iff.mp hremN with ⟨δ, hδpos, hδ⟩
  refine ⟨|D| + 1, min ρ₀ δ, lt_min hρ₀pos hδpos, ?_⟩
  intro x hx
  have hxρ₀ : |x| < ρ₀ := lt_of_lt_of_le hx (min_le_left ρ₀ δ)
  have hxδ : |x| < δ := lt_of_lt_of_le hx (min_le_right ρ₀ δ)
  have hxs : x ∈ s := by
    dsimp [s]
    exact abs_le.mp (le_of_lt hxρ₀)
  have hrem := hδ (by simpa [Real.dist_eq] using hxδ) hxs
  rw [htaylor_eval x] at hrem
  have hrem_abs : |φ x - D * x ^ 2| ≤ x ^ 2 := by
    simpa [Real.norm_eq_abs, abs_pow, abs_of_nonneg (sq_nonneg x)] using hrem
  have hmain : φ x ≤ D * x ^ 2 + x ^ 2 := by
    have := le_abs_self (φ x - D * x ^ 2)
    linarith
  have hDle : D * x ^ 2 ≤ |D| * x ^ 2 := by
    exact mul_le_mul_of_nonneg_right (le_abs_self D) (sq_nonneg x)
  calc
    φ x ≤ D * x ^ 2 + x ^ 2 := hmain
    _ ≤ |D| * x ^ 2 + x ^ 2 := by linarith
    _ = (|D| + 1) * x ^ 2 := by ring

/--
%%handwave
name:
  A centered vertical differential gives a local implicit zero graph
statement:
  If a smooth real function on the complex plane vanishes at the origin and its
  differential there is a positive multiple of the vertical coordinate, then
  its zero set is locally the graph of a smooth real function through the
  origin with horizontal tangent.
proof:
  Work in real product coordinates using the continuous linear equivalence
  \(\mathbb C\simeq\mathbb R\times\mathbb R\).  The vertical partial
  derivative is multiplication by the positive number \(L\), hence invertible,
  so Mathlib's implicit function theorem applies.  The theorem gives the
  local graph and its smoothness.  The derivative formula for the implicit
  function gives zero derivative because the horizontal part of the given
  differential is zero.
-/
theorem smoothComplexZeroSet_verticalDerivative_has_local_implicit_graph_at_origin
    {F : ℂ → ℝ}
    (hF_smooth : ContDiffAt ℝ ∞ F 0)
    {dF : ℂ →L[ℝ] ℝ}
    (hF_deriv : HasFDerivAt F dF 0) {L : ℝ} (hLpos : 0 < L)
    (hdF_vertical : ∀ w : ℂ, dF w = L * w.im)
    (hF_zero : F 0 = 0) :
    ∃ U : Set ℂ, ∃ φ : ℝ → ℝ,
      IsOpen U ∧ (0 : ℂ) ∈ U ∧
        ContDiffAt ℝ ∞ φ 0 ∧ φ 0 = 0 ∧ HasDerivAt φ 0 0 ∧
          ∀ w : ℂ, w ∈ U → (F w = 0 ↔ w.im = φ w.re) := by
  let G : ℝ × ℝ → ℝ := fun p => F (Complex.equivRealProdCLM.symm p)
  have he_smooth :
      ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => Complex.equivRealProdCLM.symm p)
        ((0, 0) : ℝ × ℝ) := by
    fun_prop
  have hF_smooth_at :
      ContDiffAt ℝ ∞ F (Complex.equivRealProdCLM.symm ((0, 0) : ℝ × ℝ)) := by
    simpa [Complex.equivRealProdCLM_symm_apply] using hF_smooth
  have hG_smooth : ContDiffAt ℝ ∞ G ((0, 0) : ℝ × ℝ) := by
    simpa [G] using hF_smooth_at.comp (((0, 0) : ℝ × ℝ)) he_smooth
  have he_deriv :
      HasFDerivAt (fun p : ℝ × ℝ => Complex.equivRealProdCLM.symm p)
        (Complex.equivRealProdCLM.symm : (ℝ × ℝ) →L[ℝ] ℂ) ((0, 0) : ℝ × ℝ) :=
    (Complex.equivRealProdCLM.symm : (ℝ × ℝ) →L[ℝ] ℂ).hasFDerivAt
  have hF_deriv_at :
      HasFDerivAt F dF (Complex.equivRealProdCLM.symm ((0, 0) : ℝ × ℝ)) := by
    simpa [Complex.equivRealProdCLM_symm_apply] using hF_deriv
  have hG_deriv :
      HasFDerivAt G (dF.comp (Complex.equivRealProdCLM.symm : (ℝ × ℝ) →L[ℝ] ℂ))
        ((0, 0) : ℝ × ℝ) := by
    simpa [G, Function.comp_def] using hF_deriv_at.comp (((0, 0) : ℝ × ℝ)) he_deriv
  have hG_fderiv :
      fderiv ℝ G ((0, 0) : ℝ × ℝ) =
        dF.comp (Complex.equivRealProdCLM.symm : (ℝ × ℝ) →L[ℝ] ℂ) :=
    hG_deriv.fderiv
  let partialY : ℝ →L[ℝ] ℝ :=
    fderiv ℝ G ((0, 0) : ℝ × ℝ) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ
  have hpartialY_eq :
      partialY = (ContinuousLinearEquiv.smulLeft (Units.mk0 L hLpos.ne') : ℝ ≃L[ℝ] ℝ) := by
    apply ContinuousLinearMap.ext
    intro y
    simp [partialY, hG_fderiv, ContinuousLinearMap.comp_apply,
      Complex.equivRealProdCLM_symm_apply, hdF_vertical]
  have if₂ :
      (fderiv ℝ G ((0, 0) : ℝ × ℝ) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
    change partialY.IsInvertible
    rw [hpartialY_eq]
    exact ContinuousLinearMap.isInvertible_equiv
  let φ : ℝ → ℝ := hG_smooth.implicitFunction (by simp) if₂
  have hφ_smooth : ContDiffAt ℝ ∞ φ 0 := by
    simpa [φ] using hG_smooth.contDiffAt_implicitFunction (by simp) if₂
  have hφ_zero : φ 0 = 0 := by
    simpa [φ] using hG_smooth.implicitFunction_apply_self (by simp) if₂
  have hpartialX_zero :
      fderiv ℝ G ((0, 0) : ℝ × ℝ) ∘L ContinuousLinearMap.inl ℝ ℝ ℝ = 0 := by
    apply ContinuousLinearMap.ext
    intro x
    simp [hG_fderiv, ContinuousLinearMap.comp_apply,
      Complex.equivRealProdCLM_symm_apply, hdF_vertical]
  have hφ_fderiv_zero : HasFDerivAt φ (0 : ℝ →L[ℝ] ℝ) 0 := by
    have hstrict := hG_smooth.hasStrictFDerivAt_implicitFunction (by simp) if₂
    have hmap :
        -((fderiv ℝ G ((0, 0) : ℝ × ℝ) ∘L
              ContinuousLinearMap.inr ℝ ℝ ℝ).inverse.comp
            (fderiv ℝ G ((0, 0) : ℝ × ℝ) ∘L
              ContinuousLinearMap.inl ℝ ℝ ℝ)) = (0 : ℝ →L[ℝ] ℝ) := by
      rw [hpartialX_zero]
      apply ContinuousLinearMap.ext
      intro x
      simp
    simpa [φ, hmap] using hstrict.hasFDerivAt
  have hφ_deriv : HasDerivAt φ 0 0 := by
    simpa using hφ_fderiv_zero.hasDerivAt
  have hzero_event_prod :
      ∀ᶠ p in 𝓝 (((0, 0) : ℝ × ℝ)),
        G p = G ((0, 0) : ℝ × ℝ) ↔ φ p.1 = p.2 := by
    simpa [φ] using hG_smooth.eventually_apply_eq_iff_implicitFunction (by simp) if₂
  have hzero_event_complex :
      ∀ᶠ w in 𝓝 (0 : ℂ), F w = 0 ↔ φ w.re = w.im := by
    have htend : Filter.Tendsto Complex.equivRealProdCLM
        (𝓝 (0 : ℂ)) (𝓝 (((0, 0) : ℝ × ℝ))) := by
      simpa [Complex.equivRealProdCLM_apply] using
        (Complex.equivRealProdCLM.continuous.continuousAt (x := (0 : ℂ)))
    have hcomp := htend.eventually hzero_event_prod
    filter_upwards [hcomp] with w hw
    simpa [G, Complex.equivRealProdCLM_apply, Complex.equivRealProdCLM_symm_apply, hF_zero]
      using hw
  rcases eventually_nhds_iff.mp hzero_event_complex with ⟨U, hUprop, hU_open, h0U⟩
  refine ⟨U, φ, hU_open, h0U, hφ_smooth, hφ_zero, hφ_deriv, ?_⟩
  intro w hwU
  have hw := hUprop w hwU
  constructor
  · intro hF
    exact (hw.mp hF).symm
  · intro hEq
    exact hw.mpr hEq.symm

/--
%%handwave
name:
  Derivative along a vertical complex line
statement:
  If \(F:\mathbb C\to\mathbb R\) is Fréchet differentiable at
  \(x+iy\) with derivative \(dF\), then
  \[
    \frac{d}{dt}\Big|_{t=y}F(x+it)=dF(i).
  \]
proof:
  The parametrization \(t\mapsto x+it\) has derivative \(i\).  Apply the
  chain rule.
-/
private theorem HasFDerivAt.hasDerivAt_verticalLine
    {F : ℂ → ℝ} {dF : ℂ →L[ℝ] ℝ} {x y : ℝ}
    (hF : HasFDerivAt F dF ((x : ℂ) + (y : ℂ) * Complex.I)) :
    HasDerivAt (fun t : ℝ => F ((x : ℂ) + (t : ℂ) * Complex.I)) (dF Complex.I) y := by
  have hline : HasDerivAt (fun t : ℝ => (x : ℂ) + (t : ℂ) * Complex.I) Complex.I y := by
    have hcoe : HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) y := by
      simpa using Complex.ofRealCLM.hasDerivAt (x := y)
    simpa using (hcoe.mul_const Complex.I).const_add (x : ℂ)
  simpa [Function.comp_def] using
    HasFDerivAt.comp_hasDerivAt (l := F)
      (f := fun t : ℝ => (x : ℂ) + (t : ℂ) * Complex.I) y hF hline

/--
%%handwave
name:
  Persistence of a positive vertical derivative near the origin
statement:
  Suppose \(F:\mathbb C\to\mathbb R\) is smooth near \(0\) and
  \[
    dF_0(w)=L\,\operatorname{Im}w
    \quad\text{with }L>0.
  \]
  Then for every \(z\) sufficiently near \(0\),
  \[
    dF_z(i)>0.
  \]
proof:
  Smoothness makes \(z\mapsto dF_z(i)\) continuous at the origin, where its
  value is \(L>0\).  Positivity persists on a neighborhood.
-/
private theorem eventually_positive_vertical_fderiv_at_origin
    {F : ℂ → ℝ}
    (hF_smooth : ContDiffAt ℝ ∞ F 0)
    {dF : ℂ →L[ℝ] ℝ}
    (hF_deriv : HasFDerivAt F dF 0) {L : ℝ} (hLpos : 0 < L)
    (hdF_vertical : ∀ w : ℂ, dF w = L * w.im) :
    ∀ᶠ z in 𝓝 (0 : ℂ), 0 < (fderiv ℝ F z) Complex.I := by
  let V : ℂ → ℝ := fun z => (fderiv ℝ F z) Complex.I
  have hV_cont : ContinuousAt V 0 := by
    exact (hF_smooth.continuousAt_fderiv (by simp)).clm_apply continuousAt_const
  have hV_zero : V 0 = L := by
    simp [V, hF_deriv.fderiv, hdF_vertical]
  exact hV_cont.eventually (isOpen_Ioi.mem_nhds (by simpa [hV_zero] using hLpos))

/--
%%handwave
name:
  Infinite smoothness near a point implies local first-order smoothness
statement:
  If \(F:\mathbb C\to\mathbb R\) is smooth to all orders at \(0\), then
  \(F\) is continuously differentiable at every point in some neighborhood
  of \(0\).
proof:
  Infinite smoothness at a point includes eventual smoothness of every
  finite order; specialize to order one.
-/
private theorem eventually_contDiffAt_one_at_origin
    {F : ℂ → ℝ} (hF_smooth : ContDiffAt ℝ ∞ F 0) :
    ∀ᶠ z in 𝓝 (0 : ℂ), ContDiffAt ℝ 1 F z := by
  exact (hF_smooth.of_le
    (by
      change ((1 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)).eventually (by simp)

/--
%%handwave
name:
  Positive vertical derivative gives strict vertical monotonicity
statement:
  Let \(F:\mathbb C\to\mathbb R\) be continuously differentiable on a set
  \(S\), with \(dF_z(i)>0\) there.  If the vertical segment
  \(\{x+iy:a\le y\le b\}\) lies in \(S\), then
  \[
    y\longmapsto F(x+iy)
  \]
  is strictly increasing on \([a,b]\).
proof:
  The chain rule identifies the derivative along the vertical line with
  \(dF_{x+iy}(i)>0\).  The one-variable positive-derivative criterion gives
  strict monotonicity on the interval.
-/
private theorem strictMonoOn_verticalLine_of_fderiv_pos
    {F : ℂ → ℝ} {S : Set ℂ} {x a b : ℝ}
    (hF_smooth : ∀ z ∈ S, ContDiffAt ℝ 1 F z)
    (hpos : ∀ z ∈ S, 0 < (fderiv ℝ F z) Complex.I)
    (hseg : ∀ y ∈ Set.Icc a b, ((x : ℂ) + (y : ℂ) * Complex.I) ∈ S) :
    StrictMonoOn (fun y : ℝ => F ((x : ℂ) + (y : ℂ) * Complex.I)) (Set.Icc a b) := by
  refine strictMonoOn_of_hasDerivWithinAt_pos
    (D := Set.Icc a b)
    (f := fun y : ℝ => F ((x : ℂ) + (y : ℂ) * Complex.I))
    (f' := fun y : ℝ => (fderiv ℝ F ((x : ℂ) + (y : ℂ) * Complex.I)) Complex.I)
    (convex_Icc a b) ?_ ?_ ?_
  · refine continuousOn_of_forall_continuousAt fun y hy => ?_
    have hz : ((x : ℂ) + (y : ℂ) * Complex.I) ∈ S := hseg y hy
    have hF_cont : ContinuousAt F ((x : ℂ) + (y : ℂ) * Complex.I) :=
      (hF_smooth _ hz).continuousAt
    have hline_cont : ContinuousAt (fun t : ℝ => (x : ℂ) + (t : ℂ) * Complex.I) y := by
      fun_prop
    exact ContinuousAt.comp' (x := y)
      (f := fun t : ℝ => (x : ℂ) + (t : ℂ) * Complex.I) (g := F) hF_cont hline_cont
  · intro y hy
    have hyIcc : y ∈ Set.Icc a b := interior_subset hy
    have hz : ((x : ℂ) + (y : ℂ) * Complex.I) ∈ S := hseg y hyIcc
    have hFat : HasFDerivAt F (fderiv ℝ F ((x : ℂ) + (y : ℂ) * Complex.I))
        ((x : ℂ) + (y : ℂ) * Complex.I) :=
      ((hF_smooth _ hz).differentiableAt (by simp)).hasFDerivAt
    exact (HasFDerivAt.hasDerivAt_verticalLine (F := F) (x := x) (y := y) hFat).hasDerivWithinAt
  · intro y hy
    have hyIcc : y ∈ Set.Icc a b := interior_subset hy
    exact hpos _ (hseg y hyIcc)

/--
%%handwave
name:
  A small vertical segment lies in a prescribed complex ball
statement:
  Let \(R>0\).  If
  \[
    |x|<R/4,\qquad |a|<R/4,\qquad |b|<R/4,
  \]
  then every \(y\in[a,b]\) satisfies
  \[
    |x+iy|<R.
  \]
proof:
  The interval bounds give \(|y|<R/4\).  Hence
  \(|x+iy|\le|x|+|y|<R/2<R\).
-/
private theorem vertical_segment_mem_ball_of_abs_bounds
    {R x a b y : ℝ} (hRpos : 0 < R)
    (hx : |x| < R / 4) (ha : |a| < R / 4) (hb : |b| < R / 4)
    (hy : y ∈ Set.Icc a b) :
    ((x : ℂ) + (y : ℂ) * Complex.I) ∈ Metric.ball (0 : ℂ) R := by
  have hy_abs : |y| < R / 4 := by
    refine abs_lt.mpr ⟨?_, ?_⟩
    · exact lt_of_lt_of_le (abs_lt.mp ha).1 hy.1
    · exact lt_of_le_of_lt hy.2 (abs_lt.mp hb).2
  have hnorm_le :
      ‖(x : ℂ) + (y : ℂ) * Complex.I‖ ≤ |x| + |y| := by
    calc
      ‖(x : ℂ) + (y : ℂ) * Complex.I‖ ≤ ‖(x : ℂ)‖ + ‖(y : ℂ) * Complex.I‖ :=
        norm_add_le _ _
      _ = |x| + |y| := by simp
  have hsum : |x| + |y| < R := by
    nlinarith [hx, hy_abs, hRpos]
  have hnorm : ‖(x : ℂ) + (y : ℂ) * Complex.I‖ < R :=
    lt_of_le_of_lt hnorm_le hsum
  simpa [Metric.mem_ball, dist_eq_norm] using hnorm

/--
%%handwave
name:
  A positive vertical derivative identifies the sublevel side of a local graph
statement:
  If the zero set is locally a graph and the differential at the origin is a
  positive multiple of the vertical coordinate, then after shrinking the
  neighborhood the closed sublevel set lies below that graph.
proof:
  By continuity of the vertical derivative, the function is strictly increasing
  in the vertical variable on a small box.  The zero graph cuts each vertical
  segment once, so points on the \(F\le0\) side must have vertical coordinate
  at most the graph height.
-/
theorem smoothComplexSublevelSet_side_of_local_implicit_graph_at_origin
    {F : ℂ → ℝ}
    (hF_smooth : ContDiffAt ℝ ∞ F 0)
    {dF : ℂ →L[ℝ] ℝ}
    (hF_deriv : HasFDerivAt F dF 0) {L : ℝ} (hLpos : 0 < L)
    (hdF_vertical : ∀ w : ℂ, dF w = L * w.im)
    {U₀ : Set ℂ} {φ : ℝ → ℝ}
    (hU₀_open : IsOpen U₀) (h0U₀ : (0 : ℂ) ∈ U₀)
    (hφ_cont : ContinuousAt φ 0) (hφ_zero : φ 0 = 0)
    (hzero_graph : ∀ w : ℂ, w ∈ U₀ → (F w = 0 ↔ w.im = φ w.re)) :
    ∃ U : Set ℂ,
      IsOpen U ∧ (0 : ℂ) ∈ U ∧ U ⊆ U₀ ∧
        ∀ w : ℂ, w ∈ U → F w ≤ 0 → w.im - φ w.re ≤ 0 := by
  let S : Set ℂ :=
    {z | z ∈ U₀ ∧ ContDiffAt ℝ 1 F z ∧ 0 < (fderiv ℝ F z) Complex.I}
  have hS_nhds : S ∈ 𝓝 (0 : ℂ) := by
    exact Filter.inter_mem (hU₀_open.mem_nhds h0U₀)
      (Filter.inter_mem (eventually_contDiffAt_one_at_origin hF_smooth)
        (eventually_positive_vertical_fderiv_at_origin hF_smooth hF_deriv hLpos hdF_vertical))
  rcases Metric.mem_nhds_iff.mp hS_nhds with ⟨R, hRpos, hRsub⟩
  have hR4pos : 0 < R / 4 := by positivity
  have hφ_small_nhds : {x : ℝ | |φ x| < R / 4} ∈ 𝓝 (0 : ℝ) := by
    have hball : Metric.ball (φ 0) (R / 4) ∈ 𝓝 (φ 0) :=
      Metric.ball_mem_nhds _ hR4pos
    have hpre := hφ_cont hball
    exact Filter.mem_of_superset hpre (by
      intro x hx
      simpa [Metric.mem_ball, Real.dist_eq, hφ_zero] using hx)
  rcases Metric.mem_nhds_iff.mp hφ_small_nhds with ⟨rφ, hrφpos, hrφsub⟩
  let r : ℝ := min rφ (R / 4)
  have hrpos : 0 < r := lt_min hrφpos hR4pos
  have hr_le_rφ : r ≤ rφ := min_le_left _ _
  have hr_le_R4 : r ≤ R / 4 := min_le_right _ _
  have hr_lt_R : r < R := by
    nlinarith [hr_le_R4, hRpos]
  refine ⟨Metric.ball (0 : ℂ) r, Metric.isOpen_ball, Metric.mem_ball_self hrpos, ?_, ?_⟩
  · intro w hw
    have hw_norm : ‖w‖ < r := by
      simpa [Metric.mem_ball, dist_eq_norm] using hw
    exact (hRsub (by
      simpa [Metric.mem_ball, dist_eq_norm] using lt_trans hw_norm hr_lt_R)).1
  · intro w hw hFw
    by_contra hnot
    have hdiff_pos : 0 < w.im - φ w.re := lt_of_not_ge hnot
    have hgraph_lt : φ w.re < w.im := sub_pos.mp hdiff_pos
    have hw_norm : ‖w‖ < r := by
      simpa [Metric.mem_ball, dist_eq_norm] using hw
    have hx_abs : |w.re| < R / 4 := by
      exact lt_of_le_of_lt (Complex.abs_re_le_norm w) (lt_of_lt_of_le hw_norm hr_le_R4)
    have him_abs : |w.im| < R / 4 := by
      exact lt_of_le_of_lt (Complex.abs_im_le_norm w) (lt_of_lt_of_le hw_norm hr_le_R4)
    have hx_abs_rφ : |w.re| < rφ :=
      lt_of_lt_of_le (lt_of_le_of_lt (Complex.abs_re_le_norm w) hw_norm) hr_le_rφ
    have hφ_abs : |φ w.re| < R / 4 := by
      exact hrφsub (by
        simpa [Metric.mem_ball, Real.dist_eq] using hx_abs_rφ)
    have hseg : ∀ y ∈ Set.Icc (φ w.re) w.im,
        ((w.re : ℂ) + (y : ℂ) * Complex.I) ∈ S := by
      intro y hy
      exact hRsub (vertical_segment_mem_ball_of_abs_bounds hRpos hx_abs hφ_abs him_abs hy)
    have hmono : StrictMonoOn
        (fun y : ℝ => F ((w.re : ℂ) + (y : ℂ) * Complex.I))
        (Set.Icc (φ w.re) w.im) :=
      strictMonoOn_verticalLine_of_fderiv_pos
        (S := S) (x := w.re) (a := φ w.re) (b := w.im)
        (fun z hz => hz.2.1) (fun z hz => hz.2.2) hseg
    have hleft_mem : φ w.re ∈ Set.Icc (φ w.re) w.im := Set.left_mem_Icc.mpr hgraph_lt.le
    have hright_mem : w.im ∈ Set.Icc (φ w.re) w.im := Set.right_mem_Icc.mpr hgraph_lt.le
    have hstrict := hmono hleft_mem hright_mem hgraph_lt
    have hgraph_mem : ((w.re : ℂ) + (φ w.re : ℂ) * Complex.I) ∈ U₀ :=
      (hseg (φ w.re) hleft_mem).1
    have hgraph_zero : F ((w.re : ℂ) + (φ w.re : ℂ) * Complex.I) = 0 := by
      have hiff := hzero_graph ((w.re : ℂ) + (φ w.re : ℂ) * Complex.I) hgraph_mem
      exact hiff.mpr (by simp)
    have hFpos : 0 < F w := by
      have hw_decomp : (w.re : ℂ) + (w.im : ℂ) * Complex.I = w := Complex.re_add_im w
      have hstrict' :
          F ((w.re : ℂ) + (φ w.re : ℂ) * Complex.I) < F w := by
        simpa [hw_decomp] using hstrict
      simpa [hgraph_zero] using hstrict'
    exact (not_le_of_gt hFpos) hFw

/--
%%handwave
name:
  A centered vertical differential gives a local implicit sublevel graph
statement:
  If a smooth real function on the complex plane vanishes at the origin and has
  positive vertical differential there, with no horizontal differential, then
  locally its closed sublevel side lies below a smooth graph through the origin
  with horizontal tangent.
proof:
  Apply the real implicit function theorem to the zero set.  Since the vertical
  derivative is positive, the function is locally strictly increasing in the
  vertical variable along short vertical segments.  This identifies the
  \(F\le0\) side as the region below the implicit graph.  The derivative
  formula for the implicit function gives horizontal tangent because the
  horizontal differential vanishes.
-/
theorem smoothComplexSublevelSet_verticalDerivative_has_local_implicit_graph_at_origin
    {F : ℂ → ℝ}
    (hF_smooth : ContDiffAt ℝ ∞ F 0)
    {dF : ℂ →L[ℝ] ℝ}
    (hF_deriv : HasFDerivAt F dF 0) {L : ℝ} (hLpos : 0 < L)
    (hdF_vertical : ∀ w : ℂ, dF w = L * w.im)
    (hF_zero : F 0 = 0) :
    ∃ U : Set ℂ, ∃ φ : ℝ → ℝ,
      IsOpen U ∧ (0 : ℂ) ∈ U ∧
        ContDiffAt ℝ ∞ φ 0 ∧ φ 0 = 0 ∧ HasDerivAt φ 0 0 ∧
          ∀ w : ℂ, w ∈ U → F w ≤ 0 → w.im - φ w.re ≤ 0 := by
  rcases smoothComplexZeroSet_verticalDerivative_has_local_implicit_graph_at_origin
      hF_smooth hF_deriv hLpos hdF_vertical hF_zero with
    ⟨U₀, φ, hU₀_open, h0U₀, hφ_smooth, hφ_zero, hφ_deriv, hzero_graph⟩
  rcases smoothComplexSublevelSet_side_of_local_implicit_graph_at_origin
      hF_smooth hF_deriv hLpos hdF_vertical hU₀_open h0U₀ hφ_smooth.continuousAt
      hφ_zero hzero_graph with
    ⟨U, hU_open, h0U, hU_sub, hside⟩
  exact ⟨U, φ, hU_open, h0U, hφ_smooth, hφ_zero, hφ_deriv, hside⟩

/--
%%handwave
name:
  A vertical differential gives a local implicit sublevel graph
statement:
  If a smooth real defining function has positive vertical differential in
  adapted orthonormal coordinates, then locally its closed sublevel side lies
  below a smooth graph through the origin with horizontal tangent.
proof:
  Apply the implicit function theorem to the zero set in the vertical variable.
  The positive vertical derivative determines the sign of the sublevel side,
  and the derivative formula for the implicit function gives horizontal
  tangent because the adapted differential kills the horizontal direction.
-/
theorem smoothPlaneSublevelSet_verticalDerivative_has_local_implicit_graph
    {r : ℂ → ℝ} {z₀ : ℂ} {T : ℂ ≃ₗᵢ[ℝ] ℂ}
    (hr_smooth : ContDiffAt ℝ ∞ r z₀)
    {dr : ℂ →L[ℝ] ℝ}
    (hr_deriv : HasFDerivAt r dr z₀) {L : ℝ} (hLpos : 0 < L)
    (hdr_vertical : ∀ w : ℂ, dr (T.symm w) = L * w.im)
    (hr_zero : r z₀ = 0) :
    ∃ U : Set ℂ, ∃ φ : ℝ → ℝ,
      IsOpen U ∧ (0 : ℂ) ∈ U ∧
        ContDiffAt ℝ ∞ φ 0 ∧ φ 0 = 0 ∧ HasDerivAt φ 0 0 ∧
          ∀ z : ℂ, T (z - z₀) ∈ U → r z ≤ 0 →
            (T (z - z₀)).im - φ ((T (z - z₀)).re) ≤ 0 := by
  let F : ℂ → ℝ := fun w => r (z₀ + T.symm w)
  have hcoord_smooth : ContDiffAt ℝ ∞ (fun w : ℂ => z₀ + T.symm w) 0 := by
    fun_prop
  have hr_smooth_at : ContDiffAt ℝ ∞ r (z₀ + T.symm (0 : ℂ)) := by
    simpa using hr_smooth
  have hF_smooth : ContDiffAt ℝ ∞ F 0 := by
    simpa [F] using hr_smooth_at.comp (0 : ℂ) hcoord_smooth
  have hcoord_deriv : HasFDerivAt (fun w : ℂ => z₀ + T.symm w)
      (T.symm : ℂ →L[ℝ] ℂ) 0 := by
    simpa using ((T.symm : ℂ →L[ℝ] ℂ).hasFDerivAt (x := (0 : ℂ))).const_add z₀
  have hr_deriv_at : HasFDerivAt r dr (z₀ + T.symm (0 : ℂ)) := by
    simpa using hr_deriv
  have hF_deriv : HasFDerivAt F (dr.comp (T.symm : ℂ →L[ℝ] ℂ)) 0 := by
    simpa [F, Function.comp_def] using hr_deriv_at.comp (0 : ℂ) hcoord_deriv
  have hF_vertical : ∀ w : ℂ, (dr.comp (T.symm : ℂ →L[ℝ] ℂ)) w = L * w.im := by
    intro w
    simpa [ContinuousLinearMap.comp_apply] using hdr_vertical w
  have hF_zero : F 0 = 0 := by
    simpa [F] using hr_zero
  rcases smoothComplexSublevelSet_verticalDerivative_has_local_implicit_graph_at_origin
      hF_smooth hF_deriv hLpos hF_vertical hF_zero with
    ⟨U, φ, hU_open, h0U, hφ_smooth, hφ_zero, hφ_deriv, hsublevel⟩
  refine ⟨U, φ, hU_open, h0U, hφ_smooth, hφ_zero, hφ_deriv, ?_⟩
  intro z hzU hrz
  let w : ℂ := T (z - z₀)
  have hz_decomp : z = z₀ + T.symm w := by
    calc
      z = z₀ + (z - z₀) := by abel
      _ = z₀ + T.symm (T (z - z₀)) := by rw [T.symm_apply_apply]
      _ = z₀ + T.symm w := rfl
  have hFz : F w = r z := by
    dsimp [F]
    rw [← hz_decomp]
  simpa [w] using hsublevel w hzU (by rwa [hFz])

/--
%%handwave
name:
  Vertical differential gives a quadratically bounded implicit graph
statement:
  If a smooth real defining function has nonzero vertical differential in
  adapted orthonormal coordinates, then the closed sublevel side lies locally
  below a graph tangent to the horizontal axis and bounded above by \(A x^2\).
proof:
  First
  [the vertical differential gives a local implicit sublevel graph](lean:JJMath.Uniformization.smoothPlaneSublevelSet_verticalDerivative_has_local_implicit_graph).
  The resulting graph is smooth, passes through the origin, and has zero first
  derivative there.  Hence
  [a smooth real graph with zero tangent has a quadratic upper bound](lean:JJMath.Uniformization.smoothRealFunction_tangent_zero_has_quadratic_upper_bound).
-/
theorem smoothPlaneSublevelSet_verticalDerivative_has_quadratic_graph_bound
    {r : ℂ → ℝ} {z₀ : ℂ} {T : ℂ ≃ₗᵢ[ℝ] ℂ}
    (hr_smooth : ContDiffAt ℝ ∞ r z₀)
    {dr : ℂ →L[ℝ] ℝ}
    (hr_deriv : HasFDerivAt r dr z₀) {L : ℝ} (hLpos : 0 < L)
    (hdr_vertical : ∀ w : ℂ, dr (T.symm w) = L * w.im)
    (hr_zero : r z₀ = 0) :
    ∃ U : Set ℂ, ∃ φ : ℝ → ℝ, ∃ A ρ : ℝ,
      IsOpen U ∧ (0 : ℂ) ∈ U ∧ 0 < ρ ∧
        (∀ x : ℝ, |x| < ρ → φ x ≤ A * x ^ 2) ∧
        ∀ z : ℂ, T (z - z₀) ∈ U → r z ≤ 0 →
          (T (z - z₀)).im - φ ((T (z - z₀)).re) ≤ 0 := by
  rcases smoothPlaneSublevelSet_verticalDerivative_has_local_implicit_graph
      hr_smooth hr_deriv hLpos hdr_vertical hr_zero with
    ⟨U, φ, hU_open, h0U, hφ_smooth, hφ_zero, hφ_deriv, hsublevel_graph⟩
  rcases smoothRealFunction_tangent_zero_has_quadratic_upper_bound
      hφ_smooth hφ_zero hφ_deriv with
    ⟨A, ρ, hρpos, hφ_bound⟩
  exact ⟨U, φ, A, ρ, hU_open, h0U, hρpos, hφ_bound, hsublevel_graph⟩

/--
%%handwave
name:
  Smooth plane sublevel sets have adapted graph coordinates
statement:
  If a smooth real function on the plane vanishes at a point and has nonzero
  differential there, then one can choose orthonormal coordinates centered at
  the point in which the closed sublevel side lies below a graph whose tangent
  at the origin is horizontal and whose height is quadratically bounded.
proof:
  First use that
  [a nonzero real differential has adapted orthonormal coordinates](lean:JJMath.Uniformization.realLinearFunctional_has_adapted_isometry).
  In those coordinates,
  [the vertical differential gives a quadratically bounded implicit graph](lean:JJMath.Uniformization.smoothPlaneSublevelSet_verticalDerivative_has_quadratic_graph_bound).
-/
theorem smoothPlaneSublevelSet_has_adapted_quadratic_graph_bound
    {r : ℂ → ℝ} {z₀ : ℂ}
    (hr_smooth : ContDiffAt ℝ ∞ r z₀)
    {dr : ℂ →L[ℝ] ℝ}
    (hr_deriv : HasFDerivAt r dr z₀) (hdr_nonzero : dr ≠ 0)
    (hr_zero : r z₀ = 0) :
    ∃ T : ℂ ≃ₗᵢ[ℝ] ℂ, ∃ U : Set ℂ, ∃ φ : ℝ → ℝ, ∃ A ρ : ℝ,
      IsOpen U ∧ (0 : ℂ) ∈ U ∧ 0 < ρ ∧
        (∀ x : ℝ, |x| < ρ → φ x ≤ A * x ^ 2) ∧
        ∀ z : ℂ, T (z - z₀) ∈ U → r z ≤ 0 →
          (T (z - z₀)).im - φ ((T (z - z₀)).re) ≤ 0 := by
  rcases realLinearFunctional_has_adapted_isometry dr hdr_nonzero with
    ⟨T, L, hLpos, hdr_vertical⟩
  rcases smoothPlaneSublevelSet_verticalDerivative_has_quadratic_graph_bound
      hr_smooth hr_deriv hLpos hdr_vertical hr_zero with
    ⟨U, φ, A, ρ, hU_open, h0U, hρpos, hφ_bound, hsublevel_graph⟩
  exact ⟨T, U, φ, A, ρ, hU_open, h0U, hρpos, hφ_bound, hsublevel_graph⟩

/--
%%handwave
name:
  Smooth plane sublevel sets have quadratic exterior support
statement:
  If a smooth real function on the plane vanishes at a point and has nonzero
  differential there, then, after shrinking, the closed sublevel side admits a
  circle center, radius, and positive constant for which the squared distance
  to the center grows at least quadratically away from the base point.
proof:
  Use
  [adapted graph coordinates](lean:JJMath.Uniformization.smoothPlaneSublevelSet_has_adapted_quadratic_graph_bound)
  to reduce to a quadratically bounded graph.  In those coordinates the
  [elementary exterior-circle estimate](lean:JJMath.Uniformization.exteriorCircle_quadraticSupport_of_graphBound)
  gives the desired squared-distance inequality, and the isometry transfers it
  back to the original coordinate plane.
-/
theorem smoothPlaneSublevelSet_has_quadratic_exterior_support
    {r : ℂ → ℝ} {z₀ : ℂ}
    (hr_smooth : ContDiffAt ℝ ∞ r z₀)
    {dr : ℂ →L[ℝ] ℝ}
    (hr_deriv : HasFDerivAt r dr z₀) (hdr_nonzero : dr ≠ 0)
    (hr_zero : r z₀ = 0) :
    ∃ W : Set ℂ, ∃ c : ℂ, ∃ R : ℝ, ∃ κ : ℝ,
      IsOpen W ∧ z₀ ∈ W ∧ 0 < R ∧ 0 < κ ∧
        ‖z₀ - c‖ = R ∧
          ∀ z ∈ W, r z ≤ 0 → R ^ 2 + κ * ‖z - z₀‖ ^ 2 ≤ ‖z - c‖ ^ 2 := by
  rcases smoothPlaneSublevelSet_has_adapted_quadratic_graph_bound
      hr_smooth hr_deriv hdr_nonzero hr_zero with
    ⟨T, U, φ, A, ρ, hU_open, h0U, hρpos, hφ_bound, hsublevel_graph⟩
  rcases exists_positive_radius_for_exteriorCircle A with ⟨R, hRpos, hRA⟩
  let W : Set ℂ := {z : ℂ | T (z - z₀) ∈ U ∧ |(T (z - z₀)).re| < ρ}
  let c₀ : ℂ := (R : ℂ) * Complex.I
  let c : ℂ := z₀ + T.symm c₀
  refine ⟨W, c, R, (1 / 4 : ℝ), ?_, ?_, hRpos, by norm_num, ?_, ?_⟩
  · have hcoord : Continuous fun z : ℂ => T (z - z₀) :=
      T.continuous.comp (continuous_id.sub continuous_const)
    have hre : Continuous fun z : ℂ => (T (z - z₀)).re :=
      Complex.continuous_re.comp hcoord
    exact (hU_open.preimage hcoord).inter
      (isOpen_lt hre.abs continuous_const)
  · simp [W, h0U, hρpos]
  · have hT_center : T (z₀ - c) = -c₀ := by
      have harg : z₀ - c = (0 : ℂ) - T.symm c₀ := by
        simp [c]
      calc
        T (z₀ - c) = T ((0 : ℂ) - T.symm c₀) := by rw [harg]
        _ = T (0 : ℂ) - T (T.symm c₀) := T.map_sub _ _
        _ = -c₀ := by simp
    have hc₀_norm : ‖c₀‖ = R := by
      have hR_nonneg : 0 ≤ R := le_of_lt hRpos
      simp [c₀, Real.norm_of_nonneg hR_nonneg]
    calc
      ‖z₀ - c‖ = ‖T (z₀ - c)‖ := (T.norm_map (z₀ - c)).symm
      _ = ‖-c₀‖ := by rw [hT_center]
      _ = ‖c₀‖ := norm_neg c₀
      _ = R := hc₀_norm
  · intro z hzW hrz
    let w : ℂ := T (z - z₀)
    have hside : w.im - φ w.re ≤ 0 := by
      simpa [w] using hsublevel_graph z hzW.1 hrz
    have hy_graph : w.im ≤ A * w.re ^ 2 := by
      have hφw : φ w.re ≤ A * w.re ^ 2 := hφ_bound w.re hzW.2
      linarith
    have halg :
        R ^ 2 + (1 / 4 : ℝ) * (w.re ^ 2 + w.im ^ 2) ≤
          w.re ^ 2 + (w.im - R) ^ 2 :=
      exteriorCircle_quadraticSupport_of_graphBound
        (le_of_lt hRpos) hRA hy_graph
    have hnorm_base :
        ‖z - z₀‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
      have hnorm : ‖z - z₀‖ = ‖w‖ := by
        simpa [w] using (T.norm_map (z - z₀)).symm
      rw [hnorm, Complex.sq_norm w]
      simp [Complex.normSq_apply, pow_two]
    have hT_center : T (z - c) = w - c₀ := by
      have harg : z - c = (z - z₀) - T.symm c₀ := by
        simp [c, sub_eq_add_neg]
        abel
      calc
        T (z - c) = T ((z - z₀) - T.symm c₀) := by rw [harg]
        _ = T (z - z₀) - T (T.symm c₀) := T.map_sub _ _
        _ = w - c₀ := by simp [w]
    have hnorm_center :
        ‖z - c‖ ^ 2 = w.re ^ 2 + (w.im - R) ^ 2 := by
      have hnorm : ‖z - c‖ = ‖w - c₀‖ := by
        calc
          ‖z - c‖ = ‖T (z - c)‖ := (T.norm_map (z - c)).symm
          _ = ‖w - c₀‖ := by rw [hT_center]
      rw [hnorm, Complex.sq_norm (w - c₀)]
      simp [c₀, Complex.normSq_apply, pow_two]
    rw [hnorm_base, hnorm_center]
    exact halg

/--
%%handwave
name:
  Smooth plane sublevel sets have squared exterior tangent disks
statement:
  If a smooth real function on the plane vanishes at a point and has nonzero
  differential there, then, after shrinking, there is a circle whose squared
  distance function is minimized on the closed sublevel side exactly at that
  point.
proof:
  Use
  [quadratic exterior support](lean:JJMath.Uniformization.smoothPlaneSublevelSet_has_quadratic_exterior_support).
  The support inequality immediately gives the squared-radius lower bound.
  If equality with the squared radius holds, then the positive multiple of
  \(\|z-z_0\|^2\) must vanish, hence \(z=z_0\).
-/
theorem smoothPlaneSublevelSet_has_squared_exterior_tangent_disk
    {r : ℂ → ℝ} {z₀ : ℂ}
    (hr_smooth : ContDiffAt ℝ ∞ r z₀)
    {dr : ℂ →L[ℝ] ℝ}
    (hr_deriv : HasFDerivAt r dr z₀) (hdr_nonzero : dr ≠ 0)
    (hr_zero : r z₀ = 0) :
    ∃ W : Set ℂ, ∃ c : ℂ, ∃ R : ℝ,
      IsOpen W ∧ z₀ ∈ W ∧ 0 < R ∧
        ‖z₀ - c‖ = R ∧
          (∀ z ∈ W, r z ≤ 0 → R ^ 2 ≤ ‖z - c‖ ^ 2) ∧
            (∀ z ∈ W, r z ≤ 0 → ‖z - c‖ ^ 2 = R ^ 2 → z = z₀) := by
  rcases smoothPlaneSublevelSet_has_quadratic_exterior_support
      hr_smooth hr_deriv hdr_nonzero hr_zero with
    ⟨W, c, R, κ, hW_open, hz₀W, hRpos, hκpos, hz₀_dist, hsupport⟩
  refine ⟨W, c, R, hW_open, hz₀W, hRpos, hz₀_dist, ?_, ?_⟩
  · intro z hzW hrz
    have h := hsupport z hzW hrz
    nlinarith [sq_nonneg (‖z - z₀‖), mul_nonneg (le_of_lt hκpos) (sq_nonneg (‖z - z₀‖))]
  · intro z hzW hrz hsquare
    have h := hsupport z hzW hrz
    have hnorm_sq_zero : ‖z - z₀‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg (‖z - z₀‖), mul_nonneg (le_of_lt hκpos) (sq_nonneg (‖z - z₀‖))]
    have hnorm_zero : ‖z - z₀‖ = 0 :=
      sq_eq_zero_iff.mp hnorm_sq_zero
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm_zero)

/--
%%handwave
name:
  Smooth plane sublevel sets have exterior tangent disks
statement:
  If a smooth real function on the plane vanishes at a point and has nonzero
  differential there, then the closed sublevel side \(\{r\le0\}\) admits,
  after shrinking, an exterior Euclidean disk tangent exactly at that point.
proof:
  Apply the squared-distance version.  Since both the radius and distances are
  nonnegative, the squared inequality is equivalent to the distance
  inequality, and equality of distances gives equality of squares.
-/
theorem smoothPlaneSublevelSet_has_exterior_tangent_disk
    {r : ℂ → ℝ} {z₀ : ℂ}
    (hr_smooth : ContDiffAt ℝ ∞ r z₀)
    {dr : ℂ →L[ℝ] ℝ}
    (hr_deriv : HasFDerivAt r dr z₀) (hdr_nonzero : dr ≠ 0)
    (hr_zero : r z₀ = 0) :
    ∃ W : Set ℂ, ∃ c : ℂ, ∃ R : ℝ,
      IsOpen W ∧ z₀ ∈ W ∧ 0 < R ∧
        (∀ z ∈ W, r z ≤ 0 → R ≤ ‖z - c‖) ∧
          (∀ z ∈ W, r z ≤ 0 → (‖z - c‖ = R ↔ z = z₀)) := by
  rcases smoothPlaneSublevelSet_has_squared_exterior_tangent_disk
      hr_smooth hr_deriv hdr_nonzero hr_zero with
    ⟨W, c, R, hW_open, hz₀W, hRpos, hz₀_dist, hsquared_le,
      hsquared_eq⟩
  refine ⟨W, c, R, hW_open, hz₀W, hRpos, ?_, ?_⟩
  · intro z hzW hrz
    have hsquare : R ^ 2 ≤ ‖z - c‖ ^ 2 := hsquared_le z hzW hrz
    have habs : |R| ≤ |‖z - c‖| := sq_le_sq.mp hsquare
    simpa [abs_of_pos hRpos, abs_of_nonneg (norm_nonneg (z - c))] using habs
  · intro z hzW hrz
    constructor
    · intro hdist
      have hsquare : ‖z - c‖ ^ 2 = R ^ 2 := by
        rw [hdist]
      exact hsquared_eq z hzW hrz hsquare
    · intro hzz₀
      rw [hzz₀]
      exact hz₀_dist

/--
%%handwave
name:
  Smooth defining functions have exterior tangent disks
statement:
  A smooth real defining function with nonzero differential gives, after
  shrinking the coordinate neighborhood, an exterior Euclidean disk tangent to
  the local closed domain only at the chosen boundary point.
proof:
  First use the local defining-function description to see that, near the
  boundary point, the closed domain lies in the closed sublevel side
  \(r\le0\).  The planar result that
  [smooth sublevel sets have exterior tangent disks](lean:JJMath.Uniformization.smoothPlaneSublevelSet_has_exterior_tangent_disk)
  gives a disk in the chart.  Pull the chart neighborhood back to the surface.
-/
theorem smoothBoundaryDefiningFunction_has_exterior_tangent_disk
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronDomain X) {p : X}
    (hp : p ∈ Ω.boundary)
    {e : OpenPartialHomeomorph X ℂ}
    (_he : e ∈ atlas ℂ X) (hp_source : p ∈ e.source)
    {r : ℂ → ℝ} (hr_smooth : ContDiffAt ℝ ∞ r (e p))
    {dr : ℂ →L[ℝ] ℝ}
    (hr_deriv : HasFDerivAt r dr (e p)) (hdr_nonzero : dr ≠ 0)
    (hdefines : ∀ᶠ y in 𝓝 p,
      y ∈ e.source ∧
        (y ∈ Ω.carrier ↔ r (e y) < 0) ∧
          (y ∈ frontier Ω.carrier ↔ r (e y) = 0)) :
    ∃ N : Set X, ∃ c : ℂ, ∃ R : ℝ,
      IsOpen N ∧ p ∈ N ∧ N ⊆ e.source ∧ 0 < R ∧
        (∀ x ∈ closure Ω.carrier ∩ N, R ≤ ‖e x - c‖) ∧
          (∀ x ∈ closure Ω.carrier ∩ N, ‖e x - c‖ = R ↔ x = p) := by
  have hp_frontier : p ∈ frontier Ω.carrier := by
    simpa [PerronDomain.boundary] using hp
  rw [eventually_nhds_iff] at hdefines
  rcases hdefines with ⟨N₀, hN₀_defines, hN₀_open, hpN₀⟩
  have hp_defines := hN₀_defines p hpN₀
  have hr_zero : r (e p) = 0 :=
    hp_defines.2.2.mp hp_frontier
  rcases smoothPlaneSublevelSet_has_exterior_tangent_disk
      hr_smooth hr_deriv hdr_nonzero hr_zero with
    ⟨W, c, R, hW_open, hepW, hRpos, houtside_plane, htangent_plane⟩
  let N : Set X := N₀ ∩ (e.source ∩ e ⁻¹' W)
  have hN_open : IsOpen N :=
    hN₀_open.inter (by simpa using e.isOpen_inter_preimage hW_open)
  have hpN : p ∈ N := by
    exact ⟨hpN₀, hp_source, hepW⟩
  have hN_source : N ⊆ e.source := by
    intro x hx
    exact hx.2.1
  refine ⟨N, c, R, hN_open, hpN, hN_source, hRpos, ?_, ?_⟩
  · intro x hx
    have hx_closure : x ∈ closure Ω.carrier := hx.1
    have hxN : x ∈ N := hx.2
    have hxW : e x ∈ W := hxN.2.2
    have hx_defines := hN₀_defines x hxN.1
    have hr_nonpos : r (e x) ≤ 0 := by
      have hx_mem_or_frontier : x ∈ Ω.carrier ∪ frontier Ω.carrier := by
        simpa [closure_eq_self_union_frontier] using hx_closure
      rcases hx_mem_or_frontier with hxΩ | hxfrontier
      · exact le_of_lt (hx_defines.2.1.mp hxΩ)
      · exact le_of_eq (hx_defines.2.2.mp hxfrontier)
    exact houtside_plane (e x) hxW hr_nonpos
  · intro x hx
    have hx_closure : x ∈ closure Ω.carrier := hx.1
    have hxN : x ∈ N := hx.2
    have hxsource : x ∈ e.source := hxN.2.1
    have hxW : e x ∈ W := hxN.2.2
    have hx_defines := hN₀_defines x hxN.1
    have hr_nonpos : r (e x) ≤ 0 := by
      have hx_mem_or_frontier : x ∈ Ω.carrier ∪ frontier Ω.carrier := by
        simpa [closure_eq_self_union_frontier] using hx_closure
      rcases hx_mem_or_frontier with hxΩ | hxfrontier
      · exact le_of_lt (hx_defines.2.1.mp hxΩ)
      · exact le_of_eq (hx_defines.2.2.mp hxfrontier)
    constructor
    · intro hnorm
      have hex_eq : e x = e p :=
        (htangent_plane (e x) hxW hr_nonpos).1 hnorm
      calc
        x = e.symm (e x) := (e.left_inv hxsource).symm
        _ = e.symm (e p) := by rw [hex_eq]
        _ = p := e.left_inv hp_source
    · intro hxp
      rw [hxp]
      exact (htangent_plane (e p) hepW (le_of_eq hr_zero)).2 rfl

/--
%%handwave
name:
  A smooth defining function gives a local Perron barrier
statement:
  If, near a boundary point, a domain is cut out in a complex coordinate by a
  smooth defining function with nonzero differential, then that boundary point
  admits a local Perron barrier.
proof:
  The nonzero differential lets one flatten the boundary by the implicit
  function theorem, or equivalently find
  [an exterior tangent disk](lean:JJMath.Uniformization.smoothBoundaryDefiningFunction_has_exterior_tangent_disk)
  in the coordinate plane.  Then
  [the logarithmic potential of that disk is a local Perron barrier](lean:JJMath.Uniformization.exteriorTangentDisk_logPotential_has_local_perron_barrier).
-/
theorem smoothBoundaryDefiningFunction_has_local_perron_barrier
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronDomain X) {p : X}
    (hp : p ∈ Ω.boundary)
    {e : OpenPartialHomeomorph X ℂ}
    (he : e ∈ atlas ℂ X) (hp_source : p ∈ e.source)
    {r : ℂ → ℝ} (hr_smooth : ContDiffAt ℝ ∞ r (e p))
    {dr : ℂ →L[ℝ] ℝ}
    (hr_deriv : HasFDerivAt r dr (e p)) (hdr_nonzero : dr ≠ 0)
    (hdefines : ∀ᶠ y in 𝓝 p,
      y ∈ e.source ∧
        (y ∈ Ω.carrier ↔ r (e y) < 0) ∧
          (y ∈ frontier Ω.carrier ↔ r (e y) = 0)) :
    HasLocalPerronBarrierAt Ω p := by
  rcases smoothBoundaryDefiningFunction_has_exterior_tangent_disk Ω hp
      he hp_source hr_smooth hr_deriv hdr_nonzero hdefines with
    ⟨N, c, R, hN_open, hpN, hN_source, hRpos, houtside, htangent⟩
  exact exteriorTangentDisk_logPotential_has_local_perron_barrier Ω hp he
    hN_open hpN hN_source hRpos houtside htangent

/--
%%handwave
name:
  Smooth boundary points have local Perron barriers
statement:
  At every smooth boundary point of a smooth boundary domain there is a local
  Perron barrier.
proof:
  In a complex boundary chart, smoothness gives a smooth defining function
  with nonzero differential.  Then
  [the smooth defining function gives a local Perron barrier](lean:JJMath.Uniformization.smoothBoundaryDefiningFunction_has_local_perron_barrier).
-/
theorem smoothBoundaryDomain_boundary_points_have_local_barriers
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : SmoothBoundaryDomain X) :
    ∀ p ∈ (PerronDomain.ofSmoothBoundaryDomain Ω).boundary,
      HasLocalPerronBarrierAt (PerronDomain.ofSmoothBoundaryDomain Ω) p := by
  intro p hp
  have hp_frontier : p ∈ frontier Ω.carrier := by
    simpa [PerronDomain.boundary] using hp
  rcases Ω.smooth_boundary p hp_frontier with
    ⟨e, he, hp_source, r, hr_smooth, dr, hr_deriv, hdr_nonzero, hdefines⟩
  exact smoothBoundaryDefiningFunction_has_local_perron_barrier
    (PerronDomain.ofSmoothBoundaryDomain Ω) hp he hp_source
    hr_smooth.contDiffAt hr_deriv hdr_nonzero hdefines

/--
%%handwave
name:
  Smooth boundary points have Perron barriers
statement:
  At every boundary point of a smooth boundary domain there is a Perron
  barrier.
proof:
  Choose a complex coordinate in which the boundary is a smooth curve and the
  domain lies on one side.
  [Every smooth boundary point has a local Perron barrier](lean:JJMath.Uniformization.smoothBoundaryDomain_boundary_points_have_local_barriers)
  by using a small exterior tangent disk or a local defining function and
  transporting the barrier through the coordinate chart.  Then
  [a local Perron barrier extends to a global Perron barrier](lean:JJMath.Uniformization.localPerronBarrierAt_globalizes)
  by compactness of the closed domain.
tags:
  milestone
-/
theorem smoothBoundaryDomain_boundary_points_have_barriers
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : SmoothBoundaryDomain X) :
    ∀ p ∈ (PerronDomain.ofSmoothBoundaryDomain Ω).boundary,
      HasPerronBarrierAt (PerronDomain.ofSmoothBoundaryDomain Ω) p := by
  intro p hp
  exact localPerronBarrierAt_globalizes
    (PerronDomain.ofSmoothBoundaryDomain Ω)
    (smoothBoundaryDomain_boundary_points_have_local_barriers Ω p hp)

/--
%%handwave
name:
  Smooth boundary domains are Perron-regular
statement:
  Every smooth boundary domain in a Riemann surface with the componentwise
  maximum-principle geometry has Perron-regular boundary.
proof:
  The geometry hypothesis gives the maximum-principle part of regularity, and
  [each smooth boundary point has a Perron barrier](lean:JJMath.Uniformization.smoothBoundaryDomain_boundary_points_have_barriers).
-/
theorem smoothBoundaryDomain_perronRegular
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : SmoothBoundaryDomain X)
    (hΩ_geometry :
      HasComponentwiseMaximumPrincipleGeometry
        (PerronDomain.ofSmoothBoundaryDomain Ω).carrier) :
    PerronRegularBoundary (PerronDomain.ofSmoothBoundaryDomain Ω) := by
  exact ⟨hΩ_geometry, smoothBoundaryDomain_boundary_points_have_barriers Ω⟩

/--
%%handwave
name:
  Perron solution on a smooth boundary domain
statement:
  Every continuous boundary value on a smooth relatively compact domain in a
  Riemann surface has a harmonic Dirichlet solution when the domain has the
  componentwise geometry needed for the maximum principle.
proof:
  [Every smooth boundary domain is Perron-regular](lean:JJMath.Uniformization.smoothBoundaryDomain_perronRegular),
  and [the Perron Dirichlet candidate solves the Dirichlet problem](lean:JJMath.Uniformization.perron_envelope_solves_dirichlet) on
  every regular Perron domain.
tags:
  milestone
-/
theorem perron_dirichlet_solution_on_smooth_boundary_domain
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : SmoothBoundaryDomain X)
    (hΩ_geometry :
      HasComponentwiseMaximumPrincipleGeometry
        (PerronDomain.ofSmoothBoundaryDomain Ω).carrier)
    (φ : PerronBoundaryData (PerronDomain.ofSmoothBoundaryDomain Ω)) :
    ∃ u : X → ℝ,
      SolvesHarmonicDirichletProblem
        (PerronDomain.ofSmoothBoundaryDomain Ω) φ u := by
  refine ⟨perronDirichletCandidate (PerronDomain.ofSmoothBoundaryDomain Ω) φ, ?_⟩
  exact perron_envelope_solves_dirichlet
    (PerronDomain.ofSmoothBoundaryDomain Ω)
    (smoothBoundaryDomain_perronRegular Ω hΩ_geometry)
    φ

/--
%%handwave
name:
  Two boundary values give a nonconstant harmonic function
statement:
  If the boundary data takes two distinct values at two regular boundary
  points, then the Perron solution is nonconstant.
proof:
  [The Perron Dirichlet candidate solves the Dirichlet problem](lean:JJMath.Uniformization.perron_envelope_solves_dirichlet), so it
  assumes the prescribed values at both boundary points.  Since those values
  are different, the range of the solution contains at least two points.
-/
theorem perron_solution_nonconstant_of_two_boundary_values
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [ComplexOneManifold X]
    (Ω : PerronDomain X) (hΩreg : PerronRegularBoundary Ω)
    (φ : PerronBoundaryData Ω) {p q : X}
    (hp : p ∈ Ω.boundary) (hq : q ∈ Ω.boundary)
    (hφp : φ p = 0) (hφq : φ q = 1) :
    ∃ u : X → ℝ,
      SolvesHarmonicDirichletProblem Ω φ u ∧ (Set.range u).Nontrivial := by
  let u := perronDirichletCandidate Ω φ
  have hu : SolvesHarmonicDirichletProblem Ω φ u :=
    perron_envelope_solves_dirichlet Ω hΩreg φ
  refine ⟨u, hu, ?_⟩
  rcases hu with ⟨_, _, hboundary⟩
  have hup : u p = 0 := by
    rw [hboundary p hp, hφp]
  have huq : u q = 1 := by
    rw [hboundary q hq, hφq]
  refine Set.nontrivial_of_exists_ne (show u p ∈ Set.range u from ⟨p, rfl⟩) ?_
  refine ⟨u q, ⟨q, rfl⟩, ?_⟩
  intro h_eq
  have h10 : (1 : ℝ) = 0 := by
    rw [← huq, h_eq, hup]
  norm_num at h10

end Uniformization

end JJMath
