import JJMath.Hyperbolic.Converse.Continuation.Fields
import JJMath.Topology.UnitIntervalSplit

/-!
# Split path-skeleton continuation machinery
-/

namespace JJMath

open UpperHalfPlane

noncomputable section

namespace HyperbolicMetric

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]

/--
A finite chain of overlapping local-transition model branches along a
representative path.

This is the componentwise-overlap version of
`PathLocalModelContinuationChain`: adjacent branches only need to be glued by
the locally selected real Mobius representative at the handoff point.
-/
structure PathLocalTransitionModelContinuationChain
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g)
    {x : X} (p : Path x₀ x) where
  /-- Number of continuation steps. -/
  length : ℕ
  /-- Ordered path parameters at the vertices of the chain. -/
  parameterAt : Fin (length + 1) → unitInterval
  /-- The chain begins at the initial parameter. -/
  parameterAt_zero : parameterAt 0 = 0
  /-- The chain ends at the terminal parameter. -/
  parameterAt_last : parameterAt (Fin.last length) = 1
  /-- The parameters are weakly increasing. -/
  parameterAt_mono :
    ∀ k : Fin length,
      (parameterAt k.castSucc : ℝ) ≤ (parameterAt k.succ : ℝ)
  /-- Consecutive subdivision parameters are genuinely distinct. -/
  parameterAt_strictMono :
    ∀ k : Fin length,
      (parameterAt k.castSucc : ℝ) < (parameterAt k.succ : ℝ)
  /-- The local-transition model center used at each chain vertex. -/
  centerAt : Fin (length + 1) → X
  /-- The real Mobius postcomposition for the branch at each chain vertex. -/
  mobiusAt : Fin (length + 1) → RealMobiusRepresentative
  /-- The chain starts with the selected local model at the basepoint. -/
  initial_center_eq : centerAt 0 = x₀
  /-- The initial branch has identity Mobius normalization. -/
  initial_mobius_eq : mobiusAt 0 = 1
  /-- The sampled path point lies in its selected model domain. -/
  sample_mem_model_domain :
    ∀ i,
      p (parameterAt i) ∈ (localModels.chartAt (centerAt i)).domain
  /--
  Each subinterval of the representative path is contained in the model domain
  attached to the initial vertex of that subinterval.
  -/
  path_segment_mem_model_domain :
    ∀ k : Fin length, ∀ t : unitInterval,
      (parameterAt k.castSucc : ℝ) ≤ (t : ℝ) →
      (t : ℝ) ≤ (parameterAt k.succ : ℝ) →
      p t ∈ (localModels.chartAt (centerAt k.castSucc)).domain
  /-- The endpoint lies in the terminal model domain. -/
  terminal_endpoint_mem_domain :
    x ∈ (localModels.chartAt (centerAt (Fin.last length))).domain
  /--
  Adjacent normalized branches agree at the actual subdivision handoff point.
  -/
  adjacent_branch_agrees_at_transition :
    ∀ k : Fin length,
      realMobiusRepresentativeAction (mobiusAt k.succ)
          ((localModels.chartAt (centerAt k.succ)).toUpperHalfPlane
            (p (parameterAt k.succ))) =
        realMobiusRepresentativeAction (mobiusAt k.castSucc)
          ((localModels.chartAt (centerAt k.castSucc)).toUpperHalfPlane
            (p (parameterAt k.succ)))

/--
A weak finite subdivision skeleton for local-transition continuation along a
path.  It contains the compactness/topological part of the finite-chain
construction: the path is cut into finitely many closed subintervals, each
lying in one selected local-model domain, and the final vertex uses the
selected model at the endpoint.

The skeleton deliberately does not choose Mobius handoff representatives.  The
next step is supplied by `transitionData_nonempty_at_handoff`, using the
componentwise local-transition hypothesis at each shared vertex.
-/
structure PathLocalTransitionModelWeakContinuationSkeleton
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g)
    {x : X} (p : Path x₀ x) where
  /-- Number of subintervals in the subdivision. -/
  length : ℕ
  /-- The subdivision has at least one subinterval. -/
  length_pos : 0 < length
  /-- Ordered path parameters at the vertices of the subdivision. -/
  parameterAt : Fin (length + 1) → unitInterval
  /-- The subdivision begins at the initial parameter. -/
  parameterAt_zero : parameterAt 0 = 0
  /-- The subdivision ends at the terminal parameter. -/
  parameterAt_last : parameterAt (Fin.last length) = 1
  /-- The parameters are weakly increasing. -/
  parameterAt_mono :
    ∀ k : Fin length,
      (parameterAt k.castSucc : ℝ) ≤ (parameterAt k.succ : ℝ)
  /-- The local-transition model center attached to each subdivision vertex. -/
  centerAt : Fin (length + 1) → X
  /-- Each sampled subdivision point lies in its attached selected model. -/
  sample_mem_model_domain :
    ∀ i,
      p (parameterAt i) ∈ (localModels.chartAt (centerAt i)).domain
  /--
  Each closed subinterval of the path lies in the selected model domain
  attached to its left vertex.
  -/
  path_segment_mem_model_domain :
    ∀ k : Fin length, ∀ t : unitInterval,
      (parameterAt k.castSucc : ℝ) ≤ (t : ℝ) →
      (t : ℝ) ≤ (parameterAt k.succ : ℝ) →
      p t ∈ (localModels.chartAt (centerAt k.castSucc)).domain
  /-- The endpoint lies in the terminal selected model domain. -/
  terminal_endpoint_mem_domain :
    x ∈ (localModels.chartAt (centerAt (Fin.last length))).domain

namespace PathLocalTransitionModelWeakContinuationSkeleton

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {x : X} {p : Path x₀ x}

omit [RiemannSurface X] in
/--
The handoff point between consecutive weak subdivision pieces lies in the
overlap of the two attached local-transition model domains.

%%handwave
name:
  Every handoff point lies in the adjacent chart overlap
statement:
  For a finite continuation skeleton along $p$, the subdivision point $p(t_{k+1})$ belongs to the domains of both local models centered at the vertices $k$ and $k+1$.
proof:
  The segment-coverage condition puts the right endpoint of segment $k$ in the left chart domain, while the sampling condition puts it in the chart domain selected at vertex $k+1$.
-/
theorem transitionPoint_mem_adjacent_overlap
    (S :
      PathLocalTransitionModelWeakContinuationSkeleton x₀ g localModels p)
    (k : Fin S.length) :
    p (S.parameterAt k.succ) ∈
      (localModels.chartAt (S.centerAt k.castSucc)).domain ∩
        (localModels.chartAt (S.centerAt k.succ)).domain := by
  constructor
  · exact S.path_segment_mem_model_domain k (S.parameterAt k.succ)
      (S.parameterAt_mono k) le_rfl
  · exact S.sample_mem_model_domain k.succ

omit [RiemannSurface X] in
/--
The componentwise local-transition atlas supplies local real-Mobius handoff
data at each shared subdivision vertex of a weak skeleton.

%%handwave
name:
  Local real Möbius transition data exist at every handoff
statement:
  At each subdivision point $p(t_{k+1})$ of a weak continuation skeleton, there is a neighborhood and a real Möbius transformation carrying the local upper-half-plane chart used on segment $k$ to the chart used on segment $k+1$.
proof:
  The handoff point lies in the overlap of the two chart domains, so apply the local real Möbius transition property of the selected atlas.
-/
theorem transitionData_nonempty_at_handoff
    (S :
      PathLocalTransitionModelWeakContinuationSkeleton x₀ g localModels p)
    (k : Fin S.length) :
    Nonempty
      (HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt (S.centerAt k.castSucc))
        (localModels.chartAt (S.centerAt k.succ))
        (p (S.parameterAt k.succ))) :=
  localModels.transition_localRealMobius
    (S.centerAt k.castSucc) (S.centerAt k.succ)
    (p (S.parameterAt k.succ))
    (S.transitionPoint_mem_adjacent_overlap k)

end PathLocalTransitionModelWeakContinuationSkeleton

/--
A weak finite subdivision skeleton together with explicit local real-Mobius
transition data at every handoff point.

This is the compactness-plus-componentwise-overlap part of path continuation.
It still does not choose the accumulated Mobius products, nor does it anchor
the initial branch to the basepoint normalization.
-/
structure PathLocalTransitionModelWeakHandoffSkeleton
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g)
    {x : X} (p : Path x₀ x) extends
      PathLocalTransitionModelWeakContinuationSkeleton x₀ g localModels p where
  /-- The local transition selected at each finite handoff point. -/
  transitionAt :
    ∀ k : Fin length,
      HyperbolicLocalChart.LocalRealMobiusTransitionData
        (localModels.chartAt (centerAt k.castSucc))
        (localModels.chartAt (centerAt k.succ))
        (p (parameterAt k.succ))

namespace PathLocalTransitionModelWeakHandoffSkeleton

variable {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {x : X} {p : Path x₀ x}

omit [RiemannSurface X] in
/-- Forget the explicit handoff representatives from a weak handoff skeleton.

%%handwave
name:
  Forgetting handoff representatives preserves the subdivision length
statement:
  Removing the chosen real Möbius transformations from a weak handoff skeleton does not change its number of path segments.
proof:
  The underlying weak continuation skeleton retains the same length field.
-/
@[simp]
theorem toWeak_length
    (S :
      PathLocalTransitionModelWeakHandoffSkeleton x₀ g localModels p) :
    S.toPathLocalTransitionModelWeakContinuationSkeleton.length = S.length :=
  rfl

omit [RiemannSurface X] in
/-- Each selected handoff representative is valid at the corresponding vertex.

%%handwave
name:
  A handoff point belongs to its transition neighborhood
statement:
  For every handoff index $k$, the point $p(t_{k+1})$ belongs to the neighborhood on which the chosen real Möbius transition between the adjacent charts is valid.
proof:
  This membership is part of the selected local transition data at index $k$.
-/
theorem transitionAt_mem_neighborhood
    (S :
      PathLocalTransitionModelWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) :
    p (S.parameterAt k.succ) ∈ (S.transitionAt k).neighborhood :=
  (S.transitionAt k).mem_neighborhood

omit [RiemannSurface X] in
/-- Each selected handoff neighborhood lies in the adjacent chart overlap.

%%handwave
name:
  A handoff neighborhood lies in the adjacent chart overlap
statement:
  The neighborhood chosen at handoff $k$ is contained in the intersection of the chart domains used on segments $k$ and $k+1$.
proof:
  This inclusion is part of the local real Möbius transition data at the handoff.
-/
theorem transitionAt_subset_overlap
    (S :
      PathLocalTransitionModelWeakHandoffSkeleton x₀ g localModels p)
    (k : Fin S.length) :
    (S.transitionAt k).neighborhood ⊆
      (localModels.chartAt (S.centerAt k.castSucc)).domain ∩
        (localModels.chartAt (S.centerAt k.succ)).domain :=
  (S.transitionAt k).subset_overlap

end PathLocalTransitionModelWeakHandoffSkeleton

omit [RiemannSurface X] in
/--
Choose explicit componentwise local-transition handoff data for every shared
vertex of a weak continuation skeleton.
-/
noncomputable def PathLocalTransitionModelWeakContinuationSkeleton.toWeakHandoffSkeleton
    {x₀ : X} {g : HyperbolicMetric X}
    {localModels : HyperbolicLocalModelLocalTransitionAtlas X g}
    {x : X} {p : Path x₀ x}
    (S :
      PathLocalTransitionModelWeakContinuationSkeleton x₀ g localModels p) :
    PathLocalTransitionModelWeakHandoffSkeleton x₀ g localModels p where
  toPathLocalTransitionModelWeakContinuationSkeleton := S
  transitionAt := fun k =>
    Classical.choice (S.transitionData_nonempty_at_handoff k)

omit [RiemannSurface X] in
/--
Compactness of the unit interval gives a finite weak continuation skeleton
subordinate to the selected local-transition model domains along any path.

This proves the finite-subdivision part of analytic continuation.  It does not
yet remove repeated subdivision vertices or prove homotopy/loop invariance of
the accumulated Mobius products.

%%handwave
name:
  Every path admits a finite local-model continuation skeleton
statement:
  For any path $p:[0,1]\to X$ and any atlas of local upper-half-plane models, there exist subdivision parameters $0=t_0<\cdots<t_n=1$ and chart centers $c_i$ such that $p(t_i)$ lies in the chart centered at $c_i$ and each subpath $p([t_i,t_{i+1}])$ remains in the chart centered at $c_i$.
proof:
  The inverse images under $p$ of the selected chart domains form an open cover of $[0,1]$. Compactness supplies a finite monotone subdivision subordinate to this cover; choose at each subdivision vertex a covering chart and use the subordinate interval containment for each segment.
-/
theorem exists_pathLocalTransitionModelWeakContinuationSkeleton
    {x₀ : X} {g : HyperbolicMetric X}
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g)
    {x : X} (p : Path x₀ x) :
    Nonempty
      (PathLocalTransitionModelWeakContinuationSkeleton x₀ g localModels p) := by
  classical
  let c : unitInterval → Set unitInterval :=
    fun s => p ⁻¹' (localModels.chartAt (p s)).domain
  have hc_open : ∀ s, IsOpen (c s) := by
    intro s
    exact (localModels.chartAt (p s)).isOpen_domain.preimage p.continuous
  have hc_cover : Set.univ ⊆ ⋃ s, c s := by
    intro r _hr
    exact Set.mem_iUnion.mpr
      ⟨r, localModels.mem_chartAt_domain (p r)⟩
  obtain ⟨tNat, ht0, htmono, ⟨m, hm⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (c := c) hc_open hc_cover
  have htlast : tNat m = 1 := hm m le_rfl
  have hmpos : 0 < m := by
    by_contra hpos
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos hpos
    have h01 : (0 : unitInterval) = 1 := by
      calc
        (0 : unitInterval) = tNat 0 := ht0.symm
        _ = tNat m := by rw [hm0]
        _ = 1 := htlast
    have hreal : (0 : ℝ) = 1 := by
      simpa using congrArg (fun t : unitInterval => (t : ℝ)) h01
    norm_num at hreal
  let parameterAt : Fin (m + 1) → unitInterval := fun i => tNat i
  let segmentCenter : ℕ → X := fun n => p (Classical.choose (hsub n))
  let centerAt : Fin (m + 1) → X := fun i =>
    if h : (i : ℕ) < m then segmentCenter i else x
  refine ⟨
    { length := m
      length_pos := hmpos
      parameterAt := parameterAt
      parameterAt_zero := by
        ext
        simpa [parameterAt] using congrArg (fun t : unitInterval => (t : ℝ)) ht0
      parameterAt_last := by
        ext
        simpa [parameterAt] using congrArg (fun t : unitInterval => (t : ℝ)) htlast
      parameterAt_mono := ?_
      centerAt := centerAt
      sample_mem_model_domain := ?_
      path_segment_mem_model_domain := ?_
      terminal_endpoint_mem_domain := ?_ }⟩
  · intro k
    exact htmono (Nat.le_succ k)
  · intro i
    by_cases hi : (i : ℕ) < m
    · have hcover := Classical.choose_spec (hsub (i : ℕ))
      have hmemIcc : tNat (i : ℕ) ∈
          Set.Icc (tNat (i : ℕ)) (tNat ((i : ℕ) + 1)) := by
        constructor
        · exact le_rfl
        · exact htmono (Nat.le_succ (i : ℕ))
      have hdomain :
          p (tNat (i : ℕ)) ∈
            (localModels.chartAt (segmentCenter (i : ℕ))).domain :=
        hcover hmemIcc
      simpa [parameterAt, centerAt, segmentCenter, hi] using hdomain
    · have hle : (i : ℕ) ≤ m := Nat.le_of_lt_succ i.isLt
      have hge : m ≤ (i : ℕ) := le_of_not_gt hi
      have hval : (i : ℕ) = m := le_antisymm hle hge
      have hi_last : i = Fin.last m := by
        ext
        exact hval
      have hpoint : p (parameterAt i) = x := by
        rw [hi_last]
        simp [parameterAt, htlast, p.target]
      have hcenter : centerAt i = x := by
        rw [hi_last]
        simp [centerAt]
      simpa [hpoint, hcenter] using localModels.mem_chartAt_domain x
  · intro k t ht_left ht_right
    have hk : ((k.castSucc : Fin (m + 1)) : ℕ) < m := k.isLt
    have hcover := Classical.choose_spec (hsub (k : ℕ))
    have hmemIcc : t ∈ Set.Icc (tNat (k : ℕ)) (tNat ((k : ℕ) + 1)) := by
      constructor
      · simpa [parameterAt] using ht_left
      · simpa [parameterAt] using ht_right
    have hdomain :
        p t ∈ (localModels.chartAt (segmentCenter (k : ℕ))).domain :=
      hcover hmemIcc
    simpa [parameterAt, centerAt, segmentCenter, hk] using hdomain
  · have hcenter_last : centerAt (Fin.last m) = x := by
      simp [centerAt]
    simpa [hcenter_last] using localModels.mem_chartAt_domain x

omit [RiemannSurface X] in
/--
Every path admits a finite weak handoff skeleton: compactness gives the
subdivision, and the componentwise local-transition atlas supplies real-Mobius
transition data at the handoffs.

%%handwave
name:
  Every path admits a finite skeleton with real Möbius handoffs
statement:
  For any path $p:[0,1]\to X$ through an atlas whose chart overlaps are locally real Möbius, there is a finite subordinate continuation skeleton together with a chosen local real Möbius transition at every subdivision handoff.
proof:
  First choose a finite subordinate continuation skeleton. At each handoff, the point lies in the adjacent chart overlap, so choose the local real Möbius transition data supplied by the atlas.
-/
theorem exists_pathLocalTransitionModelWeakHandoffSkeleton
    {x₀ : X} {g : HyperbolicMetric X}
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g)
    {x : X} (p : Path x₀ x) :
    Nonempty
      (PathLocalTransitionModelWeakHandoffSkeleton x₀ g localModels p) :=
  (exists_pathLocalTransitionModelWeakContinuationSkeleton localModels p).map
    PathLocalTransitionModelWeakContinuationSkeleton.toWeakHandoffSkeleton

omit [RiemannSurface X] in
/--
One local-transition handoff updates the accumulated branch representative by
right-multiplying with the inverse transition representative.

%%handwave
name:
  Updating an accumulated Möbius factor preserves the branch value
statement:
  Suppose $V(y)=T\cdot U(y)$ on a transition neighborhood. Then for every accumulated real Möbius transformation $M$ and every point $y$ in that neighborhood, $(MT^{-1})\cdot V(y)=M\cdot U(y)$.
proof:
  Substitute $V(y)=T\cdot U(y)$, use associativity of the Möbius action, and cancel $T^{-1}T$.
-/
theorem localRealMobiusTransitionData_accumulated_handoff
    {g : HyperbolicMetric X} {U V : HyperbolicLocalChart X g}
    {x y : X}
    (T : HyperbolicLocalChart.LocalRealMobiusTransitionData U V x)
    (hy : y ∈ T.neighborhood) (M : RealMobiusRepresentative) :
    realMobiusRepresentativeAction (M * T.representative⁻¹)
        (V.toUpperHalfPlane y) =
      realMobiusRepresentativeAction M (U.toUpperHalfPlane y) := by
  rw [T.transition_eq y hy, realMobiusRepresentativeAction_mul]
  simp [realMobiusRepresentativeAction]

/--
Equal PSL classes of real Mobius representatives have the same action on the
upper half-plane.

%%handwave
name:
  Equal projective classes have the same upper-half-plane action
statement:
  If two real Möbius representatives $A$ and $B$ define the same element of $\mathrm{PSL}_2(\mathbb R)$, then $A\cdot z=B\cdot z$ for every $z\in\mathbb H$.
proof:
  The action of a representative factors through its projective class, so equality of the classes gives equality of their actions.
-/
theorem realMobiusRepresentativeAction_eq_of_projection_eq
    {A B : RealMobiusRepresentative}
    (h : realMobiusProjection A = realMobiusProjection B) (z : ℍ) :
    realMobiusRepresentativeAction A z =
      realMobiusRepresentativeAction B z := by
  rw [← realMobiusAction_realMobiusProjection A z,
    ← realMobiusAction_realMobiusProjection B z, h]

/--
Equal PSL classes of real Mobius representatives have inverse lifts with the
same action on the upper half-plane.

%%handwave
name:
  Inverses of equal projective classes have the same action
statement:
  If $[A]=[B]$ in $\mathrm{PSL}_2(\mathbb R)$, then $A^{-1}\cdot z=B^{-1}\cdot z$ for every $z\in\mathbb H$.
proof:
  Taking inverses gives $[A^{-1}]=[B^{-1}]$; equal projective classes act identically on $\mathbb H$.
-/
theorem realMobiusRepresentativeAction_inv_eq_of_projection_eq
    {A B : RealMobiusRepresentative}
    (h : realMobiusProjection A = realMobiusProjection B) (z : ℍ) :
    realMobiusRepresentativeAction A⁻¹ z =
      realMobiusRepresentativeAction B⁻¹ z := by
  have hInv :
      realMobiusProjection A⁻¹ = realMobiusProjection B⁻¹ := by
    simpa using congrArg Inv.inv h
  exact realMobiusRepresentativeAction_eq_of_projection_eq hInv z

/--
Retarget local transition data across definitional/equality changes in its
two charts and marked point, keeping the Mobius representative unchanged.
-/
def localRealMobiusTransitionData_congr
    {g : HyperbolicMetric X}
    {U U' V V' : HyperbolicLocalChart X g} {x x' : X}
    (hU : U' = U) (hV : V' = V) (hx : x' = x)
    (T : HyperbolicLocalChart.LocalRealMobiusTransitionData U V x) :
    HyperbolicLocalChart.LocalRealMobiusTransitionData U' V' x' where
  neighborhood := T.neighborhood
  isOpen_neighborhood := T.isOpen_neighborhood
  mem_neighborhood := by
    simpa [hx] using T.mem_neighborhood
  subset_overlap := by
    intro y hy
    simpa [hU, hV] using T.subset_overlap hy
  representative := T.representative
  transition_eq := by
    intro y hy
    simpa [hU, hV] using T.transition_eq y hy

omit [RiemannSurface X] in
/--
%%handwave
name:
  Transporting transition data across equal charts preserves its representative
statement:
  If the source chart, target chart, and basepoint of local transition data are replaced by equal objects, the transported transition data use the same real Möbius representative.
proof:
  Substitute the three equalities. The transported transition is then the
  original transition, so its real Möbius representative is unchanged.
-/
@[simp]
theorem localRealMobiusTransitionData_congr_representative
    {g : HyperbolicMetric X}
    {U U' V V' : HyperbolicLocalChart X g} {x x' : X}
    (hU : U' = U) (hV : V' = V) (hx : x' = x)
    (T : HyperbolicLocalChart.LocalRealMobiusTransitionData U V x) :
    (localRealMobiusTransitionData_congr hU hV hx T).representative =
      T.representative :=
  rfl

omit [RiemannSurface X] in
/--
Move the marked point of local transition data to another point in the same
transition neighborhood, keeping the same Mobius representative.
-/
def localRealMobiusTransitionData_recenter
    {g : HyperbolicMetric X}
    {U V : HyperbolicLocalChart X g} {x y : X}
    (T : HyperbolicLocalChart.LocalRealMobiusTransitionData U V x)
    (hy : y ∈ T.neighborhood) :
    HyperbolicLocalChart.LocalRealMobiusTransitionData U V y where
  neighborhood := T.neighborhood
  isOpen_neighborhood := T.isOpen_neighborhood
  mem_neighborhood := hy
  subset_overlap := T.subset_overlap
  representative := T.representative
  transition_eq := T.transition_eq

omit [RiemannSurface X] in
/--
%%handwave
name:
  Recentering transition data preserves its Möbius representative
statement:
  If local transition data based at $x$ are recentered at a point $y$ in the same transition neighborhood, the real Möbius representative remains unchanged.
proof:
  The recentered data retain the original neighborhood and transition formula, including the same representative.
-/
@[simp]
theorem localRealMobiusTransitionData_recenter_representative
    {g : HyperbolicMetric X}
    {U V : HyperbolicLocalChart X g} {x y : X}
    (T : HyperbolicLocalChart.LocalRealMobiusTransitionData U V x)
    (hy : y ∈ T.neighborhood) :
    (localRealMobiusTransitionData_recenter T hy).representative =
      T.representative :=
  rfl

omit [RiemannSurface X] in
/--
The identity representative gives the local transition from a chart to itself.

This is the terminal-extension handoff used when a continued path is followed
by a local path that stays inside the same terminal chart.
-/
def localRealMobiusTransitionData_self
    {g : HyperbolicMetric X} (U : HyperbolicLocalChart X g)
    {x : X} (hx : x ∈ U.domain) :
    HyperbolicLocalChart.LocalRealMobiusTransitionData U U x where
  neighborhood := U.domain
  isOpen_neighborhood := U.isOpen_domain
  mem_neighborhood := hx
  subset_overlap := by
    intro y hy
    exact ⟨hy, hy⟩
  representative := 1
  transition_eq := by
    intro y hy
    simp [realMobiusRepresentativeAction_one]

omit [RiemannSurface X] in
/--
Invert local real-Mobius transition data.

If `V = A ∘ U` near the marked overlap point, then
`U = A⁻¹ ∘ V` on the same neighborhood.
-/
def localRealMobiusTransitionData_symm
    {g : HyperbolicMetric X}
    {U V : HyperbolicLocalChart X g} {x : X}
    (T : HyperbolicLocalChart.LocalRealMobiusTransitionData U V x) :
    HyperbolicLocalChart.LocalRealMobiusTransitionData V U x where
  neighborhood := T.neighborhood
  isOpen_neighborhood := T.isOpen_neighborhood
  mem_neighborhood := T.mem_neighborhood
  subset_overlap := by
    intro y hy
    exact ⟨(T.subset_overlap hy).2, (T.subset_overlap hy).1⟩
  representative := T.representative⁻¹
  transition_eq := by
    intro y hy
    rw [T.transition_eq y hy]
    simp [realMobiusRepresentativeAction]

omit [RiemannSurface X] in
/--
Compose local real-Mobius transition data.

If `V = A ∘ U` and `W = B ∘ V` near the same marked point, then
`W = (B * A) ∘ U` near that point.  The neighborhood is the intersection of
the two transition neighborhoods, so this is a purely local cocycle statement.
-/
def localRealMobiusTransitionData_trans
    {g : HyperbolicMetric X}
    {U V W : HyperbolicLocalChart X g} {x : X}
    (TUV : HyperbolicLocalChart.LocalRealMobiusTransitionData U V x)
    (TVW : HyperbolicLocalChart.LocalRealMobiusTransitionData V W x) :
    HyperbolicLocalChart.LocalRealMobiusTransitionData U W x where
  neighborhood := TUV.neighborhood ∩ TVW.neighborhood
  isOpen_neighborhood :=
    TUV.isOpen_neighborhood.inter TVW.isOpen_neighborhood
  mem_neighborhood := ⟨TUV.mem_neighborhood, TVW.mem_neighborhood⟩
  subset_overlap := by
    intro y hy
    exact ⟨(TUV.subset_overlap hy.1).1, (TVW.subset_overlap hy.2).2⟩
  representative := TVW.representative * TUV.representative
  transition_eq := by
    intro y hy
    rw [TVW.transition_eq y hy.2, TUV.transition_eq y hy.1]
    simp [realMobiusRepresentativeAction_mul]

omit [RiemannSurface X] in
/--
%%handwave
name:
  Representative of the reversed local transition
statement:
  Reversing local transition data from $U$ to $V$ gives transition data from $V$ to $U$ whose representative is $T^{-1}$ when the original representative is $T$.
proof:
  The reversed transition is defined using the inverse Möbius transformation.
-/
@[simp]
theorem localRealMobiusTransitionData_symm_representative
    {g : HyperbolicMetric X}
    {U V : HyperbolicLocalChart X g} {x : X}
    (T : HyperbolicLocalChart.LocalRealMobiusTransitionData U V x) :
    (localRealMobiusTransitionData_symm T).representative =
      T.representative⁻¹ :=
  rfl

omit [RiemannSurface X] in
/--
%%handwave
name:
  Representative of a composite local transition
statement:
  If the transition from $U$ to $V$ is represented by $T_{UV}$ and the transition from $V$ to $W$ by $T_{VW}$, then their composite transition from $U$ to $W$ is represented by $T_{VW}T_{UV}$.
proof:
  Apply the $U$-to-$V$ transition first and the $V$-to-$W$ transition second; composition of the actions corresponds to the product $T_{VW}T_{UV}$.
-/
@[simp]
theorem localRealMobiusTransitionData_trans_representative
    {g : HyperbolicMetric X}
    {U V W : HyperbolicLocalChart X g} {x : X}
    (TUV : HyperbolicLocalChart.LocalRealMobiusTransitionData U V x)
    (TVW : HyperbolicLocalChart.LocalRealMobiusTransitionData V W x) :
    (localRealMobiusTransitionData_trans TUV TVW).representative =
      TVW.representative * TUV.representative :=
  rfl

/--
A weak handoff skeleton anchored at the basepoint chart.

The compactness subdivision may choose an arbitrary chart for the first
positive-length segment.  This record adds the missing normalized initial
handoff from the selected basepoint chart to that first segment chart at
`x₀`.
-/
structure PathLocalTransitionModelBasedWeakHandoffSkeleton
    (x₀ : X) (g : HyperbolicMetric X)
    (localModels : HyperbolicLocalModelLocalTransitionAtlas X g)
    {x : X} (p : Path x₀ x) extends
      PathLocalTransitionModelWeakHandoffSkeleton x₀ g localModels p where
  /-- The basepoint-chart transition into the chart used by the first segment. -/
  initialTransition :
    HyperbolicLocalChart.LocalRealMobiusTransitionData
      (localModels.chartAt x₀)
      (localModels.chartAt (centerAt 0))
      x₀

end HyperbolicMetric

end

end JJMath
