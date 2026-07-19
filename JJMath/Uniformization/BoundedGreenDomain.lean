import JJMath.Uniformization.EvansPotential
import JJMath.Uniformization.H1ZeroExhaustion
import JJMath.Uniformization.PuncturedGreenConjugate

/-!
# Green data on a bounded exhaustion domain

This file converts the negative Dirichlet Green potentials produced by the
annular Perron construction into intrinsic positive Green data on the open
Riemann surface given by the domain.  It is the bounded-domain input to
Hubbard's normalized exhaustion argument.
-/

open Set Filter
open scoped Manifold ContDiff Topology

namespace JJMath.Uniformization

noncomputable section

/-- The open submanifold carried by a smooth boundary domain. -/
def SmoothBoundaryDomain.openCarrier
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Ω : SmoothBoundaryDomain X) : TopologicalSpace.Opens X :=
  ⟨Ω.carrier, Ω.isOpen⟩

/-- A path-connected smooth boundary domain, regarded as an open
submanifold, is a Riemann surface.

%%handwave
name: Riemann-surface structure on an open smooth domain
statement:
  If $\Omega$ is a nonempty path-connected smooth domain in a Riemann surface $X$, then its open carrier, with the induced charts, is a Riemann surface.
proof:
  Path connectedness gives connectedness of the open carrier. Restrict the ambient complex atlas to this nonempty connected open subset.
-/
theorem SmoothBoundaryDomain.openCarrier_riemannSurface
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (Ω : SmoothBoundaryDomain X) [PathConnectedSpace Ω.carrier]
    [Nonempty Ω.carrier] :
    RiemannSurface Ω.openCarrier := by
  have hnonempty : (Ω.openCarrier : Set X).Nonempty := by
    rcases (inferInstance : Nonempty Ω.carrier) with ⟨x⟩
    exact ⟨x, x.property⟩
  have hpre : IsPreconnected (Ω.openCarrier : Set X) := by
    simpa [SmoothBoundaryDomain.openCarrier] using
      (isPreconnected_iff_preconnectedSpace.mpr
        (inferInstance : PreconnectedSpace Ω.carrier))
  exact riemannSurface_openSubset Ω.openCarrier
    hnonempty hpre

noncomputable instance SmoothBoundaryDomain.openCarrier.instRiemannSurface
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (Ω : SmoothBoundaryDomain X) [PathConnectedSpace Ω.carrier]
    [Nonempty Ω.carrier] :
    RiemannSurface Ω.openCarrier :=
  Ω.openCarrier_riemannSurface

/--
%%handwave
name:
  Relatively compact open domains are noncompact as open surfaces
statement:
  A nonempty relatively compact open domain in a connected noncompact
  surface is noncompact when regarded as an open surface in its own right.
proof:
  If the open surface were compact, its image in the ambient Hausdorff
  surface would be compact and hence closed.  It would then be a nonempty
  clopen subset of a connected surface, so it would be the whole surface,
  contradicting ambient noncompactness.
-/
theorem SmoothBoundaryDomain.not_compactSpace_openCarrier
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    (Ω : SmoothBoundaryDomain X) (hX : ¬ CompactSpace X) :
    ¬ CompactSpace Ω.openCarrier := by
  intro hcompact
  letI : CompactSpace Ω.openCarrier := hcompact
  have hcarrier_compact : IsCompact Ω.carrier := by
    have himage : IsCompact
        (((↑) : Ω.openCarrier → X) '' Set.univ) :=
      isCompact_univ.image continuous_subtype_val
    simpa [SmoothBoundaryDomain.openCarrier] using himage
  have hcarrier_univ : Ω.carrier = Set.univ :=
    IsClopen.eq_univ
      ⟨hcarrier_compact.isClosed, Ω.isOpen⟩ Ω.nonempty
  apply hX
  rw [← isCompact_univ_iff]
  simpa [hcarrier_univ] using hcarrier_compact

/-- A bounded negative Green potential is strictly negative at every point
of its domain other than its pole.

%%handwave
name: Strict negativity of a bounded Green potential
statement:
  Let $G$ be a negative Green potential on a path-connected bounded domain $\Omega$, with pole $p\in\Omega$. Then $G(x)<0$ for every $x\in\Omega\setminus\{p\}$.
proof:
  The punctured open domain is connected and $G\le0$ is harmonic there. If $G$ vanished at an interior point, the strong maximum principle would make it identically zero on the punctured domain, contradicting the logarithmic divergence at the pole.
-/
theorem BoundedNegativeGreenPotential.strict_negative_on_domain
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {Ω : SmoothBoundaryDomain X} {p : X}
    [PathConnectedSpace Ω.carrier]
    (G : BoundedNegativeGreenPotential X Ω p)
    (hp : p ∈ Ω.carrier) :
    ∀ x ∈ Ω.carrier, x ≠ p → G.toFun x < 0 := by
  letI : Nonempty Ω.carrier := ⟨⟨p, hp⟩⟩
  let U : TopologicalSpace.Opens X := Ω.openCarrier
  letI : RiemannSurface U :=
    Ω.openCarrier_riemannSurface
  let pU : U := ⟨p, hp⟩
  have hpunc_pre_U : IsPreconnected {x : U | x ≠ pU} :=
    punctured_riemannSurface_preconnected U pU
  have hpunc_pre : IsPreconnected (Ω.carrier \ {p}) := by
    have himage :
        IsPreconnected (((↑) : U → X) '' {x : U | x ≠ pU}) :=
      hpunc_pre_U.image ((↑) : U → X) continuous_subtype_val.continuousOn
    have himage_eq :
        ((↑) : U → X) '' {x : U | x ≠ pU} = Ω.carrier \ {p} := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        refine ⟨y.property, ?_⟩
        intro hval
        apply hy
        exact Subtype.ext hval
      · intro hx
        refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
        intro hsub
        exact hx.2 (congrArg Subtype.val hsub)
    rw [himage_eq] at himage
    exact himage
  have hpunc_open : IsOpen (Ω.carrier \ {p}) :=
    Ω.isOpen.sdiff isClosed_singleton
  let u : X → ℝ := fun x ↦ -G.toFun x
  have hu_harm : IsHarmonicOnSurface (Ω.carrier \ {p}) u := by
    simpa [u] using harmonicOnSurface_neg G.harmonic_away_pole
  have hu_nonneg : ∀ x ∈ Ω.carrier, 0 ≤ u x := by
    intro x hx
    exact neg_nonneg.mpr (G.nonpositive_on_domain x hx)
  intro x hxΩ hxp
  have hxU : x ∈ Ω.carrier \ {p} := ⟨hxΩ, by simpa using hxp⟩
  have hux_nonneg : 0 ≤ u x := hu_nonneg x hxΩ
  by_contra hnot_neg
  have hG_nonneg : 0 ≤ G.toFun x := le_of_not_gt hnot_neg
  have hG_zero : G.toFun x = 0 :=
    le_antisymm (G.nonpositive_on_domain x hxΩ) hG_nonneg
  have hux_zero : u x = 0 := by simp [u, hG_zero]
  have hmax : IsMaxOn (fun y : X ↦ -u y) (Ω.carrier \ {p}) x := by
    intro y hy
    have hy_nonneg : 0 ≤ u y := hu_nonneg y hy.1
    simpa [hux_zero] using neg_nonpos.mpr hy_nonneg
  have hconst :
      Set.EqOn (fun y : X ↦ -u y) (fun _ ↦ -u x)
        (Ω.carrier \ {p}) :=
    harmonicOnSurface_eqOn_of_isPreconnected_of_isMaxOn
      hpunc_open hpunc_pre (harmonicOnSurface_neg hu_harm) hxU hmax
  have hzero : Set.EqOn G.toFun (fun _ : X ↦ 0) (Ω.carrier \ {p}) := by
    intro y hy
    have hy_eq : -u y = -u x := hconst hy
    have huy : u y = u x := neg_inj.mp hy_eq
    simpa [u, hux_zero] using congrArg Neg.neg huy
  have hevent_zero : G.toFun =ᶠ[𝓝[Ω.carrier \ {p}] p] fun _ : X ↦ 0 := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact hzero hy
  have htendsto_zero :
      Filter.Tendsto G.toFun (𝓝[Ω.carrier \ {p}] p) (𝓝 0) :=
    hevent_zero.tendsto
  haveI : Filter.NeBot (𝓝[Ω.carrier \ {p}] p) := by
    have hpunc_neBot_U : Filter.NeBot (𝓝[≠] pU) :=
      punctured_nhds_neBot_riemannSurface U pU
    have hfilter :
        𝓝[≠] pU =
          Filter.comap ((↑) : U → X) (𝓝[Ω.carrier \ {p}] p) := by
      have himage_eq :
          ((↑) : U → X) '' ({pU}ᶜ : Set U) = Ω.carrier \ {p} := by
        ext y
        constructor
        · rintro ⟨z, hz, rfl⟩
          refine ⟨z.property, ?_⟩
          intro hval
          apply hz
          exact Subtype.ext hval
        · intro hy
          refine ⟨⟨y, hy.1⟩, ?_, rfl⟩
          intro hsub
          exact hy.2 (congrArg Subtype.val hsub)
      rw [nhdsWithin_subtype]
      have hnhds :
          𝓝[((↑) : U → X) '' ({pU}ᶜ : Set U)] (pU : X) =
            𝓝[Ω.carrier \ {p}] p := by
        rw [himage_eq]
      exact congrArg (Filter.comap ((↑) : U → X)) hnhds
    have hmap := hpunc_neBot_U.map ((↑) : U → X)
    rw [hfilter, Filter.map_comap] at hmap
    exact hmap.mono inf_le_left
  exact (not_tendsto_nhds_of_tendsto_atBot
    G.tends_to_neg_infinity_at_pole (0 : ℝ)) htendsto_zero

/-- The negative of a bounded Green potential has the usual removable
logarithmic pole when the domain is regarded as an open Riemann surface.

%%handwave
name: Logarithmic singularity on the open carrier
statement:
  Let $G$ be a bounded negative Green potential on $\Omega$ with pole $p\in\Omega$. In every pointed complex coordinate $\chi$ on the open carrier, there is a harmonic function $H$ on the chart source such that $-G(x)+\log|\chi(x)-\chi(p)|=H(x)$ near $p$ away from $p$.
proof:
  Restrict the logarithmic-singularity identity for $G$ from the ambient surface to the open subtype. Transport its harmonic correction through the inclusion and use the equality of the induced chart with the ambient coordinate near the pole.
-/
theorem BoundedNegativeGreenPotential.neg_logarithmic_singularity_openCarrier
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {Ω : SmoothBoundaryDomain X} {p : X}
    [PathConnectedSpace Ω.carrier]
    (G : BoundedNegativeGreenPotential X Ω p)
    (hp : p ∈ Ω.carrier) :
    let U := Ω.openCarrier
    let pU : U := ⟨p, hp⟩
    ∀ χ : PointedSurfaceCoordinate U pU,
      ∃ H : U → ℝ,
        IsHarmonicOnSurface χ.chart.source H ∧
          ∀ᶠ x : U in
              (nhdsWithin pU (χ.chart.source ∩ {x : U | x ≠ pU}) : Filter U),
            -G.toFun (x : X) + Real.log ‖χ.chart x - χ.chart pU‖ = H x := by
  letI : Nonempty Ω.carrier := ⟨⟨p, hp⟩⟩
  let U : TopologicalSpace.Opens X := Ω.openCarrier
  letI : RiemannSurface U :=
    Ω.openCarrier_riemannSurface
  let pU : U := ⟨p, hp⟩
  have hharm :
      IsHarmonicOnSurface {x : U | x ≠ pU}
        (fun x : U ↦ -G.toFun x) := by
    have hambient :
        IsHarmonicOnSurface (Ω.carrier \ {p})
          (fun x : X ↦ -G.toFun x) := by
      simpa using harmonicOnSurface_neg G.harmonic_away_pole
    have hrestrict :=
      harmonicOnSurface_openSubtype_of_ambient U hambient
    have hset :
        {x : U | (x : X) ∈ Ω.carrier \ {p}} =
          {x : U | x ≠ pU} := by
      ext x
      constructor
      · intro hx hxp
        exact hx.2 (congrArg Subtype.val hxp)
      · intro hxp
        exact ⟨x.property, by
          intro hxval
          apply hxp
          exact Subtype.ext hxval⟩
    rw [← hset]
    exact hrestrict
  apply logarithmic_singularity_of_harmonicOn_punctured_and_bounded_remainder
    (X := U) hharm
  intro χ
  have hU : Nonempty U := ⟨pU⟩
  rcases TopologicalSpace.Opens.chart_eq (H := ℂ) hU χ.chart_mem_atlas with
    ⟨q, hχchart⟩
  let E : OpenPartialHomeomorph X ℂ := chartAt ℂ (q : X)
  have hpE : p ∈ E.source := by
    have hpSub : pU ∈ (E.subtypeRestr hU).source := by
      rw [← hχchart]
      exact χ.base_mem_source
    simpa [E, OpenPartialHomeomorph.subtypeRestr_source] using hpSub
  let χX : PointedSurfaceCoordinate X p :=
    { chart := E
      chart_mem_atlas := chart_mem_atlas ℂ (q : X)
      base_mem_source := hpE }
  rcases G.logarithmic_zero χX with
    ⟨N, h, hN_open, hpN, _hNΩ, _hNE, hh, hnear⟩
  have hval_tendsto :
      Filter.Tendsto ((↑) : U → X)
        (nhdsWithin pU (χ.chart.source ∩ {x : U | x ≠ pU}))
        (nhdsWithin p (N ∩ {x : X | x ≠ p})) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact continuousAt_subtype_val.tendsto.mono_left inf_le_left
    · have hN_mem : ((↑) : U → X) ⁻¹' N ∈
          nhdsWithin pU (χ.chart.source ∩ {x : U | x ≠ pU}) :=
        mem_nhdsWithin_of_mem_nhds
          (continuousAt_subtype_val.preimage_mem_nhds
            (hN_open.mem_nhds hpN))
      filter_upwards [hN_mem, self_mem_nhdsWithin] with y hyN hy
      exact ⟨hyN, by
        intro hyp
        apply hy.2
        exact Subtype.ext hyp⟩
  have hnearU := hval_tendsto.eventually hnear
  have hh_cont : ContinuousAt h p :=
    (harmonicOnSurface_continuousOn hN_open hh).continuousAt
      (hN_open.mem_nhds hpN)
  have hboundX :
      ∀ᶠ y in nhds p, ‖h y‖ ≤ ‖h p‖ + 1 := by
    have hlt :
        ∀ᶠ y in nhds p, ‖h y‖ < ‖h p‖ + 1 :=
      hh_cont.norm.tendsto.eventually
        (Iio_mem_nhds (lt_add_one ‖h p‖))
    exact hlt.mono (fun _ hy ↦ hy.le)
  have hboundU :=
    (hval_tendsto.mono_right inf_le_left).eventually hboundX
  refine ⟨‖h p‖ + 1, ?_⟩
  filter_upwards [hnearU, hboundU] with y hy hhy
  have hχy : χ.chart y = E y := by
    rw [hχchart]
    rfl
  have hχp : χ.chart pU = E p := by
    rw [hχchart]
    rfl
  rw [hχy, hχp]
  have hy' :
      G.toFun (y : X) - Real.log ‖E (y : X) - E p‖ = h (y : X) := by
    simpa [χX] using hy
  rw [← hy'] at hhy
  calc
    ‖-G.toFun (y : X) + Real.log ‖E (y : X) - E p‖‖ =
        ‖-(G.toFun (y : X) - Real.log ‖E (y : X) - E p‖)‖ := by
          congr 1
          ring
    _ = ‖G.toFun (y : X) - Real.log ‖E (y : X) - E p‖‖ := norm_neg _
    _ ≤ ‖h p‖ + 1 := hhy

/-- On the open surface carried by a bounded domain, the negative Dirichlet
Green potential tends to zero along the cocompact filter.

%%handwave
name: Vanishing of a bounded Green potential at the ideal boundary
statement:
  Let $G$ be a bounded negative Green potential on a relatively compact domain $\Omega$, with pole $p\in\Omega$. On the open Riemann surface $\Omega$, the function $-G$ tends to $0$ along the cocompact filter.
proof:
  Extend $-G$ continuously to the compact closure, where it vanishes on the boundary. For any neighborhood of $0$, compactness gives a neighborhood of the boundary on which the values lie there; the complement of that neighborhood inside the open carrier is compact, which is exactly cocompact convergence.
-/
theorem BoundedNegativeGreenPotential.neg_tendsto_zero_cocompact_openCarrier
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {Ω : SmoothBoundaryDomain X} {p : X}
    [PathConnectedSpace Ω.carrier]
    (G : BoundedNegativeGreenPotential X Ω p)
    (hp : p ∈ Ω.carrier) :
    let U := Ω.openCarrier
    Filter.Tendsto (fun x : U ↦ -G.toFun x)
      (Filter.cocompact U) (nhds 0) := by
  letI : Nonempty Ω.carrier := ⟨⟨p, hp⟩⟩
  let U : TopologicalSpace.Opens X := Ω.openCarrier
  letI : RiemannSurface U :=
    Ω.openCarrier_riemannSurface
  rw [tendsto_def]
  intro s hs
  rcases mem_nhds_iff.mp hs with ⟨T, hTs, hTopen, hzeroT⟩
  let K : Set X := closure Ω.carrier
  let pK : K := ⟨p, subset_closure hp⟩
  let fK : K → ℝ := fun x ↦ -G.toFun x
  let puncturedK : Set K := {x : K | x ≠ pK}
  have hpuncturedK_open : IsOpen puncturedK := by
    simpa [puncturedK] using (isOpen_ne (x := pK) : IsOpen {x : K | x ≠ pK})
  have hfK_cont : ContinuousOn fK puncturedK := by
    have hcont_neg :
        ContinuousOn (fun x : X ↦ -G.toFun x)
          (closure Ω.carrier \ {p}) :=
      G.continuousOn_punctured_closure.neg
    refine hcont_neg.comp continuous_subtype_val.continuousOn ?_
    intro x hx
    refine ⟨x.property, ?_⟩
    intro hxval
    apply hx
    exact Subtype.ext hxval
  let O : Set K := puncturedK ∩ fK ⁻¹' T
  have hO_open : IsOpen O := by
    dsimp [O]
    exact hfK_cont.isOpen_inter_preimage hpuncturedK_open hTopen
  let bad : Set K := Oᶜ
  have hbad_compact : IsCompact bad := by
    haveI : CompactSpace K :=
      isCompact_iff_compactSpace.mp Ω.compact_closure
    exact hO_open.isClosed_compl.isCompact
  have hbad_subset_domain : ∀ x : K, x ∈ bad → (x : X) ∈ Ω.carrier := by
    intro x hxbad
    by_cases hxpK : x = pK
    · simpa [hxpK, pK] using hp
    · by_contra hxΩ
      have hxboundary : (x : X) ∈ Ω.boundary := by
        rw [SmoothBoundaryDomain.boundary, frontier]
        exact ⟨x.property, by simpa [Ω.isOpen.interior_eq] using hxΩ⟩
      have hGzero : G.toFun (x : X) = 0 := G.boundary_zero x hxboundary
      have hxO : x ∈ O := by
        refine ⟨hxpK, ?_⟩
        simpa [fK, hGzero] using hzeroT
      exact hxbad hxO
  let Bad := {x : K // x ∈ bad}
  let toU : Bad → U := fun x ↦
    ⟨(x : K), hbad_subset_domain x x.property⟩
  have htoU_cont : Continuous toU := by
    exact Continuous.subtype_mk
      (continuous_subtype_val.comp continuous_subtype_val)
      (fun x ↦ hbad_subset_domain x x.property)
  have hbad_range_compact : IsCompact (Set.range toU) := by
    haveI : CompactSpace Bad :=
      isCompact_iff_compactSpace.mp hbad_compact
    exact isCompact_range htoU_cont
  refine Filter.mem_of_superset hbad_range_compact.compl_mem_cocompact ?_
  intro y hy
  apply hTs
  let yK : K := ⟨(y : X), subset_closure y.property⟩
  have hyK_not_bad : yK ∉ bad := by
    intro hybad
    apply hy
    refine ⟨⟨yK, hybad⟩, ?_⟩
    apply Subtype.ext
    rfl
  have hyK_O : yK ∈ O := by
    simpa [bad] using hyK_not_bad
  exact hyK_O.2

/--
%%handwave
name:
  Bounded Dirichlet Green potentials as intrinsic Green functions
statement:
  Let \(\Omega\) be a path-connected relatively compact smooth domain and
  let \(p\in\Omega\).  The negative of a boundary-normalized Green potential
  on \(\Omega\) is a positive Green function on the open surface \(\Omega\),
  and every positive superlevel set together with the pole is compact.
proof:
  The maximum principle makes the potential strictly negative away from the
  pole.  Its logarithmic zero becomes a logarithmic pole after changing sign.
  Continuity up to the compact boundary and the zero boundary value imply
  convergence to zero along the cocompact filter, which makes every positive
  superlevel set compact.
-/
noncomputable def BoundedNegativeGreenPotential.toCompactSuperlevelOpenCarrier
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {Ω : SmoothBoundaryDomain X} {p : X}
    [PathConnectedSpace Ω.carrier]
    (G : BoundedNegativeGreenPotential X Ω p)
    (hp : p ∈ Ω.carrier) :
    CompactSuperlevelGreenFunctionWithPole Ω.openCarrier ⟨p, hp⟩ := by
  letI : Nonempty Ω.carrier := ⟨⟨p, hp⟩⟩
  let U : TopologicalSpace.Opens X := Ω.openCarrier
  letI : RiemannSurface U :=
    Ω.openCarrier_riemannSurface
  let pU : U := ⟨p, hp⟩
  let g : U → ℝ := fun x ↦ -G.toFun x
  have hharm : IsHarmonicOnSurface {x : U | x ≠ pU} g := by
    have hambient :
        IsHarmonicOnSurface (Ω.carrier \ {p})
          (fun x : X ↦ -G.toFun x) := by
      simpa using harmonicOnSurface_neg G.harmonic_away_pole
    have hrestrict := harmonicOnSurface_openSubtype_of_ambient U hambient
    have hset :
        {x : U | (x : X) ∈ Ω.carrier \ {p}} =
          {x : U | x ≠ pU} := by
      ext x
      constructor
      · intro hx hxp
        exact hx.2 (congrArg Subtype.val hxp)
      · intro hxp
        exact ⟨x.property, by
          intro hxval
          apply hxp
          exact Subtype.ext hxval⟩
    rw [← hset]
    exact hrestrict
  have hlog :
      ∀ χ : PointedSurfaceCoordinate U pU,
        ∃ H : U → ℝ,
          IsHarmonicOnSurface χ.chart.source H ∧
            ∀ᶠ x in nhdsWithin pU
                (χ.chart.source ∩ {x : U | x ≠ pU}),
              g x + Real.log ‖χ.chart x - χ.chart pU‖ = H x := by
    simpa [U, pU, g] using G.neg_logarithmic_singularity_openCarrier hp
  have hinfty : Filter.Tendsto g (nhdsWithin pU {x : U | x ≠ pU})
      Filter.atTop := by
    have ht := logarithmic_singularity_tendsto_atTop U pU hlog
    change Filter.Tendsto g (nhdsWithin pU ({pU}ᶜ : Set U))
      Filter.atTop at ht
    have hpunct : {x : U | x ≠ pU} = ({pU}ᶜ : Set U) := by
      ext x
      simp
    rw [hpunct]
    exact ht
  have hzero : Filter.Tendsto g (Filter.cocompact U) (nhds 0) := by
    simpa [U, g] using G.neg_tendsto_zero_cocompact_openCarrier hp
  refine
    { toFun := g
      positive_away_pole := ?_
      harmonic_away_pole := hharm
      tends_to_infinity_at_pole := hinfty
      logarithmic_singularity := hlog
      compact_positive_superlevel := ?_ }
  · intro x hxp
    exact neg_pos.mpr (G.strict_negative_on_domain hp x x.property (by
      intro hxval
      apply hxp
      exact Subtype.ext hxval))
  · intro a ha
    exact SmoothRelativelyCompactExhaustion.compact_adjoined_superlevel_of_tendsto_zero_cocompact_of_harmonicOn_punctured
      ha hzero hharm

/--
%%handwave
name:
  Bounded Green functions along a zero-cohomology exhaustion
statement:
  Let \((\Omega_n)\) be a pointed smooth exhaustion by path-connected
  relatively compact domains with vanishing first real de Rham cohomology.
  If the ambient surface is noncompact, then one can choose on every
  \(\Omega_n\) a positive Green function with the common pole whose positive
  superlevel sets are compact.
proof:
  Hubbard's annular Perron construction gives a negative Dirichlet Green
  potential on every exhaustion member.  Change its sign and regard the
  domain as an open Riemann surface; the boundary value and compact closure
  give compact positive superlevel sets.
-/
theorem PointedH1ZeroSmoothRelativelyCompactExhaustion.has_compactSuperlevelGreenFunctions
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {p : X}
    (hnoncompact : ¬ CompactSpace X)
    (E : PointedH1ZeroSmoothRelativelyCompactExhaustion X p) :
    Nonempty
      ((n : ℕ) → CompactSuperlevelGreenFunctionWithPole
        (E.domain n).openCarrier ⟨p, E.domain_base_mem n⟩) := by
  rcases smoothRelativelyCompactExhaustion_has_boundedNegativeGreenPotentials
      hnoncompact E.toSmoothRelativelyCompactExhaustion p E.domain_base_mem with
    ⟨B⟩
  refine ⟨fun n ↦ ?_⟩
  letI : PathConnectedSpace
      (E.toSmoothRelativelyCompactExhaustion.domain n).carrier :=
    E.pathConnected n
  exact (B n).toCompactSuperlevelOpenCarrier (E.domain_base_mem n)

end

end JJMath.Uniformization
