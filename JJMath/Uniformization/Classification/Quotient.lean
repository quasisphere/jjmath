import JJMath.Uniformization.Classification.HolomorphicCover
import JJMath.Uniformization.ComplexSurfaceMaps
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Covering.Quotient

/-!
# Riemann surfaces as quotients of their uniformizing covers

Given a biholomorphic coordinate from the path-class universal cover of a
Riemann surface `X` to a complex surface `U`, this file transports the deck
action to `U`.  The resulting projection `U → X` is a quotient covering map.
Its orbit quotient carries the complex structure pulled back from `X`, and
the induced map from the quotient to `X` is biholomorphic.
-/

namespace JJMath

open scoped Manifold Topology

namespace Uniformization

open JJMath.PathHomotopyUniversalCover

namespace PathHomotopyUniversalCover

noncomputable section

variable {X U : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
  [RiemannSurface X] [TopologicalSpace U] [ChartedSpace ℂ U] {x₀ : X}

/--
%%handwave
name:
  Deck action in a uniformizing coordinate
statement:
  Given a biholomorphism $E:\widetilde X_{x_0}\to U$, the action of
  $\gamma\in\pi_1(X,x_0)$ on $u\in U$ is
  $\gamma\cdot_Eu=E(\gamma\cdot E^{-1}(u))$.
-/
def uniformizingDeckAction
    (E : Biholomorphic (PathHomotopyUniversalCover X x₀) U)
    (gamma : FundamentalGroup X x₀) (u : U) : U :=
  E.toHomeomorph (deckAction gamma (E.toHomeomorph.symm u))

/--
%%handwave
name:
  The identity acts trivially in a uniformizing coordinate
statement:
  For every $u\in U$, the identity element of $\pi_1(X,x_0)$ satisfies
  $1\cdot_Eu=u$.
proof:
  Conjugate the identity deck transformation through $E$.
-/
@[simp]
theorem uniformizingDeckAction_one
    (E : Biholomorphic (PathHomotopyUniversalCover X x₀) U) (u : U) :
    uniformizingDeckAction E 1 u = u := by
  simp [uniformizingDeckAction]

/--
%%handwave
name:
  Multiplication law for the uniformizing deck action
statement:
  For $\gamma,\delta\in\pi_1(X,x_0)$ and $u\in U$,
  $(\gamma\delta)\cdot_Eu=\gamma\cdot_E(\delta\cdot_Eu)$.
proof:
  Apply the multiplication law for deck transformations and cancel the
  adjacent maps $E^{-1}E$.
-/
theorem uniformizingDeckAction_mul
    (E : Biholomorphic (PathHomotopyUniversalCover X x₀) U)
    (gamma delta : FundamentalGroup X x₀) (u : U) :
    uniformizingDeckAction E (gamma * delta) u =
      uniformizingDeckAction E gamma (uniformizingDeckAction E delta u) := by
  simp only [uniformizingDeckAction]
  rw [deckAction_mul]
  simp

/--
%%handwave
name:
  Group action associated with a uniformizing coordinate
statement:
  The formulas $\gamma\cdot_Eu=E(\gamma\cdot E^{-1}(u))$ define an action of
  $\pi_1(X,x_0)$ on $U$.
-/
@[implicit_reducible]
noncomputable def uniformizingDeckMulAction
    (E : Biholomorphic (PathHomotopyUniversalCover X x₀) U) :
    MulAction (FundamentalGroup X x₀) U where
  smul := uniformizingDeckAction E
  one_smul := uniformizingDeckAction_one E
  mul_smul := uniformizingDeckAction_mul E

/--
%%handwave
name:
  Orbit relation of the uniformizing deck action
statement:
  Two points $u,v\in U$ are equivalent exactly when
  $u=\gamma\cdot_Ev$ for some $\gamma\in\pi_1(X,x_0)$.
-/
noncomputable def uniformizingDeckSetoid
    (E : Biholomorphic (PathHomotopyUniversalCover X x₀) U) : Setoid U :=
  @MulAction.orbitRel (FundamentalGroup X x₀) U _
    (uniformizingDeckMulAction E)

/--
%%handwave
name:
  Quotient of a uniformizing surface by its deck action
statement:
  For $E:\widetilde X_{x_0}\to U$, the quotient $U/\pi_1(X,x_0)$ is the
  set of orbits of the transported deck action $\gamma\cdot_Eu$.
-/
abbrev UniformizingDeckQuotient
    (E : Biholomorphic (PathHomotopyUniversalCover X x₀) U) :=
  Quotient (uniformizingDeckSetoid E)

/--
%%handwave
name:
  Projection from a uniformizing surface
statement:
  The projection $p_E:U\to X$ is
  $p_E(u)=\pi(E^{-1}(u))$, where
  $\pi:\widetilde X_{x_0}\to X$ is the endpoint projection.
-/
def uniformizingProjection
    (E : Biholomorphic (PathHomotopyUniversalCover X x₀) U) : U → X :=
  fun u ↦ endpoint (E.toHomeomorph.symm u)

/--
%%handwave
name:
  Uniformizing projection is invariant under deck transformations
statement:
  For $\gamma\in\pi_1(X,x_0)$ and $u\in U$,
  $p_E(\gamma\cdot_Eu)=p_E(u)$.
proof:
  After applying $E^{-1}$, this is the invariance of the endpoint projection
  under deck transformations.
-/
@[simp]
theorem uniformizingProjection_deckAction
    (E : Biholomorphic (PathHomotopyUniversalCover X x₀) U)
    (gamma : FundamentalGroup X x₀) (u : U) :
    uniformizingProjection E (uniformizingDeckAction E gamma u) =
      uniformizingProjection E u := by
  simp [uniformizingProjection, uniformizingDeckAction]

/--
%%handwave
name:
  The uniformizing projection is the deck-orbit covering
statement:
  Let $E:\widetilde X_{x_0}\to U$ be biholomorphic. Then
  $p_E:U\to X$ is a quotient covering map for the transported action of
  $\pi_1(X,x_0)$: its fibers are precisely the deck orbits, every deck
  transformation is continuous, and each point has a neighborhood disjoint
  from all its nonidentity translates.
proof:
  Conjugating the endpoint covering by $E$ makes $p_E$ a surjective covering
  map. Deck transformations are homeomorphisms, and transitivity of the deck
  action identifies fibers with orbits. On a neighborhood where $p_E$ is
  injective, an intersecting translate would fix a point; freeness of the
  deck action then forces the group element to be the identity.
-/
theorem uniformizingProjection_isQuotientCoveringMap
    (E : Biholomorphic (PathHomotopyUniversalCover X x₀) U) :
    @IsQuotientCoveringMap U X _ _ (uniformizingProjection E)
      (FundamentalGroup X x₀) _ (uniformizingDeckMulAction E) := by
  letI : MulAction (FundamentalGroup X x₀) U :=
    uniformizingDeckMulAction E
  have hp_cover : IsCoveringMap (uniformizingProjection E) := by
    have h := (isCoveringMap_endpoint_of_riemannSurface X x₀).comp_homeomorph
      E.toHomeomorph.symm
    simpa [uniformizingProjection, Function.comp_def] using h
  have hp_surjective : Function.Surjective (uniformizingProjection E) :=
    (endpoint_surjective_of_riemannSurface X x₀).comp
      E.toHomeomorph.symm.surjective
  refine
    { toIsQuotientMap := hp_cover.isQuotientMap hp_surjective
      toContinuousConstSMul := ?_
      apply_eq_iff_mem_orbit := ?_
      disjoint := ?_ }
  · refine ⟨fun gamma ↦ ?_⟩
    change Continuous (uniformizingDeckAction E gamma)
    exact E.toHomeomorph.continuous.comp
      ((deckHomeomorphism gamma).continuous.comp
        E.toHomeomorph.symm.continuous)
  · intro u v
    constructor
    · intro huv
      have hfiber :
          endpoint (E.toHomeomorph.symm v) =
            endpoint (E.toHomeomorph.symm u) := by
        simpa [uniformizingProjection] using huv.symm
      rcases deckAction_same_fiber_transitive
          (E.toHomeomorph.symm v) (E.toHomeomorph.symm u) hfiber with
        ⟨gamma, hgamma⟩
      apply MulAction.mem_orbit_iff.mpr
      refine ⟨gamma, ?_⟩
      change uniformizingDeckAction E gamma v = u
      simpa [uniformizingDeckAction] using congrArg E.toHomeomorph hgamma
    · intro horbit
      rcases MulAction.mem_orbit_iff.mp horbit with ⟨gamma, hgamma⟩
      rw [← hgamma]
      exact uniformizingProjection_deckAction E gamma v
  · intro u
    rcases hp_cover.isLocalHomeomorph.isLocallyInjective u with
      ⟨V, hVopen, huV, hVinj⟩
    refine ⟨V, hVopen.mem_nhds huV, ?_⟩
    intro gamma hinter
    rcases hinter with ⟨w, ⟨v, hvV, hvw⟩, hwV⟩
    have hfix : uniformizingDeckAction E gamma v = v := by
      apply hVinj
      · simpa [← hvw] using hwV
      · exact hvV
      exact uniformizingProjection_deckAction E gamma v
    apply deckAction_fiber_free gamma (E.toHomeomorph.symm v)
    apply E.toHomeomorph.injective
    simpa [uniformizingDeckAction] using hfix

/--
%%handwave
name:
  Map from the uniformizing orbit quotient to the surface
statement:
  The deck-invariant projection $p_E:U\to X$ induces a map
  $\overline p_E:U/\pi_1(X,x_0)\to X$.
-/
noncomputable def uniformizingQuotientToBase
    (E : Biholomorphic (PathHomotopyUniversalCover X x₀) U) :
    UniformizingDeckQuotient E → X :=
  Quotient.lift (uniformizingProjection E) (by
    intro u v huv
    letI : MulAction (FundamentalGroup X x₀) U :=
      uniformizingDeckMulAction E
    change MulAction.orbitRel (FundamentalGroup X x₀) U u v at huv
    exact (uniformizingProjection_isQuotientCoveringMap E).apply_eq_iff_mem_orbit.mpr
      ((MulAction.orbitRel_apply).mp huv))

/--
%%handwave
name:
  The quotient-to-base map is injective
statement:
  If two deck orbits in $U/\pi_1(X,x_0)$ have the same image in $X$, then
  they are equal.
proof:
  Representatives with the same image under $p_E$ lie in the same deck
  orbit because the fibers of $p_E$ are exactly the orbits.
-/
theorem uniformizingQuotientToBase_injective
    (E : Biholomorphic (PathHomotopyUniversalCover X x₀) U) :
    Function.Injective (uniformizingQuotientToBase E) := by
  intro q r hqr
  induction q using Quotient.inductionOn with
  | _ u =>
      induction r using Quotient.inductionOn with
      | _ v =>
          apply Quotient.sound
          letI : MulAction (FundamentalGroup X x₀) U :=
            uniformizingDeckMulAction E
          change MulAction.orbitRel (FundamentalGroup X x₀) U u v
          rw [MulAction.orbitRel_apply]
          apply
            (uniformizingProjection_isQuotientCoveringMap E).apply_eq_iff_mem_orbit.mp
          simpa using hqr

/--
%%handwave
name:
  The quotient-to-base map is a quotient map
statement:
  The induced map
  $\overline p_E:U/\pi_1(X,x_0)\to X$ is a topological quotient map.
proof:
  Its composite with the orbit projection is $p_E$. Both the orbit
  projection and $p_E$ are quotient maps, so the induced map is a quotient
  map.
-/
theorem uniformizingQuotientToBase_isQuotientMap
    (E : Biholomorphic (PathHomotopyUniversalCover X x₀) U) :
    Topology.IsQuotientMap (uniformizingQuotientToBase E) := by
  letI : MulAction (FundamentalGroup X x₀) U :=
    uniformizingDeckMulAction E
  let q : U → UniformizingDeckQuotient E := Quotient.mk _
  have hq : Topology.IsQuotientMap q := isQuotientMap_quotient_mk'
  apply hq.of_comp_iff.mp
  simpa [q, Function.comp_def] using
    (uniformizingProjection_isQuotientCoveringMap E).toIsQuotientMap

/--
%%handwave
name:
  Canonical homeomorphism from the deck quotient to the surface
statement:
  The map
  $\overline p_E:U/\pi_1(X,x_0)\to X$ induced by the uniformizing projection
  is a homeomorphism.
proof:
  The induced map is an injective quotient map and therefore a
  homeomorphism.
-/
noncomputable def uniformizingQuotientHomeomorph
    (E : Biholomorphic (PathHomotopyUniversalCover X x₀) U) :
    UniformizingDeckQuotient E ≃ₜ X :=
  (isHomeomorph_iff_isQuotientMap_injective.mpr
    ⟨uniformizingQuotientToBase_isQuotientMap E,
      uniformizingQuotientToBase_injective E⟩).homeomorph
        (uniformizingQuotientToBase E)

/--
%%handwave
name:
  Pullback of a charted-space structure by a homeomorphism
statement:
  If $F:M\to N$ is a homeomorphism and $N$ is charted by a model space $H$,
  then $M$ is charted by precomposing every chart of $N$ with $F$.
-/
@[implicit_reducible]
noncomputable def chartedSpacePullbackByHomeomorph
    {M N H : Type} [TopologicalSpace M] [TopologicalSpace N]
    [TopologicalSpace H] [ChartedSpace H N] (F : M ≃ₜ N) :
    ChartedSpace H M where
  atlas := {F.toOpenPartialHomeomorph.trans e | e ∈ atlas H N}
  chartAt m :=
    F.toOpenPartialHomeomorph.trans (chartAt H (F m))
  mem_chart_source m := by
    rw [OpenPartialHomeomorph.trans_source]
    exact ⟨Set.mem_univ m, mem_chart_source H (F m)⟩
  chart_mem_atlas m :=
    ⟨chartAt H (F m), chart_mem_atlas H (F m), rfl⟩

/--
%%handwave
name:
  Pullback charts preserve atlas compatibility
statement:
  If the charts of $N$ have transition maps in a structure groupoid $G$,
  then the charts pulled back along a homeomorphism $F:M\to N$ have transition
  maps in the same groupoid.
proof:
  A transition between two pulled-back charts cancels the adjacent factors
  $F^{-1}F$ and is exactly the corresponding transition between the original
  charts of $N$.
-/
theorem chartedSpacePullbackByHomeomorph_hasGroupoid
    {M N H : Type} [TopologicalSpace M] [TopologicalSpace N]
    [TopologicalSpace H] [chartedN : ChartedSpace H N]
    (F : M ≃ₜ N) (G : StructureGroupoid H) [groupoidN : HasGroupoid N G] :
    @HasGroupoid H _ M _
      (chartedSpacePullbackByHomeomorph F) G :=
  @HasGroupoid.mk H _ M _
    (chartedSpacePullbackByHomeomorph F) G (by
      intro e e' he he'
      rcases he with ⟨c, hc, rfl⟩
      rcases he' with ⟨c', hc', rfl⟩
      have heq :
          (F.toOpenPartialHomeomorph.trans c).symm.trans
              (F.toOpenPartialHomeomorph.trans c') =
            c.symm.trans c' := by
        ext z <;> simp
      rw [heq]
      exact
        @StructureGroupoid.compatible H _ G N _ chartedN groupoidN
          c c' hc hc')

/--
%%handwave
name:
  Complex atlas on a uniformizing deck quotient
statement:
  The orbit quotient $U/\pi_1(X,x_0)$ is given the complex atlas obtained by
  pulling the atlas of $X$ back through its canonical homeomorphism to $X$.
-/
noncomputable instance uniformizingDeckQuotientChartedSpace
    (E : Biholomorphic (PathHomotopyUniversalCover X x₀) U) :
    ChartedSpace ℂ (UniformizingDeckQuotient E) :=
  chartedSpacePullbackByHomeomorph (uniformizingQuotientHomeomorph E)

/--
%%handwave
name:
  Charts on the uniformizing deck quotient
statement:
  At $q\in U/\pi_1(X,x_0)$, the preferred quotient chart is the preferred
  chart of $X$ at $\overline p_E(q)$ precomposed with
  $\overline p_E$.
proof:
  This is the definition of the pulled-back charted-space structure.
-/
theorem uniformizingDeckQuotient_chartAt
    (E : Biholomorphic (PathHomotopyUniversalCover X x₀) U)
    (q : UniformizingDeckQuotient E) :
    chartAt ℂ q =
      (uniformizingQuotientHomeomorph E).toOpenPartialHomeomorph.trans
        (chartAt ℂ (uniformizingQuotientHomeomorph E q)) :=
  rfl

/--
%%handwave
name:
  The uniformizing deck quotient is a complex manifold
statement:
  With the atlas pulled back from $X$, the quotient
  $U/\pi_1(X,x_0)$ is a complex one-manifold.
-/
noncomputable instance uniformizingDeckQuotientIsManifold
    (E : Biholomorphic (PathHomotopyUniversalCover X x₀) U) :
    IsManifold 𝓘(ℂ) ⊤ (UniformizingDeckQuotient E) := by
  letI : HasGroupoid (UniformizingDeckQuotient E)
      (contDiffGroupoid ⊤ 𝓘(ℂ)) :=
    chartedSpacePullbackByHomeomorph_hasGroupoid
      (uniformizingQuotientHomeomorph E) (contDiffGroupoid ⊤ 𝓘(ℂ))
  exact IsManifold.mk' 𝓘(ℂ) ⊤ (UniformizingDeckQuotient E)




/--
%%handwave
name:
  The canonical quotient homeomorphism is biholomorphic
statement:
  Let $E:\widetilde X_{x_0}\to U$ be biholomorphic. The canonical
  homeomorphism
  $\overline p_E:U/\pi_1(X,x_0)\to X$ is biholomorphic.
proof:
  The quotient atlas was pulled back from $X$ along $\overline p_E$. In these
  paired charts, both $\overline p_E$ and its inverse have the identity as
  their local coordinate expression.
-/
noncomputable def uniformizingQuotientBiholomorphic
    (E : Biholomorphic (PathHomotopyUniversalCover X x₀) U) :
    Biholomorphic (UniformizingDeckQuotient E) X where
  toHomeomorph := uniformizingQuotientHomeomorph E
  holomorphic_toFun := by
    let F := uniformizingQuotientHomeomorph E
    intro q
    let e : OpenPartialHomeomorph (UniformizingDeckQuotient E) ℂ :=
      chartAt ℂ q
    let b : OpenPartialHomeomorph X ℂ := chartAt ℂ (F q)
    have hqsource : q ∈ e.source := mem_chart_source ℂ q
    have heq : e = F.toOpenPartialHomeomorph.trans b :=
      uniformizingDeckQuotient_chartAt E q
    have heq_b : e q = b (F q) := by
      rw [heq]
      simp
    have he_mdiff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) e q :=
      mdifferentiableAt_atlas (chart_mem_atlas ℂ q) hqsource
    have hb_symm_mdiff :
        MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) b.symm (e q) := by
      apply mdifferentiableAt_atlas_symm (chart_mem_atlas ℂ (F q))
      rw [heq_b]
      exact b.map_source (mem_chart_source ℂ (F q))
    have hcomp :
        MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (b.symm ∘ e) q :=
      hb_symm_mdiff.comp q he_mdiff
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [e.open_source.mem_nhds hqsource] with q' hq'
    have hFq'_b : F q' ∈ b.source := by
      rw [heq, OpenPartialHomeomorph.trans_source] at hq'
      exact hq'.2
    change F q' = b.symm (e q')
    rw [heq, OpenPartialHomeomorph.trans_apply]
    change F q' = b.symm (b (F q'))
    exact (b.left_inv hFq'_b).symm
  holomorphic_invFun := by
    let F := uniformizingQuotientHomeomorph E
    intro x
    let q : UniformizingDeckQuotient E := F.symm x
    let e : OpenPartialHomeomorph (UniformizingDeckQuotient E) ℂ :=
      chartAt ℂ q
    let b : OpenPartialHomeomorph X ℂ := chartAt ℂ x
    have hxsource : x ∈ b.source := mem_chart_source ℂ x
    have hqsource : q ∈ e.source := mem_chart_source ℂ q
    have heq : e = F.toOpenPartialHomeomorph.trans b := by
      have h :=
        uniformizingDeckQuotient_chartAt E q
      change e =
        F.toOpenPartialHomeomorph.trans (chartAt ℂ (F q)) at h
      rw [show F q = x by simp [q]] at h
      exact h
    have heq_b : e q = b x := by
      rw [heq]
      simp [q]
    have hb_mdiff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) b x :=
      mdifferentiableAt_atlas (chart_mem_atlas ℂ x) hxsource
    have he_symm_mdiff :
        MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) e.symm (b x) := by
      apply mdifferentiableAt_atlas_symm (chart_mem_atlas ℂ q)
      rw [← heq_b]
      exact e.map_source hqsource
    have hcomp :
        MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (e.symm ∘ b) x :=
      he_symm_mdiff.comp x hb_mdiff
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [b.open_source.mem_nhds hxsource] with x' hx'
    have hq'_e : F.symm x' ∈ e.source := by
      rw [heq, OpenPartialHomeomorph.trans_source]
      exact ⟨Set.mem_univ _, by simpa⟩
    change F.symm x' = e.symm (b x')
    rw [← e.left_inv hq'_e]
    congr 1
    rw [heq, OpenPartialHomeomorph.trans_apply]
    simp

/--
%%handwave
name:
  A Riemann surface is the quotient of any uniformizing model by its deck group
statement:
  If $E:\widetilde X_{x_0}\to U$ is biholomorphic, then $X$ is
  biholomorphic to the orbit quotient
  $U/\pi_1(X,x_0)$ for the transported deck action
  $\gamma\cdot_Eu=E(\gamma\cdot E^{-1}(u))$.
proof:
  Take the inverse of [the canonical quotient map is biholomorphic](lean:JJMath.Uniformization.PathHomotopyUniversalCover.uniformizingQuotientBiholomorphic).
-/
theorem biholomorphicSurfaces_uniformizingDeckQuotient
    (E : Biholomorphic (PathHomotopyUniversalCover X x₀) U) :
    BiholomorphicSurfaces X (UniformizingDeckQuotient E) :=
  ⟨(uniformizingQuotientBiholomorphic E).symm⟩

end

end PathHomotopyUniversalCover

end Uniformization

end JJMath
