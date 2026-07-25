import JJMath.Uniformization.AtlasVortexPair
import JJMath.Uniformization.LocallyStableSmoothPhase

/-!
# Finite transport by compact atlas vortex pairs

A finite vortex telescope should not remember all of its internal seams.
For iteration it is enough to retain its smooth unit phase together with a
factorization near the terminal endpoint into a smooth unit multiplier and
the final atlas vortex pair.  The final pair cancels with the first pair of
the next segment by the holomorphic seam theorem.
-/

open Set
open scoped Manifold ContDiff Topology

namespace JJMath.Uniformization

noncomputable section

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
variable [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X] [T2Space X]

/--
%%handwave
name:
  Smooth corestriction to an open range
statement:
  If a smooth map \(f:M\to N\) takes all its values in an open subset
  \(V\subseteq N\), then the corestricted map \(M\to V\) is smooth.
proof:
  Near each image point, use the local retraction onto \(V\), which agrees
  there with the identity, and compose it with \(f\).
-/
theorem contMDiffCodRestrictOpen_transport
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H G M N : Type*}
    [TopologicalSpace H] [TopologicalSpace G]
    [TopologicalSpace M] [TopologicalSpace N]
    {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ F G}
    [ChartedSpace H M] [ChartedSpace G N]
    {n : WithTop ℕ∞} {f : M → N}
    (hf : ContMDiff I J n f) (V : TopologicalSpace.Opens N)
    (hmem : ∀ x, f x ∈ V) :
    ContMDiff I J n (fun x ↦ (⟨f x, hmem x⟩ : V)) := by
  classical
  intro x
  let qV : V := ⟨f x, hmem x⟩
  let retract : N → V := fun y ↦
    if hy : y ∈ V then ⟨y, hy⟩ else qV
  have hretract : ContMDiffAt J J n retract (f x) := by
    rw [← contMDiffAt_subtype_iff (U := V) (x := qV)]
    have heq : (fun y : V ↦ retract y) = id := by
      funext y
      simp [retract]
    rw [heq]
    exact contMDiffAt_id
  have hcomp := hretract.comp x (hf x)
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [] with y
  simp [retract, hmem]

/--
%%handwave
name:
  Gluing two unit phases across their common puncture
statement:
  Let \(P_1\) be a smooth unit phase on \(X\setminus\{a,q\}\) and \(P_2\) one
  on \(X\setminus\{q,b\}\).  If their product has a smooth unit-valued
  extension \(S\) near \(q\), then there is a smooth unit phase \(Q\) on
  \(X\setminus\{a,b\}\) such that
  \(Q=P_1P_2\) away from \(q\).
proof:
  Define \(Q\) to be \(S\) at the middle point and \(P_1P_2\) elsewhere.
  These descriptions agree on the overlap of a neighborhood of \(q\) with
  its punctured complement, so the two smooth maps glue.  Their unit-norm
  identities likewise give \(|Q|=1\).
-/
theorem exists_gluedUnitPhase_across_middle
    {a q b : X}
    (P₁ : ContMDiffMap SurfaceRealModel (modelWithCornersSelf ℝ ℂ)
      (coordinateVortexPairOpen a q) ℂ ∞)
    (P₂ : ContMDiffMap SurfaceRealModel (modelWithCornersSelf ℝ ℂ)
      (coordinateVortexPairOpen q b) ℂ ∞)
    (hP₁ : ∀ x : coordinateVortexPairOpen a q, ‖P₁ x‖ = 1)
    (hP₂ : ∀ x : coordinateVortexPairOpen q b, ‖P₂ x‖ = 1)
    (U : TopologicalSpace.Opens X) (hqU : q ∈ U)
    (S : X → ℂ)
    (hS_smooth : ContMDiffOn SurfaceRealModel
      (modelWithCornersSelf ℝ ℂ) ∞ S U)
    (hS_norm : ∀ x ∈ U, ‖S x‖ = 1)
    (hproduct : ∀ (x : X) (_hxU : x ∈ U)
      (hxa : x ≠ a) (hxq : x ≠ q) (hxb : x ≠ b),
      P₁ ⟨x, ⟨hxa, hxq⟩⟩ * P₂ ⟨x, ⟨hxq, hxb⟩⟩ = S x) :
    ∃ Q : ContMDiffMap SurfaceRealModel (modelWithCornersSelf ℝ ℂ)
        (coordinateVortexPairOpen a b) ℂ ∞,
      (∀ x : coordinateVortexPairOpen a b, ‖Q x‖ = 1) ∧
      ∀ (x : coordinateVortexPairOpen a b) (hxq : (x : X) ≠ q),
        Q x = P₁ ⟨(x : X), ⟨x.2.1, hxq⟩⟩ *
          P₂ ⟨(x : X), ⟨hxq, x.2.2⟩⟩ := by
  let A : TopologicalSpace.Opens (coordinateVortexPairOpen a b) :=
    ⟨{x | (x : X) ∈ U}, U.isOpen.preimage
      (continuous_subtype_val : Continuous
        (fun x : coordinateVortexPairOpen a b ↦ (x : X)))⟩
  let B : TopologicalSpace.Opens (coordinateVortexPairOpen a b) :=
    ⟨{x | (x : X) ≠ q}, isOpen_ne.preimage
      (continuous_subtype_val : Continuous
        (fun x : coordinateVortexPairOpen a b ↦ (x : X)))⟩
  let Qfun : coordinateVortexPairOpen a b → ℂ := fun x ↦ by
    classical
    exact if hxq : (x : X) ≠ q then
      P₁ ⟨(x : X), ⟨x.2.1, hxq⟩⟩ *
        P₂ ⟨(x : X), ⟨hxq, x.2.2⟩⟩
    else S x
  have hA_smooth : ContMDiff SurfaceRealModel
      (modelWithCornersSelf ℝ ℂ) ∞ (fun x : A ↦ S (x : X)) := by
    intro x
    have hval : ContMDiffAt SurfaceRealModel SurfaceRealModel ∞
        (fun y : A ↦ (y : X)) x :=
      (contMDiff_subtype_val.comp contMDiff_subtype_val).contMDiffAt
    exact (hS_smooth.contMDiffAt
      (U.isOpen.mem_nhds x.2)).comp x hval
  have hBto₁ : ContMDiff SurfaceRealModel SurfaceRealModel ∞
      (fun x : B ↦
        (⟨(x : X), ⟨x.1.2.1, x.2⟩⟩ :
          coordinateVortexPairOpen a q)) := by
    have hval : ContMDiff SurfaceRealModel SurfaceRealModel ∞
        (fun x : B ↦ (x : X)) :=
      contMDiff_subtype_val.comp contMDiff_subtype_val
    exact contMDiffCodRestrictOpen_transport hval
      (coordinateVortexPairOpen a q) (fun x ↦ ⟨x.1.2.1, x.2⟩)
  have hBto₂ : ContMDiff SurfaceRealModel SurfaceRealModel ∞
      (fun x : B ↦
        (⟨(x : X), ⟨x.2, x.1.2.2⟩⟩ :
          coordinateVortexPairOpen q b)) := by
    have hval : ContMDiff SurfaceRealModel SurfaceRealModel ∞
        (fun x : B ↦ (x : X)) :=
      contMDiff_subtype_val.comp contMDiff_subtype_val
    exact contMDiffCodRestrictOpen_transport hval
      (coordinateVortexPairOpen q b) (fun x ↦ ⟨x.2, x.1.2.2⟩)
  have hB_smooth : ContMDiff SurfaceRealModel
      (modelWithCornersSelf ℝ ℂ) ∞
      (fun x : B ↦
        P₁ (⟨(x : X), ⟨x.1.2.1, x.2⟩⟩ :
            coordinateVortexPairOpen a q) *
          P₂ (⟨(x : X), ⟨x.2, x.1.2.2⟩⟩ :
            coordinateVortexPairOpen q b)) :=
    ContDiff.comp_contMDiff (by
      fun_prop : ContDiff ℝ ∞ (fun z : ℂ × ℂ ↦ z.1 * z.2))
      ((P₁.contMDiff.comp hBto₁).prodMk_space
        (P₂.contMDiff.comp hBto₂))
  have hQ_smooth : ContMDiff SurfaceRealModel
      (modelWithCornersSelf ℝ ℂ) ∞ Qfun := by
    apply contMDiff_of_contMDiffOn_union_of_isOpen
    · intro x hx
      apply ContMDiffAt.contMDiffWithinAt
      let xA : A := ⟨x, hx⟩
      rw [← contMDiffAt_subtype_iff (U := A) (x := xA)]
      have heq :
          (fun y : A ↦ Qfun (y : coordinateVortexPairOpen a b)) =
            fun y : A ↦ S (y : X) := by
        funext y
        by_cases hyq : (y : X) ≠ q
        · rw [show Qfun (y : coordinateVortexPairOpen a b) =
              P₁ ⟨(y : X), ⟨y.1.2.1, hyq⟩⟩ *
                P₂ ⟨(y : X), ⟨hyq, y.1.2.2⟩⟩ by
              simp [Qfun, hyq]]
          exact hproduct (y : X) y.2 y.1.2.1 hyq y.1.2.2
        · simp [Qfun, hyq]
      rw [heq]
      exact hA_smooth.contMDiffAt
    · intro x hx
      apply ContMDiffAt.contMDiffWithinAt
      let xB : B := ⟨x, hx⟩
      rw [← contMDiffAt_subtype_iff (U := B) (x := xB)]
      have heq :
          (fun y : B ↦ Qfun (y : coordinateVortexPairOpen a b)) =
            fun y : B ↦
              P₁ (⟨(y : X), ⟨y.1.2.1, y.2⟩⟩ :
                  coordinateVortexPairOpen a q) *
                P₂ (⟨(y : X), ⟨y.2, y.1.2.2⟩⟩ :
                  coordinateVortexPairOpen q b) := by
        funext y
        dsimp [Qfun]
        have hyq : (y : X) ≠ q := y.2
        rw [dif_pos hyq]
      rw [heq]
      exact hB_smooth.contMDiffAt
    · ext x
      simp only [Set.mem_union, Set.mem_univ, iff_true]
      by_cases hxq : (x : X) ≠ q
      · exact Or.inr hxq
      · left
        change (x : X) ∈ U
        simpa [not_ne_iff.mp hxq] using hqU
    · exact A.isOpen
    · exact B.isOpen
  let Q : ContMDiffMap SurfaceRealModel (modelWithCornersSelf ℝ ℂ)
      (coordinateVortexPairOpen a b) ℂ ∞ := ⟨Qfun, hQ_smooth⟩
  have hQ_norm : ∀ x : coordinateVortexPairOpen a b, ‖Q x‖ = 1 := by
    intro x
    by_cases hxq : (x : X) ≠ q
    · change ‖Qfun x‖ = 1
      rw [show Qfun x =
          P₁ ⟨(x : X), ⟨x.2.1, hxq⟩⟩ *
            P₂ ⟨(x : X), ⟨hxq, x.2.2⟩⟩ by
          simp [Qfun, hxq], norm_mul, hP₁, hP₂, one_mul]
    · have hxq' : (x : X) = q := not_ne_iff.mp hxq
      change ‖Qfun x‖ = 1
      rw [show Qfun x = S x by simp [Qfun, hxq]]
      exact hS_norm (x : X) (by simpa [hxq'] using hqU)
  refine ⟨Q, hQ_norm, ?_⟩
  intro x hxq
  change Qfun x = _
  simp [Qfun, hxq]

/-- A finite compact-vortex transport from `a` to `b`.  Besides the global
phase on the twice-punctured surface, it remembers a smooth factorization by
its last vortex pair near `b`; this is the induction invariant for appending
another pair. -/
structure AtlasVortexTransportData (X : Type) [TopologicalSpace X]
    [ChartedSpace ℂ X] [ComplexOneManifold X]
    [IsManifold SurfaceRealModel ∞ X] [T2Space X] (a b : X) where
  endpoints_ne : a ≠ b
  phase : ContMDiffMap SurfaceRealModel (modelWithCornersSelf ℝ ℂ)
    (coordinateVortexPairOpen a b) ℂ ∞
  norm_phase : ∀ x : coordinateVortexPairOpen a b, ‖phase x‖ = 1
  terminalStart : X
  terminalPair : AtlasVortexPairData X terminalStart b
  terminalOpen : TopologicalSpace.Opens X
  terminal_mem : b ∈ terminalOpen
  terminalMultiplier : X → ℂ
  terminalMultiplier_smooth : ContMDiffOn SurfaceRealModel
    (modelWithCornersSelf ℝ ℂ) ∞ terminalMultiplier terminalOpen
  terminalMultiplier_norm : ∀ x ∈ terminalOpen, ‖terminalMultiplier x‖ = 1
  phase_eq_terminal : ∀ (x : X) (_hxU : x ∈ terminalOpen)
      (hxa : x ≠ a) (hxs : x ≠ terminalStart) (hxb : x ≠ b),
    phase (⟨x, ⟨hxa, hxb⟩⟩ : coordinateVortexPairOpen a b) =
      terminalMultiplier x *
        terminalPair.globalPhase
          (⟨x, ⟨hxs, hxb⟩⟩ : coordinateVortexPairOpen terminalStart b)

/--
%%handwave
name: A single atlas vortex pair is the initial finite transport
statement:
  A single atlas vortex pair is the initial finite transport.
-/
def AtlasVortexTransportData.single {a b : X}
    (D : AtlasVortexPairData X a b) :
    AtlasVortexTransportData X a b where
  endpoints_ne := D.endpoints_ne
  phase := D.globalPhase
  norm_phase := D.norm_globalPhase
  terminalStart := a
  terminalPair := D
  terminalOpen := ⊤
  terminal_mem := trivial
  terminalMultiplier := fun _ ↦ 1
  terminalMultiplier_smooth := contMDiffOn_const
  terminalMultiplier_norm := by simp
  phase_eq_terminal := by simp

/--
%%handwave
name:
  Appending an atlas vortex pair to a finite transport
statement:
  Let \(T\) be a finite atlas-vortex transport from \(a\) to \(q\), and let
  \(D\) be an atlas vortex from \(q\) to \(b\), with \(a\ne b\).  There is a
  transport \(T'\) from \(a\) to \(b\) whose phase satisfies
  \[
    P_{T'}(x)=P_T(x)P_D(x)
  \]
  whenever \(x\ne q\).
proof:
  Factor the old transport near \(q\) into its smooth terminal multiplier and
  last vortex pair.  The last pair and the new pair have a smooth unit seam
  product at \(q\); multiplying by the old terminal multiplier gives a local
  extension of the full product.  Glue across \(q\), and record the old phase
  as the new terminal multiplier so that the new pair becomes the remembered
  terminal factor.
-/
theorem AtlasVortexTransportData.exists_append
    {a q b : X} (T : AtlasVortexTransportData X a q)
    (D : AtlasVortexPairData X q b) (hab : a ≠ b) :
    ∃ T' : AtlasVortexTransportData X a b,
      ∀ (x : coordinateVortexPairOpen a b) (hxq : (x : X) ≠ q),
        T'.phase x = T.phase ⟨(x : X), ⟨x.2.1, hxq⟩⟩ *
          D.globalPhase ⟨(x : X), ⟨hxq, x.2.2⟩⟩ := by
  rcases T.terminalPair.consecutive_product_local_extension D with
    ⟨Useam, hqUseam, Sseam, hSseam_smooth, hSseam_norm, hseam⟩
  let Uset : Set X :=
    ((T.terminalOpen : Set X) ∩ (Useam : Set X) ∩ {x | x ≠ a}) ∩
      {x | x ≠ T.terminalStart}
  have hUopen : IsOpen Uset :=
    ((T.terminalOpen.isOpen.inter Useam.isOpen).inter isOpen_ne).inter
      isOpen_ne
  let U : TopologicalSpace.Opens X := ⟨Uset, hUopen⟩
  have hqU : q ∈ U := by
    exact ⟨⟨⟨T.terminal_mem, hqUseam⟩, T.endpoints_ne.symm⟩,
      T.terminalPair.endpoints_ne.symm⟩
  let S : X → ℂ := fun x ↦ T.terminalMultiplier x * Sseam x
  have hS_smooth : ContMDiffOn SurfaceRealModel
      (modelWithCornersSelf ℝ ℂ) ∞ S U := by
    have hm := T.terminalMultiplier_smooth.mono (by
      intro x (hx : x ∈ U)
      exact hx.1.1.1)
    have hs := hSseam_smooth.mono (by
      intro x (hx : x ∈ U)
      exact hx.1.1.2)
    intro x hx
    have hpair := (hm x hx).prodMk_space (hs x hx)
    simpa [S, Function.comp_def] using
      (ContDiff.comp_contMDiffWithinAt (by
        fun_prop : ContDiff ℝ ∞ (fun z : ℂ × ℂ ↦ z.1 * z.2)) hpair)
  have hS_norm : ∀ x ∈ U, ‖S x‖ = 1 := by
    intro x hx
    rw [show S x = T.terminalMultiplier x * Sseam x by rfl,
      norm_mul, T.terminalMultiplier_norm x hx.1.1.1,
      hSseam_norm x hx.1.1.2, one_mul]
  have hproduct : ∀ (x : X) (_hxU : x ∈ U)
      (hxa : x ≠ a) (hxq : x ≠ q) (hxb : x ≠ b),
      T.phase ⟨x, ⟨hxa, hxq⟩⟩ *
        D.globalPhase ⟨x, ⟨hxq, hxb⟩⟩ = S x := by
    intro x hxU hxa hxq hxb
    rw [T.phase_eq_terminal x hxU.1.1.1 hxa hxU.2 hxq,
      mul_assoc, hseam x hxU.1.1.2 hxU.2 hxq hxb]
  rcases exists_gluedUnitPhase_across_middle T.phase D.globalPhase
      T.norm_phase D.norm_globalPhase U hqU S hS_smooth hS_norm hproduct with
    ⟨Q, hQnorm, hQproduct⟩
  let Vset : Set X := {x | x ≠ a} ∩ {x | x ≠ q}
  have hVopen : IsOpen Vset := isOpen_ne.inter isOpen_ne
  let V : TopologicalSpace.Opens X := ⟨Vset, hVopen⟩
  have hbV : b ∈ V := ⟨hab.symm, D.endpoints_ne.symm⟩
  let R : X → ℂ := fun x ↦ by
    classical
    exact if hx : x ∈ V then T.phase ⟨x, ⟨hx.1, hx.2⟩⟩ else 1
  have hR_smooth : ContMDiffOn SurfaceRealModel
      (modelWithCornersSelf ℝ ℂ) ∞ R V := by
    intro x hx
    have hlift : ContMDiffAt SurfaceRealModel SurfaceRealModel ∞
        (fun y : V ↦
          (⟨(y : X), ⟨y.2.1, y.2.2⟩⟩ :
            coordinateVortexPairOpen a q)) ⟨x, hx⟩ := by
      exact (contMDiffCodRestrictOpen_transport contMDiff_subtype_val
        (coordinateVortexPairOpen a q)
        (fun y : V ↦ ⟨y.2.1, y.2.2⟩)).contMDiffAt
    have hphase : ContMDiffAt SurfaceRealModel
        (modelWithCornersSelf ℝ ℂ) ∞
        (fun y : V ↦ T.phase
          (⟨(y : X), ⟨y.2.1, y.2.2⟩⟩ :
            coordinateVortexPairOpen a q)) (⟨x, hx⟩ : V) :=
      T.phase.contMDiff.contMDiffAt.comp (⟨x, hx⟩ : V) hlift
    have heq : (fun y : V ↦ R (y : X)) = fun y : V ↦
        T.phase (⟨(y : X), ⟨y.2.1, y.2.2⟩⟩ :
          coordinateVortexPairOpen a q) := by
      funext y
      simp [R, y.2]
    apply ContMDiffAt.contMDiffWithinAt
    rw [← contMDiffAt_subtype_iff (U := V) (x := ⟨x, hx⟩)]
    rw [heq]
    exact hphase
  have hR_norm : ∀ x ∈ V, ‖R x‖ = 1 := by
    intro x hx
    rw [show R x = T.phase ⟨x, ⟨hx.1, hx.2⟩⟩ by simp [R, hx]]
    exact T.norm_phase _
  let T' : AtlasVortexTransportData X a b :=
    { endpoints_ne := hab
      phase := Q
      norm_phase := hQnorm
      terminalStart := q
      terminalPair := D
      terminalOpen := V
      terminal_mem := hbV
      terminalMultiplier := R
      terminalMultiplier_smooth := hR_smooth
      terminalMultiplier_norm := hR_norm
      phase_eq_terminal := by
        intro x hxV hxa hxq hxb
        rw [hQproduct ⟨x, ⟨hxa, hxb⟩⟩ hxq]
        change T.phase ⟨x, ⟨hxa, hxq⟩⟩ *
            D.globalPhase ⟨x, ⟨hxq, hxb⟩⟩ =
          R x * D.globalPhase ⟨x, ⟨hxq, hxb⟩⟩
        rw [show R x = T.phase ⟨x, ⟨hxa, hxq⟩⟩ by
          simp [R, hxV]] }
  exact ⟨T', hQproduct⟩

/-! ## The locally stationary infinite telescope -/

/--
%%handwave
name: The surface with the initial vortex point removed
statement:
  The surface with the initial vortex point removed.
-/
def atlasVortexInitialOpen (a : X) : TopologicalSpace.Opens X :=
  ⟨{x | x ≠ a}, isOpen_ne⟩

end

end JJMath.Uniformization
