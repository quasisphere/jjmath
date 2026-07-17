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

/-- Glue the product of two smooth unit phases across their common removed
point once that product has a smooth unit local extension there. -/
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

/-- A single atlas vortex pair is the initial finite transport. -/
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

/-- Append one atlas vortex pair to a finite transport.  All old seams remain
hidden inside the existing smooth phase; only its remembered final pair has
to cancel with the new pair. -/
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

/-- Every finite initial segment of a chain of compact atlas vortex pairs
has a smooth unit transport phase.  Internal vertices need not be globally
distinct: once a seam has been glued, a later visit to it is just a visit to
an ordinary smooth point. -/
theorem exists_atlasVortexTransport_of_finite_chain
    (v : ℕ → X)
    (D : ∀ n : ℕ, AtlasVortexPairData X (v n) (v (n + 1)))
    (hfirst : ∀ n : ℕ, v 0 ≠ v (n + 1)) (n : ℕ) :
    Nonempty (AtlasVortexTransportData X (v 0) (v (n + 1))) := by
  induction n with
  | zero =>
      exact ⟨AtlasVortexTransportData.single (D 0)⟩
  | succ n ih =>
      rcases ih with ⟨T⟩
      rcases T.exists_append (D (n + 1)) (hfirst (n + 1)) with
        ⟨T', _hphase⟩
      exact ⟨T'⟩

/-- A coherent choice of finite transport phases along an infinite atlas
vortex chain.  Stage `n` transports from the initial vertex to vertex
`n + 1`. -/
noncomputable def finiteAtlasVortexTransport
    (v : ℕ → X)
    (D : ∀ n : ℕ, AtlasVortexPairData X (v n) (v (n + 1)))
    (hfirst : ∀ n : ℕ, v 0 ≠ v (n + 1)) :
    ∀ n : ℕ, AtlasVortexTransportData X (v 0) (v (n + 1))
  | 0 => AtlasVortexTransportData.single (D 0)
  | n + 1 => Classical.choose
      ((finiteAtlasVortexTransport v D hfirst n).exists_append
        (D (n + 1)) (hfirst (n + 1)))

/-- Consecutive coherent finite transports differ by precisely the next
compact atlas vortex away from their shared terminal vertex. -/
theorem finiteAtlasVortexTransport_phase_succ
    (v : ℕ → X)
    (D : ∀ n : ℕ, AtlasVortexPairData X (v n) (v (n + 1)))
    (hfirst : ∀ n : ℕ, v 0 ≠ v (n + 1)) (n : ℕ)
    (x : coordinateVortexPairOpen (v 0) (v (n + 1 + 1)))
    (hxq : (x : X) ≠ v (n + 1)) :
    (finiteAtlasVortexTransport v D hfirst (n + 1)).phase x =
      (finiteAtlasVortexTransport v D hfirst n).phase
          ⟨(x : X), ⟨x.2.1, hxq⟩⟩ *
        (D (n + 1)).globalPhase
          ⟨(x : X), ⟨hxq, x.2.2⟩⟩ := by
  exact (Classical.choose_spec
    ((finiteAtlasVortexTransport v D hfirst n).exists_append
      (D (n + 1)) (hfirst (n + 1)))) x hxq

/-! ## The locally stationary infinite telescope -/

/-- The surface with the initial vortex point removed. -/
def atlasVortexInitialOpen (a : X) : TopologicalSpace.Opens X :=
  ⟨{x | x ≠ a}, isOpen_ne⟩

/-- The finite transport phase at stage `n`, made into a total function on
the initially punctured surface by assigning an irrelevant value at its
current terminal point.  Local escape guarantees that this exceptional
point eventually leaves every fixed neighborhood. -/
noncomputable def finiteAtlasVortexTransportPartialPhase
    (v : ℕ → X)
    (D : ∀ n : ℕ, AtlasVortexPairData X (v n) (v (n + 1)))
    (hfirst : ∀ n : ℕ, v 0 ≠ v (n + 1))
    (n : ℕ) (x : atlasVortexInitialOpen (v 0)) : ℂ := by
  classical
  exact if hxt : (x : X) ≠ v (n + 1) then
    (finiteAtlasVortexTransport v D hfirst n).phase
      ⟨(x : X), ⟨x.2, hxt⟩⟩
  else 1

theorem norm_finiteAtlasVortexTransportPartialPhase
    (v : ℕ → X)
    (D : ∀ n : ℕ, AtlasVortexPairData X (v n) (v (n + 1)))
    (hfirst : ∀ n : ℕ, v 0 ≠ v (n + 1))
    (n : ℕ) (x : atlasVortexInitialOpen (v 0)) :
    ‖finiteAtlasVortexTransportPartialPhase v D hfirst n x‖ = 1 := by
  by_cases hxt : (x : X) ≠ v (n + 1)
  · rw [show finiteAtlasVortexTransportPartialPhase v D hfirst n x =
        (finiteAtlasVortexTransport v D hfirst n).phase
          ⟨(x : X), ⟨x.2, hxt⟩⟩ by
      simp [finiteAtlasVortexTransportPartialPhase, hxt]]
    exact (finiteAtlasVortexTransport v D hfirst n).norm_phase _
  · simp [finiteAtlasVortexTransportPartialPhase, hxt]

/-- Away from its current terminal point, a finite partial phase is smooth. -/
theorem contMDiffAt_finiteAtlasVortexTransportPartialPhase_of_ne
    (v : ℕ → X)
    (D : ∀ n : ℕ, AtlasVortexPairData X (v n) (v (n + 1)))
    (hfirst : ∀ n : ℕ, v 0 ≠ v (n + 1))
    (n : ℕ) (x : atlasVortexInitialOpen (v 0))
    (hxt : (x : X) ≠ v (n + 1)) :
    ContMDiffAt SurfaceRealModel (modelWithCornersSelf ℝ ℂ) ∞
      (finiteAtlasVortexTransportPartialPhase v D hfirst n) x := by
  let B : TopologicalSpace.Opens (atlasVortexInitialOpen (v 0)) :=
    ⟨{y | (y : X) ≠ v (n + 1)}, isOpen_ne.preimage
      (continuous_subtype_val : Continuous
        (fun y : atlasVortexInitialOpen (v 0) ↦ (y : X)))⟩
  let xB : B := ⟨x, hxt⟩
  have hval : ContMDiff SurfaceRealModel SurfaceRealModel ∞
      (fun y : B ↦ (y : X)) :=
    contMDiff_subtype_val.comp contMDiff_subtype_val
  have hlift : ContMDiff SurfaceRealModel SurfaceRealModel ∞
      (fun y : B ↦
        (⟨(y : X), ⟨y.1.2, y.2⟩⟩ :
          coordinateVortexPairOpen (v 0) (v (n + 1)))) :=
    contMDiffCodRestrictOpen_transport hval
      (coordinateVortexPairOpen (v 0) (v (n + 1)))
      (fun y ↦ ⟨y.1.2, y.2⟩)
  have hsmooth : ContMDiff SurfaceRealModel
      (modelWithCornersSelf ℝ ℂ) ∞
      (fun y : B ↦ (finiteAtlasVortexTransport v D hfirst n).phase
        (⟨(y : X), ⟨y.1.2, y.2⟩⟩ :
          coordinateVortexPairOpen (v 0) (v (n + 1)))) :=
    (finiteAtlasVortexTransport v D hfirst n).phase.contMDiff.comp hlift
  rw [← contMDiffAt_subtype_iff (U := B) (x := xB)]
  have heq :
      (fun y : B ↦ finiteAtlasVortexTransportPartialPhase
        v D hfirst n (y : atlasVortexInitialOpen (v 0))) =
      fun y : B ↦ (finiteAtlasVortexTransport v D hfirst n).phase
        (⟨(y : X), ⟨y.1.2, y.2⟩⟩ :
          coordinateVortexPairOpen (v 0) (v (n + 1))) := by
    funext y
    have hy : (y : X) ≠ v (n + 1) := y.2
    simp [finiteAtlasVortexTransportPartialPhase, hy]
  rw [heq]
  exact hsmooth.contMDiffAt

/-- If the next compact vortex core and the two adjacent vertices miss a
point, appending that vortex does not change the partial phase there. -/
theorem finiteAtlasVortexTransportPartialPhase_succ_eq
    (v : ℕ → X)
    (D : ∀ n : ℕ, AtlasVortexPairData X (v n) (v (n + 1)))
    (hfirst : ∀ n : ℕ, v 0 ≠ v (n + 1))
    (n : ℕ) (x : atlasVortexInitialOpen (v 0))
    (hxq : (x : X) ≠ v (n + 1))
    (hxb : (x : X) ≠ v (n + 1 + 1))
    (hxcore : (x : X) ∉ (D (n + 1)).ambientCore) :
    finiteAtlasVortexTransportPartialPhase v D hfirst (n + 1) x =
      finiteAtlasVortexTransportPartialPhase v D hfirst n x := by
  rw [show finiteAtlasVortexTransportPartialPhase v D hfirst (n + 1) x =
      (finiteAtlasVortexTransport v D hfirst (n + 1)).phase
        ⟨(x : X), ⟨x.2, hxb⟩⟩ by
      simp [finiteAtlasVortexTransportPartialPhase, hxb],
    finiteAtlasVortexTransport_phase_succ v D hfirst n
      ⟨(x : X), ⟨x.2, hxb⟩⟩ hxq]
  have hDone : (D (n + 1)).globalPhase
      (⟨(x : X), ⟨hxq, hxb⟩⟩ :
        coordinateVortexPairOpen (v (n + 1)) (v (n + 1 + 1))) = 1 :=
    (D (n + 1)).globalPhaseFun_eq_one_of_mem_exterior hxcore
  rw [hDone, mul_one]
  simp [finiteAtlasVortexTransportPartialPhase, hxq]

/-- A chain whose vertices and compact vortex cores eventually miss a
neighborhood of every point has a global smooth unit limiting phase and
hence a circle primitive.  This is the complete analytic telescope; the
remaining input is purely the locally finite atlas subdivision of an
escaping path. -/
theorem exists_circlePrimitive_of_locallyEscaping_atlasVortexChain
    (v : ℕ → X)
    (D : ∀ n : ℕ, AtlasVortexPairData X (v n) (v (n + 1)))
    (hfirst : ∀ n : ℕ, v 0 ≠ v (n + 1))
    (hescape : ∀ x : atlasVortexInitialOpen (v 0),
      ∃ N : ℕ, ∃ U : TopologicalSpace.Opens
          (atlasVortexInitialOpen (v 0)),
        x ∈ U ∧ ∀ n ≥ N, ∀ y ∈ U,
          (y : X) ≠ v (n + 1) ∧ (y : X) ∉ (D n).ambientCore) :
    ∃ (P : ContMDiffMap SurfaceRealModel (modelWithCornersSelf ℝ ℂ)
          (atlasVortexInitialOpen (v 0)) ℂ ∞)
        (hP : ∀ x : atlasVortexInitialOpen (v 0), ‖P x‖ = 1),
      Nonempty (JJMath.Manifold.SmoothCirclePrimitive SurfaceRealModel
        (smoothUnitPhaseOneForm SurfaceRealModel P hP)) := by
  let f : ℕ → atlasVortexInitialOpen (v 0) → ℂ :=
    finiteAtlasVortexTransportPartialPhase v D hfirst
  have hlocal : ∀ x : atlasVortexInitialOpen (v 0),
      ∃ N : ℕ, ∃ U : TopologicalSpace.Opens
          (atlasVortexInitialOpen (v 0)),
        x ∈ U ∧
        ContMDiffOn SurfaceRealModel (modelWithCornersSelf ℝ ℂ) ∞ (f N) U ∧
        ∀ n ≥ N, Set.EqOn (f n) (f N) U := by
    intro x
    rcases hescape x with ⟨N, U, hxU, havoid⟩
    refine ⟨N, U, hxU, ?_, ?_⟩
    · intro y hy
      exact (contMDiffAt_finiteAtlasVortexTransportPartialPhase_of_ne
        v D hfirst N y (havoid N le_rfl y hy).1).contMDiffWithinAt
    · intro n hn y hy
      induction n, hn using Nat.le_induction with
      | base => rfl
      | succ n hn ih =>
          exact (finiteAtlasVortexTransportPartialPhase_succ_eq
            v D hfirst n y
              (havoid n hn y hy).1
              (havoid (n + 1) (Nat.le_trans hn (Nat.le_succ n)) y hy).1
              (havoid (n + 1) (Nat.le_trans hn (Nat.le_succ n)) y hy).2).trans ih
  have hnorm : ∀ x : atlasVortexInitialOpen (v 0),
      ∃ N : ℕ, ∀ n ≥ N, ‖f n x‖ = 1 := by
    intro x
    exact ⟨0, fun n _ ↦ norm_finiteAtlasVortexTransportPartialPhase
      v D hfirst n x⟩
  exact exists_circlePrimitive_of_locally_eventuallyEq_unitPhase
    SurfaceRealModel f hlocal hnorm

end

end JJMath.Uniformization
