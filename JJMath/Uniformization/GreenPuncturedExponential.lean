import JJMath.Uniformization.GreenFunctionResidue

/-!
# Extending a Green exponential across its pole

A holomorphic exponential of `-G` on the punctured surface has the same
modulus as the distinguished local pole branch.  Their quotient therefore
has constant norm one on a punctured coordinate disk, so the maximum-modulus
principle makes it a unit constant.  The local first-order factorization of
the distinguished branch then transfers to the global punctured
exponential.
-/

open Set
open scoped Manifold ContDiff Topology

namespace JJMath.Uniformization

noncomputable section

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
  [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
  {p : X} {G : CompactSuperlevelGreenFunctionWithPole X p}

/-- Extend a function on an open submanifold by an arbitrary value outside
the open set.  The extension is holomorphic on the original open set.

%%handwave
name: Holomorphicity transferred from an open subtype
statement:
  Let $U$ be open in a complex manifold $X$, let $f:U\to\mathbb C$ be holomorphic, and let $F:X\to\mathbb C$ agree with $f$ on $U$. Then $F$ is holomorphic on $U$.
proof:
  Near each $x\in U$, retract $X$ to $U$ by the identity on $U$ and an arbitrary value outside. The composite with $f$ is holomorphic and agrees locally with $F$.
-/
private theorem mdifferentiableOn_of_eq_openSubtype
    (U : TopologicalSpace.Opens X) (f : U → ℂ)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (F : X → ℂ) (hF : ∀ x (hx : x ∈ U), F x = f ⟨x, hx⟩) :
    MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) F U := by
  classical
  intro x hxU
  let xU : U := ⟨x, hxU⟩
  let retract : X → U := fun y ↦
    if hy : y ∈ U then ⟨y, hy⟩ else xU
  have hretract : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) retract x := by
    have hsmooth : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ∞ retract x := by
      rw [← contMDiffAt_subtype_iff (U := U) (x := xU)]
      have heq : (fun y : U ↦ retract y) = id := by
        funext y
        simp [retract]
      rw [heq]
      exact contMDiffAt_id
    exact hsmooth.mdifferentiableAt (by simp)
  have hcomp : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (f ∘ retract) x := by
    apply (hf (retract x)).comp x hretract
  have heq : F =ᶠ[𝓝 x] f ∘ retract := by
    filter_upwards [U.isOpen.mem_nhds hxU] with y hyU
    rw [hF y hyU]
    apply congrArg f
    apply Subtype.ext
    dsimp only [retract]
    split <;> simp_all
  exact (hcomp.congr_of_eventuallyEq heq).mdifferentiableWithinAt

/-- A punctured holomorphic exponential with logarithmic modulus `-G`
inherits the first-order pole factorization of any distinguished pole
branch. -/
noncomputable def compactSuperlevelGreenFunction_puncturedPlaneMap_of_holomorphicExp
    (P : CompactSuperlevelGreenFunctionPoleExponentialBranch X G)
    (f : puncturedSurfaceOpen p → ℂ)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hf_nonzero : ∀ z, f z ≠ 0)
    (hf_log : ∀ z, Real.log ‖f z‖ = -G.toFun (z : X)) :
    CompactSuperlevelGreenFunctionPuncturedPlaneMap X G := by
  classical
  let F : X → ℂ := fun x ↦
    if hx : x ≠ p then f ⟨x, hx⟩ else 0
  refine
    { toFun := F
      holomorphic_away_pole := ?_
      log_norm_eq := ?_
      nonzero_away_pole := ?_
      pole_factorizations := ?_ }
  · apply mdifferentiableOn_of_eq_openSubtype
      (puncturedSurfaceOpen p) f hf F
    intro x hx
    have hxp : x ≠ p := by simpa [puncturedSurfaceOpen] using hx
    change (if h : x ≠ p then f ⟨x, h⟩ else 0) = f ⟨x, hx⟩
    rw [dif_pos hxp]
  · intro x hxp
    simpa [F, hxp] using hf_log ⟨x, hxp⟩
  · intro x hxp
    simpa [F, hxp] using hf_nonzero ⟨x, hxp⟩
  · intro χ
    rcases P.pole_factorizations χ with
      ⟨r₀, hr₀_pos, hball₀_target, A, hA_diff, hA_ne, hA_factor⟩
    let V : Set ℂ := χ.chart.target ∩ χ.chart.symm ⁻¹' P.domain
    have hV_open : IsOpen V := by
      simpa [V] using χ.chart.isOpen_inter_preimage_symm P.domain_open
    have hpV : χ.chart p ∈ V := by
      refine ⟨χ.chart.map_source χ.base_mem_source, ?_⟩
      simpa [V, χ.chart.left_inv χ.base_mem_source] using P.mem_domain
    rcases Metric.isOpen_iff.mp hV_open (χ.chart p) hpV with
      ⟨r₁, hr₁_pos, hball₁_subset⟩
    let r : ℝ := min r₀ r₁
    have hr_pos : 0 < r := lt_min hr₀_pos hr₁_pos
    have hball_target : Metric.ball (χ.chart p) r ⊆ χ.chart.target := by
      intro z hz
      exact hball₀_target (Metric.mem_ball.mpr
        (lt_of_lt_of_le (Metric.mem_ball.mp hz) (min_le_left r₀ r₁)))
    have hball_domain : ∀ z ∈ Metric.ball (χ.chart p) r,
        χ.chart.symm z ∈ P.domain := by
      intro z hz
      exact (hball₁_subset (Metric.mem_ball.mpr
        (lt_of_lt_of_le (Metric.mem_ball.mp hz)
          (min_le_right r₀ r₁)))).2
    let B : TopologicalSpace.Opens ℂ :=
      complexPuncturedBallOpen (χ.chart p) r
    have hB_ball (z : B) : (z : ℂ) ∈ Metric.ball (χ.chart p) r := z.2.1
    have hB_ne (z : B) : (z : ℂ) ≠ χ.chart p := z.2.2
    let toX : B → X := fun z ↦ χ.chart.symm (z : ℂ)
    have htoX_punctured (z : B) : toX z ≠ p := by
      intro hz
      have hright := χ.chart.right_inv (hball_target (hB_ball z))
      exact hB_ne z (by simpa [toX, hz] using hright.symm)
    let toU : B → puncturedSurfaceOpen p := fun z ↦
      ⟨toX z, htoX_punctured z⟩
    have htoX : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) toX := by
      intro z
      have hsymm : MDifferentiableWithinAt 𝓘(ℂ) 𝓘(ℂ)
          χ.chart.symm χ.chart.target (z : ℂ) :=
        mdifferentiableOn_atlas_symm (I := 𝓘(ℂ)) χ.chart_mem_atlas
          (z : ℂ) (hball_target (hB_ball z))
      exact hsymm.mdifferentiableAt
        (χ.chart.open_target.mem_nhds (hball_target (hB_ball z))) |>.comp z
          ((contMDiff_subtype_val (I := 𝓘(ℂ)) (n := ∞)).contMDiffAt.mdifferentiableAt
            (by simp))
    have htoU : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) toU := by
      intro z
      let zU : puncturedSurfaceOpen p := toU z
      let retract : X → puncturedSurfaceOpen p := fun x ↦
        if hx : x ≠ p then ⟨x, hx⟩ else zU
      have hretract : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) retract (toX z) := by
        have hsmooth : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ∞ retract (toX z) := by
          rw [← contMDiffAt_subtype_iff
            (U := puncturedSurfaceOpen p) (x := zU)]
          have heq : (fun x : puncturedSurfaceOpen p ↦ retract x) = id := by
            funext x
            apply Subtype.ext
            change ↑(retract (x : X)) = (x : X)
            dsimp only [retract]
            split
            · rfl
            · rename_i h
              exact False.elim (h x.2)
          rw [heq]
          exact contMDiffAt_id
        exact hsmooth.mdifferentiableAt (by simp)
      have hcomp := hretract.comp z (htoX z)
      have hopen : IsOpen {x : X | x ≠ p} := isOpen_ne
      have hevent : ∀ᶠ x in 𝓝 z, toX x ≠ p :=
        (htoX z).continuousAt.eventually
          (hopen.mem_nhds (htoX_punctured z))
      have heq : toU =ᶠ[𝓝 z] retract ∘ toX := by
        filter_upwards [hevent] with x hx
        apply Subtype.ext
        change toX x = ↑(retract (toX x))
        dsimp only [retract]
        split
        · rfl
        · rename_i h
          exact False.elim (h hx)
      exact hcomp.congr_of_eventuallyEq heq
    let fB : B → ℂ := fun z ↦ f (toU z)
    let pB : B → ℂ := fun z ↦ P.branch (toX z)
    have hfB : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) fB := by
      intro z
      exact (hf (toU z)).comp z (htoU z)
    have hpB : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pB := by
      intro z
      exact (P.branch_holomorphicOn (toX z)
        (hball_domain (z : ℂ) (hB_ball z))).mdifferentiableAt
          (P.domain_open.mem_nhds
            (hball_domain (z : ℂ) (hB_ball z))) |>.comp z (htoX z)
    have hpB_nonzero : ∀ z : B, pB z ≠ 0 := by
      intro z
      exact P.nonzero_away_pole (toX z)
        (hball_domain (z : ℂ) (hB_ball z)) (htoX_punctured z)
    let q : B → ℂ := fun z ↦ fB z / pB z
    have hq : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) q := by
      intro z
      have hpair : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ, ℂ × ℂ)
          (fun w : B ↦ (fB w, pB w)) z :=
        (hfB z).prodMk_space (hpB z)
      have hdiv : MDifferentiableAt 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ)
          (fun w : ℂ × ℂ ↦ w.1 / w.2) (fB z, pB z) := by
        have hfirst : DifferentiableAt ℂ (fun w : ℂ × ℂ ↦ w.1)
            (fB z, pB z) :=
          differentiableAt_fst
        have hsecond : DifferentiableAt ℂ (fun w : ℂ × ℂ ↦ w.2)
            (fB z, pB z) :=
          differentiableAt_snd
        simpa [div_eq_mul_inv] using
          (hfirst.mul (hsecond.inv (hpB_nonzero z))).mdifferentiableAt
      simpa [q, Function.comp_def] using hdiv.comp z hpair
    have hnorm_eq (z : B) : ‖fB z‖ = ‖pB z‖ := by
      apply Real.log_injOn_pos (norm_pos_iff.mpr (hf_nonzero (toU z)))
        (norm_pos_iff.mpr (hpB_nonzero z))
      rw [hf_log (toU z)]
      exact (P.log_norm_eq (toX z)
        (hball_domain (z : ℂ) (hB_ball z)) (htoX_punctured z)).symm
    have hq_norm (z : B) : ‖q z‖ = 1 := by
      rw [norm_div, hnorm_eq z, div_self (norm_ne_zero_iff.mpr (hpB_nonzero z))]
    let e := complexPuncturedPlaneDiffeomorphPuncturedBall
      (χ.chart p) r hr_pos
    letI : ConnectedSpace Circle :=
      Subtype.connectedSpace
        (isConnected_sphere
          (Complex.rank_real_complex ▸ (by norm_num : (1 : Cardinal) < 2))
          (0 : ℂ) (by norm_num))
    letI : ConnectedSpace complexPuncturedPlaneOpen :=
      complexPuncturedPlaneDiffeomorphAnnularCylinder.symm.surjective.connectedSpace
        complexPuncturedPlaneDiffeomorphAnnularCylinder.symm.continuous
    letI : ConnectedSpace B :=
      e.surjective.connectedSpace e.continuous
    let z₀ : B := e ⟨1, one_ne_zero⟩
    have hq_const : ∀ z : B, q z = q z₀ := by
      have hmax : IsMaxOn (norm ∘ q) Set.univ z₀ := by
        intro z _hz
        simp [hq_norm z, hq_norm z₀]
      have hconst := hq.mdifferentiableOn.eqOn_of_isPreconnected_of_isMaxOn_norm
        isPreconnected_univ isOpen_univ (Set.mem_univ z₀) hmax
      intro z
      simpa using hconst (Set.mem_univ z)
    let γ : ℂ := q z₀
    have hγ_ne : γ ≠ 0 := by
      exact norm_ne_zero_iff.mp (by simp [γ, hq_norm z₀])
    let A' : ℂ → ℂ := fun z ↦ γ * A z
    refine ⟨r, hr_pos, hball_target, A', ?_, ?_, ?_⟩
    · exact (hA_diff.mono (by
        intro z hz
        exact Metric.mem_ball.mpr
          (lt_of_lt_of_le (Metric.mem_ball.mp hz)
            (min_le_left r₀ r₁)))).const_mul γ
    · exact mul_ne_zero hγ_ne hA_ne
    · intro z hz hz_ne
      let zB : B := ⟨z, hz, hz_ne⟩
      have hratio : fB zB / pB zB = γ := by
        simpa [q, γ] using hq_const zB
      have hfp : fB zB = γ * pB zB := by
        exact (div_eq_iff (hpB_nonzero zB)).mp hratio
      have hz₀ : z ∈ Metric.ball (χ.chart p) r₀ :=
        Metric.mem_ball.mpr
          (lt_of_lt_of_le (Metric.mem_ball.mp hz) (min_le_left r₀ r₁))
      calc
        F (χ.chart.symm z) = fB zB := by
          have hne : χ.chart.symm z ≠ p := htoX_punctured zB
          rw [show F (χ.chart.symm z) =
              f ⟨χ.chart.symm z, hne⟩ by simp [F, hne]]
        _ = γ * pB zB := hfp
        _ = γ * ((z - χ.chart p) * A z) := by
          rw [show pB zB = P.branch (χ.chart.symm z) by rfl,
            hA_factor z hz₀ hz_ne]
        _ = (z - χ.chart p) * A' z := by
          dsimp [A']
          ring

end

end JJMath.Uniformization
