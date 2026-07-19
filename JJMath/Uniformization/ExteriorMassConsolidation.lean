import JJMath.Uniformization.ExteriorMassTransport

/-!
# Consolidating compact mass before transport through an end

A compactly supported two-form in an exterior component can first be moved,
modulo an exact correction, into one prescribed coordinate chart.  This is
the finite part of mass transport.  Keeping the resulting remainder intact
is useful when its total mass, rather than the individual partition pieces,
carries an integral normalization.
-/

open Set
open scoped Manifold ContDiff Topology
open JJMath.Manifold

namespace JJMath.Uniformization

noncomputable section

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
variable [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]

/-- A compactly supported two-form in an exterior component can be moved,
modulo an exact correction supported in that component, into one prescribed
full-plane coordinate chart.  All pieces of a finite partition of unity are
summed in the target chart before any transport to infinity is performed.

%%handwave
name: Consolidation of compactly supported mass in an exterior component
statement:
  Let $V$ be an exterior component of the complement of a compact set in a noncompact Riemann surface, let $C\subseteq V$ be compact, and let $T\subseteq V$ be a prescribed full-plane coordinate neighborhood. If a smooth two-form $\omega$ vanishes outside $C$, then there are a one-form $\eta$, a two-form $\beta$, and a compact set $K_T\subseteq T$ such that $d\eta=\omega-\beta$, $\eta$ vanishes outside $V$, and $\beta$ vanishes outside the ambient image of $K_T$.
proof:
  Cover $C$ by finitely many planar charts inside $V$ and split $\omega$ with a smooth partition of unity. Move each compactly supported piece along paths in $V$ into the prescribed chart, producing exact corrections supported in $V$. Sum the transported pieces in $T$ and take the finite union of their compact cores.
-/
theorem IsExteriorComponent.exists_compactSupport_consolidation_in_open
    {K V C : Set X} (hKcompact : IsCompact K)
    (hV : IsExteriorComponent K V)
    (hCcompact : IsCompact C) (hCV : C ⊆ V)
    (T : TopologicalSpace.Opens X) (hTV : T ≤ V)
    (y₀ : T)
    (omega : SmoothForms (I := SurfaceRealModel) (M := X) ℝ 2)
    (hzero : ∀ y : X, y ∉ C → omega.toFun y = 0) :
    ∃ (eta : SmoothForms (I := SurfaceRealModel) (M := X) ℝ 1)
        (beta : SmoothForms (I := SurfaceRealModel) (M := X) ℝ 2)
        (KT : Set T),
      IsCompact KT ∧
      deRhamDifferential
          (I := SurfaceRealModel) (M := X) (A := ℝ) 1 eta = omega - beta ∧
      (∀ y : X, y ∉ V → eta.toFun y = 0) ∧
      ∀ y : X, y ∉ smoothFormCompactCore T KT → beta.toFun y = 0 := by
  classical
  let Vopen : TopologicalSpace.Opens X :=
    ⟨V, hV.isComponentOf.isOpen_of_isOpen
      hKcompact.isClosed.isOpen_compl⟩
  let U : C → TopologicalSpace.Opens X := fun p ↦
    Classical.choose
      (exists_complexPlanarChart_subordinate Vopen (p : X) (hCV p.2))
  have hpU : ∀ p : C, (p : X) ∈ U p := fun p ↦
    (Classical.choose_spec
      (exists_complexPlanarChart_subordinate Vopen (p : X) (hCV p.2))).1
  have hUV : ∀ p : C, U p ≤ Vopen := fun p ↦
    (Classical.choose_spec
      (exists_complexPlanarChart_subordinate Vopen (p : X) (hCV p.2))).2.1
  have hphiU : ∀ p : C, Nonempty
      (U p ≃ₘ⟮SurfaceRealModel, SurfaceRealModel⟯
        complexPlanarModelOpen) := fun p ↦
    (Classical.choose_spec
      (exists_complexPlanarChart_subordinate Vopen (p : X) (hCV p.2))).2.2
  have hcover : C ⊆ ⋃ p : C, (U p : Set X) := by
    intro y hyC
    exact mem_iUnion.mpr ⟨⟨y, hyC⟩, hpU ⟨y, hyC⟩⟩
  rcases hCcompact.elim_finite_subcover
      (fun p : C ↦ (U p : Set X)) (fun p ↦ (U p).isOpen) hcover with
    ⟨t, ht⟩
  let J := {p : C // p ∈ t}
  let coverOpen : Option J → Set X
    | none => Cᶜ
    | some j => U (j : C)
  have hcoverOpen : ∀ i : Option J, IsOpen (coverOpen i) := by
    intro i
    cases i with
    | none => exact hCcompact.isClosed.isOpen_compl
    | some j => exact (U (j : C)).isOpen
  have hcoverUniv : (univ : Set X) ⊆ ⋃ i : Option J, coverOpen i := by
    intro y _hy
    by_cases hyC : y ∈ C
    · have hyt := ht hyC
      rcases mem_iUnion.mp hyt with ⟨p, hp⟩
      rcases mem_iUnion.mp hp with ⟨hpt, hyp⟩
      exact mem_iUnion.mpr ⟨some ⟨p, hpt⟩, hyp⟩
    · exact mem_iUnion.mpr ⟨none, hyC⟩
  letI : SecondCountableTopology X :=
    rado_secondCountableTopology_riemannSurface X
  letI : SigmaCompactSpace X := by infer_instance
  rcases SmoothPartitionOfUnity.exists_isSubordinate
      SurfaceRealModel isClosed_univ coverOpen hcoverOpen hcoverUniv with
    ⟨rho, hrho⟩
  let piece : Option J → SmoothForms
      (I := SurfaceRealModel) (M := X) ℝ 2 := fun i ↦
    smoothFormsPointwiseSMul
      (I := SurfaceRealModel) (M := X) (A := ℝ) (rho i) omega
  have hVpath : IsPathConnected V :=
    hV.isComponentOf.isPathConnected_of_compl_isClosed hKcompact.isClosed
  have hpiece_transport : ∀ i : Option J,
      ∃ (eta : SmoothForms (I := SurfaceRealModel) (M := X) ℝ 1)
          (beta : SmoothForms (I := SurfaceRealModel) (M := X) ℝ 2)
          (targetCore : Set X),
        IsCompact targetCore ∧ targetCore ⊆ T ∧
        deRhamDifferential
            (I := SurfaceRealModel) (M := X) (A := ℝ) 1 eta =
          piece i - beta ∧
        (∀ y : X, y ∉ V → eta.toFun y = 0) ∧
        ∀ y : X, y ∉ targetCore → beta.toFun y = 0 := by
    intro i
    cases i with
    | none =>
        have hpieceZero : piece none = 0 := by
          apply DifferentialForm.ext
          intro y
          by_cases hyC : y ∈ C
          · apply smoothFormsPointwiseSMul_eq_zero_of_notMem_tsupport
            intro hysupport
            exact (hrho none hysupport) hyC
          · simp [piece, smoothFormsPointwiseSMul_toFun, hzero y hyC]
        refine ⟨0, 0, ∅, isCompact_empty, empty_subset _, ?_, ?_, ?_⟩
        · rw [map_zero, hpieceZero, sub_zero]
        · intro y _hy
          rfl
        · intro y _hy
          rfl
    | some j =>
        let Cj : Set X := C ∩ tsupport (rho (some j))
        have hCjcompact : IsCompact Cj :=
          hCcompact.inter_right (isClosed_tsupport (rho (some j)))
        have hCjU : Cj ⊆ U (j : C) := by
          intro y hy
          exact hrho (some j) hy.2
        let Kj : Set (U (j : C)) :=
          smoothFormCompactCoreInOpen (U (j : C)) Cj
        have hKjcompact : IsCompact Kj :=
          smoothFormCompactCoreInOpen_isCompact
            (U (j : C)) Cj hCjcompact hCjU
        have hpieceZero : ∀ y : X,
            y ∉ smoothFormCompactCore (U (j : C)) Kj →
              (piece (some j)).toFun y = 0 := by
          intro y hy
          have hyCj : y ∉ Cj := by
            rwa [smoothFormCompactCore_coreInOpen
              (U (j : C)) Cj hCjU] at hy
          by_cases hyC : y ∈ C
          · apply smoothFormsPointwiseSMul_eq_zero_of_notMem_tsupport
            intro hysupport
            exact hyCj ⟨hyC, hysupport⟩
          · simp [piece, smoothFormsPointwiseSMul_toFun, hzero y hyC]
        have hjoined : JoinedIn V (j : X) (y₀ : X) :=
          hVpath.joinedIn (j : X) (hCV (j : C).2) (y₀ : X) (hTV y₀.2)
        obtain ⟨eta, beta, Tj, KTj, _hy₀Tj, hTj,
            _hphiTj, hKTj, hd, heta, hbeta⟩ :=
          exists_compactSupport_transport_along_path
            Vopen T (U (j : C)) (Classical.choice (hphiU (j : C)))
            hjoined.somePath hjoined.somePath_mem y₀.2 (hpU (j : C))
            (hUV (j : C)) Kj hKjcompact (piece (some j)) hpieceZero
        let targetCore : Set X := smoothFormCompactCore Tj KTj
        have htargetCompact : IsCompact targetCore :=
          smoothFormCompactCore_isCompact Tj KTj hKTj
        have htargetT : targetCore ⊆ T := by
          intro y hy
          exact (hTj.trans inf_le_right)
            (smoothFormCompactCore_subset Tj KTj hy)
        exact ⟨eta, beta, targetCore, htargetCompact, htargetT,
          hd, heta, hbeta⟩
  choose eta beta targetCore htargetCompact htargetT hd heta hbeta using
    hpiece_transport
  let targetUnion : Set X := ⋃ i : Option J, targetCore i
  have htargetUnionCompact : IsCompact targetUnion :=
    isCompact_iUnion htargetCompact
  have htargetUnionT : targetUnion ⊆ T := by
    intro y hy
    rcases mem_iUnion.mp hy with ⟨i, hyi⟩
    exact htargetT i hyi
  let KT : Set T := smoothFormCompactCoreInOpen T targetUnion
  have hKTcompact : IsCompact KT :=
    smoothFormCompactCoreInOpen_isCompact
      T targetUnion htargetUnionCompact htargetUnionT
  let etaSum := ∑ i : Option J, eta i
  let betaSum := ∑ i : Option J, beta i
  refine ⟨etaSum, betaSum, KT, hKTcompact, ?_, ?_, ?_⟩
  · rw [map_sum]
    calc
      ∑ i : Option J,
          deRhamDifferential
            (I := SurfaceRealModel) (M := X) (A := ℝ) 1 (eta i) =
          ∑ i : Option J, (piece i - beta i) := by
            apply Finset.sum_congr rfl
            intro i _hi
            exact hd i
      _ = (∑ i : Option J, piece i) - ∑ i : Option J, beta i := by
            rw [Finset.sum_sub_distrib]
      _ = omega - betaSum := by
        congr 1
        apply smoothFormsPointwiseSMul_finset_sum_eq_self_of_sum_eq_one
        intro y
        have hsum := rho.sum_eq_one (show y ∈ (univ : Set X) by simp)
        simpa [finsum_eq_sum_of_fintype] using hsum
  · intro y hyV
    rw [smoothForms_finset_sum_toFun
      SurfaceRealModel eta (Finset.univ : Finset (Option J)) y]
    simp_rw [heta _ y hyV]
    simp
  · intro y hyKT
    have hyUnion : y ∉ targetUnion := by
      rwa [smoothFormCompactCore_coreInOpen
        T targetUnion htargetUnionT] at hyKT
    rw [smoothForms_finset_sum_toFun
      SurfaceRealModel beta (Finset.univ : Finset (Option J)) y]
    apply Finset.sum_eq_zero
    intro i _hi
    exact hbeta i y (fun hyCore ↦ hyUnion (mem_iUnion.mpr ⟨i, hyCore⟩))

end

end JJMath.Uniformization
