import JJMath.Manifold.DeRhamComparison.Final

/-!
# De Rham theorem

This file contains the comparison layer between real de Rham cohomology and
real singular cohomology.  It is kept separate from `JJMath.Manifold.DeRham`
so that the basic de Rham complex and Mayer-Vietoris API do not have to import
the singular cohomology development.
-/

open scoped Manifold ContDiff Topology
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace

namespace JJMath
namespace Manifold

noncomputable section

universe v w m

variable {E : Type v} [NormedAddCommGroup E]
variable {H : Type w} [TopologicalSpace H]
variable {M : Type m} [TopologicalSpace M] [ChartedSpace H M]

/--
%%handwave
name:
  De Rham comparison theorem
statement:
  Let $M$ be a finite-dimensional Hausdorff sigma-compact smooth manifold
  without boundary.  For every $n\geq0$, its real de Rham cohomology and real
  singular cohomology are linearly equivalent:
  \[
    H_{\mathrm{dR}}^n(M;\mathbb R)
      \cong_{\mathbb R} H_{\mathrm{sing}}^n(M;\mathbb R).
  \]
proof:
  By [the scalar-compatible de Rham comparison with ordinary constant-sheaf cohomology](lean:JJMath.Manifold.exists_deRhamCohomology_addEquiv_realConstantSheafCohomology_with_smul), de Rham cohomology computes $H^n(M;\underline{\mathbb R})$.  The manifold is locally contractible and every open subspace is paracompact, so [the scalar-compatible singular comparison with the same constant-sheaf cohomology](lean:JJMath.Cohomology.exists_realSingularCohomology_addEquiv_realConstantSheafCohomology_with_smul_of_open_paracompact) applies.  Compose the first equivalence with the inverse of the second.
tags:
  milestone
-/
theorem deRhamCohomology_nonempty_linearEquiv_realSingularCohomology
    [NormedSpace ℝ E] (Iℝ : ModelWithCorners ℝ E H) [Iℝ.Boundaryless]
    [IsManifold Iℝ ∞ M] [FiniteDimensional ℝ E]
    [T2Space M] [SigmaCompactSpace M]
    (n : ℕ) :
    Nonempty
      (DeRhamCohomology (I := Iℝ) (M := M) (A := ℝ) n ≃ₗ[ℝ]
        ↥(JJMath.Cohomology.RealSingularCohomology
          (TopCat.of M : TopCat.{m}) n)) := by
  let X : TopCat.{m} := TopCat.of M
  letI : ParacompactSpace M :=
    smoothManifold_paracompactSpace_of_t2_sigmaCompact (M := M) Iℝ
  have hlocM : LocallyContractibleSpace M :=
    smoothManifold_locallyContractibleSpace (M := M) Iℝ
  letI :
      HasSheafify
        (Opens.grothendieckTopology X)
        AddCommGrpCat.{m} :=
    JJMath.Cohomology.opens_addCommGrp_hasSheafify X
  letI :
      HasExt.{m}
        (Sheaf
          (Opens.grothendieckTopology X)
          AddCommGrpCat.{m}) :=
    JJMath.Cohomology.opens_addCommGrp_hasExt X
  letI :
      HasSheafify
        (Opens.grothendieckTopology X)
        AddCommGrpCat.{max v m} :=
    opens_addCommGrp_hasSheafify_smoothFormsUniverse X
  letI :
      HasExt.{max v m}
        (Sheaf
          (Opens.grothendieckTopology X)
          AddCommGrpCat.{max v m}) :=
    opens_addCommGrp_hasExt_smoothFormsUniverse X
  have hopen :
      ∀ U : TopologicalSpace.Opens X, ParacompactSpace U := by
    intro U
    exact smoothManifold_open_paracompactSpace (M := M) Iℝ U
  have hloc : LocallyContractibleSpace X := by
    simpa [X] using hlocM
  rcases
      exists_deRhamCohomology_addEquiv_realConstantSheafCohomology_with_smul
        (M := M) Iℝ n with
    ⟨eDeRham, hDeRham⟩
  rcases
      JJMath.Cohomology.exists_realSingularCohomology_addEquiv_realConstantSheafCohomology_with_smul_of_open_paracompact
        X hopen hloc n with
    ⟨eSingular, hSingular⟩
  have hSingularSymm
      (r : ℝ)
      (α : JJMath.Cohomology.RealConstantSheafCohomology X n) :
      eSingular.symm
          (JJMath.Cohomology.realConstantSheafCohomologySMul
            X n r α) =
        r • eSingular.symm α := by
    apply eSingular.injective
    rw [eSingular.apply_symm_apply, hSingular,
      eSingular.apply_symm_apply]
    exact
      (JJMath.Cohomology.realConstantSheafCohomology_smul_eq
        X n r α).symm
  let e :
      DeRhamCohomology (I := Iℝ) (M := M) (A := ℝ) n ≃+
        ↥(JJMath.Cohomology.RealSingularCohomology X n) :=
    eDeRham.trans eSingular.symm
  refine
    ⟨{ toAddEquiv := e
       map_smul' := ?_ }⟩
  intro r α
  change eSingular.symm (eDeRham (r • α)) =
    r • eSingular.symm (eDeRham α)
  rw [hDeRham]
  exact hSingularSymm r (eDeRham α)
end

end Manifold
end JJMath
