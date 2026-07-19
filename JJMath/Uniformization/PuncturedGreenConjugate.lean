import JJMath.Uniformization.GreenFunctionCompactSuperlevel
import JJMath.Uniformization.HarmonicConjugateDeRham

/-!
# The conjugate differential of a Green potential

The negative of a compact-superlevel Green potential is harmonic away from
its pole.  Its local holomorphic real-part branches therefore have compatible
imaginary differentials, which glue to a closed one-form on the punctured
surface.  Keeping the branch data together with the glued form is useful for
the subsequent residue calculation at the pole.
-/

open Set
open scoped Manifold ContDiff Topology

namespace JJMath
namespace Uniformization

open JJMath.Manifold

noncomputable section

/-- The punctured surface as an open submanifold. -/
def puncturedSurfaceOpen
    {X : Type} [TopologicalSpace X] [T1Space X] (p : X) :
    TopologicalSpace.Opens X :=
  ⟨{x : X | x ≠ p}, isOpen_ne⟩

/-- A Riemann surface remains a Riemann surface after
removing one point.

%%handwave
name: Riemann-surface structure on a punctured surface
statement:
  If $X$ is a Riemann surface and $p\in X$, then $X\setminus\{p\}$, with the induced open-submanifold charts, is a Riemann surface.
proof:
  A Riemann surface has another point besides $p$, and its punctured complement is connected. Restrict the complex atlas to this nonempty connected open subset.
-/
theorem puncturedSurfaceOpen_riemannSurface
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (p : X) :
    RiemannSurface (puncturedSurfaceOpen p) := by
  haveI : Nontrivial X := riemannSurface_nontrivial X p
  rcases exists_ne p with ⟨q, hqp⟩
  exact riemannSurface_openSubset (puncturedSurfaceOpen p)
    ⟨q, hqp⟩ (by
      simpa [puncturedSurfaceOpen] using
        punctured_riemannSurface_preconnected X p)

noncomputable instance puncturedSurfaceOpen.instRiemannSurface
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] (p : X) :
    RiemannSurface (puncturedSurfaceOpen p) :=
  puncturedSurfaceOpen_riemannSurface X p

/-- Branches and their glued imaginary differential on the punctured
surface. -/
structure CompactSuperlevelGreenFunctionPuncturedConjugateDifferentialData
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    {p : X} (G : CompactSuperlevelGreenFunctionWithPole X p) where
  branches : ∀ q : puncturedSurfaceOpen p,
    ∃ B : SurfaceHolomorphicRealPartBranch
      (puncturedSurfaceOpen p) (fun x ↦ -G.toFun x),
      q ∈ B.source
  conjugate : HarmonicConjugateDifferentialData branches

namespace CompactSuperlevelGreenFunctionPuncturedConjugateDifferentialData

/-- The glued conjugate differential, packaged as a closed de Rham form. -/
noncomputable def toClosedForm
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    {p : X} {G : CompactSuperlevelGreenFunctionWithPole X p}
    (D : CompactSuperlevelGreenFunctionPuncturedConjugateDifferentialData X G) :
    DeRhamClosedForms (I := SurfaceRealModel)
      (M := puncturedSurfaceOpen p) (A := ℝ) 1 :=
  D.conjugate.toClosedForm

end CompactSuperlevelGreenFunctionPuncturedConjugateDifferentialData

/--
%%handwave
name:
  The Green conjugate differential on the punctured surface
statement:
  If (G) is a Green potential with pole (p), the imaginary differentials
  of local holomorphic functions with real part (-G) glue to a closed smooth
  one-form on the punctured surface (X\setminus\{p\}).
proof:
  The punctured surface is connected.  The function (-G) is harmonic there,
  so it is locally the real part of a holomorphic function.  Two such local
  functions differ by an imaginary constant on connected overlaps; hence
  their imaginary differentials agree and glue.  Local exactness also shows
  that the glued one-form is closed.
-/
theorem compactSuperlevelGreenFunction_puncturedConjugateDifferentialData_nonempty
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    {p : X} (G : CompactSuperlevelGreenFunctionWithPole X p) :
    Nonempty
      (CompactSuperlevelGreenFunctionPuncturedConjugateDifferentialData X G) := by
  let U : TopologicalSpace.Opens X := puncturedSurfaceOpen p
  letI : RiemannSurface U :=
    puncturedSurfaceOpen_riemannSurface X p
  have hneg :
      IsHarmonicOnSurface (U : Set X) (fun x : X ↦ -G.toFun x) := by
    simpa [U, puncturedSurfaceOpen] using
      harmonicOnSurface_neg G.harmonic_away_pole
  have hnegU : IsHarmonicOnSurface (Set.univ : Set U)
      (fun x : U ↦ -G.toFun x) :=
    harmonicOnSurface_openSubtype_univ_of_ambient U hneg
  let branches : ∀ q : U,
      ∃ B : SurfaceHolomorphicRealPartBranch U (fun x ↦ -G.toFun x),
        q ∈ B.source :=
    fun q ↦ harmonicOnSurface_exists_local_holomorphicRealPartBranch hnegU q
  rcases exists_harmonicConjugateDifferentialData branches with ⟨D⟩
  exact ⟨{ branches := branches, conjugate := D }⟩

end
end Uniformization
end JJMath
