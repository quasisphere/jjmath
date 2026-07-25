import JJMath.Manifold.CirclePrimitive
import JJMath.Uniformization.CirclePrimitiveHolomorphicExp
import JJMath.Uniformization.CirclePrimitiveIntegralPeriods
import JJMath.Uniformization.GreenFunctionResidue
import JJMath.Uniformization.PoleProperLineTube
import JJMath.Uniformization.GreenPuncturedExponential
import JJMath.Uniformization.PuncturedAngularCirclePrimitive

/-!
# Circle primitives of Green conjugate differentials

The conjugate differential of a Green function need not have a global
real-valued primitive on the punctured surface.  Its exponential only needs a
circle-valued primitive.  This file turns the residue decomposition into that
circle primitive once the angular generator is supplied with its standard
integral normalization.
-/

open Set
open scoped Manifold ContDiff Topology

namespace JJMath
namespace Uniformization

open JJMath.Manifold

noncomputable section

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
  [RiemannSurface X]
  {p : X} {G : CompactSuperlevelGreenFunctionWithPole X p}
  {P : CompactSuperlevelGreenFunctionPoleExponentialBranch X G}

/--
%%handwave
name:
  Holomorphic exponential of a Green conjugate circle primitive
statement:
  Let \(G\) be a compact-superlevel Green function with pole \(p\), and let
  \(\omega\) be its conjugate differential on \(X\setminus\{p\}\).  If
  \(\omega\) has a smooth circle-valued primitive, then there is a
  holomorphic function \(f:X\setminus\{p\}\to\mathbb C\) such that
  \[
    f(z)\ne0,\qquad \log|f(z)|=-G(z)
    \quad(z\ne p).
  \]
proof:
  Apply the holomorphic-exponential construction for a harmonic function and
  a circle-valued primitive of its conjugate differential.
-/
theorem CompactSuperlevelGreenFunctionPuncturedConjugateDifferentialData.circlePrimitive_has_holomorphic_exp
    [IsManifold SurfaceRealModel ∞ X]
    (C : CompactSuperlevelGreenFunctionPuncturedConjugateDifferentialData X G)
    (PC : SmoothCirclePrimitive SurfaceRealModel C.conjugate.omega) :
    ∃ f : puncturedSurfaceOpen p → ℂ,
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f ∧
        (∀ z, f z ≠ 0) ∧
          ∀ z, Real.log ‖f z‖ = -G.toFun (z : X) := by
  simpa using
    (harmonicConjugate_circlePrimitive_has_holomorphic_exp C.conjugate PC)

/--
%%handwave
name:
  A Green conjugate circle primitive gives a punctured plane map
statement:
  Suppose the Green conjugate differential \(\omega\) has a smooth
  circle-valued primitive and a local exponential branch at the pole has
  been fixed.  Then there is a punctured Green plane map whose modulus
  satisfies \(\log|F|=-G\) and which has the prescribed first-order
  factorization near the pole.
proof:
  Exponentiate the circle primitive to obtain a nonvanishing holomorphic
  function with logarithmic modulus \(-G\), then combine it with the fixed
  pole branch in the punctured-plane-map construction.
-/
theorem CompactSuperlevelGreenFunctionPuncturedConjugateDifferentialData.circlePrimitive_has_puncturedPlaneMap
    [IsManifold SurfaceRealModel ∞ X]
    (C : CompactSuperlevelGreenFunctionPuncturedConjugateDifferentialData X G)
    (P : CompactSuperlevelGreenFunctionPoleExponentialBranch X G)
    (PC : SmoothCirclePrimitive SurfaceRealModel C.conjugate.omega) :
    Nonempty (CompactSuperlevelGreenFunctionPuncturedPlaneMap X G) := by
  rcases C.circlePrimitive_has_holomorphic_exp PC with
    ⟨f, hf, hf_nonzero, hf_log⟩
  exact ⟨compactSuperlevelGreenFunction_puncturedPlaneMap_of_holomorphicExp
    P f hf hf_nonzero hf_log⟩

/--
%%handwave
name:
  A Green conjugate circle primitive gives a global plane map
statement:
  Under the same hypotheses, there exists a global holomorphic Green plane
  map \(F:X\to\mathbb C\) extending the punctured map and having a simple
  zero at the pole.
proof:
  First construct the punctured plane map from the circle primitive.  Its
  prescribed first-order pole factorization extends holomorphically across
  the puncture and supplies the required global plane map.
-/
theorem CompactSuperlevelGreenFunctionPuncturedConjugateDifferentialData.circlePrimitive_has_planeMap
    [IsManifold SurfaceRealModel ∞ X]
    (C : CompactSuperlevelGreenFunctionPuncturedConjugateDifferentialData X G)
    (P : CompactSuperlevelGreenFunctionPoleExponentialBranch X G)
    (PC : SmoothCirclePrimitive SurfaceRealModel C.conjugate.omega) :
    Nonempty (CompactSuperlevelGreenFunctionPlaneMap X G) := by
  rcases C.circlePrimitive_has_puncturedPlaneMap P PC with ⟨F⟩
  exact compactSuperlevelGreenFunctionPuncturedPlaneMap_extends_to_planeMap
    X G F

/--
%%handwave
name:
  Exponentiating the Green conjugate from an integral angular generator
statement:
  Suppose the conjugate differential of a Green function on the punctured
  surface is an angular generator with residue \(2\pi\), up to orientation,
  plus an exact one-form.  If the angular generator has a circle-valued
  primitive after multiplication by \(2\pi\), then the full conjugate
  differential has a circle-valued primitive.
proof:
  Reverse the circle orientation when the residue is \(-2\pi\), then multiply
  the phase by the exponential of a primitive of the exact remainder.
-/
noncomputable def greenConjugateCirclePrimitiveOfAngular
    [IsManifold SurfaceRealModel ∞ X]
    (C : CompactSuperlevelGreenFunctionPuncturedConjugateDifferentialData X G)
    (v : Circle)
    (eta : DeRhamClosedForms (I := SurfaceRealModel)
      (M := puncturedSurfaceOpen p) (A := ℝ) 1)
    (theta : SmoothForms (I := SurfaceRealModel)
      (M := puncturedSurfaceOpen p) ℝ 0)
    (hdecomposition :
      C.conjugate.omega =
        annularAngleTransitionCoefficient v • eta.1 +
          deRhamDifferential (I := SurfaceRealModel)
            (M := puncturedSurfaceOpen p) (A := ℝ) 0 theta)
    (Peta : SmoothCirclePrimitive SurfaceRealModel
      ((2 * Real.pi) • eta.1)) :
    SmoothCirclePrimitive SurfaceRealModel C.conjugate.omega := by
  have homega :
      C.conjugate.omega = (2 * Real.pi) • eta.1 +
          deRhamDifferential (I := SurfaceRealModel)
            (M := puncturedSurfaceOpen p) (A := ℝ) 0 theta ∨
        C.conjugate.omega = -(2 * Real.pi) • eta.1 +
          deRhamDifferential (I := SurfaceRealModel)
            (M := puncturedSurfaceOpen p) (A := ℝ) 0 theta := by
    rcases annularAngleTransitionCoefficient_eq_two_pi_or_neg v with h | h
    · left
      simpa [h] using hdecomposition
    · right
      simpa [h] using hdecomposition
  exact SmoothCirclePrimitive.angularAddExact SurfaceRealModel Peta theta homega

/--
%%handwave
name:
  Green plane map from a locally normalized angular circle phase
statement:
  Assume \(H^1_{\mathrm{dR}}(X;\mathbb R)=0\), and write the Green conjugate
  differential as
  \[
    \omega=\epsilon\,2\pi\,\eta+d\theta,
    \qquad \epsilon\in\{1,-1\}.
  \]
  Let \(\tau\) be a closed one-form whose normalized form \(2\pi\tau\) has a
  circle-valued primitive.  If the restrictions of \(\eta\) and \(\tau\) to
  a punctured coordinate disk represent equal or opposite de Rham classes,
  then the Green plane map exists.
proof:
  The local class comparison and vanishing global first cohomology transfer
  the circle primitive from \(2\pi\tau\) to \(2\pi\eta\).  Adding the exact
  term \(d\theta\), with the appropriate orientation, gives a circle
  primitive of \(\omega\), which exponentiates to the plane map.
-/
theorem greenConjugate_planeMap_of_local_angular_circlePrimitive
    [IsManifold SurfaceRealModel ∞ X]
    [Subsingleton
      (DeRhamCohomology (I := SurfaceRealModel) (M := X) (A := ℝ) 1)]
    (C : CompactSuperlevelGreenFunctionPuncturedConjugateDifferentialData X G)
    (P : CompactSuperlevelGreenFunctionPoleExponentialBranch X G)
    (v : Circle)
    (D₀ : ClosedCoordinateDisk X)
    (hp : p ∈ D₀.expandedOpenDisk D₀.closedRadius)
    (eta tau : DeRhamClosedForms (I := SurfaceRealModel)
      (M := puncturedSurfaceOpen p) (A := ℝ) 1)
    (theta : SmoothForms (I := SurfaceRealModel)
      (M := puncturedSurfaceOpen p) ℝ 0)
    (hdecomposition :
      C.conjugate.omega =
        annularAngleTransitionCoefficient v • eta.1 +
          deRhamDifferential (I := SurfaceRealModel)
            (M := puncturedSurfaceOpen p) (A := ℝ) 0 theta)
    (hlocal :
      puncturedCoordinateDiskDeRhamH1Class p D₀ eta =
          puncturedCoordinateDiskDeRhamH1Class p D₀ tau ∨
        puncturedCoordinateDiskDeRhamH1Class p D₀ eta =
          -puncturedCoordinateDiskDeRhamH1Class p D₀ tau)
    (Ptau : SmoothCirclePrimitive SurfaceRealModel
      ((2 * Real.pi) • tau.1)) :
    Nonempty (CompactSuperlevelGreenFunctionPlaneMap X G) := by
  let Peta : SmoothCirclePrimitive SurfaceRealModel
      ((2 * Real.pi) • eta.1) :=
    puncturedAngularCirclePrimitive_of_local_class_eq_or_neg
      p D₀ hp eta tau hlocal Ptau
  let PC : SmoothCirclePrimitive SurfaceRealModel C.conjugate.omega :=
    greenConjugateCirclePrimitiveOfAngular C v eta theta
      hdecomposition Peta
  exact C.circlePrimitive_has_planeMap P PC

/--
%%handwave
name:
  Green conjugate exponentiation reduces to the angular generator
statement:
  On a noncompact Riemann surface with vanishing first real de Rham
  cohomology, the conjugate differential of a compact-superlevel Green
  function admits an angular representative and an exact remainder.  For
  that representative, a circle-valued primitive with period \(2\pi\)
  produces a circle-valued primitive of the conjugate differential.
proof:
  Use the residue decomposition into an angular term and an exact term, then
  apply the preceding exponentiation construction.
-/
theorem exists_puncturedAngularForm_greenConjugate_circlePrimitive_reduction
    [IsManifold SurfaceRealModel ∞ X] [NoncompactSpace X]
    [Subsingleton
      (DeRhamCohomology (I := SurfaceRealModel) (M := X) (A := ℝ) 1)]
    (E : SmoothRelativelyCompactExhaustion X)
    (D : CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    (C : CompactSuperlevelGreenFunctionPuncturedConjugateDifferentialData X G)
    (v : Circle) :
    ∃ eta : DeRhamClosedForms (I := SurfaceRealModel)
        (M := puncturedSurfaceOpen p) (A := ℝ) 1,
      ∃ theta : SmoothForms (I := SurfaceRealModel)
          (M := puncturedSurfaceOpen p) ℝ 0,
        C.conjugate.omega =
            annularAngleTransitionCoefficient v • eta.1 +
              deRhamDifferential (I := SurfaceRealModel)
                (M := puncturedSurfaceOpen p) (A := ℝ) 0 theta ∧
          (Nonempty (SmoothCirclePrimitive SurfaceRealModel
              ((2 * Real.pi) • eta.1)) →
            Nonempty (SmoothCirclePrimitive SurfaceRealModel
              C.conjugate.omega)) := by
  rcases D.exists_puncturedAngularForm_greenConjugate_exact_decomposition E C v with
    ⟨eta, theta, hdecomposition⟩
  refine ⟨eta, theta, hdecomposition, ?_⟩
  rintro ⟨Peta⟩
  exact ⟨greenConjugateCirclePrimitiveOfAngular C v eta theta
    hdecomposition Peta⟩

end
end Uniformization
end JJMath
