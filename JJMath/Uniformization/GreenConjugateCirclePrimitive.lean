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
  Green plane map from one normalized local period
statement:
  In the preceding setting, let \(c\) be a closed one-chain in a punctured
  coordinate annulus.  Suppose
  \[
    \int_c\eta=\pm\int_c\tau,\qquad \int_c\tau\ne0,
  \]
  and \(2\pi\tau\) has a circle-valued primitive.  Then the Green plane map
  exists.
proof:
  On a punctured disk, one nonzero period detects the one-dimensional first
  de Rham class, so the period identity makes the local classes of
  \(\eta\) and \(\tau\) equal up to sign.  Transfer the circle primitive and
  apply the angular-plus-exact Green conjugate construction.
-/
theorem greenConjugate_planeMap_of_local_period_circlePrimitive
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
    (phi : (puncturedSurfaceOpen p ⊓
        ⟨D₀.expandedOpenDisk D₀.closedRadius,
          D₀.expandedOpenDisk_isOpen D₀.closedRadius⟩ :
          TopologicalSpace.Opens X) ≃ₘ⟮SurfaceRealModel,
            AnnularCylinderModel⟯ Circle × ℝ)
    (c : SingularChain (I := SurfaceRealModel)
      (M := (puncturedSurfaceOpen p ⊓
        ⟨D₀.expandedOpenDisk D₀.closedRadius,
          D₀.expandedOpenDisk_isOpen D₀.closedRadius⟩ :
            TopologicalSpace.Opens X)) 1 ∞)
    (hcycle : boundary (I := SurfaceRealModel) c = 0)
    (hperiod :
      integrateSmoothChain (I := SurfaceRealModel)
          (deRhamClosedFormsRestrictionOfLE
            (I := SurfaceRealModel) (A := ℝ) inf_le_left 1 eta).1 c =
          integrateSmoothChain (I := SurfaceRealModel)
            (deRhamClosedFormsRestrictionOfLE
              (I := SurfaceRealModel) (A := ℝ) inf_le_left 1 tau).1 c ∨
      integrateSmoothChain (I := SurfaceRealModel)
          (deRhamClosedFormsRestrictionOfLE
            (I := SurfaceRealModel) (A := ℝ) inf_le_left 1 eta).1 c =
          -integrateSmoothChain (I := SurfaceRealModel)
            (deRhamClosedFormsRestrictionOfLE
              (I := SurfaceRealModel) (A := ℝ) inf_le_left 1 tau).1 c)
    (htauPeriod :
      integrateSmoothChain (I := SurfaceRealModel)
        (deRhamClosedFormsRestrictionOfLE
          (I := SurfaceRealModel) (A := ℝ) inf_le_left 1 tau).1 c ≠ 0)
    (Ptau : SmoothCirclePrimitive SurfaceRealModel
      ((2 * Real.pi) • tau.1)) :
    Nonempty (CompactSuperlevelGreenFunctionPlaneMap X G) := by
  let Peta : SmoothCirclePrimitive SurfaceRealModel
      ((2 * Real.pi) • eta.1) :=
    puncturedAngularCirclePrimitive_of_local_period_eq_or_neg
      p D₀ hp eta tau phi v c hcycle hperiod htauPeriod Ptau
  let PC : SmoothCirclePrimitive SurfaceRealModel C.conjugate.omega :=
    greenConjugateCirclePrimitiveOfAngular C v eta theta
      hdecomposition Peta
  exact C.circlePrimitive_has_planeMap P PC

/--
%%handwave
name:
  Green plane map from matching proper-line tube periods
statement:
  Let \(\eta\) be the angular term in
  \(\omega=\pm2\pi\eta+d\theta\), and let \(\tau\) be the closed Thom form of
  a proper-line tube.  If a closed chain \(c\) in the punctured coordinate
  annulus satisfies
  \[
    \int_c\eta\in\{1,-1\},
    \qquad
    \int_c\tau\in\{1,-1\},
  \]
  then the Green plane map exists.
proof:
  The two periods agree up to sign and the period of \(\tau\) is nonzero.
  The proper-line tube supplies a circle primitive of \(2\pi\tau\), so the
  normalized local-period criterion applies.
-/
theorem greenConjugate_planeMap_of_properLineTube_periods
    [IsManifold SurfaceRealModel ∞ X]
    [Subsingleton
      (DeRhamCohomology (I := SurfaceRealModel) (M := X) (A := ℝ) 1)]
    (C : CompactSuperlevelGreenFunctionPuncturedConjugateDifferentialData X G)
    (P : CompactSuperlevelGreenFunctionPoleExponentialBranch X G)
    (v : Circle)
    (D₀ : ClosedCoordinateDisk X)
    (hp : p ∈ D₀.expandedOpenDisk D₀.closedRadius)
    (eta : DeRhamClosedForms (I := SurfaceRealModel)
      (M := puncturedSurfaceOpen p) (A := ℝ) 1)
    (theta : SmoothForms (I := SurfaceRealModel)
      (M := puncturedSurfaceOpen p) ℝ 0)
    (hdecomposition :
      C.conjugate.omega =
        annularAngleTransitionCoefficient v • eta.1 +
          deRhamDifferential (I := SurfaceRealModel)
            (M := puncturedSurfaceOpen p) (A := ℝ) 0 theta)
    (tubeU : TopologicalSpace.Opens (puncturedSurfaceOpen p))
    (tubePhi : tubeU ≃ₘ⟮SurfaceRealModel,
      ProperLineTubeModel⟯ ℝ × ℝ)
    (hcore : IsClosed
      (properLineTubeCore SurfaceRealModel tubeU tubePhi))
    (annulusPhi : (puncturedSurfaceOpen p ⊓
        ⟨D₀.expandedOpenDisk D₀.closedRadius,
          D₀.expandedOpenDisk_isOpen D₀.closedRadius⟩ :
          TopologicalSpace.Opens X) ≃ₘ⟮SurfaceRealModel,
            AnnularCylinderModel⟯ Circle × ℝ)
    (c : SingularChain (I := SurfaceRealModel)
      (M := (puncturedSurfaceOpen p ⊓
        ⟨D₀.expandedOpenDisk D₀.closedRadius,
          D₀.expandedOpenDisk_isOpen D₀.closedRadius⟩ :
            TopologicalSpace.Opens X)) 1 ∞)
    (hcycle : boundary (I := SurfaceRealModel) c = 0)
    (hetaPeriod :
      integrateSmoothChain (I := SurfaceRealModel)
          (deRhamClosedFormsRestrictionOfLE
            (I := SurfaceRealModel) (A := ℝ) inf_le_left 1 eta).1 c = 1 ∨
      integrateSmoothChain (I := SurfaceRealModel)
          (deRhamClosedFormsRestrictionOfLE
            (I := SurfaceRealModel) (A := ℝ) inf_le_left 1 eta).1 c = -1)
    (htubePeriod :
      integrateSmoothChain (I := SurfaceRealModel)
          (deRhamClosedFormsRestrictionOfLE
            (I := SurfaceRealModel) (A := ℝ) inf_le_left 1
              (properLineTubeClosedOneForm SurfaceRealModel
                tubeU tubePhi hcore)).1 c = 1 ∨
      integrateSmoothChain (I := SurfaceRealModel)
          (deRhamClosedFormsRestrictionOfLE
            (I := SurfaceRealModel) (A := ℝ) inf_le_left 1
              (properLineTubeClosedOneForm SurfaceRealModel
                tubeU tubePhi hcore)).1 c = -1) :
    Nonempty (CompactSuperlevelGreenFunctionPlaneMap X G) := by
  let tau : DeRhamClosedForms (I := SurfaceRealModel)
      (M := puncturedSurfaceOpen p) (A := ℝ) 1 :=
    properLineTubeClosedOneForm SurfaceRealModel tubeU tubePhi hcore
  have hperiod :
      integrateSmoothChain (I := SurfaceRealModel)
          (deRhamClosedFormsRestrictionOfLE
            (I := SurfaceRealModel) (A := ℝ) inf_le_left 1 eta).1 c =
          integrateSmoothChain (I := SurfaceRealModel)
            (deRhamClosedFormsRestrictionOfLE
              (I := SurfaceRealModel) (A := ℝ) inf_le_left 1 tau).1 c ∨
      integrateSmoothChain (I := SurfaceRealModel)
          (deRhamClosedFormsRestrictionOfLE
            (I := SurfaceRealModel) (A := ℝ) inf_le_left 1 eta).1 c =
          -integrateSmoothChain (I := SurfaceRealModel)
            (deRhamClosedFormsRestrictionOfLE
              (I := SurfaceRealModel) (A := ℝ) inf_le_left 1 tau).1 c := by
    rcases hetaPeriod with hetaPeriod | hetaPeriod <;>
      rcases htubePeriod with htubePeriod | htubePeriod
    · left
      rw [hetaPeriod]
      simpa [tau] using htubePeriod.symm
    · right
      rw [hetaPeriod]
      have htubePeriod' : integrateSmoothChain (I := SurfaceRealModel)
          (deRhamClosedFormsRestrictionOfLE
            (I := SurfaceRealModel) (A := ℝ) inf_le_left 1 tau).1 c = -1 := by
        simpa [tau] using htubePeriod
      rw [htubePeriod']
      norm_num
    · right
      rw [hetaPeriod]
      simpa [tau] using (congrArg Neg.neg htubePeriod).symm
    · left
      rw [hetaPeriod]
      simpa [tau] using htubePeriod.symm
  have htauPeriod :
      integrateSmoothChain (I := SurfaceRealModel)
        (deRhamClosedFormsRestrictionOfLE
          (I := SurfaceRealModel) (A := ℝ) inf_le_left 1 tau).1 c ≠ 0 := by
    rcases htubePeriod with htubePeriod | htubePeriod
    · rw [show integrateSmoothChain (I := SurfaceRealModel)
          (deRhamClosedFormsRestrictionOfLE
            (I := SurfaceRealModel) (A := ℝ) inf_le_left 1 tau).1 c = 1 by
        simpa [tau] using htubePeriod]
      norm_num
    · rw [show integrateSmoothChain (I := SurfaceRealModel)
          (deRhamClosedFormsRestrictionOfLE
            (I := SurfaceRealModel) (A := ℝ) inf_le_left 1 tau).1 c = -1 by
        simpa [tau] using htubePeriod]
      norm_num
  let Ptau : SmoothCirclePrimitive SurfaceRealModel
      ((2 * Real.pi) • tau.1) :=
    properLineTubeCirclePrimitive SurfaceRealModel tubeU tubePhi hcore
  exact greenConjugate_planeMap_of_local_period_circlePrimitive
    C P v D₀ hp eta tau theta hdecomposition annulusPhi c hcycle
      hperiod htauPeriod Ptau

/--
%%handwave
name:
  Reduction to the proper-line Thom period on a normalized pole cycle
statement:
  Fix an exhaustion, pole-coordinate Green data, conjugate-differential
  data, and a proper-line tube in \(X\setminus\{p\}\).  There is a closed
  one-chain \(c\) in the punctured pole-coordinate region such that
  \[
    \int_c\tau\in\{1,-1\}
    \quad\Longrightarrow\quad
    \text{a global Green plane map exists},
  \]
  where \(\tau\) is the tube's closed Thom form restricted to that region.
proof:
  The residue construction supplies an angular form \(\eta\), an exact
  remainder, and a normalized pole cycle with \(\int_c\eta=-1\).  Transport
  the cycle to the standard punctured annulus.  If the Thom period is
  \(\pm1\), the angular and Thom periods agree up to sign, so the
  proper-line-tube period criterion produces the plane map.
-/
theorem exists_normalizedPoleCycle_greenConjugate_planeMap_of_properLineTube
    [IsManifold SurfaceRealModel ∞ X] [NoncompactSpace X]
    [Subsingleton
      (DeRhamCohomology (I := SurfaceRealModel) (M := X) (A := ℝ) 1)]
    (E : SmoothRelativelyCompactExhaustion X)
    (D : CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    (C : CompactSuperlevelGreenFunctionPuncturedConjugateDifferentialData X G)
    (v : Circle)
    (tubeU : TopologicalSpace.Opens (puncturedSurfaceOpen p))
    (tubePhi : tubeU ≃ₘ⟮SurfaceRealModel,
      ProperLineTubeModel⟯ ℝ × ℝ)
    (hcore : IsClosed
      (properLineTubeCore SurfaceRealModel tubeU tubePhi)) :
    let Q := D.puncturedPoleDisk ⊓
      ⟨D.closedDisk.toSmoothBoundaryDomain.carrier,
        D.closedDisk.toSmoothBoundaryDomain.isOpen⟩
    ∃ c : SingularChain (I := SurfaceRealModel) (M := Q) 1 ∞,
      boundary (I := SurfaceRealModel) c = 0 ∧
        ((integrateSmoothChain (I := SurfaceRealModel)
            (deRhamClosedFormsRestrictionOfLE
              (I := SurfaceRealModel) (A := ℝ)
              (inf_le_left.trans D.puncturedPoleDisk_le_puncturedSurfaceOpen)
              1 (properLineTubeClosedOneForm SurfaceRealModel
                tubeU tubePhi hcore)).1 c = 1 ∨
          integrateSmoothChain (I := SurfaceRealModel)
            (deRhamClosedFormsRestrictionOfLE
              (I := SurfaceRealModel) (A := ℝ)
              (inf_le_left.trans D.puncturedPoleDisk_le_puncturedSurfaceOpen)
              1 (properLineTubeClosedOneForm SurfaceRealModel
                tubeU tubePhi hcore)).1 c = -1) →
          Nonempty (CompactSuperlevelGreenFunctionPlaneMap X G)) := by
  dsimp only
  rcases
      D.exists_puncturedAngularForm_greenConjugate_exact_decomposition_normalized
        E C v with
    ⟨eta, theta, c, hdecomposition, hcycle, hetaPeriod⟩
  refine ⟨c, hcycle, ?_⟩
  intro htubePeriod
  let W := D.puncturedPoleDisk
  let D₀ := D.closedDisk
  let phi := D.radialDiffeomorph
  have hside : ∀ y : W,
      ((y : X) ∈ D₀.toSmoothBoundaryDomain.carrier ↔
        (phi y).2 < 0) := by
    intro y
    exact (D₀.radialPuncturedCollarDiffeomorph_second_lt_zero_iff
      p D.pole_mem_closedDisk_chart_source
      D.closedDisk_chart_p_eq_center
      D.closedDisk_double_closedRadius.le y).symm
  let annulusPhiRaw := sidePreservingAnnularCollarDomainDiffeomorph
    D₀.toSmoothBoundaryDomain W phi hside
  let annulusPhi : (puncturedSurfaceOpen p ⊓
      ⟨D₀.expandedOpenDisk D₀.closedRadius,
        D₀.expandedOpenDisk_isOpen D₀.closedRadius⟩ :
        TopologicalSpace.Opens X) ≃ₘ⟮SurfaceRealModel,
          AnnularCylinderModel⟯ Circle × ℝ := by
    rw [← D.puncturedPoleDisk_inf_innerDomain_eq]
    exact annulusPhiRaw
  have hp : p ∈ D₀.expandedOpenDisk D₀.closedRadius := by
    refine ⟨D.pole_mem_closedDisk_chart_source, ?_⟩
    change dist (D₀.openDisk.chart p) D₀.openDisk.center <
      D₀.closedRadius
    rw [show D₀.openDisk.chart p = D₀.openDisk.center by
      exact D.closedDisk_chart_p_eq_center]
    simpa using D₀.closedRadius_pos
  let Qlarge : TopologicalSpace.Opens X := D.puncturedPoleDisk ⊓
    ⟨D₀.toSmoothBoundaryDomain.carrier,
      D₀.toSmoothBoundaryDomain.isOpen⟩
  let Qsmall : TopologicalSpace.Opens X := puncturedSurfaceOpen p ⊓
    ⟨D₀.expandedOpenDisk D₀.closedRadius,
      D₀.expandedOpenDisk_isOpen D₀.closedRadius⟩
  have hQ : Qlarge = Qsmall := by
    simpa [Qlarge, Qsmall, D₀] using
      D.puncturedPoleDisk_inf_innerDomain_eq
  let qDiff : Qlarge ≃ₘ⟮SurfaceRealModel, SurfaceRealModel⟯ Qsmall :=
    opensDiffeomorphOfMutualLE Qlarge Qsmall hQ.le hQ.ge
  let cSmall : SingularChain (I := SurfaceRealModel)
      (M := Qsmall) 1 ∞ :=
    SingularChain.postcompose (I := SurfaceRealModel)
      qDiff.toContMDiffMap c
  have hcycleSmall : boundary (I := SurfaceRealModel) cSmall = 0 := by
    calc
      boundary (I := SurfaceRealModel) cSmall =
          SingularChain.postcompose (I := SurfaceRealModel)
            qDiff.toContMDiffMap
              (boundary (I := SurfaceRealModel) c) := by
                exact (SingularChain.postcompose_boundary
                  (I := SurfaceRealModel) qDiff.toContMDiffMap c).symm
      _ = 0 := by rw [hcycle]; simp
  have hpullback (omega : SmoothForms (I := SurfaceRealModel)
      (M := puncturedSurfaceOpen p) ℝ 1) :
      smoothFormsPullbackDiffeomorph SurfaceRealModel SurfaceRealModel
          qDiff 1
          (restrictSmoothFormsOfLE (I := SurfaceRealModel) (M := X)
            (A := ℝ) inf_le_left 1 omega) =
        restrictSmoothFormsOfLE (I := SurfaceRealModel) (M := X)
          (A := ℝ)
          (inf_le_left.trans D.puncturedPoleDisk_le_puncturedSurfaceOpen)
          1 omega := by
    have htransport := restrictSmoothFormsOfLE_transportOpenMutualLE
      Qlarge Qsmall Qlarge hQ.le le_rfl hQ.ge hQ.le
        (restrictSmoothFormsOfLE (I := SurfaceRealModel) (M := X)
          (A := ℝ) inf_le_left 1 omega)
    simpa [qDiff, smoothFormsTransportOpenMutualLE,
      restrictSmoothFormsOfLE_id, restrictSmoothFormsOfLE_comp,
      Qlarge, Qsmall] using htransport
  have hetaTransport := integrateSmoothChain_diffeomorph
    SurfaceRealModel SurfaceRealModel qDiff
      (restrictSmoothFormsOfLE (I := SurfaceRealModel) (M := X)
        (A := ℝ) inf_le_left 1 eta.1) c
  have hetaPeriodSmall :
      integrateSmoothChain (I := SurfaceRealModel)
        (deRhamClosedFormsRestrictionOfLE
          (I := SurfaceRealModel) (A := ℝ) inf_le_left 1 eta).1
          cSmall = -1 := by
    rw [hpullback eta.1] at hetaTransport
    exact hetaTransport.trans hetaPeriod
  let tau : DeRhamClosedForms (I := SurfaceRealModel)
      (M := puncturedSurfaceOpen p) (A := ℝ) 1 :=
    properLineTubeClosedOneForm SurfaceRealModel tubeU tubePhi hcore
  have htubeTransport := integrateSmoothChain_diffeomorph
    SurfaceRealModel SurfaceRealModel qDiff
      (restrictSmoothFormsOfLE (I := SurfaceRealModel) (M := X)
        (A := ℝ) inf_le_left 1 tau.1) c
  have htubePeriodSmall :
      integrateSmoothChain (I := SurfaceRealModel)
        (deRhamClosedFormsRestrictionOfLE
          (I := SurfaceRealModel) (A := ℝ) inf_le_left 1 tau).1
          cSmall = 1 ∨
      integrateSmoothChain (I := SurfaceRealModel)
        (deRhamClosedFormsRestrictionOfLE
          (I := SurfaceRealModel) (A := ℝ) inf_le_left 1 tau).1
          cSmall = -1 := by
    rw [hpullback tau.1] at htubeTransport
    rcases htubePeriod with htubePeriod | htubePeriod
    · left
      exact htubeTransport.trans (by simpa [tau] using htubePeriod)
    · right
      exact htubeTransport.trans (by simpa [tau] using htubePeriod)
  have hdata : ∃ cSmall : SingularChain (I := SurfaceRealModel)
      (M := Qsmall) 1 ∞,
      boundary (I := SurfaceRealModel) cSmall = 0 ∧
        integrateSmoothChain (I := SurfaceRealModel)
          (deRhamClosedFormsRestrictionOfLE
            (I := SurfaceRealModel) (A := ℝ) inf_le_left 1 eta).1
            cSmall = -1 ∧
        (integrateSmoothChain (I := SurfaceRealModel)
            (deRhamClosedFormsRestrictionOfLE
              (I := SurfaceRealModel) (A := ℝ) inf_le_left 1
                (properLineTubeClosedOneForm SurfaceRealModel
                  tubeU tubePhi hcore)).1 cSmall = 1 ∨
          integrateSmoothChain (I := SurfaceRealModel)
            (deRhamClosedFormsRestrictionOfLE
              (I := SurfaceRealModel) (A := ℝ) inf_le_left 1
                (properLineTubeClosedOneForm SurfaceRealModel
                  tubeU tubePhi hcore)).1 cSmall = -1) := by
    exact ⟨cSmall, hcycleSmall, hetaPeriodSmall,
      by simpa [tau] using htubePeriodSmall⟩
  rcases hdata with
    ⟨cSmall, hcycleSmall, hetaPeriodSmall, htubePeriodSmall⟩
  apply greenConjugate_planeMap_of_properLineTube_periods
    C P v D₀ hp eta theta hdecomposition tubeU tubePhi hcore
      annulusPhi cSmall hcycleSmall
  · exact Or.inr hetaPeriodSmall
  · exact htubePeriodSmall

/--
%%handwave
name:
  Reduction to one transverse tube crossing and an exterior return
statement:
  With the same data, there is a closed normalized pole chain \(c\) such
  that a Green plane map exists whenever the image of \(c\) in the punctured
  surface decomposes as
  \[
    c=\sigma+\rho,
  \]
  where \(\sigma\) crosses the proper-line tube once from a level
  \(a\le-1\) to a level \(b\ge1\), and \(\rho\) is supported outside the
  closed transition strip.
proof:
  The tube Thom form integrates to \(1\) on the transverse crossing and
  vanishes on the exterior return chain.  Thus its period on \(c\) is \(1\),
  and the normalized-pole-cycle reduction applies.
-/
theorem exists_normalizedPoleCycle_greenConjugate_planeMap_of_crossing_return
    [IsManifold SurfaceRealModel ∞ X] [NoncompactSpace X]
    [Subsingleton
      (DeRhamCohomology (I := SurfaceRealModel) (M := X) (A := ℝ) 1)]
    (E : SmoothRelativelyCompactExhaustion X)
    (D : CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    (C : CompactSuperlevelGreenFunctionPuncturedConjugateDifferentialData X G)
    (v : Circle)
    (tubeU : TopologicalSpace.Opens (puncturedSurfaceOpen p))
    (tubePhi : tubeU ≃ₘ⟮SurfaceRealModel,
      ProperLineTubeModel⟯ ℝ × ℝ)
    (hcore : IsClosed
      (properLineTubeCore SurfaceRealModel tubeU tubePhi)) :
    let Q := D.puncturedPoleDisk ⊓
      ⟨D.closedDisk.toSmoothBoundaryDomain.carrier,
        D.closedDisk.toSmoothBoundaryDomain.isOpen⟩
    let hQU : Q ≤ puncturedSurfaceOpen p :=
      inf_le_left.trans D.puncturedPoleDisk_le_puncturedSurfaceOpen
    ∃ c : SingularChain (I := SurfaceRealModel) (M := Q) 1 ∞,
      boundary (I := SurfaceRealModel) c = 0 ∧
        ((∃ (s a b : ℝ)
            (returning : SingularChain (I := SurfaceRealModel)
              (M := properLineTubeExteriorOpen SurfaceRealModel
                tubeU tubePhi hcore) 1 ∞),
            a ≤ -1 ∧ 1 ≤ b ∧
              SingularChain.nestedOpenInclusion
                  (I := SurfaceRealModel) hQU c =
                Finsupp.single
                    ((properLineTubeTransverseSimplex SurfaceRealModel
                      tubeU tubePhi s a b).openInclusion
                        (I := SurfaceRealModel) tubeU) (1 : ℤ) +
                  SingularChain.openInclusion (I := SurfaceRealModel)
                    (properLineTubeExteriorOpen SurfaceRealModel
                      tubeU tubePhi hcore) returning) →
          Nonempty (CompactSuperlevelGreenFunctionPlaneMap X G)) := by
  dsimp only
  rcases exists_normalizedPoleCycle_greenConjugate_planeMap_of_properLineTube
      E D C v tubeU tubePhi hcore with ⟨c, hcycle, hfinish⟩
  refine ⟨c, hcycle, ?_⟩
  rintro ⟨s, a, b, returning, ha, hb, hdecomposition⟩
  apply hfinish
  left
  let tau : DeRhamClosedForms (I := SurfaceRealModel)
      (M := puncturedSurfaceOpen p) (A := ℝ) 1 :=
    properLineTubeClosedOneForm SurfaceRealModel tubeU tubePhi hcore
  have hglobal :
      integrateSmoothChain (I := SurfaceRealModel) tau.1
          (SingularChain.nestedOpenInclusion (I := SurfaceRealModel)
            (inf_le_left.trans
              D.puncturedPoleDisk_le_puncturedSurfaceOpen) c) = 1 := by
    exact
      integrate_properLineTubeGlobalOneForm_eq_one_of_eq_crossing_add_exterior
        SurfaceRealModel tubeU tubePhi hcore s ha hb returning
          (SingularChain.nestedOpenInclusion (I := SurfaceRealModel)
            (inf_le_left.trans
              D.puncturedPoleDisk_le_puncturedSurfaceOpen) c)
          hdecomposition
  have hnested := integrateSmoothChain_nestedOpenInclusion
    (I := SurfaceRealModel)
    (inf_le_left.trans D.puncturedPoleDisk_le_puncturedSurfaceOpen)
    tau.1 c
  exact hnested.symm.trans (by simpa [tau] using hglobal)

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

/--
%%handwave
name:
  Green plane map from a normalized puncture-cycle generator
statement:
  Fix a base point in \(X\setminus\{p\}\).  There exist a closed one-form
  \(\eta\), a function \(\theta\), and a closed one-chain \(\gamma\) such
  that
  \[
    \omega=\pm2\pi\eta+d\theta,
    \qquad
    \int_\gamma 2\pi\eta=2\pi.
  \]
  If every closed smooth one-chain has the form
  \(c=k\gamma+\partial b\) for some \(k\in\mathbb Z\), then the global Green
  plane map exists.
proof:
  Reverse the normalized pole cycle so its \(2\pi\eta\)-period is \(2\pi\).
  The cycle-generator hypothesis makes every period of \(2\pi\eta\) an
  integral multiple of \(2\pi\), yielding a circle-valued primitive
  normalized at the base point.  Combine it with the exact remainder and
  exponentiate the Green conjugate.
-/
theorem exists_normalizedPunctureCycle_greenConjugate_planeMap_of_cycleGenerator
    [IsManifold SurfaceRealModel ∞ X] [NoncompactSpace X]
    [Subsingleton
      (DeRhamCohomology (I := SurfaceRealModel) (M := X) (A := ℝ) 1)]
    (E : SmoothRelativelyCompactExhaustion X)
    (D : CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    (C : CompactSuperlevelGreenFunctionPuncturedConjugateDifferentialData X G)
    (v : Circle) (x₀ : puncturedSurfaceOpen p) :
    ∃ eta : DeRhamClosedForms (I := SurfaceRealModel)
        (M := puncturedSurfaceOpen p) (A := ℝ) 1,
      ∃ theta : SmoothForms (I := SurfaceRealModel)
          (M := puncturedSurfaceOpen p) ℝ 0,
        ∃ gamma : SingularChain (I := SurfaceRealModel)
            (M := puncturedSurfaceOpen p) 1 ∞,
          C.conjugate.omega =
              annularAngleTransitionCoefficient v • eta.1 +
                deRhamDifferential (I := SurfaceRealModel)
                  (M := puncturedSurfaceOpen p) (A := ℝ) 0 theta ∧
            boundary (I := SurfaceRealModel) gamma = 0 ∧
              integrateSmoothChain (I := SurfaceRealModel)
                  ((2 * Real.pi) • eta.1) gamma = 2 * Real.pi ∧
                ((∀ c : SingularChain (I := SurfaceRealModel)
                      (M := puncturedSurfaceOpen p) 1 ∞,
                    boundary (I := SurfaceRealModel) c = 0 →
                      ∃ (k : ℤ) (b : SingularChain
                          (I := SurfaceRealModel)
                          (M := puncturedSurfaceOpen p) 2 ∞),
                        c = k • gamma + boundary (I := SurfaceRealModel) b) →
                  Nonempty (CompactSuperlevelGreenFunctionPlaneMap X G)) := by
  let Q : TopologicalSpace.Opens X := D.puncturedPoleDisk ⊓
    ⟨D.closedDisk.toSmoothBoundaryDomain.carrier,
      D.closedDisk.toSmoothBoundaryDomain.isOpen⟩
  let U : TopologicalSpace.Opens X := puncturedSurfaceOpen p
  have hQU : Q ≤ U :=
    inf_le_left.trans D.puncturedPoleDisk_le_puncturedSurfaceOpen
  rcases
      D.exists_puncturedAngularForm_greenConjugate_exact_decomposition_normalized
        E C v with
    ⟨eta, theta, c, hdecomposition, hcycle, hperiod⟩
  let cU : SingularChain (I := SurfaceRealModel) (M := U) 1 ∞ :=
    SingularChain.nestedOpenInclusion (I := SurfaceRealModel) hQU c
  let gamma : SingularChain (I := SurfaceRealModel) (M := U) 1 ∞ := -cU
  have hcUcycle : boundary (I := SurfaceRealModel) cU = 0 := by
    rw [← SingularChain.nestedOpenInclusion_boundary, hcycle]
    simp
  have hgammaCycle : boundary (I := SurfaceRealModel) gamma = 0 := by
    change boundary (I := SurfaceRealModel) (-cU) = 0
    rw [map_neg, hcUcycle, neg_zero]
  have hcUperiod :
      integrateSmoothChain (I := SurfaceRealModel) eta.1 cU = -1 := by
    calc
      integrateSmoothChain (I := SurfaceRealModel) eta.1 cU =
          integrateSmoothChain (I := SurfaceRealModel)
            (restrictSmoothFormsOfLE
              (I := SurfaceRealModel) (A := ℝ) hQU 1 eta.1) c :=
        integrateSmoothChain_nestedOpenInclusion
          (I := SurfaceRealModel) hQU eta.1 c
      _ = -1 := by
        simpa [Q, U, hQU] using hperiod
  have hgammaPeriod :
      integrateSmoothChain (I := SurfaceRealModel)
          ((2 * Real.pi) • eta.1) gamma = 2 * Real.pi := by
    change integrateSmoothChain (I := SurfaceRealModel)
        ((2 * Real.pi) • eta.1) (-cU) = 2 * Real.pi
    rw [integrateSmoothChain_neg_one, integrateSmoothChain_smul_form,
      hcUperiod]
    ring
  refine ⟨eta, theta, gamma, hdecomposition, hgammaCycle,
    hgammaPeriod, ?_⟩
  intro hgenerate
  let etaScaled : DeRhamClosedForms (I := SurfaceRealModel)
      (M := U) (A := ℝ) 1 := (2 * Real.pi) • eta
  let PetaScaled : SmoothCirclePrimitive SurfaceRealModel etaScaled.1 :=
    smoothCirclePrimitiveOfNormalizedCycleGenerator
      etaScaled x₀ gamma (by simpa [etaScaled] using hgammaPeriod) hgenerate
  let Peta : SmoothCirclePrimitive SurfaceRealModel
      ((2 * Real.pi) • eta.1) :=
    SmoothCirclePrimitive.congr SurfaceRealModel PetaScaled rfl
  let PC : SmoothCirclePrimitive SurfaceRealModel C.conjugate.omega :=
    greenConjugateCirclePrimitiveOfAngular C v eta theta
      hdecomposition Peta
  exact C.circlePrimitive_has_planeMap P PC

/--
%%handwave
name:
  Plane-map reduction to a puncture-cycle generator
statement:
  Let \(G\) be a compact-superlevel Green function with pole \(p\) on a
  noncompact Riemann surface with
  \(H^1_{\mathrm{dR}}(X;\mathbb R)=0\).  There is a closed smooth one-chain
  \(\gamma\) in \(X\setminus\{p\}\) such that
  \[
    \bigl[\forall c\text{ closed},
      c=k\gamma+\partial b\text{ for some }k\in\mathbb Z,b\bigr]
    \Longrightarrow
    \text{a global Green plane map exists}.
  \]
proof:
  Choose the pole exponential branch, pole-coordinate logarithmic data, and
  conjugate-differential data attached to \(G\).  The normalized
  puncture-cycle reduction then supplies the required \(\gamma\) and the
  stated implication.
-/
theorem compactSuperlevelGreenFunction_planeMap_of_puncturedCycleGenerator
    [IsManifold SurfaceRealModel ∞ X] [NoncompactSpace X]
    [Subsingleton
      (DeRhamCohomology (I := SurfaceRealModel) (M := X) (A := ℝ) 1)]
    (E : SmoothRelativelyCompactExhaustion X)
    (G : CompactSuperlevelGreenFunctionWithPole X p) :
    ∃ gamma : SingularChain (I := SurfaceRealModel)
        (M := puncturedSurfaceOpen p) 1 ∞,
      boundary (I := SurfaceRealModel) gamma = 0 ∧
        ((∀ c : SingularChain (I := SurfaceRealModel)
              (M := puncturedSurfaceOpen p) 1 ∞,
            boundary (I := SurfaceRealModel) c = 0 →
              ∃ (k : ℤ) (b : SingularChain (I := SurfaceRealModel)
                  (M := puncturedSurfaceOpen p) 2 ∞),
                c = k • gamma + boundary (I := SurfaceRealModel) b) →
          Nonempty (CompactSuperlevelGreenFunctionPlaneMap X G)) := by
  rcases compactSuperlevelGreenFunction_poleExponentialBranch X G with ⟨P⟩
  rcases compactSuperlevelGreenFunction_poleCoordinateLogData_nonempty
      X G P with ⟨D⟩
  rcases compactSuperlevelGreenFunction_puncturedConjugateDifferentialData_nonempty
      X G with ⟨C⟩
  have hpuncturedNonempty : (puncturedSurfaceOpen p : Set X).Nonempty := by
    exact Set.nonempty_compl.mpr isCompact_singleton.ne_univ
  let x₀ : puncturedSurfaceOpen p :=
    ⟨Classical.choose hpuncturedNonempty,
      Classical.choose_spec hpuncturedNonempty⟩
  rcases exists_normalizedPunctureCycle_greenConjugate_planeMap_of_cycleGenerator
      E D C (1 : Circle) x₀ with
    ⟨_eta, _theta, gamma, _hdecomposition, hcycle,
      _hperiod, hfinish⟩
  exact ⟨gamma, hcycle, hfinish⟩

/--
%%handwave
name:
  Holomorphic Green exponential from integral angular periods
statement:
  There are a closed angular form \(\eta\) and a smooth function \(\theta\)
  on \(X\setminus\{p\}\) such that
  \[
    \omega=\pm2\pi\eta+d\theta.
  \]
  If every closed smooth one-chain \(c\) satisfies
  \[
    \int_c2\pi\eta=2\pi k
    \quad\text{for some }k\in\mathbb Z,
  \]
  then there is a holomorphic nonvanishing
  \(f:X\setminus\{p\}\to\mathbb C\) with
  \(\log|f|=-G\).
proof:
  The integral-period criterion gives \(2\pi\eta\) a circle-valued
  primitive, normalized at the chosen base point.  Add the exact term
  \(d\theta\), adjust for orientation, and apply the holomorphic
  exponential construction for the Green conjugate.
-/
theorem exists_puncturedAngularForm_greenConjugate_holomorphicExp_of_integralPeriods
    [IsManifold SurfaceRealModel ∞ X] [NoncompactSpace X]
    [Subsingleton
      (DeRhamCohomology (I := SurfaceRealModel) (M := X) (A := ℝ) 1)]
    (E : SmoothRelativelyCompactExhaustion X)
    (D : CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    (C : CompactSuperlevelGreenFunctionPuncturedConjugateDifferentialData X G)
    (v : Circle) (x₀ : puncturedSurfaceOpen p) :
    ∃ eta : DeRhamClosedForms (I := SurfaceRealModel)
        (M := puncturedSurfaceOpen p) (A := ℝ) 1,
      ∃ theta : SmoothForms (I := SurfaceRealModel)
          (M := puncturedSurfaceOpen p) ℝ 0,
        C.conjugate.omega =
            annularAngleTransitionCoefficient v • eta.1 +
              deRhamDifferential (I := SurfaceRealModel)
                (M := puncturedSurfaceOpen p) (A := ℝ) 0 theta ∧
          ((∀ c : SingularChain (I := SurfaceRealModel)
                (M := puncturedSurfaceOpen p) 1 ∞,
              boundary (I := SurfaceRealModel) c = 0 →
                ∃ k : ℤ,
                  integrateSmoothChain (I := SurfaceRealModel)
                    ((2 * Real.pi) • eta.1) c =
                      (2 * Real.pi) * (k : ℝ)) →
            ∃ f : puncturedSurfaceOpen p → ℂ,
              MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f ∧
                (∀ z, f z ≠ 0) ∧
                  ∀ z, Real.log ‖f z‖ = -G.toFun (z : X)) := by
  rcases D.exists_puncturedAngularForm_greenConjugate_exact_decomposition
      E C v with ⟨eta, theta, hdecomposition⟩
  refine ⟨eta, theta, hdecomposition, ?_⟩
  intro hperiod
  let etaScaled : DeRhamClosedForms (I := SurfaceRealModel)
      (M := puncturedSurfaceOpen p) (A := ℝ) 1 :=
    (2 * Real.pi) • eta
  have hscaledForm : etaScaled.1 = (2 * Real.pi) • eta.1 := rfl
  have hperiodScaled : ∀ c : SingularChain (I := SurfaceRealModel)
        (M := puncturedSurfaceOpen p) 1 ∞,
      boundary (I := SurfaceRealModel) c = 0 →
        ∃ k : ℤ, integrateSmoothChain (I := SurfaceRealModel)
            etaScaled.1 c = (2 * Real.pi) * (k : ℝ) := by
    intro c hc
    simpa [hscaledForm] using hperiod c hc
  let Pscaled : SmoothCirclePrimitive SurfaceRealModel etaScaled.1 :=
    smoothCirclePrimitiveOfIntegralSmoothPeriods etaScaled x₀ hperiodScaled
  let Peta : SmoothCirclePrimitive SurfaceRealModel
      ((2 * Real.pi) • eta.1) :=
    SmoothCirclePrimitive.congr SurfaceRealModel Pscaled hscaledForm
  let PC : SmoothCirclePrimitive SurfaceRealModel C.conjugate.omega :=
    greenConjugateCirclePrimitiveOfAngular C v eta theta
      hdecomposition Peta
  exact C.circlePrimitive_has_holomorphic_exp PC

/--
%%handwave
name:
  Punctured Green plane map from integral angular periods
statement:
  Under the same Green and cohomological hypotheses, there are
  \(\eta\) and \(\theta\) with
  \(\omega=\pm2\pi\eta+d\theta\) such that integral \(2\pi\)-periods of
  \(2\pi\eta\) imply the existence of a punctured Green plane map with the
  prescribed first-order pole factorization.
proof:
  Integral periods produce a nonvanishing holomorphic exponential
  \(f\) with \(\log|f|=-G\).  Combining \(f\) with the fixed local pole
  branch is exactly the punctured Green plane-map construction.
-/
theorem exists_puncturedAngularForm_greenConjugate_planeMap_of_integralPeriods
    [IsManifold SurfaceRealModel ∞ X] [NoncompactSpace X]
    [Subsingleton
      (DeRhamCohomology (I := SurfaceRealModel) (M := X) (A := ℝ) 1)]
    (E : SmoothRelativelyCompactExhaustion X)
    (D : CompactSuperlevelGreenFunctionPoleCoordinateLogData X G P)
    (C : CompactSuperlevelGreenFunctionPuncturedConjugateDifferentialData X G)
    (v : Circle) (x₀ : puncturedSurfaceOpen p) :
    ∃ eta : DeRhamClosedForms (I := SurfaceRealModel)
        (M := puncturedSurfaceOpen p) (A := ℝ) 1,
      ∃ theta : SmoothForms (I := SurfaceRealModel)
          (M := puncturedSurfaceOpen p) ℝ 0,
        C.conjugate.omega =
            annularAngleTransitionCoefficient v • eta.1 +
              deRhamDifferential (I := SurfaceRealModel)
                (M := puncturedSurfaceOpen p) (A := ℝ) 0 theta ∧
          ((∀ c : SingularChain (I := SurfaceRealModel)
                (M := puncturedSurfaceOpen p) 1 ∞,
              boundary (I := SurfaceRealModel) c = 0 →
                ∃ k : ℤ,
                  integrateSmoothChain (I := SurfaceRealModel)
                    ((2 * Real.pi) • eta.1) c =
                      (2 * Real.pi) * (k : ℝ)) →
            Nonempty (CompactSuperlevelGreenFunctionPuncturedPlaneMap X G)) := by
  rcases exists_puncturedAngularForm_greenConjugate_holomorphicExp_of_integralPeriods
      E D C v x₀ with ⟨eta, theta, hdecomposition, hExp⟩
  refine ⟨eta, theta, hdecomposition, ?_⟩
  intro hperiod
  rcases hExp hperiod with ⟨f, hf, hf_nonzero, hf_log⟩
  exact ⟨compactSuperlevelGreenFunction_puncturedPlaneMap_of_holomorphicExp
    P f hf hf_nonzero hf_log⟩

end
end Uniformization
end JJMath
