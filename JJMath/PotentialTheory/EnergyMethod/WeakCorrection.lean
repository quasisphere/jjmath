import JJMath.PotentialTheory.EnergyMethod.DirectMethod
import JJMath.Analysis.Sobolev.Basic
import JJMath.Analysis.Weyl

/-!
# Energy method: WeakCorrection

Riesz representatives, scalar local corrections, and weak correction data.
-/

namespace JJMath

open MeasureTheory
open scoped Manifold Topology ENNReal ContDiff

namespace Uniformization

/--
%%handwave
name:
  Euler equation for the concrete pure \(H^1_0\) Riesz minimizer
statement:
  The concrete Riesz minimizer represents the extended smooth-core source
  functional by the pure Dirichlet inner product.
proof:
  [The Riesz representative in a completed pure Dirichlet space satisfies the Euler--Lagrange identity against every vector](lean:JJMath.Uniformization.greenSobolevH10CompletionEnergy_rieszRepresentative_eulerLagrange). Apply it to the compactly supported smooth Dirichlet core and its extended source functional.
-/
theorem greenSobolevH10SmoothCompactSupportEnergy_rieszRepresentative_eulerLagrange
    {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (source : (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ)
    (η : GreenSobolevH10SmoothCompactSupport g) :
    inner ℝ
        (greenSobolevH10RieszRepresentative
          ((greenSobolevH10SmoothCompactSupportCore g).extendSource source)) η =
      greenSobolevH10SmoothCompactSupportSource source η :=
  greenSobolevH10CompletionEnergy_rieszRepresentative_eulerLagrange
    (greenSobolevH10SmoothCompactSupportCore g) source η

section PureDirichletH10WeakCorrectionDecode

/--
%%handwave
name:
  Local finite-Dirichlet correction
statement:
  A homogeneous finite-energy correction carries a scalar representative
  together with a globally square-integrable Dirichlet differential.  The
  later regularity step replaces the raw scalar representative by the
  harmonic representative supplied by Weyl's lemma.
-/
structure GreenSobolevH10LocalCorrection {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (g : BackgroundSurfaceMetricOnSurface X) where
  toFun : X → ℝ
  weakGradient : X → ℂ →L[ℝ] ℝ
  dirichlet_integrable :
    Integrable
      (fun x ↦ g.gradientInner x (weakGradient x) (weakGradient x))
      g.volume

namespace GreenSobolevH10LocalCorrection

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] {g : BackgroundSurfaceMetricOnSurface X}

instance : CoeFun (GreenSobolevH10LocalCorrection g) (fun _ ↦ X → ℝ) where
  coe u := u.toFun

end GreenSobolevH10LocalCorrection

/--
%%handwave
name:
  Dirichlet pairing with a local correction
statement:
  The Dirichlet pairing of a homogeneous local correction against a
  representative zero-trace test function is the integral of the background
  cotangent pairing of their weak gradients.
-/
noncomputable def greenLocalCorrectionDirichletPairing {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    (g : BackgroundSurfaceMetricOnSurface X)
    (h : GreenSobolevH10LocalCorrection g)
    (η : SobolevH1ZeroOnSurface g.volume) : ℝ :=
  ∫ x, g.gradientInner x (h.weakGradient x) (η.weakGradient x) ∂g.volume

/--
%%handwave
name:
  Smooth compactly supported pure \(H^1_0\) test
statement:
  A smooth compactly supported test for the homogeneous Dirichlet completion
  is a compactly supported smooth scalar function whose differential is
  square-integrable for the chosen conformal background metric.
-/
structure GreenSobolevH10SmoothTest {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    (g : BackgroundSurfaceMetricOnSurface X) where
  F : SmoothCompactlySupportedGlobalSurfaceFunction X
  differential_memL2 :
    SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
      (SurfaceDifferentialField.ofCoordinateField F.gradient)

namespace GreenSobolevH10SmoothTest

variable {X : Type}
variable [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
variable [BorelSpace X] [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
variable [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
variable [TopologicalSpace.PseudoMetrizableSpace
  (SurfaceDifferentialTotalSpace X ℝ)]
variable {g : BackgroundSurfaceMetricOnSurface X}

instance : CoeFun (GreenSobolevH10SmoothTest g) (fun _ ↦ X → ℝ) where
  coe η := η.F.toFun

/--
%%handwave
name:
  Differential class of a smooth pure test
statement:
  A smooth compactly supported pure test determines an \(L^2\) cotangent
  class by taking its classical differential.
-/
noncomputable def differentialClass
    (η : GreenSobolevH10SmoothTest g) : GreenDifferentialL2Intrinsic g :=
  (Quotient.mk
    (SquareIntegrableSurfaceDifferentialField.aeSetoid
      (X := X) (E := ℝ) (g := g.metric) (μ := g.volume))
    ({ toSection := SurfaceDifferentialField.ofCoordinateField η.F.gradient
       memL2 := η.differential_memL2 } :
      SquareIntegrableSurfaceDifferentialField
        (X := X) (E := ℝ) g.metric g.volume) :
    GreenDifferentialL2Intrinsic g)

/--
%%handwave
name:
  Differential class of a smooth pure test is in the smooth core
statement:
  The differential class associated to a smooth compactly supported pure test
  belongs to the smooth Dirichlet core.
proof:
  The differential class is generated by the chosen smooth compactly supported test itself, so it belongs to the defining smooth core.
-/
theorem differentialClass_isSmoothCompactlySupported
    (η : GreenSobolevH10SmoothTest g) :
    IsSmoothCompactlySupportedGreenDifferentialClass g
      (η.differentialClass) := by
  exact ⟨η.F, η.differential_memL2, rfl⟩

/--
%%handwave
name:
  Smooth pure test as a completed \(H^1_0\) direction
statement:
  A smooth compactly supported pure test has a canonical image in the
  completed homogeneous \(H^1_0\) space.
-/
noncomputable def toH10
    (η : GreenSobolevH10SmoothTest g) :
    GreenSobolevH10SmoothCompactSupport g :=
  smoothCompactlySupportedGreenDifferentialClassToH10
    (η.differentialClass_isSmoothCompactlySupported)

noncomputable def ofChartTest
    [T2Space X]
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    {Ω : Set ℂ}
    (η : SmoothCompactlySupportedManifoldCoordinateFunction Ω)
    (hΩ_target : Ω ⊆ e.target)
    (hdiff :
      SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
        (SurfaceDifferentialField.ofCoordinateField
          (SmoothCompactlySupportedGlobalSurfaceFunction.ofChartTest
            e he η hΩ_target).gradient)) :
    GreenSobolevH10SmoothTest g where
  F := SmoothCompactlySupportedGlobalSurfaceFunction.ofChartTest
    e he η hΩ_target
  differential_memL2 := hdiff

/--
%%handwave
name:
  A globalized chart test recovers the coordinate test
statement:
  Let \(e\) be a surface chart and let \(\eta\) be a smooth compactly supported
  coordinate test whose domain lies in \(e.target\).  For every \(z\in e.target\),
  the associated global test satisfies \(F(e^{-1}z)=\eta(z)\).
proof:
  This is the corresponding evaluation formula for the zero-extended global
  chart test used to construct \(F\).
-/
theorem ofChartTest_apply_symm_of_mem_target
    [T2Space X]
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    {Ω : Set ℂ}
    (η : SmoothCompactlySupportedManifoldCoordinateFunction Ω)
    (hΩ_target : Ω ⊆ e.target)
    (hdiff :
      SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
        (SurfaceDifferentialField.ofCoordinateField
          (SmoothCompactlySupportedGlobalSurfaceFunction.ofChartTest
            e he η hΩ_target).gradient))
    {z : ℂ} (hz : z ∈ e.target) :
    (ofChartTest (g := g) e he η hΩ_target hdiff).F.toFun (e.symm z) =
      η z := by
  exact
    SmoothCompactlySupportedGlobalSurfaceFunction.ofChartTest_apply_symm_of_mem_target
      e he η hΩ_target hz

end GreenSobolevH10SmoothTest

/--
%%handwave
name:
  Chart-extended tests have the expected metric pairing in coordinates
statement:
  The surface metric pairing of a cotangent field with the gradient of a
  zero-extended coordinate test is, in the original chart, the coordinate
  weak-gradient/test pairing.
proof:
  The global cotangent pairing is the inverse-metric coordinate contraction.
  The gradient of the zero extension agrees on the chart with the Euclidean
  differential of the coordinate test.
-/
theorem smoothChartTestExtension_gradientInner_eq_weakGradientCoordinatePairing
    {X : Type}
    [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [IsManifold SurfaceRealModel ∞ X]
    (g : BackgroundSurfaceMetricOnSurface X)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    {Ω : Set ℂ}
    (η : SmoothCompactlySupportedManifoldCoordinateFunction Ω)
    (hΩ_target : Ω ⊆ e.target)
    (ξ : ℂ →L[ℝ] ℝ) {z : ℂ} (hz : z ∈ e.target) :
    g.gradientInner (e.symm z) ξ
        ((SmoothCompactlySupportedGlobalSurfaceFunction.ofChartTest
          e he η hΩ_target).gradient (e.symm z)) =
      surfaceMetricWeakGradientCoordinatePairingInChart g e z ξ
        (fderiv ℝ (η : ℂ → ℝ) z) := by
  calc
    g.gradientInner (e.symm z) ξ
        ((SmoothCompactlySupportedGlobalSurfaceFunction.ofChartTest
          e he η hΩ_target).gradient (e.symm z))
        =
      surfaceMetricCoordinateCotangentPairingInChart g.metric e z ξ
        ((SmoothCompactlySupportedGlobalSurfaceFunction.ofChartTest
          e he η hΩ_target).gradient (e.symm z)) := by
        exact
          surfaceMetricCotangentPairingInChart_eq
            g.metric g.gradientInner
            (BackgroundSurfaceMetricOnSurface.gradientInner_isMetricDual g)
            e he ξ
            ((SmoothCompactlySupportedGlobalSurfaceFunction.ofChartTest
              e he η hΩ_target).gradient (e.symm z)) z hz
    _ =
      surfaceMetricWeakGradientCoordinatePairingInChart g e z ξ
        (fderiv ℝ (η : ℂ → ℝ) z) := by
        simp only [surfaceMetricCoordinateCotangentPairingInChart,
          surfaceMetricWeakGradientCoordinatePairingInChart]
        apply Finset.sum_congr rfl
        intro i _hi
        apply Finset.sum_congr rfl
        intro j _hj
        have hgrad :
            (SmoothCompactlySupportedGlobalSurfaceFunction.ofChartTest
              e he η hΩ_target).gradient (e.symm z)
                (surfaceChartTangentMap e z (complexCoordinateVector j)) =
              fderiv ℝ (η : ℂ → ℝ) z (complexCoordinateVector j) :=
          SmoothCompactlySupportedGlobalSurfaceFunction.ofChartTest_gradient_apply_symm_of_mem_target
            e he η hΩ_target (z := z) (v := complexCoordinateVector j) hz
        rw [hgrad]

/--
%%handwave
name:
  Chart-extended tests have the expected source value in coordinates
statement:
  Pulling a zero-extended coordinate test back along its defining chart gives
  the original coordinate test, and hence gives the expected source-product
  identity.
proof:
  This is the defining pointwise formula for the chart zero extension.
-/
theorem smoothChartTestExtension_sourcePairing_eq_chartSourcePairing
    {X : Type}
    [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X]
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    {Ω : Set ℂ}
    (η : SmoothCompactlySupportedManifoldCoordinateFunction Ω)
    (hΩ_target : Ω ⊆ e.target)
    (F : X → ℝ) {z : ℂ} (hz : z ∈ e.target) :
    F (e.symm z) *
        (SmoothCompactlySupportedGlobalSurfaceFunction.ofChartTest
          e he η hΩ_target).toFun (e.symm z) =
      F (e.symm z) * η z := by
  have hvalue :
      (SmoothCompactlySupportedGlobalSurfaceFunction.ofChartTest
        e he η hΩ_target).toFun (e.symm z) = η z :=
    SmoothCompactlySupportedGlobalSurfaceFunction.ofChartTest_apply_symm_of_mem_target
      e he η hΩ_target hz
  rw [hvalue]

/--
%%handwave
name:
  Differential extension agrees on smooth tests
statement:
  The canonical ambient \(L^2\)-cotangent class of a smooth compactly
  supported pure \(H^1_0\) test is its classical differential class.
proof:
  The continuous extension from the dense smooth core agrees with the original differential functional on every core generator.
-/
theorem greenSobolevH10SmoothCompactSupportDifferentialClass_smoothTest
    {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (η : GreenSobolevH10SmoothTest g) :
    greenSobolevH10SmoothCompactSupportDifferentialClass η.toH10 =
      η.differentialClass := by
  let C := greenSobolevH10SmoothCompactSupportCore g
  let ucore : C.Core :=
    ⟨η.differentialClass,
      smoothCompactlySupportedGreenDifferentialClass_mem_core
        η.differentialClass_isSmoothCompactlySupported⟩
  have htoH10 : η.toH10 = C.toCompletion ucore := by
    rfl
  rw [htoH10]
  exact greenSobolevH10SmoothCompactSupportDifferentialClass_toCompletion ucore

/--
%%handwave
name:
  Completed inner products are ambient differential pairings on smooth tests
statement:
  Pairing a completed pure \(H^1_0\) class with a smooth compactly supported
  test in the completed Dirichlet inner product is the same as pairing their
  ambient \(L^2\)-cotangent classes.
proof:
  Both sides are continuous linear functionals of the completed class.  They
  agree on the dense smooth differential core, where the completion inner
  product is the original core inner product and the extended differential
  class is the original cotangent class.
-/
theorem greenSobolevH10SmoothCompactSupport_inner_smoothTest_eq_differential_inner
    {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (u : GreenSobolevH10SmoothCompactSupport g)
    (η : GreenSobolevH10SmoothTest g) :
    inner ℝ u η.toH10 =
      inner ℝ
        (greenSobolevH10SmoothCompactSupportDifferentialClass u)
        η.differentialClass := by
  let C := greenSobolevH10SmoothCompactSupportCore g
  let e : C.Core →L[ℝ] UniformSpace.Completion C.Core :=
    UniformSpace.Completion.toComplL
  let D :
      GreenSobolevH10SmoothCompactSupport g →L[ℝ]
        GreenDifferentialL2Intrinsic g :=
    greenSobolevH10SmoothCompactSupportDifferentialClass
  let Lcomp : GreenSobolevH10SmoothCompactSupport g →L[ℝ] ℝ :=
    innerSL ℝ η.toH10
  let Lamb : GreenSobolevH10SmoothCompactSupport g →L[ℝ] ℝ :=
    (innerSL ℝ η.differentialClass).comp D
  let ucore : C.Core :=
    ⟨η.differentialClass,
      smoothCompactlySupportedGreenDifferentialClass_mem_core
        η.differentialClass_isSmoothCompactlySupported⟩
  have htoH10 : η.toH10 = C.toCompletion ucore := by
    rfl
  have hcore : Lcomp.comp e = Lamb.comp e := by
    ext v
    have hvD :
        D (C.toCompletion v) = v.1 :=
      greenSobolevH10SmoothCompactSupportDifferentialClass_toCompletion v
    have heq : e v = C.toCompletion v := by
      rfl
    calc
      (Lcomp.comp e) v = inner ℝ η.toH10 (e v) := by
        rfl
      _ = inner ℝ (C.toCompletion ucore) (C.toCompletion v) := by
        rw [htoH10, heq]
      _ = inner ℝ ucore v := by
        rw [GreenSobolevH10DirichletCore.toCompletion,
          GreenSobolevH10DirichletCore.toCompletion]
        exact UniformSpace.Completion.inner_coe ucore v
      _ = inner ℝ η.differentialClass v.1 := by
        rfl
      _ = inner ℝ η.differentialClass (D (C.toCompletion v)) := by
        rw [hvD]
      _ = (Lamb.comp e) v := by
        change inner ℝ η.differentialClass (D (C.toCompletion v)) =
          inner ℝ η.differentialClass (D (e v))
        rw [heq]
  have hdense : DenseRange e := by
    simpa [e, UniformSpace.Completion.coe_toComplL] using
      (UniformSpace.Completion.denseRange_coe : DenseRange
        ((↑) : C.Core → UniformSpace.Completion C.Core))
  have hind : IsUniformInducing e := by
    simpa [e, UniformSpace.Completion.coe_toComplL] using
      (UniformSpace.Completion.isUniformInducing_coe C.Core)
  have hLcomp_ext :
      (Lcomp.comp e).extend e = Lcomp :=
    ContinuousLinearMap.extend_unique (f := Lcomp.comp e) (e := e)
      hdense hind Lcomp rfl
  have hLamb_ext :
      (Lcomp.comp e).extend e = Lamb :=
    ContinuousLinearMap.extend_unique (f := Lcomp.comp e) (e := e)
      hdense hind Lamb hcore.symm
  have hmaps : Lcomp = Lamb := by
    rw [← hLcomp_ext, hLamb_ext]
  have hcomp_eval : Lcomp u = inner ℝ u η.toH10 := by
    dsimp [Lcomp]
    exact (real_inner_comm η.toH10 u).symm
  have hamb_eval :
      Lamb u =
        inner ℝ
          (greenSobolevH10SmoothCompactSupportDifferentialClass u)
          η.differentialClass := by
    dsimp [Lamb, D]
    exact (real_inner_comm η.differentialClass
      (greenSobolevH10SmoothCompactSupportDifferentialClass u)).symm
  rw [← hcomp_eval, hmaps, hamb_eval]

/--
%%handwave
name:
  Chosen differential representative pairs with smooth tests by integration
statement:
  The ambient \(L^2\) cotangent pairing between a completed pure \(H^1_0\)
  class and a smooth compactly supported test is represented by integrating
  the background cotangent pairing of the chosen differential representative
  with the test differential.
proof:
  Replace the completed differential class by its chosen square-integrable
  representative and the smooth test by its smooth differential
  representative.  The \(L^2\)-section inner product is the integral of the
  fiberwise Hilbert--Schmidt inner product, and the scalar surface
  Hilbert--Schmidt pairing is the cotangent metric pairing.
-/
theorem greenSobolevH10SmoothCompactSupportDifferentialRep_inner_smoothTest_eq_integral
    {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (u : GreenSobolevH10SmoothCompactSupport g)
    (η : GreenSobolevH10SmoothTest g) :
    inner ℝ
        (greenSobolevH10SmoothCompactSupportDifferentialClass u)
        η.differentialClass =
      ∫ x,
        g.gradientInner x
          (SurfaceDifferentialField.toCoordinateField
            (greenSobolevH10SmoothCompactSupportDifferentialRep u).toField x)
          (η.F.gradient x) ∂g.volume := by
  let metric :=
    manifoldDifferentialHilbertSchmidtContinuousRiemannianMetric
      (I := SurfaceRealModel) (X := X) (E := ℝ) g.metric.toManifoldMetric
  letI : Bundle.RiemannianBundle
      (ManifoldDifferentialBundleFiber
        (I := SurfaceRealModel) (X := X) (E := ℝ)) :=
    ⟨metric.toRiemannianMetric⟩
  letI (x : X) :
      NormedAddCommGroup
        (ManifoldDifferentialBundleFiber
          (I := SurfaceRealModel) (X := X) (E := ℝ) x) :=
    manifoldDifferentialHilbertSchmidtNormedAddCommGroup
      (I := SurfaceRealModel) (X := X) (E := ℝ) metric x
  letI (x : X) :
      InnerProductSpace ℝ
        (ManifoldDifferentialBundleFiber
          (I := SurfaceRealModel) (X := X) (E := ℝ) x) :=
    manifoldDifferentialHilbertSchmidtInnerProductSpace
      (I := SurfaceRealModel) (X := X) (E := ℝ) metric x
  let dU : SquareIntegrableSurfaceDifferentialField
      (X := X) (E := ℝ) g.metric g.volume :=
    greenSobolevH10SmoothCompactSupportDifferentialRep u
  let dη : SquareIntegrableSurfaceDifferentialField
      (X := X) (E := ℝ) g.metric g.volume :=
    { toSection := SurfaceDifferentialField.ofCoordinateField η.F.gradient
      memL2 := η.differential_memL2 }
  let DU : GreenDifferentialL2Intrinsic g :=
    (Quotient.mk
      (SquareIntegrableSurfaceDifferentialField.aeSetoid
        (X := X) (E := ℝ) (g := g.metric) (μ := g.volume)) dU :
      GreenDifferentialL2Intrinsic g)
  let Dη : GreenDifferentialL2Intrinsic g :=
    (Quotient.mk
      (SquareIntegrableSurfaceDifferentialField.aeSetoid
        (X := X) (E := ℝ) (g := g.metric) (μ := g.volume)) dη :
      GreenDifferentialL2Intrinsic g)
  have hDU :
      greenSobolevH10SmoothCompactSupportDifferentialClass u = DU := by
    simpa [DU, dU] using
      (greenSobolevH10SmoothCompactSupportDifferentialRep_class_eq u).symm
  have hDη : η.differentialClass = Dη := by
    rfl
  rw [hDU, hDη]
  change
    ∫ x, inner ℝ (dU.toSection x) (dη.toSection x) ∂g.volume =
      ∫ x,
        g.gradientInner x
          (SurfaceDifferentialField.toCoordinateField dU.toField x)
          (η.F.gradient x) ∂g.volume
  apply integral_congr_ae
  filter_upwards [] with x
  have hfiber :
      manifoldDifferentialHilbertSchmidtInnerCLMAt
        (I := SurfaceRealModel) (X := X) (E := ℝ)
        g.metric.toManifoldMetric x
        (SurfaceDifferentialField.toCoordinateField dU.toField x)
        (η.F.gradient x) =
      g.gradientInner x
        (SurfaceDifferentialField.toCoordinateField dU.toField x)
        (η.F.gradient x) :=
    surface_coordinate_cotangent_fiberInner_eq_gradientInner g x
      (SurfaceDifferentialField.toCoordinateField dU.toField x)
      (η.F.gradient x)
  simpa [dU, dη, DU, Dη, SurfaceDifferentialField.toCoordinateField,
    SurfaceDifferentialField.ofCoordinateField] using hfiber

/--
%%handwave
name:
  Dirichlet pairing with a smooth pure test
statement:
  The local correction Dirichlet pairing against a smooth compactly supported
  pure test is the integral of the background cotangent pairing of the local
  weak gradient and the test differential.
-/
noncomputable def greenLocalCorrectionSmoothTestDirichletPairing {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    (g : BackgroundSurfaceMetricOnSurface X)
    (h : GreenSobolevH10LocalCorrection g)
    (η : GreenSobolevH10SmoothTest g) : ℝ :=
  ∫ x, g.gradientInner x (h.weakGradient x) (η.F.gradient x) ∂g.volume

/--
%%handwave
name:
  Representative weak gradient gives the completed smooth-test pairing
statement:
  If a local correction uses the chosen differential representative of a
  completed pure \(H^1_0\) class as its weak gradient, then its Dirichlet
  pairing against every smooth compactly supported test is the completed
  pure \(H^1_0\) inner product with that test.
proof:
  Rewrite the local Dirichlet pairing as the integral pairing of the chosen
  differential representative, identify that integral with the ambient
  \(L^2\)-cotangent pairing, and use the completed smooth-test inner-product
  comparison.
-/
theorem greenLocalCorrectionSmoothTestDirichletPairing_eq_inner_of_weakGradient_eq
    {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (u : GreenSobolevH10SmoothCompactSupport g)
    (h : GreenSobolevH10LocalCorrection g)
    (hgrad :
      h.weakGradient =
        fun x ↦
          SurfaceDifferentialField.toCoordinateField
            (greenSobolevH10SmoothCompactSupportDifferentialRep u).toField x)
    (η : GreenSobolevH10SmoothTest g) :
    greenLocalCorrectionSmoothTestDirichletPairing g h η =
      inner ℝ u η.toH10 := by
  calc
    greenLocalCorrectionSmoothTestDirichletPairing g h η =
        ∫ x,
          g.gradientInner x
            (SurfaceDifferentialField.toCoordinateField
              (greenSobolevH10SmoothCompactSupportDifferentialRep u).toField x)
            (η.F.gradient x) ∂g.volume := by
      simp [greenLocalCorrectionSmoothTestDirichletPairing, hgrad]
    _ =
        inner ℝ
          (greenSobolevH10SmoothCompactSupportDifferentialClass u)
          η.differentialClass :=
      (greenSobolevH10SmoothCompactSupportDifferentialRep_inner_smoothTest_eq_integral
        u η).symm
    _ = inner ℝ u η.toH10 :=
      (greenSobolevH10SmoothCompactSupport_inner_smoothTest_eq_differential_inner
        u η).symm

/--
%%handwave
name:
  A local Sobolev representative gives the local correction
statement:
  Suppose a completed pure \(H^1_0\) class has a scalar local Sobolev
  representative whose weak gradient is the chosen differential
  representative of the class.  Then it defines a local finite-Dirichlet
  correction whose smooth-test Dirichlet pairings are the completed
  \(H^1_0\) inner products.
proof:
  Package the scalar representative and the chosen weak gradient into the
  local correction structure.  Finite Dirichlet energy follows from
  square-integrability of the chosen differential representative, and the
  pairing identity is the representative pairing lemma.
-/
theorem greenSobolevH10SmoothCompactSupport_has_local_correction_of_local_sobolev_rep
    {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (u : GreenSobolevH10SmoothCompactSupport g)
    {toFun : X → ℝ}
    (_hlocal :
      IsIntrinsicLocalSobolevH1OnSurface g Set.univ toFun
        (fun x ↦
          SurfaceDifferentialField.toCoordinateField
            (greenSobolevH10SmoothCompactSupportDifferentialRep u).toField x)) :
    ∃ h : GreenSobolevH10LocalCorrection g,
      h.toFun = toFun ∧
        h.weakGradient =
          (fun x ↦
            SurfaceDifferentialField.toCoordinateField
              (greenSobolevH10SmoothCompactSupportDifferentialRep u).toField x) ∧
        ∀ η : GreenSobolevH10SmoothTest g,
          greenLocalCorrectionSmoothTestDirichletPairing g h η =
            inner ℝ u η.toH10 := by
  let grad : X → ℂ →L[ℝ] ℝ :=
    fun x ↦
      SurfaceDifferentialField.toCoordinateField
        (greenSobolevH10SmoothCompactSupportDifferentialRep u).toField x
  let h : GreenSobolevH10LocalCorrection g :=
    { toFun := toFun
      weakGradient := grad
      dirichlet_integrable := by
        simpa [grad] using
          greenSobolevH10SmoothCompactSupportDifferentialRep_dirichlet_integrable
            u }
  refine ⟨h, rfl, rfl, ?_⟩
  intro η
  exact
    greenLocalCorrectionSmoothTestDirichletPairing_eq_inner_of_weakGradient_eq
      u h rfl η

/--
%%handwave
name:
  Riesz vector in the pure Dirichlet completion
statement:
  A continuous source on the smooth Dirichlet core has a Riesz vector in the
  completed pure \(H^1_0\) space.
-/
noncomputable def greenSobolevH10SmoothCompactSupportRieszVector
    {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (source : (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ) :
    GreenSobolevH10SmoothCompactSupport g :=
  greenSobolevH10RieszRepresentative
    ((greenSobolevH10SmoothCompactSupportCore g).extendSource source)

/--
%%handwave
name:
  Chosen gradient of the pure Riesz vector
statement:
  The chosen finite-energy differential representative of the Riesz vector is
  viewed as a coordinate cotangent field on the surface.
-/
noncomputable def greenSobolevH10SmoothCompactSupportRieszGradient
    {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (source : (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ) :
    X → ℂ →L[ℝ] ℝ :=
  fun x ↦
    SurfaceDifferentialField.toCoordinateField
      (greenSobolevH10SmoothCompactSupportDifferentialRep
        (greenSobolevH10SmoothCompactSupportRieszVector source)).toField x

/--
%%handwave
name:
  Scalar representative data for a pure Riesz vector
statement:
  Scalar representative data for a pure Dirichlet Riesz vector consists of a
  function on the surface and smooth compactly supported approximants whose
  primitives converge to it in \(L^2\) on every compact set.  The same
  approximants converge to the Riesz vector in the pure completion and their
  differential classes converge to the chosen finite-energy differential.
proof:
  This is a bookkeeping object for the compact-local reconstruction step.
-/
structure GreenSobolevH10SmoothCompactSupportRieszScalarRepresentativeData
    {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (source : (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ)
    where
  toFun : X → ℝ
  approximants : ℕ → (greenSobolevH10SmoothCompactSupportCore g).Core
  approximants_tendsto :
    Filter.Tendsto
      (fun n : ℕ ↦
        (greenSobolevH10SmoothCompactSupportCore g).toCompletion
          (approximants n))
      Filter.atTop
      (𝓝 (greenSobolevH10SmoothCompactSupportRieszVector source))
  primitive_tendsto_localL2 :
    ∀ K : Set X, IsCompact K →
      TendstoInLocalL2OnSurface g.volume K
        (fun n : ℕ ↦
          (greenSobolevH10SmoothCompactSupportCorePrimitive
            (approximants n)).toFun)
        toFun
  primitive_memLp_local :
    ∀ K : Set X, IsCompact K → MemLp toFun 2 (g.volume.restrict K)
  differentialClass_tendsto :
    Filter.Tendsto (fun n : ℕ ↦ (approximants n).1) Filter.atTop
      (𝓝
        (greenSobolevH10SmoothCompactSupportDifferentialClass
          (greenSobolevH10SmoothCompactSupportRieszVector source)))

/--
%%handwave
name:
  Honest local representative data for the pure Riesz vector
statement:
  Honest local representative data for the pure Riesz vector consists of a
  scalar local \(W^{1,2}\) representative whose weak gradient is the chosen
  Riesz differential.
-/
structure GreenSobolevH10SmoothCompactSupportRieszRepresentativeSobolevData
    {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    (φ : LogarithmicCutoffPoleModel g p)
    (source : (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ)
    where
  scalar :
    GreenSobolevH10SmoothCompactSupportRieszScalarRepresentativeData source
  toFun : X → ℝ
  toFun_eq_scalar : toFun = scalar.toFun
  localSobolev :
    IsIntrinsicLocalSobolevH1OnSurface g Set.univ toFun
      (greenSobolevH10SmoothCompactSupportRieszGradient source)

/--
%%handwave
name:
  Source pairing with a smooth pure test
statement:
  The cutoff source pairing against a smooth compactly supported pure test is
  integration of the stored smooth source against the test function.
-/
noncomputable def greenSmoothTestSourcePairing {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    (φ : LogarithmicCutoffPoleModel g p)
    (η : GreenSobolevH10SmoothTest g) : ℝ :=
  ∫ x, φ.source x * η.F.toFun x ∂g.volume

/--
%%handwave
name:
  Smooth pure-test source pairing is bounded by pure energy
statement:
  Under pure Dirichlet capacity at infinity, the cutoff source pairing
  against smooth compactly supported pure tests is bounded by a constant
  times the square root of the test's pure Dirichlet energy.
proof:
  Apply the smooth compact-source estimate to the stored cutoff source.
-/
theorem greenSmoothTestSourcePairing_abs_le_const_mul_sqrt_dirichlet_of_pure_capacity
    {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    (φ : LogarithmicCutoffPoleModel g p)
    (hcap : HasPureDirichletCapacityAtInfinity g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η : GreenSobolevH10SmoothTest g,
      |greenSmoothTestSourcePairing φ η| ≤
        C * Real.sqrt
          (∫ x, g.gradientInner x (η.F.gradient x) (η.F.gradient x)
            ∂g.volume) := by
  rcases
    compactly_supported_smooth_source_abs_pairing_smooth_le_const_mul_sqrt_dirichlet_of_pure_capacity
      (g := g) φ.source_compact_support φ.source_smooth hcap with
    ⟨C, hC_nonneg, hC⟩
  exact ⟨C, hC_nonneg, fun η ↦ by
    simpa [greenSmoothTestSourcePairing] using hC η.F⟩

/--
%%handwave
name:
  The compact source pairing is bounded by the differential-class norm
statement:
  Under pure Dirichlet capacity at infinity, for a logarithmic cutoff source
  \(s\) there is \(C\ge0\) such that every smooth compactly supported \(F\) with
  \(L^2\) differential satisfies
  \[
    \left|\int_X sF\,d\mu_g\right|\le C\lVert[dF]\rVert.
  \]
proof:
  Apply the source estimate for smooth pure tests, then replace the square root
  of the Dirichlet integral by the norm of \([dF]\).
-/
theorem greenSmoothDifferentialClass_source_abs_le_const_mul_norm_of_pure_capacity
    {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    (φ : LogarithmicCutoffPoleModel g p)
    (hcap : HasPureDirichletCapacityAtInfinity g) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (F : SmoothCompactlySupportedGlobalSurfaceFunction X)
        (hF : SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
          (SurfaceDifferentialField.ofCoordinateField F.gradient)),
        |∫ x, φ.source x * F.toFun x ∂g.volume| ≤
          C * ‖greenSmoothDifferentialClass (g := g) F hF‖ := by
  rcases
      greenSmoothTestSourcePairing_abs_le_const_mul_sqrt_dirichlet_of_pure_capacity
        φ hcap with
    ⟨C, hC_nonneg, hC⟩
  refine ⟨C, hC_nonneg, ?_⟩
  intro F hF
  let η : GreenSobolevH10SmoothTest g :=
    { F := F
      differential_memL2 := hF }
  have hη := hC η
  rw [greenSmoothDifferentialClass_norm_eq_sqrt_dirichlet F hF]
  simpa [η, greenSmoothTestSourcePairing] using hη

/--
%%handwave
name:
  Source pairing depends only on the differential class
statement:
  Suppose \(s\) is smooth and compactly supported and pure capacity holds at
  infinity.  If smooth compactly supported \(F,G\) satisfy \([dF]=[dG]\), then
  \(\int_X sF\,d\mu_g=\int_X sG\,d\mu_g\).
proof:
  Form \(H=F-G\).  Its differential class is zero, so the norm bound forces
  \(\int_X sH\,d\mu_g=0\).  Additivity and homogeneity of the pairing identify
  this integral with the difference of the two asserted pairings.
-/
theorem greenSmoothDifferentialClass_source_pairing_eq_of_eq
    {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X} {source : X → ℝ}
    (hsource_compact : HasCompactSupportOnSurface source)
    (hsource_smooth : IsSmoothOnSurface (Set.univ : Set X) source)
    (hcap : HasPureDirichletCapacityAtInfinity g)
    (F G : SmoothCompactlySupportedGlobalSurfaceFunction X)
    (hF : SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
      (SurfaceDifferentialField.ofCoordinateField F.gradient))
    (hG : SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
      (SurfaceDifferentialField.ofCoordinateField G.gradient))
    (hEq :
      greenSmoothDifferentialClass (g := g) F hF =
        greenSmoothDifferentialClass (g := g) G hG) :
    ∫ x, source x * F.toFun x ∂g.volume =
      ∫ x, source x * G.toFun x ∂g.volume := by
  let negG : SmoothCompactlySupportedGlobalSurfaceFunction X :=
    SmoothCompactlySupportedGlobalSurfaceFunction.smul (-1 : ℝ) G
  let H : SmoothCompactlySupportedGlobalSurfaceFunction X :=
    SmoothCompactlySupportedGlobalSurfaceFunction.add F negG
  let dF : SquareIntegrableSurfaceDifferentialField
      (X := X) (E := ℝ) g.metric g.volume :=
    { toSection := SurfaceDifferentialField.ofCoordinateField F.gradient
      memL2 := hF }
  let dG : SquareIntegrableSurfaceDifferentialField
      (X := X) (E := ℝ) g.metric g.volume :=
    { toSection := SurfaceDifferentialField.ofCoordinateField G.gradient
      memL2 := hG }
  let dNegG : SquareIntegrableSurfaceDifferentialField
      (X := X) (E := ℝ) g.metric g.volume :=
    squareIntegrableSurfaceDifferentialFieldSmul g.metric g.volume
      (-1 : ℝ) dG
  let dH : SquareIntegrableSurfaceDifferentialField
      (X := X) (E := ℝ) g.metric g.volume :=
    squareIntegrableSurfaceDifferentialFieldAdd g.metric g.volume dF dNegG
  have hH : SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
      (SurfaceDifferentialField.ofCoordinateField H.gradient) := by
    change SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
      dH.toSection
    exact dH.memL2
  have hAe : ∀ᵐ x ∂g.volume, F.gradient x = G.gradient x := by
    have hrel := Quotient.exact hEq
    simpa [greenSmoothDifferentialClass,
      SquareIntegrableSurfaceDifferentialField.AeEq,
      SquareIntegrableHilbertBundleSection.AeEq,
      SurfaceDifferentialField.ofCoordinateField, dF, dG] using hrel
  have hD :
      ∫ x, g.gradientInner x (H.gradient x) (H.gradient x) ∂g.volume = 0 := by
    have hzero_ae :
        (fun x ↦ g.gradientInner x (H.gradient x) (H.gradient x)) =ᵐ[g.volume]
          (fun _ : X ↦ (0 : ℝ)) := by
      filter_upwards [hAe] with x hx
      have hHx : H.gradient x = 0 := by
        dsimp [H, negG, SmoothCompactlySupportedGlobalSurfaceFunction.add,
          SmoothCompactlySupportedGlobalSurfaceFunction.smul]
        ext v
        simp [hx]
      simpa [hHx] using
        (BackgroundSurfaceMetricOnSurface.gradientInner_smul_smul
          g x (0 : ℂ →L[ℝ] ℝ) (0 : ℝ))
    calc
      ∫ x, g.gradientInner x (H.gradient x) (H.gradient x) ∂g.volume =
          ∫ _x, (0 : ℝ) ∂g.volume := by
        exact integral_congr_ae hzero_ae
      _ = 0 := by simp
  have hzero_source :
      ∫ x, source x * H.toFun x ∂g.volume = 0 :=
    compactly_supported_smooth_source_pairing_eq_zero_of_pure_dirichlet_eq_zero
      hsource_compact hsource_smooth hcap H hD
  have hH_source :
      ∫ x, source x * H.toFun x ∂g.volume =
        ∫ x, source x * F.toFun x ∂g.volume -
          ∫ x, source x * G.toFun x ∂g.volume := by
    calc
      ∫ x, source x * H.toFun x ∂g.volume =
          ∫ x, source x * F.toFun x ∂g.volume +
            ∫ x, source x * negG.toFun x ∂g.volume := by
        simpa [H] using
          compactly_supported_smooth_source_pairing_add
            hsource_compact hsource_smooth F negG
      _ = ∫ x, source x * F.toFun x ∂g.volume +
            (-1 : ℝ) * ∫ x, source x * G.toFun x ∂g.volume := by
        rw [compactly_supported_smooth_source_pairing_smul
          hsource_compact hsource_smooth (-1 : ℝ) G]
      _ = ∫ x, source x * F.toFun x ∂g.volume -
            ∫ x, source x * G.toFun x ∂g.volume := by
        ring
  have hsub :
      ∫ x, source x * F.toFun x ∂g.volume -
          ∫ x, source x * G.toFun x ∂g.volume = 0 := by
    rw [← hH_source]
    exact hzero_source
  exact sub_eq_zero.mp hsub

noncomputable def greenSmoothCoreSourceRaw
    {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    (φ : LogarithmicCutoffPoleModel g p)
    (u : (greenSobolevH10SmoothCompactSupportCore g).Core) : ℝ :=
  ∫ x, φ.source x *
    (greenSobolevH10SmoothCompactSupportCorePrimitive u).toFun x ∂g.volume

/--
%%handwave
name:
  The raw source functional is additive on the smooth core
statement:
  Under pure capacity at infinity, for core elements \(u,v\),
  \[
    \Lambda_{\mathrm{raw}}(u+v)=\Lambda_{\mathrm{raw}}(u)+\Lambda_{\mathrm{raw}}(v).
  \]
proof:
  The sum of the chosen primitives of \(u,v\) represents \(u+v\).  Independence
  of source pairing from the chosen primitive replaces the primitive selected
  for \(u+v\) by that sum, after which integral additivity applies.
-/
theorem greenSmoothCoreSourceRaw_add
    {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    (φ : LogarithmicCutoffPoleModel g p)
    (hcap : HasPureDirichletCapacityAtInfinity g)
    (u v : (greenSobolevH10SmoothCompactSupportCore g).Core) :
    greenSmoothCoreSourceRaw φ (u + v) =
      greenSmoothCoreSourceRaw φ u + greenSmoothCoreSourceRaw φ v := by
  let Fu := greenSobolevH10SmoothCompactSupportCorePrimitive u
  let Fv := greenSobolevH10SmoothCompactSupportCorePrimitive v
  let hFu := greenSobolevH10SmoothCompactSupportCorePrimitive_memL2 u
  let hFv := greenSobolevH10SmoothCompactSupportCorePrimitive_memL2 v
  let H := SmoothCompactlySupportedGlobalSurfaceFunction.add Fu Fv
  let dFu : SquareIntegrableSurfaceDifferentialField
      (X := X) (E := ℝ) g.metric g.volume :=
    { toSection := SurfaceDifferentialField.ofCoordinateField Fu.gradient
      memL2 := hFu }
  let dFv : SquareIntegrableSurfaceDifferentialField
      (X := X) (E := ℝ) g.metric g.volume :=
    { toSection := SurfaceDifferentialField.ofCoordinateField Fv.gradient
      memL2 := hFv }
  let dH : SquareIntegrableSurfaceDifferentialField
      (X := X) (E := ℝ) g.metric g.volume :=
    squareIntegrableSurfaceDifferentialFieldAdd g.metric g.volume dFu dFv
  have hH : SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
      (SurfaceDifferentialField.ofCoordinateField H.gradient) := by
    change SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
      dH.toSection
    exact dH.memL2
  have hH_class :
      greenSmoothDifferentialClass (g := g) H hH = (u + v).1 := by
    calc
      greenSmoothDifferentialClass (g := g) H hH =
          greenSmoothDifferentialClass (g := g) Fu hFu +
            greenSmoothDifferentialClass (g := g) Fv hFv :=
        greenSmoothDifferentialClass_add Fu Fv hFu hFv hH
      _ = u.1 + v.1 := by
        rw [greenSobolevH10SmoothCompactSupportCorePrimitive_class_eq u,
          greenSobolevH10SmoothCompactSupportCorePrimitive_class_eq v]
      _ = (u + v).1 := rfl
  have hchoice_eq_H :
      ∫ x, φ.source x *
          (greenSobolevH10SmoothCompactSupportCorePrimitive (u + v)).toFun x
          ∂g.volume =
        ∫ x, φ.source x * H.toFun x ∂g.volume :=
    greenSmoothDifferentialClass_source_pairing_eq_of_eq
      φ.source_compact_support φ.source_smooth hcap
      (greenSobolevH10SmoothCompactSupportCorePrimitive (u + v)) H
      (greenSobolevH10SmoothCompactSupportCorePrimitive_memL2 (u + v)) hH
      ((greenSobolevH10SmoothCompactSupportCorePrimitive_class_eq
          (u + v)).trans hH_class.symm)
  calc
    greenSmoothCoreSourceRaw φ (u + v) =
        ∫ x, φ.source x * H.toFun x ∂g.volume := by
      simpa [greenSmoothCoreSourceRaw] using hchoice_eq_H
    _ = ∫ x, φ.source x * Fu.toFun x ∂g.volume +
          ∫ x, φ.source x * Fv.toFun x ∂g.volume := by
      simpa [H] using
        compactly_supported_smooth_source_pairing_add
          φ.source_compact_support φ.source_smooth Fu Fv
    _ = greenSmoothCoreSourceRaw φ u + greenSmoothCoreSourceRaw φ v := by
      rfl

/--
%%handwave
name:
  The raw source functional is homogeneous on the smooth core
statement:
  Under pure capacity at infinity, for \(c\in\mathbb R\) and a core element \(u\),
  \[
    \Lambda_{\mathrm{raw}}(cu)=c\,\Lambda_{\mathrm{raw}}(u).
  \]
proof:
  The scalar multiple of the chosen primitive of \(u\) represents \(cu\).
  Replace the chosen primitive of \(cu\) by this one using independence of
  source pairing, then pull \(c\) through the integral.
-/
theorem greenSmoothCoreSourceRaw_smul
    {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    (φ : LogarithmicCutoffPoleModel g p)
    (hcap : HasPureDirichletCapacityAtInfinity g)
    (c : ℝ) (u : (greenSobolevH10SmoothCompactSupportCore g).Core) :
    greenSmoothCoreSourceRaw φ (c • u) =
      c • greenSmoothCoreSourceRaw φ u := by
  let Fu := greenSobolevH10SmoothCompactSupportCorePrimitive u
  let hFu := greenSobolevH10SmoothCompactSupportCorePrimitive_memL2 u
  let H := SmoothCompactlySupportedGlobalSurfaceFunction.smul c Fu
  let dFu : SquareIntegrableSurfaceDifferentialField
      (X := X) (E := ℝ) g.metric g.volume :=
    { toSection := SurfaceDifferentialField.ofCoordinateField Fu.gradient
      memL2 := hFu }
  let dH : SquareIntegrableSurfaceDifferentialField
      (X := X) (E := ℝ) g.metric g.volume :=
    squareIntegrableSurfaceDifferentialFieldSmul g.metric g.volume c dFu
  have hH : SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
      (SurfaceDifferentialField.ofCoordinateField H.gradient) := by
    change SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
      dH.toSection
    exact dH.memL2
  have hH_class :
      greenSmoothDifferentialClass (g := g) H hH = (c • u).1 := by
    calc
      greenSmoothDifferentialClass (g := g) H hH =
          c • greenSmoothDifferentialClass (g := g) Fu hFu :=
        greenSmoothDifferentialClass_smul c Fu hFu hH
      _ = c • u.1 := by
        rw [greenSobolevH10SmoothCompactSupportCorePrimitive_class_eq u]
      _ = (c • u).1 := rfl
  have hchoice_eq_H :
      ∫ x, φ.source x *
          (greenSobolevH10SmoothCompactSupportCorePrimitive (c • u)).toFun x
          ∂g.volume =
        ∫ x, φ.source x * H.toFun x ∂g.volume :=
    greenSmoothDifferentialClass_source_pairing_eq_of_eq
      φ.source_compact_support φ.source_smooth hcap
      (greenSobolevH10SmoothCompactSupportCorePrimitive (c • u)) H
      (greenSobolevH10SmoothCompactSupportCorePrimitive_memL2 (c • u)) hH
      ((greenSobolevH10SmoothCompactSupportCorePrimitive_class_eq
          (c • u)).trans hH_class.symm)
  calc
    greenSmoothCoreSourceRaw φ (c • u) =
        ∫ x, φ.source x * H.toFun x ∂g.volume := by
      simpa [greenSmoothCoreSourceRaw] using hchoice_eq_H
    _ = c * ∫ x, φ.source x * Fu.toFun x ∂g.volume := by
      simpa [H] using
        compactly_supported_smooth_source_pairing_smul
          φ.source_compact_support φ.source_smooth c Fu
    _ = c • greenSmoothCoreSourceRaw φ u := by
      rfl

noncomputable def greenSmoothCoreSourceLinearMap
    {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    (φ : LogarithmicCutoffPoleModel g p)
    (hcap : HasPureDirichletCapacityAtInfinity g) :
    (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ := by
  let L : (greenSobolevH10SmoothCompactSupportCore g).Core →ₗ[ℝ] ℝ :=
    { toFun := greenSmoothCoreSourceRaw φ
      map_add' := by
        intro u v
        exact greenSmoothCoreSourceRaw_add φ hcap u v
      map_smul' := by
        intro c u
        exact greenSmoothCoreSourceRaw_smul φ hcap c u }
  let hbound_exists :=
    greenSmoothDifferentialClass_source_abs_le_const_mul_norm_of_pure_capacity
      φ hcap
  let C : ℝ := Classical.choose hbound_exists
  have hC :
      ∀ (F : SmoothCompactlySupportedGlobalSurfaceFunction X)
        (hF : SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
          (SurfaceDifferentialField.ofCoordinateField F.gradient)),
        |∫ x, φ.source x * F.toFun x ∂g.volume| ≤
          C * ‖greenSmoothDifferentialClass (g := g) F hF‖ :=
    (Classical.choose_spec hbound_exists).2
  exact L.mkContinuous C (by
    intro u
    let F := greenSobolevH10SmoothCompactSupportCorePrimitive u
    let hF := greenSobolevH10SmoothCompactSupportCorePrimitive_memL2 u
    have hbound := hC F hF
    calc
      ‖L u‖ = |greenSmoothCoreSourceRaw φ u| := by
        rfl
      _ ≤ C * ‖greenSmoothDifferentialClass (g := g) F hF‖ := by
        simpa [greenSmoothCoreSourceRaw, F, hF] using hbound
      _ = C * ‖u‖ := by
        rw [greenSobolevH10SmoothCompactSupportCorePrimitive_class_eq u]
        rfl)

/--
%%handwave
name:
  The extended core source agrees with smooth-test pairing
statement:
  For a logarithmic cutoff model and pure capacity at infinity, the continuous
  source functional obtained from the smooth core satisfies
  \[
    \Lambda(\eta)=\int_X s\,\eta\,d\mu_g
  \]
  on every smooth compactly supported pure test \(\eta\).
proof:
  Write \(\eta\) as the completion image of its differential core element.
  The extension agrees with the raw core functional there, and primitive
  independence replaces the chosen primitive by \(\eta\) itself.
-/
theorem greenSmoothCoreSourceLinearMap_toH10_smoothTest
    {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    (φ : LogarithmicCutoffPoleModel g p)
    (hcap : HasPureDirichletCapacityAtInfinity g)
    (η : GreenSobolevH10SmoothTest g) :
    greenSobolevH10SmoothCompactSupportSource
        (greenSmoothCoreSourceLinearMap φ hcap) η.toH10 =
      greenSmoothTestSourcePairing φ η := by
  let Ccore := greenSobolevH10SmoothCompactSupportCore g
  let ucore : Ccore.Core :=
    ⟨η.differentialClass,
      smoothCompactlySupportedGreenDifferentialClass_mem_core
        η.differentialClass_isSmoothCompactlySupported⟩
  have htoH10 : η.toH10 = Ccore.toCompletion ucore := by
    rfl
  have hsource_core :
      greenSobolevH10SmoothCompactSupportSource
          (greenSmoothCoreSourceLinearMap φ hcap) (Ccore.toCompletion ucore) =
        greenSmoothCoreSourceRaw φ ucore := by
    rw [greenSobolevH10SmoothCompactSupportSource,
      greenSobolevH10CompletionSource]
    rw [GreenSobolevH10DirichletCore.extendSource_toCompletion]
    rfl
  have hclass_eta :
      greenSmoothDifferentialClass (g := g) η.F η.differential_memL2 =
        ucore.1 := by
    rfl
  have hprimitive_eq_eta :
      ∫ x, φ.source x *
          (greenSobolevH10SmoothCompactSupportCorePrimitive ucore).toFun x
          ∂g.volume =
        ∫ x, φ.source x * η.F.toFun x ∂g.volume :=
    greenSmoothDifferentialClass_source_pairing_eq_of_eq
      φ.source_compact_support φ.source_smooth hcap
      (greenSobolevH10SmoothCompactSupportCorePrimitive ucore) η.F
      (greenSobolevH10SmoothCompactSupportCorePrimitive_memL2 ucore)
      η.differential_memL2
      ((greenSobolevH10SmoothCompactSupportCorePrimitive_class_eq
          ucore).trans hclass_eta.symm)
  calc
    greenSobolevH10SmoothCompactSupportSource
        (greenSmoothCoreSourceLinearMap φ hcap) η.toH10 =
        greenSobolevH10SmoothCompactSupportSource
          (greenSmoothCoreSourceLinearMap φ hcap) (Ccore.toCompletion ucore) := by
      rw [htoH10]
    _ = greenSmoothCoreSourceRaw φ ucore := hsource_core
    _ = greenSmoothTestSourcePairing φ η := by
      simpa [greenSmoothCoreSourceRaw, greenSmoothTestSourcePairing]
        using hprimitive_eq_eta

/--
%%handwave
name:
  A logarithmic cutoff source extends continuously to pure \(H^1_0\)
statement:
  Under pure capacity at infinity, every logarithmic cutoff pole model has a
  continuous linear functional on the smooth compactly supported Dirichlet
  core whose extension pairs with each smooth pure test as
  \(\int_X s\,\eta\,d\mu_g\).
proof:
  Take the bounded continuous core source functional and use [its extension agrees with the smooth-test source pairing](lean:JJMath.Uniformization.greenSmoothCoreSourceLinearMap_toH10_smoothTest).
-/
theorem logarithmicCutoffPoleModel_has_smooth_h10_core_source
    {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    (φ : LogarithmicCutoffPoleModel g p)
    (hcap : HasPureDirichletCapacityAtInfinity g) :
    ∃ source :
      (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ,
        ∀ η : GreenSobolevH10SmoothTest g,
          greenSobolevH10SmoothCompactSupportSource source η.toH10 =
            greenSmoothTestSourcePairing φ η :=
  ⟨greenSmoothCoreSourceLinearMap φ hcap,
    greenSmoothCoreSourceLinearMap_toH10_smoothTest φ hcap⟩

/--
%%handwave
name:
  Local weak Green correction
statement:
  A local finite-Dirichlet correction is a weak Green correction when its
  scalar representative is locally \(W^{1,2}\), its weak gradient is the
  stored finite-energy differential, its Dirichlet pairing against every
  smooth compactly supported pure test equals the source pairing, and it
  solves the opposite-source equation on the punctured surface.
-/
structure IsLocalWeakGreenCorrection {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    (φ : LogarithmicCutoffPoleModel g p)
    (h : GreenSobolevH10LocalCorrection g) : Prop where
  localSobolev :
    IsIntrinsicLocalSobolevH1OnSurface g (Set.univ : Set X)
      h.toFun h.weakGradient
  smooth_test_pairing :
    ∀ η : GreenSobolevH10SmoothTest g,
      greenLocalCorrectionSmoothTestDirichletPairing g h η =
        greenSmoothTestSourcePairing φ η
  punctured_opposite_source :
    IsWeakLaplaceBeltramiSourceOnSurface g {x : X | x ≠ p}
      h.toFun (fun x : X ↦ -φ.source x)

/--
%%handwave
name:
  Weak Green corrections satisfy the source-pairing identity
statement:
  If \(h\) is a local weak Green correction for a cutoff source \(s\), then
  for every smooth compactly supported pure test \(\eta\),
  \[
    \int_X\langle dh,d\eta\rangle_g\,d\mu_g=\int_X s\eta\,d\mu_g.
  \]
proof:
  This is the smooth-test pairing clause in the definition of a local weak Green correction.
-/
theorem IsLocalWeakGreenCorrection.dirichletPairing_eq_sourcePairing
    {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    {φ : LogarithmicCutoffPoleModel g p}
    {h : GreenSobolevH10LocalCorrection g}
    (hweak : IsLocalWeakGreenCorrection φ h)
    (η : GreenSobolevH10SmoothTest g) :
    greenLocalCorrectionSmoothTestDirichletPairing g h η =
      greenSmoothTestSourcePairing φ η :=
  hweak.smooth_test_pairing η

/--
%%handwave
name:
  Local weak-correction data for the pure Riesz vector
statement:
  Local weak-correction data for the pure \(H^1_0\) variational solution
  consist of a local Sobolev representative of the Riesz vector, the weak
  opposite-source equation on the punctured surface, a lift of smooth
  compactly supported tests to completed directions, and compatibility of the
  completed inner product and source functional with the local representative
  pairings.
-/
structure GreenSobolevH10SmoothCompactSupportLocalWeakCorrectionData {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    (φ : LogarithmicCutoffPoleModel g p)
    (source : (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ) where
  scalar : GreenSobolevH10SmoothCompactSupportRieszScalarRepresentativeData source
  correction : GreenSobolevH10LocalCorrection g
  correction_toFun_eq_scalar : correction.toFun = scalar.toFun
  localSobolev :
    IsIntrinsicLocalSobolevH1OnSurface g (Set.univ : Set X)
      correction.toFun correction.weakGradient
  punctured_opposite_source :
    IsWeakLaplaceBeltramiSourceOnSurface g {x : X | x ≠ p}
      correction.toFun (fun x : X ↦ -φ.source x)
  test :
    GreenSobolevH10SmoothTest g → GreenSobolevH10SmoothCompactSupport g
  dirichlet_pairing_eq_inner :
    ∀ η : GreenSobolevH10SmoothTest g,
      greenLocalCorrectionSmoothTestDirichletPairing g correction η =
        inner ℝ
          (greenSobolevH10RieszRepresentative
            ((greenSobolevH10SmoothCompactSupportCore g).extendSource source))
          (test η)
  source_eq_source_pairing :
    ∀ η : GreenSobolevH10SmoothTest g,
      greenSobolevH10SmoothCompactSupportSource source (test η) =
        greenSmoothTestSourcePairing φ η

/--
%%handwave
name:
  Local correction decoded from the pure \(H^1_0\) Riesz vector
statement:
  The local scalar correction associated to pure \(H^1_0\) Riesz data is the
  stored local representative of the Riesz representative of the extended
  source functional.
-/
noncomputable def greenSobolevH10SmoothCompactSupportLocalRieszCorrection
    {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    {φ : LogarithmicCutoffPoleModel g p}
    {source : (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ}
    (hdata :
      GreenSobolevH10SmoothCompactSupportLocalWeakCorrectionData φ source) :
    GreenSobolevH10LocalCorrection g :=
  hdata.correction

/--
%%handwave
name:
  Pure \(H^1_0\) Riesz decode gives a local weak correction
statement:
  If the pure \(H^1_0\) source and the stored local Riesz representative are
  compatible with smooth compactly supported test pairings, then the
  representative solves the local weak Green equation.
proof:
  The stored differential pairing is the Hilbert inner product of the Riesz
  vector with the test vector. [The Euler--Lagrange identity identifies this inner product with the extended source](lean:JJMath.Uniformization.greenSobolevH10SmoothCompactSupportEnergy_rieszRepresentative_eulerLagrange), and the compatibility hypothesis identifies that source with the local Green pairing. The punctured opposite-source equation is already part of the local data.
-/
theorem greenSobolevH10SmoothCompactSupportLocalRieszCorrection_isLocalWeakGreenCorrection
    {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    {φ : LogarithmicCutoffPoleModel g p}
    {source : (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ}
    (hdata :
      GreenSobolevH10SmoothCompactSupportLocalWeakCorrectionData φ source) :
    IsLocalWeakGreenCorrection φ
      (greenSobolevH10SmoothCompactSupportLocalRieszCorrection hdata) := by
  refine
    { localSobolev := hdata.localSobolev
      smooth_test_pairing := ?_
      punctured_opposite_source := hdata.punctured_opposite_source }
  intro η
  let u : GreenSobolevH10SmoothCompactSupport g :=
    greenSobolevH10RieszRepresentative
      ((greenSobolevH10SmoothCompactSupportCore g).extendSource source)
  change
    greenLocalCorrectionSmoothTestDirichletPairing g hdata.correction η =
      greenSmoothTestSourcePairing φ η
  calc
    greenLocalCorrectionSmoothTestDirichletPairing g hdata.correction η =
        inner ℝ u (hdata.test η) :=
      hdata.dirichlet_pairing_eq_inner η
    _ = greenSobolevH10SmoothCompactSupportSource source (hdata.test η) := by
      dsimp [u]
      exact
        greenSobolevH10SmoothCompactSupportEnergy_rieszRepresentative_eulerLagrange
          source (hdata.test η)
    _ = greenSmoothTestSourcePairing φ η :=
      hdata.source_eq_source_pairing η

/--
%%handwave
name:
  Pure \(H^1_0\) local Riesz data gives a local weak correction
statement:
  Compatible pure \(H^1_0\) source and local decode data produce a local
  finite-Dirichlet weak Green correction.
proof:
  Decode the Riesz minimizer into a local Sobolev function, use the Euler identity against every smooth compactly supported test, and identify the resulting distributional equation as the desired weak correction.
-/
theorem exists_local_weak_green_correction_of_smooth_h10_riesz_decode
    {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    (φ : LogarithmicCutoffPoleModel g p)
    (source : (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ)
    (hdata :
      GreenSobolevH10SmoothCompactSupportLocalWeakCorrectionData φ source) :
    ∃ h : GreenSobolevH10LocalCorrection g, IsLocalWeakGreenCorrection φ h :=
  ⟨greenSobolevH10SmoothCompactSupportLocalRieszCorrection hdata,
    greenSobolevH10SmoothCompactSupportLocalRieszCorrection_isLocalWeakGreenCorrection
      hdata⟩

/--
%%handwave
name:
  Pure Riesz vector has a local finite-Dirichlet representative
statement:
  The Riesz representative of a continuous source on the smooth Dirichlet
  core determines a finite-Dirichlet variational correction whose Dirichlet
  pairings against compactly supported smooth tests agree with the completed
  \(H^1_0\) inner product.
proof:
  Choose the square-integrable cotangent representative of the completed
  differential class of the Riesz vector and package it as the correction
  differential.  The smooth-test pairing identity follows from the
  completed-to-intrinsic differential pairing comparison.
-/
theorem greenSobolevH10SmoothCompactSupport_rieszRepresentative_has_local_correction
    {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (_hcap : HasPureDirichletCapacityAtInfinity g)
    (source : (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ) :
    ∃ h : GreenSobolevH10LocalCorrection g,
      ∀ η : GreenSobolevH10SmoothTest g,
        greenLocalCorrectionSmoothTestDirichletPairing g h η =
          inner ℝ
            (greenSobolevH10RieszRepresentative
              ((greenSobolevH10SmoothCompactSupportCore g).extendSource source))
            η.toH10 := by
  let u : GreenSobolevH10SmoothCompactSupport g :=
    greenSobolevH10RieszRepresentative
      ((greenSobolevH10SmoothCompactSupportCore g).extendSource source)
  let grad : X → ℂ →L[ℝ] ℝ :=
    fun x ↦
      SurfaceDifferentialField.toCoordinateField
        (greenSobolevH10SmoothCompactSupportDifferentialRep u).toField x
  let h : GreenSobolevH10LocalCorrection g :=
    { toFun := fun _ ↦ 0
      weakGradient := grad
      dirichlet_integrable := by
        simpa [grad] using
          greenSobolevH10SmoothCompactSupportDifferentialRep_dirichlet_integrable
            u }
  refine ⟨h, ?_⟩
  intro η
  simpa [u] using
    greenLocalCorrectionSmoothTestDirichletPairing_eq_inner_of_weakGradient_eq
      u h (by simp [h, grad]) η

/--
%%handwave
name:
  Riesz vectors have compact-local Cauchy primitive approximants
statement:
  Under pure Dirichlet capacity at infinity, the pure \(H^1_0\) Riesz vector
  admits smooth compactly supported primitive approximants which converge in
  the pure completion, are compact-locally Cauchy in \(L^2\), and whose
  differential classes converge to the Riesz differential class.
proof:
  Apply the compact-local \(L^2\) Cauchy approximation theorem to the Riesz
  vector in the pure Dirichlet completion.
-/
theorem
    greenSobolevH10SmoothCompactSupport_rieszRepresentative_exists_core_sequence_with_localL2_cauchy
    {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (hcap : HasPureDirichletCapacityAtInfinity g)
    (source : (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ) :
    ∃ U : ℕ → (greenSobolevH10SmoothCompactSupportCore g).Core,
      Filter.Tendsto
        (fun n : ℕ ↦
          (greenSobolevH10SmoothCompactSupportCore g).toCompletion (U n))
        Filter.atTop
        (𝓝 (greenSobolevH10SmoothCompactSupportRieszVector source)) ∧
      (∀ K : Set X, IsCompact K →
        ∀ ε : ℝ, 0 < ε →
          ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
            ∫ x in K,
                ‖(greenSobolevH10SmoothCompactSupportCorePrimitive (U n)).toFun x -
                  (greenSobolevH10SmoothCompactSupportCorePrimitive (U m)).toFun x‖ ^
                  (2 : ℕ) ∂g.volume < ε) ∧
      Filter.Tendsto (fun n : ℕ ↦ (U n).1) Filter.atTop
        (𝓝
          (greenSobolevH10SmoothCompactSupportDifferentialClass
            (greenSobolevH10SmoothCompactSupportRieszVector source))) := by
  exact
    greenSobolevH10SmoothCompactSupport_exists_core_sequence_with_localL2_cauchy
      hcap (greenSobolevH10SmoothCompactSupportRieszVector source)

/--
%%handwave
name:
  Riesz vectors have compact-local \(L^2\) primitive limits
statement:
  Under pure Dirichlet capacity at infinity, the smooth primitive
  approximants for the pure Riesz vector have an \(L^2\)-limit on every
  compact subset.
proof:
  Choose the smooth approximating sequence whose primitives are
  compact-locally \(L^2\)-Cauchy.  Completeness of \(L^2(K)\) gives a limit
  on each compact set, while the same sequence still converges to the Riesz
  vector in the pure completion and in differential class.
-/
theorem
    greenSobolevH10SmoothCompactSupport_rieszRepresentative_exists_core_sequence_with_localLp_limits
    {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (hcap : HasPureDirichletCapacityAtInfinity g)
    (source : (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ) :
    ∃ U : ℕ → (greenSobolevH10SmoothCompactSupportCore g).Core,
      Filter.Tendsto
        (fun n : ℕ ↦
          (greenSobolevH10SmoothCompactSupportCore g).toCompletion (U n))
        Filter.atTop
        (𝓝 (greenSobolevH10SmoothCompactSupportRieszVector source)) ∧
      (∀ K : Set X, (hK : IsCompact K) →
        ∃ fK : Lp ℝ 2 (g.volume.restrict K),
          Filter.Tendsto
            (fun n : ℕ ↦
              (((greenSobolevH10SmoothCompactSupportCorePrimitive (U n)).memLp_restrict_compact
                (g := g) hK).toLp
                  (greenSobolevH10SmoothCompactSupportCorePrimitive (U n)).toFun :
                Lp ℝ 2 (g.volume.restrict K)))
            Filter.atTop (𝓝 fK)) ∧
      Filter.Tendsto (fun n : ℕ ↦ (U n).1) Filter.atTop
        (𝓝
          (greenSobolevH10SmoothCompactSupportDifferentialClass
            (greenSobolevH10SmoothCompactSupportRieszVector source))) := by
  rcases
      greenSobolevH10SmoothCompactSupport_rieszRepresentative_exists_core_sequence_with_localL2_cauchy
        hcap source with
    ⟨U, hU, _hlocalCauchy, hU_diff⟩
  refine ⟨U, hU, ?_, hU_diff⟩
  intro K hK
  exact
    greenSobolevH10SmoothCompactSupportCorePrimitive_exists_localLp_limit_of_tendsto_completion
      hcap U (greenSobolevH10SmoothCompactSupportRieszVector source) hU hK

/--
%%handwave
name:
  Riesz Euler identity against smooth tests
statement:
  The chosen \(L^2\) cotangent representative of the Riesz vector pairs
  against every compactly supported smooth test as the source pairing.
proof:
  Identify the integral pairing with the completed \(H^1_0\) inner product
  against the smooth test.  The Riesz Euler equation evaluates that inner
  product as the extended source, and the assumed smooth-test compatibility
  identifies it with integration against the cutoff source.
-/
theorem greenSobolevH10SmoothCompactSupport_rieszRepresentative_smoothTest_euler
    {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    (φ : LogarithmicCutoffPoleModel g p)
    (source : (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ)
    (hsource_smooth_tests :
      ∀ η : GreenSobolevH10SmoothTest g,
        greenSobolevH10SmoothCompactSupportSource source η.toH10 =
          greenSmoothTestSourcePairing φ η)
    (η : GreenSobolevH10SmoothTest g) :
    ∫ x, g.gradientInner x
        (greenSobolevH10SmoothCompactSupportRieszGradient source x)
        (η.F.gradient x) ∂g.volume =
      greenSmoothTestSourcePairing φ η := by
  let u : GreenSobolevH10SmoothCompactSupport g :=
    greenSobolevH10SmoothCompactSupportRieszVector source
  calc
    ∫ x, g.gradientInner x
        (greenSobolevH10SmoothCompactSupportRieszGradient source x)
        (η.F.gradient x) ∂g.volume =
        ∫ x, g.gradientInner x
          (SurfaceDifferentialField.toCoordinateField
            (greenSobolevH10SmoothCompactSupportDifferentialRep u).toField x)
          (η.F.gradient x) ∂g.volume := by
          simp [u, greenSobolevH10SmoothCompactSupportRieszGradient,
            greenSobolevH10SmoothCompactSupportRieszVector]
    _ =
        inner ℝ
          (greenSobolevH10SmoothCompactSupportDifferentialClass u)
          η.differentialClass :=
          (greenSobolevH10SmoothCompactSupportDifferentialRep_inner_smoothTest_eq_integral
            u η).symm
    _ = inner ℝ u η.toH10 :=
          (greenSobolevH10SmoothCompactSupport_inner_smoothTest_eq_differential_inner
            u η).symm
    _ = greenSobolevH10SmoothCompactSupportSource source η.toH10 := by
          simpa [u, greenSobolevH10SmoothCompactSupportRieszVector] using
            greenSobolevH10SmoothCompactSupportEnergy_rieszRepresentative_eulerLagrange
              source η.toH10
    _ = greenSmoothTestSourcePairing φ η :=
          hsource_smooth_tests η

/--
%%handwave
name:
  The Riesz differential pairs integrably with smooth pure tests
statement:
  The pointwise metric pairing of the chosen Riesz differential
  representative with the differential of a smooth compactly supported pure
  test is integrable over the surface.
proof:
  Both differentials are square-integrable Hilbert-bundle sections.  The
  fiberwise inner product of two \(L^2\) sections is integrable, and the
  intrinsic Hilbert--Schmidt fiber inner product is the background cotangent
  metric pairing.
-/
theorem
    greenSobolevH10SmoothCompactSupport_rieszRepresentative_smoothTest_pairing_integrable
    {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (source : (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ)
    (η : GreenSobolevH10SmoothTest g) :
    Integrable
      (fun x ↦
        g.gradientInner x
          (greenSobolevH10SmoothCompactSupportRieszGradient source x)
          (η.F.gradient x)) g.volume := by
  let metric :=
    manifoldDifferentialHilbertSchmidtContinuousRiemannianMetric
      (I := SurfaceRealModel) (X := X) (E := ℝ) g.metric.toManifoldMetric
  letI : Bundle.RiemannianBundle
      (ManifoldDifferentialBundleFiber
        (I := SurfaceRealModel) (X := X) (E := ℝ)) :=
    ⟨metric.toRiemannianMetric⟩
  letI (x : X) :
      NormedAddCommGroup
        (ManifoldDifferentialBundleFiber
          (I := SurfaceRealModel) (X := X) (E := ℝ) x) :=
    manifoldDifferentialHilbertSchmidtNormedAddCommGroup
      (I := SurfaceRealModel) (X := X) (E := ℝ) metric x
  letI (x : X) :
      InnerProductSpace ℝ
        (ManifoldDifferentialBundleFiber
          (I := SurfaceRealModel) (X := X) (E := ℝ) x) :=
    manifoldDifferentialHilbertSchmidtInnerProductSpace
      (I := SurfaceRealModel) (X := X) (E := ℝ) metric x
  let u : GreenSobolevH10SmoothCompactSupport g :=
    greenSobolevH10SmoothCompactSupportRieszVector source
  let dU : SquareIntegrableSurfaceDifferentialField
      (X := X) (E := ℝ) g.metric g.volume :=
    greenSobolevH10SmoothCompactSupportDifferentialRep u
  let dη : SquareIntegrableSurfaceDifferentialField
      (X := X) (E := ℝ) g.metric g.volume :=
    { toSection := SurfaceDifferentialField.ofCoordinateField η.F.gradient
      memL2 := η.differential_memL2 }
  have hinner :
      Integrable (fun x : X ↦ inner ℝ (dU.toSection x) (dη.toSection x))
        g.volume :=
    squareIntegrableHilbertBundleSection_inner_integrable
      (I := SurfaceRealModel)
      (G := manifoldDifferentialHilbertBundleGeometry
        (I := SurfaceRealModel) (X := X) (E := ℝ)
        g.metric.toManifoldMetric)
      (fun _ _ _ ↦ rfl) g.volume dU dη
  refine hinner.congr ?_
  filter_upwards [] with x
  have hfiber :
      inner ℝ (dU.toSection x) (dη.toSection x) =
        g.gradientInner x
          (SurfaceDifferentialField.toCoordinateField dU.toField x)
          (η.F.gradient x) := by
    simpa [dU, dη, SurfaceDifferentialField.toCoordinateField,
      SurfaceDifferentialField.ofCoordinateField] using
      surface_coordinate_cotangent_fiberInner_eq_gradientInner g x
        (SurfaceDifferentialField.toCoordinateField dU.toField x)
        (η.F.gradient x)
  simpa [u, dU, greenSobolevH10SmoothCompactSupportRieszGradient] using
    hfiber

/--
%%handwave
name:
  Local corrections pair integrably with smooth pure tests
statement:
  If a local finite-energy correction is locally \(W^{1,2}\), then its
  weak gradient pairs integrably with the differential of every compactly
  supported smooth pure test.
proof:
  Localize to the compact support of the test.  On this compact set both the
  correction differential and the test differential are square-integrable
  Hilbert-bundle sections, so their fiberwise inner product is integrable by
  Cauchy--Schwarz.  Outside the test support the test differential vanishes.
-/
theorem greenLocalCorrectionSmoothChartTest_pairing_integrable_of_localSobolev
    {X : Type}
    [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    {h : GreenSobolevH10LocalCorrection g}
    (hlocal :
      IsIntrinsicLocalSobolevH1OnSurface g (Set.univ : Set X)
        h.toFun h.weakGradient)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    {Ω : Set ℂ}
    (η : SmoothCompactlySupportedManifoldCoordinateFunction Ω)
    (hΩ_target : Ω ⊆ e.target)
    (hdiff :
      SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
        (SurfaceDifferentialField.ofCoordinateField
          (SmoothCompactlySupportedGlobalSurfaceFunction.ofChartTest
            e he η hΩ_target).gradient)) :
    Integrable
      (fun x ↦
        g.gradientInner x (h.weakGradient x)
          ((SmoothCompactlySupportedGlobalSurfaceFunction.ofChartTest
            e he η hΩ_target).gradient x)) g.volume := by
  let F : SmoothCompactlySupportedGlobalSurfaceFunction X :=
    SmoothCompactlySupportedGlobalSurfaceFunction.ofChartTest
      e he η hΩ_target
  let K : Set X := tsupport F.toFun
  have hK_compact : IsCompact K := F.compact_support
  have hduK :
      SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric
        (g.volume.restrict K)
        (SurfaceCotangentField.ofCoordinateField h.weakGradient) :=
    (hlocal.2 K hK_compact (Set.subset_univ K)).2
  have hdηK :
      SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric
        (g.volume.restrict K)
        (SurfaceDifferentialField.ofCoordinateField F.gradient) :=
    ⟨hdiff.1.mono_measure Measure.restrict_le_self,
      hdiff.2.mono_measure Measure.restrict_le_self⟩
  let metric :=
    manifoldDifferentialHilbertSchmidtContinuousRiemannianMetric
      (I := SurfaceRealModel) (X := X) (E := ℝ) g.metric.toManifoldMetric
  letI : Bundle.RiemannianBundle
      (ManifoldDifferentialBundleFiber
        (I := SurfaceRealModel) (X := X) (E := ℝ)) :=
    ⟨metric.toRiemannianMetric⟩
  letI (x : X) :
      NormedAddCommGroup
        (ManifoldDifferentialBundleFiber
          (I := SurfaceRealModel) (X := X) (E := ℝ) x) :=
    manifoldDifferentialHilbertSchmidtNormedAddCommGroup
      (I := SurfaceRealModel) (X := X) (E := ℝ) metric x
  letI (x : X) :
      InnerProductSpace ℝ
        (ManifoldDifferentialBundleFiber
          (I := SurfaceRealModel) (X := X) (E := ℝ) x) :=
    manifoldDifferentialHilbertSchmidtInnerProductSpace
      (I := SurfaceRealModel) (X := X) (E := ℝ) metric x
  let dH : SquareIntegrableSurfaceDifferentialField
      (X := X) (E := ℝ) g.metric (g.volume.restrict K) :=
    { toSection := SurfaceCotangentField.ofCoordinateField h.weakGradient
      memL2 := hduK }
  let dη : SquareIntegrableSurfaceDifferentialField
      (X := X) (E := ℝ) g.metric (g.volume.restrict K) :=
    { toSection := SurfaceDifferentialField.ofCoordinateField F.gradient
      memL2 := hdηK }
  have hinnerK :
      Integrable (fun x : X ↦ inner ℝ (dH.toSection x) (dη.toSection x))
        (g.volume.restrict K) :=
    squareIntegrableHilbertBundleSection_inner_integrable
      (I := SurfaceRealModel)
      (G := manifoldDifferentialHilbertBundleGeometry
        (I := SurfaceRealModel) (X := X) (E := ℝ)
        g.metric.toManifoldMetric)
      (fun _ _ _ ↦ rfl) (g.volume.restrict K) dH dη
  let gradSurface : X → ℝ := fun x ↦
    g.gradientInner x (h.weakGradient x) (F.gradient x)
  have hgradK : Integrable gradSurface (g.volume.restrict K) := by
    refine hinnerK.congr ?_
    filter_upwards [] with x
    have hfiber :
        inner ℝ (dH.toSection x) (dη.toSection x) =
          g.gradientInner x (h.weakGradient x) (F.gradient x) := by
      simpa [dH, dη, SurfaceCotangentField.ofCoordinateField,
        SurfaceDifferentialField.ofCoordinateField] using
        surface_coordinate_cotangent_fiberInner_eq_gradientInner g x
          (h.weakGradient x) (F.gradient x)
    simpa [gradSurface] using hfiber
  have hgrad_support : Function.support gradSurface ⊆ K := by
    intro x hx
    by_contra hxK
    have hdiff_zero :
        surfaceExteriorDerivative F.toFun x = 0 :=
      surfaceDifferential_eq_zero_of_notMem_tsupport
        (surfaceExteriorDerivative_isSurfaceDifferential F.smooth) hxK
    have hgrad_zero : F.gradient x = 0 := by
      simpa [F, SmoothCompactlySupportedGlobalSurfaceFunction.ofChartTest] using hdiff_zero
    have hzero : gradSurface x = 0 := by
      simp only [gradSurface, hgrad_zero]
      exact cotangentInner_zero_right_of_isMetricDual
        g.metric g.gradientInner
        (BackgroundSurfaceMetricOnSurface.gradientInner_isMetricDual g) x
        (h.weakGradient x)
    exact hx hzero
  have hgradOn : IntegrableOn gradSurface K g.volume := hgradK
  exact
    (integrableOn_iff_integrable_of_support_subset
      (μ := g.volume) hgrad_support).1 hgradOn

/--
%%handwave
name:
  Compact \(L^2\)-class convergence gives representative convergence
statement:
  If smooth primitive classes converge in \(L^2(K)\) and a scalar function is
  a representative of the limiting \(L^2(K)\)-class, then the primitives
  converge to that scalar function in the \(L^2(K)\)-seminorm.
proof:
  Replace the limiting \(L^2\)-class by the class represented by the scalar
  function.  Mathlib's characterization of convergence in \(L^p\) as
  convergence of the \(L^p\)-norm of the difference gives the result.
-/
theorem
    greenSobolevH10SmoothCompactSupportCorePrimitive_tendsto_localL2_of_localLp_limit_ae_eq
    {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (U : ℕ → (greenSobolevH10SmoothCompactSupportCore g).Core)
    {K : Set X} (hK : IsCompact K)
    (fK : Lp ℝ 2 (g.volume.restrict K))
    (hlim :
      Filter.Tendsto
        (fun n : ℕ ↦
          (((greenSobolevH10SmoothCompactSupportCorePrimitive (U n)).memLp_restrict_compact
            (g := g) hK).toLp
              (greenSobolevH10SmoothCompactSupportCorePrimitive (U n)).toFun :
            Lp ℝ 2 (g.volume.restrict K)))
        Filter.atTop (𝓝 fK))
    {toFun : X → ℝ}
    (hmem : MemLp toFun 2 (g.volume.restrict K))
    (hae : toFun =ᵐ[g.volume.restrict K] fK) :
    TendstoInLocalL2OnSurface g.volume K
      (fun n : ℕ ↦
        (greenSobolevH10SmoothCompactSupportCorePrimitive (U n)).toFun)
      toFun := by
  let μK := g.volume.restrict K
  let F : ℕ → X → ℝ :=
    fun n : ℕ ↦
      (greenSobolevH10SmoothCompactSupportCorePrimitive (U n)).toFun
  have hseq_mem : ∀ n : ℕ, MemLp (F n) 2 μK := by
    intro n
    simpa [F, μK] using
      (greenSobolevH10SmoothCompactSupportCorePrimitive (U n)).memLp_restrict_compact
        (g := g) hK
  have htarget :
      fK = hmem.toLp toFun := by
    calc
      fK = (Lp.memLp fK).toLp (fK : X → ℝ) :=
        (Lp.toLp_coeFn fK (Lp.memLp fK)).symm
      _ = hmem.toLp toFun :=
        MemLp.toLp_congr (Lp.memLp fK) hmem hae.symm
  have hlim_toFun :
      Filter.Tendsto (fun n : ℕ ↦ (hseq_mem n).toLp (F n))
        Filter.atTop (𝓝 (hmem.toLp toFun)) := by
    simpa [F, μK, htarget] using hlim
  simpa [TendstoInLocalL2OnSurface, F, μK, Pi.sub_apply] using
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (f := F) (f_ℒp := hseq_mem) (f_lim := toFun) (f_lim_ℒp := hmem)).mp
      hlim_toFun

/--
%%handwave
name:
  Exhaustion representative from compact \(L^2\) limits
statement:
  Given compact-local \(L^2\)-limits of one smooth primitive sequence, an
  exhaustion representative is obtained by evaluating, at each point, the
  limit class on the first compact exhaustion piece containing that point.
proof:
  The first containing piece exists because the exhaustion covers the surface.
  Compatibility of the compact-local \(L^2\)-limits on nested pieces is a
  separate almost-everywhere gluing statement.
-/
noncomputable def
    greenSobolevH10SmoothCompactSupport_rieszRepresentativeExhaustionScalar
    {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (K : CompactExhaustion X)
    (U : ℕ → (greenSobolevH10SmoothCompactSupportCore g).Core)
    (hlocalLp :
      ∀ K₀ : Set X, (hK₀ : IsCompact K₀) →
        ∃ fK : Lp ℝ 2 (g.volume.restrict K₀),
          Filter.Tendsto
            (fun n : ℕ ↦
              (((greenSobolevH10SmoothCompactSupportCorePrimitive (U n)).memLp_restrict_compact
                (g := g) hK₀).toLp
                  (greenSobolevH10SmoothCompactSupportCorePrimitive (U n)).toFun :
                Lp ℝ 2 (g.volume.restrict K₀)))
            Filter.atTop (𝓝 fK)) :
    X → ℝ :=
  fun x : X ↦
    (Classical.choose
      (hlocalLp (K (K.find x)) (K.isCompact (K.find x)))) x

/--
%%handwave
name:
  Compact-local \(L^2\) limits are compatible under restriction
statement:
  If \(A\subset B\) are compact sets and the same smooth primitive sequence
  has \(L^2\)-limits on \(A\) and on \(B\), then the two limiting classes
  agree almost everywhere on \(A\).
proof:
  The \(L^2(B)\)-convergence implies \(L^2(A)\)-convergence after restricting
  the measure, because the \(L^2(A)\)-norm is bounded by the \(L^2(B)\)-norm.
  Thus the same sequence has two limits in the Hausdorff \(L^2(A)\) space,
  and uniqueness of limits identifies them.
-/
theorem
    greenSobolevH10SmoothCompactSupportCorePrimitive_localLp_limit_ae_eq_of_subset
    {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (U : ℕ → (greenSobolevH10SmoothCompactSupportCore g).Core)
    {A B : Set X} (hA : IsCompact A) (hB : IsCompact B) (hAB : A ⊆ B)
    (fA : Lp ℝ 2 (g.volume.restrict A))
    (hlimA :
      Filter.Tendsto
        (fun n : ℕ ↦
          (((greenSobolevH10SmoothCompactSupportCorePrimitive (U n)).memLp_restrict_compact
            (g := g) hA).toLp
              (greenSobolevH10SmoothCompactSupportCorePrimitive (U n)).toFun :
            Lp ℝ 2 (g.volume.restrict A)))
        Filter.atTop (𝓝 fA))
    (fB : Lp ℝ 2 (g.volume.restrict B))
    (hlimB :
      Filter.Tendsto
        (fun n : ℕ ↦
          (((greenSobolevH10SmoothCompactSupportCorePrimitive (U n)).memLp_restrict_compact
            (g := g) hB).toLp
              (greenSobolevH10SmoothCompactSupportCorePrimitive (U n)).toFun :
            Lp ℝ 2 (g.volume.restrict B)))
        Filter.atTop (𝓝 fB)) :
    (fA : X → ℝ) =ᵐ[g.volume.restrict A] (fB : X → ℝ) := by
  let μA := g.volume.restrict A
  let μB := g.volume.restrict B
  let F : ℕ → X → ℝ :=
    fun n : ℕ ↦
      (greenSobolevH10SmoothCompactSupportCorePrimitive (U n)).toFun
  have hmemA : ∀ n : ℕ, MemLp (F n) 2 μA := by
    intro n
    simpa [F, μA] using
      (greenSobolevH10SmoothCompactSupportCorePrimitive (U n)).memLp_restrict_compact
        (g := g) hA
  have hmemB : ∀ n : ℕ, MemLp (F n) 2 μB := by
    intro n
    simpa [F, μB] using
      (greenSobolevH10SmoothCompactSupportCorePrimitive (U n)).memLp_restrict_compact
        (g := g) hB
  have hμA_le_μB : μA ≤ μB := by
    exact Measure.restrict_mono hAB le_rfl
  have hfB_memA : MemLp (fB : X → ℝ) 2 μA :=
    (Lp.memLp fB).mono_measure hμA_le_μB
  have hlimB' :
      Filter.Tendsto (fun n : ℕ ↦ (hmemB n).toLp (F n))
        Filter.atTop (𝓝 ((Lp.memLp fB).toLp (fB : X → ℝ))) := by
    have hfB_toLp :
        (Lp.memLp fB).toLp (fB : X → ℝ) = fB :=
      Lp.toLp_coeFn fB (Lp.memLp fB)
    simpa [F, μB, hfB_toLp] using hlimB
  have hlimB_e :
      Filter.Tendsto
        (fun n : ℕ ↦ eLpNorm (F n - (fB : X → ℝ)) 2 μB)
        Filter.atTop (𝓝 0) := by
    simpa [F, μB, Pi.sub_apply] using
      (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
        (f := F) (f_ℒp := hmemB) (f_lim := (fB : X → ℝ))
        (f_lim_ℒp := Lp.memLp fB)).mp hlimB'
  have hlimB_A_e :
      Filter.Tendsto
        (fun n : ℕ ↦ eLpNorm (F n - (fB : X → ℝ)) 2 μA)
        Filter.atTop (𝓝 0) := by
    refine
      tendsto_of_tendsto_of_tendsto_of_le_of_le
        tendsto_const_nhds hlimB_e ?_ ?_
    · intro n
      exact bot_le
    · intro n
      exact eLpNorm_mono_measure (F n - (fB : X → ℝ)) hμA_le_μB
  have hlimB_A :
      Filter.Tendsto (fun n : ℕ ↦ (hmemA n).toLp (F n))
        Filter.atTop (𝓝 (hfB_memA.toLp (fB : X → ℝ))) := by
    exact
      (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
        (f := F) (f_ℒp := hmemA) (f_lim := (fB : X → ℝ))
        (f_lim_ℒp := hfB_memA)).mpr hlimB_A_e
  have hlimA' :
      Filter.Tendsto (fun n : ℕ ↦ (hmemA n).toLp (F n))
        Filter.atTop (𝓝 fA) := by
    simpa [F, μA] using hlimA
  have hLp_eq : fA = hfB_memA.toLp (fB : X → ℝ) :=
    tendsto_nhds_unique hlimA' hlimB_A
  have htoLp_eq :
      (Lp.memLp fA).toLp (fA : X → ℝ) =
        hfB_memA.toLp (fB : X → ℝ) := by
    simpa using hLp_eq
  exact
    (MemLp.toLp_eq_toLp_iff (Lp.memLp fA) hfB_memA).1 htoLp_eq

/--
%%handwave
name:
  Exhaustion representative agrees with compact \(L^2\) limits
statement:
  The scalar representative built from a compact exhaustion agrees almost
  everywhere on each compact set with the \(L^2\)-limit of the same primitive
  sequence on that compact set.
proof:
  Restrict the compact-local convergence on a larger exhaustion piece to the
  given compact set.  Both the restricted exhaustion limit and the compact
  limit are \(L^2\)-limits of the same primitive sequence, so uniqueness of
  limits in \(L^2\) gives equality of the two classes.  The pointwise
  exhaustion representative was chosen from those exhaustion-piece classes,
  hence it agrees almost everywhere with the compact limit.
-/
theorem
    greenSobolevH10SmoothCompactSupport_rieszRepresentativeExhaustionScalar_ae_eq_localLpLimit
    {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [SecondCountableTopology X] [ComplexOneManifold X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (K : CompactExhaustion X)
    (U : ℕ → (greenSobolevH10SmoothCompactSupportCore g).Core)
    (hlocalLp :
      ∀ K₀ : Set X, (hK₀ : IsCompact K₀) →
        ∃ fK : Lp ℝ 2 (g.volume.restrict K₀),
          Filter.Tendsto
            (fun n : ℕ ↦
              (((greenSobolevH10SmoothCompactSupportCorePrimitive (U n)).memLp_restrict_compact
                (g := g) hK₀).toLp
                  (greenSobolevH10SmoothCompactSupportCorePrimitive (U n)).toFun :
                Lp ℝ 2 (g.volume.restrict K₀)))
            Filter.atTop (𝓝 fK))
    {K₀ : Set X} (hK₀ : IsCompact K₀)
    (fK : Lp ℝ 2 (g.volume.restrict K₀))
    (_hlim :
      Filter.Tendsto
        (fun n : ℕ ↦
          (((greenSobolevH10SmoothCompactSupportCorePrimitive (U n)).memLp_restrict_compact
            (g := g) hK₀).toLp
              (greenSobolevH10SmoothCompactSupportCorePrimitive (U n)).toFun :
            Lp ℝ 2 (g.volume.restrict K₀)))
        Filter.atTop (𝓝 fK)) :
    greenSobolevH10SmoothCompactSupport_rieszRepresentativeExhaustionScalar
        K U hlocalLp =ᵐ[g.volume.restrict K₀] fK := by
  let μ := g.volume
  let scalar : X → ℝ :=
    greenSobolevH10SmoothCompactSupport_rieszRepresentativeExhaustionScalar
      K U hlocalLp
  let fE : (m : ℕ) → Lp ℝ 2 (g.volume.restrict (K m)) :=
    fun m ↦ Classical.choose (hlocalLp (K m) (K.isCompact m))
  have hlimE :
      ∀ m : ℕ,
        Filter.Tendsto
          (fun n : ℕ ↦
            (((greenSobolevH10SmoothCompactSupportCorePrimitive (U n)).memLp_restrict_compact
              (g := g) (K.isCompact m)).toLp
                (greenSobolevH10SmoothCompactSupportCorePrimitive (U n)).toFun :
              Lp ℝ 2 (g.volume.restrict (K m))))
          Filter.atTop (𝓝 (fE m)) := by
    intro m
    simpa [fE] using
      Classical.choose_spec (hlocalLp (K m) (K.isCompact m))
  rcases K.exists_superset_of_isCompact hK₀ with ⟨N, hK₀N⟩
  have hfK_fN :
      (fK : X → ℝ) =ᵐ[g.volume.restrict K₀] (fE N : X → ℝ) :=
    greenSobolevH10SmoothCompactSupportCorePrimitive_localLp_limit_ae_eq_of_subset
      U hK₀ (K.isCompact N) hK₀N fK _hlim (fE N) (hlimE N)
  have hpiece :
      ∀ m ∈ Finset.range (N + 1),
        ∀ᵐ x ∂g.volume.restrict K₀,
          K.find x = m → scalar x = (fE N : X → ℝ) x := by
    intro m hm
    have hmN : m ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have hfm_fN :
        (fE m : X → ℝ) =ᵐ[g.volume.restrict (K m)] (fE N : X → ℝ) :=
      greenSobolevH10SmoothCompactSupportCorePrimitive_localLp_limit_ae_eq_of_subset
        U (K.isCompact m) (K.isCompact N) (K.subset hmN)
        (fE m) (hlimE m) (fE N) (hlimE N)
    have hglobal :
        ∀ᵐ x ∂g.volume, x ∈ K m → (fE m : X → ℝ) x = (fE N : X → ℝ) x :=
      ae_imp_of_ae_restrict hfm_fN
    have hK₀_event :
        ∀ᵐ x ∂g.volume.restrict K₀,
          x ∈ K m → (fE m : X → ℝ) x = (fE N : X → ℝ) x :=
      ae_restrict_of_ae hglobal
    filter_upwards [hK₀_event] with x hx hfind
    have hxKm : x ∈ K m := by
      simpa [hfind] using K.mem_find x
    have hscalar_fm : scalar x = (fE m : X → ℝ) x := by
      subst m
      rfl
    exact hscalar_fm.trans (hx hxKm)
  have hall :
      ∀ᵐ x ∂g.volume.restrict K₀,
        ∀ m ∈ Finset.range (N + 1),
          K.find x = m → scalar x = (fE N : X → ℝ) x := by
    rw [Filter.eventually_all_finset]
    exact hpiece
  have hK₀_meas : MeasurableSet K₀ := hK₀.isClosed.measurableSet
  have hmemK₀ : ∀ᵐ x ∂g.volume.restrict K₀, x ∈ K₀ :=
    ae_restrict_mem hK₀_meas
  have hscalar_fN :
      scalar =ᵐ[g.volume.restrict K₀] (fE N : X → ℝ) := by
    filter_upwards [hall, hmemK₀] with x hxall hxK₀
    have hxN : K.find x ≤ N :=
      K.mem_iff_find_le.mp (hK₀N hxK₀)
    have hxrange : K.find x ∈ Finset.range (N + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hxN)
    exact hxall (K.find x) hxrange rfl
  exact hscalar_fN.trans hfK_fN.symm

/--
%%handwave
name:
  Compatible compact \(L^2\) limits give a scalar representative
statement:
  Suppose smooth compactly supported primitive approximants converge to a
  pure Riesz vector and have \(L^2\)-limits on every compact subset.  Then
  those compact-local limits can be chosen compatibly and represented by a
  single scalar function on the surface.
proof:
  Use a countable compact exhaustion of the surface.  The \(L^2\)-limits on
  nested exhaustion pieces agree after restriction because they are limits of
  the same smooth primitive sequence.  Choose representatives on the
  exhaustion pieces and modify them on null sets so that the representatives
  agree on overlaps.  The resulting pointwise glued function has the required
  compact-local \(L^2\) convergence, local square-integrability, and the
  original completion and differential convergence properties.
-/
theorem
    greenSobolevH10SmoothCompactSupport_rieszRepresentative_scalarRepresentative_of_core_localLp_limits
    {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [SecondCountableTopology X] [ComplexOneManifold X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    {source : (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ}
    (U : ℕ → (greenSobolevH10SmoothCompactSupportCore g).Core)
    (hU :
      Filter.Tendsto
        (fun n : ℕ ↦
          (greenSobolevH10SmoothCompactSupportCore g).toCompletion (U n))
        Filter.atTop
        (𝓝 (greenSobolevH10SmoothCompactSupportRieszVector source)))
    (hlocalLp :
      ∀ K : Set X, (hK : IsCompact K) →
        ∃ fK : Lp ℝ 2 (g.volume.restrict K),
          Filter.Tendsto
            (fun n : ℕ ↦
              (((greenSobolevH10SmoothCompactSupportCorePrimitive (U n)).memLp_restrict_compact
                (g := g) hK).toLp
                  (greenSobolevH10SmoothCompactSupportCorePrimitive (U n)).toFun :
                Lp ℝ 2 (g.volume.restrict K)))
            Filter.atTop (𝓝 fK))
    (hU_diff :
      Filter.Tendsto (fun n : ℕ ↦ (U n).1) Filter.atTop
        (𝓝
          (greenSobolevH10SmoothCompactSupportDifferentialClass
            (greenSobolevH10SmoothCompactSupportRieszVector source)))) :
    Nonempty
      (GreenSobolevH10SmoothCompactSupportRieszScalarRepresentativeData
        source) := by
  letI : SigmaCompactSpace X := inferInstance
  let K : CompactExhaustion X := CompactExhaustion.choice X
  let toFun : X → ℝ :=
    greenSobolevH10SmoothCompactSupport_rieszRepresentativeExhaustionScalar
      K U hlocalLp
  refine
    ⟨{ toFun := toFun
       approximants := U
       approximants_tendsto := hU
       primitive_tendsto_localL2 := ?_
       primitive_memLp_local := ?_
       differentialClass_tendsto := hU_diff }⟩
  · intro K₀ hK₀
    rcases hlocalLp K₀ hK₀ with ⟨fK, hlim⟩
    have hae :
        toFun =ᵐ[g.volume.restrict K₀] fK := by
      simpa [toFun] using
        greenSobolevH10SmoothCompactSupport_rieszRepresentativeExhaustionScalar_ae_eq_localLpLimit
          K U hlocalLp hK₀ fK hlim
    have hmem : MemLp toFun 2 (g.volume.restrict K₀) :=
      MemLp.ae_eq hae.symm (Lp.memLp fK)
    exact
      greenSobolevH10SmoothCompactSupportCorePrimitive_tendsto_localL2_of_localLp_limit_ae_eq
        U hK₀ fK hlim hmem hae
  · intro K₀ hK₀
    rcases hlocalLp K₀ hK₀ with ⟨fK, hlim⟩
    have hae :
        toFun =ᵐ[g.volume.restrict K₀] fK := by
      simpa [toFun] using
        greenSobolevH10SmoothCompactSupport_rieszRepresentativeExhaustionScalar_ae_eq_localLpLimit
          K U hlocalLp hK₀ fK hlim
    exact MemLp.ae_eq hae.symm (Lp.memLp fK)

/--
%%handwave
name:
  Pure Riesz vectors have scalar compact-local \(L^2\) representatives
statement:
  Under pure Dirichlet capacity at infinity, the pure \(H^1_0\) Riesz vector
  has a scalar representative obtained as the compact-local \(L^2\) limit of
  smooth compactly supported primitive approximants.
proof:
  Choose smooth compactly supported approximants converging to the Riesz
  vector in the pure completion.  Pure capacity makes their primitives Cauchy
  in \(L^2\) on every compact set.  A countable compact exhaustion supplies
  compatible local \(L^2\) limits, which glue almost everywhere to a single
  function on the surface.  The glued function is square-integrable on every
  compact set, and the original approximants converge to it compact-locally.
-/
theorem greenSobolevH10SmoothCompactSupport_rieszRepresentative_exists_scalarRepresentative
    {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [SecondCountableTopology X] [ComplexOneManifold X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (hcap : HasPureDirichletCapacityAtInfinity g)
    (source : (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ) :
    Nonempty
      (GreenSobolevH10SmoothCompactSupportRieszScalarRepresentativeData
        source) := by
  rcases
      greenSobolevH10SmoothCompactSupport_rieszRepresentative_exists_core_sequence_with_localLp_limits
        hcap source with
    ⟨U, hU, hlocalLp, hU_diff⟩
  exact
    greenSobolevH10SmoothCompactSupport_rieszRepresentative_scalarRepresentative_of_core_localLp_limits
      U hU hlocalLp hU_diff

/--
%%handwave
name:
  Differential pairings converge for a scalar Riesz representative
statement:
  For a fixed compactly supported coordinate test function and tangent direction,
  the coordinate pairings of the smooth approximating differentials converge to
  the coordinate pairing of the chosen Riesz differential.
proof:
  The approximating differentials converge to the chosen Riesz differential in
  the intrinsic \(L^2\)-section quotient.  The fixed coordinate test defines a
  continuous linear \(L^2\)-pairing, so the corresponding coordinate integrals
  converge.
-/
theorem
    greenSobolevH10SmoothCompactSupport_rieszRepresentative_differentialPairing_tendsto
    {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [SecondCountableTopology X] [ComplexOneManifold X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    {source : (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ}
    (scalar :
      GreenSobolevH10SmoothCompactSupportRieszScalarRepresentativeData
        source)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    (φ : SmoothCompactlySupportedCoordinateFunction
      (surfaceChartRegion e (Set.univ : Set X))) (v : ℂ) :
    Integrable
        (fun z ↦
          greenSobolevH10SmoothCompactSupportRieszGradient source (e.symm z)
            (surfaceChartTangentMap e z v) * φ z)
        (MeasureTheory.volume.restrict
          (surfaceChartRegion e (Set.univ : Set X))) ∧
      Filter.Tendsto
        (fun n : ℕ ↦
          ∫ z in surfaceChartRegion e (Set.univ : Set X),
            (greenSobolevH10SmoothCompactSupportCorePrimitive
                (scalar.approximants n)).gradient (e.symm z)
              (surfaceChartTangentMap e z v) * φ z ∂MeasureTheory.volume)
        Filter.atTop
        (𝓝 (∫ z in surfaceChartRegion e (Set.univ : Set X),
          greenSobolevH10SmoothCompactSupportRieszGradient source (e.symm z)
            (surfaceChartTangentMap e z v) * φ z ∂MeasureTheory.volume)) := by
  letI : IsManifold SurfaceRealModel 1 X := inferInstance
  letI : NormedAddCommGroup (GreenDifferentialL2Intrinsic g) :=
    greenDifferentialL2Intrinsic_normedAddCommGroup g
  let hμ : SmoothPositiveMeasureOnManifold (I := SurfaceRealModel) g.volume :=
    { finite_on_compact :=
        (BackgroundSurfaceMetricOnSurface.volume_smooth_positive g).finite_on_compact
      chart_density :=
        (BackgroundSurfaceMetricOnSurface.volume_smooth_positive g).chart_density }
  let ψ : SmoothCompactlySupportedManifoldCoordinateFunction
      (manifoldChartRegion e (Set.univ : Set X)) :=
    { toFun := φ.toFun
      smooth := φ.smooth
      support_subset := by
        simpa [manifoldChartRegion, surfaceChartRegion] using φ.support_subset
      compact_support := φ.compact_support }
  let duSeq : ℕ → SquareIntegrableSurfaceDifferentialField
      (X := X) (E := ℝ) g.metric g.volume :=
    fun n ↦
      { toSection :=
          SurfaceDifferentialField.ofCoordinateField
            (greenSobolevH10SmoothCompactSupportCorePrimitive
              (scalar.approximants n)).gradient
        memL2 :=
          greenSobolevH10SmoothCompactSupportCorePrimitive_memL2
            (scalar.approximants n) }
  let uR : GreenSobolevH10SmoothCompactSupport g :=
    greenSobolevH10SmoothCompactSupportRieszVector source
  let duLim : SquareIntegrableSurfaceDifferentialField
      (X := X) (E := ℝ) g.metric g.volume :=
    greenSobolevH10SmoothCompactSupportDifferentialRep uR
  let duLimClass : GreenDifferentialL2Intrinsic g :=
    greenSobolevH10SmoothCompactSupportDifferentialClass uR
  have hduLim_eq :
      (Quotient.mk
        (SquareIntegrableSurfaceDifferentialField.aeSetoid
          (X := X) (E := ℝ) (g := g.metric) (μ := g.volume)) duLim :
        GreenDifferentialL2Intrinsic g) =
        duLimClass := by
    simpa [duLim, duLimClass, uR] using
      greenSobolevH10SmoothCompactSupportDifferentialRep_class_eq uR
  rcases
      manifoldDifferentialCoordinateTestPairing_tendsto_of_tendsto_l2_sections
        (I := SurfaceRealModel) (X := X) (E := ℝ)
        (ι := ℕ) (l := Filter.atTop)
        g.metric.toManifoldMetric g.volume hμ
        (du := duSeq) (duLim := duLim) (duLimClass := duLimClass)
        hduLim_eq
        (by
          have hpoint : ∀ n : ℕ,
              (Quotient.mk
                (SquareIntegrableSurfaceDifferentialField.aeSetoid
                  (X := X) (E := ℝ) (g := g.metric) (μ := g.volume)) (duSeq n) :
                GreenDifferentialL2Intrinsic g) =
                (scalar.approximants n).1 := by
            intro n
            simpa [duSeq, greenSmoothDifferentialClass] using
              greenSobolevH10SmoothCompactSupportCorePrimitive_class_eq
                (scalar.approximants n)
          exact
            Filter.Tendsto.congr'
              (Filter.Eventually.of_forall fun n ↦ (hpoint n).symm)
              scalar.differentialClass_tendsto)
        e he ψ v with
    ⟨hlim_int, htendsto⟩
  constructor
  · simpa [ψ, duLim, uR, greenSobolevH10SmoothCompactSupportRieszGradient,
      SurfaceDifferentialField.toCoordinateField, ManifoldDifferentialField.evalChart,
      manifoldChartRegion, surfaceChartRegion, smul_eq_mul, mul_comm] using hlim_int
  · simpa [ψ, duSeq, duLim, uR, greenSobolevH10SmoothCompactSupportRieszGradient,
      SurfaceDifferentialField.toCoordinateField, SurfaceDifferentialField.ofCoordinateField,
      ManifoldDifferentialField.evalChart, manifoldChartRegion, surfaceChartRegion,
      smul_eq_mul, mul_comm] using htendsto

/--
%%handwave
name:
  Scalar pairings converge for a scalar Riesz representative
statement:
  For a fixed compactly supported coordinate test function and tangent direction,
  compact-local \(L^2\) convergence of the smooth primitives implies convergence
  of the scalar coordinate pairings against the derivative of the test.
proof:
  The derivative of the test has compact support in the chart.  On that compact
  support, the smooth positive coordinate density of the surface measure is
  comparable with Lebesgue measure.  Thus compact-local \(L^2\) convergence on
  the surface gives \(L^2\) convergence of the coordinate pullbacks on the test
  support, and Cauchy--Schwarz gives convergence of the pairings.
-/
theorem
    greenSobolevH10SmoothCompactSupport_rieszRepresentative_scalarPairing_tendsto
    {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [SecondCountableTopology X] [ComplexOneManifold X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    {source : (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ}
    (scalar :
      GreenSobolevH10SmoothCompactSupportRieszScalarRepresentativeData
        source)
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
    (φ : SmoothCompactlySupportedCoordinateFunction
      (surfaceChartRegion e (Set.univ : Set X))) (v : ℂ) :
    Integrable
        (fun z ↦ scalar.toFun (e.symm z) *
          fderiv ℝ (φ : ℂ → ℝ) z v)
        (MeasureTheory.volume.restrict
          (surfaceChartRegion e (Set.univ : Set X))) ∧
      Filter.Tendsto
        (fun n : ℕ ↦
          ∫ z in surfaceChartRegion e (Set.univ : Set X),
            (greenSobolevH10SmoothCompactSupportCorePrimitive
                (scalar.approximants n)).toFun (e.symm z) *
              fderiv ℝ (φ : ℂ → ℝ) z v ∂MeasureTheory.volume)
        Filter.atTop
        (𝓝 (∫ z in surfaceChartRegion e (Set.univ : Set X),
          scalar.toFun (e.symm z) *
            fderiv ℝ (φ : ℂ → ℝ) z v ∂MeasureTheory.volume)) := by
  classical
  let μ : Measure X := g.volume
  let ψ : ℂ → ℝ := fun z ↦ fderiv ℝ (φ : ℂ → ℝ) z v
  let K : Set X := e.symm '' tsupport ψ
  have hψ_support : tsupport ψ ⊆ surfaceChartRegion e (Set.univ : Set X) := by
    simpa [ψ] using
      (tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := (φ : ℂ → ℝ)) v).trans
        φ.support_subset
  have hψ_target : tsupport ψ ⊆ e.target := by
    intro z hz
    have hzΩ : z ∈ surfaceChartRegion e (Set.univ : Set X) := hψ_support hz
    simpa [surfaceChartRegion] using hzΩ
  have hψ_compact : IsCompact (tsupport ψ) := by
    exact φ.compact_support.of_isClosed_subset (isClosed_tsupport ψ)
      (by
        simpa [ψ] using
          tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := (φ : ℂ → ℝ)) v)
  have hK_compact : IsCompact K := by
    dsimp [K]
    exact hψ_compact.image_of_continuousOn
      (e.continuousOn_symm.mono hψ_target)
  have hK_meas : MeasurableSet K := hK_compact.measurableSet
  let F : ℕ → X → ℝ :=
    fun n ↦
      (greenSobolevH10SmoothCompactSupportCorePrimitive
        (scalar.approximants n)).toFun
  let uSeqFun : ℕ → X → ℝ := fun n ↦ K.indicator (F n)
  let uLimFun : X → ℝ := K.indicator scalar.toFun
  have hF_memK : ∀ n : ℕ, MemLp (F n) 2 (μ.restrict K) := by
    intro n
    simpa [F, μ] using
      (greenSobolevH10SmoothCompactSupportCorePrimitive
        (scalar.approximants n)).memLp_restrict_compact
          (g := g) hK_compact
  have hLim_memK : MemLp scalar.toFun 2 (μ.restrict K) := by
    simpa [μ] using scalar.primitive_memLp_local K hK_compact
  have hSeq_indicator_mem : ∀ n : ℕ, MemLp (uSeqFun n) 2 μ := by
    intro n
    exact
      (memLp_indicator_iff_restrict
        (f := F n) (p := (2 : ℝ≥0∞)) (μ := μ) hK_meas).2
        (hF_memK n)
  have hLim_indicator_mem : MemLp uLimFun 2 μ :=
    (memLp_indicator_iff_restrict
      (f := scalar.toFun) (p := (2 : ℝ≥0∞)) (μ := μ) hK_meas).2
      hLim_memK
  let uSeq : ℕ → Lp ℝ 2 μ :=
    fun n ↦ (hSeq_indicator_mem n).toLp (uSeqFun n)
  let uLim : Lp ℝ 2 μ := hLim_indicator_mem.toLp uLimFun
  have hindicator_sub : ∀ n : ℕ,
      (fun x : X ↦ uSeqFun n x - uLimFun x) =
        K.indicator (fun x : X ↦ F n x - scalar.toFun x) := by
    intro n
    funext x
    by_cases hx : x ∈ K
    · simp [uSeqFun, uLimFun, Set.indicator_of_mem hx]
    · simp [uSeqFun, uLimFun, Set.indicator_of_notMem hx]
  have hindicator_norm : ∀ n : ℕ,
      eLpNorm (fun x : X ↦ uSeqFun n x - uLimFun x) 2 μ =
        eLpNorm (fun x : X ↦ F n x - scalar.toFun x) 2 (μ.restrict K) := by
    intro n
    rw [hindicator_sub n]
    exact eLpNorm_indicator_eq_eLpNorm_restrict
      (f := fun x : X ↦ F n x - scalar.toFun x)
      (p := (2 : ℝ≥0∞)) (μ := μ) hK_meas
  have hu_tendsto : Filter.Tendsto uSeq Filter.atTop (𝓝 uLim) := by
    have hlocal :
        Filter.Tendsto
          (fun n : ℕ ↦ eLpNorm (fun x : X ↦ F n x - scalar.toFun x) 2
            (μ.restrict K))
          Filter.atTop (𝓝 0) := by
      simpa [TendstoInLocalL2OnSurface, F, μ] using
        scalar.primitive_tendsto_localL2 K hK_compact
    have hindicator_tendsto :
        Filter.Tendsto
          (fun n : ℕ ↦ eLpNorm (fun x : X ↦ uSeqFun n x - uLimFun x) 2 μ)
          Filter.atTop (𝓝 0) := by
      simpa [hindicator_norm] using hlocal
    have hLp :=
      (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
        (f := uSeqFun) (f_ℒp := hSeq_indicator_mem)
        (f_lim := uLimFun) (f_lim_ℒp := hLim_indicator_mem)).2
        hindicator_tendsto
    simpa [uSeq, uLim] using hLp
  have hμ :
      SmoothPositiveAreaMeasureOnSurface X μ := by
    simpa [μ] using BackgroundSurfaceMetricOnSurface.volume_smooth_positive g
  rcases coordinateScalarTestPairing_tendsto_of_tendsto_Lp
      μ hμ hu_tendsto e _he φ v with
    ⟨hLim_int_indicator, htendsto_indicator⟩
  have hSeq_ae : ∀ n : ℕ,
      (fun x : X ↦ uSeq n x) =ᵐ[μ] uSeqFun n := by
    intro n
    simpa [uSeq] using (hSeq_indicator_mem n).coeFn_toLp
  have hLim_ae : (fun x : X ↦ uLim x) =ᵐ[μ] uLimFun := by
    simpa [uLim] using hLim_indicator_mem.coeFn_toLp
  have hSeq_chart_eq : ∀ n : ℕ,
      (fun z : ℂ ↦ uSeq n (e.symm z) * ψ z) =ᵐ[
        MeasureTheory.volume.restrict (surfaceChartRegion e (Set.univ : Set X))]
        fun z ↦ F n (e.symm z) * ψ z := by
    intro n
    have hchart_target :
        (fun z : ℂ ↦ uSeq n (e.symm z)) =ᵐ[
          MeasureTheory.volume.restrict e.target]
          fun z ↦ uSeqFun n (e.symm z) :=
      smoothPositiveAreaMeasureOnSurface_chart_comp_symm_ae_eq μ hμ e _he
        (hSeq_ae n)
    have hchart :
        (fun z : ℂ ↦ uSeq n (e.symm z)) =ᵐ[
          MeasureTheory.volume.restrict
            (surfaceChartRegion e (Set.univ : Set X))]
          fun z ↦ uSeqFun n (e.symm z) := by
      have hΩ_eq : surfaceChartRegion e (Set.univ : Set X) = e.target := by
        ext z
        simp [surfaceChartRegion]
      simpa [hΩ_eq] using hchart_target
    filter_upwards [hchart] with z hz
    by_cases hzψ : z ∈ tsupport ψ
    · have hzK : e.symm z ∈ K := ⟨z, hzψ, rfl⟩
      simp [uSeqFun, Set.indicator_of_mem hzK, hz]
    · have hψ_zero : ψ z = 0 := image_eq_zero_of_notMem_tsupport hzψ
      simp [hψ_zero]
  have hLim_chart_eq :
      (fun z : ℂ ↦ uLim (e.symm z) * ψ z) =ᵐ[
        MeasureTheory.volume.restrict (surfaceChartRegion e (Set.univ : Set X))]
        fun z ↦ scalar.toFun (e.symm z) * ψ z := by
    have hchart_target :
        (fun z : ℂ ↦ uLim (e.symm z)) =ᵐ[
          MeasureTheory.volume.restrict e.target]
          fun z ↦ uLimFun (e.symm z) :=
      smoothPositiveAreaMeasureOnSurface_chart_comp_symm_ae_eq μ hμ e _he
        hLim_ae
    have hchart :
        (fun z : ℂ ↦ uLim (e.symm z)) =ᵐ[
          MeasureTheory.volume.restrict
            (surfaceChartRegion e (Set.univ : Set X))]
          fun z ↦ uLimFun (e.symm z) := by
      have hΩ_eq : surfaceChartRegion e (Set.univ : Set X) = e.target := by
        ext z
        simp [surfaceChartRegion]
      simpa [hΩ_eq] using hchart_target
    filter_upwards [hchart] with z hz
    by_cases hzψ : z ∈ tsupport ψ
    · have hzK : e.symm z ∈ K := ⟨z, hzψ, rfl⟩
      simp [uLimFun, Set.indicator_of_mem hzK, hz]
    · have hψ_zero : ψ z = 0 := image_eq_zero_of_notMem_tsupport hzψ
      simp [hψ_zero]
  constructor
  · simpa [ψ] using hLim_int_indicator.congr hLim_chart_eq
  · have hseq_integral_eq : ∀ n : ℕ,
        (∫ z in surfaceChartRegion e (Set.univ : Set X),
            uSeq n (e.symm z) * ψ z ∂MeasureTheory.volume) =
          ∫ z in surfaceChartRegion e (Set.univ : Set X),
            F n (e.symm z) * ψ z ∂MeasureTheory.volume := by
      intro n
      exact integral_congr_ae (hSeq_chart_eq n)
    have hlim_integral_eq :
        (∫ z in surfaceChartRegion e (Set.univ : Set X),
            uLim (e.symm z) * ψ z ∂MeasureTheory.volume) =
          ∫ z in surfaceChartRegion e (Set.univ : Set X),
            scalar.toFun (e.symm z) * ψ z ∂MeasureTheory.volume :=
      integral_congr_ae hLim_chart_eq
    have htendsto_original :
        Filter.Tendsto
          (fun n : ℕ ↦
            ∫ z in surfaceChartRegion e (Set.univ : Set X),
              F n (e.symm z) * ψ z ∂MeasureTheory.volume)
          Filter.atTop
          (𝓝 (∫ z in surfaceChartRegion e (Set.univ : Set X),
              scalar.toFun (e.symm z) * ψ z ∂MeasureTheory.volume)) := by
      have ht :=
        Filter.Tendsto.congr'
          (Filter.Eventually.of_forall hseq_integral_eq)
          htendsto_indicator
      simpa [ψ, hlim_integral_eq] using ht
    simpa [F, ψ] using htendsto_original

/--
%%handwave
name:
  Scalar Riesz representatives have the Riesz weak gradient
statement:
  A compact-local \(L^2\) scalar representative obtained from smooth
  compactly supported pure-core approximants has weak gradient equal to the
  chosen finite-energy Riesz differential.
proof:
  Test the weak-gradient identities for the smooth approximants against a
  fixed compactly supported coordinate test.  The scalar terms converge by
  compact-local \(L^2\) convergence, and the differential terms converge by
  convergence of the completed \(L^2\) differential classes.  Passing to the
  limit gives the distributional identity for the scalar representative.
-/
theorem
    greenSobolevH10SmoothCompactSupport_rieszRepresentative_weakGradient_of_scalarRepresentative
    {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [SecondCountableTopology X] [ComplexOneManifold X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    {source : (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ}
    (scalar :
      GreenSobolevH10SmoothCompactSupportRieszScalarRepresentativeData
        source) :
    IsWeakGradientOnRegion (Set.univ : Set X) scalar.toFun
      (greenSobolevH10SmoothCompactSupportRieszGradient source) := by
  intro e he φ v
  let Ω : Set ℂ := surfaceChartRegion e (Set.univ : Set X)
  let L : ℕ → ℝ :=
    fun n ↦
      ∫ z in Ω,
        (greenSobolevH10SmoothCompactSupportCorePrimitive
            (scalar.approximants n)).toFun (e.symm z) *
          fderiv ℝ (φ : ℂ → ℝ) z v ∂MeasureTheory.volume
  let R : ℕ → ℝ :=
    fun n ↦
      ∫ z in Ω,
        (greenSobolevH10SmoothCompactSupportCorePrimitive
            (scalar.approximants n)).gradient (e.symm z)
          (surfaceChartTangentMap e z v) * φ z ∂MeasureTheory.volume
  let Llim : ℝ :=
    ∫ z in Ω,
      scalar.toFun (e.symm z) *
        fderiv ℝ (φ : ℂ → ℝ) z v ∂MeasureTheory.volume
  let Rlim : ℝ :=
    ∫ z in Ω,
      greenSobolevH10SmoothCompactSupportRieszGradient source (e.symm z)
        (surfaceChartTangentMap e z v) * φ z ∂MeasureTheory.volume
  rcases
      greenSobolevH10SmoothCompactSupport_rieszRepresentative_scalarPairing_tendsto
        scalar e he φ v with
    ⟨hLlim_int, hL_tendsto⟩
  rcases
      greenSobolevH10SmoothCompactSupport_rieszRepresentative_differentialPairing_tendsto
        scalar e he φ v with
    ⟨hRlim_int, hR_tendsto⟩
  have hweak_eq_eventually : ∀ᶠ n in Filter.atTop, L n = -R n := by
    refine Filter.Eventually.of_forall ?_
    intro n
    let F := greenSobolevH10SmoothCompactSupportCorePrimitive
      (scalar.approximants n)
    have hweak :
        IsWeakGradientOnSurface g.volume F.toFun F.gradient :=
      SmoothCompactlySupportedGlobalSurfaceFunction.isWeakGradientOnSurface
        g.volume F
    simpa [L, R, Ω, F] using (hweak e he φ v).2.2
  have hnegR_tendsto_to_Llim :
      Filter.Tendsto (fun n : ℕ ↦ -R n) Filter.atTop (𝓝 Llim) := by
    exact Filter.Tendsto.congr' hweak_eq_eventually
      (by simpa [L, Llim, Ω] using hL_tendsto)
  have hnegR_tendsto_to_neg_Rlim :
      Filter.Tendsto (fun n : ℕ ↦ -R n) Filter.atTop (𝓝 (-Rlim)) := by
    have hR_tendsto' : Filter.Tendsto R Filter.atTop (𝓝 Rlim) := by
      simpa [R, Rlim, Ω] using hR_tendsto
    exact hR_tendsto'.neg
  have hlim_eq : Llim = -Rlim :=
    tendsto_nhds_unique hnegR_tendsto_to_Llim hnegR_tendsto_to_neg_Rlim
  exact ⟨by simpa [Llim, Ω] using hLlim_int,
    by simpa [Rlim, Ω] using hRlim_int,
    by simpa [Llim, Rlim, Ω] using hlim_eq⟩

/--
%%handwave
name:
  Chartwise \(L^2\) control transfers to compact surface sets
statement:
  Let \(\mu\) be a smooth positive measure, \(e\) a manifold chart, and
  \(K_0\subseteq e.source\) compact with \(K=e(K_0)\).  If
  \(f\circ e^{-1}\in L^2(K)\) for Lebesgue measure, then
  \(f\in L^2(K_0,\mu)\).
proof:
  On the compact chart image \(K\), the smooth density of the pushforward of
  \(\mu\) is bounded above by a finite constant.  This bounds the weighted
  \(L^2\)-integral by the assumed Lebesgue \(L^2\)-integral, and the chart
  pushforward identity transfers it back to \(K_0\).
-/
private theorem smoothPositiveMeasureOnManifold_memLp_on_compact_of_chartPullback_memLp
    {H X F : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace F] [ContinuousENorm F]
    {μ : Measure X} (hμ : SmoothPositiveMeasureOnManifold (I := I) μ)
    (e : OpenPartialHomeomorph X H) (he : e ∈ atlas H X)
    {K₀ : Set X} {K : Set H}
    (hK₀_compact : IsCompact K₀)
    (hK₀_source : K₀ ⊆ e.source)
    (hK_def : K = e '' K₀)
    {f : X → F}
    (hf : MemLp (fun z : H ↦ f (e.symm z)) 2
      (MeasureTheory.volume.restrict K)) :
    MemLp f 2 (μ.restrict K₀) := by
  classical
  have hK_target : K ⊆ e.target := by
    rw [hK_def]
    intro z hz
    rcases hz with ⟨x, hxK₀, rfl⟩
    exact e.map_source (hK₀_source hxK₀)
  have hK_compact : IsCompact K := by
    rw [hK_def]
    exact hK₀_compact.image_of_continuousOn
      (e.continuousOn.mono hK₀_source)
  have hK_meas : MeasurableSet K := hK_compact.measurableSet
  rcases hμ.chart_density e he with ⟨ρ, hρ_smooth, _hρ_pos, hmap⟩
  let ν : Measure H := MeasureTheory.volume.restrict e.target
  let δ : H → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (ρ z)
  have hρ_cont_K : ContinuousOn ρ K :=
    hρ_smooth.continuousOn.mono hK_target
  rcases hK_compact.exists_bound_of_continuousOn hρ_cont_K with
    ⟨M, hM⟩
  let R : ℝ := max M 1
  let c : ℝ≥0∞ := ENNReal.ofReal R
  have hR_pos : 0 < R := by
    dsimp [R]
    exact lt_of_lt_of_le zero_lt_one (le_max_right M 1)
  have hc_ne_zero : c ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hR_pos)
  have hc_ne_top : c ≠ (⊤ : ℝ≥0∞) := by
    simp [c]
  have hδ_upper : ∀ᵐ z ∂ν.restrict K, δ z ≤ c := by
    filter_upwards [ae_restrict_mem hK_meas] with z hzK
    have hρ_le_norm : ρ z ≤ ‖ρ z‖ := le_abs_self (ρ z)
    have hnorm_le_R : ‖ρ z‖ ≤ R := by
      exact (hM z hzK).trans (le_max_left M 1)
    exact ENNReal.ofReal_le_ofReal (hρ_le_norm.trans hnorm_le_R)
  have hweighted_eq :
      (ν.withDensity δ).restrict K =
        (Measure.map e (μ.restrict e.source)).restrict K := by
    simpa [ν, δ] using congrArg (fun m : Measure H ↦ m.restrict K) hmap.symm
  have hweighted_le :
      (ν.withDensity δ).restrict K ≤ c • ν.restrict K := by
    have hweighted_restrict :
        (ν.withDensity δ).restrict K = (ν.restrict K).withDensity δ :=
      restrict_withDensity hK_meas δ
    rw [hweighted_restrict, ← withDensity_const (μ := ν.restrict K) c]
    exact withDensity_mono hδ_upper
  have hνK_eq : ν.restrict K = MeasureTheory.volume.restrict K := by
    simpa [ν] using
      Measure.restrict_restrict_of_subset (μ := MeasureTheory.volume) hK_target
  let Fpull : H → F := fun z ↦ f (e.symm z)
  have hF_weighted :
      MemLp Fpull 2 ((ν.withDensity δ).restrict K) := by
    have hfν : MemLp Fpull 2 (ν.restrict K) := by
      simpa [Fpull, hνK_eq] using hf
    exact hfν.of_measure_le_smul hc_ne_top hweighted_le
  let μsK : Measure X := (μ.restrict e.source).restrict (e ⁻¹' K)
  have hpre_ae : e ⁻¹' K =ᵐ[μ.restrict e.source] K₀ := by
    filter_upwards [ae_restrict_mem e.open_source.measurableSet] with x hx_source
    apply propext
    constructor
    · intro hxK
      rw [hK_def] at hxK
      rcases hxK with ⟨y, hyK₀, hyx⟩
      have hy_source : y ∈ e.source := hK₀_source hyK₀
      have hy_eq_x : y = x := e.injOn hy_source hx_source hyx
      simpa [hy_eq_x] using hyK₀
    · intro hxK₀
      rw [hK_def]
      exact ⟨x, hxK₀, rfl⟩
  have hμsK_eq : μsK = μ.restrict K₀ := by
    calc
      μsK = (μ.restrict e.source).restrict K₀ := by
        simpa [μsK] using Measure.restrict_congr_set hpre_ae
      _ = μ.restrict K₀ := Measure.restrict_restrict_of_subset hK₀_source
  have he_aemeas_source : AEMeasurable e (μ.restrict e.source) :=
    openPartialHomeomorph_aemeasurable_restrict_source e μ
  have he_aemeas_μsK : AEMeasurable e μsK := by
    exact he_aemeas_source.mono_measure (by
      dsimp [μsK]
      exact Measure.restrict_le_self)
  have hmap_restrict :
      (Measure.map e (μ.restrict e.source)).restrict K = Measure.map e μsK := by
    dsimp [μsK]
    exact Measure.restrict_map_of_aemeasurable he_aemeas_source hK_meas
  have hF_map : MemLp Fpull 2 (Measure.map e μsK) := by
    simpa [Fpull, hweighted_eq, hmap_restrict] using hF_weighted
  have hcomp_mem : MemLp (fun x : X ↦ Fpull (e x)) 2 μsK :=
    hF_map.comp_of_map he_aemeas_μsK
  have hcomp_eq : (fun x : X ↦ Fpull (e x)) =ᵐ[μsK] f := by
    have hsource_ae : ∀ᵐ x ∂μsK, x ∈ e.source := by
      dsimp [μsK]
      exact ae_restrict_of_ae (ae_restrict_mem e.open_source.measurableSet)
    exact hsource_ae.mono fun x hx_source ↦ by
      simp [Fpull, e.left_inv hx_source]
  have hf_μsK : MemLp f 2 μsK :=
    (memLp_congr_ae hcomp_eq).1 hcomp_mem
  simpa [hμsK_eq] using hf_μsK

/--
%%handwave
name:
  Scalar representatives have the Riesz weak gradient
statement:
  A scalar representative obtained as the compact-local \(L^2\) limit of
  smooth pure-core approximants is locally \(W^{1,2}\), with weak gradient
  equal to the chosen finite-energy Riesz differential.
proof:
  On each compact chart piece, the smooth primitive approximants converge in
  \(L^2\) to the scalar representative, while their differentials converge in
  the ambient \(L^2\) differential space to the chosen Riesz differential.
  The closedness of the weak-gradient graph passes the distributional
  gradient identity to the limit, and the chart pieces cover the surface.
-/
theorem greenSobolevH10SmoothCompactSupport_rieszRepresentative_localSobolev_of_scalarRepresentative
    {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [SecondCountableTopology X] [ComplexOneManifold X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    {source : (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ}
    (scalar :
      GreenSobolevH10SmoothCompactSupportRieszScalarRepresentativeData
        source) :
    IsIntrinsicLocalSobolevH1OnSurface g Set.univ scalar.toFun
      (greenSobolevH10SmoothCompactSupportRieszGradient source) := by
  refine ⟨?_, ?_⟩
  · exact
      greenSobolevH10SmoothCompactSupport_rieszRepresentative_weakGradient_of_scalarRepresentative
        scalar
  · intro K hK _hKU
    refine ⟨scalar.primitive_memLp_local K hK, ?_⟩
    let u : GreenSobolevH10SmoothCompactSupport g :=
      greenSobolevH10SmoothCompactSupportRieszVector source
    let du : SquareIntegrableSurfaceDifferentialField
        (X := X) (E := ℝ) g.metric g.volume :=
      greenSobolevH10SmoothCompactSupportDifferentialRep u
    have hdu_global :
        SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
          du.toField := by
      exact du.memHilbertSchmidtL2
    have hdu_restrict :
        SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric
          (g.volume.restrict K) du.toField := by
      exact
        ⟨hdu_global.1.mono_measure Measure.restrict_le_self,
          hdu_global.2.mono_measure Measure.restrict_le_self⟩
    simpa [u, du, greenSobolevH10SmoothCompactSupportRieszGradient,
      SurfaceCotangentField.ofCoordinateField_toCoordinateField] using
      hdu_restrict

/--
%%handwave
name:
  The exterior differential is a continuous cotangent-bundle section
statement:
  If \(f:X\to\mathbb R\) is smooth on a real smooth surface, then
  \[
    x\longmapsto (x,df_x)
  \]
  is continuous as a section of the surface cotangent bundle.
proof:
  Smoothness of \(f\) makes its manifold derivative a continuous order-zero
  bundle map in tangent coordinates.  Identify that derivative with the
  coordinate exterior differential and forget smoothness to obtain continuity.
-/
theorem surfaceExteriorDerivative_totalSpace_continuous
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X]
    {f : X → ℝ} (hf : ContMDiff SurfaceRealModel 𝓘(ℝ, ℝ) ∞ f) :
    Continuous
      (fun x : X ↦
        (Bundle.TotalSpace.mk' (ℂ →L[ℝ] ℝ) x
          (surfaceExteriorDerivative f x) :
            SurfaceDifferentialTotalSpace X ℝ)) := by
  have hsec :
      ContMDiff SurfaceRealModel
        (SurfaceRealModel.prod 𝓘(ℝ, ℂ →L[ℝ] ℝ)) 0
        (fun x : X ↦
          (Bundle.TotalSpace.mk' (ℂ →L[ℝ] ℝ) x
            (surfaceExteriorDerivative f x) :
              SurfaceDifferentialTotalSpace X ℝ)) := by
    intro x₀
    rw [contMDiffAt_hom_bundle]
    constructor
    · exact contMDiffAt_id
    · have hmf :
          ContMDiffAt SurfaceRealModel 𝓘(ℝ, ℂ →L[ℝ] ℝ) 0
            (inTangentCoordinates SurfaceRealModel 𝓘(ℝ, ℝ)
              (id : X → X) f
              (fun x : X ↦
                (mfderiv SurfaceRealModel 𝓘(ℝ, ℝ) f x : ℂ →L[ℝ] ℝ))
              x₀) x₀ := by
        exact (hf x₀).mfderiv_const (m := 0) (by norm_num)
      have hcoord :
          (inTangentCoordinates SurfaceRealModel 𝓘(ℝ, ℝ)
              (id : X → X) f
              (fun x : X ↦
                (mfderiv SurfaceRealModel 𝓘(ℝ, ℝ) f x : ℂ →L[ℝ] ℝ))
              x₀) =
            (fun x : X ↦
              ContinuousLinearMap.inCoordinates ℂ (TangentSpace SurfaceRealModel)
                ℝ (Bundle.Trivial X ℝ) x₀ x x₀ x
                (mfderiv SurfaceRealModel 𝓘(ℝ, ℝ) f x)) := by
        funext x
        ext v
        simp [inTangentCoordinates, ContinuousLinearMap.inCoordinates, SurfaceRealModel,
          TangentBundle.continuousLinearMapAt_model_space, ContinuousLinearMap.comp_apply]
        rfl
      simpa [surfaceExteriorDerivative, hcoord] using hmf
  exact hsec.continuous

/--
%%handwave
name:
  Chart-extended compactly supported tests have square-integrable differential
statement:
  Extending a compactly supported smooth coordinate test by zero through a
  surface chart gives a smooth compactly supported surface test whose
  classical differential is square-integrable for the background metric.
proof:
  The extension is smooth and has compact support contained in the chart
  source.  In the defining chart its derivative is the Euclidean derivative
  of the compactly supported coordinate test, and in other charts this is
  transported by smooth coordinate changes.  Compact support and smoothness
  give intrinsic square-integrability of the cotangent field.
-/
theorem smoothChartTestExtension_differential_memHilbertSchmidtL2
    {X : Type}
    [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    {Ω : Set ℂ}
    (η : SmoothCompactlySupportedManifoldCoordinateFunction Ω)
    (hΩ_target : Ω ⊆ e.target) :
    SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
      (SurfaceDifferentialField.ofCoordinateField
        (SmoothCompactlySupportedGlobalSurfaceFunction.ofChartTest
          e he η hΩ_target).gradient) := by
  let F :=
    SmoothCompactlySupportedGlobalSurfaceFunction.ofChartTest
      e he η hΩ_target
  let G :=
    manifoldDifferentialHilbertBundleGeometry
      (I := SurfaceRealModel) (X := X) (E := ℝ) g.metric.toManifoldMetric
  change HilbertBundleSectionMemL2 G g.volume
    (SurfaceDifferentialField.ofCoordinateField F.gradient)
  refine ⟨?_, ?_⟩
  · have hf_contMDiff : ContMDiff SurfaceRealModel 𝓘(ℝ, ℝ) ∞ F.toFun :=
      isSmoothOnSurface_univ_contMDiff F.smooth
    have hcont :
        Continuous
          (fun x : X ↦
            (Bundle.TotalSpace.mk' (ℂ →L[ℝ] ℝ) x
              ((SurfaceDifferentialField.ofCoordinateField F.gradient) x) :
                SurfaceDifferentialTotalSpace X ℝ)) := by
      simpa [F, SmoothCompactlySupportedGlobalSurfaceFunction.ofChartTest,
        SurfaceDifferentialField.ofCoordinateField] using
        surfaceExteriorDerivative_totalSpace_continuous hf_contMDiff
    simpa [HilbertBundleSectionOnSurface.toTotalSpace] using hcont.aemeasurable
  · let M :=
      manifoldDifferentialHilbertSchmidtContinuousRiemannianMetric
        (I := SurfaceRealModel) (X := X) (E := ℝ) g.metric.toManifoldMetric
    let ψ : X → ℝ := fun x ↦
      G.fiberNormSq x ((SurfaceDifferentialField.ofCoordinateField F.gradient) x)
    have hsec :
        Continuous
          (fun x : X ↦
            (Bundle.TotalSpace.mk' (ℂ →L[ℝ] ℝ) x
              ((SurfaceDifferentialField.ofCoordinateField F.gradient) x) :
                SurfaceDifferentialTotalSpace X ℝ)) := by
      have hf_contMDiff : ContMDiff SurfaceRealModel 𝓘(ℝ, ℝ) ∞ F.toFun :=
        isSmoothOnSurface_univ_contMDiff F.smooth
      simpa [F, SmoothCompactlySupportedGlobalSurfaceFunction.ofChartTest,
        SurfaceDifferentialField.ofCoordinateField] using
        surfaceExteriorDerivative_totalSpace_continuous hf_contMDiff
    have htot :
        Continuous
          (fun x : X ↦
            Bundle.TotalSpace.mk' ℝ (E := Bundle.Trivial X ℝ) x
              (M.inner x
                ((SurfaceDifferentialField.ofCoordinateField F.gradient) x)
                ((SurfaceDifferentialField.ofCoordinateField F.gradient) x))) := by
      exact M.continuous.clm_bundle_apply₂ hsec hsec
    have hsnd : Continuous (Bundle.TotalSpace.trivialSnd X ℝ) := by
      simpa [Bundle.TotalSpace.trivialSnd, Bundle.Trivial.homeomorphProd,
        Bundle.TotalSpace.toProd] using
        (continuous_snd.comp (Bundle.Trivial.homeomorphProd X ℝ).continuous)
    have hψ_cont : Continuous ψ := by
      have hcomp := hsnd.comp htot
      simpa [ψ, G, M, manifoldDifferentialHilbertBundleGeometry,
        manifoldDifferentialHilbertBundleGeometryOfMetric,
        Bundle.TotalSpace.trivialSnd, Bundle.Trivial.homeomorphProd,
        Bundle.TotalSpace.toProd] using hcomp
    have hψ_support : tsupport ψ ⊆ tsupport F.toFun := by
      intro x hxψ
      by_contra hxF
      have hzero_ev : ψ =ᶠ[𝓝 x] fun _ : X ↦ (0 : ℝ) := by
        filter_upwards [(isClosed_tsupport F.toFun).isOpen_compl.mem_nhds hxF] with y hy
        have hdy :
            F.gradient y = 0 := by
          have hdiff :
              surfaceExteriorDerivative F.toFun y = 0 :=
            surfaceDifferential_eq_zero_of_notMem_tsupport
              (surfaceExteriorDerivative_isSurfaceDifferential F.smooth) hy
          simpa [F, SmoothCompactlySupportedGlobalSurfaceFunction.ofChartTest] using hdiff
        have hsection_y :
            (SurfaceDifferentialField.ofCoordinateField F.gradient) y = 0 := by
          simpa [SurfaceDifferentialField.ofCoordinateField] using hdy
        simp [ψ, G, manifoldDifferentialHilbertBundleGeometry,
          manifoldDifferentialHilbertBundleGeometryOfMetric, hsection_y]
      exact (notMem_tsupport_iff_eventuallyEq.mpr hzero_ev) hxψ
    have hψ_compact : IsCompact (tsupport ψ) :=
      F.compact_support.of_isClosed_subset (isClosed_tsupport ψ) hψ_support
    haveI : IsFiniteMeasureOnCompacts g.volume :=
      BackgroundSurfaceMetricOnSurface.volume_isFiniteMeasureOnCompacts g
    have hψ_int : Integrable ψ g.volume :=
      integrable_of_continuousOn_of_tsupport_subset_isCompact
        (s := Set.univ) hψ_cont.continuousOn isOpen_univ
        (by intro x hx; simp) hψ_compact
    simpa [ψ] using hψ_int

/--
%%handwave
name:
  Pullback measurability for chart volume
statement:
  A coordinate integrand that agrees on the chart image with the inverse-chart
  pullback of a surface integrand is measurable for the coordinate
  Riemannian volume measure, provided the surface integrand is measurable on
  the chart source.
proof:
  The coordinate volume is the pushforward of the restricted surface volume.
  The inverse chart is measurable for this pushforward measure, and the
  claimed pointwise agreement holds almost everywhere because the coordinate
  measure is supported on the chart image.
-/
theorem
    riemannianVolumeChartMeasure_aestronglyMeasurable_of_background_pointwise_symm
    {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X]
    {g : BackgroundSurfaceMetricOnSurface X}
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    {φ : X → ℝ} {ψ : ℂ → ℝ}
    (hφ :
      AEStronglyMeasurable φ (g.volume.restrict e.source))
    (hpoint : ∀ z ∈ e.target, ψ z = φ (e.symm z)) :
    AEStronglyMeasurable ψ (riemannianVolumeChartMeasure g.metric e) := by
  have hsymm :
      AEMeasurable e.symm (riemannianVolumeChartMeasure g.metric e) := by
    have h :=
      smoothPositiveAreaMeasureOnSurface_chart_symm_aemeasurable
        g.volume (BackgroundSurfaceMetricOnSurface.volume_smooth_positive g)
        e he
    have hmap :
        Measure.map e (g.volume.restrict e.source) =
          riemannianVolumeChartMeasure g.metric e :=
      (BackgroundSurfaceMetricOnSurface.volume_isRiemannian g).2 e he
    simpa [hmap] using h
  have hmap_symm :
      Measure.map e.symm (riemannianVolumeChartMeasure g.metric e) =
        g.volume.restrict e.source := by
    have h :=
      smoothPositiveAreaMeasureOnSurface_chart_map_symm_map
        g.volume (BackgroundSurfaceMetricOnSurface.volume_smooth_positive g)
        e he
    have hmap :
        Measure.map e (g.volume.restrict e.source) =
          riemannianVolumeChartMeasure g.metric e :=
      (BackgroundSurfaceMetricOnSurface.volume_isRiemannian g).2 e he
    simpa [hmap] using h
  have hφ_map :
      AEStronglyMeasurable φ
        (Measure.map e.symm (riemannianVolumeChartMeasure g.metric e)) := by
    simpa [hmap_symm] using hφ
  have hpull :
      AEStronglyMeasurable (fun z : ℂ ↦ φ (e.symm z))
        (riemannianVolumeChartMeasure g.metric e) :=
    hφ_map.comp_aemeasurable hsymm
  refine hpull.congr ?_
  have hac :
      riemannianVolumeChartMeasure g.metric e ≪
        MeasureTheory.volume.restrict e.target := by
    rw [riemannianVolumeChartMeasure]
    exact withDensity_absolutelyContinuous _ _
  filter_upwards [hac (ae_restrict_mem e.open_target.measurableSet)] with z hz
  exact (hpoint z hz).symm

/--
%%handwave
name:
  Chart source terms for compactly supported tests are integrable
statement:
  The density-weighted coordinate expression of the smooth compactly
  supported cutoff source against a compactly supported chart test is
  integrable on the corresponding chart region.
proof:
  The source is smooth on the surface, so its pullback by the inverse chart is
  continuous on the chart target.  Multiplying by the smooth coordinate test
  and the smooth positive volume density gives a continuous coordinate
  function whose support is contained in the compact support of the test.
-/
theorem logarithmicCutoffPoleModel_negative_chartTest_source_integrable
    {X : Type}
    [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [IsManifold SurfaceRealModel ∞ X]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    (φ : LogarithmicCutoffPoleModel g p)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    {U : Set X}
    (η : SmoothCompactlySupportedManifoldCoordinateFunction
      (surfaceChartRegion e U)) :
    Integrable
      (fun z ↦
        (fun x : X ↦ -φ.source x) (e.symm z) * η z *
          surfaceMetricVolumeDensityInChart g.metric e z)
      (MeasureTheory.volume.restrict
        (surfaceChartRegion e U)) := by
  let Ω : Set ℂ := surfaceChartRegion e U
  let ρ : ℂ → ℝ := surfaceMetricVolumeDensityInChart g.metric e
  let χ : ℂ → ℝ := fun z ↦ (-φ.source (e.symm z) * ρ z) * η z
  have hsource_cont : Continuous φ.source :=
    isSmoothOnSurface_univ_continuous φ.source_smooth
  have hsource_chart_cont :
      ContinuousOn (fun z : ℂ ↦ φ.source (e.symm z)) e.target :=
    hsource_cont.continuousOn.comp e.continuousOn_symm
      (fun _z _hz ↦ Set.mem_univ _)
  have hneg_source_chart_cont :
      ContinuousOn (fun z : ℂ ↦ -φ.source (e.symm z)) e.target :=
    hsource_chart_cont.neg
  have hρ_cont : ContinuousOn ρ e.target :=
    (surfaceMetricVolumeDensityInChart_smooth_positive X g.metric e he).1.continuousOn
  have hη_cont : ContinuousOn (η : ℂ → ℝ) e.target :=
    η.smooth.continuous.continuousOn
  have hχ_cont : ContinuousOn χ e.target := by
    exact (hneg_source_chart_cont.mul hρ_cont).mul hη_cont
  have hχ_support : tsupport χ ⊆ e.target := by
    have hη_target : tsupport (η : ℂ → ℝ) ⊆ e.target := by
      intro z hz
      exact (η.support_subset hz).1
    exact (tsupport_mul_subset_right (f := fun z : ℂ ↦ -φ.source (e.symm z) * ρ z)
      (g := (η : ℂ → ℝ))).trans hη_target
  have hχ_compact : IsCompact (tsupport χ) := by
    exact η.compact_support.of_isClosed_subset (isClosed_tsupport χ)
      (tsupport_mul_subset_right
        (f := fun z : ℂ ↦ -φ.source (e.symm z) * ρ z)
        (g := (η : ℂ → ℝ)))
  have hχ_int : Integrable χ MeasureTheory.volume :=
    integrable_of_continuousOn_of_tsupport_subset_isCompact
      (s := e.target) hχ_cont e.open_target hχ_support hχ_compact
  refine (hχ_int.restrict (s := Ω)).congr ?_
  filter_upwards [] with z
  ring

/--
%%handwave
name:
  Local correction smooth-test identities localize to chart tests
statement:
  If a local correction is locally \(W^{1,2}\) and satisfies the variational
  identity against every compactly supported smooth surface test, then the
  same identity holds for every compactly supported coordinate test after
  zero extension through the chart.
proof:
  Extend the coordinate test by zero to a smooth compactly supported surface
  test.  The global smooth-test identity gives the equality of surface
  integrals.  The chart-extension formulas identify the surface test and its
  differential with the coordinate test, and the Riemannian chart measure
  formula rewrites the surface integrals as coordinate integrals.
-/
theorem localCorrection_chartTest_source_identity_of_smoothTestPairing
    {X : Type}
    [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [SecondCountableTopology X] [ComplexOneManifold X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    (φ : LogarithmicCutoffPoleModel g p)
    (h : GreenSobolevH10LocalCorrection g)
    (hlocal :
      IsIntrinsicLocalSobolevH1OnSurface g (Set.univ : Set X)
        h.toFun h.weakGradient)
    (hsmooth_test_pairing :
      ∀ η : GreenSobolevH10SmoothTest g,
        greenLocalCorrectionSmoothTestDirichletPairing g h η =
          greenSmoothTestSourcePairing φ η)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    {U : Set X}
    (η : SmoothCompactlySupportedManifoldCoordinateFunction
      (surfaceChartRegion e U)) :
    Integrable
        (fun z ↦
          surfaceMetricWeakGradientCoordinatePairingInChart g e z
            (h.weakGradient (e.symm z))
            (fderiv ℝ (η : ℂ → ℝ) z) *
              surfaceMetricVolumeDensityInChart g.metric e z)
        (MeasureTheory.volume.restrict (surfaceChartRegion e U)) ∧
      Integrable
        (fun z ↦
          (fun x : X ↦ -φ.source x) (e.symm z) * η z *
            surfaceMetricVolumeDensityInChart g.metric e z)
        (MeasureTheory.volume.restrict (surfaceChartRegion e U)) ∧
        ∫ z in surfaceChartRegion e U,
            surfaceMetricWeakGradientCoordinatePairingInChart g e z
              (h.weakGradient (e.symm z))
              (fderiv ℝ (η : ℂ → ℝ) z) *
                surfaceMetricVolumeDensityInChart g.metric e z
            ∂MeasureTheory.volume =
          -∫ z in surfaceChartRegion e U,
            (fun x : X ↦ -φ.source x) (e.symm z) * η z *
              surfaceMetricVolumeDensityInChart g.metric e z
            ∂MeasureTheory.volume := by
  let Ω : Set ℂ := surfaceChartRegion e U
  let hΩ_target : Ω ⊆ e.target := fun _z hz ↦ hz.1
  have hdiff :
      SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
        (SurfaceDifferentialField.ofCoordinateField
          (SmoothCompactlySupportedGlobalSurfaceFunction.ofChartTest
            e he η hΩ_target).gradient) :=
    smoothChartTestExtension_differential_memHilbertSchmidtL2
      (g := g) e he η hΩ_target
  let test : GreenSobolevH10SmoothTest g :=
    GreenSobolevH10SmoothTest.ofChartTest
      (g := g) e he η hΩ_target hdiff
  let gradSurface : X → ℝ := fun x ↦
    g.gradientInner x (h.weakGradient x) (test.F.gradient x)
  let gradChart : ℂ → ℝ := fun z ↦
    surfaceMetricWeakGradientCoordinatePairingInChart g e z
      (h.weakGradient (e.symm z))
      (fderiv ℝ (η : ℂ → ℝ) z)
  let sourceChart : ℂ → ℝ := fun z ↦
    φ.source (e.symm z) * η z
  have hgrad_surface_int :
      Integrable gradSurface g.volume := by
    simpa [gradSurface, test] using
      greenLocalCorrectionSmoothChartTest_pairing_integrable_of_localSobolev
        (g := g) hlocal e he η hΩ_target hdiff
  have hglobal :
      ∫ x, gradSurface x ∂g.volume =
        greenSmoothTestSourcePairing φ test := by
    simpa [gradSurface, greenLocalCorrectionSmoothTestDirichletPairing] using
      hsmooth_test_pairing test
  have htest_support_source :
      tsupport test.F.toFun ⊆ e.source := by
    simpa [test, hΩ_target] using
      SmoothCompactlySupportedGlobalSurfaceFunction.ofChartTest_tsupport_subset_source
        e he η hΩ_target
  have hgrad_global_source :
      ∫ x, gradSurface x ∂g.volume =
        ∫ x in e.source, gradSurface x ∂g.volume := by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero
      (μ := g.volume) (s := e.source) (f := gradSurface) ?_).symm
    intro x hx_source
    have hxF : x ∉ tsupport test.F.toFun :=
      fun hx ↦ hx_source (htest_support_source hx)
    have hgrad_zero : test.F.gradient x = 0 := by
      have hdiff_zero :
          surfaceExteriorDerivative test.F.toFun x = 0 :=
        surfaceDifferential_eq_zero_of_notMem_tsupport
          (surfaceExteriorDerivative_isSurfaceDifferential test.F.smooth) hxF
      simpa [test, SmoothCompactlySupportedGlobalSurfaceFunction.ofChartTest] using
        hdiff_zero
    change gradSurface x = 0
    simp only [gradSurface, hgrad_zero]
    exact cotangentInner_zero_right_of_isMetricDual
      g.metric g.gradientInner
      (BackgroundSurfaceMetricOnSurface.gradientInner_isMetricDual g) x
      (h.weakGradient x)
  have hgrad_chart_point :
      ∀ z ∈ e.target, gradChart z = gradSurface (e.symm z) := by
    intro z hz
    have hpair :=
      smoothChartTestExtension_gradientInner_eq_weakGradientCoordinatePairing
        (g := g) e he η hΩ_target
        (h.weakGradient (e.symm z)) hz
    simpa [gradSurface, gradChart, test] using hpair.symm
  have hgrad_chart_aesm :
      AEStronglyMeasurable gradChart
        (riemannianVolumeChartMeasure g.metric e) :=
    riemannianVolumeChartMeasure_aestronglyMeasurable_of_background_pointwise_symm
      (g := g) e he hgrad_surface_int.restrict.aestronglyMeasurable
      hgrad_chart_point
  have hgrad_chart_measure_int :
      Integrable gradChart (riemannianVolumeChartMeasure g.metric e) := by
    refine riemannianVolume_source_integrable_chartMeasure_of_pointwise
      g.metric g.measureGeometry e he
      (surfaceChart_source_nullMeasurable_volume g.metric g.measureGeometry e he)
      (surfaceChart_aemeasurable_restrict_volume g.metric g.measureGeometry e he)
      hgrad_chart_aesm ?_ hgrad_surface_int.restrict
    intro x hx
    have hpair :=
      smoothChartTestExtension_gradientInner_eq_weakGradientCoordinatePairing
        (g := g) e he η hΩ_target
        (h.weakGradient x) (e.map_source hx)
    simpa [gradSurface, gradChart, test, e.left_inv hx] using hpair
  have hgrad_density_target_int :
      IntegrableOn
        (fun z : ℂ ↦
          gradChart z * surfaceMetricVolumeDensityInChart g.metric e z)
        e.target :=
    riemannianVolumeChartMeasure_integrableOn_density
      g.metric e he gradChart hgrad_chart_measure_int
  have hgrad_int_Ω :
      IntegrableOn
        (fun z : ℂ ↦
          gradChart z * surfaceMetricVolumeDensityInChart g.metric e z)
        Ω :=
    hgrad_density_target_int.mono_set hΩ_target
  have hgrad_source_chartMeasure :
      ∫ x in e.source, gradSurface x ∂g.volume =
        ∫ z, gradChart z ∂riemannianVolumeChartMeasure g.metric e := by
    refine riemannianVolume_source_integral_eq_chartMeasure_of_pointwise
      g.metric g.measureGeometry e he
      (surfaceChart_source_nullMeasurable_volume g.metric g.measureGeometry e he)
      (surfaceChart_aemeasurable_restrict_volume g.metric g.measureGeometry e he)
      hgrad_chart_aesm ?_
    intro x hx
    have hpair :=
      smoothChartTestExtension_gradientInner_eq_weakGradientCoordinatePairing
        (g := g) e he η hΩ_target
        (h.weakGradient x) (e.map_source hx)
    simpa [gradSurface, gradChart, test, e.left_inv hx] using hpair
  have hgrad_source_chart :
      ∫ x in e.source, gradSurface x ∂g.volume =
        ∫ z in e.target,
          gradChart z * surfaceMetricVolumeDensityInChart g.metric e z
            ∂MeasureTheory.volume := by
    calc
      ∫ x in e.source, gradSurface x ∂g.volume =
          ∫ z, gradChart z ∂riemannianVolumeChartMeasure g.metric e :=
          hgrad_source_chartMeasure
      _ = ∫ z in e.target,
          gradChart z * surfaceMetricVolumeDensityInChart g.metric e z
            ∂MeasureTheory.volume :=
            riemannianVolumeChartMeasure_integral_eq_setIntegral_density
              g.metric e he gradChart
  have hgrad_target_Ω :
      ∫ z in e.target,
          gradChart z * surfaceMetricVolumeDensityInChart g.metric e z
            ∂MeasureTheory.volume =
        ∫ z in Ω,
          gradChart z * surfaceMetricVolumeDensityInChart g.metric e z
            ∂MeasureTheory.volume := by
    refine setIntegral_eq_of_subset_of_forall_diff_eq_zero
      e.open_target.measurableSet hΩ_target ?_
    intro z hz
    have hz_notΩ : z ∉ Ω := hz.2
    have hzη : z ∉ tsupport (η : ℂ → ℝ) :=
      fun hzts ↦ hz_notΩ (η.support_subset hzts)
    have hdη_zero : fderiv ℝ (η : ℂ → ℝ) z = 0 :=
      fderiv_of_notMem_tsupport (𝕜 := ℝ) (f := (η : ℂ → ℝ)) hzη
    simp [gradChart, surfaceMetricWeakGradientCoordinatePairingInChart, hdη_zero]
  let sourceSurface : X → ℝ := fun x ↦
    φ.source x * test.F.toFun x
  have hsource_surface_cont : Continuous sourceSurface := by
    have hsource_cont : Continuous φ.source :=
      isSmoothOnSurface_univ_continuous φ.source_smooth
    have htest_cont : Continuous test.F.toFun :=
      isSmoothOnSurface_univ_continuous test.F.smooth
    exact hsource_cont.mul htest_cont
  have hsource_surface_support :
      tsupport sourceSurface ⊆ tsupport test.F.toFun := by
    exact tsupport_mul_subset_right
  have hsource_surface_compact : IsCompact (tsupport sourceSurface) :=
    test.F.compact_support.of_isClosed_subset
      (isClosed_tsupport sourceSurface) hsource_surface_support
  haveI : IsFiniteMeasureOnCompacts g.volume :=
    BackgroundSurfaceMetricOnSurface.volume_isFiniteMeasureOnCompacts g
  have hsource_surface_int : Integrable sourceSurface g.volume :=
    integrable_of_continuousOn_of_tsupport_subset_isCompact
      (s := Set.univ) hsource_surface_cont.continuousOn isOpen_univ
      (by intro x hx; simp) hsource_surface_compact
  have hsource_global_source :
      ∫ x, sourceSurface x ∂g.volume =
        ∫ x in e.source, sourceSurface x ∂g.volume := by
    exact integral_eq_setIntegral_of_tsupport_subset
      (μ := g.volume) (s := e.source)
      (hsource_surface_support.trans htest_support_source)
  have hsource_chart_point :
      ∀ z ∈ e.target, sourceChart z = sourceSurface (e.symm z) := by
    intro z hz
    have hsource :=
      smoothChartTestExtension_sourcePairing_eq_chartSourcePairing
        e he η hΩ_target φ.source hz
    simpa [sourceSurface, sourceChart, test] using hsource.symm
  have hsource_chart_aesm :
      AEStronglyMeasurable sourceChart
        (riemannianVolumeChartMeasure g.metric e) :=
    riemannianVolumeChartMeasure_aestronglyMeasurable_of_background_pointwise_symm
      (g := g) e he hsource_surface_int.restrict.aestronglyMeasurable
      hsource_chart_point
  have hsource_source_chartMeasure :
      ∫ x in e.source, sourceSurface x ∂g.volume =
        ∫ z, sourceChart z ∂riemannianVolumeChartMeasure g.metric e := by
    refine riemannianVolume_source_integral_eq_chartMeasure_of_pointwise
      g.metric g.measureGeometry e he
      (surfaceChart_source_nullMeasurable_volume g.metric g.measureGeometry e he)
      (surfaceChart_aemeasurable_restrict_volume g.metric g.measureGeometry e he)
      hsource_chart_aesm ?_
    intro x hx
    have hsource :=
      smoothChartTestExtension_sourcePairing_eq_chartSourcePairing
        e he η hΩ_target φ.source (e.map_source hx)
    simpa [sourceSurface, sourceChart, test, e.left_inv hx] using hsource
  have hsource_source_chart :
      ∫ x in e.source, sourceSurface x ∂g.volume =
        ∫ z in e.target,
          sourceChart z * surfaceMetricVolumeDensityInChart g.metric e z
            ∂MeasureTheory.volume := by
    calc
      ∫ x in e.source, sourceSurface x ∂g.volume =
          ∫ z, sourceChart z ∂riemannianVolumeChartMeasure g.metric e :=
          hsource_source_chartMeasure
      _ = ∫ z in e.target,
          sourceChart z * surfaceMetricVolumeDensityInChart g.metric e z
            ∂MeasureTheory.volume :=
            riemannianVolumeChartMeasure_integral_eq_setIntegral_density
              g.metric e he sourceChart
  have hsource_target_Ω :
      ∫ z in e.target,
          sourceChart z * surfaceMetricVolumeDensityInChart g.metric e z
            ∂MeasureTheory.volume =
        ∫ z in Ω,
          sourceChart z * surfaceMetricVolumeDensityInChart g.metric e z
            ∂MeasureTheory.volume := by
    refine setIntegral_eq_of_subset_of_forall_diff_eq_zero
      e.open_target.measurableSet hΩ_target ?_
    intro z hz
    have hz_notΩ : z ∉ Ω := hz.2
    have hzη : z ∉ tsupport (η : ℂ → ℝ) :=
      fun hzts ↦ hz_notΩ (η.support_subset hzts)
    have hη_zero : η z = 0 := image_eq_zero_of_notMem_tsupport hzη
    simp [sourceChart, hη_zero]
  have hgrad_chart_eq_global :
      ∫ z in Ω,
          gradChart z * surfaceMetricVolumeDensityInChart g.metric e z
            ∂MeasureTheory.volume =
        ∫ x, gradSurface x ∂g.volume := by
    calc
      ∫ z in Ω,
          gradChart z * surfaceMetricVolumeDensityInChart g.metric e z
            ∂MeasureTheory.volume =
          ∫ z in e.target,
            gradChart z * surfaceMetricVolumeDensityInChart g.metric e z
              ∂MeasureTheory.volume := hgrad_target_Ω.symm
      _ = ∫ x in e.source, gradSurface x ∂g.volume :=
          hgrad_source_chart.symm
      _ = ∫ x, gradSurface x ∂g.volume :=
          hgrad_global_source.symm
  have hsource_chart_eq_global :
      ∫ z in Ω,
          sourceChart z * surfaceMetricVolumeDensityInChart g.metric e z
            ∂MeasureTheory.volume =
        greenSmoothTestSourcePairing φ test := by
    calc
      ∫ z in Ω,
          sourceChart z * surfaceMetricVolumeDensityInChart g.metric e z
            ∂MeasureTheory.volume =
          ∫ z in e.target,
            sourceChart z * surfaceMetricVolumeDensityInChart g.metric e z
              ∂MeasureTheory.volume := hsource_target_Ω.symm
      _ = ∫ x in e.source, sourceSurface x ∂g.volume :=
          hsource_source_chart.symm
      _ = ∫ x, sourceSurface x ∂g.volume :=
          hsource_global_source.symm
      _ = greenSmoothTestSourcePairing φ test := by
          rfl
  have hidentity_pos :
      ∫ z in Ω,
          gradChart z * surfaceMetricVolumeDensityInChart g.metric e z
            ∂MeasureTheory.volume =
        ∫ z in Ω,
          sourceChart z * surfaceMetricVolumeDensityInChart g.metric e z
            ∂MeasureTheory.volume := by
    rw [hgrad_chart_eq_global, hsource_chart_eq_global, hglobal]
  have hnegative :
      -∫ z in Ω,
          (fun x : X ↦ -φ.source x) (e.symm z) * η z *
            surfaceMetricVolumeDensityInChart g.metric e z
          ∂MeasureTheory.volume =
        ∫ z in Ω,
          sourceChart z * surfaceMetricVolumeDensityInChart g.metric e z
            ∂MeasureTheory.volume := by
    rw [← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [] with z
    simp [sourceChart]
  constructor
  · simpa [Ω, gradChart] using hgrad_int_Ω
  · exact
      ⟨logarithmicCutoffPoleModel_negative_chartTest_source_integrable
          φ e he η,
        by
          calc
            ∫ z in surfaceChartRegion e U,
                surfaceMetricWeakGradientCoordinatePairingInChart g e z
                  (h.weakGradient (e.symm z))
                  (fderiv ℝ (η : ℂ → ℝ) z) *
                    surfaceMetricVolumeDensityInChart g.metric e z
                ∂MeasureTheory.volume =
                ∫ z in Ω,
                  sourceChart z * surfaceMetricVolumeDensityInChart g.metric e z
                    ∂MeasureTheory.volume := by
                  simpa [Ω, gradChart] using hidentity_pos
            _ =
                -∫ z in surfaceChartRegion e U,
                  (fun x : X ↦ -φ.source x) (e.symm z) * η z *
                    surfaceMetricVolumeDensityInChart g.metric e z
                  ∂MeasureTheory.volume := by
                  simpa [Ω] using hnegative.symm⟩

/--
%%handwave
name:
  Riesz gradient chart identity for punctured tests
statement:
  For an admissible zero-extended punctured chart test, the Riesz Euler
  identity localizes to the density-weighted coordinate identity between the
  Riesz gradient pairing and the negative cutoff source.
proof:
  Apply the global Riesz Euler identity to the zero-extended test.  The
  pointwise chart-extension formulas identify the test value and differential
  in the chart.  The compact support of the chart test localizes the surface
  integral to the chart region, and the Riemannian volume formula supplies the
  coordinate density.
-/
theorem
    greenSobolevH10SmoothCompactSupport_rieszRepresentative_chartTest_gradient_source_identity_of_memL2
    {X : Type}
    [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [SecondCountableTopology X] [ComplexOneManifold X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    (φ : LogarithmicCutoffPoleModel g p)
    (source : (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ)
    (hsource_smooth_tests :
      ∀ η : GreenSobolevH10SmoothTest g,
        greenSobolevH10SmoothCompactSupportSource source η.toH10 =
          greenSmoothTestSourcePairing φ η)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    (η : SmoothCompactlySupportedManifoldCoordinateFunction
      (surfaceChartRegion e {x : X | x ≠ p}))
    (hdiff :
      SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
        (SurfaceDifferentialField.ofCoordinateField
          (SmoothCompactlySupportedGlobalSurfaceFunction.ofChartTest
            e he η (fun _z hz ↦ hz.1)).gradient)) :
    Integrable
        (fun z ↦
          surfaceMetricWeakGradientCoordinatePairingInChart g e z
            (greenSobolevH10SmoothCompactSupportRieszGradient source
              (e.symm z))
            (fderiv ℝ (η : ℂ → ℝ) z) *
              surfaceMetricVolumeDensityInChart g.metric e z)
        (MeasureTheory.volume.restrict
          (surfaceChartRegion e {x : X | x ≠ p})) ∧
        ∫ z in surfaceChartRegion e {x : X | x ≠ p},
            surfaceMetricWeakGradientCoordinatePairingInChart g e z
              (greenSobolevH10SmoothCompactSupportRieszGradient source
                (e.symm z))
              (fderiv ℝ (η : ℂ → ℝ) z) *
                surfaceMetricVolumeDensityInChart g.metric e z
            ∂MeasureTheory.volume =
          -∫ z in surfaceChartRegion e {x : X | x ≠ p},
            (fun x : X ↦ -φ.source x) (e.symm z) * η z *
              surfaceMetricVolumeDensityInChart g.metric e z
            ∂MeasureTheory.volume := by
  let Ω : Set ℂ := surfaceChartRegion e {x : X | x ≠ p}
  let hΩ_target : Ω ⊆ e.target := fun _z hz ↦ hz.1
  let test : GreenSobolevH10SmoothTest g :=
    GreenSobolevH10SmoothTest.ofChartTest
      (g := g) e he η hΩ_target hdiff
  let gradSurface : X → ℝ := fun x ↦
    g.gradientInner x
      (greenSobolevH10SmoothCompactSupportRieszGradient source x)
      (test.F.gradient x)
  let gradChart : ℂ → ℝ := fun z ↦
    surfaceMetricWeakGradientCoordinatePairingInChart g e z
      (greenSobolevH10SmoothCompactSupportRieszGradient source (e.symm z))
      (fderiv ℝ (η : ℂ → ℝ) z)
  let sourceChart : ℂ → ℝ := fun z ↦
    φ.source (e.symm z) * η z
  have hgrad_surface_int :
      Integrable gradSurface g.volume :=
    greenSobolevH10SmoothCompactSupport_rieszRepresentative_smoothTest_pairing_integrable
      source test
  have hglobal :
      ∫ x, gradSurface x ∂g.volume =
        greenSmoothTestSourcePairing φ test := by
    simpa [gradSurface] using
      greenSobolevH10SmoothCompactSupport_rieszRepresentative_smoothTest_euler
        φ source hsource_smooth_tests test
  have htest_support_source :
      tsupport test.F.toFun ⊆ e.source := by
    simpa [test, hΩ_target] using
      SmoothCompactlySupportedGlobalSurfaceFunction.ofChartTest_tsupport_subset_source
        e he η hΩ_target
  have htest_support_punctured :
      tsupport test.F.toFun ⊆ {x : X | x ≠ p} := by
    simpa [test, hΩ_target, Ω, surfaceChartRegion] using
      SmoothCompactlySupportedGlobalSurfaceFunction.ofChartTest_tsupport_subset_set
        e he η (fun z hz ↦ hz)
  have hgrad_global_source :
      ∫ x, gradSurface x ∂g.volume =
        ∫ x in e.source, gradSurface x ∂g.volume := by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero
      (μ := g.volume) (s := e.source) (f := gradSurface) ?_).symm
    intro x hx_source
    have hxF : x ∉ tsupport test.F.toFun :=
      fun hx ↦ hx_source (htest_support_source hx)
    have hgrad_zero : test.F.gradient x = 0 := by
      have hdiff_zero :
          surfaceExteriorDerivative test.F.toFun x = 0 :=
        surfaceDifferential_eq_zero_of_notMem_tsupport
          (surfaceExteriorDerivative_isSurfaceDifferential test.F.smooth) hxF
      simpa [test, SmoothCompactlySupportedGlobalSurfaceFunction.ofChartTest] using
        hdiff_zero
    change gradSurface x = 0
    simp only [gradSurface, hgrad_zero]
    exact cotangentInner_zero_right_of_isMetricDual
      g.metric g.gradientInner
      (BackgroundSurfaceMetricOnSurface.gradientInner_isMetricDual g) x
      (greenSobolevH10SmoothCompactSupportRieszGradient source x)
  have hgrad_chart_point :
      ∀ z ∈ e.target, gradChart z = gradSurface (e.symm z) := by
    intro z hz
    have h :=
      smoothChartTestExtension_gradientInner_eq_weakGradientCoordinatePairing
        (g := g) e he η hΩ_target
        (greenSobolevH10SmoothCompactSupportRieszGradient source (e.symm z))
        hz
    simpa [gradSurface, gradChart, test] using h.symm
  have hgrad_chart_aesm :
      AEStronglyMeasurable gradChart
        (riemannianVolumeChartMeasure g.metric e) :=
    riemannianVolumeChartMeasure_aestronglyMeasurable_of_background_pointwise_symm
      (g := g) e he hgrad_surface_int.restrict.aestronglyMeasurable
      hgrad_chart_point
  have hgrad_chart_measure_int :
      Integrable gradChart (riemannianVolumeChartMeasure g.metric e) := by
    refine riemannianVolume_source_integrable_chartMeasure_of_pointwise
      g.metric g.measureGeometry e he
      (surfaceChart_source_nullMeasurable_volume g.metric g.measureGeometry e he)
      (surfaceChart_aemeasurable_restrict_volume g.metric g.measureGeometry e he)
      hgrad_chart_aesm ?_ hgrad_surface_int.restrict
    intro x hx
    have h :=
      smoothChartTestExtension_gradientInner_eq_weakGradientCoordinatePairing
        (g := g) e he η hΩ_target
        (greenSobolevH10SmoothCompactSupportRieszGradient source x)
        (e.map_source hx)
    simpa [gradSurface, gradChart, test, e.left_inv hx] using h
  have hgrad_density_target_int :
      IntegrableOn
        (fun z : ℂ ↦
          gradChart z * surfaceMetricVolumeDensityInChart g.metric e z)
        e.target :=
    riemannianVolumeChartMeasure_integrableOn_density
      g.metric e he gradChart hgrad_chart_measure_int
  have hgrad_int_Ω :
      IntegrableOn
        (fun z : ℂ ↦
          gradChart z * surfaceMetricVolumeDensityInChart g.metric e z)
        Ω :=
    hgrad_density_target_int.mono_set hΩ_target
  have hgrad_source_chartMeasure :
      ∫ x in e.source, gradSurface x ∂g.volume =
        ∫ z, gradChart z ∂riemannianVolumeChartMeasure g.metric e := by
    refine riemannianVolume_source_integral_eq_chartMeasure_of_pointwise
      g.metric g.measureGeometry e he
      (surfaceChart_source_nullMeasurable_volume g.metric g.measureGeometry e he)
      (surfaceChart_aemeasurable_restrict_volume g.metric g.measureGeometry e he)
      hgrad_chart_aesm ?_
    intro x hx
    have h :=
      smoothChartTestExtension_gradientInner_eq_weakGradientCoordinatePairing
        (g := g) e he η hΩ_target
        (greenSobolevH10SmoothCompactSupportRieszGradient source x)
        (e.map_source hx)
    simpa [gradSurface, gradChart, test, e.left_inv hx] using h
  have hgrad_source_chart :
      ∫ x in e.source, gradSurface x ∂g.volume =
        ∫ z in e.target,
          gradChart z * surfaceMetricVolumeDensityInChart g.metric e z
            ∂MeasureTheory.volume := by
    calc
      ∫ x in e.source, gradSurface x ∂g.volume =
          ∫ z, gradChart z ∂riemannianVolumeChartMeasure g.metric e :=
          hgrad_source_chartMeasure
      _ = ∫ z in e.target,
          gradChart z * surfaceMetricVolumeDensityInChart g.metric e z
            ∂MeasureTheory.volume :=
            riemannianVolumeChartMeasure_integral_eq_setIntegral_density
              g.metric e he gradChart
  have hgrad_target_Ω :
      ∫ z in e.target,
          gradChart z * surfaceMetricVolumeDensityInChart g.metric e z
            ∂MeasureTheory.volume =
        ∫ z in Ω,
          gradChart z * surfaceMetricVolumeDensityInChart g.metric e z
            ∂MeasureTheory.volume := by
    refine setIntegral_eq_of_subset_of_forall_diff_eq_zero
      e.open_target.measurableSet hΩ_target ?_
    intro z hz
    have hz_notΩ : z ∉ Ω := hz.2
    have hzη : z ∉ tsupport (η : ℂ → ℝ) :=
      fun hzts ↦ hz_notΩ (η.support_subset hzts)
    have hdη_zero : fderiv ℝ (η : ℂ → ℝ) z = 0 :=
      fderiv_of_notMem_tsupport (𝕜 := ℝ) (f := (η : ℂ → ℝ)) hzη
    simp [gradChart, surfaceMetricWeakGradientCoordinatePairingInChart, hdη_zero]
  let sourceSurface : X → ℝ := fun x ↦
    φ.source x * test.F.toFun x
  have hsource_surface_cont : Continuous sourceSurface := by
    have hsource_cont : Continuous φ.source :=
      isSmoothOnSurface_univ_continuous φ.source_smooth
    have htest_cont : Continuous test.F.toFun :=
      isSmoothOnSurface_univ_continuous test.F.smooth
    exact hsource_cont.mul htest_cont
  have hsource_surface_support :
      tsupport sourceSurface ⊆ tsupport test.F.toFun := by
    exact tsupport_mul_subset_right
  have hsource_surface_compact : IsCompact (tsupport sourceSurface) :=
    test.F.compact_support.of_isClosed_subset
      (isClosed_tsupport sourceSurface) hsource_surface_support
  haveI : IsFiniteMeasureOnCompacts g.volume :=
    BackgroundSurfaceMetricOnSurface.volume_isFiniteMeasureOnCompacts g
  have hsource_surface_int : Integrable sourceSurface g.volume :=
    integrable_of_continuousOn_of_tsupport_subset_isCompact
      (s := Set.univ) hsource_surface_cont.continuousOn isOpen_univ
      (by intro x hx; simp) hsource_surface_compact
  have hsource_global_source :
      ∫ x, sourceSurface x ∂g.volume =
        ∫ x in e.source, sourceSurface x ∂g.volume := by
    exact integral_eq_setIntegral_of_tsupport_subset
      (μ := g.volume) (s := e.source)
      (hsource_surface_support.trans htest_support_source)
  have hsource_chart_point :
      ∀ z ∈ e.target, sourceChart z = sourceSurface (e.symm z) := by
    intro z hz
    have h :=
      smoothChartTestExtension_sourcePairing_eq_chartSourcePairing
        e he η hΩ_target φ.source hz
    simpa [sourceSurface, sourceChart, test] using h.symm
  have hsource_chart_aesm :
      AEStronglyMeasurable sourceChart
        (riemannianVolumeChartMeasure g.metric e) :=
    riemannianVolumeChartMeasure_aestronglyMeasurable_of_background_pointwise_symm
      (g := g) e he hsource_surface_int.restrict.aestronglyMeasurable
      hsource_chart_point
  have hsource_source_chartMeasure :
      ∫ x in e.source, sourceSurface x ∂g.volume =
        ∫ z, sourceChart z ∂riemannianVolumeChartMeasure g.metric e := by
    refine riemannianVolume_source_integral_eq_chartMeasure_of_pointwise
      g.metric g.measureGeometry e he
      (surfaceChart_source_nullMeasurable_volume g.metric g.measureGeometry e he)
      (surfaceChart_aemeasurable_restrict_volume g.metric g.measureGeometry e he)
      hsource_chart_aesm ?_
    intro x hx
    have h :=
      smoothChartTestExtension_sourcePairing_eq_chartSourcePairing
        e he η hΩ_target φ.source (e.map_source hx)
    simpa [sourceSurface, sourceChart, test, e.left_inv hx] using h
  have hsource_source_chart :
      ∫ x in e.source, sourceSurface x ∂g.volume =
        ∫ z in e.target,
          sourceChart z * surfaceMetricVolumeDensityInChart g.metric e z
            ∂MeasureTheory.volume := by
    calc
      ∫ x in e.source, sourceSurface x ∂g.volume =
          ∫ z, sourceChart z ∂riemannianVolumeChartMeasure g.metric e :=
          hsource_source_chartMeasure
      _ = ∫ z in e.target,
          sourceChart z * surfaceMetricVolumeDensityInChart g.metric e z
            ∂MeasureTheory.volume :=
            riemannianVolumeChartMeasure_integral_eq_setIntegral_density
              g.metric e he sourceChart
  have hsource_target_Ω :
      ∫ z in e.target,
          sourceChart z * surfaceMetricVolumeDensityInChart g.metric e z
            ∂MeasureTheory.volume =
        ∫ z in Ω,
          sourceChart z * surfaceMetricVolumeDensityInChart g.metric e z
            ∂MeasureTheory.volume := by
    refine setIntegral_eq_of_subset_of_forall_diff_eq_zero
      e.open_target.measurableSet hΩ_target ?_
    intro z hz
    have hz_notΩ : z ∉ Ω := hz.2
    have hzη : z ∉ tsupport (η : ℂ → ℝ) :=
      fun hzts ↦ hz_notΩ (η.support_subset hzts)
    have hη_zero : η z = 0 := image_eq_zero_of_notMem_tsupport hzη
    simp [sourceChart, hη_zero]
  have hgrad_chart_eq_global :
      ∫ z in Ω,
          gradChart z * surfaceMetricVolumeDensityInChart g.metric e z
            ∂MeasureTheory.volume =
        ∫ x, gradSurface x ∂g.volume := by
    calc
      ∫ z in Ω,
          gradChart z * surfaceMetricVolumeDensityInChart g.metric e z
            ∂MeasureTheory.volume =
          ∫ z in e.target,
            gradChart z * surfaceMetricVolumeDensityInChart g.metric e z
              ∂MeasureTheory.volume := hgrad_target_Ω.symm
      _ = ∫ x in e.source, gradSurface x ∂g.volume :=
          hgrad_source_chart.symm
      _ = ∫ x, gradSurface x ∂g.volume :=
          hgrad_global_source.symm
  have hsource_chart_eq_global :
      ∫ z in Ω,
          sourceChart z * surfaceMetricVolumeDensityInChart g.metric e z
            ∂MeasureTheory.volume =
        greenSmoothTestSourcePairing φ test := by
    calc
      ∫ z in Ω,
          sourceChart z * surfaceMetricVolumeDensityInChart g.metric e z
            ∂MeasureTheory.volume =
          ∫ z in e.target,
            sourceChart z * surfaceMetricVolumeDensityInChart g.metric e z
              ∂MeasureTheory.volume := hsource_target_Ω.symm
      _ = ∫ x in e.source, sourceSurface x ∂g.volume :=
          hsource_source_chart.symm
      _ = ∫ x, sourceSurface x ∂g.volume :=
          hsource_global_source.symm
      _ = greenSmoothTestSourcePairing φ test := by
          rfl
  have hidentity_pos :
      ∫ z in Ω,
          gradChart z * surfaceMetricVolumeDensityInChart g.metric e z
            ∂MeasureTheory.volume =
        ∫ z in Ω,
          sourceChart z * surfaceMetricVolumeDensityInChart g.metric e z
            ∂MeasureTheory.volume := by
    rw [hgrad_chart_eq_global, hsource_chart_eq_global, hglobal]
  have hnegative :
      -∫ z in Ω,
          (fun x : X ↦ -φ.source x) (e.symm z) * η z *
            surfaceMetricVolumeDensityInChart g.metric e z
          ∂MeasureTheory.volume =
        ∫ z in Ω,
          sourceChart z * surfaceMetricVolumeDensityInChart g.metric e z
            ∂MeasureTheory.volume := by
    rw [← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [] with z
    simp [sourceChart]
  constructor
  · simpa [Ω, gradChart] using hgrad_int_Ω
  · calc
      ∫ z in surfaceChartRegion e {x : X | x ≠ p},
          surfaceMetricWeakGradientCoordinatePairingInChart g e z
            (greenSobolevH10SmoothCompactSupportRieszGradient source
              (e.symm z))
            (fderiv ℝ (η : ℂ → ℝ) z) *
              surfaceMetricVolumeDensityInChart g.metric e z
          ∂MeasureTheory.volume =
          ∫ z in Ω,
            sourceChart z * surfaceMetricVolumeDensityInChart g.metric e z
              ∂MeasureTheory.volume := by
            simpa [Ω, gradChart] using hidentity_pos
      _ =
          -∫ z in surfaceChartRegion e {x : X | x ≠ p},
            (fun x : X ↦ -φ.source x) (e.symm z) * η z *
              surfaceMetricVolumeDensityInChart g.metric e z
            ∂MeasureTheory.volume := by
            simpa [Ω] using hnegative.symm

/--
%%handwave
name:
  The Riesz Euler identity localizes to an admissible chart test
statement:
  If the zero-extended coordinate test is an admissible smooth pure test,
  then the global Riesz Euler identity rewrites as the corresponding
  density-weighted coordinate identity on the punctured chart region.
proof:
  Apply the global Euler identity to the zero extension.  The pointwise
  chart-extension formulas identify both the test value and the gradient
  pairing on the chart.  Since the extended test has support inside the
  chart region, the surface integral equals the coordinate integral with the
  Riemannian density.
-/
theorem
    greenSobolevH10SmoothCompactSupport_rieszRepresentative_chartTest_source_identity_of_memL2
    {X : Type}
    [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [SecondCountableTopology X] [ComplexOneManifold X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    (φ : LogarithmicCutoffPoleModel g p)
    (source : (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ)
    (hsource_smooth_tests :
      ∀ η : GreenSobolevH10SmoothTest g,
        greenSobolevH10SmoothCompactSupportSource source η.toH10 =
          greenSmoothTestSourcePairing φ η)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    (η : SmoothCompactlySupportedManifoldCoordinateFunction
      (surfaceChartRegion e {x : X | x ≠ p}))
    (hdiff :
      SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
        (SurfaceDifferentialField.ofCoordinateField
          (SmoothCompactlySupportedGlobalSurfaceFunction.ofChartTest
            e he η (fun _z hz ↦ hz.1)).gradient)) :
    Integrable
        (fun z ↦
          surfaceMetricWeakGradientCoordinatePairingInChart g e z
            (greenSobolevH10SmoothCompactSupportRieszGradient source
              (e.symm z))
            (fderiv ℝ (η : ℂ → ℝ) z) *
              surfaceMetricVolumeDensityInChart g.metric e z)
        (MeasureTheory.volume.restrict
          (surfaceChartRegion e {x : X | x ≠ p})) ∧
      Integrable
        (fun z ↦
          (fun x : X ↦ -φ.source x) (e.symm z) * η z *
            surfaceMetricVolumeDensityInChart g.metric e z)
        (MeasureTheory.volume.restrict
          (surfaceChartRegion e {x : X | x ≠ p})) ∧
        ∫ z in surfaceChartRegion e {x : X | x ≠ p},
            surfaceMetricWeakGradientCoordinatePairingInChart g e z
              (greenSobolevH10SmoothCompactSupportRieszGradient source
                (e.symm z))
              (fderiv ℝ (η : ℂ → ℝ) z) *
                surfaceMetricVolumeDensityInChart g.metric e z
            ∂MeasureTheory.volume =
          -∫ z in surfaceChartRegion e {x : X | x ≠ p},
            (fun x : X ↦ -φ.source x) (e.symm z) * η z *
              surfaceMetricVolumeDensityInChart g.metric e z
            ∂MeasureTheory.volume := by
  rcases
      greenSobolevH10SmoothCompactSupport_rieszRepresentative_chartTest_gradient_source_identity_of_memL2
        φ source hsource_smooth_tests e he η hdiff with
    ⟨hgrad_int, hidentity⟩
  exact
    ⟨hgrad_int,
      logarithmicCutoffPoleModel_negative_chartTest_source_integrable φ e he η,
      hidentity⟩

/--
%%handwave
name:
  Riesz Euler identity localizes to punctured chart tests
statement:
  The Riesz Euler identity against compactly supported smooth surface tests
  localizes to every compactly supported coordinate test on the punctured
  surface, with the Riemannian volume density in the chart.
proof:
  Extend the coordinate test by zero to a compactly supported smooth surface
  test.  The pointwise chart-extension formulas identify its pullback and
  gradient pairing with the coordinate test and its Euclidean differential.
  Change variables between surface volume and the Riemannian chart measure,
  then use the smooth-test Euler identity.
-/
theorem greenSobolevH10SmoothCompactSupport_rieszRepresentative_punctured_chartTest_source_identity
    {X : Type}
    [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [SecondCountableTopology X] [ComplexOneManifold X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    (φ : LogarithmicCutoffPoleModel g p)
    (source : (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ)
    (hsource_smooth_tests :
      ∀ η : GreenSobolevH10SmoothTest g,
        greenSobolevH10SmoothCompactSupportSource source η.toH10 =
          greenSmoothTestSourcePairing φ η)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    (η : SmoothCompactlySupportedManifoldCoordinateFunction
      (surfaceChartRegion e {x : X | x ≠ p})) :
    Integrable
        (fun z ↦
          surfaceMetricWeakGradientCoordinatePairingInChart g e z
            (greenSobolevH10SmoothCompactSupportRieszGradient source
              (e.symm z))
            (fderiv ℝ (η : ℂ → ℝ) z) *
              surfaceMetricVolumeDensityInChart g.metric e z)
        (MeasureTheory.volume.restrict
          (surfaceChartRegion e {x : X | x ≠ p})) ∧
      Integrable
        (fun z ↦
          (fun x : X ↦ -φ.source x) (e.symm z) * η z *
            surfaceMetricVolumeDensityInChart g.metric e z)
        (MeasureTheory.volume.restrict
          (surfaceChartRegion e {x : X | x ≠ p})) ∧
        ∫ z in surfaceChartRegion e {x : X | x ≠ p},
            surfaceMetricWeakGradientCoordinatePairingInChart g e z
              (greenSobolevH10SmoothCompactSupportRieszGradient source
                (e.symm z))
              (fderiv ℝ (η : ℂ → ℝ) z) *
                surfaceMetricVolumeDensityInChart g.metric e z
            ∂MeasureTheory.volume =
          -∫ z in surfaceChartRegion e {x : X | x ≠ p},
            (fun x : X ↦ -φ.source x) (e.symm z) * η z *
              surfaceMetricVolumeDensityInChart g.metric e z
            ∂MeasureTheory.volume := by
  have hdiff :
      SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
        (SurfaceDifferentialField.ofCoordinateField
          (SmoothCompactlySupportedGlobalSurfaceFunction.ofChartTest
            e he η (fun _z hz ↦ hz.1)).gradient) :=
    smoothChartTestExtension_differential_memHilbertSchmidtL2
      (g := g) e he η (fun _z hz ↦ hz.1)
  exact
    greenSobolevH10SmoothCompactSupport_rieszRepresentative_chartTest_source_identity_of_memL2
      φ source hsource_smooth_tests e he η hdiff

/--
%%handwave
name:
  Scalar Riesz representatives solve the punctured weak equation
statement:
  If a scalar representative realizes the pure Riesz vector and the source
  functional agrees with the cutoff source on smooth tests, then the
  representative solves the opposite weak source equation away from the pole.
proof:
  The Riesz Euler identity holds against every smooth compactly supported
  surface test.  Tests supported away from the pole are admissible, and the
  local Sobolev representative has the same weak gradient as the Riesz
  differential.  Substituting this gradient into the Euler identity gives the
  weak equation with the opposite cutoff source on the punctured surface.
-/
theorem greenSobolevH10SmoothCompactSupport_rieszRepresentative_puncturedSource_of_scalarRepresentative
    {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [SecondCountableTopology X] [ComplexOneManifold X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    (φ : LogarithmicCutoffPoleModel g p)
    (source : (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ)
    (hsource_smooth_tests :
      ∀ η : GreenSobolevH10SmoothTest g,
        greenSobolevH10SmoothCompactSupportSource source η.toH10 =
          greenSmoothTestSourcePairing φ η)
    (scalar :
      GreenSobolevH10SmoothCompactSupportRieszScalarRepresentativeData
        source)
    (hlocal :
      IsIntrinsicLocalSobolevH1OnSurface g Set.univ scalar.toFun
        (greenSobolevH10SmoothCompactSupportRieszGradient source)) :
    IsWeakLaplaceBeltramiSourceOnSurface g {x : X | x ≠ p}
      scalar.toFun (fun x : X ↦ -φ.source x) := by
  refine ⟨?_, ?_⟩
  · simpa using (isOpen_ne (x := p) : IsOpen {x : X | x ≠ p})
  · refine ⟨greenSobolevH10SmoothCompactSupportRieszGradient source, ?_, ?_⟩
    · exact IsIntrinsicLocalSobolevH1OnSurface.mono_set hlocal
        (Set.subset_univ _)
    · intro e he η
      exact
        greenSobolevH10SmoothCompactSupport_rieszRepresentative_punctured_chartTest_source_identity
          φ source hsource_smooth_tests e he η

/--
%%handwave
name:
  Sobolev representatives solve the punctured weak equation
statement:
  If the Sobolev representative of the pure Riesz vector realizes the
  localized smooth-test Euler identity away from the pole, then it solves the
  opposite weak source equation on the punctured surface.
proof:
  This is the chart-localization step for the variational Euler identity:
  compactly supported coordinate tests away from the pole must be compared
  with smooth compactly supported surface tests.  Once that localization is
  available, the stored local Sobolev representative supplies the weak
  gradient and the localized identity gives the weak source equation.
-/
theorem greenSobolevH10SmoothCompactSupport_rieszRepresentative_puncturedSource_of_sobolevData
    {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [SecondCountableTopology X] [ComplexOneManifold X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    (φ : LogarithmicCutoffPoleModel g p)
    (source : (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ)
    (hsource_smooth_tests :
      ∀ η : GreenSobolevH10SmoothTest g,
        greenSobolevH10SmoothCompactSupportSource source η.toH10 =
          greenSmoothTestSourcePairing φ η)
    (hsobolev :
      GreenSobolevH10SmoothCompactSupportRieszRepresentativeSobolevData
        φ source) :
    IsWeakLaplaceBeltramiSourceOnSurface g {x : X | x ≠ p}
      hsobolev.toFun (fun x : X ↦ -φ.source x) := by
  refine ⟨?_, ?_⟩
  · simpa using (isOpen_ne (x := p) : IsOpen {x : X | x ≠ p})
  · refine ⟨greenSobolevH10SmoothCompactSupportRieszGradient source, ?_, ?_⟩
    · exact IsIntrinsicLocalSobolevH1OnSurface.mono_set
        hsobolev.localSobolev (Set.subset_univ _)
    · intro e he η
      exact
        greenSobolevH10SmoothCompactSupport_rieszRepresentative_punctured_chartTest_source_identity
          φ source hsource_smooth_tests e he η

/--
%%handwave
name:
  Pure Riesz vectors have local Sobolev representatives
statement:
  Under pure Dirichlet capacity at infinity, the Riesz representative of a
  compactly supported smooth source has a scalar local \(W^{1,2}\)
  representative whose weak gradient is the chosen \(L^2\) cotangent
  representative.
proof:
  Choose smooth compactly supported primitive approximants for the pure
  Riesz vector.  Pure capacity makes these primitives Cauchy in \(L^2\) on
  compact subsets; using a countable compact exhaustion, choose a compatible
  local \(L^2\) representative.  Closedness of weak derivatives identifies
  its weak gradient with the completed differential.
-/
theorem greenSobolevH10SmoothCompactSupport_rieszRepresentative_local_reconstruction
    {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [SecondCountableTopology X] [ComplexOneManifold X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (hcap : HasPureDirichletCapacityAtInfinity g)
    (source : (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ) :
    ∃ toFun : X → ℝ,
      IsIntrinsicLocalSobolevH1OnSurface g Set.univ toFun
        (greenSobolevH10SmoothCompactSupportRieszGradient source) := by
  rcases
      greenSobolevH10SmoothCompactSupport_rieszRepresentative_exists_scalarRepresentative
        hcap source with
    ⟨scalar⟩
  have hlocal :
      IsIntrinsicLocalSobolevH1OnSurface g Set.univ scalar.toFun
        (greenSobolevH10SmoothCompactSupportRieszGradient source) :=
    greenSobolevH10SmoothCompactSupport_rieszRepresentative_localSobolev_of_scalarRepresentative
      scalar
  exact ⟨scalar.toFun, hlocal⟩

/--
%%handwave
name:
  Pure capacity supplies honest Sobolev data for the Riesz vector
statement:
  For a logarithmic cutoff source satisfying the smooth-test source
  compatibility, positive pure Dirichlet capacity supplies a scalar local
  Sobolev representative of the pure Riesz vector whose weak gradient is the
  chosen Riesz differential.
proof:
  Choose smooth compactly supported primitive approximants for the pure
  Riesz vector.  Pure capacity makes them compact-locally Cauchy in \(L^2\),
  and closedness of weak derivatives identifies the local weak gradient of
  the limit with the chosen Riesz differential.
-/
theorem greenSobolevH10SmoothCompactSupport_rieszRepresentative_exists_sobolev_data
    {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [SecondCountableTopology X] [ComplexOneManifold X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    (φ : LogarithmicCutoffPoleModel g p)
    (hcap : HasPureDirichletCapacityAtInfinity g)
    (source : (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ) :
    Nonempty
      (GreenSobolevH10SmoothCompactSupportRieszRepresentativeSobolevData
        φ source) := by
  rcases
      greenSobolevH10SmoothCompactSupport_rieszRepresentative_exists_scalarRepresentative
        hcap source with
    ⟨scalar⟩
  have hlocal :
      IsIntrinsicLocalSobolevH1OnSurface g Set.univ scalar.toFun
        (greenSobolevH10SmoothCompactSupportRieszGradient source) :=
    greenSobolevH10SmoothCompactSupport_rieszRepresentative_localSobolev_of_scalarRepresentative
      scalar
  exact
    ⟨{ scalar := scalar
       toFun := scalar.toFun
       toFun_eq_scalar := rfl
       localSobolev := hlocal }⟩

/--
%%handwave
name:
  Chosen honest Sobolev data for the pure Riesz vector
statement:
  Choose the local Sobolev representative data supplied by the compact-local
  \(L^2\) construction for the pure Riesz vector.
-/
noncomputable def greenSobolevH10SmoothCompactSupport_rieszRepresentativeSobolevData
    {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [SecondCountableTopology X] [ComplexOneManifold X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    (φ : LogarithmicCutoffPoleModel g p)
    (hcap : HasPureDirichletCapacityAtInfinity g)
    (source : (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ) :
    GreenSobolevH10SmoothCompactSupportRieszRepresentativeSobolevData
      φ source :=
  Classical.choice
    (greenSobolevH10SmoothCompactSupport_rieszRepresentative_exists_sobolev_data
      φ hcap source)

/--
%%handwave
name:
  Pure Riesz vector has an honest local weak representative
statement:
  Given honest local Sobolev representative data for the pure \(H^1_0\)
  Riesz vector, the representative packages as a local finite-Dirichlet
  correction whose weak gradient is the chosen Riesz differential, whose
  smooth-test pairings are the Hilbert inner products, and which satisfies
  the opposite weak source equation on the punctured surface.
proof:
  Package the supplied scalar representative and chosen weak gradient into a
  local correction.  Finite Dirichlet energy and the smooth-test pairing
  identity follow from the completed differential representative; the local
  Sobolev and punctured weak-source facts are exactly the supplied data.
-/
theorem greenSobolevH10SmoothCompactSupport_rieszRepresentative_has_honest_local_correction
    {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    (φ : LogarithmicCutoffPoleModel g p)
    (source : (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ)
    (hsobolev :
      GreenSobolevH10SmoothCompactSupportRieszRepresentativeSobolevData
        φ source)
    (hpunctured :
      IsWeakLaplaceBeltramiSourceOnSurface g {x : X | x ≠ p}
        hsobolev.toFun (fun x : X ↦ -φ.source x)) :
    ∃ h : GreenSobolevH10LocalCorrection g,
      h.toFun = hsobolev.toFun ∧
        IsIntrinsicLocalSobolevH1OnSurface g (Set.univ : Set X)
          h.toFun h.weakGradient ∧
        IsWeakLaplaceBeltramiSourceOnSurface g {x : X | x ≠ p}
          h.toFun (fun x : X ↦ -φ.source x) ∧
        ∀ η : GreenSobolevH10SmoothTest g,
          greenLocalCorrectionSmoothTestDirichletPairing g h η =
            inner ℝ
              (greenSobolevH10RieszRepresentative
                ((greenSobolevH10SmoothCompactSupportCore g).extendSource source))
              η.toH10 := by
  let u : GreenSobolevH10SmoothCompactSupport g :=
    greenSobolevH10SmoothCompactSupportRieszVector source
  rcases
      greenSobolevH10SmoothCompactSupport_has_local_correction_of_local_sobolev_rep
        u (by
          simpa [u, greenSobolevH10SmoothCompactSupportRieszGradient,
            greenSobolevH10SmoothCompactSupportRieszVector]
            using hsobolev.localSobolev) with
    ⟨h, htoFun, hgrad, hpair⟩
  refine ⟨h, htoFun, ?_, ?_, ?_⟩
  · rw [htoFun, hgrad]
    simpa [u, greenSobolevH10SmoothCompactSupportRieszGradient,
      greenSobolevH10SmoothCompactSupportRieszVector]
      using hsobolev.localSobolev
  · rw [htoFun]
    exact hpunctured
  · intro η
    simpa [u, greenSobolevH10SmoothCompactSupportRieszVector] using hpair η

/--
%%handwave
name:
  Pure capacity gives local \(H^1_0\) source and decode data
statement:
  For a logarithmic cutoff pole model on a surface with positive pure
  Dirichlet capacity at infinity, the compactly supported source defines a
  continuous functional on the pure \(H^1_0\) core, and the Riesz
  representative has a finite-Dirichlet variational correction solving the
  weak equation against compactly supported smooth tests.
proof:
  Pure Dirichlet capacity controls compact local \(L^2\) norms of smooth
  primitives by their pure Dirichlet norm.  This makes the compactly
  supported source continuous on the smooth Dirichlet core.  The Riesz vector
  is then packaged through its completed differential representative.
-/
theorem logarithmicCutoffPoleModel_has_smooth_h10_local_weak_correction_data
    {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [SecondCountableTopology X] [ComplexOneManifold X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    (φ : LogarithmicCutoffPoleModel g p)
    (hcap : HasPureDirichletCapacityAtInfinity g) :
    Nonempty
      (Σ source :
        (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ,
        GreenSobolevH10SmoothCompactSupportLocalWeakCorrectionData
          φ source) := by
  let source := greenSmoothCoreSourceLinearMap φ hcap
  let hsobolev :
      GreenSobolevH10SmoothCompactSupportRieszRepresentativeSobolevData
        φ source :=
    greenSobolevH10SmoothCompactSupport_rieszRepresentativeSobolevData
      φ hcap source
  have hpunctured :
      IsWeakLaplaceBeltramiSourceOnSurface g {x : X | x ≠ p}
        hsobolev.toFun (fun x : X ↦ -φ.source x) :=
    greenSobolevH10SmoothCompactSupport_rieszRepresentative_puncturedSource_of_sobolevData
      φ source (greenSmoothCoreSourceLinearMap_toH10_smoothTest φ hcap)
      hsobolev
  rcases
      greenSobolevH10SmoothCompactSupport_rieszRepresentative_has_honest_local_correction
        φ source hsobolev hpunctured with
    ⟨h, htoFun, hlocal, hpunctured, hpair⟩
  refine ⟨⟨source, ?_⟩⟩
  exact
    { scalar := hsobolev.scalar
      correction := h
      correction_toFun_eq_scalar := by
        rw [htoFun, hsobolev.toFun_eq_scalar]
      localSobolev := hlocal
      punctured_opposite_source := hpunctured
      test := fun η ↦ η.toH10
      dirichlet_pairing_eq_inner := by
        intro η
        exact hpair η
      source_eq_source_pairing := by
        intro η
        exact greenSmoothCoreSourceLinearMap_toH10_smoothTest φ hcap η }

/--
%%handwave
name:
  Pure Dirichlet capacity gives a local weak Green correction
statement:
  For a logarithmic cutoff pole model on a surface with positive pure
  Dirichlet capacity at infinity, there is a local finite-Dirichlet weak
  Green correction.
proof:
  [Positive pure Dirichlet capacity supplies a continuous source and compatible local Riesz data](lean:JJMath.Uniformization.logarithmicCutoffPoleModel_has_smooth_h10_local_weak_correction_data). Choose those data and [decode them as a finite-Dirichlet local weak correction](lean:JJMath.Uniformization.exists_local_weak_green_correction_of_smooth_h10_riesz_decode).
-/
theorem exists_local_weak_green_correction_of_pure_dirichlet_capacity
    {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [SecondCountableTopology X] [ComplexOneManifold X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    (φ : LogarithmicCutoffPoleModel g p)
    (hcap : HasPureDirichletCapacityAtInfinity g) :
    ∃ h : GreenSobolevH10LocalCorrection g,
      IsLocalWeakGreenCorrection φ h := by
  rcases Classical.choice
      (logarithmicCutoffPoleModel_has_smooth_h10_local_weak_correction_data
        φ hcap) with
    ⟨source, hdecode⟩
  exact exists_local_weak_green_correction_of_smooth_h10_riesz_decode
    φ source hdecode

end PureDirichletH10WeakCorrectionDecode

end Uniformization

end JJMath
