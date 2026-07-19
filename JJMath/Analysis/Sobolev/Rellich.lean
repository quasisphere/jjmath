import JJMath.Analysis.Sobolev.Bundle
import JJMath.Analysis.Sobolev.Hilbert
import JJMath.Analysis.Sobolev.ACL
import Mathlib.Analysis.BoxIntegral.Partition.Measure
import Mathlib.Analysis.BoxIntegral.UnitPartition
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.Order.T5

/-!
# Rellich compactness for manifold Sobolev spaces

This file records local Rellich compactness, zero-gradient rigidity, and the
subsequence extraction principle for sequences with vanishing gradients.
-/

namespace JJMath

open MeasureTheory
open scoped Manifold Topology ENNReal NNReal ContDiff

namespace Uniformization

noncomputable section

/--
%%handwave
name:
  Local \(L^2\) seminorm for Hilbert-valued maps on manifolds
statement:
  The local \(L^2\) seminorm squared of a Hilbert-valued map on a set is the
  integral of the squared Hilbert norm over that set.
-/
def manifoldLocalValueL2SeminormSq {X E : Type} [MeasurableSpace X]
    [NormedAddCommGroup E]
    (μ : Measure X) (K : Set X) (u : X → E) : ℝ :=
  ∫ x in K, ‖u x‖ ^ 2 ∂μ

/--
%%handwave
name:
  Local differential seminorm for Hilbert-valued maps on manifolds
statement:
  The local differential seminorm squared on a set is the integral of the
  fiberwise Hilbert-Schmidt norm squared of the weak differential.
-/
def manifoldLocalDifferentialSeminormSq {H X E : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I : ModelWithCorners ℝ H H) [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold I 1 X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : SmoothRiemannianMetricOnManifold I X) (μ : Measure X)
    (K : Set X) (du : ManifoldDifferentialField I X E) : ℝ :=
  ∫ x in K,
    (manifoldDifferentialHilbertBundleGeometry (I := I) (X := X) (E := E) g).fiberNormSq
      x (du x) ∂μ

/--
%%handwave
name:
  Local \(W^{1,2}\) seminorm for Hilbert-valued maps on manifolds
statement:
  The local \(W^{1,2}\) seminorm squared is the sum of the local \(L^2\)
  seminorm squared of the map and the local Hilbert-Schmidt \(L^2\) seminorm
  squared of its weak differential.
-/
def manifoldLocalH1SeminormSq {H X E : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I : ModelWithCorners ℝ H H) [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold I 1 X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : SmoothRiemannianMetricOnManifold I X) (μ : Measure X)
    (K : Set X) (u : X → E) (du : ManifoldDifferentialField I X E) : ℝ :=
  manifoldLocalValueL2SeminormSq μ K u +
    manifoldLocalDifferentialSeminormSq I g μ K du

/--
%%handwave
name:
  Local Sobolev regularity for Hilbert-valued maps on manifolds
statement:
  A Hilbert-valued map is locally \(W^{1,2}\) on a manifold region, with a
  chosen weak differential, if the differential satisfies the chartwise weak
  derivative identities on that region and both the map and differential are
  square-integrable on every compact subset of the region.
-/
def IsLocalSobolevH1OnManifoldWithValues {H X E : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H]
    [MeasurableSpace X] [BorelSpace X] [IsManifold I 1 X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : SmoothRiemannianMetricOnManifold I X) (μ : Measure X)
    (U : Set X) (u : X → E) (du : ManifoldDifferentialField I X E) : Prop :=
  IsWeakDerivativeOnManifoldRegionBundle (I := I) U u du ∧
    ∀ K : Set X, IsCompact K → K ⊆ U →
      HilbertBundleSectionMemL2 (trivialHilbertBundleGeometry X E)
          (μ.restrict K) u ∧
        ManifoldDifferentialFieldMemHilbertSchmidtL2 (I := I) g
          (μ.restrict K) du

/--
%%handwave
name:
  Trivial square-integrable bundle sections are \(L^2\) maps
statement:
  A square-integrable section of the trivial Hilbert bundle with fiber \(E\)
  is an \(E\)-valued \(L^2\) map.
proof:
  The total-space representative is almost everywhere measurable.  Composing
  it with the continuous projection from the trivial bundle to its fiber gives
  almost everywhere measurability of the \(E\)-valued map; finite
  dimensionality of \(E\) upgrades this to almost everywhere strong
  measurability.  The fiberwise square norm in the trivial bundle is
  \(\|u(x)\|^2\), so the defining integrability condition is precisely the
  \(L^2\) integrability condition.
-/
theorem HilbertBundleSectionMemL2.memLp_trivial
    {X E : Type} [TopologicalSpace X] [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {μ : Measure X} {u : X → E}
    (hu : HilbertBundleSectionMemL2 (trivialHilbertBundleGeometry X E) μ u) :
    MemLp u 2 μ := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  have htotal :
      AEMeasurable
        (HilbertBundleSectionOnSurface.toTotalSpace
          (F := E) (V := Bundle.Trivial X E) u) μ :=
    hu.aemeasurable
  have hsnd : Continuous (Bundle.TotalSpace.trivialSnd X E) := by
    simpa [Bundle.TotalSpace.trivialSnd, Bundle.Trivial.homeomorphProd,
      Bundle.TotalSpace.toProd] using
      (continuous_snd.comp (Bundle.Trivial.homeomorphProd X E).continuous)
  have hu_aemeas : AEMeasurable u μ := by
    have hcomp :
        AEMeasurable
          (fun x : X ↦
            Bundle.TotalSpace.trivialSnd X E
              (HilbertBundleSectionOnSurface.toTotalSpace
                (F := E) (V := Bundle.Trivial X E) u x)) μ :=
      hsnd.measurable.comp_aemeasurable htotal
    simpa [HilbertBundleSectionOnSurface.toTotalSpace,
      Bundle.TotalSpace.trivialSnd, Bundle.Trivial.homeomorphProd,
      Bundle.TotalSpace.toProd] using hcomp
  have hu_aestr : AEStronglyMeasurable u μ :=
    hu_aemeas.aestronglyMeasurable
  have hintegrable :
      Integrable (fun x : X ↦ ‖u x‖ ^ 2) μ := by
    refine hu.integrable_normSq.congr ?_
    filter_upwards [] with x
    simp [trivialHilbertBundleGeometry]
  exact (memLp_two_iff_integrable_sq_norm hu_aestr).2 hintegrable

/--
%%handwave
name:
  Real-valued \(L^2\) maps are square-integrable trivial sections
statement:
  A real-valued \(L^2\) map is square-integrable as a section of the trivial
  real Hilbert bundle.
proof:
  The trivial bundle total space is \(X\times\mathbb R\).  Almost-everywhere
  measurability of the map gives almost-everywhere measurability of the
  section graph, and the fiber square norm is exactly \(|u|^2\).
-/
theorem trivial_real_hilbertBundleSectionMemL2_of_memLp
    {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} {u : X → ℝ}
    (hu : MemLp u 2 μ) :
    HilbertBundleSectionMemL2 (trivialHilbertBundleGeometry X ℝ) μ u := by
  refine ⟨?_, ?_⟩
  · let graph : X → X × ℝ := fun x ↦ (x, u x)
    have hgraph : AEMeasurable graph μ := by
      exact aemeasurable_id'.prodMk hu.aestronglyMeasurable.aemeasurable
    have hcomp :
        AEMeasurable
          ((Bundle.Trivial.homeomorphProd X ℝ).symm ∘ graph) μ :=
      (Bundle.Trivial.homeomorphProd X ℝ).symm.continuous.measurable.comp_aemeasurable hgraph
    refine hcomp.congr ?_
    filter_upwards [] with x
    rfl
  · have hintegrable :
        Integrable (fun x : X ↦ ‖u x‖ ^ 2) μ :=
      (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).1 hu
    refine hintegrable.congr ?_
    filter_upwards [] with x
    simp [trivialHilbertBundleGeometry]

/--
%%handwave
name:
  Bounded local Sobolev family on a manifold
statement:
  A sequence of Hilbert-valued local Sobolev maps is bounded in \(W^{1,2}\)
  on a set if the local \(W^{1,2}\) seminorms of the sequence on that set are
  uniformly bounded.
-/
def BoundedInLocalSobolevH1OnManifoldWithValues {H X E : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold I 1 X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : SmoothRiemannianMetricOnManifold I X) (μ : Measure X)
    (K : Set X) (u : ℕ → X → E)
    (du : ℕ → ManifoldDifferentialField I X E) : Prop :=
  ∃ C : ℝ, ∀ n : ℕ,
    manifoldLocalH1SeminormSq I g μ K (u n) (du n) ≤ C

/--
%%handwave
name:
  Local \(L^2\) convergence for Hilbert-valued maps on manifolds
statement:
  A sequence of Hilbert-valued maps converges locally in \(L^2\) on a set if
  the \(L^2\) seminorm of the difference tends to zero on that set.
-/
def TendstoInLocalL2OnManifoldWithValues {X E : Type} [MeasurableSpace X]
    [NormedAddCommGroup E]
    (μ : Measure X) (K : Set X) (uSeq : ℕ → X → E) (u : X → E) : Prop :=
  Filter.Tendsto
    (fun n : ℕ ↦ eLpNorm (fun x ↦ uSeq n x - u x) 2 (μ.restrict K))
    Filter.atTop (𝓝 0)

/--
%%handwave
name:
  Local \(L^2\) convergence restricts to smaller sets
statement:
  If a sequence converges in \(L^2\) on a set \(P\), then it also converges
  in \(L^2\) on every subset \(K\subset P\).
proof:
  The restricted measure on \(K\) is bounded above by the restricted measure
  on \(P\), so the \(L^2(K)\)-seminorm of the difference is bounded by its
  \(L^2(P)\)-seminorm.  Squeeze between this upper bound and zero.
-/
theorem TendstoInLocalL2OnManifoldWithValues.mono_set {X E : Type}
    [MeasurableSpace X] [NormedAddCommGroup E]
    {μ : Measure X} {K P : Set X} {uSeq : ℕ → X → E} {u : X → E}
    (hKP : K ⊆ P)
    (hlim : TendstoInLocalL2OnManifoldWithValues μ P uSeq u) :
    TendstoInLocalL2OnManifoldWithValues μ K uSeq u := by
  dsimp [TendstoInLocalL2OnManifoldWithValues] at hlim ⊢
  have hle :
      (fun n : ℕ ↦ eLpNorm (fun x ↦ uSeq n x - u x) 2 (μ.restrict K))
        ≤ᶠ[Filter.atTop]
      (fun n : ℕ ↦ eLpNorm (fun x ↦ uSeq n x - u x) 2 (μ.restrict P)) :=
    Filter.Eventually.of_forall fun n ↦
      eLpNorm_mono_measure (fun x ↦ uSeq n x - u x)
        (Measure.restrict_mono hKP le_rfl)
  have hnonneg :
      (fun _n : ℕ ↦ (0 : ℝ≥0∞)) ≤ᶠ[Filter.atTop]
        (fun n : ℕ ↦
          eLpNorm (fun x ↦ uSeq n x - u x) 2 (μ.restrict K)) :=
    Filter.Eventually.of_forall fun _n ↦ zero_le
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hlim hnonneg hle

/--
%%handwave
name:
  Local value \(L^2\) seminorm is nonnegative
statement:
  The local \(L^2\) seminorm squared of a Hilbert-valued map is nonnegative.
proof:
  The integrand is the square of the pointwise norm.
-/
theorem manifoldLocalValueL2SeminormSq_nonneg {X E : Type}
    [MeasurableSpace X] [NormedAddCommGroup E]
    (μ : Measure X) (K : Set X) (u : X → E) :
    0 ≤ manifoldLocalValueL2SeminormSq μ K u := by
  dsimp [manifoldLocalValueL2SeminormSq]
  exact integral_nonneg (fun x ↦ sq_nonneg ‖u x‖)

/--
%%handwave
name:
  Local differential seminorm is nonnegative
statement:
  The local Hilbert-Schmidt \(L^2\) seminorm squared of a weak differential is
  nonnegative.
proof:
  The fiber metric is positive definite, so its diagonal value is
  nonnegative at each point.
-/
theorem manifoldLocalDifferentialSeminormSq_nonneg {H X E : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I : ModelWithCorners ℝ H H) [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold I 1 X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : SmoothRiemannianMetricOnManifold I X) (μ : Measure X)
    (K : Set X) (du : ManifoldDifferentialField I X E) :
    0 ≤ manifoldLocalDifferentialSeminormSq I g μ K du := by
  let metric :=
    manifoldDifferentialHilbertSchmidtContinuousRiemannianMetric
      (I := I) (X := X) (E := E) g
  dsimp [manifoldLocalDifferentialSeminormSq,
    manifoldDifferentialHilbertBundleGeometry,
    manifoldDifferentialHilbertBundleGeometryOfMetric]
  exact integral_nonneg (fun x ↦ by
    by_cases hdu : du x = 0
    · simp [hdu]
    · exact (metric.pos x (du x) hdu).le)

/--
%%handwave
name:
  Zero extension of a differential field
statement:
  The zero extension of a differential field from a set \(Q\) is the field
  which agrees with the original field on \(Q\) and is zero outside \(Q\).
-/
noncomputable def manifoldDifferentialFieldZeroExtend {H X E : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I : ModelWithCorners ℝ H H) [TopologicalSpace X] [ChartedSpace H X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : Set X) (du : ManifoldDifferentialField I X E) :
    ManifoldDifferentialField I X E := by
  classical
  exact fun x ↦ if x ∈ Q then du x else 0

/--
%%handwave
name:
  Zero extension of an \(L^2\) differential field
statement:
  If a differential field is square-integrable on a measurable set \(Q\), then
  the field extended by zero outside \(Q\) is square-integrable on the whole
  manifold.
proof:
  The total-space section of the zero extension is the measurable piecewise
  section obtained by using the original field on \(Q\) and the zero section
  on \(Q^c\).  Its squared fiber norm is the corresponding piecewise
  function, whose integrability follows from the assumed \(L^2\)-integrability
  on \(Q\) and the trivial integrability of the zero section on \(Q^c\).
-/
theorem manifoldDifferentialFieldMemHilbertSchmidtL2_zero_extend_of_restrict
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold I 1 X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := I) X E)]
    [TopologicalSpace.PseudoMetrizableSpace
      (ManifoldDifferentialTotalSpace (I := I) X E)]
    {g : SmoothRiemannianMetricOnManifold I X} {μ : Measure X}
    {Q : Set X} (hQ_meas : MeasurableSet Q)
    {du : ManifoldDifferentialField I X E}
    (hduQ : ManifoldDifferentialFieldMemHilbertSchmidtL2 (I := I) g
      (μ.restrict Q) du) :
    ManifoldDifferentialFieldMemHilbertSchmidtL2 (I := I) g μ
      (manifoldDifferentialFieldZeroExtend I Q du) := by
  classical
  let G :=
    manifoldDifferentialHilbertBundleGeometry
      (I := I) (X := X) (E := E) g
  let metric :=
    manifoldDifferentialHilbertSchmidtContinuousRiemannianMetric
      (I := I) (X := X) (E := E) g
  letI : Bundle.RiemannianBundle
      (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E)) :=
    ⟨metric.toRiemannianMetric⟩
  letI (x : X) :
      NormedAddCommGroup (ManifoldDifferentialBundleFiber
        (I := I) (X := X) (E := E) x) :=
    manifoldDifferentialHilbertSchmidtNormedAddCommGroup
      (I := I) (X := X) (E := E) metric x
  letI (x : X) :
      InnerProductSpace ℝ (ManifoldDifferentialBundleFiber
        (I := I) (X := X) (E := E) x) :=
    manifoldDifferentialHilbertSchmidtInnerProductSpace
      (I := I) (X := X) (E := E) metric x
  let duExt : ManifoldDifferentialField I X E :=
    manifoldDifferentialFieldZeroExtend I Q du
  have htotal_ext_eq :
      HilbertBundleSectionOnSurface.toTotalSpace
          (F := H →L[ℝ] E) duExt =
        Q.piecewise
          (HilbertBundleSectionOnSurface.toTotalSpace
            (F := H →L[ℝ] E) du)
          (HilbertBundleSectionOnSurface.toTotalSpace
            (F := H →L[ℝ] E) (0 : ManifoldDifferentialField I X E)) := by
    funext x
    by_cases hx : x ∈ Q
    · simp [HilbertBundleSectionOnSurface.toTotalSpace, duExt, hx,
        manifoldDifferentialFieldZeroExtend]
    · simp [HilbertBundleSectionOnSurface.toTotalSpace, duExt, hx,
        manifoldDifferentialFieldZeroExtend]
  have hzero_mem :
      HilbertBundleSectionMemL2 G (μ.restrict Qᶜ)
        (0 : ManifoldDifferentialField I X E) :=
    hilbertBundleSectionMemL2_zero
      (I := I) (G := G) (by intro x A B; rfl) (μ.restrict Qᶜ)
  refine ⟨?_, ?_⟩
  · have hdu_aestr :
        AEStronglyMeasurable
          (HilbertBundleSectionOnSurface.toTotalSpace
            (F := H →L[ℝ] E) du) (μ.restrict Q) :=
      hduQ.aemeasurable.aestronglyMeasurable
    have hzero_aestr :
        AEStronglyMeasurable
          (HilbertBundleSectionOnSurface.toTotalSpace
            (F := H →L[ℝ] E) (0 : ManifoldDifferentialField I X E))
          (μ.restrict Qᶜ) :=
      hzero_mem.aemeasurable.aestronglyMeasurable
    exact
      (AEStronglyMeasurable.piecewise hQ_meas hdu_aestr hzero_aestr).aemeasurable.congr
        (Filter.EventuallyEq.of_eq htotal_ext_eq.symm)
  · have hnorm_ext_eq :
        (fun x : X ↦ G.fiberNormSq x (duExt x)) =
          Q.piecewise
            (fun x : X ↦ G.fiberNormSq x (du x))
            (fun x : X ↦
              G.fiberNormSq x ((0 : ManifoldDifferentialField I X E) x)) := by
      funext x
      by_cases hx : x ∈ Q
      · simp [duExt, hx, manifoldDifferentialFieldZeroExtend]
      · simp [duExt, hx, manifoldDifferentialFieldZeroExtend]
    have hint :
        Integrable
          (Q.piecewise
            (fun x : X ↦ G.fiberNormSq x (du x))
            (fun x : X ↦
              G.fiberNormSq x ((0 : ManifoldDifferentialField I X E) x))) μ :=
      Integrable.piecewise hQ_meas hduQ.integrable_normSq
        hzero_mem.integrable_normSq
    change Integrable (fun x : X ↦ G.fiberNormSq x (duExt x)) μ
    rw [hnorm_ext_eq]
    exact hint

/--
%%handwave
name:
  Squared \(L^2\)-norm of a zero-extended differential
statement:
  The global squared \(L^2\)-norm of a differential field extended by zero
  outside a measurable set \(Q\) is the local differential seminorm squared on
  \(Q\).
proof:
  The squared fiber norm of the zero extension is the piecewise function equal
  to the original squared norm on \(Q\) and zero on \(Q^c\).  Integrating the
  piecewise function splits the integral into the local integral on \(Q\) plus
  the zero integral on the complement.
-/
theorem squareIntegrableManifoldDifferentialField_zero_extend_l2NormSq_eq
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold I 1 X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := I) X E)]
    [TopologicalSpace.PseudoMetrizableSpace
      (ManifoldDifferentialTotalSpace (I := I) X E)]
    {g : SmoothRiemannianMetricOnManifold I X} {μ : Measure X}
    {Q : Set X} (hQ_meas : MeasurableSet Q)
    {du : ManifoldDifferentialField I X E}
    (hduQ : ManifoldDifferentialFieldMemHilbertSchmidtL2 (I := I) g
      (μ.restrict Q) du) :
    squareIntegrableHilbertBundleSectionL2NormSq
        (manifoldDifferentialHilbertBundleGeometry
          (I := I) (X := X) (E := E) g) μ
        ({ toSection := manifoldDifferentialFieldZeroExtend I Q du
           memL2 :=
            manifoldDifferentialFieldMemHilbertSchmidtL2_zero_extend_of_restrict
              (I := I) (g := g) (μ := μ) hQ_meas hduQ } :
          SquareIntegrableManifoldDifferentialField
            (I := I) (X := X) (E := E) g μ) =
      manifoldLocalDifferentialSeminormSq I g μ Q du := by
  classical
  let G :=
    manifoldDifferentialHilbertBundleGeometry
      (I := I) (X := X) (E := E) g
  let metric :=
    manifoldDifferentialHilbertSchmidtContinuousRiemannianMetric
      (I := I) (X := X) (E := E) g
  letI : Bundle.RiemannianBundle
      (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E)) :=
    ⟨metric.toRiemannianMetric⟩
  letI (x : X) :
      NormedAddCommGroup (ManifoldDifferentialBundleFiber
        (I := I) (X := X) (E := E) x) :=
    manifoldDifferentialHilbertSchmidtNormedAddCommGroup
      (I := I) (X := X) (E := E) metric x
  letI (x : X) :
      InnerProductSpace ℝ (ManifoldDifferentialBundleFiber
        (I := I) (X := X) (E := E) x) :=
    manifoldDifferentialHilbertSchmidtInnerProductSpace
      (I := I) (X := X) (E := E) metric x
  have hG_inner :
      ∀ (x : X)
        (A B : ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E) x),
        G.fiberInner x A B = inner ℝ A B := by
    intro x A B
    rfl
  have hG_zero :
      ∀ x : X,
        G.fiberNormSq x ((0 : ManifoldDifferentialField I X E) x) = 0 := by
    intro x
    rw [G.fiberNormSq_eq_inner, hG_inner]
    simp
  have hzero_mem :
      HilbertBundleSectionMemL2 G (μ.restrict Qᶜ)
        (0 : ManifoldDifferentialField I X E) :=
    hilbertBundleSectionMemL2_zero
      (I := I) (G := G) (by intro x A B; rfl) (μ.restrict Qᶜ)
  unfold squareIntegrableHilbertBundleSectionL2NormSq
  have hnorm_ext_eq :
      (fun x : X ↦ G.fiberNormSq x
          ((manifoldDifferentialFieldZeroExtend I Q du) x)) =
        Q.piecewise
          (fun x : X ↦ G.fiberNormSq x (du x))
          (fun x : X ↦
            G.fiberNormSq x ((0 : ManifoldDifferentialField I X E) x)) := by
    funext x
    by_cases hx : x ∈ Q
    · simp [hx, manifoldDifferentialFieldZeroExtend]
    · simp [hx, manifoldDifferentialFieldZeroExtend]
  have hzero_int :
      ∫ x in Qᶜ,
        G.fiberNormSq x ((0 : ManifoldDifferentialField I X E) x) ∂μ = 0 := by
    have hzero_ae :
        (fun x : X ↦
          G.fiberNormSq x ((0 : ManifoldDifferentialField I X E) x)) =ᵐ[
            μ.restrict Qᶜ] fun _x : X ↦ (0 : ℝ) := by
      filter_upwards [] with x
      exact hG_zero x
    simpa using integral_congr_ae hzero_ae
  rw [hnorm_ext_eq]
  rw [integral_piecewise hQ_meas hduQ.integrable_normSq
    hzero_mem.integrable_normSq]
  rw [hzero_int]
  simp [manifoldLocalDifferentialSeminormSq]

/--
%%handwave
name:
  Vanishing local energy gives zero-extended differential \(L^2\)-convergence
statement:
  If differential fields are square-integrable on a measurable set \(Q\) and
  their local Hilbert-Schmidt energies on \(Q\) tend to zero, then their
  zero extensions converge to zero in the global intrinsic differential
  \(L^2\)-space.
proof:
  The squared \(L^2\)-norm of each zero extension is exactly the local
  differential seminorm on \(Q\).  The Hilbert-space quotient topology
  identifies convergence to zero with convergence of these norms to zero.
-/
theorem manifoldDifferentialL2Section_zeroExtend_tendsto_zero_of_localSeminormSq_tendsto_zero
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := I) X E)]
    [TopologicalSpace.PseudoMetrizableSpace
      (ManifoldDifferentialTotalSpace (I := I) X E)]
    {g : SmoothRiemannianMetricOnManifold I X} {μ : Measure X}
    {Q : Set X} (hQ_meas : MeasurableSet Q)
    (du : ℕ → ManifoldDifferentialField I X E)
    (hduQ : ∀ n : ℕ,
      ManifoldDifferentialFieldMemHilbertSchmidtL2 (I := I) g
        (μ.restrict Q) (du n))
    (henergy :
      Filter.Tendsto
        (fun n : ℕ ↦ manifoldLocalDifferentialSeminormSq I g μ Q (du n))
        Filter.atTop (𝓝 0)) :
    letI : NormedAddCommGroup
        (ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ) :=
      manifoldDifferentialL2SectionNormedAddCommGroup
        (I := I) (X := X) (E := E) g μ
    Filter.Tendsto
      (fun n : ℕ ↦
        (Quotient.mk
          (SquareIntegrableManifoldDifferentialField.aeSetoid
            (I := I) (X := X) (E := E) (g := g) (μ := μ))
          ({ toSection := manifoldDifferentialFieldZeroExtend I Q (du n)
             memL2 :=
              manifoldDifferentialFieldMemHilbertSchmidtL2_zero_extend_of_restrict
                (I := I) (g := g) (μ := μ) hQ_meas (hduQ n) } :
            SquareIntegrableManifoldDifferentialField
              (I := I) (X := X) (E := E) g μ) :
          ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ))
      Filter.atTop
      (𝓝 (0 :
        ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ)) := by
  letI : NormedAddCommGroup
      (ManifoldDifferentialL2Section (I := I) (X := X) (E := E) g μ) :=
    manifoldDifferentialL2SectionNormedAddCommGroup
      (I := I) (X := X) (E := E) g μ
  let w : ℕ → SquareIntegrableManifoldDifferentialField
      (I := I) (X := X) (E := E) g μ := fun n ↦
    { toSection := manifoldDifferentialFieldZeroExtend I Q (du n)
      memL2 :=
        manifoldDifferentialFieldMemHilbertSchmidtL2_zero_extend_of_restrict
          (I := I) (g := g) (μ := μ) hQ_meas (hduQ n) }
  have hsq :
      Filter.Tendsto
        (fun n : ℕ ↦
          squareIntegrableHilbertBundleSectionL2NormSq
            (manifoldDifferentialHilbertBundleGeometry
              (I := I) (X := X) (E := E) g) μ (w n))
        Filter.atTop (𝓝 0) := by
    refine henergy.congr' ?_
    filter_upwards [] with n
    exact
      squareIntegrableManifoldDifferentialField_zero_extend_l2NormSq_eq
        (I := I) (g := g) (μ := μ) hQ_meas (hduQ n) |>.symm
  simpa [w] using
    manifoldDifferentialL2Section_tendsto_zero_of_l2NormSq_tendsto_zero
      (I := I) (X := X) (E := E) g μ (du := w) hsq

/--
%%handwave
name:
  Indicator representative as a square-integrable value section
statement:
  If a real-valued function is \(L^2\) on a measurable set \(P\), then its
  zero extension outside \(P\) is a square-integrable trivial-bundle section
  on the ambient measure space.
-/
noncomputable def squareIntegrableValueSectionIndicator
    {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} {P : Set X} (hP_meas : MeasurableSet P)
    (u : X → ℝ) (hu : MemLp u 2 (μ.restrict P)) :
    SquareIntegrableValueSection (X := X) (E := ℝ) μ :=
  { toSection := P.indicator u
    memL2 :=
      trivial_real_hilbertBundleSectionMemL2_of_memLp
        ((memLp_indicator_iff_restrict (μ := μ) (p := (2 : ℝ≥0∞))
          (f := u) hP_meas).2 hu) }

set_option maxHeartbeats 800000

/--
%%handwave
name:
  Local \(L^2\)-convergence gives convergence of zero-extended values
statement:
  If real-valued functions converge in \(L^2\) on a measurable set \(P\), then
  their zero extensions outside \(P\) converge in the global intrinsic
  value \(L^2\)-section space.
proof:
  The zero extension is the indicator of \(P\).  Its global \(L^2\)-norm is
  the restricted \(L^2\)-norm on \(P\), and the quotient topology on
  value \(L^2\)-sections is induced by this norm.
-/
theorem valueL2Section_indicator_tendsto_of_restrict_eLpNorm_tendsto_zero
    {H X : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [SecondCountableTopology (Bundle.TotalSpace ℝ (Bundle.Trivial X ℝ))]
    {μ : Measure X} {P : Set X} (hP_meas : MeasurableSet P)
    {u : ℕ → X → ℝ} {uLim : X → ℝ}
    (hmem : ∀ n : ℕ, MemLp (u n) 2 (μ.restrict P))
    (hmemLim : MemLp uLim 2 (μ.restrict P))
    (hlim :
      Filter.Tendsto
        (fun n : ℕ ↦ eLpNorm (fun x : X ↦ u n x - uLim x) 2 (μ.restrict P))
        Filter.atTop (𝓝 0)) :
    letI : NormedAddCommGroup (ValueL2Section (X := X) (E := ℝ) μ) :=
      valueL2SectionNormedAddCommGroup (I := I) (X := X) (E := ℝ) μ
    Filter.Tendsto
      (fun n : ℕ ↦
        (Quotient.mk
          (SquareIntegrableValueSection.aeSetoid
            (X := X) (E := ℝ) (μ := μ))
          (squareIntegrableValueSectionIndicator hP_meas (u n) (hmem n)) :
          ValueL2Section (X := X) (E := ℝ) μ))
      Filter.atTop
      (𝓝
        (Quotient.mk
          (SquareIntegrableValueSection.aeSetoid
            (X := X) (E := ℝ) (μ := μ))
          (squareIntegrableValueSectionIndicator hP_meas uLim hmemLim) :
          ValueL2Section (X := X) (E := ℝ) μ)) := by
  letI : NormedAddCommGroup (ValueL2Section (X := X) (E := ℝ) μ) :=
    valueL2SectionNormedAddCommGroup (I := I) (X := X) (E := ℝ) μ
  let w : ℕ → SquareIntegrableValueSection (X := X) (E := ℝ) μ := fun n ↦
    squareIntegrableValueSectionIndicator hP_meas (u n) (hmem n)
  let wLim : SquareIntegrableValueSection (X := X) (E := ℝ) μ :=
    squareIntegrableValueSectionIndicator hP_meas uLim hmemLim
  have hglobal :
      Filter.Tendsto
        (fun n : ℕ ↦
          eLpNorm (fun x : X ↦ (w n).toFunction x - wLim.toFunction x) 2 μ)
        Filter.atTop (𝓝 0) := by
    refine hlim.congr' ?_
    filter_upwards [] with n
    have hindicator :
        (fun x : X ↦ (w n).toFunction x - wLim.toFunction x) =
          P.indicator (fun x : X ↦ u n x - uLim x) := by
      funext x
      by_cases hx : x ∈ P
      · simp [w, wLim, squareIntegrableValueSectionIndicator,
          SquareIntegrableValueSection.toFunction, hx]
      · simp [w, wLim, squareIntegrableValueSectionIndicator,
          SquareIntegrableValueSection.toFunction, hx]
    rw [hindicator]
    exact
      eLpNorm_indicator_eq_eLpNorm_restrict
        (μ := μ) (p := (2 : ℝ≥0∞)) (f := fun x : X ↦ u n x - uLim x)
        hP_meas |>.symm
  change
    Filter.Tendsto
      (fun n : ℕ ↦
        (Quotient.mk
          (SquareIntegrableValueSection.aeSetoid
            (X := X) (E := ℝ) (μ := μ)) (w n) :
          ValueL2Section (X := X) (E := ℝ) μ))
      Filter.atTop
      (𝓝
        (Quotient.mk
          (SquareIntegrableValueSection.aeSetoid
            (X := X) (E := ℝ) (μ := μ)) wLim :
          ValueL2Section (X := X) (E := ℝ) μ))
  exact
    valueL2Section_tendsto_of_eLpNorm_sub_tendsto_zero
      (I := I) (X := X) (E := ℝ) μ hglobal

set_option maxHeartbeats 200000

/--
%%handwave
name:
  The value term is bounded by the local \(W^{1,2}\) seminorm
statement:
  The local value \(L^2\) seminorm squared is bounded by the local
  \(W^{1,2}\) seminorm squared.
proof:
  The \(W^{1,2}\) seminorm is the sum of the value term and the nonnegative
  differential term.
-/
theorem manifoldLocalValueL2SeminormSq_le_h1 {H X E : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I : ModelWithCorners ℝ H H) [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold I 1 X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : SmoothRiemannianMetricOnManifold I X) (μ : Measure X)
    (K : Set X) (u : X → E) (du : ManifoldDifferentialField I X E) :
    manifoldLocalValueL2SeminormSq μ K u ≤
      manifoldLocalH1SeminormSq I g μ K u du := by
  have hdiff_nonneg :
      0 ≤ manifoldLocalDifferentialSeminormSq I g μ K du :=
    manifoldLocalDifferentialSeminormSq_nonneg I g μ K du
  dsimp [manifoldLocalH1SeminormSq]
  linarith

/--
%%handwave
name:
  The differential term is bounded by the local \(W^{1,2}\) seminorm
statement:
  The local Hilbert-Schmidt \(L^2\) seminorm squared of the weak differential
  is bounded by the local \(W^{1,2}\) seminorm squared.
proof:
  The \(W^{1,2}\) seminorm is the sum of the differential term and the
  nonnegative value term.
-/
theorem manifoldLocalDifferentialSeminormSq_le_h1 {H X E : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I : ModelWithCorners ℝ H H) [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold I 1 X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : SmoothRiemannianMetricOnManifold I X) (μ : Measure X)
    (K : Set X) (u : X → E) (du : ManifoldDifferentialField I X E) :
    manifoldLocalDifferentialSeminormSq I g μ K du ≤
      manifoldLocalH1SeminormSq I g μ K u du := by
  have hvalue_nonneg :
      0 ≤ manifoldLocalValueL2SeminormSq μ K u :=
    manifoldLocalValueL2SeminormSq_nonneg μ K u
  dsimp [manifoldLocalH1SeminormSq]
  linarith

/--
%%handwave
name:
  A local \(W^{1,2}\)-bounded family has bounded value \(L^2\) seminorms
statement:
  Uniform local \(W^{1,2}\) boundedness implies uniform boundedness of the
  local value \(L^2\) seminorms.
proof:
  The value seminorm is one of the two nonnegative summands of the local
  \(W^{1,2}\) seminorm.
-/
theorem BoundedInLocalSobolevH1OnManifoldWithValues.value_l2_bound
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold I 1 X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {g : SmoothRiemannianMetricOnManifold I X} {μ : Measure X}
    {K : Set X} {u : ℕ → X → E}
    {du : ℕ → ManifoldDifferentialField I X E}
    (hbounded : BoundedInLocalSobolevH1OnManifoldWithValues (I := I) g μ K u du) :
    ∃ C : ℝ, ∀ n : ℕ,
      manifoldLocalValueL2SeminormSq μ K (u n) ≤ C := by
  rcases hbounded with ⟨C, hC⟩
  refine ⟨C, fun n ↦ ?_⟩
  exact (manifoldLocalValueL2SeminormSq_le_h1 I g μ K (u n) (du n)).trans (hC n)

/--
%%handwave
name:
  A local \(W^{1,2}\)-bounded family has bounded differential seminorms
statement:
  Uniform local \(W^{1,2}\) boundedness implies uniform boundedness of the
  local Hilbert-Schmidt \(L^2\) seminorms of the weak differentials.
proof:
  The differential seminorm is one of the two nonnegative summands of the
  local \(W^{1,2}\) seminorm.
-/
theorem BoundedInLocalSobolevH1OnManifoldWithValues.differential_l2_bound
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold I 1 X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {g : SmoothRiemannianMetricOnManifold I X} {μ : Measure X}
    {K : Set X} {u : ℕ → X → E}
    {du : ℕ → ManifoldDifferentialField I X E}
    (hbounded : BoundedInLocalSobolevH1OnManifoldWithValues (I := I) g μ K u du) :
    ∃ C : ℝ, ∀ n : ℕ,
      manifoldLocalDifferentialSeminormSq I g μ K (du n) ≤ C := by
  rcases hbounded with ⟨C, hC⟩
  refine ⟨C, fun n ↦ ?_⟩
  exact (manifoldLocalDifferentialSeminormSq_le_h1 I g μ K (u n) (du n)).trans (hC n)

namespace ManifoldDifferentialField

/--
%%handwave
name:
  Coordinate pullback of a manifold differential field
statement:
  In a chart, a manifold differential field becomes an operator-valued field
  on the model vector space by composing the fiber differential with the
  tangent map of the inverse chart.
-/
noncomputable def chartPullback {H X E : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (du : ManifoldDifferentialField I X E) (e : OpenPartialHomeomorph X H) :
    H → H →L[ℝ] E :=
  fun z ↦ (du (e.symm z)).comp
    (fderivWithin ℝ
      (fun w : H ↦ chartAt H (e.symm z) (e.symm w)) e.target z)

/--
%%handwave
name:
  Evaluation of a differential field pulled back to a chart
statement:
  The chart pullback of a manifold differential field \(du\), evaluated at
  \(z\) and \(v\), is the fiber differential at \(e^{-1}(z)\) applied to the
  tangent image of \(v\) under the inverse chart.
proof:
  This is the defining formula for the chart pullback.
-/
@[simp]
theorem chartPullback_apply {H X E : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (du : ManifoldDifferentialField I X E)
    (e : OpenPartialHomeomorph X H) (z v : H) :
    chartPullback du e z v = evalChart du e z v :=
  rfl

end ManifoldDifferentialField

/--
%%handwave
name:
  Manifold weak derivatives are Euclidean weak derivatives in charts
statement:
  If a Hilbert-valued map has a weak differential on a manifold region, then
  in every coordinate chart the pulled-back map has the pulled-back
  differential field as its Euclidean weak derivative on the corresponding
  coordinate region.
proof:
  This is exactly the chartwise integration-by-parts identity in the
  definition of the manifold weak differential.
-/
theorem IsWeakDerivativeOnManifoldRegionBundle.chartPullback
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H] [IsManifold I 1 X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set X} {u : X → E} {du : ManifoldDifferentialField I X E}
    (hweak : IsWeakDerivativeOnManifoldRegionBundle (I := I) U u du)
    (e : OpenPartialHomeomorph X H) (he : e ∈ atlas H X) :
    IsWeakDerivativeOnEuclideanRegionWithValues
      (manifoldChartRegion e U)
      (fun z : H ↦ u (e.symm z))
      (ManifoldDifferentialField.chartPullback du e) := by
  intro φ v
  simpa [ManifoldDifferentialField.chartPullback] using hweak e he φ v

/--
%%handwave
name:
  Euclidean local \(W^{1,2}\)-bounded family
statement:
  A sequence of Hilbert-valued maps on a region of a finite-dimensional real
  vector space is locally \(W^{1,2}\)-bounded on a compact set if the
  Euclidean \(L^2\) norms of the maps and their weak derivative fields are
  uniformly bounded there.
-/
def BoundedInEuclideanLocalSobolevH1WithValues {H E : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set H) (u : ℕ → H → E) (du : ℕ → H → H →L[ℝ] E) : Prop :=
  ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ n : ℕ,
    MemLp (u n) 2 (MeasureTheory.volume.restrict K) ∧
      MemLp (du n) 2 (MeasureTheory.volume.restrict K) ∧
        eLpNorm (u n) 2 (MeasureTheory.volume.restrict K) +
          eLpNorm (du n) 2 (MeasureTheory.volume.restrict K) ≤ C

/--
%%handwave
name:
  A bounded Euclidean Sobolev family has \(L^2\) values
statement:
  A uniformly locally \(W^{1,2}\)-bounded Euclidean family has each value
  function in \(L^2\) on the compact set.
proof:
  Unpack the uniform local Sobolev bound; its first component states \(L^2\)-membership of every value function on the compact set.
-/
theorem BoundedInEuclideanLocalSobolevH1WithValues.value_memLp {H E : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set H} {u : ℕ → H → E} {du : ℕ → H → H →L[ℝ] E}
    (hbounded : BoundedInEuclideanLocalSobolevH1WithValues K u du)
    (n : ℕ) :
    MemLp (u n) 2 (MeasureTheory.volume.restrict K) := by
  rcases hbounded with ⟨_C, _hC_top, hC⟩
  exact (hC n).1

/--
%%handwave
name:
  A bounded Euclidean Sobolev family has \(L^2\) derivatives
statement:
  A uniformly locally \(W^{1,2}\)-bounded Euclidean family has each weak
  derivative field in \(L^2\) on the compact set.
proof:
  Unpack the second component of the boundedness hypothesis, which supplies \(L^2\)-membership of every weak derivative on the compact set.
-/
theorem BoundedInEuclideanLocalSobolevH1WithValues.derivative_memLp {H E : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set H} {u : ℕ → H → E} {du : ℕ → H → H →L[ℝ] E}
    (hbounded : BoundedInEuclideanLocalSobolevH1WithValues K u du)
    (n : ℕ) :
    MemLp (du n) 2 (MeasureTheory.volume.restrict K) := by
  rcases hbounded with ⟨_C, _hC_top, hC⟩
  exact (hC n).2.1

/--
%%handwave
name:
  A bounded Euclidean Sobolev family has uniformly bounded \(L^2\) values
statement:
  A uniformly locally \(W^{1,2}\)-bounded Euclidean family has uniformly
  bounded \(L^2\) norms of its value functions on the compact set.
proof:
  Use the common bound furnished by the definition for the value component at the chosen family index.
-/
theorem BoundedInEuclideanLocalSobolevH1WithValues.value_eLpNorm_bound {H E : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set H} {u : ℕ → H → E} {du : ℕ → H → H →L[ℝ] E}
    (hbounded : BoundedInEuclideanLocalSobolevH1WithValues K u du) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ n : ℕ,
      eLpNorm (u n) 2 (MeasureTheory.volume.restrict K) ≤ C := by
  rcases hbounded with ⟨C, hC_top, hC⟩
  refine ⟨C, hC_top, fun n ↦ ?_⟩
  exact (le_self_add.trans (hC n).2.2)

/--
%%handwave
name:
  A bounded Euclidean Sobolev family has uniformly bounded \(L^2\) derivatives
statement:
  A uniformly locally \(W^{1,2}\)-bounded Euclidean family has uniformly
  bounded \(L^2\) norms of its weak derivative fields on the compact set.
proof:
  Use the derivative component of the uniform bound at the chosen index.
-/
theorem BoundedInEuclideanLocalSobolevH1WithValues.derivative_eLpNorm_bound {H E : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set H} {u : ℕ → H → E} {du : ℕ → H → H →L[ℝ] E}
    (hbounded : BoundedInEuclideanLocalSobolevH1WithValues K u du) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ n : ℕ,
      eLpNorm (du n) 2 (MeasureTheory.volume.restrict K) ≤ C := by
  rcases hbounded with ⟨C, hC_top, hC⟩
  refine ⟨C, hC_top, fun n ↦ ?_⟩
  exact (le_add_self.trans (hC n).2.2)

/--
%%handwave
name:
  Euclidean Sobolev boundedness restricts to smaller sets
statement:
  If a sequence is uniformly locally \(W^{1,2}\)-bounded on a set, then it is
  uniformly locally \(W^{1,2}\)-bounded on every subset.
proof:
  Restricting the measure only decreases the \(L^2\) seminorms.
-/
theorem BoundedInEuclideanLocalSobolevH1WithValues.mono_set {H E : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K Q : Set H} {u : ℕ → H → E} {du : ℕ → H → H →L[ℝ] E}
    (hKQ : K ⊆ Q)
    (hbounded : BoundedInEuclideanLocalSobolevH1WithValues Q u du) :
    BoundedInEuclideanLocalSobolevH1WithValues K u du := by
  rcases hbounded with ⟨C, hC_top, hC⟩
  refine ⟨C, hC_top, fun n ↦ ?_⟩
  rcases hC n with ⟨hu, hdu, hbound⟩
  have hμ : MeasureTheory.volume.restrict K ≤ MeasureTheory.volume.restrict Q :=
    Measure.restrict_mono hKQ le_rfl
  refine ⟨hu.mono_measure hμ, hdu.mono_measure hμ, ?_⟩
  exact (add_le_add (eLpNorm_mono_measure (u n) hμ)
    (eLpNorm_mono_measure (du n) hμ)).trans hbound

/--
%%handwave
name:
  Euclidean local \(L^2\) convergence for Hilbert-valued maps
statement:
  A sequence of Hilbert-valued maps on a finite-dimensional real vector space
  converges locally in \(L^2\) on a set if the Euclidean \(L^2\) norm of the
  difference tends to zero on that set.
-/
def TendstoInEuclideanLocalL2WithValues {H E : Type} [MeasureSpace H]
    [NormedAddCommGroup E]
    (K : Set H) (uSeq : ℕ → H → E) (u : H → E) : Prop :=
  Filter.Tendsto
    (fun n : ℕ ↦
      eLpNorm (fun z ↦ uSeq n z - u z) 2
        (MeasureTheory.volume.restrict K))
    Filter.atTop (𝓝 0)

/--
%%handwave
name:
  Euclidean weak derivative for scalar maps
statement:
  A real-valued map on a Euclidean region has a weak derivative field if it
  satisfies the usual integration-by-parts identity against smooth compactly
  supported scalar coordinate tests and constant directions.
-/
abbrev IsWeakDerivativeOnEuclideanRegionScalar {H : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    (Ω : Set H) (u : H → ℝ) (du : H → H →L[ℝ] ℝ) : Prop :=
  IsWeakDerivativeOnEuclideanRegionWithValues Ω u du

/--
%%handwave
name:
  Restricting a Euclidean weak derivative identity
statement:
  If a vector-valued weak derivative identity holds on a region, then the same
  identity holds on every smaller region contained in it.
proof:
  A compactly supported test on the smaller region is also a compactly
  supported test on the larger region.  The two integration domains give the
  same integrals, because the test function and its derivative vanish outside
  the smaller region.
-/
theorem IsWeakDerivativeOnEuclideanRegionWithValues.mono_set
    {H E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U Ω : Set H} {u : H → E} {du : H → H →L[ℝ] E}
    (hweak : IsWeakDerivativeOnEuclideanRegionWithValues Ω u du)
    (hUΩ : U ⊆ Ω) :
    IsWeakDerivativeOnEuclideanRegionWithValues U u du := by
  intro φ v
  let ψ : SmoothCompactlySupportedManifoldCoordinateFunction Ω :=
    { toFun := φ
      smooth := φ.smooth
      support_subset := φ.support_subset.trans hUΩ
      compact_support := φ.compact_support }
  rcases hweak ψ v with ⟨hleftΩ, hrightΩ, heqΩ⟩
  let left : H → E := fun z ↦ (fderiv ℝ (φ : H → ℝ) z v) • u z
  let right : H → E := fun z ↦ φ z • du z v
  have hleft_int_U : Integrable left (MeasureTheory.volume.restrict U) := by
    have hres := hleftΩ.restrict (s := U)
    simpa [left, ψ, Measure.restrict_restrict_of_subset hUΩ] using hres
  have hright_int_U : Integrable right (MeasureTheory.volume.restrict U) := by
    have hres := hrightΩ.restrict (s := U)
    simpa [right, ψ, Measure.restrict_restrict_of_subset hUΩ] using hres
  have hleft_zero_U : ∀ z : H, z ∉ U → left z = 0 := by
    intro z hzU
    have hz_not : z ∉ tsupport (fun z ↦ fderiv ℝ (φ : H → ℝ) z v) := by
      intro hz
      exact hzU <| φ.support_subset <|
        (tsupport_fderiv_apply_subset (𝕜 := ℝ)
          (f := (φ : H → ℝ)) v) hz
    have hzero :
        fderiv ℝ (φ : H → ℝ) z v = 0 :=
      image_eq_zero_of_notMem_tsupport
        (f := fun y : H ↦ fderiv ℝ (φ : H → ℝ) y v) hz_not
    simp [left, hzero]
  have hright_zero_U : ∀ z : H, z ∉ U → right z = 0 := by
    intro z hzU
    have hz_not : z ∉ tsupport (φ : H → ℝ) := by
      intro hz
      exact hzU (φ.support_subset hz)
    have hzero : φ z = 0 := image_eq_zero_of_notMem_tsupport hz_not
    simp [right, hzero]
  have hleft_zero_Ω : ∀ z : H, z ∉ Ω → left z = 0 := by
    intro z hzΩ
    exact hleft_zero_U z (fun hzU ↦ hzΩ (hUΩ hzU))
  have hright_zero_Ω : ∀ z : H, z ∉ Ω → right z = 0 := by
    intro z hzΩ
    exact hright_zero_U z (fun hzU ↦ hzΩ (hUΩ hzU))
  have hleft_U_eq_Ω :
      ∫ z in U, left z ∂MeasureTheory.volume =
        ∫ z in Ω, left z ∂MeasureTheory.volume := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hleft_zero_U,
      setIntegral_eq_integral_of_forall_compl_eq_zero hleft_zero_Ω]
  have hright_U_eq_Ω :
      ∫ z in U, right z ∂MeasureTheory.volume =
        ∫ z in Ω, right z ∂MeasureTheory.volume := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hright_zero_U,
      setIntegral_eq_integral_of_forall_compl_eq_zero hright_zero_Ω]
  refine ⟨?_, ?_, ?_⟩
  · simpa [left] using hleft_int_U
  · simpa [right] using hright_int_U
  · calc
      ∫ z in U, (fderiv ℝ (φ : H → ℝ) z v) • u z
          ∂MeasureTheory.volume
          = ∫ z in U, left z ∂MeasureTheory.volume := rfl
      _ = ∫ z in Ω, left z ∂MeasureTheory.volume := hleft_U_eq_Ω
      _ = -∫ z in Ω, right z ∂MeasureTheory.volume := by
            simpa [left, right, ψ] using heqΩ
      _ = -∫ z in U, right z ∂MeasureTheory.volume := by
            rw [hright_U_eq_Ω]
      _ = -∫ z in U, φ z • du z v ∂MeasureTheory.volume := rfl

/--
%%handwave
name:
  Euclidean local \(W^{1,2}\)-bounded scalar family
statement:
  A sequence of real-valued maps on a Euclidean region is locally
  \(W^{1,2}\)-bounded on a compact set if the Euclidean \(L^2\) norms of the
  maps and their weak derivative fields are uniformly bounded there.
-/
abbrev BoundedInEuclideanLocalSobolevH1Scalar {H : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    (K : Set H) (u : ℕ → H → ℝ) (du : ℕ → H → H →L[ℝ] ℝ) : Prop :=
  BoundedInEuclideanLocalSobolevH1WithValues K u du

/--
%%handwave
name:
  Euclidean local \(L^2\) convergence for scalar maps
statement:
  A sequence of real-valued maps on a finite-dimensional real vector space
  converges locally in \(L^2\) on a set if the Euclidean \(L^2\) norm of the
  difference tends to zero on that set.
-/
abbrev TendstoInEuclideanLocalL2Scalar {H : Type} [MeasureSpace H]
    (K : Set H) (uSeq : ℕ → H → ℝ) (u : H → ℝ) : Prop :=
  TendstoInEuclideanLocalL2WithValues K uSeq u

/--
%%handwave
name:
  Uniform \(L^2\)-boundedness for a family on a compact Euclidean set
statement:
  A family of scalar functions is uniformly bounded in \(L^2\) on a compact
  Euclidean set if all its \(L^2\) seminorms on that set are bounded by one
  finite constant.
-/
def EuclideanL2BoundedFamilyOnCompact {ι H : Type}
    [MeasureSpace H]
    (K : Set H) (u : ι → H → ℝ) : Prop :=
  ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ i : ι,
    eLpNorm (u i) 2 (MeasureTheory.volume.restrict K) ≤ C

/--
%%handwave
name:
  Uniform translation tightness for a family on a compact Euclidean set
statement:
  A family of scalar functions is uniformly translation-tight in \(L^2\) on
  a compact set if small translations change every function in the sequence
  by a uniformly small \(L^2\) amount on that set.
-/
def EuclideanL2TranslationTightFamilyOnCompactForMeasure {ι H : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasurableSpace H]
    (μ : Measure H) (K : Set H) (u : ι → H → ℝ) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : H, ‖h‖ < δ →
      ∀ i : ι,
        eLpNorm (fun z ↦ u i (z + h) - u i z) 2
          (μ.restrict K) ≤ ε

/--
%%handwave
name:
  Uniform translation tightness for a family on a compact Euclidean set
statement:
  A family of scalar functions is uniformly translation-tight in \(L^2\) on
  a compact set if small translations change every function in the sequence
  by a uniformly small \(L^2\) amount on that set.
-/
def EuclideanL2TranslationTightFamilyOnCompact {ι H : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    (K : Set H) (u : ι → H → ℝ) : Prop :=
  EuclideanL2TranslationTightFamilyOnCompactForMeasure (volume : Measure H) K u

/--
%%handwave
name:
  Uniform translation tightness on a compact Euclidean set
statement:
  A sequence of scalar functions is uniformly translation-tight in \(L^2\) on
  a compact set if small translations change every function in the sequence
  by a uniformly small \(L^2\) amount on that set.
-/
abbrev EuclideanL2TranslationTightOnCompact {H : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    (K : Set H) (u : ℕ → H → ℝ) : Prop :=
  EuclideanL2TranslationTightFamilyOnCompact K u

/--
%%handwave
name:
  Linear translation modulus implies uniform translation tightness
statement:
  Suppose that for \(\lVert h\rVert<\rho\),
  \[\lVert u_i(\,\cdot+h)-u_i\rVert_{L^2(K,\mu)}
    \le \lVert h\rVert A\]
  uniformly in \(i\), where \(A<\infty\). Then the family is uniformly
  translation-tight in \(L^2(K,\mu)\).
proof:
  Given \(\varepsilon>0\), choose
  \(\delta<\min(\rho,\varepsilon/(2A))\). The linear modulus is then below
  \(\varepsilon\); the cases \(A=0\) and \(\varepsilon=\infty\) are immediate.
-/
private theorem euclideanL2TranslationTightFamilyOnCompactForMeasure_of_linear_modulus
    {ι H : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasurableSpace H]
    {μ : Measure H} {K : Set H} {u : ι → H → ℝ}
    {A : ℝ≥0∞} (hA_top : A < ⊤) {ρ : ℝ} (hρ : 0 < ρ)
    (hmod : ∀ h : H, ‖h‖ < ρ → ∀ i : ι,
      eLpNorm (fun z ↦ u i (z + h) - u i z) 2 (μ.restrict K) ≤
        ENNReal.ofReal ‖h‖ * A) :
    EuclideanL2TranslationTightFamilyOnCompactForMeasure μ K u := by
  intro ε hε
  by_cases hε_top : ε = ⊤
  · refine ⟨ρ, hρ, fun h hh i ↦ ?_⟩
    simp [hε_top]
  by_cases hA_zero : A = 0
  · refine ⟨ρ, hρ, fun h hh i ↦ ?_⟩
    calc
      eLpNorm (fun z ↦ u i (z + h) - u i z) 2 (μ.restrict K)
          ≤ ENNReal.ofReal ‖h‖ * A := hmod h hh i
      _ = 0 := by simp [hA_zero]
      _ ≤ ε := zero_le
  have hA_pos : 0 < A.toReal := ENNReal.toReal_pos hA_zero hA_top.ne
  have hε_pos : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hε_top
  let δ : ℝ := min ρ (ε.toReal / (2 * A.toReal))
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    exact lt_min hρ (div_pos hε_pos (mul_pos (by norm_num) hA_pos))
  refine ⟨δ, hδ_pos, fun h hh i ↦ ?_⟩
  have hhρ : ‖h‖ < ρ := by
    exact lt_of_lt_of_le hh (by dsimp [δ]; exact min_le_left _ _)
  have hhsmall : ‖h‖ < ε.toReal / (2 * A.toReal) := by
    exact lt_of_lt_of_le hh (by dsimp [δ]; exact min_le_right _ _)
  have hhalf_eq :
      (ε.toReal / (2 * A.toReal)) * A.toReal = ε.toReal / 2 := by
    field_simp [hA_pos.ne']
  have hhalf_lt : ‖h‖ * A.toReal < ε.toReal / 2 := by
    have hmul := mul_lt_mul_of_pos_right hhsmall hA_pos
    simpa [hhalf_eq] using hmul
  have hreal_lt : ‖h‖ * A.toReal < ε.toReal := by
    have : ε.toReal / 2 < ε.toReal := by nlinarith
    exact hhalf_lt.trans this
  have hprod_lt : ENNReal.ofReal ‖h‖ * A < ε := by
    calc
      ENNReal.ofReal ‖h‖ * A
          = ENNReal.ofReal ‖h‖ * ENNReal.ofReal A.toReal := by
            rw [ENNReal.ofReal_toReal hA_top.ne]
      _ = ENNReal.ofReal (‖h‖ * A.toReal) := by
            rw [← ENNReal.ofReal_mul (norm_nonneg h)]
      _ < ENNReal.ofReal ε.toReal := by
            rw [ENNReal.ofReal_lt_ofReal_iff hε_pos]
            exact hreal_lt
      _ = ε := ENNReal.ofReal_toReal hε_top
  exact (hmod h hhρ i).trans (le_of_lt hprod_lt)

/--
%%handwave
name:
  Compact containment gives a uniform segment radius
statement:
  If a compact set lies in the interior of another set in a finite-dimensional
  Euclidean space, then all sufficiently short line segments starting in the
  compact set remain in the larger set.
proof:
  A compact subset of an open set has a positive closed metric thickening
  contained in that open set.  If \(\|h\|\) is below this radius and
  \(0\le t\le 1\), then \(x+t h\) is within this thickening of \(x\).
-/
theorem euclideanCompact_exists_translation_segment_radius
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [FiniteDimensional ℝ H]
    {K Q : Set H} (hK : IsCompact K) (hKQ : K ⊆ interior Q) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ x ∈ K, ∀ h : H, ‖h‖ < ρ → ∀ t : ℝ, t ∈ Set.Icc 0 1 →
        x + t • h ∈ Q := by
  rcases hK.exists_cthickening_subset_open isOpen_interior hKQ with
    ⟨ρ, hρ_pos, hρ_sub⟩
  refine ⟨ρ, hρ_pos, fun x hx h hh t ht ↦ ?_⟩
  have ht_abs : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  have hdist : dist (x + t • h) x ≤ ρ := by
    calc
      dist (x + t • h) x = ‖t • h‖ := by
        simp [dist_eq_norm]
      _ = |t| * ‖h‖ := norm_smul t h
      _ ≤ 1 * ‖h‖ := mul_le_mul_of_nonneg_right ht_abs (norm_nonneg h)
      _ = ‖h‖ := one_mul ‖h‖
      _ ≤ ρ := le_of_lt hh
  exact interior_subset (hρ_sub
    (Metric.mem_cthickening_of_dist_le (x + t • h) x ρ K hx hdist))

/--
%%handwave
name:
  Directional weak derivatives are locally integrable
statement:
  On every compact subset of an open Euclidean region, a directional weak
  derivative is integrable.
proof:
  Choose a smooth cutoff equal to one on the compact set and whose support is
  contained in the open region.  The weak-derivative definition gives
  integrability of the cutoff directional derivative on the region.  Since
  the cutoff is one on the compact set, restricting the integral gives
  integrability of the directional derivative there.
-/
theorem scalarWeakSobolev_directionalDerivative_integrableOn_compact
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Q Ω : Set H} (hQ : IsCompact Q)
    (hQΩ : Q ⊆ Ω) (hΩ_open : IsOpen Ω)
    {u : H → ℝ} {du : H → H →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionScalar Ω u du)
    {h : H} :
    Integrable (fun z ↦ du z h) (MeasureTheory.volume.restrict Q) := by
  obtain ⟨δ, hδ_pos, hδΩ⟩ :=
    hQ.exists_cthickening_subset_open hΩ_open hQΩ
  obtain ⟨ψ, hψ_smooth, _hψ_range, hψ_support, hψ_one⟩ :=
    exists_contMDiff_support_eq_eq_one_iff
      (I := 𝓘(ℝ, H)) (n := ⊤)
      (Metric.isOpen_thickening) hQ.isClosed
      (Metric.self_subset_thickening hδ_pos Q)
  have hψ_tsupport_subset_cthickening :
      tsupport ψ ⊆ Metric.cthickening δ Q := by
    rw [tsupport, hψ_support]
    exact Metric.closure_thickening_subset_cthickening δ Q
  let φ : SmoothCompactlySupportedManifoldCoordinateFunction Ω :=
    { toFun := ψ
      smooth := hψ_smooth.contDiff
      support_subset := hψ_tsupport_subset_cthickening.trans hδΩ
      compact_support := by
        exact IsCompact.of_isClosed_subset (hQ.cthickening)
          (isClosed_tsupport ψ) hψ_tsupport_subset_cthickening }
  have hcutoff_int : Integrable (fun z ↦ φ z • du z h)
      (MeasureTheory.volume.restrict Ω) :=
    (hweak φ h).2.1
  have hcutoff_int_Q : Integrable (fun z ↦ φ z • du z h)
      (MeasureTheory.volume.restrict Q) := by
    have hres := hcutoff_int.restrict (s := Q)
    simpa [Measure.restrict_restrict_of_subset hQΩ] using hres
  have hcutoff_eq :
      (fun z ↦ φ z • du z h) =ᵐ[MeasureTheory.volume.restrict Q]
        fun z ↦ du z h := by
    exact ae_restrict_of_forall_mem hQ.measurableSet fun z hzQ ↦ by
      have hψ_eq_one : ψ z = 1 := (hψ_one z).1 hzQ
      simp [φ, hψ_eq_one]
  exact hcutoff_int_Q.congr hcutoff_eq

/--
%%handwave
name:
  Directional weak derivatives are locally integrable
statement:
  On an open Euclidean region, each directional weak derivative of a scalar
  weak Sobolev function is locally integrable.
proof:
  Local integrability on an open set is equivalent to integrability on every
  compact subset of that open set.  Apply the compact integrability theorem.
-/
theorem scalarWeakSobolev_directionalDerivative_locallyIntegrableOn
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Ω : Set H} (hΩ_open : IsOpen Ω)
    {u : H → ℝ} {du : H → H →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionScalar Ω u du)
    (h : H) :
    LocallyIntegrableOn (fun z ↦ du z h) Ω
      (MeasureTheory.volume : Measure H) := by
  rw [locallyIntegrableOn_iff hΩ_open.isLocallyClosed]
  intro K hKΩ hK
  exact scalarWeakSobolev_directionalDerivative_integrableOn_compact
    hK hKΩ hΩ_open hweak

/--
%%handwave
name:
  Weak Sobolev functions are locally integrable on compact subsets
statement:
  On every compact subset of an open Euclidean region, a scalar weak
  Sobolev function is integrable, provided the weak derivative identity is
  tested in one nonzero direction.
proof:
  Choose a continuous linear coordinate \(\ell\) with \(\ell(h)=1\).  Around
  the compact set choose a smooth cutoff \(\chi\) which is identically one on
  a small open neighborhood of the compact set and whose support is contained
  in the region.  The test function \(\varphi=\chi\,\ell\) is compactly
  supported in the region and satisfies \(D\varphi(h)=1\) on the compact set.
  The weak-derivative definition gives integrability of
  \(D\varphi(h)u\); restricting to the compact set gives integrability of
  \(u\).
-/
theorem scalarWeakSobolev_function_integrableOn_compact_of_nonzero_direction
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Q Ω : Set H} (hQ : IsCompact Q)
    (hQΩ : Q ⊆ Ω) (hΩ_open : IsOpen Ω)
    {u : H → ℝ} {du : H → H →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionScalar Ω u du)
    {h : H} (hh : h ≠ 0) :
    Integrable u (MeasureTheory.volume.restrict Q) := by
  obtain ⟨L, hLh⟩ := SeparatingDual.exists_eq_one (R := ℝ) hh
  obtain ⟨δ, hδ_pos, hδΩ⟩ :=
    hQ.exists_cthickening_subset_open hΩ_open hQΩ
  let η : ℝ := δ / 2
  have hη_pos : 0 < η := by
    dsimp [η]
    linarith
  have hη_ltδ : η < δ := by
    dsimp [η]
    linarith
  have hclosed_eta : IsClosed (Metric.cthickening η Q) :=
    Metric.isClosed_cthickening
  have heta_subset_thickening :
      Metric.cthickening η Q ⊆ Metric.thickening δ Q :=
    Metric.cthickening_subset_thickening' hδ_pos hη_ltδ Q
  obtain ⟨χ, hχ_smooth, _hχ_range, hχ_support, hχ_one⟩ :=
    exists_contMDiff_support_eq_eq_one_iff
      (I := 𝓘(ℝ, H)) (n := ⊤)
      (Metric.isOpen_thickening) hclosed_eta heta_subset_thickening
  have hχ_tsupport_subset_cthickening :
      tsupport χ ⊆ Metric.cthickening δ Q := by
    rw [tsupport, hχ_support]
    exact Metric.closure_thickening_subset_cthickening δ Q
  have hχ_deriv_zero :
      ∀ z ∈ Q, fderiv ℝ χ z = 0 := by
    intro z hzQ
    have hz_thick : z ∈ Metric.thickening η Q :=
      Metric.self_subset_thickening hη_pos Q hzQ
    have hnhds : Metric.thickening η Q ∈ 𝓝 z :=
      Metric.isOpen_thickening.mem_nhds hz_thick
    have hχ_eventually :
        χ =ᶠ[𝓝 z] fun _ : H ↦ (1 : ℝ) := by
      filter_upwards [hnhds] with y hy
      exact (hχ_one y).1 ((Metric.thickening_subset_cthickening η Q) hy)
    rw [Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hχ_eventually]
    simp
  let φ : SmoothCompactlySupportedManifoldCoordinateFunction Ω :=
    { toFun := fun z : H ↦ χ z * L z
      smooth := by
        exact hχ_smooth.contDiff.mul L.contDiff
      support_subset := by
        exact (tsupport_mul_subset_left (f := χ) (g := fun z : H ↦ L z)).trans
          (hχ_tsupport_subset_cthickening.trans hδΩ)
      compact_support := by
        exact IsCompact.of_isClosed_subset (hQ.cthickening)
          (isClosed_tsupport _) ((tsupport_mul_subset_left
            (f := χ) (g := fun z : H ↦ L z)).trans hχ_tsupport_subset_cthickening) }
  have hφ_deriv_one :
      ∀ z ∈ Q, fderiv ℝ (φ : H → ℝ) z h = 1 := by
    intro z hzQ
    have hχz : χ z = 1 := by
      exact (hχ_one z).1 (Metric.self_subset_cthickening Q hzQ)
    have hχdiff : DifferentiableAt ℝ χ z :=
      (hχ_smooth.contDiff.differentiable (by simp)) z
    have hLdiff : DifferentiableAt ℝ (fun y : H ↦ L y) z :=
      L.isBoundedLinearMap.differentiableAt
    have hLfderiv : fderiv ℝ (fun y : H ↦ L y) z = L :=
      L.isBoundedLinearMap.fderiv
    change fderiv ℝ (fun y : H ↦ χ y * L y) z h = 1
    rw [fderiv_fun_mul hχdiff hLdiff]
    simp [hχz, hχ_deriv_zero z hzQ, hLfderiv, hLh]
  have htest_int : Integrable (fun z ↦ (fderiv ℝ (φ : H → ℝ) z h) • u z)
      (MeasureTheory.volume.restrict Ω) :=
    (hweak φ h).1
  have htest_int_Q : Integrable (fun z ↦ (fderiv ℝ (φ : H → ℝ) z h) • u z)
      (MeasureTheory.volume.restrict Q) := by
    have hres := htest_int.restrict (s := Q)
    simpa [Measure.restrict_restrict_of_subset hQΩ] using hres
  have htest_eq :
      (fun z ↦ (fderiv ℝ (φ : H → ℝ) z h) • u z)
        =ᵐ[MeasureTheory.volume.restrict Q] u := by
    exact ae_restrict_of_forall_mem hQ.measurableSet fun z hzQ ↦ by
      simp [hφ_deriv_one z hzQ]
  exact htest_int_Q.congr htest_eq

/--
%%handwave
name:
  Weak Sobolev functions are locally integrable
statement:
  On an open Euclidean region, a scalar weak Sobolev function is locally
  integrable.
proof:
  Local integrability on an open set is equivalent to integrability on every
  compact subset of the open set.  Apply the compact integrability theorem.
-/
theorem scalarWeakSobolev_function_locallyIntegrableOn_of_nonzero_direction
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Ω : Set H} (hΩ_open : IsOpen Ω)
    {u : H → ℝ} {du : H → H →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionScalar Ω u du)
    {h : H} (hh : h ≠ 0) :
    LocallyIntegrableOn u Ω (MeasureTheory.volume : Measure H) := by
  rw [locallyIntegrableOn_iff hΩ_open.isLocallyClosed]
  intro K hKΩ hK
  exact scalarWeakSobolev_function_integrableOn_compact_of_nonzero_direction
    hK hKΩ hΩ_open hweak hh

/--
%%handwave
name:
  Finite \(L^2\) seminorm gives \(L^2\) membership for weak Sobolev functions
statement:
  On a compact subset of an open Euclidean region, if a scalar weak Sobolev
  function has finite \(L^2\) seminorm, then it belongs to \(L^2\) there.
proof:
  Local integrability gives almost-everywhere strong measurability on the
  compact set, and the finite seminorm assumption gives the \(L^2\) bound.
-/
theorem scalarWeakSobolev_function_memLp_of_eLpNorm_ne_top
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Q Ω : Set H} (hQ : IsCompact Q)
    (hQΩ : Q ⊆ Ω) (hΩ_open : IsOpen Ω)
    {u : H → ℝ} {du : H → H →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionScalar Ω u du)
    {h : H} (hh : h ≠ 0)
    (hfinite : eLpNorm u 2
      (MeasureTheory.volume.restrict Q) ≠ (∞ : ℝ≥0∞)) :
    MemLp u 2 (MeasureTheory.volume.restrict Q) := by
  have hu_int : Integrable u (MeasureTheory.volume.restrict Q) :=
    scalarWeakSobolev_function_integrableOn_compact_of_nonzero_direction
      hQ hQΩ hΩ_open hweak hh
  exact ⟨hu_int.aestronglyMeasurable, lt_top_iff_ne_top.mpr hfinite⟩

/--
%%handwave
name:
  Directional weak derivatives are locally measurable when their \(L^2\)
  seminorm is finite
statement:
  On a compact set inside an open Euclidean region, a directional weak
  derivative with finite \(L^2\) seminorm is an \(L^2\) function on that
  compact set.
proof:
  Choose a smooth cutoff which is identically one on the compact set and whose
  support is contained in the open region.  The weak-derivative definition
  gives integrability, hence measurability, of the cutoff directional
  derivative.  Since the cutoff is one on the compact set, this gives
  measurability of the directional derivative there; the assumed finite
  seminorm gives the \(L^2\) bound.
-/
theorem scalarWeakSobolev_directionalDerivative_memLp_of_eLpNorm_ne_top
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Q Ω : Set H} (hQ : IsCompact Q)
    (hQΩ : Q ⊆ Ω) (hΩ_open : IsOpen Ω)
    {u : H → ℝ} {du : H → H →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionScalar Ω u du)
    {h : H}
    (hfinite : eLpNorm (fun z ↦ du z h) 2
      (MeasureTheory.volume.restrict Q) ≠ (∞ : ℝ≥0∞)) :
    MemLp (fun z ↦ du z h) 2 (MeasureTheory.volume.restrict Q) := by
  have hdu_int : Integrable (fun z ↦ du z h)
      (MeasureTheory.volume.restrict Q) :=
    scalarWeakSobolev_directionalDerivative_integrableOn_compact
      hQ hQΩ hΩ_open hweak
  exact ⟨hdu_int.aestronglyMeasurable,
    lt_top_iff_ne_top.mpr hfinite⟩

/--
%%handwave
name:
  Translates of compactly supported tests are compactly supported tests
statement:
  If a smooth compactly supported test is translated by a fixed vector and
  the translated closed support lies in an open region, then the translated
  function is again a smooth compactly supported test on that region.
proof:
  Translation is a smooth homeomorphism.  Smoothness follows by composition,
  the closed support is the inverse image of the original closed support, and
  compactness is preserved by homeomorphisms.
-/
def smoothCompactlySupportedManifoldCoordinateFunction_translate
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {U Ω : Set H} (ψ : SmoothCompactlySupportedManifoldCoordinateFunction U)
    (v : H)
    (hsupport : ∀ z ∈ tsupport (ψ : H → ℝ), z + v ∈ Ω) :
    SmoothCompactlySupportedManifoldCoordinateFunction Ω where
  toFun := (ψ : H → ℝ) ∘ (Homeomorph.addRight (-v))
  smooth := by
    have htranslate : ContDiff ℝ ∞ (fun z : H ↦ z + (-v)) :=
      contDiff_id.add contDiff_const
    simpa [Function.comp_def, sub_eq_add_neg] using ψ.smooth.comp htranslate
  support_subset := by
    intro z hz
    have hzpre : z + (-v) ∈ tsupport (ψ : H → ℝ) := by
      have h :=
        (Set.ext_iff.mp
          (tsupport_comp_eq_preimage (ψ : H → ℝ)
            (Homeomorph.addRight (-v))) z).mp hz
      simpa using h
    have hzΩ : (z + (-v)) + v ∈ Ω := hsupport (z + (-v)) hzpre
    simpa [add_assoc] using hzΩ
  compact_support := by
    rw [tsupport_comp_eq_preimage]
    exact (Homeomorph.addRight (-v)).isCompact_preimage.2 ψ.compact_support

/--
%%handwave
name:
  Value of a translated compactly supported test function
statement:
  If translating the support of a smooth test \(\psi\) by \(v\) stays in the
  target region, then its translated test satisfies
  \(\psi_v(z)=\psi(z-v)\).
proof:
  Unfold translation as composition with addition by \(-v\).
-/
@[simp]
theorem smoothCompactlySupportedManifoldCoordinateFunction_translate_apply
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {U Ω : Set H} (ψ : SmoothCompactlySupportedManifoldCoordinateFunction U)
    (v : H) (hsupport : ∀ z ∈ tsupport (ψ : H → ℝ), z + v ∈ Ω)
    (z : H) :
    (smoothCompactlySupportedManifoldCoordinateFunction_translate ψ v hsupport :
        SmoothCompactlySupportedManifoldCoordinateFunction Ω) z =
      ψ (z - v) := by
  simp [smoothCompactlySupportedManifoldCoordinateFunction_translate, sub_eq_add_neg]

/--
%%handwave
name:
  Derivative of a translated compactly supported test function
statement:
  For the translated test \(\psi_v(z)=\psi(z-v)\),
  \[D\psi_v(z)(h)=D\psi(z-v)(h).\]
proof:
  Differentiate composition with the translation \(z\mapsto z-v\), whose
  derivative is the identity.
-/
@[simp]
theorem smoothCompactlySupportedManifoldCoordinateFunction_translate_fderiv_apply
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {U Ω : Set H} (ψ : SmoothCompactlySupportedManifoldCoordinateFunction U)
    (v h z : H) (hsupport : ∀ z ∈ tsupport (ψ : H → ℝ), z + v ∈ Ω) :
    fderiv ℝ
        ((smoothCompactlySupportedManifoldCoordinateFunction_translate ψ v hsupport :
          SmoothCompactlySupportedManifoldCoordinateFunction Ω) : H → ℝ) z h =
      fderiv ℝ (ψ : H → ℝ) (z - v) h := by
  simp [smoothCompactlySupportedManifoldCoordinateFunction_translate,
    Function.comp_def, sub_eq_add_neg, fderiv_comp_add_right]

/--
%%handwave
name:
  The weak derivative identity applies to translated tests
statement:
  If translating the support of a smooth compactly supported test by a fixed
  vector keeps it inside the region, then the integration-by-parts identity
  for a weak derivative can be applied to that translated test.
proof:
  The translated test is a smooth compactly supported test on the region.
  Applying the weak derivative identity to it and rewriting the derivative of
  a translated smooth function gives the stated formula.
-/
theorem scalarWeakDerivativeOnEuclideanRegionScalar_translated_test
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    {U Ω : Set H} {u : H → ℝ} {du : H → H →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionScalar Ω u du)
    (ψ : SmoothCompactlySupportedManifoldCoordinateFunction U)
    (v h : H)
    (hsupport : ∀ z ∈ tsupport (ψ : H → ℝ), z + v ∈ Ω) :
    Integrable
        (fun z ↦ (fderiv ℝ (ψ : H → ℝ) (z - v) h) • u z)
        (MeasureTheory.volume.restrict Ω) ∧
      Integrable
        (fun z ↦ (ψ (z - v)) • du z h)
        (MeasureTheory.volume.restrict Ω) ∧
        ∫ z in Ω,
            (fderiv ℝ (ψ : H → ℝ) (z - v) h) • u z ∂MeasureTheory.volume =
          -∫ z in Ω, (ψ (z - v)) • du z h ∂MeasureTheory.volume := by
  let φ : SmoothCompactlySupportedManifoldCoordinateFunction Ω :=
    smoothCompactlySupportedManifoldCoordinateFunction_translate ψ v hsupport
  have hφ := hweak φ h
  simpa [φ, smoothCompactlySupportedManifoldCoordinateFunction_translate,
    Function.comp_def, sub_eq_add_neg, fderiv_comp_add_right] using hφ

/--
%%handwave
name:
  Segment integral along a Euclidean direction
statement:
  The segment integral of a scalar function along the direction \(v\) from a
  point \(z\) is the integral over \(0\le t\le1\) of the absolute value of the
  function at \(z+t v\).
-/
noncomputable def euclideanSegmentIntegralAlong {H : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (f : H → ℝ) (v z : H) : ℝ :=
  ∫ t in Set.Icc (0 : ℝ) 1, ‖f (z + t • v)‖ ∂MeasureTheory.volume

/--
%%handwave
name:
  Segment maps preserve null sets
statement:
  If every segment \(x+t h\), \(x\in K\), \(0\le t\le1\), remains in \(Q\),
  then the map \((x,t)\mapsto x+t h\) sends null sets in \(Q\) to null sets
  when pulled back to \(K\times[0,1]\).
proof:
  For almost every \(t\in[0,1]\), the map \(x\mapsto x+t h\) is a Euclidean
  translation, hence preserves null sets.  The containment hypothesis turns
  this into a restricted null-set-preserving map from \(K\) to \(Q\), and the
  product criterion gives the segment map.
-/
theorem euclideanSegmentMap_quasiMeasurePreserving_restrict_prod
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {K Q : Set H} {h : H}
    (hsegments : ∀ x ∈ K, ∀ t : ℝ, t ∈ Set.Icc 0 1 → x + t • h ∈ Q) :
    Measure.QuasiMeasurePreserving
      (fun p : H × ℝ ↦ p.1 + p.2 • h)
      ((MeasureTheory.volume.restrict K).prod
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)))
      (MeasureTheory.volume.restrict Q) := by
  refine MeasureTheory.QuasiMeasurePreserving.prod_of_left
    (τ := MeasureTheory.volume.restrict Q) ?_ ?_
  · fun_prop
  · filter_upwards [ae_restrict_mem
      (measurableSet_Icc : MeasurableSet (Set.Icc (0 : ℝ) 1))] with t ht
    have hmap : Set.MapsTo (fun z : H ↦ z + t • h) K Q := by
      intro z hz
      exact hsegments z hz t ht
    exact
      (MeasureTheory.measurePreserving_add_right
        (MeasureTheory.volume : Measure H) (t • h)).quasiMeasurePreserving.restrict hmap

/--
%%handwave
name:
  Square of an integral on a probability space
statement:
  If \(\mu(\alpha)=1\) and \(g\) is strongly measurable, then
  \[\left\lVert\int g\,d\mu\right\rVert_{\!e}^{\,2}
    \le\int\lVert g\rVert_{\!e}^{\,2}\,d\mu.\]
proof:
  Bound the norm of the integral by the integral of the norm, apply
  Hölder with exponents \(2,2\), and use that the \(L^2\)-norm of \(1\) is one.
-/
private theorem enorm_integral_sq_le_lintegral_enorm_sq_of_measure_univ_eq_one
    {α : Type} [MeasurableSpace α] {μ : Measure α}
    {g : α → ℝ} (hμ : μ Set.univ = 1)
    (hg : AEStronglyMeasurable g μ) :
    ‖∫ x, g x ∂μ‖ₑ ^ (2 : ℝ) ≤
      ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂μ := by
  have hnorm :
      ‖∫ x, g x ∂μ‖ₑ ≤ ∫⁻ x, ‖g x‖ₑ ∂μ :=
    MeasureTheory.enorm_integral_le_lintegral_enorm g
  have hholder :
      ∫⁻ x, ‖g x‖ₑ ∂μ ≤
        (∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂μ) ^ ((2 : ℝ)⁻¹) := by
    have hH : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
    have h :=
      ENNReal.lintegral_mul_le_Lp_mul_Lq
        (μ := μ) (p := (2 : ℝ)) (q := (2 : ℝ))
        (f := fun x ↦ ‖g x‖ₑ) (g := fun _x ↦ (1 : ℝ≥0∞))
        hH hg.enorm aemeasurable_const
    simpa [hμ, one_div] using h
  exact (ENNReal.le_rpow_inv_iff (by norm_num : 0 < (2 : ℝ))).1
    (hnorm.trans hholder)

/--
%%handwave
name:
  Segment square integrals are bounded after translating the compact set
statement:
  If every segment \(x+t h\), \(x\in K\), \(0\le t\le1\), remains in \(Q\),
  then
  \[
    \int_0^1\int_K |f(x+t h)|^2\,dx\,dt
      \le \int_Q |f(y)|^2\,dy .
  \]
proof:
  For each fixed \(t\), translation by \(t h\) preserves Euclidean volume and
  sends \(K\) into \(Q\), so the translated spatial integral over \(K\) is
  bounded by the integral over \(Q\).  Integrating this bound over
  \(0\le t\le1\) gives the result because the interval has length one.
-/
theorem euclideanSegmentIntegral_iterated_lintegral_sq_le_of_segments
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {K Q : Set H} {f : H → ℝ} {h : H}
    (hsegments : ∀ x ∈ K, ∀ t : ℝ, t ∈ Set.Icc 0 1 → x + t • h ∈ Q) :
    ∫⁻ t in Set.Icc (0 : ℝ) 1,
        ∫⁻ z in K, ‖f (z + t • h)‖ₑ ^ (2 : ℝ) ∂MeasureTheory.volume
        ∂MeasureTheory.volume ≤
      ∫⁻ z in Q, ‖f z‖ₑ ^ (2 : ℝ) ∂MeasureTheory.volume := by
  let F : H → ℝ≥0∞ := fun z ↦ ‖f z‖ₑ ^ (2 : ℝ)
  have hslice :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ∫⁻ z in K, F (z + t • h) ∂MeasureTheory.volume ≤
          ∫⁻ z in Q, F z ∂MeasureTheory.volume := by
    intro t ht
    let τ : H → H := fun z ↦ z + t • h
    have hτ_mp :
        MeasurePreserving τ MeasureTheory.volume MeasureTheory.volume := by
      simpa [τ] using
        (MeasureTheory.measurePreserving_add_right
          (MeasureTheory.volume : Measure H) (t • h))
    have hτ_emb : MeasurableEmbedding τ := by
      simpa [τ] using
        (Homeomorph.addRight (t • h)).isClosedEmbedding.measurableEmbedding
    have hτ_image : τ '' K ⊆ Q := by
      rintro y ⟨x, hxK, rfl⟩
      exact hsegments x hxK t ht
    calc
      ∫⁻ z in K, F (z + t • h) ∂MeasureTheory.volume
          = ∫⁻ z in K, F (τ z) ∂MeasureTheory.volume := rfl
      _ = ∫⁻ y in τ '' K, F y ∂MeasureTheory.volume :=
            hτ_mp.setLIntegral_comp_emb hτ_emb F K
      _ ≤ ∫⁻ y in Q, F y ∂MeasureTheory.volume :=
            lintegral_mono_set hτ_image
  calc
    ∫⁻ t in Set.Icc (0 : ℝ) 1,
        ∫⁻ z in K, ‖f (z + t • h)‖ₑ ^ (2 : ℝ) ∂MeasureTheory.volume
        ∂MeasureTheory.volume
        = ∫⁻ t in Set.Icc (0 : ℝ) 1,
            ∫⁻ z in K, F (z + t • h) ∂MeasureTheory.volume
            ∂MeasureTheory.volume := rfl
    _ ≤ ∫⁻ _t in Set.Icc (0 : ℝ) 1,
          ∫⁻ z in Q, F z ∂MeasureTheory.volume ∂MeasureTheory.volume :=
          setLIntegral_mono' measurableSet_Icc hslice
    _ = ∫⁻ z in Q, F z ∂MeasureTheory.volume := by
          simp [Real.volume_Icc]

/--
%%handwave
name:
  Segment averages are bounded by iterated square integrals
statement:
  For a square-integrable function, the square of the segment average is
  bounded in integral by the iterated integral of the pointwise square:
  \[
    \int_K \left(\int_0^1 |f(x+t h)|\,dt\right)^2 dx
      \le \int_0^1\int_K |f(x+t h)|^2 dx\,dt .
  \]
proof:
  Cauchy--Schwarz on the unit interval gives the pointwise bound for almost
  every base point for which the sliced function is measurable and integrable.
  Tonelli's theorem supplies those good base points and then integrates the
  pointwise inequality over \(K\).
-/
theorem euclideanSegmentIntegral_lintegral_sq_le_iterated_lintegral_sq
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {K Q : Set H} (_hK : IsCompact K) (_hQ : IsCompact Q)
    {f : H → ℝ} {h : H}
    (hf : MemLp f 2 (MeasureTheory.volume.restrict Q))
    (hsegments : ∀ x ∈ K, ∀ t : ℝ, t ∈ Set.Icc 0 1 → x + t • h ∈ Q) :
    ∫⁻ z, ‖euclideanSegmentIntegralAlong f h z‖ₑ ^ (2 : ℝ)
        ∂MeasureTheory.volume.restrict K ≤
      ∫⁻ t in Set.Icc (0 : ℝ) 1,
        ∫⁻ z in K, ‖f (z + t • h)‖ₑ ^ (2 : ℝ) ∂MeasureTheory.volume
        ∂MeasureTheory.volume := by
  let μK : Measure H := MeasureTheory.volume.restrict K
  let μI : Measure ℝ := MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)
  let G : H × ℝ → ℝ := fun p ↦ ‖f (p.1 + p.2 • h)‖
  have hμI_univ : μI Set.univ = 1 := by
    simp [μI, Real.volume_Icc]
  have hqmp :
      Measure.QuasiMeasurePreserving
        (fun p : H × ℝ ↦ p.1 + p.2 • h)
        (μK.prod μI) (MeasureTheory.volume.restrict Q) := by
    simpa [μK, μI] using
      euclideanSegmentMap_quasiMeasurePreserving_restrict_prod
        (H := H) (K := K) (Q := Q) (h := h) hsegments
  have hG_ae : AEStronglyMeasurable G (μK.prod μI) := by
    exact hf.aestronglyMeasurable.norm.comp_quasiMeasurePreserving hqmp
  have hGsq_ae :
      AEMeasurable (fun p : H × ℝ ↦ ‖G p‖ₑ ^ (2 : ℝ)) (μK.prod μI) :=
    hG_ae.enorm.pow_const _
  have hslices :
      ∀ᵐ z ∂μK, AEStronglyMeasurable (fun t : ℝ ↦ G (z, t)) μI :=
    hG_ae.prodMk_left
  have hpoint :
      ∀ᵐ z ∂μK,
        ‖∫ t, G (z, t) ∂μI‖ₑ ^ (2 : ℝ) ≤
          ∫⁻ t, ‖G (z, t)‖ₑ ^ (2 : ℝ) ∂μI := by
    filter_upwards [hslices] with z hz
    exact
      enorm_integral_sq_le_lintegral_enorm_sq_of_measure_univ_eq_one
        hμI_univ hz
  calc
    ∫⁻ z, ‖euclideanSegmentIntegralAlong f h z‖ₑ ^ (2 : ℝ) ∂MeasureTheory.volume.restrict K
        = ∫⁻ z, ‖∫ t, G (z, t) ∂μI‖ₑ ^ (2 : ℝ) ∂μK := by
          simp [euclideanSegmentIntegralAlong, μK, μI, G]
    _ ≤ ∫⁻ z, ∫⁻ t, ‖G (z, t)‖ₑ ^ (2 : ℝ) ∂μI ∂μK :=
          lintegral_mono_ae hpoint
    _ = ∫⁻ t, ∫⁻ z, ‖G (z, t)‖ₑ ^ (2 : ℝ) ∂μK ∂μI := by
          exact MeasureTheory.lintegral_lintegral_swap
            (μ := μK) (ν := μI)
            (f := fun z t ↦ ‖G (z, t)‖ₑ ^ (2 : ℝ)) hGsq_ae
    _ = ∫⁻ t in Set.Icc (0 : ℝ) 1,
          ∫⁻ z in K, ‖f (z + t • h)‖ₑ ^ (2 : ℝ) ∂MeasureTheory.volume
          ∂MeasureTheory.volume := by
          simp [μK, μI, G]

/--
%%handwave
name:
  Segment averages satisfy the \(L^2\) square estimate
statement:
  If every segment \(x+t h\), \(x\in K\), \(0\le t\le1\), remains in \(Q\),
  then
  \[
    \int_K \left(\int_0^1 |f(x+t h)|\,dt\right)^2\,dx
      \le \int_Q |f(y)|^2\,dy .
  \]
proof:
  Jensen's inequality for the probability measure on \([0,1]\) gives the
  pointwise estimate by the time average of \(|f(x+t h)|^2\).  Tonelli swaps
  the \(x\)- and \(t\)-integrals.  For each fixed \(t\), translation by
  \(t h\) preserves Euclidean measure and maps \(K\) into \(Q\), so the
  spatial integral is bounded by the integral over \(Q\).  The interval has
  measure one.
-/
theorem euclideanSegmentIntegral_lintegral_sq_le_of_segments
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {K Q : Set H} (hK : IsCompact K) (hQ : IsCompact Q)
    {f : H → ℝ} {h : H}
    (hf : MemLp f 2 (MeasureTheory.volume.restrict Q))
    (hsegments : ∀ x ∈ K, ∀ t : ℝ, t ∈ Set.Icc 0 1 → x + t • h ∈ Q) :
    ∫⁻ z, ‖euclideanSegmentIntegralAlong f h z‖ₑ ^ (2 : ℝ)
        ∂MeasureTheory.volume.restrict K ≤
      ∫⁻ z, ‖f z‖ₑ ^ (2 : ℝ) ∂MeasureTheory.volume.restrict Q := by
  calc
    ∫⁻ z, ‖euclideanSegmentIntegralAlong f h z‖ₑ ^ (2 : ℝ)
        ∂MeasureTheory.volume.restrict K
        ≤ ∫⁻ t in Set.Icc (0 : ℝ) 1,
            ∫⁻ z in K, ‖f (z + t • h)‖ₑ ^ (2 : ℝ) ∂MeasureTheory.volume
            ∂MeasureTheory.volume :=
          euclideanSegmentIntegral_lintegral_sq_le_iterated_lintegral_sq
            hK hQ hf hsegments
    _ ≤ ∫⁻ z in Q, ‖f z‖ₑ ^ (2 : ℝ) ∂MeasureTheory.volume :=
          euclideanSegmentIntegral_iterated_lintegral_sq_le_of_segments
            hsegments

/--
%%handwave
name:
  Almost everywhere equality transfers to segment endpoint differences
statement:
  Let \(K\) and \(Q\) be subsets of a finite-dimensional Euclidean space, and
  let every segment \(x+t h\), \(x\in K\), \(0\le t\le1\), lie in \(Q\).
  If two scalar functions agree almost everywhere on \(Q\), then their
  endpoint differences along the displacement \(h\) agree almost everywhere
  on \(K\):
  \[
    u(x+h)-u(x)=v(x+h)-v(x)
  \]
  for almost every \(x\in K\).
proof:
  Agreement at the initial endpoint follows by restricting the null set from
  \(Q\) to \(K\).  Agreement at the translated endpoint follows from
  translation invariance of Euclidean volume, because \(x\mapsto x+h\) sends
  \(K\) into \(Q\).  Subtract the two endpoint equalities.
-/
theorem ae_eq_endpoint_difference_of_ae_eq_on_segments
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {K Q : Set H} {u v : H → ℝ} {h : H}
    (huv : v =ᵐ[MeasureTheory.volume.restrict Q] u)
    (hsegments : ∀ x ∈ K, ∀ t : ℝ, t ∈ Set.Icc 0 1 → x + t • h ∈ Q) :
    (fun z ↦ u (z + h) - u z) =ᵐ[MeasureTheory.volume.restrict K]
      fun z ↦ v (z + h) - v z := by
  have hKQ : K ⊆ Q := by
    intro x hx
    simpa using hsegments x hx 0 (by simp)
  have hKhQ : Set.MapsTo (fun z : H ↦ z + h) K Q := by
    intro x hx
    simpa using hsegments x hx 1 (by simp)
  have hbase :
      u =ᵐ[MeasureTheory.volume.restrict K] v :=
    Filter.EventuallyEq.symm (ae_restrict_of_ae_restrict_of_subset hKQ huv)
  have htranslate_qmp :
      Measure.QuasiMeasurePreserving (fun z : H ↦ z + h)
        (MeasureTheory.volume.restrict K) (MeasureTheory.volume.restrict Q) :=
    (MeasureTheory.measurePreserving_add_right (MeasureTheory.volume : Measure H) h).quasiMeasurePreserving.restrict
      hKhQ
  have htranslate :
      (fun z : H ↦ u (z + h)) =ᵐ[MeasureTheory.volume.restrict K]
        fun z ↦ v (z + h) := by
    simpa [Function.comp_def] using
      Filter.EventuallyEq.symm (htranslate_qmp.ae_eq_comp huv)
  exact htranslate.comp₂ (fun a b : ℝ ↦ a - b) hbase

/--
%%handwave
name:
  A nonzero direction can be made the first coordinate direction
statement:
  Let \(H\) be a finite-dimensional real normed vector space and let
  \(h\ne0\).  Then there is an integer \(d\) and a continuous linear
  coordinate equivalence
  \[
    H \simeq \mathbb R\times\mathbb R^d
  \]
  which sends \(h\) to \((1,0)\).
proof:
  Choose a linear functional \(\ell\) with \(\ell(h)=1\), extend \(h\) to a
  basis of \(H\), and use the remaining basis vectors as coordinates on a
  complementary subspace.  In finite dimension all linear maps between
  normed spaces are continuous.
-/
theorem exists_continuousLinearEquiv_apply_nonzero_eq_firstCoordinate
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [FiniteDimensional ℝ H] {h : H} (hh_ne : h ≠ 0) :
    ∃ d : ℕ, ∃ e : H ≃L[ℝ] (ℝ × (Fin d → ℝ)),
      e h = ((1 : ℝ), (0 : Fin d → ℝ)) := by
  classical
  let s : Set H := {h}
  have hs : LinearIndepOn ℝ id s := by
    simpa [s] using (LinearIndepOn.singleton (R := ℝ) (v := id) hh_ne)
  let J := hs.extend (Set.subset_univ s)
  let b : Module.Basis J ℝ H := Module.Basis.extend hs
  have hi0 : h ∈ J :=
    hs.subset_extend (Set.subset_univ s) (by simp [s])
  let i0 : J := ⟨h, hi0⟩
  let Tail : Type := ({j : J | j ≠ i0} : Type)
  haveI : Fintype J := FiniteDimensional.fintypeBasisIndex b
  haveI : Fintype Tail := inferInstance
  let d := Fintype.card Tail
  let r : Tail ≃ Fin d := Fintype.equivFin Tail
  let split : Unit ⊕ Tail ≃ J :=
    (Equiv.sumCongr (Equiv.Set.singleton i0).symm (Equiv.refl Tail)).trans
      (Equiv.Set.sumCompl ({i0} : Set J))
  let eLin : H ≃ₗ[ℝ] ℝ × (Fin d → ℝ) :=
    b.equivFun.trans <|
      (LinearEquiv.piCongrLeft' ℝ (fun _ : J ↦ ℝ) split.symm).trans <|
        (LinearEquiv.sumArrowLequivProdArrow Unit Tail ℝ ℝ).trans <|
          (LinearEquiv.funUnique Unit ℝ ℝ).prodCongr
          (LinearEquiv.piCongrLeft' ℝ (fun _ : Tail ↦ ℝ) r)
  refine ⟨d, eLin.toContinuousLinearEquiv, ?_⟩
  have hb_first : b i0 = h := by
    change b i0 = (i0 : H)
    exact Module.Basis.extend_apply_self hs i0
  have hb_coord (j : J) :
      b.equivFun h j = if i0 = j then 1 else 0 := by
    rw [← hb_first]
    exact b.equivFun_self i0 j
  ext i
  · have hcoord : b.repr h (split (Sum.inl ())) = 1 := by
      have hsplit : split (Sum.inl ()) = i0 := by
        change (Equiv.Set.sumCompl ({i0} : Set J))
            (Sum.inl ((Equiv.Set.singleton i0).symm ())) = i0
        rw [Equiv.Set.sumCompl_apply_inl]
        rfl
      simpa [Module.Basis.equivFun_apply, hsplit] using
        hb_coord (split (Sum.inl ()))
    simpa [eLin, Module.Basis.equivFun_apply] using hcoord
  · have htail_ne : i0 ≠ ((r.symm i : Tail) : J) :=
      Ne.symm (r.symm i).property
    have hcoord : b.repr h (split (Sum.inr (r.symm i))) = 0 := by
      have hsplit_tail :
          split (Sum.inr (r.symm i)) = ((r.symm i : Tail) : J) := by
        change (Equiv.Set.sumCompl ({i0} : Set J)) (Sum.inr (r.symm i)) =
          ((r.symm i : Tail) : J)
        rw [Equiv.Set.sumCompl_apply_inr]
      have hsplit_ne : i0 ≠ split (Sum.inr (r.symm i)) := by
        rwa [hsplit_tail]
      have h := hb_coord (split (Sum.inr (r.symm i)))
      rw [if_neg hsplit_ne] at h
      simpa [Module.Basis.equivFun_apply] using h
    simpa [eLin, Module.Basis.equivFun_apply] using hcoord

/--
%%handwave
name:
  Vertical fibers of subsets of product Euclidean space
statement:
  For a set \(K\subset \mathbb R\times\mathbb R^d\) and a transverse
  coordinate \(y\in\mathbb R^d\), its vertical fiber is the set of real
  numbers \(a\) such that \((a,y)\in K\).
-/
def firstCoordinateVerticalFiber {d : ℕ}
    (K : Set (ℝ × (Fin d → ℝ))) (y : Fin d → ℝ) : Set ℝ :=
  {a | (a, y) ∈ K}

/--
%%handwave
name:
  Vertical fibers are monotone under set inclusion
statement:
  If \(K\subset Q\), then every vertical fiber of \(K\) is contained in the
  corresponding vertical fiber of \(Q\).
proof:
  If a scalar lies in the fiber of (K), the corresponding product point lies in (K); inclusion puts it in (Q), hence in the fiber of (Q).
-/
theorem firstCoordinateVerticalFiber_mono {d : ℕ}
    {K Q : Set (ℝ × (Fin d → ℝ))}
    (hKQ : K ⊆ Q) (y : Fin d → ℝ) :
    firstCoordinateVerticalFiber K y ⊆ firstCoordinateVerticalFiber Q y := by
  intro a ha
  exact hKQ ha

/--
%%handwave
name:
  Closed product sets have closed vertical fibers
statement:
  A vertical section of a closed subset of
  \(\mathbb R\times\mathbb R^d\) is closed in \(\mathbb R\).
proof:
  The fiber is the preimage of the closed set under the continuous map \(t\mapsto(t,y)\).
-/
theorem firstCoordinateVerticalFiber_isClosed {d : ℕ}
    {K : Set (ℝ × (Fin d → ℝ))} (hK : IsClosed K)
    (y : Fin d → ℝ) :
    IsClosed (firstCoordinateVerticalFiber K y) := by
  have hcont : Continuous (fun a : ℝ ↦ ((a, y) : ℝ × (Fin d → ℝ))) := by
    fun_prop
  exact hK.preimage hcont

/--
%%handwave
name:
  Open product sets have open vertical fibers
statement:
  A vertical section of an open subset of
  \(\mathbb R\times\mathbb R^d\) is open in \(\mathbb R\).
proof:
  The fiber is the preimage of the open set under the continuous embedding \(t\mapsto(t,y)\).
-/
theorem firstCoordinateVerticalFiber_isOpen {d : ℕ}
    {Ω : Set (ℝ × (Fin d → ℝ))} (hΩ : IsOpen Ω)
    (y : Fin d → ℝ) :
    IsOpen (firstCoordinateVerticalFiber Ω y) := by
  have hcont : Continuous (fun a : ℝ ↦ ((a, y) : ℝ × (Fin d → ℝ))) := by
    fun_prop
  exact hΩ.preimage hcont

/--
%%handwave
name:
  Fiber tests have product neighborhoods inside the region
statement:
  Let \(\Omega\subset \mathbb R\times\mathbb R^d\) be open.  If
  \(\varphi\) is a smooth compactly supported test on the vertical fiber
  \(\Omega_y\), then there are open sets \(U\subset\mathbb R\) and
  \(V\subset\mathbb R^d\), with \(y\in V\), such that the closed support of
  \(\varphi\) is contained in \(U\) and \(U\times V\subset\Omega\).
proof:
  The compact set \(\operatorname{supp}\varphi\times\{y\}\) lies in
  \(\Omega\).  Apply the tube lemma for compact subsets of a product.
-/
theorem firstCoordinateVerticalFiber_test_exists_product_tube {d : ℕ}
    {Ω : Set (ℝ × (Fin d → ℝ))} (hΩ : IsOpen Ω)
    (y : Fin d → ℝ)
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction
      (firstCoordinateVerticalFiber Ω y)) :
    ∃ U : Set ℝ, ∃ V : Set (Fin d → ℝ),
      IsOpen U ∧ IsOpen V ∧ y ∈ V ∧
        tsupport (φ : ℝ → ℝ) ⊆ U ∧ U ×ˢ V ⊆ Ω := by
  have hprod_subset :
      tsupport (φ : ℝ → ℝ) ×ˢ ({y} : Set (Fin d → ℝ)) ⊆ Ω := by
    rintro ⟨a, y'⟩ ⟨ha, hy'⟩
    have hy_eq : y' = y := by simpa using hy'
    subst y'
    exact φ.support_subset ha
  rcases generalized_tube_lemma φ.compact_support isCompact_singleton
      hΩ hprod_subset with
    ⟨U, V, hU_open, hV_open, hφU, hyV, hUV⟩
  exact ⟨U, V, hU_open, hV_open, hyV (by simp), hφU, hUV⟩

/--
%%handwave
name:
  Fiber tests extend to tests on a one-dimensional neighborhood
statement:
  Under the same hypotheses, the test function on the fiber may be viewed as
  a smooth compactly supported test on an open one-dimensional set \(U\),
  with an open transverse neighborhood \(V\) of the fiber parameter such that
  \(U\times V\subset\Omega\).
proof:
  Use [a product neighborhood of the fiber support inside the region](lean:JJMath.Uniformization.firstCoordinateVerticalFiber_test_exists_product_tube),
  and keep the same underlying smooth function.
-/
theorem firstCoordinateVerticalFiber_test_exists_product_tube_test {d : ℕ}
    {Ω : Set (ℝ × (Fin d → ℝ))} (hΩ : IsOpen Ω)
    (y : Fin d → ℝ)
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction
      (firstCoordinateVerticalFiber Ω y)) :
    ∃ U : Set ℝ, ∃ V : Set (Fin d → ℝ),
      ∃ φU : SmoothCompactlySupportedManifoldCoordinateFunction U,
        IsOpen U ∧ IsOpen V ∧ y ∈ V ∧ U ×ˢ V ⊆ Ω ∧
          (φU : ℝ → ℝ) = φ := by
  rcases firstCoordinateVerticalFiber_test_exists_product_tube hΩ y φ with
    ⟨U, V, hU_open, hV_open, hyV, hφU, hUV⟩
  let φU : SmoothCompactlySupportedManifoldCoordinateFunction U :=
    { toFun := φ
      smooth := φ.smooth
      support_subset := hφU
      compact_support := φ.compact_support }
  exact ⟨U, V, φU, hU_open, hV_open, hyV, hUV, rfl⟩

/--
%%handwave
name:
  Compact product sets have compact vertical fibers
statement:
  A vertical section of a compact subset of
  \(\mathbb R\times\mathbb R^d\) is compact in \(\mathbb R\).
proof:
  The fiber is closed, and it is contained in the first-coordinate projection
  of the compact set.
-/
theorem firstCoordinateVerticalFiber_isCompact {d : ℕ}
    {K : Set (ℝ × (Fin d → ℝ))} (hK : IsCompact K)
    (y : Fin d → ℝ) :
    IsCompact (firstCoordinateVerticalFiber K y) := by
  have hproj : IsCompact (Prod.fst '' K) :=
    hK.image continuous_fst
  have hclosed : IsClosed (firstCoordinateVerticalFiber K y) :=
    firstCoordinateVerticalFiber_isClosed hK.isClosed y
  have hsub : firstCoordinateVerticalFiber K y ⊆ Prod.fst '' K := by
    intro a ha
    exact ⟨(a, y), ha, rfl⟩
  exact IsCompact.of_isClosed_subset hproj hclosed hsub

/--
%%handwave
name:
  Product vertical segments restrict to fiber segments
statement:
  If every product segment \((a,y)+t e_1\), starting from \(K\), remains in
  \(Q\), then every one-dimensional segment \(a+t\), starting from the
  vertical fiber \(K_y\), remains in the corresponding fiber \(Q_y\).
proof:
  Translate membership in a vertical fiber into membership of the corresponding product point, apply the product-segment hypothesis, and translate back.
-/
theorem firstCoordinateVerticalFiber_segments {d : ℕ}
    {K Q : Set (ℝ × (Fin d → ℝ))}
    (hsegments :
      ∀ x ∈ K, ∀ t : ℝ, t ∈ Set.Icc 0 1 →
        x + t • ((1 : ℝ), (0 : Fin d → ℝ)) ∈ Q)
    (y : Fin d → ℝ) :
    ∀ a ∈ firstCoordinateVerticalFiber K y, ∀ t : ℝ, t ∈ Set.Icc 0 1 →
      a + t ∈ firstCoordinateVerticalFiber Q y := by
  intro a ha t ht
  have hq := hsegments ((a, y) : ℝ × (Fin d → ℝ)) ha t ht
  simpa [firstCoordinateVerticalFiber, Prod.ext_iff, smul_eq_mul, add_comm, add_left_comm,
    add_assoc] using hq

/--
%%handwave
name:
  The first-coordinate unit-segment image of a compact set is compact
statement:
  The set of all points \(x+t e_1\), with \(x\) in a compact set and
  \(0\le t\le1\), is compact.
proof:
  It is the continuous image of the compact product \(K\times[0,1]\) under \((x,t)\mapsto x+t e_1\).
-/
theorem firstCoordinate_unitSegmentImage_isCompact {d : ℕ}
    {K : Set (ℝ × (Fin d → ℝ))} (hK : IsCompact K) :
    IsCompact
      ((fun p : (ℝ × (Fin d → ℝ)) × ℝ ↦
          p.1 + p.2 • ((1 : ℝ), (0 : Fin d → ℝ))) ''
        (K ×ˢ Set.Icc (0 : ℝ) 1)) := by
  have hcont :
      Continuous (fun p : (ℝ × (Fin d → ℝ)) × ℝ ↦
        p.1 + p.2 • ((1 : ℝ), (0 : Fin d → ℝ))) := by
    fun_prop
  exact (hK.prod isCompact_Icc).image hcont

/--
%%handwave
name:
  Segment containment controls the first-coordinate unit-segment image
statement:
  If all vertical unit segments starting from \(K\) remain in \(Q\), then the
  compact image of those segments is contained in \(Q\).
proof:
  Every point of the segment image has the form (x+t e_1) with (xin K) and (tin[0,1]); apply the assumed segment containment.
-/
theorem firstCoordinate_unitSegmentImage_subset_of_segments {d : ℕ}
    {K Q : Set (ℝ × (Fin d → ℝ))}
    (hsegments :
      ∀ x ∈ K, ∀ t : ℝ, t ∈ Set.Icc 0 1 →
        x + t • ((1 : ℝ), (0 : Fin d → ℝ)) ∈ Q) :
    ((fun p : (ℝ × (Fin d → ℝ)) × ℝ ↦
        p.1 + p.2 • ((1 : ℝ), (0 : Fin d → ℝ))) ''
      (K ×ˢ Set.Icc (0 : ℝ) 1)) ⊆ Q := by
  intro z hz
  rcases hz with ⟨p, hp, rfl⟩
  exact hsegments p.1 hp.1 p.2 hp.2

/--
%%handwave
name:
  Compact vertical segments have an open tube inside the weak-derivative region
statement:
  If every vertical unit segment starting from a compact set \(K\) lies in a
  set \(Q\subset\Omega\), with \(\Omega\) open, then a small open thickening
  of \(K\) has all of its vertical unit segments contained in \(\Omega\).
proof:
  The union of the original compact family of segments is compact and lies in
  \(\Omega\).  Choose a positive closed metric thickening of this compact
  segment image inside \(\Omega\).  If \(z\) is sufficiently close to \(K\),
  then \(z+t e_1\) stays within that thickening of the original segment image.
-/
theorem firstCoordinate_exists_segment_tube {d : ℕ}
    {K Q Ω : Set (ℝ × (Fin d → ℝ))} (hK : IsCompact K)
    (hQΩ : Q ⊆ Ω) (hΩ_open : IsOpen Ω)
    (hsegments :
      ∀ x ∈ K, ∀ t : ℝ, t ∈ Set.Icc 0 1 →
        x + t • ((1 : ℝ), (0 : Fin d → ℝ)) ∈ Q) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ z ∈ Metric.thickening ρ K, ∀ t : ℝ, t ∈ Set.Icc 0 1 →
        z + t • ((1 : ℝ), (0 : Fin d → ℝ)) ∈ Ω := by
  let e : ℝ × (Fin d → ℝ) := ((1 : ℝ), (0 : Fin d → ℝ))
  let S : Set (ℝ × (Fin d → ℝ)) :=
    ((fun p : (ℝ × (Fin d → ℝ)) × ℝ ↦ p.1 + p.2 • e) ''
      (K ×ˢ Set.Icc (0 : ℝ) 1))
  have hS_compact : IsCompact S := by
    simpa [S, e] using firstCoordinate_unitSegmentImage_isCompact (d := d) hK
  have hSΩ : S ⊆ Ω := by
    intro z hz
    exact hQΩ (firstCoordinate_unitSegmentImage_subset_of_segments
      (d := d) (K := K) (Q := Q) hsegments (by simpa [S, e] using hz))
  obtain ⟨δ, hδ_pos, hδΩ⟩ :=
    hS_compact.exists_cthickening_subset_open hΩ_open hSΩ
  refine ⟨δ / 2, by positivity, fun z hzK t ht ↦ ?_⟩
  rcases Metric.mem_thickening_iff.mp hzK with ⟨x, hxK, hzx⟩
  have hx_segment : x + t • e ∈ S := by
    exact ⟨(x, t), ⟨hxK, ht⟩, rfl⟩
  have hdist_lt :
      dist (z + t • e) (x + t • e) < δ := by
    calc
      dist (z + t • e) (x + t • e) = dist z x := by
        simp [dist_eq_norm]
      _ < δ / 2 := hzx
      _ < δ := by linarith
  exact hδΩ (Metric.mem_cthickening_of_dist_le
    (z + t • e) (x + t • e) δ S hx_segment (le_of_lt hdist_lt))

/--
%%handwave
name:
  Fiberwise almost-everywhere statements recombine over vertical fibers
statement:
  Let \(K\subset\mathbb R\times\mathbb R^d\) be measurable.  Suppose the
  exceptional subset of \(K\) on which a property fails is measurable up to
  null sets.  If the property holds for almost every point of almost every
  vertical fiber of \(K\), then it holds for almost every point of \(K\).
proof:
  Euclidean measure on the product is the product measure.  The
  null-measurable exceptional set can be replaced by a measurable set equal
  to it up to a null set.  Fubini applied to this measurable exceptional set
  shows that it has zero product measure, because almost every vertical
  section has zero one-dimensional measure.  Restricting the product measure
  to \(K\) gives the claimed almost-everywhere statement.
-/
theorem ae_restrict_prod_of_ae_vertical_fibers
    {d : ℕ} {K : Set (ℝ × (Fin d → ℝ))}
    {P : (ℝ × (Fin d → ℝ)) → Prop}
    (hK : MeasurableSet K)
    (hbad :
      NullMeasurableSet {z : ℝ × (Fin d → ℝ) | z ∈ K ∧ ¬ P z}
        (MeasureTheory.volume : Measure (ℝ × (Fin d → ℝ))))
    (hfiber :
      ∀ᵐ y ∂(MeasureTheory.volume : Measure (Fin d → ℝ)),
        ∀ᵐ a ∂(MeasureTheory.volume.restrict (firstCoordinateVerticalFiber K y)),
          P (a, y)) :
    ∀ᵐ z ∂MeasureTheory.volume.restrict K, P z := by
  classical
  let bad : Set (ℝ × (Fin d → ℝ)) := {z | z ∈ K ∧ ¬ P z}
  let B : Set (ℝ × (Fin d → ℝ)) :=
    MeasureTheory.toMeasurable (MeasureTheory.volume : Measure (ℝ × (Fin d → ℝ))) bad
  have hBmeas : MeasurableSet B := by
    simp [B, measurableSet_toMeasurable
      (MeasureTheory.volume : Measure (ℝ × (Fin d → ℝ))) bad]
  have hBbad :
      B =ᵐ[(MeasureTheory.volume : Measure (ℝ × (Fin d → ℝ)))] bad := by
    simpa [B, bad] using
      (NullMeasurableSet.toMeasurable_ae_eq hbad)
  have hBbad_prod :
      B =ᵐ[((MeasureTheory.volume : Measure ℝ).prod
        (MeasureTheory.volume : Measure (Fin d → ℝ)))] bad := by
    simpa [Measure.volume_eq_prod] using hBbad
  have hBbad_swap :
      ∀ᵐ p ∂((MeasureTheory.volume : Measure (Fin d → ℝ)).prod
          (MeasureTheory.volume : Measure ℝ)),
        ((p.2, p.1) : ℝ × (Fin d → ℝ)) ∈ B ↔
          ((p.2, p.1) : ℝ × (Fin d → ℝ)) ∈ bad := by
    have h :=
      (Measure.measurePreserving_swap
        (μ := (MeasureTheory.volume : Measure (Fin d → ℝ)))
        (ν := (MeasureTheory.volume : Measure ℝ))).quasiMeasurePreserving.tendsto_ae
        hBbad_prod
    simpa [Filter.EventuallyEq, Prod.swap] using h
  have hBbad_slices :
      ∀ᵐ y ∂(MeasureTheory.volume : Measure (Fin d → ℝ)),
        ∀ᵐ a ∂(MeasureTheory.volume : Measure ℝ),
          ((a, y) : ℝ × (Fin d → ℝ)) ∈ B ↔
            ((a, y) : ℝ × (Fin d → ℝ)) ∈ bad := by
    simpa using Measure.ae_ae_of_ae_prod hBbad_swap
  have hnotbad_slices :
      ∀ᵐ y ∂(MeasureTheory.volume : Measure (Fin d → ℝ)),
        ∀ᵐ a ∂(MeasureTheory.volume : Measure ℝ),
          ((a, y) : ℝ × (Fin d → ℝ)) ∉ bad := by
    filter_upwards [hfiber] with y hy
    have hy_unrestricted :
        ∀ᵐ a ∂(MeasureTheory.volume : Measure ℝ),
          a ∈ firstCoordinateVerticalFiber K y → P (a, y) :=
      ae_imp_of_ae_restrict hy
    filter_upwards [hy_unrestricted] with a ha
    intro hb
    exact hb.2 (ha (by simpa [bad, firstCoordinateVerticalFiber] using hb.1))
  have hnotB_slices :
      ∀ᵐ y ∂(MeasureTheory.volume : Measure (Fin d → ℝ)),
        ∀ᵐ a ∂(MeasureTheory.volume : Measure ℝ),
          ((a, y) : ℝ × (Fin d → ℝ)) ∉ B := by
    filter_upwards [hnotbad_slices, hBbad_slices] with y hnotbad_y hBbad_y
    filter_upwards [hnotbad_y, hBbad_y] with a hnotbad_a hBbad_a
    intro hBmem
    exact hnotbad_a (hBbad_a.mp hBmem)
  have hnotB_swap_prod :
      ∀ᵐ p ∂((MeasureTheory.volume : Measure (Fin d → ℝ)).prod
          (MeasureTheory.volume : Measure ℝ)),
        ((p.2, p.1) : ℝ × (Fin d → ℝ)) ∉ B := by
    have hmeas :
        MeasurableSet
          {p : (Fin d → ℝ) × ℝ |
            ((p.2, p.1) : ℝ × (Fin d → ℝ)) ∉ B} := by
      change MeasurableSet (Prod.swap ⁻¹' Bᶜ)
      exact measurable_swap hBmeas.compl
    exact (Measure.ae_prod_iff_ae_ae hmeas).2 hnotB_slices
  have hnotB_prod :
      ∀ᵐ z ∂((MeasureTheory.volume : Measure ℝ).prod
          (MeasureTheory.volume : Measure (Fin d → ℝ))),
        z ∉ B := by
    have h :=
      (Measure.measurePreserving_swap
        (μ := (MeasureTheory.volume : Measure ℝ))
        (ν := (MeasureTheory.volume : Measure (Fin d → ℝ)))).quasiMeasurePreserving.tendsto_ae
        hnotB_swap_prod
    simpa [Prod.swap] using h
  have hB_zero :
      ((MeasureTheory.volume : Measure ℝ).prod
          (MeasureTheory.volume : Measure (Fin d → ℝ))) B = 0 := by
    simpa [ae_iff] using hnotB_prod
  have hbad_zero :
      (MeasureTheory.volume : Measure (ℝ × (Fin d → ℝ))) bad = 0 := by
    have hB_zero_volume :
        (MeasureTheory.volume : Measure (ℝ × (Fin d → ℝ))) B = 0 := by
      simpa [Measure.volume_eq_prod] using hB_zero
    change
        (MeasureTheory.volume : Measure (ℝ × (Fin d → ℝ)))
          (MeasureTheory.toMeasurable
            (MeasureTheory.volume : Measure (ℝ × (Fin d → ℝ))) bad) = 0 at hB_zero_volume
    rw [measure_toMeasurable] at hB_zero_volume
    simpa using hB_zero_volume
  rw [ae_iff, Measure.restrict_apply' hK]
  have hset : {z : ℝ × (Fin d → ℝ) | ¬ P z} ∩ K = bad := by
    ext z
    simp [bad, and_comm]
  rw [hset]
  exact hbad_zero

/--
%%handwave
name:
  Product almost-everywhere statements restrict to almost every vertical fiber
statement:
  If a statement holds for almost every point of a closed subset
  \(K\subset\mathbb R\times\mathbb R^d\), then for almost every transverse
  coordinate \(y\) it holds for almost every point of the vertical section
  \(K_y\).
proof:
  Rewrite Euclidean measure on the product as the product of one-dimensional
  and transverse Euclidean measure.  After swapping the product factors,
  Fubini gives the assertion on almost every vertical slice.  The restricted
  fiber measure is handled by restricting the resulting unrestricted
  almost-everywhere implication to the closed fiber.
-/
theorem ae_vertical_fibers_of_ae_restrict_prod
    {d : ℕ} {K : Set (ℝ × (Fin d → ℝ))}
    {P : (ℝ × (Fin d → ℝ)) → Prop}
    (hK : IsClosed K)
    (hprod : ∀ᵐ z ∂MeasureTheory.volume.restrict K, P z) :
    ∀ᵐ y ∂(MeasureTheory.volume : Measure (Fin d → ℝ)),
      ∀ᵐ a ∂(MeasureTheory.volume.restrict (firstCoordinateVerticalFiber K y)),
        P (a, y) := by
  have hprod_unrestricted :
      ∀ᵐ z ∂(MeasureTheory.volume : Measure (ℝ × (Fin d → ℝ))),
        z ∈ K → P z :=
    ae_imp_of_ae_restrict hprod
  have hprod_prod :
      ∀ᵐ z ∂((MeasureTheory.volume : Measure ℝ).prod
          (MeasureTheory.volume : Measure (Fin d → ℝ))),
        z ∈ K → P z := by
    simpa [Measure.volume_eq_prod] using hprod_unrestricted
  have hswap :
      ∀ᵐ p ∂((MeasureTheory.volume : Measure (Fin d → ℝ)).prod
          (MeasureTheory.volume : Measure ℝ)),
        ((p.2, p.1) : ℝ × (Fin d → ℝ)) ∈ K → P (p.2, p.1) := by
    have h :=
      (Measure.measurePreserving_swap
        (μ := (MeasureTheory.volume : Measure (Fin d → ℝ)))
        (ν := (MeasureTheory.volume : Measure ℝ))).quasiMeasurePreserving.tendsto_ae
        hprod_prod
    simpa [Prod.swap] using h
  have hslices :
      ∀ᵐ y ∂(MeasureTheory.volume : Measure (Fin d → ℝ)),
        ∀ᵐ a ∂(MeasureTheory.volume : Measure ℝ),
          ((a, y) : ℝ × (Fin d → ℝ)) ∈ K → P (a, y) := by
    simpa using Measure.ae_ae_of_ae_prod hswap
  filter_upwards [hslices] with y hy
  have hfiber_meas : MeasurableSet (firstCoordinateVerticalFiber K y) := by
    have hcont : Continuous (fun a : ℝ ↦ ((a, y) : ℝ × (Fin d → ℝ))) := by
      fun_prop
    exact (hK.preimage hcont).measurableSet
  have hy_restrict :
      ∀ᵐ a ∂(MeasureTheory.volume.restrict (firstCoordinateVerticalFiber K y)),
        ((a, y) : ℝ × (Fin d → ℝ)) ∈ K → P (a, y) :=
    ae_restrict_of_ae hy
  filter_upwards [hy_restrict, ae_restrict_mem hfiber_meas] with a ha hmem
  exact ha (by simpa [firstCoordinateVerticalFiber] using hmem)

/--
%%handwave
name:
  Product vertical fundamental theorem gives the fiberwise statement
statement:
  If the vertical fundamental theorem holds for almost every point of
  \(K\subset\mathbb R\times\mathbb R^d\), then it holds for almost every
  point in almost every vertical fiber of \(K\).
proof:
  Apply Fubini to the product almost-everywhere statement and then restrict
  the one-dimensional almost-everywhere implication to each closed vertical
  fiber of the compact set.
-/
theorem scalarWeakSobolev_firstCoordinate_fiberwise_line_integral_eq_ae_of_product
    {d : ℕ}
    {K : Set (ℝ × (Fin d → ℝ))} (hK : IsCompact K)
    {u : (ℝ × (Fin d → ℝ)) → ℝ}
    {du : (ℝ × (Fin d → ℝ)) → (ℝ × (Fin d → ℝ)) →L[ℝ] ℝ}
    (hprod :
      ∀ᵐ z ∂MeasureTheory.volume.restrict K,
        u (z + ((1 : ℝ), (0 : Fin d → ℝ))) - u z =
          ∫ t in Set.Icc (0 : ℝ) 1,
            du (z + t • ((1 : ℝ), (0 : Fin d → ℝ)))
              ((1 : ℝ), (0 : Fin d → ℝ)) ∂MeasureTheory.volume) :
    ∀ᵐ y ∂(MeasureTheory.volume : Measure (Fin d → ℝ)),
      ∀ᵐ a ∂(MeasureTheory.volume.restrict (firstCoordinateVerticalFiber K y)),
        u (((a, y) : ℝ × (Fin d → ℝ)) + ((1 : ℝ), (0 : Fin d → ℝ))) -
            u (a, y) =
          ∫ t in Set.Icc (0 : ℝ) 1,
            du (((a, y) : ℝ × (Fin d → ℝ)) +
                t • ((1 : ℝ), (0 : Fin d → ℝ)))
              ((1 : ℝ), (0 : Fin d → ℝ)) ∂MeasureTheory.volume := by
  exact
    ae_vertical_fibers_of_ae_restrict_prod
      (K := K)
      (P := fun z ↦
        u (z + ((1 : ℝ), (0 : Fin d → ℝ))) - u z =
          ∫ t in Set.Icc (0 : ℝ) 1,
            du (z + t • ((1 : ℝ), (0 : Fin d → ℝ)))
              ((1 : ℝ), (0 : Fin d → ℝ)) ∂MeasureTheory.volume)
      hK.isClosed hprod

/--
%%handwave
name:
  One-dimensional weak derivative
statement:
  A real-valued function on an open subset of \(\mathbb R\) has weak derivative
  \(g\) if the usual integration-by-parts identity holds against every smooth
  compactly supported test function:
  \[
    \int \varphi'(a) u(a)\,da=-\int \varphi(a)g(a)\,da .
  \]
-/
def IsWeakDerivativeOnRealRegionScalar
    (Ω : Set ℝ) (u g : ℝ → ℝ) : Prop :=
  ∀ φ : SmoothCompactlySupportedManifoldCoordinateFunction Ω,
    Integrable
        (fun a ↦ (fderiv ℝ (φ : ℝ → ℝ) a (1 : ℝ)) • u a)
        (MeasureTheory.volume.restrict Ω) ∧
      Integrable
        (fun a ↦ φ a • g a)
        (MeasureTheory.volume.restrict Ω) ∧
        ∫ a in Ω,
            (fderiv ℝ (φ : ℝ → ℝ) a (1 : ℝ)) • u a ∂MeasureTheory.volume =
          -∫ a in Ω, φ a • g a ∂MeasureTheory.volume

/--
%%handwave
name:
  A smooth compactly supported function is a coordinate test
statement:
  A smooth real-valued function with compact support contained in a region is
  a smooth compactly supported coordinate test on that region.
-/
def smoothCompactlySupportedManifoldCoordinateFunction_of_contDiff_hasCompactSupport
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {Ω : Set H} (φ : H → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφΩ : tsupport φ ⊆ Ω) :
    SmoothCompactlySupportedManifoldCoordinateFunction Ω where
  toFun := φ
  smooth := hφ
  support_subset := hφΩ
  compact_support := hφc

/--
%%handwave
name:
  The real weak derivative identity applies to ordinary smooth compactly
  supported tests
statement:
  In the one-dimensional weak-derivative identity, any smooth compactly
  supported function whose support lies in the region may be used as a test
  function.
proof:
  Regard the function as a smooth compactly supported coordinate test and
  apply the weak-derivative identity.
-/
theorem IsWeakDerivativeOnRealRegionScalar.contDiff_test
    {Ω : Set ℝ} {u g : ℝ → ℝ}
    (hweak : IsWeakDerivativeOnRealRegionScalar Ω u g)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hφΩ : tsupport φ ⊆ Ω) :
    Integrable
        (fun a ↦ (fderiv ℝ φ a (1 : ℝ)) • u a)
        (MeasureTheory.volume.restrict Ω) ∧
      Integrable
        (fun a ↦ φ a • g a)
        (MeasureTheory.volume.restrict Ω) ∧
        ∫ a in Ω,
            (fderiv ℝ φ a (1 : ℝ)) • u a ∂MeasureTheory.volume =
          -∫ a in Ω, φ a • g a ∂MeasureTheory.volume := by
  let ψ : SmoothCompactlySupportedManifoldCoordinateFunction Ω :=
    smoothCompactlySupportedManifoldCoordinateFunction_of_contDiff_hasCompactSupport
      φ hφ hφc hφΩ
  simpa [ψ, smoothCompactlySupportedManifoldCoordinateFunction_of_contDiff_hasCompactSupport]
    using hweak ψ

/--
%%handwave
name:
  The one-dimensional weak derivative identity for ordinary tests on the real
  line
statement:
  If a smooth compactly supported test function has support contained in the
  region, then the weak derivative integration-by-parts identity may be
  written as an integral over the whole real line.
proof:
  Apply the weak derivative identity on the region.  The test function and
  its derivative vanish off the region, because the closed support of the
  test lies in the region and the derivative has support contained in the
  closed support of the test.
-/
theorem IsWeakDerivativeOnRealRegionScalar.contDiff_test_integral_eq
    {Ω : Set ℝ} {u g : ℝ → ℝ}
    (hweak : IsWeakDerivativeOnRealRegionScalar Ω u g)
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ)
    (hθc : HasCompactSupport θ) (hθΩ : tsupport θ ⊆ Ω) :
    ∫ x, (fderiv ℝ θ x (1 : ℝ)) • u x
        ∂(MeasureTheory.volume : Measure ℝ) =
      -∫ x, θ x • g x ∂(MeasureTheory.volume : Measure ℝ) := by
  rcases hweak.contDiff_test hθ hθc hθΩ with ⟨_hleft_int, _hright_int, hEq⟩
  have hderiv_support :
      tsupport (fun x : ℝ ↦ fderiv ℝ θ x (1 : ℝ)) ⊆ Ω :=
    (tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := θ) (1 : ℝ)).trans hθΩ
  have hleft :
      ∫ x in Ω, (fderiv ℝ θ x (1 : ℝ)) • u x
          ∂(MeasureTheory.volume : Measure ℝ) =
        ∫ x, (fderiv ℝ θ x (1 : ℝ)) • u x
          ∂(MeasureTheory.volume : Measure ℝ) := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero ?_
    intro x hxΩ
    have hx_not :
        x ∉ tsupport (fun y : ℝ ↦ fderiv ℝ θ y (1 : ℝ)) := by
      exact fun hx ↦ hxΩ (hderiv_support hx)
    simp [image_eq_zero_of_notMem_tsupport hx_not]
  have hright :
      ∫ x in Ω, θ x • g x ∂(MeasureTheory.volume : Measure ℝ) =
        ∫ x, θ x • g x ∂(MeasureTheory.volume : Measure ℝ) := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero ?_
    intro x hxΩ
    have hx_not : x ∉ tsupport θ := fun hx ↦ hxΩ (hθΩ hx)
    simp [image_eq_zero_of_notMem_tsupport hx_not]
  calc
    ∫ x, (fderiv ℝ θ x (1 : ℝ)) • u x
        ∂(MeasureTheory.volume : Measure ℝ)
        = ∫ x in Ω, (fderiv ℝ θ x (1 : ℝ)) • u x
            ∂(MeasureTheory.volume : Measure ℝ) := hleft.symm
    _ = -∫ x in Ω, θ x • g x ∂(MeasureTheory.volume : Measure ℝ) := hEq
    _ = -∫ x, θ x • g x ∂(MeasureTheory.volume : Measure ℝ) := by
      rw [hright]

/--
%%handwave
name:
  The real-line weak derivative is the one-dimensional Euclidean weak derivative
statement:
  A Euclidean weak derivative field on a real interval gives the real-line weak
  derivative in the unit direction.
proof:
  Specialize the Euclidean integration-by-parts identity to the one-dimensional model and the unit tangent direction.  The continuous linear derivative field evaluated at (1) is the scalar real weak derivative.
-/
theorem IsWeakDerivativeOnEuclideanRegionScalar.toRealRegion
    {Ω : Set ℝ} {u : ℝ → ℝ} {du : ℝ → ℝ →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionScalar Ω u du) :
    IsWeakDerivativeOnRealRegionScalar Ω u (fun a ↦ du a (1 : ℝ)) := by
  intro φ
  exact hweak φ (1 : ℝ)

private abbrev SmoothTestIoo :=
  SmoothCompactlySupportedManifoldCoordinateFunction (Set.Ioo (0 : ℝ) 1)

private abbrev SupportedSmoothTestIoo (K : Set ℝ) :=
  {φ : SmoothTestIoo // tsupport (φ : ℝ → ℝ) ⊆ K}

private noncomputable def supportedSmoothTestC1GraphMap
    (K : Set ℝ) (φ : SupportedSmoothTestIoo K) :
    C(K, ℝ) × C(K, ℝ) :=
  ( { toFun := fun x : K ↦ (φ.val : ℝ → ℝ) x.1
      continuous_toFun := φ.val.smooth.continuous.comp continuous_subtype_val },
    { toFun := fun x : K ↦ fderiv ℝ (φ.val : ℝ → ℝ) x.1 (1 : ℝ)
      continuous_toFun :=
        ((φ.val.smooth.continuous_fderiv (by simp)).clm_apply
          continuous_const).comp continuous_subtype_val } )

private abbrev SmoothTestC1Graph (K : Set ℝ) :=
  Set.range (supportedSmoothTestC1GraphMap K)

/--
%%handwave
name:
  Separability of the graph space of supported smooth tests
statement:
  For compact \(K\subset\mathbb R\), the set of pairs
  \((\varphi|_K,\varphi'|_K)\) arising from smooth tests supported in \(K\) is
  a separable topological space.
proof:
  It is a subspace of the product \(C(K,\mathbb R)\times C(K,\mathbb R)\),
  which is separable for compact metrizable \(K\).
-/
private theorem smoothTestC1Graph_separableSpace
    (K : Set ℝ) (hK : IsCompact K) :
    TopologicalSpace.SeparableSpace (SmoothTestC1Graph K) := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hsep :
      TopologicalSpace.IsSeparable
        (SmoothTestC1Graph K : Set (C(K, ℝ) × C(K, ℝ))) := by
    exact TopologicalSpace.IsSeparable.mono
      (TopologicalSpace.isSeparable_univ_iff.2 inferInstance) (Set.subset_univ _)
  exact hsep.separableSpace

private noncomputable def smoothTestC1GraphDenseSet
    (K : Set ℝ) (hK : IsCompact K) :
    Set (SmoothTestC1Graph K) :=
  letI : TopologicalSpace.SeparableSpace (SmoothTestC1Graph K) :=
    smoothTestC1Graph_separableSpace K hK
  Classical.choose (TopologicalSpace.exists_countable_dense (SmoothTestC1Graph K))

/--
%%handwave
name:
  Countability of the selected dense graph tests
statement:
  The chosen dense subset of the \(C^1\)-graph space of tests supported in a
  compact set \(K\) is countable.
proof:
  This is the countability part of the chosen countable dense subset supplied
  by separability.
-/
private theorem smoothTestC1GraphDenseSet_countable
    (K : Set ℝ) (hK : IsCompact K) :
    (smoothTestC1GraphDenseSet K hK).Countable := by
  letI : TopologicalSpace.SeparableSpace (SmoothTestC1Graph K) :=
    smoothTestC1Graph_separableSpace K hK
  exact (Classical.choose_spec
    (TopologicalSpace.exists_countable_dense (SmoothTestC1Graph K))).1

/--
%%handwave
name:
  Density of the selected graph tests
statement:
  The chosen countable subset is dense in the \(C^1\)-graph space of smooth
  tests supported in \(K\).
proof:
  This is the density part of the choice made from separability of that graph
  space.
-/
private theorem smoothTestC1GraphDenseSet_dense
    (K : Set ℝ) (hK : IsCompact K) :
    Dense (smoothTestC1GraphDenseSet K hK) := by
  letI : TopologicalSpace.SeparableSpace (SmoothTestC1Graph K) :=
    smoothTestC1Graph_separableSpace K hK
  exact (Classical.choose_spec
    (TopologicalSpace.exists_countable_dense (SmoothTestC1Graph K))).2

private noncomputable def smoothTestC1GraphPreimage
    (K : Set ℝ) (p : SmoothTestC1Graph K) :
    SupportedSmoothTestIoo K :=
  Classical.choose p.2

/--
%%handwave
name:
  A chosen test represents its graph point
statement:
  If \(p\) is a graph point \((\varphi|_K,\varphi'|_K)\), the test chosen as a
  preimage of \(p\) has graph exactly \(p\).
proof:
  This is the defining property of the chosen preimage of a point in the
  range of the graph map.
-/
private theorem smoothTestC1GraphPreimage_graph
    (K : Set ℝ) (p : SmoothTestC1Graph K) :
    supportedSmoothTestC1GraphMap K (smoothTestC1GraphPreimage K p) = p.1 :=
  Classical.choose_spec p.2

private noncomputable def smoothTestC1DenseTestsOn
    (K : Set ℝ) (hK : IsCompact K) : Set SmoothTestIoo :=
  (fun p : SmoothTestC1Graph K ↦ (smoothTestC1GraphPreimage K p).val) ''
    smoothTestC1GraphDenseSet K hK

/--
%%handwave
name:
  Countability of dense smooth tests on a compact interval
statement:
  For compact \(K\subset(0,1)\), the selected family of smooth tests supported
  in \(K\) is countable.
proof:
  It is the image of the chosen countable dense subset of the graph space.
-/
private theorem smoothTestC1DenseTestsOn_countable
    (K : Set ℝ) (hK : IsCompact K) :
    (smoothTestC1DenseTestsOn K hK).Countable :=
  (smoothTestC1GraphDenseSet_countable K hK).image _

private abbrev RationalCompactSubintervalIndex :=
  {p : ℚ × ℚ // 0 < (p.1 : ℝ) ∧ (p.1 : ℝ) < (p.2 : ℝ) ∧ (p.2 : ℝ) < 1}

private def rationalCompactSubinterval
    (j : RationalCompactSubintervalIndex) : Set ℝ :=
  Set.Icc (j.1.1 : ℝ) (j.1.2 : ℝ)

/--
%%handwave
name:
  Compactness of a rational closed subinterval
statement:
  Every closed interval \([a,b]\) with rational endpoints
  \(0<a<b<1\) is compact.
proof:
  Closed bounded intervals in \(\mathbb R\) are compact.
-/
private theorem rationalCompactSubinterval_compact
    (j : RationalCompactSubintervalIndex) :
    IsCompact (rationalCompactSubinterval j) := by
  exact isCompact_Icc

/--
%%handwave
name:
  A rational compact subinterval lies in the unit interval
statement:
  If \(0<a<b<1\), then \([a,b]\subset(0,1)\).
proof:
  Combine \(a\le x\le b\) with the strict endpoint inequalities.
-/
private theorem rationalCompactSubinterval_subset_Ioo
    (j : RationalCompactSubintervalIndex) :
    rationalCompactSubinterval j ⊆ Set.Ioo (0 : ℝ) 1 := by
  intro x hx
  exact ⟨lt_of_lt_of_le j.2.1 hx.1, lt_of_le_of_lt hx.2 j.2.2.2⟩

/--
%%handwave
name:
  Rational interval covering a compact subset of the unit interval
statement:
  Every compact set \(S\subset(0,1)\) is contained in some
  \([a,b]\subset(0,1)\) with rational \(a<b\).
proof:
  For nonempty \(S\), take its minimum and maximum and choose rational numbers
  strictly between \(0\) and the minimum and between the maximum and \(1\).
  The empty set is covered by any fixed rational subinterval.
-/
private theorem exists_rationalCompactSubinterval_cover_of_compact_subset_Ioo
    {S : Set ℝ} (hS : IsCompact S) (hSI : S ⊆ Set.Ioo (0 : ℝ) 1) :
    ∃ j : RationalCompactSubintervalIndex, S ⊆ rationalCompactSubinterval j := by
  by_cases hSne : S.Nonempty
  · rcases hS.exists_isLeast hSne with ⟨m, hm⟩
    rcases hS.exists_isGreatest hSne with ⟨M, hM⟩
    have hmI : m ∈ Set.Ioo (0 : ℝ) 1 := hSI hm.1
    have hMI : M ∈ Set.Ioo (0 : ℝ) 1 := hSI hM.1
    rcases exists_rat_btwn hmI.1 with ⟨a, ha0, ham⟩
    rcases exists_rat_btwn hMI.2 with ⟨b, hMb, hb1⟩
    have hmM : m ≤ M := hm.2 hM.1
    have hab : (a : ℝ) < (b : ℝ) :=
      lt_trans ham (lt_of_le_of_lt hmM hMb)
    refine ⟨⟨(a, b), ha0, hab, hb1⟩, ?_⟩
    intro x hx
    exact
      ⟨le_of_lt (lt_of_lt_of_le ham (hm.2 hx)),
        le_of_lt (lt_of_le_of_lt (hM.2 hx) hMb)⟩
  · let j : RationalCompactSubintervalIndex :=
      ⟨((1 / 3 : ℚ), (2 / 3 : ℚ)), by norm_num, by norm_num, by norm_num⟩
    refine ⟨j, ?_⟩
    intro x hx
    exact False.elim (hSne ⟨x, hx⟩)

/--
%%handwave
name:
  Uniform \(C^1\) approximation by a countable test family
statement:
  Let \(K\subset(0,1)\) be compact and let \(\varphi\) be a smooth test
  supported in \(K\). For every \(\varepsilon>0\), some selected test
  \(\psi\), also supported in \(K\), satisfies
  \(\sup|\psi-\varphi|<\varepsilon\) and
  \(\sup|\psi'-\varphi'|<\varepsilon\).
proof:
  Approximate the graph point \((\varphi|_K,\varphi'|_K)\) by the chosen dense
  subset in the product sup norm. Outside \(K\), both tests and their
  derivatives vanish.
-/
private theorem smoothTestC1DenseTestsOn_approx
    (K : Set ℝ) (hK : IsCompact K) (φ : SupportedSmoothTestIoo K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ ∈ smoothTestC1DenseTestsOn K hK,
      tsupport (ψ : ℝ → ℝ) ⊆ K ∧
        (∀ x : ℝ, ‖(ψ : ℝ → ℝ) x - (φ.val : ℝ → ℝ) x‖ < ε) ∧
          (∀ x : ℝ,
            ‖fderiv ℝ (ψ : ℝ → ℝ) x (1 : ℝ) -
              fderiv ℝ (φ.val : ℝ → ℝ) x (1 : ℝ)‖ < ε) := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let pφ : SmoothTestC1Graph K :=
    ⟨supportedSmoothTestC1GraphMap K φ, ⟨φ, rfl⟩⟩
  rcases (smoothTestC1GraphDenseSet_dense K hK).exists_dist_lt pφ hε with
    ⟨p, hp_mem, hp_dist⟩
  let η : SupportedSmoothTestIoo K := smoothTestC1GraphPreimage K p
  let ψ : SmoothTestIoo := η.val
  have hη_graph : supportedSmoothTestC1GraphMap K η = p.1 :=
    smoothTestC1GraphPreimage_graph K p
  have hprod :
      dist (supportedSmoothTestC1GraphMap K φ)
          (supportedSmoothTestC1GraphMap K η) < ε := by
    simpa [pφ, η, hη_graph] using hp_dist
  have hfst :
      dist (supportedSmoothTestC1GraphMap K φ).1
          (supportedSmoothTestC1GraphMap K η).1 < ε := by
    have hmax :
        max (dist (supportedSmoothTestC1GraphMap K φ).1
                (supportedSmoothTestC1GraphMap K η).1)
            (dist (supportedSmoothTestC1GraphMap K φ).2
                (supportedSmoothTestC1GraphMap K η).2) < ε := by
      simpa [Prod.dist_eq] using hprod
    exact (max_lt_iff.mp hmax).1
  have hsnd :
      dist (supportedSmoothTestC1GraphMap K φ).2
          (supportedSmoothTestC1GraphMap K η).2 < ε := by
    have hmax :
        max (dist (supportedSmoothTestC1GraphMap K φ).1
                (supportedSmoothTestC1GraphMap K η).1)
            (dist (supportedSmoothTestC1GraphMap K φ).2
                (supportedSmoothTestC1GraphMap K η).2) < ε := by
      simpa [Prod.dist_eq] using hprod
    exact (max_lt_iff.mp hmax).2
  refine ⟨ψ, ?_, η.property, ?_, ?_⟩
  · exact ⟨p, hp_mem, rfl⟩
  · intro x
    by_cases hxK : x ∈ K
    · have hpoint :
          dist ((supportedSmoothTestC1GraphMap K φ).1 ⟨x, hxK⟩)
              ((supportedSmoothTestC1GraphMap K η).1 ⟨x, hxK⟩) < ε :=
        lt_of_le_of_lt
          (ContinuousMap.dist_apply_le_dist (⟨x, hxK⟩ : K)) hfst
      simpa [supportedSmoothTestC1GraphMap, ψ, η, dist_eq_norm,
        norm_sub_rev] using hpoint
    · have hη_not : x ∉ tsupport (η.val : ℝ → ℝ) :=
        fun hx ↦ hxK (η.property hx)
      have hφ_not : x ∉ tsupport (φ.val : ℝ → ℝ) :=
        fun hx ↦ hxK (φ.property hx)
      have hη_zero : (η.val : ℝ → ℝ) x = 0 :=
        image_eq_zero_of_notMem_tsupport hη_not
      have hφ_zero : (φ.val : ℝ → ℝ) x = 0 :=
        image_eq_zero_of_notMem_tsupport hφ_not
      simp [ψ, η, hη_zero, hφ_zero, hε]
  · intro x
    by_cases hxK : x ∈ K
    · have hpoint :
          dist ((supportedSmoothTestC1GraphMap K φ).2 ⟨x, hxK⟩)
              ((supportedSmoothTestC1GraphMap K η).2 ⟨x, hxK⟩) < ε :=
        lt_of_le_of_lt
          (ContinuousMap.dist_apply_le_dist (⟨x, hxK⟩ : K)) hsnd
      simpa [supportedSmoothTestC1GraphMap, ψ, η, dist_eq_norm,
        norm_sub_rev] using hpoint
    · have hη_not : x ∉ tsupport (η.val : ℝ → ℝ) :=
        fun hx ↦ hxK (η.property hx)
      have hφ_not : x ∉ tsupport (φ.val : ℝ → ℝ) :=
        fun hx ↦ hxK (φ.property hx)
      have hη_fderiv :
          fderiv ℝ (η.val : ℝ → ℝ) x = 0 :=
        fderiv_of_notMem_tsupport (𝕜 := ℝ) (f := (η.val : ℝ → ℝ)) hη_not
      have hφ_fderiv :
          fderiv ℝ (φ.val : ℝ → ℝ) x = 0 :=
        fderiv_of_notMem_tsupport (𝕜 := ℝ) (f := (φ.val : ℝ → ℝ)) hφ_not
      simp [ψ, η, hη_fderiv, hφ_fderiv, hε]

/--
%%handwave
name:
  Countably many smooth tests are dense in the \(C^1\) test topology on an
  interval
statement:
  There is a countable family of smooth compactly supported functions on
  \((0,1)\) such that every smooth compactly supported test function can be
  approximated uniformly together with its first derivative by functions from
  the family, with all approximants supported in one compact subinterval of
  \((0,1)\) depending on the original test.
proof:
  Cover compact subintervals of \((0,1)\) by rational closed intervals.  On
  each such interval, map a smooth test supported there to the pair consisting
  of its restriction and the restriction of its derivative.  The ambient
  product of continuous-function spaces is separable, hence so is this graph
  subspace.  Choose a countable dense subset of the graph and then choose one
  smooth preimage for each selected graph point.  A countable union over the
  rational intervals gives the desired family.
-/
theorem exists_countable_c1_dense_smooth_tests_Ioo :
    ∃ T : Set
        (SmoothCompactlySupportedManifoldCoordinateFunction
          (Set.Ioo (0 : ℝ) 1)),
      T.Countable ∧
        ∀ φ : SmoothCompactlySupportedManifoldCoordinateFunction
            (Set.Ioo (0 : ℝ) 1),
          ∃ K : Set ℝ,
            IsCompact K ∧
              K ⊆ Set.Ioo (0 : ℝ) 1 ∧
              tsupport (φ : ℝ → ℝ) ⊆ K ∧
              ∀ ε : ℝ, 0 < ε →
                ∃ ψ ∈ T,
                  tsupport (ψ : ℝ → ℝ) ⊆ K ∧
                    (∀ x : ℝ, ‖(ψ : ℝ → ℝ) x - φ x‖ < ε) ∧
                      (∀ x : ℝ,
                        ‖fderiv ℝ (ψ : ℝ → ℝ) x (1 : ℝ) -
                          fderiv ℝ (φ : ℝ → ℝ) x (1 : ℝ)‖ < ε) := by
  let T : Set SmoothTestIoo :=
    ⋃ j : RationalCompactSubintervalIndex,
      smoothTestC1DenseTestsOn (rationalCompactSubinterval j)
        (rationalCompactSubinterval_compact j)
  refine ⟨T, ?_, ?_⟩
  · haveI : Countable RationalCompactSubintervalIndex := by infer_instance
    exact Set.countable_iUnion fun j ↦
      smoothTestC1DenseTestsOn_countable (rationalCompactSubinterval j)
        (rationalCompactSubinterval_compact j)
  · intro φ
    rcases exists_rationalCompactSubinterval_cover_of_compact_subset_Ioo
        φ.compact_support φ.support_subset with
      ⟨j, hφK⟩
    let K : Set ℝ := rationalCompactSubinterval j
    let φK : SupportedSmoothTestIoo K := ⟨φ, hφK⟩
    refine ⟨K, rationalCompactSubinterval_compact j,
      rationalCompactSubinterval_subset_Ioo j, hφK, ?_⟩
    intro ε hε
    rcases smoothTestC1DenseTestsOn_approx K
        (rationalCompactSubinterval_compact j) φK hε with
      ⟨ψ, hψ_on, hψK, hψ_val, hψ_deriv⟩
    have hψT : ψ ∈ T := by
      exact Set.mem_iUnion.2 ⟨j, hψ_on⟩
    refine ⟨ψ, hψT, hψK, ?_, ?_⟩
    · intro x
      simpa [φK] using hψ_val x
    · intro x
      simpa [φK] using hψ_deriv x

/--
%%handwave
name:
  Slice data for a countable family of one-dimensional tests
statement:
  For a vertical line in the product strip, the countable test data consists
  of local integrability of the sliced function and sliced first-coordinate
  weak derivative on compact subintervals, together with the
  one-dimensional integration-by-parts identity for every test in the chosen
  countable family.
-/
def FirstCoordinateSliceWeakDerivativeTestData
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : Set
      (SmoothCompactlySupportedManifoldCoordinateFunction
        (Set.Ioo (0 : ℝ) 1)))
    (U : ℝ × E → ℝ)
    (DU : ℝ × E → (ℝ × E) →L[ℝ] ℝ)
    (y : E) : Prop :=
  (∀ K : Set ℝ, IsCompact K → K ⊆ Set.Ioo (0 : ℝ) 1 →
      IntegrableOn (fun r : ℝ ↦ U (r, y)) K
        (MeasureTheory.volume : Measure ℝ) ∧
        IntegrableOn
          (fun r : ℝ ↦ DU (r, y) ((1 : ℝ), (0 : E))) K
          (MeasureTheory.volume : Measure ℝ)) ∧
    ∀ ψ ∈ T,
      Integrable
          (fun r : ℝ ↦
            (fderiv ℝ (ψ : ℝ → ℝ) r (1 : ℝ)) • U (r, y))
          (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)) ∧
        Integrable
          (fun r : ℝ ↦
            ψ r • DU (r, y) ((1 : ℝ), (0 : E)))
          (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)) ∧
          ∫ r in Set.Ioo (0 : ℝ) 1,
              (fderiv ℝ (ψ : ℝ → ℝ) r (1 : ℝ)) • U (r, y)
              ∂MeasureTheory.volume =
            -∫ r in Set.Ioo (0 : ℝ) 1,
              ψ r • DU (r, y) ((1 : ℝ), (0 : E))
              ∂MeasureTheory.volume

/--
%%handwave
name:
  Compact support and compact local integrability give restricted
  integrability
statement:
  If a scalar function is integrable on a compact set \(K\), and a continuous
  multiplier is bounded and supported in \(K\), then the product is
  integrable after restriction to any measurable region.
proof:
  Bounded multiplication preserves integrability on \(K\).  The product is
  supported in \(K\), so integrability on \(K\) is equivalent to global
  integrability of the zero extension.  Restricting the measure only makes
  integrability easier.
-/
theorem integrable_restrict_smul_of_integrableOn_compact_tsupport_subset
    {Ω K : Set ℝ} {a f : ℝ → ℝ}
    (hK : IsCompact K)
    (hfK : IntegrableOn f K (MeasureTheory.volume : Measure ℝ))
    (ha_cont : Continuous a)
    (ha_bound : ∃ C : NNReal, ∀ x : ℝ, ‖a x‖ ≤ C)
    (ha_support : tsupport a ⊆ K) :
    Integrable (fun x : ℝ ↦ a x • f x)
      (MeasureTheory.volume.restrict Ω) := by
  rcases ha_bound with ⟨C, hC⟩
  have hprodK : Integrable (fun x : ℝ ↦ a x * f x)
      (MeasureTheory.volume.restrict K) := by
    exact hfK.bdd_mul ha_cont.aestronglyMeasurable
      (ae_restrict_of_forall_mem hK.measurableSet fun x _hx ↦ hC x)
  have hprod_support : Function.support (fun x : ℝ ↦ a x * f x) ⊆ K := by
    intro x hx
    exact ha_support
      (subset_tsupport a
        (Function.support_mul_subset_left (f := a) (g := f) hx))
  have hglobal : Integrable (fun x : ℝ ↦ a x * f x)
      (MeasureTheory.volume : Measure ℝ) :=
    (integrableOn_iff_integrable_of_support_subset hprod_support).mp hprodK
  simpa using hglobal.mono_measure
    (Measure.restrict_le_self (μ := MeasureTheory.volume) (s := Ω))

/--
%%handwave
name:
  Uniformly close compactly supported multipliers have close pairings
statement:
  If two scalar multipliers are supported in a measurable set \(K\), differ
  uniformly by at most \(\varepsilon\), and \(f\) is integrable on \(K\), then
  the integral of their difference times \(f\) over any larger measurable set
  is bounded by \(\varepsilon\int_K |f|\).
proof:
  The integrand vanishes off \(K\), so the integral over the larger set is the
  integral over \(K\).  The pointwise estimate
  \(|(a-b)f|\le\varepsilon |f|\) and monotonicity of the integral give the
  result.
-/
theorem norm_setIntegral_smul_error_le_of_tsupport_subset
    {Ω K : Set ℝ} {a b f : ℝ → ℝ} {ε : ℝ}
    (hΩ_meas : MeasurableSet Ω)
    (hKΩ : K ⊆ Ω)
    (hfK : IntegrableOn f K (MeasureTheory.volume : Measure ℝ))
    (ha_support : tsupport a ⊆ K) (hb_support : tsupport b ⊆ K)
    (hclose : ∀ x : ℝ, ‖a x - b x‖ ≤ ε) :
    ‖∫ x in Ω, (a x - b x) • f x ∂MeasureTheory.volume‖ ≤
      ε * ∫ x in K, ‖f x‖ ∂MeasureTheory.volume := by
  have hzero :
      ∀ x ∈ Ω \ K, ((a x - b x) • f x : ℝ) = 0 := by
    intro x hx
    have hxK : x ∉ K := hx.2
    have hxa : x ∉ tsupport a := fun hxsa ↦ hxK (ha_support hxsa)
    have hxb : x ∉ tsupport b := fun hxsb ↦ hxK (hb_support hxsb)
    have ha0 : a x = 0 := image_eq_zero_of_notMem_tsupport hxa
    have hb0 : b x = 0 := image_eq_zero_of_notMem_tsupport hxb
    simp [ha0, hb0]
  have hlocalize :
      ∫ x in Ω, (a x - b x) • f x ∂MeasureTheory.volume =
        ∫ x in K, (a x - b x) • f x ∂MeasureTheory.volume :=
    setIntegral_eq_of_subset_of_forall_diff_eq_zero hΩ_meas hKΩ hzero
  have hbound_int :
      Integrable (fun x : ℝ ↦ ε * ‖f x‖)
        (MeasureTheory.volume.restrict K) := by
    simpa [smul_eq_mul] using hfK.norm.const_mul ε
  have hnorm_le :
      ∫ x in K, ‖(a x - b x) • f x‖ ∂MeasureTheory.volume ≤
        ∫ x in K, ε * ‖f x‖ ∂MeasureTheory.volume := by
    apply integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _)
      hbound_int
    filter_upwards with x
    calc
      ‖(a x - b x) • f x‖ = ‖a x - b x‖ * ‖f x‖ := by
        rw [norm_smul]
      _ ≤ ε * ‖f x‖ :=
        mul_le_mul_of_nonneg_right (hclose x) (norm_nonneg _)
  calc
    ‖∫ x in Ω, (a x - b x) • f x ∂MeasureTheory.volume‖
        = ‖∫ x in K, (a x - b x) • f x ∂MeasureTheory.volume‖ := by
          rw [hlocalize]
    _ ≤ ∫ x in K, ‖(a x - b x) • f x‖ ∂MeasureTheory.volume :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x in K, ε * ‖f x‖ ∂MeasureTheory.volume := hnorm_le
    _ = ε * ∫ x in K, ‖f x‖ ∂MeasureTheory.volume := by
      rw [integral_const_mul]

/--
%%handwave
name:
  The countable dense test identities pass to a smooth test
statement:
  Let a sliced function and candidate derivative be locally integrable on a
  compact set \(K\subset(0,1)\).  If a smooth test can be approximated in
  \(C^1\) by members of the countable test family, with all approximants
  supported in \(K\), and the integration-by-parts identity holds for the
  approximants, then it holds for the original smooth test.
proof:
  The uniform convergence of the functions and their derivatives, together
  with integrability of the sliced function and sliced derivative on \(K\),
  bounds the two error integrals by the uniform errors times the corresponding
  \(L^1\)-norms on \(K\).  These errors tend to zero, so the approximating
  identities converge to the desired identity.
-/
theorem realWeakDerivativeOn_Ioo_test_identity_of_countable_c1_dense_test_data
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : Set
      (SmoothCompactlySupportedManifoldCoordinateFunction
        (Set.Ioo (0 : ℝ) 1))}
    {U : ℝ × E → ℝ}
    {DU : ℝ × E → (ℝ × E) →L[ℝ] ℝ}
    {y : E}
    (hT_dense :
      ∀ φ : SmoothCompactlySupportedManifoldCoordinateFunction
          (Set.Ioo (0 : ℝ) 1),
        ∃ K : Set ℝ,
          IsCompact K ∧
            K ⊆ Set.Ioo (0 : ℝ) 1 ∧
            tsupport (φ : ℝ → ℝ) ⊆ K ∧
            ∀ ε : ℝ, 0 < ε →
              ∃ ψ ∈ T,
                tsupport (ψ : ℝ → ℝ) ⊆ K ∧
                  (∀ x : ℝ, ‖(ψ : ℝ → ℝ) x - φ x‖ < ε) ∧
                    (∀ x : ℝ,
                      ‖fderiv ℝ (ψ : ℝ → ℝ) x (1 : ℝ) -
                        fderiv ℝ (φ : ℝ → ℝ) x (1 : ℝ)‖ < ε))
    (hdata : FirstCoordinateSliceWeakDerivativeTestData T U DU y)
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction
        (Set.Ioo (0 : ℝ) 1)) :
    ∫ r in Set.Ioo (0 : ℝ) 1,
        (fderiv ℝ (φ : ℝ → ℝ) r (1 : ℝ)) • U (r, y)
        ∂MeasureTheory.volume =
      -∫ r in Set.Ioo (0 : ℝ) 1,
        φ r • DU (r, y) ((1 : ℝ), (0 : E))
        ∂MeasureTheory.volume := by
  let I : Set ℝ := Set.Ioo (0 : ℝ) 1
  let g : ℝ → ℝ := fun r ↦ DU (r, y) ((1 : ℝ), (0 : E))
  rcases hT_dense φ with ⟨K, hK_compact, hKΩ, hφ_support, happrox⟩
  rcases hdata.1 K hK_compact hKΩ with ⟨hU_K, hg_K⟩
  let Aφ : ℝ :=
    ∫ r in I, (fderiv ℝ (φ : ℝ → ℝ) r (1 : ℝ)) • U (r, y)
      ∂MeasureTheory.volume
  let Bφ : ℝ :=
    ∫ r in I, φ r • g r ∂MeasureTheory.volume
  have hI_meas : MeasurableSet I := measurableSet_Ioo
  have hderiv_cont :
      Continuous (fun r : ℝ ↦ fderiv ℝ (φ : ℝ → ℝ) r (1 : ℝ)) :=
    (φ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have hderiv_support :
      tsupport (fun r : ℝ ↦ fderiv ℝ (φ : ℝ → ℝ) r (1 : ℝ)) ⊆ K :=
    (tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := (φ : ℝ → ℝ)) (1 : ℝ)).trans
      hφ_support
  have hAφ_int : Integrable
      (fun r : ℝ ↦ (fderiv ℝ (φ : ℝ → ℝ) r (1 : ℝ)) • U (r, y))
      (MeasureTheory.volume.restrict I) := by
    exact
      integrable_restrict_smul_of_integrableOn_compact_tsupport_subset
        (Ω := I) (K := K)
        (a := fun r : ℝ ↦ fderiv ℝ (φ : ℝ → ℝ) r (1 : ℝ))
        (f := fun r : ℝ ↦ U (r, y))
        hK_compact hU_K hderiv_cont
        (SmoothCompactlySupportedManifoldCoordinateFunction.exists_derivative_bound
          φ (1 : ℝ))
        hderiv_support
  have hBφ_int : Integrable (fun r : ℝ ↦ φ r • g r)
      (MeasureTheory.volume.restrict I) := by
    exact
      integrable_restrict_smul_of_integrableOn_compact_tsupport_subset
        (Ω := I) (K := K)
        (a := fun r : ℝ ↦ φ r) (f := g)
        hK_compact hg_K φ.smooth.continuous
        (SmoothCompactlySupportedManifoldCoordinateFunction.exists_bound φ)
        hφ_support
  let SU : ℝ := ∫ r in K, ‖U (r, y)‖ ∂MeasureTheory.volume
  let Sg : ℝ := ∫ r in K, ‖g r‖ ∂MeasureTheory.volume
  have hSU_nonneg : 0 ≤ SU := by
    dsimp [SU]
    exact integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun r ↦ by
        simp)
  have hSg_nonneg : 0 ≤ Sg := by
    dsimp [Sg]
    exact integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun r ↦ by
        simp)
  have hsum_zero : Aφ + Bφ = 0 := by
    apply eq_of_forall_dist_le
    intro ε hε
    let S : ℝ := SU + Sg + 1
    have hS_pos : 0 < S := by
      dsimp [S]
      linarith
    let δ : ℝ := ε / S
    have hδ_pos : 0 < δ := by
      dsimp [δ]
      exact div_pos hε hS_pos
    rcases happrox δ hδ_pos with
      ⟨ψ, hψT, hψ_support, hψ_close, hψ_deriv_close⟩
    rcases hdata.2 ψ hψT with ⟨hAψ_int, hBψ_int, hψ_eq⟩
    let Aψ : ℝ :=
      ∫ r in I, (fderiv ℝ (ψ : ℝ → ℝ) r (1 : ℝ)) • U (r, y)
        ∂MeasureTheory.volume
    let Bψ : ℝ :=
      ∫ r in I, ψ r • g r ∂MeasureTheory.volume
    have hψ_eq' : Aψ = -Bψ := by
      simpa [Aψ, Bψ, I, g] using hψ_eq
    have hψ_sum : Aψ + Bψ = 0 := by
      linarith
    have hψ_deriv_support :
        tsupport (fun r : ℝ ↦ fderiv ℝ (ψ : ℝ → ℝ) r (1 : ℝ)) ⊆ K :=
      (tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := (ψ : ℝ → ℝ)) (1 : ℝ)).trans
        hψ_support
    have hA_diff :
        Aφ - Aψ =
          ∫ r in I,
            ((fderiv ℝ (φ : ℝ → ℝ) r (1 : ℝ) -
                fderiv ℝ (ψ : ℝ → ℝ) r (1 : ℝ)) • U (r, y))
            ∂MeasureTheory.volume := by
      dsimp [Aφ, Aψ]
      rw [← integral_sub
        (by simpa [smul_eq_mul] using hAφ_int)
        (by simpa [smul_eq_mul] using hAψ_int)]
      apply integral_congr_ae
      filter_upwards with r
      ring
    have hB_diff :
        Bφ - Bψ =
          ∫ r in I, ((φ r - ψ r) • g r) ∂MeasureTheory.volume := by
      dsimp [Bφ, Bψ]
      rw [← integral_sub
        (by simpa [smul_eq_mul] using hBφ_int)
        (by simpa [g, smul_eq_mul] using hBψ_int)]
      apply integral_congr_ae
      filter_upwards with r
      ring
    have hAerr : ‖Aφ - Aψ‖ ≤ δ * SU := by
      rw [hA_diff]
      simpa [smul_eq_mul] using
        norm_setIntegral_smul_error_le_of_tsupport_subset
          (Ω := I) (K := K)
          (a := fun r : ℝ ↦ fderiv ℝ (φ : ℝ → ℝ) r (1 : ℝ))
          (b := fun r : ℝ ↦ fderiv ℝ (ψ : ℝ → ℝ) r (1 : ℝ))
          (f := fun r : ℝ ↦ U (r, y))
          hI_meas hKΩ hU_K hderiv_support hψ_deriv_support
          (fun r ↦ by
            have hr := le_of_lt (hψ_deriv_close r)
            simpa [norm_sub_rev] using hr)
    have hBerr : ‖Bφ - Bψ‖ ≤ δ * Sg := by
      rw [hB_diff]
      simpa [smul_eq_mul] using
        norm_setIntegral_smul_error_le_of_tsupport_subset
          (Ω := I) (K := K)
          (a := fun r : ℝ ↦ φ r) (b := fun r : ℝ ↦ ψ r) (f := g)
          hI_meas hKΩ hg_K hφ_support hψ_support
          (fun r ↦ by
            have hr := le_of_lt (hψ_close r)
            simpa [norm_sub_rev] using hr)
    have hdecomp : Aφ + Bφ = (Aφ - Aψ) + (Bφ - Bψ) := by
      linarith
    have hnorm_sum : ‖Aφ + Bφ‖ ≤ δ * SU + δ * Sg := by
      calc
        ‖Aφ + Bφ‖ = ‖(Aφ - Aψ) + (Bφ - Bψ)‖ := by
          rw [hdecomp]
        _ ≤ ‖Aφ - Aψ‖ + ‖Bφ - Bψ‖ :=
          norm_add_le _ _
        _ ≤ δ * SU + δ * Sg :=
          add_le_add hAerr hBerr
    have hδ_nonneg : 0 ≤ δ := hδ_pos.le
    have hsum_le_S : SU + Sg ≤ S := by
      dsimp [S]
      linarith
    have harith : δ * SU + δ * Sg ≤ ε := by
      calc
        δ * SU + δ * Sg = δ * (SU + Sg) := by ring
        _ ≤ δ * S := mul_le_mul_of_nonneg_left hsum_le_S hδ_nonneg
        _ = ε := by
          simpa [δ] using div_mul_cancel₀ ε hS_pos.ne'
    have hdist : dist (Aφ + Bφ) 0 ≤ ε := by
      simpa [dist_eq_norm] using hnorm_sum.trans harith
    simpa using hdist
  dsimp [Aφ, Bφ, I, g] at hsum_zero ⊢
  linarith

/--
%%handwave
name:
  Countable \(C^1\)-dense test identities determine the one-dimensional weak
  derivative
statement:
  Suppose a sliced function and sliced candidate derivative are locally
  integrable on compact subintervals of \((0,1)\), and suppose the
  integration-by-parts identity holds for every member of a countable family
  that is dense for uniform convergence of a test and its derivative, with
  common compact support control.  Then the identity holds for every smooth
  compactly supported test on \((0,1)\), so the sliced function has the stated
  weak derivative.
proof:
  Given an arbitrary test, choose approximants from the countable family with
  the same compact support control and with both the functions and their
  first derivatives converging uniformly.  Local integrability of the sliced
  function and derivative on that compact set lets the two integrals pass to
  the limit by dominated convergence, and the identities for the approximants
  converge to the desired identity.
-/
theorem realWeakDerivativeOn_Ioo_of_countable_c1_dense_test_data
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : Set
      (SmoothCompactlySupportedManifoldCoordinateFunction
        (Set.Ioo (0 : ℝ) 1))}
    {U : ℝ × E → ℝ}
    {DU : ℝ × E → (ℝ × E) →L[ℝ] ℝ}
    {y : E}
    (_hT_dense :
      ∀ φ : SmoothCompactlySupportedManifoldCoordinateFunction
          (Set.Ioo (0 : ℝ) 1),
        ∃ K : Set ℝ,
          IsCompact K ∧
            K ⊆ Set.Ioo (0 : ℝ) 1 ∧
            tsupport (φ : ℝ → ℝ) ⊆ K ∧
            ∀ ε : ℝ, 0 < ε →
              ∃ ψ ∈ T,
                tsupport (ψ : ℝ → ℝ) ⊆ K ∧
                  (∀ x : ℝ, ‖(ψ : ℝ → ℝ) x - φ x‖ < ε) ∧
                    (∀ x : ℝ,
                      ‖fderiv ℝ (ψ : ℝ → ℝ) x (1 : ℝ) -
                        fderiv ℝ (φ : ℝ → ℝ) x (1 : ℝ)‖ < ε))
    (_hdata : FirstCoordinateSliceWeakDerivativeTestData T U DU y) :
    IsWeakDerivativeOnRealRegionScalar (Set.Ioo (0 : ℝ) 1)
      (fun r : ℝ => U (r, y))
      (fun r : ℝ => DU (r, y) ((1 : ℝ), (0 : E))) := by
  intro φ
  rcases _hT_dense φ with ⟨K, hK_compact, hKΩ, hφ_support, _happrox⟩
  rcases _hdata.1 K hK_compact hKΩ with ⟨hU_K, hDU_K⟩
  have hderiv_cont :
      Continuous (fun r : ℝ ↦ fderiv ℝ (φ : ℝ → ℝ) r (1 : ℝ)) :=
    (φ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have hderiv_support :
      tsupport (fun r : ℝ ↦ fderiv ℝ (φ : ℝ → ℝ) r (1 : ℝ)) ⊆ K :=
    (tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := (φ : ℝ → ℝ)) (1 : ℝ)).trans
      hφ_support
  refine ⟨?_, ?_, ?_⟩
  · exact
      integrable_restrict_smul_of_integrableOn_compact_tsupport_subset
        (Ω := Set.Ioo (0 : ℝ) 1) (K := K)
        (a := fun r : ℝ ↦ fderiv ℝ (φ : ℝ → ℝ) r (1 : ℝ))
        (f := fun r : ℝ ↦ U (r, y))
        hK_compact hU_K hderiv_cont
        (SmoothCompactlySupportedManifoldCoordinateFunction.exists_derivative_bound
          φ (1 : ℝ))
        hderiv_support
  · exact
      integrable_restrict_smul_of_integrableOn_compact_tsupport_subset
        (Ω := Set.Ioo (0 : ℝ) 1) (K := K)
        (a := fun r : ℝ ↦ φ r)
        (f := fun r : ℝ ↦ DU (r, y) ((1 : ℝ), (0 : E)))
        hK_compact hDU_K φ.smooth.continuous
        (SmoothCompactlySupportedManifoldCoordinateFunction.exists_bound φ)
        hφ_support
  · exact
      realWeakDerivativeOn_Ioo_test_identity_of_countable_c1_dense_test_data
        (E := E) (T := T) (U := U) (DU := DU) (y := y)
        _hT_dense _hdata φ

/--
%%handwave
name:
  Integrability on a product cylinder gives integrability on almost every
  vertical section
statement:
  If a scalar function is integrable on \(K\times C\subset\mathbb R\times E\),
  then for almost every \(y\in C\), the vertical slice \(r\mapsto f(r,y)\) is
  integrable on \(K\).
proof:
  Rewrite Lebesgue measure on the product as the product of the one-dimensional
  and transverse Lebesgue measures.  The restricted product measure on
  \(K\times C\) is the product of the restricted measures, and Fubini gives
  integrability of almost every vertical section.
-/
theorem integrableOn_prod_vertical_slice_ae
    {E : Type} [MeasureSpace E] [SFinite (MeasureTheory.volume : Measure E)]
    {K : Set ℝ} {C : Set E} {f : ℝ × E → ℝ}
    (hf : IntegrableOn f (K ×ˢ C)
      (MeasureTheory.volume : Measure (ℝ × E))) :
    ∀ᵐ y ∂(MeasureTheory.volume.restrict C : Measure E),
      Integrable (fun r : ℝ ↦ f (r, y))
        (MeasureTheory.volume.restrict K) := by
  let μK : Measure ℝ := MeasureTheory.volume.restrict K
  let μC : Measure E := MeasureTheory.volume.restrict C
  have hmeasure :
      (MeasureTheory.volume : Measure (ℝ × E)).restrict (K ×ˢ C) =
        μK.prod μC := by
    rw [Measure.volume_eq_prod]
    exact (Measure.prod_restrict
      (μ := (MeasureTheory.volume : Measure ℝ))
      (ν := (MeasureTheory.volume : Measure E)) K C).symm
  have hf_prod : Integrable f (μK.prod μC) := by
    simpa [IntegrableOn, hmeasure] using hf
  simpa [μK, μC] using hf_prod.prod_left_ae

/--
%%handwave
name:
  Integrability on a measurable product subset gives integrability on almost
  every vertical section
statement:
  If a scalar function is integrable on a measurable subset
  \(S\subset\mathbb R\times E\), then for almost every transverse coordinate
  \(y\), the vertical slice is integrable on the section
  \(\{r:(r,y)\in S\}\).
proof:
  Extend the function by zero off \(S\).  The extension is globally
  integrable, and Fubini gives integrability of almost every vertical slice.
  On each slice this zero extension is the indicator of the vertical section
  times the original sliced function.
-/
theorem integrableOn_vertical_slice_ae_of_integrableOn_measurable
    {E : Type} [MeasureSpace E] [SFinite (MeasureTheory.volume : Measure E)]
    {S : Set (ℝ × E)} {f : ℝ × E → ℝ}
    (hS : MeasurableSet S)
    (hf : IntegrableOn f S
      (MeasureTheory.volume : Measure (ℝ × E))) :
    ∀ᵐ y ∂(MeasureTheory.volume : Measure E),
      IntegrableOn (fun r : ℝ ↦ f (r, y))
        {r : ℝ | ((r, y) : ℝ × E) ∈ S}
        (MeasureTheory.volume : Measure ℝ) := by
  let F : ℝ × E → ℝ := S.indicator f
  have hF_volume : Integrable F (MeasureTheory.volume : Measure (ℝ × E)) :=
    hf.integrable_indicator hS
  have hF_prod :
      Integrable F
        ((MeasureTheory.volume : Measure ℝ).prod
          (MeasureTheory.volume : Measure E)) := by
    simpa [Measure.volume_eq_prod] using hF_volume
  have hslices :
      ∀ᵐ y ∂(MeasureTheory.volume : Measure E),
        Integrable (fun r : ℝ ↦ F (r, y))
          (MeasureTheory.volume : Measure ℝ) :=
    hF_prod.prod_left_ae
  filter_upwards [hslices] with y hy
  let Sy : Set ℝ := {r : ℝ | ((r, y) : ℝ × E) ∈ S}
  have hSy_meas : MeasurableSet Sy := by
    exact hS.preimage measurable_prodMk_right
  have hslice_indicator :
      (fun r : ℝ ↦ F (r, y)) =
        Sy.indicator (fun r : ℝ ↦ f (r, y)) := by
    funext r
    by_cases hr : ((r, y) : ℝ × E) ∈ S
    · simp [F, Sy, hr]
    · simp [F, Sy, hr]
  exact (integrable_indicator_iff hSy_meas).1 (by simpa [hslice_indicator] using hy)

/--
%%handwave
name:
  Locally integrable functions on the strip have locally integrable vertical
  slices
statement:
  If a scalar function is locally integrable on the product strip
  \((0,1)\times E\), then for almost every transverse coordinate its vertical
  slice is integrable on every compact subinterval of \((0,1)\).
proof:
  Apply Fubini on compact cylinders \(K\times B\), where \(K\Subset(0,1)\)
  and \(B\) runs through a countable compact exhaustion of \(E\).  A countable
  basis for \((0,1)\) then upgrades the conclusion to all compact
  subintervals.
-/
theorem locallyIntegrableOn_unit_strip_vertical_slices_ae
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)]
    [FiniteDimensional ℝ E]
    {f : ℝ × E → ℝ}
    (hf : LocallyIntegrableOn f
      {p : ℝ × E | 0 < p.1 ∧ p.1 < 1}
      (MeasureTheory.volume : Measure (ℝ × E))) :
    ∀ᵐ y ∂(MeasureTheory.volume : Measure E),
      ∀ K : Set ℝ, IsCompact K → K ⊆ Set.Ioo (0 : ℝ) 1 →
        IntegrableOn (fun r : ℝ ↦ f (r, y)) K
          (MeasureTheory.volume : Measure ℝ) := by
  let Ω : Set (ℝ × E) := {p : ℝ × E | 0 < p.1 ∧ p.1 < 1}
  have hΩ_open : IsOpen Ω := by
    exact (isOpen_lt continuous_const continuous_fst).inter
      (isOpen_lt continuous_fst continuous_const)
  rcases hf.exists_nat_integrableOn with ⟨U, hU_open, hΩ_cover, hU_int⟩
  have hsections :
      ∀ᵐ y ∂(MeasureTheory.volume : Measure E),
        ∀ n : ℕ,
          IntegrableOn (fun r : ℝ ↦ f (r, y))
            {r : ℝ | ((r, y) : ℝ × E) ∈ U n ∩ Ω}
            (MeasureTheory.volume : Measure ℝ) := by
    rw [ae_all_iff]
    intro n
    exact
      integrableOn_vertical_slice_ae_of_integrableOn_measurable
        (E := E) (S := U n ∩ Ω) (f := f)
        ((hU_open n).measurableSet.inter hΩ_open.measurableSet)
        (hU_int n)
  filter_upwards [hsections] with y hy_sections
  have hslice_loc :
      LocallyIntegrableOn (fun r : ℝ ↦ f (r, y))
        (Set.Ioo (0 : ℝ) 1) (MeasureTheory.volume : Measure ℝ) := by
    intro r hr
    have hpΩ : ((r, y) : ℝ × E) ∈ Ω := by
      simpa [Ω] using hr
    obtain ⟨n, hn⟩ : ∃ n : ℕ, ((r, y) : ℝ × E) ∈ U n := by
      simpa [Set.mem_iUnion] using hΩ_cover hpΩ
    let Sy : Set ℝ := {a : ℝ | ((a, y) : ℝ × E) ∈ U n ∩ Ω}
    have hSy_int : IntegrableOn (fun a : ℝ ↦ f (a, y)) Sy
        (MeasureTheory.volume : Measure ℝ) := by
      simpa [Sy] using hy_sections n
    have hSy_open : IsOpen Sy := by
      have hcont : Continuous (fun a : ℝ ↦ ((a, y) : ℝ × E)) := by
        fun_prop
      exact ((hU_open n).inter hΩ_open).preimage hcont
    have hrSy : r ∈ Sy := by
      exact ⟨hn, hpΩ⟩
    refine ⟨Sy, ?_, hSy_int⟩
    exact mem_nhdsWithin_of_mem_nhds (hSy_open.mem_nhds hrSy)
  have hcompact :
      ∀ K : Set ℝ, K ⊆ Set.Ioo (0 : ℝ) 1 → IsCompact K →
        IntegrableOn (fun r : ℝ ↦ f (r, y)) K
          (MeasureTheory.volume : Measure ℝ) := by
    rw [locallyIntegrableOn_iff isOpen_Ioo.isLocallyClosed] at hslice_loc
    exact hslice_loc
  intro K hK hKΩ
  exact hcompact K hKΩ hK

/--
%%handwave
name:
  Product weak derivatives give local integrability on almost every slice
statement:
  For a Sobolev function on the product strip, the vertical slice of the
  function and of its first-coordinate weak derivative are integrable on every
  compact subinterval of \((0,1)\), for almost every transverse coordinate.
proof:
  Restrict the product Sobolev data to \(K\times B\), where \(K\) is the
  compact subinterval and \(B\) is a bounded measurable transverse set, and
  apply Fubini.  Exhaust the transverse space by countably many bounded sets.
-/
theorem scalarWeakSobolev_firstCoordinate_slice_local_integrability_ae_on_unit_strip
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)]
    [FiniteDimensional ℝ E]
    {U : ℝ × E → ℝ}
    {DU : ℝ × E → (ℝ × E) →L[ℝ] ℝ}
    (_hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      {p : ℝ × E | 0 < p.1 ∧ p.1 < 1} U DU) :
    ∀ᵐ y ∂(MeasureTheory.volume : Measure E),
      ∀ K : Set ℝ, IsCompact K → K ⊆ Set.Ioo (0 : ℝ) 1 →
        IntegrableOn (fun r : ℝ ↦ U (r, y)) K
          (MeasureTheory.volume : Measure ℝ) ∧
        IntegrableOn
          (fun r : ℝ ↦ DU (r, y) ((1 : ℝ), (0 : E))) K
          (MeasureTheory.volume : Measure ℝ) := by
  let Ω : Set (ℝ × E) := {p : ℝ × E | 0 < p.1 ∧ p.1 < 1}
  have hΩ_open : IsOpen Ω := by
    exact (isOpen_lt continuous_const continuous_fst).inter
      (isOpen_lt continuous_fst continuous_const)
  let e : ℝ × E := ((1 : ℝ), (0 : E))
  have he_ne : e ≠ 0 := by
    intro h
    have hfst := congrArg Prod.fst h
    norm_num [e] at hfst
  haveI hprod_haar :
      Measure.IsAddHaarMeasure
        (MeasureTheory.volume : Measure (ℝ × E)) := by
    rw [Measure.volume_eq_prod]
    infer_instance
  have hU_loc : LocallyIntegrableOn U Ω
      (MeasureTheory.volume : Measure (ℝ × E)) :=
    scalarWeakSobolev_function_locallyIntegrableOn_of_nonzero_direction
      (H := ℝ × E) (Ω := Ω) hΩ_open _hweak he_ne
  have hDU_loc : LocallyIntegrableOn (fun z : ℝ × E ↦ DU z e) Ω
      (MeasureTheory.volume : Measure (ℝ × E)) :=
    scalarWeakSobolev_directionalDerivative_locallyIntegrableOn
      (H := ℝ × E) (Ω := Ω) hΩ_open _hweak e
  have hU_slices :
      ∀ᵐ y ∂(MeasureTheory.volume : Measure E),
        ∀ K : Set ℝ, IsCompact K → K ⊆ Set.Ioo (0 : ℝ) 1 →
          IntegrableOn (fun r : ℝ ↦ U (r, y)) K
            (MeasureTheory.volume : Measure ℝ) :=
    locallyIntegrableOn_unit_strip_vertical_slices_ae
      (E := E) (f := U) hU_loc
  have hDU_slices :
      ∀ᵐ y ∂(MeasureTheory.volume : Measure E),
        ∀ K : Set ℝ, IsCompact K → K ⊆ Set.Ioo (0 : ℝ) 1 →
          IntegrableOn
            (fun r : ℝ ↦ DU (r, y) ((1 : ℝ), (0 : E))) K
            (MeasureTheory.volume : Measure ℝ) := by
    simpa [e] using
      locallyIntegrableOn_unit_strip_vertical_slices_ae
        (E := E) (f := fun z : ℝ × E ↦ DU z e) hDU_loc
  filter_upwards [hU_slices, hDU_slices] with y hU_y hDU_y
  intro K hK hKΩ
  exact ⟨hU_y K hK hKΩ, hDU_y K hK hKΩ⟩

/--
%%handwave
name:
  Compactly supported first-coordinate pairings are locally integrable
statement:
  Let \(f\) be locally integrable on the product strip
  \((0,1)\times E\).  If \(a\) is a bounded continuous function of the first
  coordinate whose support is contained in a compact set
  \(K\Subset(0,1)\), then
  \[
    y\mapsto \int_0^1 a(r)f(r,y)\,dr
  \]
  is locally integrable in \(y\).
proof:
  On each compact transverse set \(C\), the product \(K\times C\) is compact
  and contained in the strip, hence \(f\) is integrable there.  Bounded
  multiplication by \(a\) preserves integrability.  Fubini then gives
  integrability of the iterated integral over \(C\), and the support of \(a\)
  replaces the integral over \(K\) by the integral over \((0,1)\).
-/
theorem compactlySupported_firstCoordinate_slicedIntegral_locallyIntegrable_on_unit_strip
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)]
    [FiniteDimensional ℝ E]
    {a : ℝ → ℝ} {f : ℝ × E → ℝ} {K : Set ℝ}
    (hK : IsCompact K) (hK_strip : K ⊆ Set.Ioo (0 : ℝ) 1)
    (hf : LocallyIntegrableOn f
      {p : ℝ × E | 0 < p.1 ∧ p.1 < 1}
      (MeasureTheory.volume : Measure (ℝ × E)))
    (ha_cont : Continuous a)
    (ha_bound : ∃ C : NNReal, ∀ r : ℝ, ‖a r‖ ≤ C)
    (ha_support : tsupport a ⊆ K) :
    LocallyIntegrable
      (fun y : E ↦ ∫ r in Set.Ioo (0 : ℝ) 1,
        a r • f (r, y) ∂MeasureTheory.volume)
      (MeasureTheory.volume : Measure E) := by
  let I : Set ℝ := Set.Ioo (0 : ℝ) 1
  let Ω : Set (ℝ × E) := {p : ℝ × E | 0 < p.1 ∧ p.1 < 1}
  have hΩ_open : IsOpen Ω := by
    exact (isOpen_lt continuous_const continuous_fst).inter
      (isOpen_lt continuous_fst continuous_const)
  have hI_meas : MeasurableSet I := measurableSet_Ioo
  have hloc_on :
      LocallyIntegrableOn
        (fun y : E ↦ ∫ r in I, a r • f (r, y) ∂MeasureTheory.volume)
        Set.univ (MeasureTheory.volume : Measure E) := by
    rw [locallyIntegrableOn_iff isOpen_univ.isLocallyClosed]
    intro C _hC_univ hC
    have hKC_compact : IsCompact (K ×ˢ C) := hK.prod hC
    have hKC_subset : K ×ˢ C ⊆ Ω := by
      rintro ⟨r, y⟩ ⟨hrK, _hyC⟩
      simpa [Ω] using hK_strip hrK
    have hfKC : IntegrableOn f (K ×ˢ C)
        (MeasureTheory.volume : Measure (ℝ × E)) := by
      have hcompact_integrable :=
        (locallyIntegrableOn_iff hΩ_open.isLocallyClosed).1 hf
      exact hcompact_integrable (K ×ˢ C) hKC_subset hKC_compact
    rcases ha_bound with ⟨M, hM⟩
    have hmulKC : IntegrableOn
        (fun p : ℝ × E ↦ a p.1 * f p) (K ×ˢ C)
        (MeasureTheory.volume : Measure (ℝ × E)) := by
      exact hfKC.bdd_mul
        ((ha_cont.comp continuous_fst).aestronglyMeasurable)
        (ae_restrict_of_forall_mem hKC_compact.measurableSet fun p _hp ↦ hM p.1)
    let μK : Measure ℝ := MeasureTheory.volume.restrict K
    let μC : Measure E := MeasureTheory.volume.restrict C
    have hmeasure :
        (MeasureTheory.volume : Measure (ℝ × E)).restrict (K ×ˢ C) =
          μK.prod μC := by
      rw [Measure.volume_eq_prod]
      exact (Measure.prod_restrict
        (μ := (MeasureTheory.volume : Measure ℝ))
        (ν := (MeasureTheory.volume : Measure E)) K C).symm
    have hmul_prod : Integrable (fun p : ℝ × E ↦ a p.1 * f p)
        (μK.prod μC) := by
      simpa [IntegrableOn, hmeasure] using hmulKC
    have hiter : Integrable
        (fun y : E ↦ ∫ r, a r * f (r, y) ∂μK) μC := by
      simpa [μK, μC] using hmul_prod.integral_prod_right
    refine hiter.congr ?_
    refine ae_restrict_of_forall_mem hC.measurableSet ?_
    intro y _hyC
    have hlocal :
        ∫ r in I, a r • f (r, y) ∂MeasureTheory.volume =
          ∫ r in K, a r * f (r, y) ∂MeasureTheory.volume := by
      have hzero :
          ∀ r ∈ I \ K, a r * f (r, y) = 0 := by
        intro r hr
        have hr_not : r ∉ tsupport a := fun hrs ↦ hr.2 (ha_support hrs)
        have ha0 : a r = 0 := image_eq_zero_of_notMem_tsupport hr_not
        simp [ha0]
      calc
        ∫ r in I, a r • f (r, y) ∂MeasureTheory.volume
            = ∫ r in I, a r * f (r, y) ∂MeasureTheory.volume := by
              simp [smul_eq_mul]
        _ = ∫ r in K, a r * f (r, y) ∂MeasureTheory.volume :=
          setIntegral_eq_of_subset_of_forall_diff_eq_zero hI_meas hK_strip hzero
    simpa [μK] using hlocal.symm
  exact locallyIntegrableOn_univ.mp hloc_on

/--
%%handwave
name:
  Residual of the sliced first-coordinate identity for one test
statement:
  For a fixed smooth compactly supported one-dimensional test \(\psi\), the
  residual on a transverse point \(y\) is the sum of the two sliced
  integration-by-parts terms,
  \[
    \int_0^1 \psi'(r)U(r,y)\,dr+
    \int_0^1 \psi(r)DU(r,y)[(1,0)]\,dr .
  \]
-/
def firstCoordinateSliceWeakDerivativeResidual
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ψ : SmoothCompactlySupportedManifoldCoordinateFunction
        (Set.Ioo (0 : ℝ) 1))
    (U : ℝ × E → ℝ)
    (DU : ℝ × E → (ℝ × E) →L[ℝ] ℝ) : E → ℝ :=
  fun y : E ↦
    (∫ r in Set.Ioo (0 : ℝ) 1,
        (fderiv ℝ (ψ : ℝ → ℝ) r (1 : ℝ)) • U (r, y)
        ∂MeasureTheory.volume) +
      ∫ r in Set.Ioo (0 : ℝ) 1,
        ψ r • DU (r, y) ((1 : ℝ), (0 : E))
        ∂MeasureTheory.volume

/--
%%handwave
name:
  The sliced first-coordinate residual is locally integrable
statement:
  For a Sobolev function on the product strip and a fixed one-dimensional
  smooth compactly supported test, the residual of the sliced
  first-coordinate identity is locally integrable in the transverse variable.
proof:
  The Sobolev function and its first-coordinate weak derivative are locally
  integrable on the product strip.  Apply the compactly supported
  first-coordinate pairing lemma to \(\psi'\) and to \(\psi\), then add the
  two locally integrable transverse functions.
-/
theorem firstCoordinateSliceWeakDerivativeResidual_locallyIntegrable_on_unit_strip
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)]
    [FiniteDimensional ℝ E]
    {U : ℝ × E → ℝ}
    {DU : ℝ × E → (ℝ × E) →L[ℝ] ℝ}
    (ψ : SmoothCompactlySupportedManifoldCoordinateFunction
        (Set.Ioo (0 : ℝ) 1))
    (_hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      {p : ℝ × E | 0 < p.1 ∧ p.1 < 1} U DU) :
    LocallyIntegrable
        (firstCoordinateSliceWeakDerivativeResidual (E := E) ψ U DU)
        (MeasureTheory.volume : Measure E) := by
  let Ω : Set (ℝ × E) := {p : ℝ × E | 0 < p.1 ∧ p.1 < 1}
  have hΩ_open : IsOpen Ω := by
    exact (isOpen_lt continuous_const continuous_fst).inter
      (isOpen_lt continuous_fst continuous_const)
  let e : ℝ × E := ((1 : ℝ), (0 : E))
  have he_ne : e ≠ 0 := by
    intro h
    have hfst := congrArg Prod.fst h
    norm_num [e] at hfst
  haveI hprod_haar :
      Measure.IsAddHaarMeasure
        (MeasureTheory.volume : Measure (ℝ × E)) := by
    rw [Measure.volume_eq_prod]
    infer_instance
  have hU_loc : LocallyIntegrableOn U Ω
      (MeasureTheory.volume : Measure (ℝ × E)) :=
    scalarWeakSobolev_function_locallyIntegrableOn_of_nonzero_direction
      (H := ℝ × E) (Ω := Ω) hΩ_open _hweak he_ne
  have hDU_loc : LocallyIntegrableOn (fun z : ℝ × E ↦ DU z e) Ω
      (MeasureTheory.volume : Measure (ℝ × E)) :=
    scalarWeakSobolev_directionalDerivative_locallyIntegrableOn
      (H := ℝ × E) (Ω := Ω) hΩ_open _hweak e
  let K : Set ℝ := tsupport (ψ : ℝ → ℝ)
  have hderiv_cont :
      Continuous (fun r : ℝ ↦ fderiv ℝ (ψ : ℝ → ℝ) r (1 : ℝ)) :=
    (ψ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have hderiv_support :
      tsupport (fun r : ℝ ↦ fderiv ℝ (ψ : ℝ → ℝ) r (1 : ℝ)) ⊆ K :=
    tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := (ψ : ℝ → ℝ)) (1 : ℝ)
  have hleft : LocallyIntegrable
      (fun y : E ↦ ∫ r in Set.Ioo (0 : ℝ) 1,
        (fderiv ℝ (ψ : ℝ → ℝ) r (1 : ℝ)) • U (r, y)
        ∂MeasureTheory.volume)
      (MeasureTheory.volume : Measure E) :=
    compactlySupported_firstCoordinate_slicedIntegral_locallyIntegrable_on_unit_strip
      (E := E) (a := fun r : ℝ ↦ fderiv ℝ (ψ : ℝ → ℝ) r (1 : ℝ))
      (f := U) (K := K)
      ψ.compact_support ψ.support_subset hU_loc hderiv_cont
      (SmoothCompactlySupportedManifoldCoordinateFunction.exists_derivative_bound
        ψ (1 : ℝ))
      hderiv_support
  have hright : LocallyIntegrable
      (fun y : E ↦ ∫ r in Set.Ioo (0 : ℝ) 1,
        ψ r • DU (r, y) e ∂MeasureTheory.volume)
      (MeasureTheory.volume : Measure E) :=
    compactlySupported_firstCoordinate_slicedIntegral_locallyIntegrable_on_unit_strip
      (E := E) (a := fun r : ℝ ↦ ψ r)
      (f := fun z : ℝ × E ↦ DU z e) (K := K)
      ψ.compact_support ψ.support_subset hDU_loc ψ.smooth.continuous
      (SmoothCompactlySupportedManifoldCoordinateFunction.exists_bound ψ)
      (by intro r hr; exact hr)
  have hsum := hleft.add hright
  simpa [firstCoordinateSliceWeakDerivativeResidual, e] using hsum

/--
%%handwave
name:
  The sliced first-coordinate residual has zero transverse test pairings
statement:
  For a Sobolev function on the product strip and a fixed one-dimensional
  smooth compactly supported test, the residual of the sliced
  first-coordinate identity integrates to zero against every smooth compactly
  supported transverse test.
proof:
  Multiply the one-dimensional test by the transverse test and insert the
  product into the product weak-derivative identity.  The derivative in the
  first-coordinate direction differentiates only the one-dimensional factor.
  Fubini rewrites the product identity as the asserted transverse pairing.
-/
theorem scalarWeakSobolev_firstCoordinate_one_test_slice_residual_pairing_zero_on_unit_strip
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)]
    [FiniteDimensional ℝ E]
    {U : ℝ × E → ℝ}
    {DU : ℝ × E → (ℝ × E) →L[ℝ] ℝ}
    (ψ : SmoothCompactlySupportedManifoldCoordinateFunction
        (Set.Ioo (0 : ℝ) 1))
    (_hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      {p : ℝ × E | 0 < p.1 ∧ p.1 < 1} U DU) :
    ∀ θ : E → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      ∫ y, θ y •
          firstCoordinateSliceWeakDerivativeResidual (E := E) ψ U DU y
          ∂(MeasureTheory.volume : Measure E) = 0 := by
  intro θ hθ_smooth hθ_compact
  let I : Set ℝ := Set.Ioo (0 : ℝ) 1
  let Ω : Set (ℝ × E) := {p : ℝ × E | 0 < p.1 ∧ p.1 < 1}
  let e : ℝ × E := ((1 : ℝ), (0 : E))
  let μℝ : Measure ℝ := MeasureTheory.volume
  let μE : Measure E := MeasureTheory.volume
  have hΩ_eq : Ω = I ×ˢ (Set.univ : Set E) := by
    ext p
    simp [Ω, I]
  let Φ : SmoothCompactlySupportedManifoldCoordinateFunction Ω :=
    { toFun := fun p : ℝ × E ↦ (ψ : ℝ → ℝ) p.1 * θ p.2
      smooth := by
        exact (ψ.smooth.comp contDiff_fst).mul (hθ_smooth.comp contDiff_snd)
      support_subset := by
        intro p hp
        have hp_left :
            p ∈ tsupport (fun q : ℝ × E ↦ (ψ : ℝ → ℝ) q.1) :=
          (tsupport_mul_subset_left
            (f := fun q : ℝ × E ↦ (ψ : ℝ → ℝ) q.1)
            (g := fun q : ℝ × E ↦ θ q.2)) hp
        have hpψ : p.1 ∈ tsupport (ψ : ℝ → ℝ) :=
          (tsupport_comp_subset_preimage (ψ : ℝ → ℝ)
            (f := fun q : ℝ × E ↦ q.1) continuous_fst) hp_left
        simpa [Ω] using ψ.support_subset hpψ
      compact_support := by
        have hsub :
            tsupport (fun p : ℝ × E ↦ (ψ : ℝ → ℝ) p.1 * θ p.2) ⊆
              tsupport (ψ : ℝ → ℝ) ×ˢ tsupport θ := by
          intro p hp
          have hp_left :
              p ∈ tsupport (fun q : ℝ × E ↦ (ψ : ℝ → ℝ) q.1) :=
            (tsupport_mul_subset_left
              (f := fun q : ℝ × E ↦ (ψ : ℝ → ℝ) q.1)
              (g := fun q : ℝ × E ↦ θ q.2)) hp
          have hp_right :
              p ∈ tsupport (fun q : ℝ × E ↦ θ q.2) :=
            (tsupport_mul_subset_right
              (f := fun q : ℝ × E ↦ (ψ : ℝ → ℝ) q.1)
              (g := fun q : ℝ × E ↦ θ q.2)) hp
          exact
            ⟨(tsupport_comp_subset_preimage (ψ : ℝ → ℝ)
                (f := fun q : ℝ × E ↦ q.1) continuous_fst) hp_left,
              (tsupport_comp_subset_preimage θ
                (f := fun q : ℝ × E ↦ q.2) continuous_snd) hp_right⟩
        exact IsCompact.of_isClosed_subset
          (ψ.compact_support.prod hθ_compact) (isClosed_tsupport _) hsub }
  have hΦ_deriv :
      ∀ p : ℝ × E,
        fderiv ℝ (Φ : ℝ × E → ℝ) p e =
          (fderiv ℝ (ψ : ℝ → ℝ) p.1 (1 : ℝ)) * θ p.2 := by
    intro p
    have hψ_diff :
        DifferentiableAt ℝ (fun q : ℝ × E ↦ (ψ : ℝ → ℝ) q.1) p :=
      ((ψ.smooth.differentiable (by simp)) p.1).comp p differentiableAt_fst
    have hθ_diff :
        DifferentiableAt ℝ (fun q : ℝ × E ↦ θ q.2) p :=
      ((hθ_smooth.differentiable (by simp)) p.2).comp p differentiableAt_snd
    have hψ_fderiv :
        fderiv ℝ (fun q : ℝ × E ↦ (ψ : ℝ → ℝ) q.1) p e =
          fderiv ℝ (ψ : ℝ → ℝ) p.1 (1 : ℝ) := by
      have hcomp :
          fderiv ℝ (fun q : ℝ × E ↦ (ψ : ℝ → ℝ) q.1) p =
            (fderiv ℝ (ψ : ℝ → ℝ) p.1).comp
              (fderiv ℝ (fun q : ℝ × E ↦ q.1) p) :=
        fderiv_comp'
          (x := p) (f := fun q : ℝ × E ↦ q.1)
          (g := (ψ : ℝ → ℝ))
          (((ψ.smooth.differentiable (by simp)) p.1))
          differentiableAt_fst
      rw [hcomp]
      simp [fderiv_fst, e]
    have hθ_fderiv :
        fderiv ℝ (fun q : ℝ × E ↦ θ q.2) p e = 0 := by
      have hcomp :
          fderiv ℝ (fun q : ℝ × E ↦ θ q.2) p =
            (fderiv ℝ θ p.2).comp
              (fderiv ℝ (fun q : ℝ × E ↦ q.2) p) :=
        fderiv_comp'
          (x := p) (f := fun q : ℝ × E ↦ q.2)
          (g := θ)
          (((hθ_smooth.differentiable (by simp)) p.2))
          differentiableAt_snd
      rw [hcomp]
      simp [fderiv_snd, e]
    change
      fderiv ℝ
          (fun q : ℝ × E ↦ (ψ : ℝ → ℝ) q.1 * θ q.2) p e =
        (fderiv ℝ (ψ : ℝ → ℝ) p.1 (1 : ℝ)) * θ p.2
    rw [fderiv_fun_mul hψ_diff hθ_diff]
    simp [hψ_fderiv, hθ_fderiv, mul_comm]
  rcases _hweak Φ e with ⟨hweak_left_int, hweak_right_int, hweak_eq⟩
  let Fleft : ℝ × E → ℝ :=
    fun p ↦ ((fderiv ℝ (ψ : ℝ → ℝ) p.1 (1 : ℝ)) * θ p.2) * U p
  let Fright : ℝ × E → ℝ :=
    fun p ↦ ((ψ : ℝ → ℝ) p.1 * θ p.2) * DU p e
  have hleft_int_on : IntegrableOn Fleft (I ×ˢ (Set.univ : Set E)) (μℝ.prod μE) := by
    have hleft :
        Integrable Fleft ((MeasureTheory.volume : Measure (ℝ × E)).restrict Ω) := by
      refine hweak_left_int.congr ?_
      exact ae_of_all _ fun p ↦ by
        simp [Fleft, hΦ_deriv p, smul_eq_mul]
    simpa [IntegrableOn, μℝ, μE, hΩ_eq, Measure.volume_eq_prod] using hleft
  have hright_int_on : IntegrableOn Fright (I ×ˢ (Set.univ : Set E)) (μℝ.prod μE) := by
    have hright :
        Integrable Fright ((MeasureTheory.volume : Measure (ℝ × E)).restrict Ω) := by
      refine hweak_right_int.congr ?_
      exact ae_of_all _ fun p ↦ by
        simp [Fright, Φ, e, smul_eq_mul]
    simpa [IntegrableOn, μℝ, μE, hΩ_eq, Measure.volume_eq_prod] using hright
  have hleft_prod_int :
      Integrable Fleft ((μℝ.restrict I).prod μE) := by
    have hmeasure :
        (μℝ.prod μE).restrict (I ×ˢ (Set.univ : Set E)) =
          (μℝ.restrict I).prod μE := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    simpa [IntegrableOn, hmeasure]
      using hleft_int_on
  have hright_prod_int :
      Integrable Fright ((μℝ.restrict I).prod μE) := by
    have hmeasure :
        (μℝ.prod μE).restrict (I ×ˢ (Set.univ : Set E)) =
          (μℝ.restrict I).prod μE := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    simpa [IntegrableOn, hmeasure]
      using hright_int_on
  have hleft_iter_int :
      Integrable
        (fun y : E ↦ ∫ r, Fleft (r, y) ∂(μℝ.restrict I)) μE :=
    hleft_prod_int.integral_prod_right
  have hright_iter_int :
      Integrable
        (fun y : E ↦ ∫ r, Fright (r, y) ∂(μℝ.restrict I)) μE :=
    hright_prod_int.integral_prod_right
  let L : E → ℝ :=
    fun y ↦ ∫ r in I,
      (fderiv ℝ (ψ : ℝ → ℝ) r (1 : ℝ)) • U (r, y) ∂MeasureTheory.volume
  let R : E → ℝ :=
    fun y ↦ ∫ r in I,
      ψ r • DU (r, y) e ∂MeasureTheory.volume
  have hleft_iter_eq :
      (fun y : E ↦ ∫ r, Fleft (r, y) ∂(μℝ.restrict I)) =
        fun y : E ↦ θ y • L y := by
    funext y
    calc
      ∫ r, Fleft (r, y) ∂(μℝ.restrict I) =
          ∫ r in I, θ y *
            ((fderiv ℝ (ψ : ℝ → ℝ) r (1 : ℝ)) * U (r, y))
            ∂MeasureTheory.volume := by
            apply integral_congr_ae
            exact ae_of_all _ fun r ↦ by
              simp [Fleft, smul_eq_mul]
              ring
      _ = θ y *
          ∫ r in I,
            (fderiv ℝ (ψ : ℝ → ℝ) r (1 : ℝ)) * U (r, y)
            ∂MeasureTheory.volume := by
            rw [integral_const_mul]
      _ = θ y • L y := by
            simp [L, smul_eq_mul]
  have hright_iter_eq :
      (fun y : E ↦ ∫ r, Fright (r, y) ∂(μℝ.restrict I)) =
        fun y : E ↦ θ y • R y := by
    funext y
    calc
      ∫ r, Fright (r, y) ∂(μℝ.restrict I) =
          ∫ r in I, θ y * ((ψ : ℝ → ℝ) r * DU (r, y) e)
            ∂MeasureTheory.volume := by
            apply integral_congr_ae
            exact ae_of_all _ fun r ↦ by
              simp [Fright]
              ring
      _ = θ y *
          ∫ r in I, (ψ : ℝ → ℝ) r * DU (r, y) e
            ∂MeasureTheory.volume := by
            rw [integral_const_mul]
      _ = θ y • R y := by
            simp [R, smul_eq_mul]
  have hθL_int : Integrable (fun y : E ↦ θ y • L y) μE := by
    simpa [hleft_iter_eq] using hleft_iter_int
  have hθR_int : Integrable (fun y : E ↦ θ y • R y) μE := by
    simpa [hright_iter_eq] using hright_iter_int
  have hleft_fubini :
      ∫ p in Ω,
          (fderiv ℝ (Φ : ℝ × E → ℝ) p e) • U p
          ∂(MeasureTheory.volume : Measure (ℝ × E)) =
        ∫ y, θ y • L y ∂μE := by
    calc
      ∫ p in Ω,
          (fderiv ℝ (Φ : ℝ × E → ℝ) p e) • U p
          ∂(MeasureTheory.volume : Measure (ℝ × E))
          = ∫ p in I ×ˢ (Set.univ : Set E),
              (fderiv ℝ (Φ : ℝ × E → ℝ) p e) • U p
              ∂(μℝ.prod μE) := by
            simp [hΩ_eq, μℝ, μE, Measure.volume_eq_prod]
      _ = ∫ p in I ×ˢ (Set.univ : Set E), Fleft p ∂(μℝ.prod μE) := by
            apply integral_congr_ae
            exact ae_of_all _ fun p ↦ by
              simp [Fleft, hΦ_deriv p, smul_eq_mul]
      _ = ∫ p, Fleft p ∂((μℝ.restrict I).prod μE) := by
            have hmeasure :
                (μℝ.prod μE).restrict (I ×ˢ (Set.univ : Set E)) =
                  (μℝ.restrict I).prod μE := by
              rw [← Measure.prod_restrict, Measure.restrict_univ]
            rw [hmeasure]
      _ = ∫ y, ∫ r, Fleft (r, y) ∂(μℝ.restrict I) ∂μE := by
            rw [MeasureTheory.integral_prod Fleft hleft_prod_int]
            exact MeasureTheory.integral_integral_swap hleft_prod_int
      _ = ∫ y, θ y • L y ∂μE := by
            rw [hleft_iter_eq]
  have hright_fubini :
      ∫ p in Ω, Φ p • DU p e
          ∂(MeasureTheory.volume : Measure (ℝ × E)) =
        ∫ y, θ y • R y ∂μE := by
    calc
      ∫ p in Ω, Φ p • DU p e
          ∂(MeasureTheory.volume : Measure (ℝ × E))
          = ∫ p in I ×ˢ (Set.univ : Set E), Φ p • DU p e
              ∂(μℝ.prod μE) := by
            simp [hΩ_eq, μℝ, μE, Measure.volume_eq_prod]
      _ = ∫ p in I ×ˢ (Set.univ : Set E), Fright p ∂(μℝ.prod μE) := by
            apply integral_congr_ae
            exact ae_of_all _ fun p ↦ by
              simp [Fright, Φ, e, smul_eq_mul]
      _ = ∫ p, Fright p ∂((μℝ.restrict I).prod μE) := by
            have hmeasure :
                (μℝ.prod μE).restrict (I ×ˢ (Set.univ : Set E)) =
                  (μℝ.restrict I).prod μE := by
              rw [← Measure.prod_restrict, Measure.restrict_univ]
            rw [hmeasure]
      _ = ∫ y, ∫ r, Fright (r, y) ∂(μℝ.restrict I) ∂μE := by
            rw [MeasureTheory.integral_prod Fright hright_prod_int]
            exact MeasureTheory.integral_integral_swap hright_prod_int
      _ = ∫ y, θ y • R y ∂μE := by
            rw [hright_iter_eq]
  have hpair_eq : ∫ y, θ y • L y ∂μE = -∫ y, θ y • R y ∂μE := by
    calc
      ∫ y, θ y • L y ∂μE =
          ∫ p in Ω,
            (fderiv ℝ (Φ : ℝ × E → ℝ) p e) • U p
            ∂(MeasureTheory.volume : Measure (ℝ × E)) := hleft_fubini.symm
      _ = -∫ p in Ω, Φ p • DU p e
            ∂(MeasureTheory.volume : Measure (ℝ × E)) := hweak_eq
      _ = -∫ y, θ y • R y ∂μE := by
            rw [hright_fubini]
  have hsum_zero : ∫ y, θ y • (L y + R y) ∂μE = 0 := by
    calc
      ∫ y, θ y • (L y + R y) ∂μE =
          ∫ y, (θ y • L y + θ y • R y) ∂μE := by
            apply integral_congr_ae
            exact ae_of_all _ fun y ↦ by
              simp [smul_eq_mul]
              ring
      _ = ∫ y, θ y • L y ∂μE + ∫ y, θ y • R y ∂μE := by
            rw [integral_add hθL_int hθR_int]
      _ = 0 := by
            linarith
  simpa [firstCoordinateSliceWeakDerivativeResidual, L, R, e, μE] using hsum_zero

/--
%%handwave
name:
  The residual of the sliced first-coordinate identity is zero as a
  transverse distribution
statement:
  For a Sobolev function on the product strip and a fixed one-dimensional
  smooth compactly supported test, the residual of the sliced
  first-coordinate identity is locally integrable in the transverse variable
  and its integral against every smooth compactly supported transverse test
  is zero.
proof:
  Multiply the fixed one-dimensional test by an arbitrary transverse test and
  insert the product into the product weak-derivative identity.  Fubini
  rewrites the product identity as the vanishing of the transverse pairing of
  the residual; compact support and local integrability give local
  integrability of the residual.
-/
theorem scalarWeakSobolev_firstCoordinate_one_test_slice_residual_distribution_zero_on_unit_strip
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)]
    [FiniteDimensional ℝ E]
    {U : ℝ × E → ℝ}
    {DU : ℝ × E → (ℝ × E) →L[ℝ] ℝ}
    (ψ : SmoothCompactlySupportedManifoldCoordinateFunction
        (Set.Ioo (0 : ℝ) 1))
    (_hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      {p : ℝ × E | 0 < p.1 ∧ p.1 < 1} U DU) :
    LocallyIntegrable
        (firstCoordinateSliceWeakDerivativeResidual (E := E) ψ U DU)
        (MeasureTheory.volume : Measure E) ∧
      ∀ θ : E → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
        ∫ y, θ y •
            firstCoordinateSliceWeakDerivativeResidual (E := E) ψ U DU y
            ∂(MeasureTheory.volume : Measure E) = 0 := by
  exact
    ⟨firstCoordinateSliceWeakDerivativeResidual_locallyIntegrable_on_unit_strip
        (E := E) (U := U) (DU := DU) ψ _hweak,
      scalarWeakSobolev_firstCoordinate_one_test_slice_residual_pairing_zero_on_unit_strip
        (E := E) (U := U) (DU := DU) ψ _hweak⟩

/--
%%handwave
name:
  The product weak derivative identity disintegrates for one vertical test
statement:
  Fix a smooth compactly supported test in the vertical variable.  For a
  Sobolev function on the product strip, Fubini disintegrates the
  first-coordinate weak-derivative identity into the corresponding
  one-dimensional identity on almost every vertical slice.
proof:
  Pair the fixed vertical test with smooth compactly supported transverse
  tests and use the product weak-derivative identity.  Fubini rewrites the
  result as equality of two locally integrable transverse distributions, so
  the sliced scalar integrals agree almost everywhere.
-/
theorem scalarWeakSobolev_firstCoordinate_one_test_slice_integral_eq_ae_on_unit_strip
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)]
    [FiniteDimensional ℝ E]
    {U : ℝ × E → ℝ}
    {DU : ℝ × E → (ℝ × E) →L[ℝ] ℝ}
    (ψ : SmoothCompactlySupportedManifoldCoordinateFunction
        (Set.Ioo (0 : ℝ) 1))
    (_hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      {p : ℝ × E | 0 < p.1 ∧ p.1 < 1} U DU) :
    ∀ᵐ y ∂(MeasureTheory.volume : Measure E),
      ∫ r in Set.Ioo (0 : ℝ) 1,
          (fderiv ℝ (ψ : ℝ → ℝ) r (1 : ℝ)) • U (r, y)
          ∂MeasureTheory.volume =
        -∫ r in Set.Ioo (0 : ℝ) 1,
          ψ r • DU (r, y) ((1 : ℝ), (0 : E))
          ∂MeasureTheory.volume := by
  let R : E → ℝ :=
    firstCoordinateSliceWeakDerivativeResidual (E := E) ψ U DU
  rcases
      scalarWeakSobolev_firstCoordinate_one_test_slice_residual_distribution_zero_on_unit_strip
        (E := E) (U := U) (DU := DU) ψ _hweak with
    ⟨hR_loc, hR_zero⟩
  have hR_ae : ∀ᵐ y ∂(MeasureTheory.volume : Measure E), R y = 0 := by
    exact
      ae_eq_zero_of_integral_contDiff_smul_eq_zero
        (E := E) (F := ℝ) (μ := (MeasureTheory.volume : Measure E))
        (f := R) hR_loc hR_zero
  filter_upwards [hR_ae] with y hy
  dsimp [R, firstCoordinateSliceWeakDerivativeResidual] at hy ⊢
  linarith

/--
%%handwave
name:
  Product weak derivatives give the sliced identity for one fixed test
statement:
  Fix one smooth compactly supported test in the vertical variable.  For a
  Sobolev function on the product strip, the one-dimensional
  integration-by-parts identity for that test holds on almost every vertical
  slice.
proof:
  Multiply the fixed vertical test by arbitrary smooth compactly supported
  tests in the transverse variable and insert the product into the product
  weak-derivative identity.  Fubini rewrites this as equality of transverse
  distributions, and equality of locally integrable distributions gives the
  asserted almost-everywhere equality of sliced integrals.
-/
theorem scalarWeakSobolev_firstCoordinate_one_test_slice_identity_ae_on_unit_strip
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)]
    [FiniteDimensional ℝ E]
    {U : ℝ × E → ℝ}
    {DU : ℝ × E → (ℝ × E) →L[ℝ] ℝ}
    (ψ : SmoothCompactlySupportedManifoldCoordinateFunction
        (Set.Ioo (0 : ℝ) 1))
    (_hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      {p : ℝ × E | 0 < p.1 ∧ p.1 < 1} U DU) :
    ∀ᵐ y ∂(MeasureTheory.volume : Measure E),
      Integrable
          (fun r : ℝ ↦
            (fderiv ℝ (ψ : ℝ → ℝ) r (1 : ℝ)) • U (r, y))
          (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)) ∧
        Integrable
          (fun r : ℝ ↦
            ψ r • DU (r, y) ((1 : ℝ), (0 : E)))
          (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)) ∧
          ∫ r in Set.Ioo (0 : ℝ) 1,
              (fderiv ℝ (ψ : ℝ → ℝ) r (1 : ℝ)) • U (r, y)
              ∂MeasureTheory.volume =
            -∫ r in Set.Ioo (0 : ℝ) 1,
              ψ r • DU (r, y) ((1 : ℝ), (0 : E))
              ∂MeasureTheory.volume := by
  have hloc :
      ∀ᵐ y ∂(MeasureTheory.volume : Measure E),
        ∀ K : Set ℝ, IsCompact K → K ⊆ Set.Ioo (0 : ℝ) 1 →
          IntegrableOn (fun r : ℝ ↦ U (r, y)) K
            (MeasureTheory.volume : Measure ℝ) ∧
          IntegrableOn
            (fun r : ℝ ↦ DU (r, y) ((1 : ℝ), (0 : E))) K
            (MeasureTheory.volume : Measure ℝ) :=
    scalarWeakSobolev_firstCoordinate_slice_local_integrability_ae_on_unit_strip
      (E := E) (U := U) (DU := DU) _hweak
  have heq :
      ∀ᵐ y ∂(MeasureTheory.volume : Measure E),
        ∫ r in Set.Ioo (0 : ℝ) 1,
            (fderiv ℝ (ψ : ℝ → ℝ) r (1 : ℝ)) • U (r, y)
            ∂MeasureTheory.volume =
          -∫ r in Set.Ioo (0 : ℝ) 1,
            ψ r • DU (r, y) ((1 : ℝ), (0 : E))
            ∂MeasureTheory.volume :=
    scalarWeakSobolev_firstCoordinate_one_test_slice_integral_eq_ae_on_unit_strip
      (E := E) (U := U) (DU := DU) ψ _hweak
  filter_upwards [hloc, heq] with y hy_loc hy_eq
  let K : Set ℝ := tsupport (ψ : ℝ → ℝ)
  have hU_K : IntegrableOn (fun r : ℝ ↦ U (r, y)) K
      (MeasureTheory.volume : Measure ℝ) :=
    (hy_loc K ψ.compact_support ψ.support_subset).1
  have hDU_K : IntegrableOn
      (fun r : ℝ ↦ DU (r, y) ((1 : ℝ), (0 : E))) K
      (MeasureTheory.volume : Measure ℝ) :=
    (hy_loc K ψ.compact_support ψ.support_subset).2
  have hderiv_cont :
      Continuous (fun r : ℝ ↦ fderiv ℝ (ψ : ℝ → ℝ) r (1 : ℝ)) :=
    (ψ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have hderiv_support :
      tsupport (fun r : ℝ ↦ fderiv ℝ (ψ : ℝ → ℝ) r (1 : ℝ)) ⊆ K :=
    tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := (ψ : ℝ → ℝ)) (1 : ℝ)
  refine ⟨?_, ?_, hy_eq⟩
  · exact
      integrable_restrict_smul_of_integrableOn_compact_tsupport_subset
        (Ω := Set.Ioo (0 : ℝ) 1) (K := K)
        (a := fun r : ℝ ↦ fderiv ℝ (ψ : ℝ → ℝ) r (1 : ℝ))
        (f := fun r : ℝ ↦ U (r, y))
        ψ.compact_support hU_K hderiv_cont
        (SmoothCompactlySupportedManifoldCoordinateFunction.exists_derivative_bound
          ψ (1 : ℝ))
        hderiv_support
  · exact
      integrable_restrict_smul_of_integrableOn_compact_tsupport_subset
        (Ω := Set.Ioo (0 : ℝ) 1) (K := K)
        (a := fun r : ℝ ↦ ψ r)
        (f := fun r : ℝ ↦ DU (r, y) ((1 : ℝ), (0 : E)))
        ψ.compact_support hDU_K ψ.smooth.continuous
        (SmoothCompactlySupportedManifoldCoordinateFunction.exists_bound ψ)
        (by intro r hr; exact hr)

/--
%%handwave
name:
  Product weak derivatives provide countable test data on almost every
  vertical line
statement:
  Let \(U\) be a scalar Sobolev function on the product strip
  \((0,1)\times E\), with weak derivative \(DU\), and fix a countable family
  of one-dimensional tests.  Then for almost every transverse coordinate
  \(y\), the sliced function and sliced first-coordinate weak derivative are
  locally integrable on compact subintervals and satisfy the
  integration-by-parts identity for every test in the countable family.
proof:
  For each test in the family, multiply it by arbitrary smooth compactly
  supported transverse tests and insert the product test into the weak
  derivative identity on the strip.  Fubini rewrites the product identity as
  equality of transverse distributions.  Since locally integrable functions
  whose pairings with all smooth compactly supported transverse tests agree
  are equal almost everywhere, the one-dimensional identity holds for almost
  every vertical line.  Countability intersects these full-measure sets, and
  the same cutoff/Fubini argument gives local integrability of the sliced
  functions on compact subintervals.
-/
theorem scalarWeakSobolev_firstCoordinate_slice_test_data_ae_on_unit_strip
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)]
    [FiniteDimensional ℝ E]
    {U : ℝ × E → ℝ}
    {DU : ℝ × E → (ℝ × E) →L[ℝ] ℝ}
    {T : Set
        (SmoothCompactlySupportedManifoldCoordinateFunction
          (Set.Ioo (0 : ℝ) 1))}
    (_hT_countable : T.Countable)
    (_hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      {p : ℝ × E | 0 < p.1 ∧ p.1 < 1} U DU) :
    ∀ᵐ y ∂(MeasureTheory.volume : Measure E),
      FirstCoordinateSliceWeakDerivativeTestData T U DU y := by
  have hloc :
      ∀ᵐ y ∂(MeasureTheory.volume : Measure E),
        ∀ K : Set ℝ, IsCompact K → K ⊆ Set.Ioo (0 : ℝ) 1 →
          IntegrableOn (fun r : ℝ ↦ U (r, y)) K
            (MeasureTheory.volume : Measure ℝ) ∧
          IntegrableOn
            (fun r : ℝ ↦ DU (r, y) ((1 : ℝ), (0 : E))) K
            (MeasureTheory.volume : Measure ℝ) :=
    scalarWeakSobolev_firstCoordinate_slice_local_integrability_ae_on_unit_strip
      (E := E) (U := U) (DU := DU) _hweak
  have htests :
      ∀ᵐ y ∂(MeasureTheory.volume : Measure E),
        ∀ ψ ∈ T,
          Integrable
              (fun r : ℝ ↦
                (fderiv ℝ (ψ : ℝ → ℝ) r (1 : ℝ)) • U (r, y))
              (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)) ∧
            Integrable
              (fun r : ℝ ↦
                ψ r • DU (r, y) ((1 : ℝ), (0 : E)))
              (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)) ∧
              ∫ r in Set.Ioo (0 : ℝ) 1,
                  (fderiv ℝ (ψ : ℝ → ℝ) r (1 : ℝ)) • U (r, y)
                  ∂MeasureTheory.volume =
                -∫ r in Set.Ioo (0 : ℝ) 1,
                  ψ r • DU (r, y) ((1 : ℝ), (0 : E))
                  ∂MeasureTheory.volume := by
    rw [ae_ball_iff _hT_countable]
    intro ψ _hψ
    exact
      scalarWeakSobolev_firstCoordinate_one_test_slice_identity_ae_on_unit_strip
        (E := E) (U := U) (DU := DU) ψ _hweak
  filter_upwards [hloc, htests] with y hy_loc hy_tests
  exact ⟨hy_loc, hy_tests⟩

/--
%%handwave
name:
  Countable \(C^1\)-dense tests suffice for vertical Sobolev slicing
statement:
  Let \(U\) be a scalar Sobolev function on the product strip
  \((0,1)\times E\), with weak derivative \(DU\).  If a countable
  \(C^1\)-dense family of one-dimensional compactly supported tests is fixed,
  then for almost every transverse coordinate \(y\), the vertical slice
  \(r\mapsto U(r,y)\) has weak derivative
  \(r\mapsto DU(r,y)[(1,0)]\) on \((0,1)\).
proof:
  For one fixed test from the countable family, insert product tests in the
  strip weak-derivative identity and apply Fubini to obtain the corresponding
  one-dimensional identity for almost every vertical line.  Countability
  gives one full-measure set on which all identities from the family hold.
  The compact-support control in the \(C^1\)-density statement and local
  integrability of the sliced Sobolev function and derivative allow passage to
  arbitrary smooth compactly supported tests by dominated convergence.
-/
theorem scalarWeakSobolev_firstCoordinate_fiberwise_realWeakDerivative_on_unit_strip_of_countable_c1_dense_tests
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)]
    [FiniteDimensional ℝ E]
    {U : ℝ × E → ℝ}
    {DU : ℝ × E → (ℝ × E) →L[ℝ] ℝ}
    {T : Set
        (SmoothCompactlySupportedManifoldCoordinateFunction
          (Set.Ioo (0 : ℝ) 1))}
    (_hT_countable : T.Countable)
    (_hT_dense :
      ∀ φ : SmoothCompactlySupportedManifoldCoordinateFunction
          (Set.Ioo (0 : ℝ) 1),
        ∃ K : Set ℝ,
          IsCompact K ∧
            K ⊆ Set.Ioo (0 : ℝ) 1 ∧
            tsupport (φ : ℝ → ℝ) ⊆ K ∧
            ∀ ε : ℝ, 0 < ε →
              ∃ ψ ∈ T,
                tsupport (ψ : ℝ → ℝ) ⊆ K ∧
                  (∀ x : ℝ, ‖(ψ : ℝ → ℝ) x - φ x‖ < ε) ∧
                    (∀ x : ℝ,
                      ‖fderiv ℝ (ψ : ℝ → ℝ) x (1 : ℝ) -
                        fderiv ℝ (φ : ℝ → ℝ) x (1 : ℝ)‖ < ε))
    (_hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      {p : ℝ × E | 0 < p.1 ∧ p.1 < 1} U DU) :
    ∀ᵐ y ∂(MeasureTheory.volume : Measure E),
      IsWeakDerivativeOnRealRegionScalar (Set.Ioo (0 : ℝ) 1)
        (fun r : ℝ => U (r, y))
        (fun r : ℝ => DU (r, y) ((1 : ℝ), (0 : E))) := by
  have hdata :
      ∀ᵐ y ∂(MeasureTheory.volume : Measure E),
        FirstCoordinateSliceWeakDerivativeTestData T U DU y :=
    scalarWeakSobolev_firstCoordinate_slice_test_data_ae_on_unit_strip
      (E := E) (U := U) (DU := DU) _hT_countable _hweak
  filter_upwards [hdata] with y hy
  exact
    realWeakDerivativeOn_Ioo_of_countable_c1_dense_test_data
      (E := E) (T := T) (U := U) (DU := DU) (y := y) _hT_dense hy

/--
%%handwave
name:
  Weak derivatives on the unit strip restrict to almost every vertical line
statement:
  Let \(U\) be a scalar Sobolev function on the product strip
  \((0,1)\times E\), with weak derivative \(DU\).  Then for almost every
  transverse coordinate \(y\), the one-dimensional function
  \(r\mapsto U(r,y)\) has weak derivative
  \(r\mapsto DU(r,y)[(1,0)]\) on \((0,1)\).
proof:
  Choose [a countable \(C^1\)-dense family of compactly supported one-dimensional tests](lean:JJMath.Uniformization.exists_countable_c1_dense_smooth_tests_Ioo),
  then apply [countable \(C^1\)-dense tests suffice for vertical Sobolev slicing](lean:JJMath.Uniformization.scalarWeakSobolev_firstCoordinate_fiberwise_realWeakDerivative_on_unit_strip_of_countable_c1_dense_tests).
-/
theorem scalarWeakSobolev_firstCoordinate_fiberwise_realWeakDerivative_on_unit_strip
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)]
    [FiniteDimensional ℝ E]
    {U : ℝ × E → ℝ}
    {DU : ℝ × E → (ℝ × E) →L[ℝ] ℝ}
    (_hweak : IsWeakDerivativeOnEuclideanRegionWithValues
      {p : ℝ × E | 0 < p.1 ∧ p.1 < 1} U DU) :
    ∀ᵐ y ∂(MeasureTheory.volume : Measure E),
      IsWeakDerivativeOnRealRegionScalar (Set.Ioo (0 : ℝ) 1)
        (fun r : ℝ => U (r, y))
        (fun r : ℝ => DU (r, y) ((1 : ℝ), (0 : E))) := by
  rcases exists_countable_c1_dense_smooth_tests_Ioo with
    ⟨T, hT_countable, hT_dense⟩
  exact
    scalarWeakSobolev_firstCoordinate_fiberwise_realWeakDerivative_on_unit_strip_of_countable_c1_dense_tests
      (E := E) (U := U) (DU := DU) hT_countable hT_dense _hweak

/--
%%handwave
name:
  One-dimensional weak derivatives are locally integrable
statement:
  On every compact subset of an open real region, the weak derivative in the
  one-dimensional integration-by-parts identity is integrable.
proof:
  Choose a smooth cutoff equal to one on the compact set and supported in the
  open region.  The weak-derivative identity gives integrability of the
  cutoff times the derivative, and the cutoff is identically one on the
  compact set.
-/
theorem realWeakSobolev_derivative_integrableOn_compact
    {Q Ω : Set ℝ} (hQ : IsCompact Q)
    (hQΩ : Q ⊆ Ω) (hΩ_open : IsOpen Ω)
    {u g : ℝ → ℝ}
    (hweak : IsWeakDerivativeOnRealRegionScalar Ω u g) :
    Integrable g (MeasureTheory.volume.restrict Q) := by
  obtain ⟨δ, hδ_pos, hδΩ⟩ :=
    hQ.exists_cthickening_subset_open hΩ_open hQΩ
  obtain ⟨ψ, hψ_smooth, _hψ_range, hψ_support, hψ_one⟩ :=
    exists_contMDiff_support_eq_eq_one_iff
      (I := 𝓘(ℝ, ℝ)) (n := ⊤)
      (Metric.isOpen_thickening) hQ.isClosed
      (Metric.self_subset_thickening hδ_pos Q)
  have hψ_tsupport_subset_cthickening :
      tsupport ψ ⊆ Metric.cthickening δ Q := by
    rw [tsupport, hψ_support]
    exact Metric.closure_thickening_subset_cthickening δ Q
  let φ : SmoothCompactlySupportedManifoldCoordinateFunction Ω :=
    { toFun := ψ
      smooth := hψ_smooth.contDiff
      support_subset := hψ_tsupport_subset_cthickening.trans hδΩ
      compact_support := by
        exact IsCompact.of_isClosed_subset (hQ.cthickening)
          (isClosed_tsupport ψ) hψ_tsupport_subset_cthickening }
  have hcutoff_int : Integrable (fun a ↦ φ a • g a)
      (MeasureTheory.volume.restrict Ω) :=
    (hweak φ).2.1
  have hcutoff_int_Q : Integrable (fun a ↦ φ a • g a)
      (MeasureTheory.volume.restrict Q) := by
    have hres := hcutoff_int.restrict (s := Q)
    simpa [Measure.restrict_restrict_of_subset hQΩ] using hres
  have hcutoff_eq :
      (fun a ↦ φ a • g a) =ᵐ[MeasureTheory.volume.restrict Q] g := by
    exact ae_restrict_of_forall_mem hQ.measurableSet fun a haQ ↦ by
      have hψ_eq_one : ψ a = 1 := (hψ_one a).1 haQ
      simp [φ, hψ_eq_one]
  exact hcutoff_int_Q.congr hcutoff_eq

/--
%%handwave
name:
  One-dimensional weak Sobolev functions are locally integrable
statement:
  On every compact subset of an open real region, the function appearing in a
  one-dimensional weak-derivative identity is integrable.
proof:
  Choose a smooth cutoff equal to one near the compact set and supported in
  the open region.  Multiplying the cutoff by the coordinate function gives a
  compactly supported test whose derivative is identically one on the compact
  set.  The weak-derivative identity gives integrability of that derivative
  times the function, hence integrability of the function on the compact set.
-/
theorem realWeakSobolev_function_integrableOn_compact
    {Q Ω : Set ℝ} (hQ : IsCompact Q)
    (hQΩ : Q ⊆ Ω) (hΩ_open : IsOpen Ω)
    {u g : ℝ → ℝ}
    (hweak : IsWeakDerivativeOnRealRegionScalar Ω u g) :
    Integrable u (MeasureTheory.volume.restrict Q) := by
  obtain ⟨δ, hδ_pos, hδΩ⟩ :=
    hQ.exists_cthickening_subset_open hΩ_open hQΩ
  let η : ℝ := δ / 2
  have hη_pos : 0 < η := by
    dsimp [η]
    linarith
  have hη_ltδ : η < δ := by
    dsimp [η]
    linarith
  have hclosed_eta : IsClosed (Metric.cthickening η Q) :=
    Metric.isClosed_cthickening
  have heta_subset_thickening :
      Metric.cthickening η Q ⊆ Metric.thickening δ Q :=
    Metric.cthickening_subset_thickening' hδ_pos hη_ltδ Q
  obtain ⟨χ, hχ_smooth, _hχ_range, hχ_support, hχ_one⟩ :=
    exists_contMDiff_support_eq_eq_one_iff
      (I := 𝓘(ℝ, ℝ)) (n := ⊤)
      (Metric.isOpen_thickening) hclosed_eta heta_subset_thickening
  have hχ_tsupport_subset_cthickening :
      tsupport χ ⊆ Metric.cthickening δ Q := by
    rw [tsupport, hχ_support]
    exact Metric.closure_thickening_subset_cthickening δ Q
  have hχ_deriv_zero :
      ∀ a ∈ Q, fderiv ℝ χ a = 0 := by
    intro a haQ
    have ha_thick : a ∈ Metric.thickening η Q :=
      Metric.self_subset_thickening hη_pos Q haQ
    have hnhds : Metric.thickening η Q ∈ 𝓝 a :=
      Metric.isOpen_thickening.mem_nhds ha_thick
    have hχ_eventually :
        χ =ᶠ[𝓝 a] fun _ : ℝ ↦ (1 : ℝ) := by
      filter_upwards [hnhds] with b hb
      exact (hχ_one b).1 ((Metric.thickening_subset_cthickening η Q) hb)
    rw [Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hχ_eventually]
    simp
  let φ : SmoothCompactlySupportedManifoldCoordinateFunction Ω :=
    { toFun := fun a : ℝ ↦ χ a * a
      smooth := by
        exact hχ_smooth.contDiff.mul contDiff_id
      support_subset := by
        exact (tsupport_mul_subset_left (f := χ) (g := fun a : ℝ ↦ a)).trans
          (hχ_tsupport_subset_cthickening.trans hδΩ)
      compact_support := by
        exact IsCompact.of_isClosed_subset (hQ.cthickening)
          (isClosed_tsupport _) ((tsupport_mul_subset_left
            (f := χ) (g := fun a : ℝ ↦ a)).trans hχ_tsupport_subset_cthickening) }
  have hφ_deriv_one :
      ∀ a ∈ Q, fderiv ℝ (φ : ℝ → ℝ) a (1 : ℝ) = 1 := by
    intro a haQ
    have hχa : χ a = 1 := by
      exact (hχ_one a).1 (Metric.self_subset_cthickening Q haQ)
    have hχdiff : DifferentiableAt ℝ χ a :=
      (hχ_smooth.contDiff.differentiable (by simp)) a
    have hiddiff : DifferentiableAt ℝ (fun b : ℝ ↦ b) a :=
      differentiableAt_id
    change fderiv ℝ (fun b : ℝ ↦ χ b * b) a (1 : ℝ) = 1
    rw [fderiv_fun_mul hχdiff hiddiff]
    simp [hχa, hχ_deriv_zero a haQ]
  have htest_int : Integrable (fun a ↦ (fderiv ℝ (φ : ℝ → ℝ) a (1 : ℝ)) • u a)
      (MeasureTheory.volume.restrict Ω) :=
    (hweak φ).1
  have htest_int_Q :
      Integrable (fun a ↦ (fderiv ℝ (φ : ℝ → ℝ) a (1 : ℝ)) • u a)
        (MeasureTheory.volume.restrict Q) := by
    have hres := htest_int.restrict (s := Q)
    simpa [Measure.restrict_restrict_of_subset hQΩ] using hres
  have htest_eq :
      (fun a ↦ (fderiv ℝ (φ : ℝ → ℝ) a (1 : ℝ)) • u a)
        =ᵐ[MeasureTheory.volume.restrict Q] u := by
    exact ae_restrict_of_forall_mem hQ.measurableSet fun a haQ ↦ by
      simp [hφ_deriv_one a haQ]
  exact htest_int_Q.congr htest_eq

/--
%%handwave
name:
  One-dimensional weak derivatives are locally integrable on the region
statement:
  In a one-dimensional weak-derivative identity on an open real region, the
  weak derivative is locally integrable on that region.
proof:
  Local integrability on an open set is equivalent to integrability on every
  compact subset of the set.  Apply the compact integrability statement.
-/
theorem realWeakSobolev_derivative_locallyIntegrableOn
    {Ω : Set ℝ} (hΩ_open : IsOpen Ω)
    {u g : ℝ → ℝ}
    (hweak : IsWeakDerivativeOnRealRegionScalar Ω u g) :
    LocallyIntegrableOn g Ω (MeasureTheory.volume : Measure ℝ) := by
  rw [locallyIntegrableOn_iff hΩ_open.isLocallyClosed]
  intro K hKΩ hK
  exact realWeakSobolev_derivative_integrableOn_compact hK hKΩ hΩ_open hweak

/--
%%handwave
name:
  One-dimensional weak Sobolev functions are locally integrable on the region
statement:
  In a one-dimensional weak-derivative identity on an open real region, the
  function itself is locally integrable on that region.
proof:
  Local integrability on an open set is equivalent to integrability on every
  compact subset of the set.  Apply the compact integrability statement.
-/
theorem realWeakSobolev_function_locallyIntegrableOn
    {Ω : Set ℝ} (hΩ_open : IsOpen Ω)
    {u g : ℝ → ℝ}
    (hweak : IsWeakDerivativeOnRealRegionScalar Ω u g) :
    LocallyIntegrableOn u Ω (MeasureTheory.volume : Measure ℝ) := by
  rw [locallyIntegrableOn_iff hΩ_open.isLocallyClosed]
  intro K hKΩ hK
  exact realWeakSobolev_function_integrableOn_compact hK hKΩ hΩ_open hweak

/--
%%handwave
name:
  Smooth compactly supported pairings determine locally integrable functions
  on open real regions
statement:
  A locally integrable function on an open subset of the real line is zero
  almost everywhere if its integral against every smooth compactly supported
  test function in the region is zero.
proof:
  This is the standard distributional uniqueness theorem for locally
  integrable functions, specialized to open subsets of the real line.
-/
theorem realLocallyIntegrableOn_ae_eq_zero_of_integral_contDiff_smul_eq_zero_on_open
    {Ω : Set ℝ} (hΩ_open : IsOpen Ω)
    {f : ℝ → ℝ}
    (hf : LocallyIntegrableOn f Ω (MeasureTheory.volume : Measure ℝ))
    (hzero :
      ∀ θ : ℝ → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ → tsupport θ ⊆ Ω →
        ∫ x, θ x • f x ∂(MeasureTheory.volume : Measure ℝ) = 0) :
    f =ᵐ[MeasureTheory.volume.restrict Ω] 0 := by
  have h_unrestricted :
      ∀ᵐ x ∂(MeasureTheory.volume : Measure ℝ), x ∈ Ω → f x = 0 :=
    hΩ_open.ae_eq_zero_of_integral_contDiff_smul_eq_zero hf hzero
  filter_upwards [ae_restrict_of_ae h_unrestricted,
    ae_restrict_mem hΩ_open.measurableSet] with x hx hxΩ
  exact hx hxΩ

/--
%%handwave
name:
  Weak derivatives are interval-integrable on compact intervals
statement:
  If \(u\) has weak derivative \(g\) on an open real region, then \(g\) is
  integrable on every compact interval contained in the region.
proof:
  The compact interval is a compact subset of the open region, so local
  integrability of the weak derivative gives integrability there.  The
  interval-integrability statement is the same assertion with endpoints
  ordered intrinsically.
-/
theorem realWeakSobolev_derivative_intervalIntegrable_on_uIcc
    {Ω : Set ℝ} (hΩ_open : IsOpen Ω)
    {u g : ℝ → ℝ}
    (hweak : IsWeakDerivativeOnRealRegionScalar Ω u g)
    {a b : ℝ} (habΩ : Set.uIcc a b ⊆ Ω) :
    IntervalIntegrable g MeasureTheory.volume a b := by
  have hg_integrable :
      Integrable g (MeasureTheory.volume.restrict (Set.uIcc a b)) :=
    realWeakSobolev_derivative_integrableOn_compact
      isCompact_uIcc habΩ hΩ_open hweak
  rw [intervalIntegrable_iff]
  exact hg_integrable.mono_measure
    (Measure.restrict_mono Set.uIoc_subset_uIcc le_rfl)

/--
%%handwave
name:
  Weak Sobolev functions are interval-integrable on compact intervals
statement:
  If \(u\) has a weak derivative on an open real region, then \(u\) is
  integrable on every compact interval contained in the region.
proof:
  The compact interval is a compact subset of the open region, so local
  integrability of the function gives integrability there.
-/
theorem realWeakSobolev_function_intervalIntegrable_on_uIcc
    {Ω : Set ℝ} (hΩ_open : IsOpen Ω)
    {u g : ℝ → ℝ}
    (hweak : IsWeakDerivativeOnRealRegionScalar Ω u g)
    {a b : ℝ} (habΩ : Set.uIcc a b ⊆ Ω) :
    IntervalIntegrable u MeasureTheory.volume a b := by
  have hu_integrable :
      Integrable u (MeasureTheory.volume.restrict (Set.uIcc a b)) :=
    realWeakSobolev_function_integrableOn_compact
      isCompact_uIcc habΩ hΩ_open hweak
  rw [intervalIntegrable_iff]
  exact hu_integrable.mono_measure
    (Measure.restrict_mono Set.uIoc_subset_uIcc le_rfl)

/--
%%handwave
name:
  Primitives of interval-integrable functions are absolutely continuous
statement:
  If \(g\) is integrable on an interval \([a,b]\), then
  \(x\mapsto \int_a^x g(t)\,dt\) is absolutely continuous on that interval.
proof:
  This is the standard absolute continuity theorem for indefinite Lebesgue
  integrals on compact intervals.
-/
theorem realPrimitive_absolutelyContinuousOnInterval_of_intervalIntegrable
    {g : ℝ → ℝ} {a b : ℝ}
    (hg : IntervalIntegrable g MeasureTheory.volume a b) :
    AbsolutelyContinuousOnInterval (fun x : ℝ ↦ ∫ t in a..x, g t) a b := by
  exact hg.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by simp)

/--
%%handwave
name:
  Primitives have the integrand as derivative almost everywhere
statement:
  If \(g\) is integrable on an interval \([a,b]\), then the primitive
  \(x\mapsto\int_a^x g(t)\,dt\) has classical derivative \(g(x)\) for almost
  every \(x\in[a,b]\).
proof:
  This is the interval form of the Lebesgue differentiation theorem applied
  to the indefinite integral.
-/
theorem realPrimitive_hasDerivAt_ae_of_intervalIntegrable
    {g : ℝ → ℝ} {a b : ℝ}
    (hg : IntervalIntegrable g MeasureTheory.volume a b) :
    ∀ᵐ x ∂(MeasureTheory.volume : Measure ℝ),
      x ∈ Set.uIcc a b →
        HasDerivAt (fun y : ℝ ↦ ∫ t in a..y, g t) (g x) x := by
  filter_upwards [hg.ae_hasDerivAt_integral] with x hx hxmem
  exact hx hxmem a (by simp)

/--
%%handwave
name:
  Adding a constant to a primitive preserves the interval ACL structure
statement:
  If \(g\) is integrable on \([a,b]\), then
  \(x\mapsto C+\int_a^x g(t)\,dt\) is absolutely continuous on \([a,b]\) and
  has derivative \(g\) almost everywhere there.
proof:
  Add a constant to the primitive.  Absolute continuity and the derivative
  statement are unchanged by adding a constant.
-/
theorem realPrimitive_add_const_acl_on_interval
    {g : ℝ → ℝ} {a b C : ℝ}
    (hg : IntervalIntegrable g MeasureTheory.volume a b) :
    AbsolutelyContinuousOnInterval
        (fun x : ℝ ↦ C + ∫ t in a..x, g t) a b ∧
      ∀ᵐ x ∂(MeasureTheory.volume : Measure ℝ),
        x ∈ Set.uIcc a b →
          HasDerivAt (fun y : ℝ ↦ C + ∫ t in a..y, g t) (g x) x := by
  constructor
  · have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ C) a b := by
      simpa [AbsolutelyContinuousOnInterval] using
        (tendsto_const_nhds :
          Filter.Tendsto
            (fun _ : ℕ × (ℕ → ℝ × ℝ) ↦ (0 : ℝ))
            (AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
              Filter.principal (AbsolutelyContinuousOnInterval.disjWithin a b))
            (𝓝 (0 : ℝ)))
    simpa [Pi.add_apply] using
      hconst.add (realPrimitive_absolutelyContinuousOnInterval_of_intervalIntegrable hg)
  · filter_upwards [realPrimitive_hasDerivAt_ae_of_intervalIntegrable hg]
      with x hx hxmem
    exact (hx hxmem).const_add C

/--
%%handwave
name:
  Absolute continuity is unchanged by modifying values outside the interval
statement:
  If two real functions agree on a compact interval and one of them is
  absolutely continuous on that interval, then the other one is absolutely
  continuous there as well.
proof:
  Use the \(\varepsilon\)-\(\delta\) definition of absolute continuity.  All
  endpoint values used in the definition lie in the interval, where the two
  functions agree.
-/
theorem absolutelyContinuousOnInterval_congr_on_uIcc
    {f h : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hfh : Set.EqOn f h (Set.uIcc a b)) :
    AbsolutelyContinuousOnInterval h a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  rcases hf ε hε with ⟨δ, hδ_pos, hδ⟩
  refine ⟨δ, hδ_pos, ?_⟩
  intro E hE hlen
  have hsum :
      (∑ i ∈ Finset.range E.1,
          dist (h (E.2 i).1) (h (E.2 i).2)) =
        ∑ i ∈ Finset.range E.1,
          dist (f (E.2 i).1) (f (E.2 i).2) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hi_mem := hE.1 i hi
    rw [← hfh hi_mem.1, ← hfh hi_mem.2]
  rw [hsum]
  exact hδ E hE hlen

/--
%%handwave
name:
  Smooth primitives have the expected classical derivative
statement:
  If \(\phi\) is a smooth real function, then the primitive
  \(x\mapsto\int_a^x\phi(t)\,dt\) has derivative \(\phi(x)\) at every point.
proof:
  This is the fundamental theorem of calculus for continuous integrands,
  applied to the continuous function \(\phi\).
-/
theorem realPrimitive_hasDerivAt_of_contDiff
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (a x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ ∫ t in a..y, φ t) (φ x) x := by
  exact (hφ.continuous.integral_hasStrictDerivAt a x).hasDerivAt

/--
%%handwave
name:
  The derivative of a smooth primitive is the integrand
statement:
  If \(\phi\) is smooth, then
  \[
    \frac{d}{dx}\int_a^x \phi(t)\,dt=\phi(x)
  \]
  for every \(x\).
proof:
  This is the pointwise derivative form of the fundamental theorem of
  calculus for continuous integrands.
-/
theorem realPrimitive_deriv_eq_of_contDiff
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (a : ℝ) :
    deriv (fun x : ℝ ↦ ∫ t in a..x, φ t) = φ := by
  funext x
  exact (realPrimitive_hasDerivAt_of_contDiff hφ a x).deriv

/--
%%handwave
name:
  The Fréchet derivative of a smooth real primitive in the unit direction is
  the integrand
statement:
  If \(\phi\) is smooth, then
  \[
    D\left(x\mapsto\int_a^x \phi(t)\,dt\right)_x(1)=\phi(x).
  \]
proof:
  In one real variable, applying the Fréchet derivative to \(1\) is the
  ordinary derivative.  The ordinary derivative of the primitive is the
  integrand by the fundamental theorem of calculus.
-/
theorem realPrimitive_fderiv_apply_one_eq_of_contDiff
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (a x : ℝ) :
    fderiv ℝ (fun y : ℝ ↦ ∫ t in a..y, φ t) x (1 : ℝ) = φ x := by
  rw [fderiv_apply_one_eq_deriv]
  exact congr_fun (realPrimitive_deriv_eq_of_contDiff hφ a) x

/--
%%handwave
name:
  A primitive of an interior-supported function vanishes to the left of the
  interval
statement:
  If the closed support of \(\phi\) is contained in \((a,b)\), then
  \[
    \int_a^x \phi(t)\,dt=0
  \]
  for every \(x\le a\).
proof:
  On the interval between \(x\) and \(a\), the integrand is identically zero,
  because that interval lies outside the closed support of \(\phi\).
-/
theorem realPrimitive_eq_zero_of_le_left_of_tsupport_subset_Ioo
    {φ : ℝ → ℝ} {a b x : ℝ}
    (hφI : tsupport φ ⊆ Set.Ioo a b) (hx : x ≤ a) :
    ∫ t in a..x, φ t = 0 := by
  have hzero : ∫ t in x..a, φ t = 0 := by
    have hcongr :
        ∫ t in x..a, φ t = ∫ t in x..a, (0 : ℝ) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with t ht
      have htI : t ∈ Set.Ioc x a := by
        simpa [Set.uIoc_of_le hx] using ht
      have ht_not : t ∉ tsupport φ := by
        intro htφ
        have htIoo : t ∈ Set.Ioo a b := hφI htφ
        exact (not_lt_of_ge htI.2) htIoo.1
      exact image_eq_zero_of_notMem_tsupport ht_not
    simpa using hcongr
  rw [intervalIntegral.integral_symm x a, hzero, neg_zero]

/--
%%handwave
name:
  An interior-supported function integrates to zero on intervals to the right
statement:
  If the closed support of \(\phi\) is contained in \((a,b)\), then
  \[
    \int_b^x \phi(t)\,dt=0
  \]
  for every \(x\ge b\).
proof:
  On the interval between \(b\) and \(x\), the integrand is identically zero,
  because that interval lies outside the closed support of \(\phi\).
-/
theorem intervalIntegral_eq_zero_of_right_le_of_tsupport_subset_Ioo
    {φ : ℝ → ℝ} {a b x : ℝ}
    (hφI : tsupport φ ⊆ Set.Ioo a b) (hx : b ≤ x) :
    ∫ t in b..x, φ t = 0 := by
  have hcongr :
      ∫ t in b..x, φ t = ∫ t in b..x, (0 : ℝ) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with t ht
    have htI : t ∈ Set.Ioc b x := by
      simpa [Set.uIoc_of_le hx] using ht
    have ht_not : t ∉ tsupport φ := by
      intro htφ
      have htIoo : t ∈ Set.Ioo a b := hφI htφ
      exact (not_lt_of_ge htIoo.2.le) htI.1
    exact image_eq_zero_of_notMem_tsupport ht_not
  simpa using hcongr

/--
%%handwave
name:
  A primitive of an interior-supported function is constant to the right of
  the interval
statement:
  If the closed support of \(\phi\) is contained in \((a,b)\), then for
  every \(x\ge b\),
  \[
    \int_a^x \phi(t)\,dt=\int_a^b \phi(t)\,dt .
  \]
proof:
  Split the integral over \([a,x]\) into the adjacent intervals \([a,b]\) and
  \([b,x]\).  The second integral is zero because the integrand vanishes to
  the right of \(b\).
-/
theorem realPrimitive_eq_intervalIntegral_of_right_le_of_tsupport_subset_Ioo
    {φ : ℝ → ℝ} {a b x : ℝ}
    (hφI : tsupport φ ⊆ Set.Ioo a b)
    (hab_int : IntervalIntegrable φ MeasureTheory.volume a b)
    (hbx_int : IntervalIntegrable φ MeasureTheory.volume b x)
    (hx : b ≤ x) :
    ∫ t in a..x, φ t = ∫ t in a..b, φ t := by
  have hzero :
      ∫ t in b..x, φ t = 0 :=
    intervalIntegral_eq_zero_of_right_le_of_tsupport_subset_Ioo hφI hx
  have hadd :=
    intervalIntegral.integral_add_adjacent_intervals hab_int hbx_int
  simpa [hzero] using hadd.symm

/--
%%handwave
name:
  A zero-mean primitive of an interior-supported function has compact support
statement:
  Let \(a\le b\).  If the closed support of \(\phi\) is contained in
  \((a,b)\), and \(\int_a^b\phi=0\), then
  \(x\mapsto\int_a^x\phi(t)\,dt\) has compact support.
proof:
  The primitive vanishes on the left of \(a\).  On the right of \(b\), it is
  equal to the total integral over \([a,b]\), which is zero by assumption.
  Hence its support is contained in the compact interval \([a,b]\).
-/
theorem realPrimitive_hasCompactSupport_of_tsupport_subset_Ioo_of_intervalIntegral_eq_zero
    {φ : ℝ → ℝ} {a b : ℝ} (_hab : a ≤ b)
    (hφI : tsupport φ ⊆ Set.Ioo a b)
    (hφint : ∀ c d : ℝ, IntervalIntegrable φ MeasureTheory.volume c d)
    (hmean : ∫ t in a..b, φ t = 0) :
    HasCompactSupport (fun x : ℝ ↦ ∫ t in a..x, φ t) := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro x hx
  by_cases hax : a ≤ x
  · by_cases hxb : x ≤ b
    · exact ⟨hax, hxb⟩
    · have hbx : b ≤ x := le_of_lt (lt_of_not_ge hxb)
      have hzero :
          ∫ t in a..x, φ t = 0 := by
        calc
          ∫ t in a..x, φ t
              = ∫ t in a..b, φ t :=
                  realPrimitive_eq_intervalIntegral_of_right_le_of_tsupport_subset_Ioo
                    hφI (hφint a b) (hφint b x) hbx
          _ = 0 := hmean
      exact (hx hzero).elim
  · have hxa : x ≤ a := le_of_not_ge hax
    have hzero :
        ∫ t in a..x, φ t = 0 :=
      realPrimitive_eq_zero_of_le_left_of_tsupport_subset_Ioo hφI hxa
    exact (hx hzero).elim

/--
%%handwave
name:
  Compact subsets of an open interval have a smaller open interval
statement:
  If \(K\) is compact and \(K\subset(a,b)\), with \(a<b\), then there are
  \(c,d\) such that
  \[
    a<c\le d<b,\qquad K\subset(c,d).
  \]
proof:
  Compactness gives a positive closed thickening of \(K\) still contained in
  \((a,b)\).  Moving each point of \(K\) by half this margin to the left and
  right remains in \((a,b)\), giving uniform lower and upper margins.
-/
theorem isCompact_subset_Ioo_exists_Ioo_subset
    {K : Set ℝ} (hK : IsCompact K) {a b : ℝ}
    (hab : a < b) (hKI : K ⊆ Set.Ioo a b) :
    ∃ c d : ℝ, a < c ∧ c ≤ d ∧ d < b ∧ K ⊆ Set.Ioo c d := by
  by_cases hne : K.Nonempty
  · obtain ⟨δ, hδ_pos, hδI⟩ :=
      hK.exists_cthickening_subset_open isOpen_Ioo hKI
    let η : ℝ := δ / 2
    have hη_pos : 0 < η := by
      dsimp [η]
      linarith
    have hη_nonneg : 0 ≤ η := hη_pos.le
    have hη_leδ : η ≤ δ := by
      dsimp [η]
      linarith
    have hleft_margin : ∀ y ∈ K, a + η < y := by
      intro y hy
      have hdist : dist (y - η) y ≤ δ := by
        have hdist_eq : dist (y - η) y = η := by
          rw [Real.dist_eq]
          have hsub : y - η - y = -η := by ring
          rw [hsub, abs_neg, abs_of_nonneg hη_nonneg]
        rw [hdist_eq]
        exact hη_leδ
      have hy_thick :
          y - η ∈ Metric.cthickening δ K :=
        Metric.mem_cthickening_of_dist_le (y - η) y δ K hy hdist
      have hyI : y - η ∈ Set.Ioo a b := hδI hy_thick
      have hya : a < y - η := hyI.1
      linarith
    have hright_margin : ∀ y ∈ K, y < b - η := by
      intro y hy
      have hdist : dist (y + η) y ≤ δ := by
        have hdist_eq : dist (y + η) y = η := by
          rw [Real.dist_eq]
          have hsub : y + η - y = η := by ring
          rw [hsub, abs_of_nonneg hη_nonneg]
        rw [hdist_eq]
        exact hη_leδ
      have hy_thick :
          y + η ∈ Metric.cthickening δ K :=
        Metric.mem_cthickening_of_dist_le (y + η) y δ K hy hdist
      have hyI : y + η ∈ Set.Ioo a b := hδI hy_thick
      have hyb : y + η < b := hyI.2
      linarith
    refine ⟨a + η, b - η, ?_, ?_, ?_, ?_⟩
    · linarith
    · rcases hne with ⟨y, hy⟩
      have hy_left := hleft_margin y hy
      have hy_right := hright_margin y hy
      linarith
    · linarith
    · intro y hy
      exact ⟨hleft_margin y hy, hright_margin y hy⟩
  · let m : ℝ := (a + b) / 2
    refine ⟨m, m, ?_, le_rfl, ?_, ?_⟩
    · dsimp [m]
      linarith
    · dsimp [m]
      linarith
    · intro y hy
      exact (hne ⟨y, hy⟩).elim

/--
%%handwave
name:
  A primitive vanishes to the left of a smaller support interval
statement:
  If the closed support of \(\phi\) is contained in \((c,d)\), and both
  \(a\) and \(x\) lie to the left of \(c\), then
  \[
    \int_a^x \phi(t)\,dt=0 .
  \]
proof:
  The unordered interval between \(a\) and \(x\) lies to the left of \(c\),
  while the integrand is supported strictly to the right of \(c\).
-/
theorem realPrimitive_eq_zero_of_le_support_left_of_tsupport_subset_Ioo
    {φ : ℝ → ℝ} {a c d x : ℝ}
    (ha : a ≤ c) (hx : x ≤ c)
    (hφI : tsupport φ ⊆ Set.Ioo c d) :
    ∫ t in a..x, φ t = 0 := by
  have hcongr :
      ∫ t in a..x, φ t = ∫ t in a..x, (0 : ℝ) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with t ht
    have ht_le_c : t ≤ c := by
      rw [Set.mem_uIoc] at ht
      rcases ht with ht | ht
      · exact ht.2.trans hx
      · exact ht.2.trans ha
    have ht_not : t ∉ tsupport φ := by
      intro htφ
      have htIoo : t ∈ Set.Ioo c d := hφI htφ
      exact (not_lt_of_ge ht_le_c) htIoo.1
    exact image_eq_zero_of_notMem_tsupport ht_not
  simpa using hcongr

/--
%%handwave
name:
  A zero-mean primitive vanishes to the right of a smaller support interval
statement:
  Suppose the closed support of \(\phi\) is contained in \((c,d)\), with
  \(d\le b\), and \(\int_a^b\phi=0\).  Then the primitive
  \(x\mapsto\int_a^x\phi\) vanishes for every \(x\ge d\).
proof:
  The integral from \(d\) to any \(x\ge d\) is zero because the integrand
  vanishes to the right of \(d\).  Also the integral from \(d\) to \(b\) is
  zero, so the zero total integral over \([a,b]\) forces the integral over
  \([a,d]\) to be zero.
-/
theorem realPrimitive_eq_zero_of_support_right_le_of_tsupport_subset_Ioo
    {φ : ℝ → ℝ} {a b c d x : ℝ}
    (hdb : d ≤ b) (hx : d ≤ x)
    (hφI : tsupport φ ⊆ Set.Ioo c d)
    (hφint : ∀ p q : ℝ, IntervalIntegrable φ MeasureTheory.volume p q)
    (hmean : ∫ t in a..b, φ t = 0) :
    ∫ t in a..x, φ t = 0 := by
  have hzero_dx :
      ∫ t in d..x, φ t = 0 :=
    intervalIntegral_eq_zero_of_right_le_of_tsupport_subset_Ioo hφI hx
  have hzero_db :
      ∫ t in d..b, φ t = 0 :=
    intervalIntegral_eq_zero_of_right_le_of_tsupport_subset_Ioo hφI hdb
  have had_eq :
      ∫ t in a..d, φ t = 0 := by
    have hadd :=
      intervalIntegral.integral_add_adjacent_intervals (hφint a d) (hφint d b)
    have hEq : ∫ t in a..d, φ t = ∫ t in a..b, φ t := by
      simpa [hzero_db] using hadd
    exact hEq.trans hmean
  have hadd :=
    intervalIntegral.integral_add_adjacent_intervals (hφint a d) (hφint d x)
  simpa [hzero_dx, had_eq] using hadd.symm

/--
%%handwave
name:
  A zero-mean primitive has closed support in the original interval interior
statement:
  Let \(a<b\).  If \(\phi\) is supported in \((a,b)\), is integrable on
  compact intervals, and \(\int_a^b\phi=0\), then the closed support of
  \(x\mapsto\int_a^x\phi(t)\,dt\) is contained in \((a,b)\).
proof:
  Compactness of the support of \(\phi\) gives a smaller interval
  \((c,d)\) with \(a<c\le d<b\) containing that support.  The primitive
  vanishes to the left of \(c\) and to the right of \(d\), hence its ordinary
  support is contained in \([c,d]\).  Taking closure keeps the closed support
  in \([c,d]\subset(a,b)\).
-/
theorem realPrimitive_tsupport_subset_interior_uIcc_of_tsupport_subset_Ioo
    {φ : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hφc : HasCompactSupport φ)
    (hφI : tsupport φ ⊆ Set.Ioo a b)
    (hφint : ∀ p q : ℝ, IntervalIntegrable φ MeasureTheory.volume p q)
    (hmean : ∫ t in a..b, φ t = 0) :
    tsupport (fun x : ℝ ↦ ∫ t in a..x, φ t) ⊆
      interior (Set.uIcc a b) := by
  rcases isCompact_subset_Ioo_exists_Ioo_subset hφc hab hφI with
    ⟨c, d, hac, hcd, hdb, hφ_cd⟩
  have hsupp :
      Function.support (fun x : ℝ ↦ ∫ t in a..x, φ t) ⊆ Set.Icc c d := by
    intro x hx
    by_cases hcx : c ≤ x
    · by_cases hxd : x ≤ d
      · exact ⟨hcx, hxd⟩
      · have hdx : d ≤ x := le_of_lt (lt_of_not_ge hxd)
        have hzero :
            ∫ t in a..x, φ t = 0 :=
          realPrimitive_eq_zero_of_support_right_le_of_tsupport_subset_Ioo
            hdb.le hdx hφ_cd hφint hmean
        exact (hx hzero).elim
    · have hxc : x ≤ c := le_of_not_ge hcx
      have hzero :
          ∫ t in a..x, φ t = 0 :=
        realPrimitive_eq_zero_of_le_support_left_of_tsupport_subset_Ioo
          hac.le hxc hφ_cd
      exact (hx hzero).elim
  have htsupp :
      tsupport (fun x : ℝ ↦ ∫ t in a..x, φ t) ⊆ Set.Icc c d :=
    closure_minimal hsupp isClosed_Icc
  have hIcc_interior : Set.Icc c d ⊆ interior (Set.uIcc a b) := by
    intro y hy
    rw [Set.uIcc_of_le hab.le, interior_Icc]
    exact ⟨lt_of_lt_of_le hac hy.1, lt_of_le_of_lt hy.2 hdb⟩
  exact htsupp.trans hIcc_interior

/--
%%handwave
name:
  Smooth primitives are smooth
statement:
  If \(\phi\) is smooth, then the primitive
  \(x\mapsto\int_a^x\phi(t)\,dt\) is smooth.
proof:
  The primitive is differentiable everywhere, and its derivative is the
  smooth function \(\phi\).  The usual recursive characterization of smooth
  real functions gives smoothness of the primitive.
-/
theorem realPrimitive_contDiff_of_contDiff
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (a : ℝ) :
    ContDiff ℝ ∞ (fun x : ℝ ↦ ∫ t in a..x, φ t) := by
  rw [contDiff_infty_iff_deriv]
  constructor
  · intro x
    exact (realPrimitive_hasDerivAt_of_contDiff hφ a x).differentiableAt
  · simpa [realPrimitive_deriv_eq_of_contDiff hφ a] using hφ

/--
%%handwave
name:
  Smooth real functions are absolutely continuous on compact intervals
statement:
  A smooth real-valued function is absolutely continuous on every compact
  interval.
proof:
  Its derivative is continuous, hence bounded on the compact interval.  The
  mean-value estimate gives a Lipschitz bound on the interval, and every
  Lipschitz function on an interval is absolutely continuous.
-/
theorem contDiff_absolutelyContinuousOnInterval
    {θ : ℝ → ℝ} {a b : ℝ}
    (hθ : ContDiff ℝ ∞ θ) :
    AbsolutelyContinuousOnInterval θ a b := by
  have hdiff : ∀ x ∈ Set.uIcc a b, DifferentiableAt ℝ θ x := by
    intro x _hx
    exact (hθ.differentiable (by simp)) x
  have hderiv_cont : Continuous fun x : ℝ ↦ ‖deriv θ x‖₊ := by
    exact (hθ.continuous_deriv (by simp)).nnnorm
  have hcompact :
      IsCompact ((fun x : ℝ ↦ ‖deriv θ x‖₊) '' Set.uIcc a b) :=
    isCompact_uIcc.image hderiv_cont
  rcases hcompact.bddAbove with ⟨C, hC⟩
  have hbound : ∀ x ∈ Set.uIcc a b, ‖deriv θ x‖₊ ≤ C := by
    intro x hx
    exact hC ⟨x, hx, rfl⟩
  exact
    ((convex_uIcc a b).lipschitzOnWith_of_nnnorm_deriv_le
      (𝕜 := ℝ) (f := θ) hdiff hbound).absolutelyContinuousOnInterval

/--
%%handwave
name:
  Tests supported in the interior of an interval vanish at the endpoints
statement:
  If the closed support of a function is contained in the interior of the
  unordered interval between \(a\) and \(b\), then the function vanishes at
  both endpoints.
proof:
  Neither endpoint belongs to the interior of the interval.  Since the
  function vanishes off its closed support, it vanishes at the endpoints.
-/
theorem eq_zero_at_endpoints_of_tsupport_subset_interior_uIcc
    {θ : ℝ → ℝ} {a b : ℝ}
    (hθI : tsupport θ ⊆ interior (Set.uIcc a b)) :
    θ a = 0 ∧ θ b = 0 := by
  have ha_not_interior : a ∉ interior (Set.uIcc a b) := by
    intro ha
    rcases le_total a b with hab | hba
    · have haIoo : a ∈ Set.Ioo a b := by
        rw [Set.uIcc_of_le hab, interior_Icc] at ha
        exact ha
      exact (lt_irrefl a) haIoo.1
    · have haIoo : a ∈ Set.Ioo b a := by
        rw [Set.uIcc_of_ge hba, interior_Icc] at ha
        exact ha
      exact (lt_irrefl a) haIoo.2
  have hb_not_interior : b ∉ interior (Set.uIcc a b) := by
    intro hb
    rcases le_total a b with hab | hba
    · have hbIoo : b ∈ Set.Ioo a b := by
        rw [Set.uIcc_of_le hab, interior_Icc] at hb
        exact hb
      exact (lt_irrefl b) hbIoo.2
    · have hbIoo : b ∈ Set.Ioo b a := by
        rw [Set.uIcc_of_ge hba, interior_Icc] at hb
        exact hb
      exact (lt_irrefl b) hbIoo.1
  constructor
  · exact image_eq_zero_of_notMem_tsupport (fun ha ↦ ha_not_interior (hθI ha))
  · exact image_eq_zero_of_notMem_tsupport (fun hb ↦ hb_not_interior (hθI hb))

/--
%%handwave
name:
  The derivative of an interior-supported test is supported in the open
  interval
statement:
  If \(a\le b\) and the closed support of a test function is contained in the
  interior of \([a,b]\), then the support of its derivative, multiplied by
  any auxiliary function, is contained in \((a,b]\).
proof:
  The support of the derivative is contained in the closed support of the
  test function, and the interior of \([a,b]\) is \((a,b)\), which is
  contained in \((a,b]\).
-/
theorem support_fderiv_test_smul_subset_Ioc_of_le
    {θ F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hθI : tsupport θ ⊆ interior (Set.uIcc a b)) :
    Function.support
        (fun x : ℝ ↦ (fderiv ℝ θ x (1 : ℝ)) • F x) ⊆
      Set.Ioc a b := by
  intro x hx
  have hx_deriv_support :
      x ∈ Function.support (fun y : ℝ ↦ fderiv ℝ θ y (1 : ℝ)) :=
    Function.support_smul_subset_left
      (fun y : ℝ ↦ fderiv ℝ θ y (1 : ℝ)) F hx
  have hx_deriv_tsupport :
      x ∈ tsupport (fun y : ℝ ↦ fderiv ℝ θ y (1 : ℝ)) :=
    subset_tsupport _ hx_deriv_support
  have hxθ : x ∈ tsupport θ :=
    tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := θ) (1 : ℝ)
      hx_deriv_tsupport
  have hxI : x ∈ interior (Set.uIcc a b) := hθI hxθ
  have hxIoo : x ∈ Set.Ioo a b := by
    rw [Set.uIcc_of_le hab, interior_Icc] at hxI
    exact hxI
  exact Set.Ioo_subset_Ioc_self hxIoo

/--
%%handwave
name:
  An interior-supported test is supported in the open interval
statement:
  If \(a\le b\) and the closed support of a test function is contained in the
  interior of \([a,b]\), then the support of the test, multiplied by any
  auxiliary function, is contained in \((a,b]\).
proof:
  The ordinary support is contained in the closed support, which lies in
  \((a,b)\subset (a,b]\).
-/
theorem support_test_smul_subset_Ioc_of_le
    {θ F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hθI : tsupport θ ⊆ interior (Set.uIcc a b)) :
    Function.support (fun x : ℝ ↦ θ x • F x) ⊆ Set.Ioc a b := by
  intro x hx
  have hxθ_support : x ∈ Function.support θ :=
    Function.support_smul_subset_left θ F hx
  have hxθ : x ∈ tsupport θ := subset_tsupport _ hxθ_support
  have hxI : x ∈ interior (Set.uIcc a b) := hθI hxθ
  have hxIoo : x ∈ Set.Ioo a b := by
    rw [Set.uIcc_of_le hab, interior_Icc] at hxI
    exact hxI
  exact Set.Ioo_subset_Ioc_self hxIoo

/--
%%handwave
name:
  Interval integrals of supported test derivatives are whole-line integrals
statement:
  If \(a\le b\) and the closed support of a test function lies in the
  interior of \([a,b]\), then integrating its derivative times any auxiliary
  function over \(a..b\) is the same as integrating over the whole real line.
proof:
  The previous support statement places the integrand inside \((a,b]\), so
  the standard interval-integral support theorem applies.
-/
theorem intervalIntegral_fderiv_test_smul_eq_integral_of_le
    {θ F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hθI : tsupport θ ⊆ interior (Set.uIcc a b)) :
    ∫ x in a..b, (fderiv ℝ θ x (1 : ℝ)) • F x =
      ∫ x, (fderiv ℝ θ x (1 : ℝ)) • F x
        ∂(MeasureTheory.volume : Measure ℝ) := by
  exact intervalIntegral.integral_eq_integral_of_support_subset
    (μ := MeasureTheory.volume)
    (f := fun x : ℝ ↦ (fderiv ℝ θ x (1 : ℝ)) • F x)
    (support_fderiv_test_smul_subset_Ioc_of_le hab hθI)

/--
%%handwave
name:
  Interval integrals of supported tests are whole-line integrals
statement:
  If \(a\le b\) and the closed support of a test function lies in the
  interior of \([a,b]\), then integrating the test times any auxiliary
  function over \(a..b\) is the same as integrating over the whole real line.
proof:
  The integrand is supported in \((a,b]\), so the standard interval-integral
  support theorem applies.
-/
theorem intervalIntegral_test_smul_eq_integral_of_le
    {θ F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hθI : tsupport θ ⊆ interior (Set.uIcc a b)) :
    ∫ x in a..b, θ x • F x =
      ∫ x, θ x • F x ∂(MeasureTheory.volume : Measure ℝ) := by
  exact intervalIntegral.integral_eq_integral_of_support_subset
    (μ := MeasureTheory.volume)
    (f := fun x : ℝ ↦ θ x • F x)
    (support_test_smul_subset_Ioc_of_le hab hθI)

/--
%%handwave
name:
  Smooth tests integrate by parts against primitives on an ordered interval
statement:
  Let \(l\le r\), let \(c\in[l,r]\), and let \(g\) be integrable on
  \([l,r]\).  If a smooth test \(\theta\) has closed support in the interior
  of \([l,r]\), then
  \[
    \int \theta'(x)\Bigl(\int_c^x g(t)\,dt\Bigr)\,dx
      = -\int \theta(x)g(x)\,dx ,
  \]
  and the left-hand integrand is integrable.
proof:
  The primitive is absolutely continuous with derivative \(g\) almost
  everywhere, while the smooth test is absolutely continuous and vanishes at
  the interval endpoints.  Apply integration by parts on \([l,r]\), replace
  the primitive derivative by \(g\) almost everywhere, and use the support
  condition to identify the interval integrals with whole-line integrals.
-/
theorem realPrimitive_integral_fderiv_test_eq_neg_integral_test_of_le
    {g θ : ℝ → ℝ} {l r c : ℝ}
    (hlr : l ≤ r)
    (hg : IntervalIntegrable g MeasureTheory.volume l r)
    (hc : c ∈ Set.uIcc l r)
    (hθ : ContDiff ℝ ∞ θ)
    (hθI : tsupport θ ⊆ interior (Set.uIcc l r)) :
    Integrable
        (fun x : ℝ ↦
          (fderiv ℝ θ x (1 : ℝ)) • (∫ t in c..x, g t))
        (MeasureTheory.volume : Measure ℝ) ∧
      ∫ x,
          (fderiv ℝ θ x (1 : ℝ)) • (∫ t in c..x, g t)
          ∂(MeasureTheory.volume : Measure ℝ) =
        -∫ x, θ x • g x ∂(MeasureTheory.volume : Measure ℝ) := by
  let G : ℝ → ℝ := fun x ↦ ∫ t in c..x, g t
  have hθ_ac : AbsolutelyContinuousOnInterval θ l r :=
    contDiff_absolutelyContinuousOnInterval hθ
  have hG_ac : AbsolutelyContinuousOnInterval G l r := by
    exact hg.absolutelyContinuousOnInterval_intervalIntegral (c := c) hc
  have hleft_interval :
      IntervalIntegrable
        (fun x : ℝ ↦ (fderiv ℝ θ x (1 : ℝ)) • G x)
        MeasureTheory.volume l r := by
    simpa [G, fderiv_apply_one_eq_deriv, mul_comm] using
      hθ_ac.intervalIntegrable_deriv.continuousOn_mul hG_ac.continuousOn
  have hleft_on :
      IntegrableOn
        (fun x : ℝ ↦ (fderiv ℝ θ x (1 : ℝ)) • G x)
        (Set.Ioc l r) (MeasureTheory.volume : Measure ℝ) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hlr).1 hleft_interval
  have hleft_integrable :
      Integrable
        (fun x : ℝ ↦ (fderiv ℝ θ x (1 : ℝ)) • G x)
        (MeasureTheory.volume : Measure ℝ) := by
    exact hleft_on.integrable_of_forall_notMem_eq_zero (fun x hxIoc ↦ by
      have hx_not :
          x ∉ Function.support
            (fun y : ℝ ↦ (fderiv ℝ θ y (1 : ℝ)) • G y) := by
        exact fun hx ↦ hxIoc
          (support_fderiv_test_smul_subset_Ioc_of_le hlr hθI hx)
      exact Function.notMem_support.1 hx_not)
  have hderiv_eq :
      ∫ x in l..r, deriv G x * θ x =
        ∫ x in l..r, g x * θ x := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hg.ae_hasDerivAt_integral] with x hx hxmem
    have hxmem' : x ∈ Set.uIcc l r := Set.uIoc_subset_uIcc hxmem
    have hxderiv : HasDerivAt G (g x) x := by
      simpa [G] using hx hxmem' c hc
    simp [hxderiv.deriv]
  rcases eq_zero_at_endpoints_of_tsupport_subset_interior_uIcc hθI with
    ⟨hθl, hθr⟩
  have hboundary : G r * θ r - G l * θ l = 0 := by
    simp [G, hθl, hθr]
  have hibp :
      ∫ x in l..r, G x * deriv θ x =
        G r * θ r - G l * θ l -
          ∫ x in l..r, deriv G x * θ x :=
    hG_ac.integral_mul_deriv_eq_deriv_mul hθ_ac
  have hinterval :
      ∫ x in l..r, (fderiv ℝ θ x (1 : ℝ)) • G x =
        -∫ x in l..r, θ x • g x := by
    calc
      ∫ x in l..r, (fderiv ℝ θ x (1 : ℝ)) • G x
          = ∫ x in l..r, G x * deriv θ x := by
              simp [mul_comm]
      _ = G r * θ r - G l * θ l -
            ∫ x in l..r, deriv G x * θ x := hibp
      _ = 0 - ∫ x in l..r, g x * θ x := by
              rw [hboundary, hderiv_eq]
      _ = -∫ x in l..r, θ x • g x := by
              simp [mul_comm]
  refine ⟨hleft_integrable, ?_⟩
  calc
    ∫ x, (fderiv ℝ θ x (1 : ℝ)) • (∫ t in c..x, g t)
        ∂(MeasureTheory.volume : Measure ℝ)
        = ∫ x in l..r, (fderiv ℝ θ x (1 : ℝ)) • G x := by
            rw [intervalIntegral_fderiv_test_smul_eq_integral_of_le
              (θ := θ) (F := G) hlr hθI]
    _ = -∫ x in l..r, θ x • g x := hinterval
    _ = -∫ x, θ x • g x ∂(MeasureTheory.volume : Measure ℝ) := by
            rw [intervalIntegral_test_smul_eq_integral_of_le
              (θ := θ) (F := g) hlr hθI]

/--
%%handwave
name:
  Smooth tests integrate by parts against interval primitives
statement:
  Let \(g\) be integrable on a compact interval and let \(\theta\) be a
  smooth compactly supported test function whose support is contained in the
  interior of the interval.  Then
  \[
    \int \theta'(x)\Bigl(\int_a^x g(t)\,dt\Bigr)\,dx
      = -\int \theta(x)g(x)\,dx .
  \]
  Moreover, the left-hand integrand is integrable.
proof:
  The primitive of \(g\) is absolutely continuous and has derivative \(g\)
  almost everywhere on the interval.  Since \(\theta\) is smooth and vanishes
  at the boundary of the interval, the absolutely-continuous integration by
  parts formula has no boundary term.  Outside the interval the test and its
  derivative vanish, so the interval identity is the same as the whole-line
  identity.
-/
theorem realPrimitive_integral_fderiv_test_eq_neg_integral_test
    {g θ : ℝ → ℝ} {a b : ℝ}
    (hg : IntervalIntegrable g MeasureTheory.volume a b)
    (hθ : ContDiff ℝ ∞ θ) (_hθc : HasCompactSupport θ)
    (hθI : tsupport θ ⊆ interior (Set.uIcc a b)) :
    Integrable
        (fun x : ℝ ↦
          (fderiv ℝ θ x (1 : ℝ)) • (∫ t in a..x, g t))
        (MeasureTheory.volume : Measure ℝ) ∧
      ∫ x,
          (fderiv ℝ θ x (1 : ℝ)) • (∫ t in a..x, g t)
          ∂(MeasureTheory.volume : Measure ℝ) =
        -∫ x, θ x • g x ∂(MeasureTheory.volume : Measure ℝ) := by
  by_cases hab : a ≤ b
  · exact realPrimitive_integral_fderiv_test_eq_neg_integral_test_of_le
      (g := g) (θ := θ) (l := a) (r := b) (c := a)
      hab hg (by simp) hθ hθI
  · have hba : b ≤ a := le_of_not_ge hab
    have hθI' : tsupport θ ⊆ interior (Set.uIcc b a) := by
      simpa [Set.uIcc_comm] using hθI
    exact realPrimitive_integral_fderiv_test_eq_neg_integral_test_of_le
      (g := g) (θ := θ) (l := b) (r := a) (c := a)
      hba hg.symm (by simp) hθ hθI'

/--
%%handwave
name:
  The difference between a weak Sobolev function and the primitive of its
  weak derivative has zero distributional derivative
statement:
  Let \(u\) have weak derivative \(g\) on an open real region.  On an interval
  compactly contained in the region, the function
  \(u(x)-\int_a^x g(t)\,dt\) has zero distributional derivative: its pairing
  with the derivative of every smooth compactly supported test function in
  the interval vanishes.
proof:
  Apply the weak derivative identity to the test function.  The primitive of
  \(g\) is absolutely continuous with derivative \(g\) almost everywhere, so
  integration by parts for absolutely continuous functions gives the same
  pairing with opposite sign.  The two terms cancel.
-/
theorem realWeakSobolev_sub_primitive_distributional_derivative_zero_on_interval
    {Ω : Set ℝ} (hΩ_open : IsOpen Ω)
    {u g : ℝ → ℝ}
    (hweak : IsWeakDerivativeOnRealRegionScalar Ω u g)
    {a b : ℝ} (habΩ : Set.uIcc a b ⊆ Ω) :
    ∀ θ : ℝ → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      tsupport θ ⊆ interior (Set.uIcc a b) →
        ∫ x, (fderiv ℝ θ x (1 : ℝ)) •
            (u x - ∫ t in a..x, g t) ∂(MeasureTheory.volume : Measure ℝ) = 0 := by
  intro θ hθ hθc hθI
  have hθΩ : tsupport θ ⊆ Ω :=
    hθI.trans (interior_subset.trans habΩ)
  have hweak_eq :
      ∫ x, (fderiv ℝ θ x (1 : ℝ)) • u x
          ∂(MeasureTheory.volume : Measure ℝ) =
        -∫ x, θ x • g x ∂(MeasureTheory.volume : Measure ℝ) :=
    hweak.contDiff_test_integral_eq hθ hθc hθΩ
  have hderiv_support :
      tsupport (fun x : ℝ ↦ fderiv ℝ θ x (1 : ℝ)) ⊆ Ω :=
    (tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := θ) (1 : ℝ)).trans hθΩ
  rcases hweak.contDiff_test hθ hθc hθΩ with
    ⟨hleft_int_region, _hright_int_region, _hregion_eq⟩
  have hleft_int :
      Integrable (fun x : ℝ ↦ (fderiv ℝ θ x (1 : ℝ)) • u x)
        (MeasureTheory.volume : Measure ℝ) := by
    exact
      (show IntegrableOn
          (fun x : ℝ ↦ (fderiv ℝ θ x (1 : ℝ)) • u x) Ω
          (MeasureTheory.volume : Measure ℝ) from hleft_int_region)
        |>.integrable_of_forall_notMem_eq_zero (fun x hxΩ ↦ by
          have hx_not :
              x ∉ tsupport (fun y : ℝ ↦ fderiv ℝ θ y (1 : ℝ)) := by
            exact fun hx ↦ hxΩ (hderiv_support hx)
          simp [image_eq_zero_of_notMem_tsupport hx_not])
  have hg :
      IntervalIntegrable g MeasureTheory.volume a b :=
    realWeakSobolev_derivative_intervalIntegrable_on_uIcc
      hΩ_open hweak habΩ
  rcases realPrimitive_integral_fderiv_test_eq_neg_integral_test
      hg hθ hθc hθI with
    ⟨hprim_int, hprim_eq⟩
  calc
    ∫ x, (fderiv ℝ θ x (1 : ℝ)) •
        (u x - ∫ t in a..x, g t) ∂(MeasureTheory.volume : Measure ℝ)
        =
      ∫ x,
          ((fderiv ℝ θ x (1 : ℝ)) • u x -
            (fderiv ℝ θ x (1 : ℝ)) • (∫ t in a..x, g t))
          ∂(MeasureTheory.volume : Measure ℝ) := by
        refine integral_congr_ae (Filter.Eventually.of_forall ?_)
        intro x
        exact smul_sub (fderiv ℝ θ x (1 : ℝ)) (u x) (∫ t in a..x, g t)
    _ =
      ∫ x, (fderiv ℝ θ x (1 : ℝ)) • u x
          ∂(MeasureTheory.volume : Measure ℝ) -
        ∫ x, (fderiv ℝ θ x (1 : ℝ)) • (∫ t in a..x, g t)
          ∂(MeasureTheory.volume : Measure ℝ) := by
        exact integral_sub hleft_int hprim_int
    _ = (-∫ x, θ x • g x ∂(MeasureTheory.volume : Measure ℝ)) -
        (-∫ x, θ x • g x ∂(MeasureTheory.volume : Measure ℝ)) := by
        rw [hweak_eq, hprim_eq]
    _ = 0 := by ring

/--
%%handwave
name:
  Zero-mean tests are derivatives of compactly supported tests
statement:
  Let \(a<b\).  Suppose \(\phi\) is a smooth compactly supported test
  supported in \((a,b)\) and \(\int_a^b \phi=0\).  If a locally integrable
  function has zero distributional derivative on \((a,b)\), then
  \[
    \int \phi(x) w(x)\,dx = 0 .
  \]
proof:
  The primitive \(\theta(x)=\int_a^x\phi(t)\,dt\) is smooth, compactly
  supported in \((a,b)\), and satisfies \(\theta'=\phi\).  Applying the zero
  distributional derivative hypothesis to \(\theta\) gives the result.
-/
theorem realZeroMeanTest_integral_smul_eq_zero_of_distributional_derivative_zero
    {a b : ℝ} {w φ : ℝ → ℝ}
    (hab : a < b)
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφI : tsupport φ ⊆ interior (Set.uIcc a b))
    (hmean : ∫ t in a..b, φ t = 0)
    (hzero :
      ∀ θ : ℝ → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
        tsupport θ ⊆ interior (Set.uIcc a b) →
          ∫ x, (fderiv ℝ θ x (1 : ℝ)) • w x
            ∂(MeasureTheory.volume : Measure ℝ) = 0) :
    ∫ x, φ x • w x ∂(MeasureTheory.volume : Measure ℝ) = 0 := by
  let θ : ℝ → ℝ := fun x ↦ ∫ t in a..x, φ t
  have hφIoo : tsupport φ ⊆ Set.Ioo a b := by
    intro x hx
    have hxI := hφI hx
    rwa [Set.uIcc_of_le hab.le, interior_Icc] at hxI
  have hφint : ∀ c d : ℝ, IntervalIntegrable φ MeasureTheory.volume c d := by
    intro c d
    exact hφ.continuous.intervalIntegrable c d
  have hθ : ContDiff ℝ ∞ θ := by
    simpa [θ] using realPrimitive_contDiff_of_contDiff hφ a
  have hθc : HasCompactSupport θ := by
    simpa [θ] using
      realPrimitive_hasCompactSupport_of_tsupport_subset_Ioo_of_intervalIntegral_eq_zero
        hab.le hφIoo hφint hmean
  have hθI : tsupport θ ⊆ interior (Set.uIcc a b) := by
    simpa [θ] using
      realPrimitive_tsupport_subset_interior_uIcc_of_tsupport_subset_Ioo
        hab hφc hφIoo hφint hmean
  have hθzero := hzero θ hθ hθc hθI
  simpa [θ, realPrimitive_fderiv_apply_one_eq_of_contDiff hφ a] using hθzero

/--
%%handwave
name:
  Interval integrability gives integrability against interior-supported tests
statement:
  If \(w\) is integrable on the compact interval between \(a\) and \(b\), and
  \(\theta\) is continuous with compact support contained in the interior of
  that interval, then \(\theta w\) is integrable on the whole line.
proof:
  On the compact support of \(\theta\), integrability follows from the
  interval integrability of \(w\) and boundedness of the continuous function
  \(\theta\).  Off the support, the product vanishes.
-/
theorem integrable_test_smul_of_integrable_restrict_uIcc
    {a b : ℝ} {w θ : ℝ → ℝ}
    (hw : Integrable w (MeasureTheory.volume.restrict (Set.uIcc a b)))
    (hθ : Continuous θ) (hθc : HasCompactSupport θ)
    (hθI : tsupport θ ⊆ interior (Set.uIcc a b)) :
    Integrable (fun x : ℝ ↦ θ x • w x)
      (MeasureTheory.volume : Measure ℝ) := by
  have hw_interval : IntegrableOn w (Set.uIcc a b)
      (MeasureTheory.volume : Measure ℝ) := by
    simpa [IntegrableOn] using hw
  have hw_support : IntegrableOn w (tsupport θ)
      (MeasureTheory.volume : Measure ℝ) :=
    hw_interval.mono_set (hθI.trans interior_subset)
  have hprod_support :
      IntegrableOn (fun x : ℝ ↦ θ x • w x) (tsupport θ)
        (MeasureTheory.volume : Measure ℝ) :=
    hw_support.continuousOn_smul hθ.continuousOn hθc
  exact hprod_support.integrable_of_forall_notMem_eq_zero fun x hx ↦ by
    have hθx : θ x = 0 := image_eq_zero_of_notMem_tsupport hx
    simp [hθx]

/--
%%handwave
name:
  Every nondegenerate interval contains a smooth test of total integral one
statement:
  If \(a<b\), then there is a smooth compactly supported function
  \(\eta\), supported in \((a,b)\), whose integral over the line is one.
proof:
  Put a standard smooth bump at the midpoint of the interval with outer
  radius smaller than the distance to the endpoints, and normalize it by its
  integral.
-/
theorem exists_smooth_compactSupport_integral_one_tsupport_subset_Ioo
    {a b : ℝ} (hab : a < b) :
    ∃ η : ℝ → ℝ,
      ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧
        tsupport η ⊆ Set.Ioo a b ∧
        ∫ x, η x ∂(MeasureTheory.volume : Measure ℝ) = 1 := by
  let c : ℝ := (a + b) / 2
  let rOut : ℝ := (b - a) / 4
  let rIn : ℝ := (b - a) / 8
  have hba_pos : 0 < b - a := sub_pos.mpr hab
  have hrOut_pos : 0 < rOut := by
    dsimp [rOut]
    positivity
  have hrIn_pos : 0 < rIn := by
    dsimp [rIn]
    positivity
  have hrIn_lt_rOut : rIn < rOut := by
    dsimp [rIn, rOut]
    linarith
  let β : ContDiffBump c :=
    { rIn := rIn
      rOut := rOut
      rIn_pos := hrIn_pos
      rIn_lt_rOut := hrIn_lt_rOut }
  refine ⟨β.normed (MeasureTheory.volume : Measure ℝ), ?_, ?_, ?_, ?_⟩
  · exact β.contDiff_normed
  · exact β.hasCompactSupport_normed
  · intro x hx
    have hxballβ : x ∈ Metric.closedBall c β.rOut := by
      rw [β.tsupport_normed_eq (μ := MeasureTheory.volume)] at hx
      exact hx
    have hxball : x ∈ Metric.closedBall c rOut := by
      simpa [β] using hxballβ
    have hdist : |x - c| ≤ rOut := by
      simpa [Metric.mem_closedBall, Real.dist_eq, abs_sub_comm] using hxball
    have hleft_bound : c - rOut ≤ x := by
      have h := (abs_le.mp hdist).1
      linarith
    have hright_bound : x ≤ c + rOut := by
      have h := (abs_le.mp hdist).2
      linarith
    have hleft : a < c - rOut := by
      dsimp [c, rOut]
      linarith
    have hright : c + rOut < b := by
      dsimp [c, rOut]
      linarith
    exact ⟨lt_of_lt_of_le hleft hleft_bound,
      lt_of_le_of_lt hright_bound hright⟩
  · exact β.integral_normed

/--
%%handwave
name:
  Removing the mean of a test function
statement:
  Given a reference test \(\eta\) of total integral one, the zero-mean
  adjustment of a test \(\theta\) is
  \[
    \theta-\Bigl(\int \theta\Bigr)\eta .
  \]
-/
def realZeroMeanAdjustment (θ η : ℝ → ℝ) : ℝ → ℝ :=
  fun x ↦ θ x -
    (∫ y, θ y ∂(MeasureTheory.volume : Measure ℝ)) • η x

/--
%%handwave
name:
  The zero-mean adjustment is smooth
statement:
  If \(\theta\) and \(\eta\) are smooth, then
  \[
    \theta-\Bigl(\int \theta\Bigr)\eta
  \]
  is smooth.
proof:
  Smooth functions are closed under scalar multiplication and subtraction.
-/
theorem realZeroMeanAdjustment_contDiff
    {θ η : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η) :
    ContDiff ℝ ∞ (realZeroMeanAdjustment θ η) := by
  change ContDiff ℝ ∞
    (fun x ↦ θ x -
      (∫ y, θ y ∂(MeasureTheory.volume : Measure ℝ)) • η x)
  exact hθ.sub (hη.const_smul (∫ y, θ y ∂(MeasureTheory.volume : Measure ℝ)))

/--
%%handwave
name:
  The zero-mean adjustment has compact support
statement:
  If \(\theta\) and \(\eta\) have compact support, then
  \[
    \theta-\Bigl(\int \theta\Bigr)\eta
  \]
  has compact support.
proof:
  Compact support is preserved by scalar multiplication and subtraction.
-/
theorem realZeroMeanAdjustment_hasCompactSupport
    {θ η : ℝ → ℝ} (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) :
    HasCompactSupport (realZeroMeanAdjustment θ η) := by
  let m : ℝ := ∫ y, θ y ∂(MeasureTheory.volume : Measure ℝ)
  change HasCompactSupport (θ - ((fun _ : ℝ ↦ m) • η))
  have hmηc : HasCompactSupport (((fun _ : ℝ ↦ m) : ℝ → ℝ) • η) :=
    HasCompactSupport.smul_left (f := (fun _ : ℝ ↦ m)) (f' := η) hηc
  exact hθc.sub hmηc

/--
%%handwave
name:
  The zero-mean adjustment stays supported in the same interval
statement:
  If \(\theta\) and \(\eta\) are supported in the interior of an interval,
  then so is
  \[
    \theta-\Bigl(\int \theta\Bigr)\eta .
  \]
proof:
  The closed support of a difference lies in the union of the closed supports.
-/
theorem realZeroMeanAdjustment_tsupport_subset
    {a b : ℝ} {θ η : ℝ → ℝ}
    (hθI : tsupport θ ⊆ interior (Set.uIcc a b))
    (hηI : tsupport η ⊆ interior (Set.uIcc a b)) :
    tsupport (realZeroMeanAdjustment θ η) ⊆ interior (Set.uIcc a b) := by
  intro x hx
  let m : ℝ := ∫ y, θ y ∂(MeasureTheory.volume : Measure ℝ)
  have hx' :
      x ∈ tsupport θ ∪ tsupport (fun x : ℝ ↦ m • η x) := by
    exact tsupport_sub θ (fun x : ℝ ↦ m • η x) (by simpa [realZeroMeanAdjustment, m] using hx)
  have hmηI : tsupport (fun x : ℝ ↦ m • η x) ⊆
      interior (Set.uIcc a b) :=
    (tsupport_smul_subset_right (fun _ : ℝ ↦ m) η).trans hηI
  rcases hx' with hxθ | hxη
  · exact hθI hxθ
  · exact hmηI hxη

/--
%%handwave
name:
  The zero-mean adjustment has integral zero
statement:
  If \(\eta\) has total integral one, then
  \[
    \int \left(\theta-\Bigl(\int\theta\Bigr)\eta\right)=0
  \]
  for every compactly supported continuous \(\theta\).
proof:
  Expand the integral using linearity and the normalization of \(\eta\).
-/
theorem realZeroMeanAdjustment_integral_eq_zero
    {θ η : ℝ → ℝ} (hθ : Continuous θ) (hθc : HasCompactSupport θ)
    (hη : Continuous η) (hηc : HasCompactSupport η)
    (hη_one : ∫ y, η y ∂(MeasureTheory.volume : Measure ℝ) = 1) :
    ∫ x, realZeroMeanAdjustment θ η x
        ∂(MeasureTheory.volume : Measure ℝ) = 0 := by
  let m : ℝ := ∫ y, θ y ∂(MeasureTheory.volume : Measure ℝ)
  have hθ_int : Integrable θ (MeasureTheory.volume : Measure ℝ) :=
    hθ.integrable_of_hasCompactSupport hθc
  have hη_int : Integrable η (MeasureTheory.volume : Measure ℝ) :=
    hη.integrable_of_hasCompactSupport hηc
  have hmη_int : Integrable (fun x : ℝ ↦ m • η x)
      (MeasureTheory.volume : Measure ℝ) :=
    hη_int.smul m
  calc
    ∫ x, realZeroMeanAdjustment θ η x
        ∂(MeasureTheory.volume : Measure ℝ)
        =
      ∫ x, θ x - m • η x ∂(MeasureTheory.volume : Measure ℝ) := rfl
    _ = ∫ x, θ x ∂(MeasureTheory.volume : Measure ℝ) -
          ∫ x, m • η x ∂(MeasureTheory.volume : Measure ℝ) := by
            exact integral_sub hθ_int hmη_int
    _ = m - m • (∫ x, η x ∂(MeasureTheory.volume : Measure ℝ)) := by
            rw [integral_smul]
    _ = 0 := by
            simp [m, hη_one]

/--
%%handwave
name:
  The zero-mean adjustment has zero interval integral
statement:
  If \(a<b\), the supports of \(\theta\) and \(\eta\) lie in \((a,b)\), and
  \(\eta\) has total integral one, then the zero-mean adjustment has integral
  zero over \([a,b]\).
proof:
  The interval integral agrees with the whole-line integral because the
  support lies in the interval, and the whole-line integral is zero by the
  normalization calculation.
-/
theorem realZeroMeanAdjustment_intervalIntegral_eq_zero
    {a b : ℝ} {θ η : ℝ → ℝ} (hab : a < b)
    (hθ : Continuous θ) (hθc : HasCompactSupport θ)
    (hη : Continuous η) (hηc : HasCompactSupport η)
    (hθI : tsupport θ ⊆ interior (Set.uIcc a b))
    (hηI : tsupport η ⊆ interior (Set.uIcc a b))
    (hη_one : ∫ y, η y ∂(MeasureTheory.volume : Measure ℝ) = 1) :
    ∫ x in a..b, realZeroMeanAdjustment θ η x = 0 := by
  have hφI :
      tsupport (realZeroMeanAdjustment θ η) ⊆ interior (Set.uIcc a b) :=
    realZeroMeanAdjustment_tsupport_subset hθI hηI
  have hinterval :
      ∫ x in a..b, realZeroMeanAdjustment θ η x =
        ∫ x, realZeroMeanAdjustment θ η x
          ∂(MeasureTheory.volume : Measure ℝ) := by
    have h := intervalIntegral_test_smul_eq_integral_of_le
      (θ := realZeroMeanAdjustment θ η)
      (F := fun _ : ℝ ↦ (1 : ℝ)) hab.le hφI
    simpa using h
  exact hinterval.trans
    (realZeroMeanAdjustment_integral_eq_zero hθ hθc hη hηc hη_one)

/--
%%handwave
name:
  Zero distributional derivative annihilates zero-mean adjustments
statement:
  Let \(a<b\).  Suppose \(w\) has zero distributional derivative on
  \((a,b)\).  If \(\eta\) is a smooth compactly supported test in \((a,b)\)
  with integral one, then for every smooth compactly supported test
  \(\theta\) in \((a,b)\),
  \[
    \int \left(\theta-\Bigl(\int\theta\Bigr)\eta\right) w =0 .
  \]
proof:
  The adjusted test is smooth, compactly supported in the interval, and has
  zero interval integral.  Apply the primitive form of the zero-distributional
  derivative argument.
-/
theorem realZeroMeanAdjustment_integral_smul_eq_zero_of_distributional_derivative_zero
    {a b : ℝ} {w θ η : ℝ → ℝ} (hab : a < b)
    (hθ : ContDiff ℝ ∞ θ) (hθc : HasCompactSupport θ)
    (hθI : tsupport θ ⊆ interior (Set.uIcc a b))
    (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηI : tsupport η ⊆ interior (Set.uIcc a b))
    (hη_one : ∫ y, η y ∂(MeasureTheory.volume : Measure ℝ) = 1)
    (hzero :
      ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ interior (Set.uIcc a b) →
          ∫ x, (fderiv ℝ ψ x (1 : ℝ)) • w x
            ∂(MeasureTheory.volume : Measure ℝ) = 0) :
    ∫ x, realZeroMeanAdjustment θ η x • w x
        ∂(MeasureTheory.volume : Measure ℝ) = 0 := by
  have hφ : ContDiff ℝ ∞ (realZeroMeanAdjustment θ η) :=
    realZeroMeanAdjustment_contDiff hθ hη
  have hφc : HasCompactSupport (realZeroMeanAdjustment θ η) :=
    realZeroMeanAdjustment_hasCompactSupport hθc hηc
  have hφI : tsupport (realZeroMeanAdjustment θ η) ⊆
      interior (Set.uIcc a b) :=
    realZeroMeanAdjustment_tsupport_subset hθI hηI
  have hφmean :
      ∫ x in a..b, realZeroMeanAdjustment θ η x = 0 :=
    realZeroMeanAdjustment_intervalIntegral_eq_zero
      hab hθ.continuous hθc hη.continuous hηc hθI hηI hη_one
  exact
    realZeroMeanTest_integral_smul_eq_zero_of_distributional_derivative_zero
      hab hφ hφc hφI hφmean hzero

/--
%%handwave
name:
  Pairing of the zero-mean adjustment expands linearly
statement:
  If \(w\) is integrable on the interval and \(\theta,\eta\) are compactly
  supported in its interior, then
  \[
    \int \left(\theta-\Bigl(\int\theta\Bigr)\eta\right)w
      =
    \int \theta w - \Bigl(\int\theta\Bigr)\int\eta w .
  \]
proof:
  The products are integrable because the tests have compact support inside
  the interval.  The identity is then just linearity of the integral.
-/
theorem realZeroMeanAdjustment_integral_smul_expand
    {a b : ℝ} {w θ η : ℝ → ℝ}
    (hw : Integrable w (MeasureTheory.volume.restrict (Set.uIcc a b)))
    (hθ : Continuous θ) (hθc : HasCompactSupport θ)
    (hθI : tsupport θ ⊆ interior (Set.uIcc a b))
    (hη : Continuous η) (hηc : HasCompactSupport η)
    (hηI : tsupport η ⊆ interior (Set.uIcc a b)) :
    ∫ x, realZeroMeanAdjustment θ η x • w x
        ∂(MeasureTheory.volume : Measure ℝ) =
      ∫ x, θ x • w x ∂(MeasureTheory.volume : Measure ℝ) -
        (∫ x, θ x ∂(MeasureTheory.volume : Measure ℝ)) •
          (∫ x, η x • w x ∂(MeasureTheory.volume : Measure ℝ)) := by
  let m : ℝ := ∫ x, θ x ∂(MeasureTheory.volume : Measure ℝ)
  have hηw_int : Integrable (fun x : ℝ ↦ η x • w x)
      (MeasureTheory.volume : Measure ℝ) :=
    integrable_test_smul_of_integrable_restrict_uIcc
      hw hη hηc hηI
  have hθw_int : Integrable (fun x : ℝ ↦ θ x • w x)
      (MeasureTheory.volume : Measure ℝ) :=
    integrable_test_smul_of_integrable_restrict_uIcc
      hw hθ hθc hθI
  have hmηw_int : Integrable (fun x : ℝ ↦ (m • η x) • w x)
      (MeasureTheory.volume : Measure ℝ) := by
    have hmηw_eq :
        (fun x : ℝ ↦ (m • η x) • w x) =
          fun x : ℝ ↦ m • (η x • w x) := by
      funext x
      simp [mul_assoc]
    rw [hmηw_eq]
    exact hηw_int.smul m
  have hsub :
      ∫ x, realZeroMeanAdjustment θ η x • w x
          ∂(MeasureTheory.volume : Measure ℝ) =
        ∫ x, θ x • w x ∂(MeasureTheory.volume : Measure ℝ) -
          ∫ x, (m • η x) • w x ∂(MeasureTheory.volume : Measure ℝ) := by
    calc
      ∫ x, realZeroMeanAdjustment θ η x • w x
          ∂(MeasureTheory.volume : Measure ℝ)
          =
        ∫ x, (θ x • w x) - ((m • η x) • w x)
          ∂(MeasureTheory.volume : Measure ℝ) := by
            refine integral_congr_ae (Filter.Eventually.of_forall ?_)
            intro x
            simp only [realZeroMeanAdjustment]
            dsimp [m]
            ring
      _ = ∫ x, θ x • w x ∂(MeasureTheory.volume : Measure ℝ) -
            ∫ x, (m • η x) • w x ∂(MeasureTheory.volume : Measure ℝ) := by
              exact integral_sub hθw_int hmηw_int
  have hmηw_integral :
      ∫ x, (m • η x) • w x ∂(MeasureTheory.volume : Measure ℝ) =
        m • (∫ x, η x • w x ∂(MeasureTheory.volume : Measure ℝ)) := by
    have hmηw_eq :
        (fun x : ℝ ↦ (m • η x) • w x) =
          fun x : ℝ ↦ m • (η x • w x) := by
      funext x
      simp [mul_assoc]
    rw [hmηw_eq, integral_smul]
  rw [hmηw_integral] at hsub
  simpa [m] using hsub

/--
%%handwave
name:
  Zero distributional derivative gives constant pairings with test functions
statement:
  Let \(a<b\).  If \(w\) is integrable on \([a,b]\) and has zero
  distributional derivative on \((a,b)\), then there is a constant \(C\) such
  that every smooth compactly supported test \(\theta\) in \((a,b)\) satisfies
  \[
    \int \theta(x)w(x)\,dx
      =\int \theta(x)C\,dx .
  \]
proof:
  Choose a smooth test \(\eta\) supported in \((a,b)\) with total integral
  one, and set \(C=\int \eta w\).  For any test \(\theta\), the adjusted test
  \(\theta-(\int\theta)\eta\) has zero mean, so its pairing with \(w\)
  vanishes.  Expanding that identity gives the formula.
-/
theorem realDistributionalDerivative_zero_test_integral_eq_const_integral_on_ordered_interval
    {a b : ℝ} {w : ℝ → ℝ} (hab : a < b)
    (hw : Integrable w (MeasureTheory.volume.restrict (Set.uIcc a b)))
    (hzero :
      ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ interior (Set.uIcc a b) →
          ∫ x, (fderiv ℝ ψ x (1 : ℝ)) • w x
            ∂(MeasureTheory.volume : Measure ℝ) = 0) :
    ∃ C : ℝ,
      ∀ θ : ℝ → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
        tsupport θ ⊆ interior (Set.uIcc a b) →
          ∫ x, θ x • w x ∂(MeasureTheory.volume : Measure ℝ) =
            ∫ x, θ x • C ∂(MeasureTheory.volume : Measure ℝ) := by
  rcases exists_smooth_compactSupport_integral_one_tsupport_subset_Ioo hab with
    ⟨η, hη, hηc, hηIoo, hη_one⟩
  have hηI : tsupport η ⊆ interior (Set.uIcc a b) := by
    intro x hx
    have hxIoo := hηIoo hx
    rwa [Set.uIcc_of_le hab.le, interior_Icc]
  let C : ℝ := ∫ x, η x • w x ∂(MeasureTheory.volume : Measure ℝ)
  refine ⟨C, ?_⟩
  intro θ hθ hθc hθI
  let m : ℝ := ∫ x, θ x ∂(MeasureTheory.volume : Measure ℝ)
  have hzero_adj :
      ∫ x, realZeroMeanAdjustment θ η x • w x
          ∂(MeasureTheory.volume : Measure ℝ) = 0 :=
    realZeroMeanAdjustment_integral_smul_eq_zero_of_distributional_derivative_zero
      hab hθ hθc hθI hη hηc hηI hη_one hzero
  have hexpand :
      ∫ x, realZeroMeanAdjustment θ η x • w x
          ∂(MeasureTheory.volume : Measure ℝ) =
        ∫ x, θ x • w x ∂(MeasureTheory.volume : Measure ℝ) -
          m • C := by
    simpa [m, C] using
      realZeroMeanAdjustment_integral_smul_expand
        (a := a) (b := b) (w := w) (θ := θ) (η := η)
        hw hθ.continuous hθc hθI hη.continuous hηc hηI
  have hmain :
      ∫ x, θ x • w x ∂(MeasureTheory.volume : Measure ℝ) - m • C = 0 := by
    rw [← hexpand, hzero_adj]
  have hθw_eq :
      ∫ x, θ x • w x ∂(MeasureTheory.volume : Measure ℝ) = m • C := by
    linarith
  calc
    ∫ x, θ x • w x ∂(MeasureTheory.volume : Measure ℝ)
        = m • C := hθw_eq
    _ = ∫ x, θ x • C ∂(MeasureTheory.volume : Measure ℝ) := by
        rw [integral_smul_const]

/--
%%handwave
name:
  Zero distributional derivative gives an almost everywhere constant on an
  ordered interval
statement:
  Let \(a<b\).  If an integrable function on \([a,b]\) has zero
  distributional derivative on \((a,b)\), then it agrees almost everywhere on
  \([a,b]\) with a constant.
proof:
  First show that all smooth compactly supported tests in \((a,b)\) pair with
  \(w\) exactly as they pair with a fixed constant.  Thus the difference
  between \(w\) and that constant annihilates every such test.  The
  smooth-test separation theorem gives equality almost everywhere on
  \((a,b)\), and the endpoints have zero Lebesgue measure.
-/
theorem realDistributionalDerivative_zero_ae_const_on_ordered_interval
    {a b : ℝ} {w : ℝ → ℝ} (hab : a < b)
    (hw : Integrable w (MeasureTheory.volume.restrict (Set.uIcc a b)))
    (hzero :
      ∀ θ : ℝ → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
        tsupport θ ⊆ interior (Set.uIcc a b) →
          ∫ x, (fderiv ℝ θ x (1 : ℝ)) • w x
            ∂(MeasureTheory.volume : Measure ℝ) = 0) :
    ∃ C : ℝ,
      w =ᵐ[MeasureTheory.volume.restrict (Set.uIcc a b)] fun _ : ℝ ↦ C := by
  rcases
      realDistributionalDerivative_zero_test_integral_eq_const_integral_on_ordered_interval
        hab hw hzero with
    ⟨C, hpair⟩
  refine ⟨C, ?_⟩
  let U : Set ℝ := interior (Set.uIcc a b)
  have hw_interval : IntegrableOn w (Set.uIcc a b)
      (MeasureTheory.volume : Measure ℝ) := by
    simpa [IntegrableOn] using hw
  have hw_U_integrable : IntegrableOn w U
      (MeasureTheory.volume : Measure ℝ) :=
    hw_interval.mono_set interior_subset
  have hw_U : LocallyIntegrableOn w U
      (MeasureTheory.volume : Measure ℝ) :=
    hw_U_integrable.locallyIntegrableOn
  have hC_U : LocallyIntegrableOn (fun _ : ℝ ↦ C) U
      (MeasureTheory.volume : Measure ℝ) :=
    MeasureTheory.locallyIntegrableOn_const C
  have hsub_U : LocallyIntegrableOn (fun x : ℝ ↦ w x - C) U
      (MeasureTheory.volume : Measure ℝ) :=
    hw_U.sub hC_U
  have htest_zero :
      ∀ θ : ℝ → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ → tsupport θ ⊆ U →
        ∫ x, θ x • (w x - C) ∂(MeasureTheory.volume : Measure ℝ) = 0 := by
    intro θ hθ hθc hθU
    have hθw_int : Integrable (fun x : ℝ ↦ θ x • w x)
        (MeasureTheory.volume : Measure ℝ) :=
      integrable_test_smul_of_integrable_restrict_uIcc
        hw hθ.continuous hθc hθU
    have hθ_int : Integrable θ (MeasureTheory.volume : Measure ℝ) :=
      hθ.continuous.integrable_of_hasCompactSupport hθc
    have hθC_int : Integrable (fun x : ℝ ↦ θ x • C)
        (MeasureTheory.volume : Measure ℝ) :=
      hθ_int.smul_const C
    calc
      ∫ x, θ x • (w x - C) ∂(MeasureTheory.volume : Measure ℝ)
          =
        ∫ x, θ x • w x - θ x • C
          ∂(MeasureTheory.volume : Measure ℝ) := by
            refine integral_congr_ae (Filter.Eventually.of_forall ?_)
            intro x
            simp [smul_eq_mul]
            ring
      _ = ∫ x, θ x • w x ∂(MeasureTheory.volume : Measure ℝ) -
            ∫ x, θ x • C ∂(MeasureTheory.volume : Measure ℝ) := by
              exact integral_sub hθw_int hθC_int
      _ = 0 := by
              exact sub_eq_zero.mpr (hpair θ hθ hθc hθU)
  have hsub_zero_U :
      (fun x : ℝ ↦ w x - C) =ᵐ[MeasureTheory.volume.restrict U]
        fun _ : ℝ ↦ 0 :=
    realLocallyIntegrableOn_ae_eq_zero_of_integral_contDiff_smul_eq_zero_on_open
      (by
        dsimp [U]
        exact isOpen_interior)
      hsub_U htest_zero
  have hU_ae_interval :
      U =ᵐ[(MeasureTheory.volume : Measure ℝ)] Set.uIcc a b := by
    dsimp [U]
    rw [Set.uIcc_of_le hab.le, interior_Icc]
    exact MeasureTheory.Ioo_ae_eq_Icc
  have hsub_zero_interval :
      (fun x : ℝ ↦ w x - C) =ᵐ[MeasureTheory.volume.restrict (Set.uIcc a b)]
        fun _ : ℝ ↦ 0 := by
    rw [← MeasureTheory.Measure.restrict_congr_set hU_ae_interval]
    exact hsub_zero_U
  filter_upwards [hsub_zero_interval] with x hx
  linarith

/--
%%handwave
name:
  A locally integrable function with zero distributional derivative on an
  interval is almost everywhere constant
statement:
  If an integrable function on a compact interval pairs to zero against the
  derivative of every smooth compactly supported test function in the
  interior, then it is equal almost everywhere on the interval to a constant.
proof:
  This is the one-dimensional distributional uniqueness theorem.  A
  distribution whose derivative vanishes on an interval is constant on each
  connected component; the interval is connected, so there is one constant.
-/
theorem realDistributionalDerivative_zero_ae_const_on_interval
    {a b : ℝ} {w : ℝ → ℝ}
    (hw : Integrable w (MeasureTheory.volume.restrict (Set.uIcc a b)))
    (hzero :
      ∀ θ : ℝ → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
        tsupport θ ⊆ interior (Set.uIcc a b) →
          ∫ x, (fderiv ℝ θ x (1 : ℝ)) • w x
            ∂(MeasureTheory.volume : Measure ℝ) = 0) :
    ∃ C : ℝ,
      w =ᵐ[MeasureTheory.volume.restrict (Set.uIcc a b)] fun _ : ℝ ↦ C := by
  by_cases hab : a < b
  · exact realDistributionalDerivative_zero_ae_const_on_ordered_interval
      hab hw hzero
  · by_cases hba : b < a
    · have hw' : Integrable w
          (MeasureTheory.volume.restrict (Set.uIcc b a)) := by
        simpa [Set.uIcc_comm] using hw
      have hzero' :
          ∀ θ : ℝ → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
            tsupport θ ⊆ interior (Set.uIcc b a) →
              ∫ x, (fderiv ℝ θ x (1 : ℝ)) • w x
                ∂(MeasureTheory.volume : Measure ℝ) = 0 := by
        intro θ hθ hθc hθI
        exact hzero θ hθ hθc (by simpa [Set.uIcc_comm] using hθI)
      rcases realDistributionalDerivative_zero_ae_const_on_ordered_interval
          hba hw' hzero' with ⟨C, hC⟩
      refine ⟨C, ?_⟩
      simpa [Set.uIcc_comm] using hC
    · have hle_ab : a ≤ b := le_of_not_gt hba
      have hle_ba : b ≤ a := le_of_not_gt hab
      have hEq : a = b := le_antisymm hle_ab hle_ba
      subst b
      refine ⟨0, ?_⟩
      rw [Set.uIcc_of_le le_rfl]
      simp
      exact Filter.eventually_bot

/--
%%handwave
name:
  Distributional primitives identify weak Sobolev functions on intervals
statement:
  Let \(u\) have weak derivative \(g\) on an open real region.  On every
  compact interval contained in the region, \(u\) agrees almost everywhere
  with a primitive of \(g\), up to an additive constant.
proof:
  Subtract the primitive of \(g\).  The weak derivative of the difference is
  zero on the interval.  A locally integrable function whose distributional
  derivative vanishes on an interval is almost everywhere constant there.
-/
theorem realWeakSobolev_eq_primitive_add_const_ae_on_interval
    {Ω : Set ℝ} (hΩ_open : IsOpen Ω)
    {u g : ℝ → ℝ}
    (hweak : IsWeakDerivativeOnRealRegionScalar Ω u g)
    {a b : ℝ} (habΩ : Set.uIcc a b ⊆ Ω) :
    ∃ C : ℝ,
      u =ᵐ[MeasureTheory.volume.restrict (Set.uIcc a b)]
        fun x : ℝ ↦ C + ∫ t in a..x, g t := by
  let G : ℝ → ℝ := fun x ↦ ∫ t in a..x, g t
  have hu_integrable :
      Integrable u (MeasureTheory.volume.restrict (Set.uIcc a b)) :=
    realWeakSobolev_function_integrableOn_compact
      isCompact_uIcc habΩ hΩ_open hweak
  have hg_interval :
      IntervalIntegrable g MeasureTheory.volume a b :=
    realWeakSobolev_derivative_intervalIntegrable_on_uIcc
      hΩ_open hweak habΩ
  have hG_ac : AbsolutelyContinuousOnInterval G a b := by
    exact realPrimitive_absolutelyContinuousOnInterval_of_intervalIntegrable
      hg_interval
  have hG_integrable :
      Integrable G (MeasureTheory.volume.restrict (Set.uIcc a b)) := by
    exact hG_ac.continuousOn.integrableOn_uIcc
  have hw_integrable :
      Integrable (fun x : ℝ ↦ u x - G x)
        (MeasureTheory.volume.restrict (Set.uIcc a b)) :=
    hu_integrable.sub hG_integrable
  have hzero :
      ∀ θ : ℝ → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
        tsupport θ ⊆ interior (Set.uIcc a b) →
          ∫ x, (fderiv ℝ θ x (1 : ℝ)) • (u x - G x)
            ∂(MeasureTheory.volume : Measure ℝ) = 0 := by
    simpa [G] using
      realWeakSobolev_sub_primitive_distributional_derivative_zero_on_interval
        hΩ_open hweak habΩ
  rcases realDistributionalDerivative_zero_ae_const_on_interval
      hw_integrable hzero with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  filter_upwards [hC] with x hx
  dsimp [G] at hx ⊢
  linarith

/--
%%handwave
name:
  Interval primitives agree on open overlaps
statement:
  Let two compact intervals lie in an open real region, and suppose that on
  each interval the same locally integrable function is represented almost
  everywhere by a primitive of \(g\), possibly with different additive
  constants and different base points.  On every open subinterval contained
  in the overlap, the two primitive representatives agree pointwise.
proof:
  The two primitive representatives are continuous on their intervals.  On
  the open overlap they are almost everywhere equal, because both agree
  almost everywhere with the same function.  A continuous function that
  vanishes almost everywhere on an open set with respect to Lebesgue measure
  vanishes everywhere on that open set.
-/
theorem realPrimitive_representatives_agree_on_open_overlap
    {Ω U : Set ℝ} {u g : ℝ → ℝ}
    (hg_interval :
      ∀ a b : ℝ, Set.uIcc a b ⊆ Ω →
        IntervalIntegrable g MeasureTheory.volume a b)
    (hU_open : IsOpen U)
    {a b c d C D : ℝ}
    (habΩ : Set.uIcc a b ⊆ Ω) (hcdΩ : Set.uIcc c d ⊆ Ω)
    (hUab : U ⊆ Set.uIcc a b) (hUcd : U ⊆ Set.uIcc c d)
    (hC :
      u =ᵐ[MeasureTheory.volume.restrict (Set.uIcc a b)]
        fun x : ℝ ↦ C + ∫ t in a..x, g t)
    (hD :
      u =ᵐ[MeasureTheory.volume.restrict (Set.uIcc c d)]
        fun x : ℝ ↦ D + ∫ t in c..x, g t) :
    Set.EqOn
      (fun x : ℝ ↦ C + ∫ t in a..x, g t)
      (fun x : ℝ ↦ D + ∫ t in c..x, g t) U := by
  have hCU :
      u =ᵐ[MeasureTheory.volume.restrict U]
        fun x : ℝ ↦ C + ∫ t in a..x, g t :=
    ae_restrict_of_ae_restrict_of_subset hUab hC
  have hDU :
      u =ᵐ[MeasureTheory.volume.restrict U]
        fun x : ℝ ↦ D + ∫ t in c..x, g t :=
    ae_restrict_of_ae_restrict_of_subset hUcd hD
  have hprim_eq :
      (fun x : ℝ ↦ C + ∫ t in a..x, g t)
        =ᵐ[MeasureTheory.volume.restrict U]
      fun x : ℝ ↦ D + ∫ t in c..x, g t :=
    hCU.symm.trans hDU
  have hC_cont :
      ContinuousOn (fun x : ℝ ↦ C + ∫ t in a..x, g t) U :=
    (realPrimitive_add_const_acl_on_interval
      (hg_interval a b habΩ)).1.continuousOn.mono hUab
  have hD_cont :
      ContinuousOn (fun x : ℝ ↦ D + ∫ t in c..x, g t) U :=
    (realPrimitive_add_const_acl_on_interval
      (hg_interval c d hcdΩ)).1.continuousOn.mono hUcd
  exact MeasureTheory.Measure.eqOn_open_of_ae_eq
    (μ := (MeasureTheory.volume : Measure ℝ)) hprim_eq hU_open hC_cont hD_cont

/--
%%handwave
name:
  Interval primitives agree on open interval overlaps
statement:
  Under the same hypotheses as the open-overlap comparison, the primitive
  representatives agree pointwise on every open interval contained in the
  overlap of the two compact intervals.
proof:
  Apply the open-overlap comparison to the chosen open interval.
-/
theorem realPrimitive_representatives_agree_on_Ioo_overlap
    {Ω : Set ℝ} {u g : ℝ → ℝ}
    (hg_interval :
      ∀ a b : ℝ, Set.uIcc a b ⊆ Ω →
        IntervalIntegrable g MeasureTheory.volume a b)
    {a b c d l r C D : ℝ}
    (habΩ : Set.uIcc a b ⊆ Ω) (hcdΩ : Set.uIcc c d ⊆ Ω)
    (hIab : Set.Ioo l r ⊆ Set.uIcc a b)
    (hIcd : Set.Ioo l r ⊆ Set.uIcc c d)
    (hC :
      u =ᵐ[MeasureTheory.volume.restrict (Set.uIcc a b)]
        fun x : ℝ ↦ C + ∫ t in a..x, g t)
    (hD :
      u =ᵐ[MeasureTheory.volume.restrict (Set.uIcc c d)]
        fun x : ℝ ↦ D + ∫ t in c..x, g t) :
    Set.EqOn
      (fun x : ℝ ↦ C + ∫ t in a..x, g t)
      (fun x : ℝ ↦ D + ∫ t in c..x, g t) (Set.Ioo l r) := by
  exact realPrimitive_representatives_agree_on_open_overlap
    (Ω := Ω) (U := Set.Ioo l r) (u := u) (g := g)
    hg_interval isOpen_Ioo habΩ hcdΩ hIab hIcd hC hD

/--
%%handwave
name:
  Open real sets contain right-hand compact intervals
statement:
  Every point of an open subset of the real line is the left endpoint of a
  nondegenerate compact interval contained in the open set.
proof:
  Choose a small metric ball around the point contained in the open set, and
  take the right endpoint halfway across that ball.
-/
theorem realOpenSet_exists_right_uIcc_subset
    {Ω : Set ℝ} (hΩ_open : IsOpen Ω) {p : ℝ} (hp : p ∈ Ω) :
    ∃ q : ℝ, p < q ∧ Set.uIcc p q ⊆ Ω := by
  rcases Metric.isOpen_iff.mp hΩ_open p hp with ⟨ε, hε_pos, hεΩ⟩
  refine ⟨p + ε / 2, by linarith, ?_⟩
  intro y hy
  have hpq : p ≤ p + ε / 2 := by linarith
  have hyIcc : y ∈ Set.Icc p (p + ε / 2) := by
    simpa [Set.uIcc_of_le hpq] using hy
  have hdist : dist y p < ε := by
    rw [Real.dist_eq]
    have hnonneg : 0 ≤ y - p := sub_nonneg.mpr hyIcc.1
    have hle : y - p ≤ ε / 2 := by linarith [hyIcc.2]
    rw [abs_of_nonneg hnonneg]
    linarith
  exact hεΩ hdist

/--
%%handwave
name:
  A base point for each order component of an open real set
statement:
  For every point of a real set, choose a point in the same order-connected
  component, and outside the set leave the point unchanged.
-/
noncomputable def realOpenOrdComponentBase (Ω : Set ℝ) (x : ℝ) : ℝ :=
  by
    classical
    exact if hx : x ∈ Ω then Set.ordConnectedProj Ω ⟨x, hx⟩ else x

/--
%%handwave
name:
  The chosen component base point lies in the set
statement:
  If \(x\) lies in the set, then its chosen order-component base point also
  lies in the set.
proof:
  The chosen base point lies in the order-connected component of \(x\), and
  every such component is contained in the original set.
-/
theorem realOpenOrdComponentBase_mem
    {Ω : Set ℝ} {x : ℝ} (hx : x ∈ Ω) :
    realOpenOrdComponentBase Ω x ∈ Ω := by
  classical
  have hbase : Set.ordConnectedProj Ω ⟨x, hx⟩ ∈ Ω :=
    Set.ordConnectedComponent_subset
    (Set.ordConnectedProj_mem_ordConnectedComponent Ω ⟨x, hx⟩)
  simpa [realOpenOrdComponentBase, hx] using hbase

/--
%%handwave
name:
  Points are connected to their chosen base point inside the set
statement:
  If \(x\) lies in the set, then the compact interval joining \(x\) to its
  chosen order-component base point is contained in the set.
proof:
  This is exactly the defining property of the order-connected component.
-/
theorem realOpenOrdComponentBase_uIcc_subset
    {Ω : Set ℝ} {x : ℝ} (hx : x ∈ Ω) :
    Set.uIcc (realOpenOrdComponentBase Ω x) x ⊆ Ω := by
  classical
  have hmem : Set.uIcc (Set.ordConnectedProj Ω ⟨x, hx⟩) x ⊆ Ω := by
    change x ∈ Set.ordConnectedComponent Ω
      (Set.ordConnectedProj Ω ⟨x, hx⟩)
    exact Set.mem_ordConnectedComponent_ordConnectedProj Ω ⟨x, hx⟩
  simpa [realOpenOrdComponentBase, hx] using hmem

/--
%%handwave
name:
  The chosen base point is constant along an order-connected interval
statement:
  If two points of a set can be joined by a compact interval contained in the
  set, then they have the same chosen order-component base point.
proof:
  The chosen section takes exactly one point from each order-connected
  component.
-/
theorem realOpenOrdComponentBase_eq_of_uIcc_subset
    {Ω : Set ℝ} {x y : ℝ} (hx : x ∈ Ω) (hy : y ∈ Ω)
    (hxy : Set.uIcc x y ⊆ Ω) :
    realOpenOrdComponentBase Ω x = realOpenOrdComponentBase Ω y := by
  classical
  have hbase : Set.ordConnectedProj Ω ⟨x, hx⟩ =
      Set.ordConnectedProj Ω ⟨y, hy⟩ :=
    Set.ordConnectedProj_eq.2 hxy
  simpa [realOpenOrdComponentBase, hx, hy] using hbase

/--
%%handwave
name:
  The chosen base point is constant on compact intervals inside the set
statement:
  On any compact interval contained in a set, all points have the same chosen
  order-component base point.
proof:
  Every point of the interval can be joined to either endpoint by a smaller
  compact interval still contained in the original interval.
-/
theorem realOpenOrdComponentBase_eq_on_uIcc
    {Ω : Set ℝ} {a b x : ℝ}
    (habΩ : Set.uIcc a b ⊆ Ω) (hx : x ∈ Set.uIcc a b) :
    realOpenOrdComponentBase Ω x = realOpenOrdComponentBase Ω a := by
  classical
  have haΩ : a ∈ Ω := habΩ Set.left_mem_uIcc
  have hxΩ : x ∈ Ω := habΩ hx
  have hxa : Set.uIcc x a ⊆ Ω := by
    exact (Set.uIcc_subset_uIcc hx Set.left_mem_uIcc).trans habΩ
  exact realOpenOrdComponentBase_eq_of_uIcc_subset hxΩ haΩ hxa

/--
%%handwave
name:
  Equal chosen base points characterize being in the same order component
statement:
  If two points of the open set have the same chosen order-component base
  point, then the compact interval joining them is contained in the set.
proof:
  The chosen base point is the quotient representative of the order-connected
  component, and equality of these representatives means the two points lie in
  the same order component.
-/
theorem realOpenOrdComponentBase_uIcc_subset_of_eq_base
    {Ω : Set ℝ} {x y : ℝ} (hx : x ∈ Ω) (hy : y ∈ Ω)
    (hbase : realOpenOrdComponentBase Ω x = realOpenOrdComponentBase Ω y) :
    Set.uIcc x y ⊆ Ω := by
  classical
  have hproj :
      Set.ordConnectedProj Ω ⟨x, hx⟩ =
        Set.ordConnectedProj Ω ⟨y, hy⟩ := by
    simpa [realOpenOrdComponentBase, hx, hy] using hbase
  exact Set.ordConnectedProj_eq.1 hproj

/--
%%handwave
name:
  Chosen component base points are fixed by the base-point choice
statement:
  If \(x\) lies in the set, then applying the component base-point choice to
  the chosen base point gives the same base point.
proof:
  The chosen base point and the original point lie in the same
  order-connected component.
-/
theorem realOpenOrdComponentBase_idem
    {Ω : Set ℝ} {x : ℝ} (hx : x ∈ Ω) :
    realOpenOrdComponentBase Ω (realOpenOrdComponentBase Ω x) =
      realOpenOrdComponentBase Ω x := by
  have hpΩ : realOpenOrdComponentBase Ω x ∈ Ω :=
    realOpenOrdComponentBase_mem (Ω := Ω) hx
  have hpx : Set.uIcc (realOpenOrdComponentBase Ω x) x ⊆ Ω :=
    realOpenOrdComponentBase_uIcc_subset (Ω := Ω) hx
  exact realOpenOrdComponentBase_eq_of_uIcc_subset hpΩ hx hpx

/--
%%handwave
name:
  A right-hand anchor inside an open real set
statement:
  From each point of an open real set choose a strictly larger point such
  that the compact interval between them remains in the open set.
-/
noncomputable def realOpenRightAnchor
    (Ω : Set ℝ) (hΩ_open : IsOpen Ω) (p : ℝ) : ℝ :=
  by
    classical
    exact
      if hp : p ∈ Ω then
        Classical.choose (realOpenSet_exists_right_uIcc_subset hΩ_open hp)
      else p

/--
%%handwave
name:
  The right-hand anchor is strictly to the right
statement:
  If \(p\) lies in the open set, its chosen right-hand anchor is strictly
  larger than \(p\).
proof:
  This is part of the chosen compact interval contained in the open set.
-/
theorem realOpenRightAnchor_gt
    {Ω : Set ℝ} {hΩ_open : IsOpen Ω} {p : ℝ} (hp : p ∈ Ω) :
    p < realOpenRightAnchor Ω hΩ_open p := by
  classical
  have hchoose :=
    (Classical.choose_spec
      (realOpenSet_exists_right_uIcc_subset hΩ_open hp)).1
  simpa [realOpenRightAnchor, hp] using hchoose

/--
%%handwave
name:
  The interval to the right-hand anchor stays in the open set
statement:
  If \(p\) lies in the open set, then the compact interval from \(p\) to its
  chosen right-hand anchor is contained in the open set.
proof:
  This is part of the chosen compact interval contained in the open set.
-/
theorem realOpenRightAnchor_uIcc_subset
    {Ω : Set ℝ} {hΩ_open : IsOpen Ω} {p : ℝ} (hp : p ∈ Ω) :
    Set.uIcc p (realOpenRightAnchor Ω hΩ_open p) ⊆ Ω := by
  classical
  have hchoose :=
    (Classical.choose_spec
      (realOpenSet_exists_right_uIcc_subset hΩ_open hp)).2
  simpa [realOpenRightAnchor, hp] using hchoose

/--
%%handwave
name:
  Component base points have right-hand anchors
statement:
  If \(x\) lies in an open real set, then the chosen base point of its
  order-connected component has a chosen right-hand anchor in the same open
  set.
proof:
  The base point lies in the open set, so the right-hand anchor construction
  applies to it.
-/
theorem realOpenOrdComponentBase_rightAnchor_uIcc_subset
    {Ω : Set ℝ} {hΩ_open : IsOpen Ω} {x : ℝ} (hx : x ∈ Ω) :
    Set.uIcc (realOpenOrdComponentBase Ω x)
        (realOpenRightAnchor Ω hΩ_open (realOpenOrdComponentBase Ω x)) ⊆ Ω := by
  exact realOpenRightAnchor_uIcc_subset
    (realOpenOrdComponentBase_mem (Ω := Ω) hx)

/--
%%handwave
name:
  The right-hand anchor has the same component base point
statement:
  The right-hand anchor of a point in the open set lies in the same
  order-connected component as that point.
proof:
  The compact interval from the point to its anchor is contained in the open
  set, so both endpoints have the same chosen component base point.
-/
theorem realOpenRightAnchor_base_eq
    {Ω : Set ℝ} {hΩ_open : IsOpen Ω} {p : ℝ} (hp : p ∈ Ω) :
    realOpenOrdComponentBase Ω (realOpenRightAnchor Ω hΩ_open p) =
      realOpenOrdComponentBase Ω p := by
  have hqΩ : realOpenRightAnchor Ω hΩ_open p ∈ Ω :=
    (realOpenRightAnchor_uIcc_subset (Ω := Ω) (hΩ_open := hΩ_open) hp)
      Set.right_mem_uIcc
  exact realOpenOrdComponentBase_eq_of_uIcc_subset hqΩ hp
    (by
      simpa [Set.uIcc_comm] using
        realOpenRightAnchor_uIcc_subset (Ω := Ω) (hΩ_open := hΩ_open) hp)

/--
%%handwave
name:
  The interval and the component anchor lie in one compact subinterval of the
  open set
statement:
  If a compact interval is contained in the open set, and \(p\) is the chosen
  base point of its component with right-hand anchor \(q\), then the compact
  interval spanning \(a,b,p,q\) is still contained in the open set.
proof:
  The four points \(a,b,p,q\) all lie in the same order-connected component.
  Since an order-connected component is an interval, the interval between the
  leftmost and rightmost of these points remains inside the component, hence
  inside the open set.
-/
theorem realOpenOrdComponentBase_anchor_hull_subset
    {Ω : Set ℝ} {hΩ_open : IsOpen Ω} {a b : ℝ}
    (habΩ : Set.uIcc a b ⊆ Ω) :
    Set.uIcc
        (min (min a b) (realOpenOrdComponentBase Ω a))
        (max (max a b)
          (realOpenRightAnchor Ω hΩ_open (realOpenOrdComponentBase Ω a))) ⊆ Ω := by
  classical
  let p := realOpenOrdComponentBase Ω a
  let q := realOpenRightAnchor Ω hΩ_open p
  have haΩ : a ∈ Ω := habΩ Set.left_mem_uIcc
  have hbΩ : b ∈ Ω := habΩ Set.right_mem_uIcc
  have hpΩ : p ∈ Ω := by
    dsimp [p]
    exact realOpenOrdComponentBase_mem (Ω := Ω) haΩ
  have hqΩ : q ∈ Ω := by
    dsimp [q]
    exact (realOpenRightAnchor_uIcc_subset (Ω := Ω)
      (hΩ_open := hΩ_open) hpΩ) Set.right_mem_uIcc
  have hpqΩ : Set.uIcc p q ⊆ Ω := by
    dsimp [q]
    exact realOpenRightAnchor_uIcc_subset (Ω := Ω)
      (hΩ_open := hΩ_open) hpΩ
  have ha_comp : a ∈ Set.ordConnectedComponent Ω p := by
    dsimp [p]
    exact realOpenOrdComponentBase_uIcc_subset (Ω := Ω) haΩ
  have hb_comp : b ∈ Set.ordConnectedComponent Ω p := by
    have hbase_b : realOpenOrdComponentBase Ω b = p := by
      dsimp [p]
      exact realOpenOrdComponentBase_eq_on_uIcc habΩ Set.right_mem_uIcc
    have hbase_p : realOpenOrdComponentBase Ω p = p := by
      dsimp [p]
      exact realOpenOrdComponentBase_idem (Ω := Ω) haΩ
    have hbase_pb : realOpenOrdComponentBase Ω p = realOpenOrdComponentBase Ω b := by
      rw [hbase_p, hbase_b]
    exact realOpenOrdComponentBase_uIcc_subset_of_eq_base hpΩ hbΩ
      hbase_pb
  have hp_comp : p ∈ Set.ordConnectedComponent Ω p := by
    exact Set.self_mem_ordConnectedComponent.2 hpΩ
  have hq_comp : q ∈ Set.ordConnectedComponent Ω p := by
    exact hpqΩ
  have hmin_mem :
      min (min a b) p ∈ Set.ordConnectedComponent Ω p := by
    by_cases hab : a ≤ b
    · have hminab : min a b = a := min_eq_left hab
      by_cases hap : a ≤ p
      · simp [hminab, min_eq_left hap, ha_comp]
      · have hpa : p ≤ a := le_of_not_ge hap
        simp [hminab, min_eq_right hpa, hp_comp]
    · have hba : b ≤ a := le_of_not_ge hab
      have hminab : min a b = b := min_eq_right hba
      by_cases hbp : b ≤ p
      · simp [hminab, min_eq_left hbp, hb_comp]
      · have hpb : p ≤ b := le_of_not_ge hbp
        simp [hminab, min_eq_right hpb, hp_comp]
  have hmax_mem :
      max (max a b) q ∈ Set.ordConnectedComponent Ω p := by
    by_cases hab : a ≤ b
    · have hmaxab : max a b = b := max_eq_right hab
      by_cases hbq : b ≤ q
      · simp [hmaxab, max_eq_right hbq, hq_comp]
      · have hqb : q ≤ b := le_of_not_ge hbq
        simp [hmaxab, max_eq_left hqb, hb_comp]
    · have hba : b ≤ a := le_of_not_ge hab
      have hmaxab : max a b = a := max_eq_left hba
      by_cases haq : a ≤ q
      · simp [hmaxab, max_eq_right haq, hq_comp]
      · have hqa : q ≤ a := le_of_not_ge haq
        simp [hmaxab, max_eq_left hqa, ha_comp]
  have hp_min :
      p ∈ Set.ordConnectedComponent Ω (min (min a b) p) :=
    Set.mem_ordConnectedComponent_comm.1 hmin_mem
  have hmax_min :
      max (max a b) q ∈
        Set.ordConnectedComponent Ω (min (min a b) p) :=
    Set.mem_ordConnectedComponent_trans hp_min hmax_mem
  exact hmax_min

/--
%%handwave
name:
  Componentwise primitive constants
statement:
  For each chosen base point of an order component of an open real set, choose
  the additive constant of the primitive representative on a fixed
  nondegenerate anchor interval in that component.
-/
noncomputable def realOpenComponentPrimitiveConstant
    (Ω : Set ℝ) (hΩ_open : IsOpen Ω) (u g : ℝ → ℝ)
    (hprimitive :
      ∀ a b : ℝ, Set.uIcc a b ⊆ Ω →
        ∃ C : ℝ,
          u =ᵐ[MeasureTheory.volume.restrict (Set.uIcc a b)]
            fun x : ℝ ↦ C + ∫ t in a..x, g t)
    (p : ℝ) : ℝ :=
  by
    classical
    exact
      if hp : p ∈ Ω then
        Classical.choose
          (hprimitive p (realOpenRightAnchor Ω hΩ_open p)
            (realOpenRightAnchor_uIcc_subset (Ω := Ω)
              (hΩ_open := hΩ_open) hp))
      else 0

/--
%%handwave
name:
  The chosen component constant represents the function on its anchor interval
statement:
  On the fixed anchor interval of a component base point, the componentwise
  primitive constant gives a primitive representative of the original
  function almost everywhere.
proof:
  This is the defining choice of the componentwise primitive constant.
-/
theorem realOpenComponentPrimitiveConstant_ae_eq_on_anchor
    {Ω : Set ℝ} {hΩ_open : IsOpen Ω} {u g : ℝ → ℝ}
    {hprimitive :
      ∀ a b : ℝ, Set.uIcc a b ⊆ Ω →
        ∃ C : ℝ,
          u =ᵐ[MeasureTheory.volume.restrict (Set.uIcc a b)]
            fun x : ℝ ↦ C + ∫ t in a..x, g t}
    {p : ℝ} (hp : p ∈ Ω) :
    u =ᵐ[MeasureTheory.volume.restrict
        (Set.uIcc p (realOpenRightAnchor Ω hΩ_open p))]
      fun x : ℝ ↦
        realOpenComponentPrimitiveConstant Ω hΩ_open u g hprimitive p +
          ∫ t in p..x, g t := by
  classical
  have hchosen :=
    Classical.choose_spec
      (hprimitive p (realOpenRightAnchor Ω hΩ_open p)
        (realOpenRightAnchor_uIcc_subset (Ω := Ω)
          (hΩ_open := hΩ_open) hp))
  simpa [realOpenComponentPrimitiveConstant, hp] using hchosen

/--
%%handwave
name:
  Candidate glued primitive representative
statement:
  The candidate representative on an open real set is obtained by using, in
  each order component, the primitive based at the chosen component base point
  with the componentwise primitive constant.  Outside the open set, it is
  defined to be the original function.
-/
noncomputable def realWeakSobolevGluedPrimitiveRepresentative
    (Ω : Set ℝ) (hΩ_open : IsOpen Ω) (u g : ℝ → ℝ)
    (hprimitive :
      ∀ a b : ℝ, Set.uIcc a b ⊆ Ω →
        ∃ C : ℝ,
          u =ᵐ[MeasureTheory.volume.restrict (Set.uIcc a b)]
            fun x : ℝ ↦ C + ∫ t in a..x, g t) :
    ℝ → ℝ :=
  by
    classical
    exact fun x : ℝ ↦
      if hx : x ∈ Ω then
        let p := realOpenOrdComponentBase Ω x
        realOpenComponentPrimitiveConstant Ω hΩ_open u g hprimitive p +
          ∫ t in p..x, g t
      else
        u x

/--
%%handwave
name:
  Formula for the glued primitive representative inside the open set
statement:
  At every point of the open set, the candidate glued representative is the
  componentwise primitive based at the chosen base point of that component.
proof:
  Choose the ordered connected component containing the point and unfold the glued definition.  Membership selects that component, giving its fixed base constant plus the integral of the weak derivative from the component base point.
-/
theorem realWeakSobolevGluedPrimitiveRepresentative_apply_of_mem
    {Ω : Set ℝ} {hΩ_open : IsOpen Ω} {u g : ℝ → ℝ}
    {hprimitive :
      ∀ a b : ℝ, Set.uIcc a b ⊆ Ω →
        ∃ C : ℝ,
          u =ᵐ[MeasureTheory.volume.restrict (Set.uIcc a b)]
            fun x : ℝ ↦ C + ∫ t in a..x, g t}
    {x : ℝ} (hx : x ∈ Ω) :
    realWeakSobolevGluedPrimitiveRepresentative Ω hΩ_open u g hprimitive x =
      let p := realOpenOrdComponentBase Ω x
      realOpenComponentPrimitiveConstant Ω hΩ_open u g hprimitive p +
        ∫ t in p..x, g t := by
  simp [realWeakSobolevGluedPrimitiveRepresentative, hx]

/--
%%handwave
name:
  The glued representative has the chosen primitive formula on anchor intervals
statement:
  Let \(p\) be the chosen base point of the order component of \(x\).  On the
  fixed anchor interval from \(p\) to its right-hand anchor, the candidate
  glued representative is pointwise equal to the primitive formula with the
  componentwise constant based at \(p\).
proof:
  Every point of the anchor interval lies in the same order-connected
  component as \(p\), so its chosen base point is again \(p\).  Substitute
  this into the definition of the candidate representative.
-/
theorem realWeakSobolevGluedPrimitiveRepresentative_eq_on_base_anchor
    {Ω : Set ℝ} {hΩ_open : IsOpen Ω} {u g : ℝ → ℝ}
    {hprimitive :
      ∀ a b : ℝ, Set.uIcc a b ⊆ Ω →
        ∃ C : ℝ,
          u =ᵐ[MeasureTheory.volume.restrict (Set.uIcc a b)]
            fun x : ℝ ↦ C + ∫ t in a..x, g t}
    {x y : ℝ} (hx : x ∈ Ω)
    (hy : y ∈ Set.uIcc (realOpenOrdComponentBase Ω x)
        (realOpenRightAnchor Ω hΩ_open (realOpenOrdComponentBase Ω x))) :
    realWeakSobolevGluedPrimitiveRepresentative Ω hΩ_open u g hprimitive y =
      realOpenComponentPrimitiveConstant Ω hΩ_open u g hprimitive
          (realOpenOrdComponentBase Ω x) +
        ∫ t in realOpenOrdComponentBase Ω x..y, g t := by
  classical
  let p := realOpenOrdComponentBase Ω x
  have hpΩ : p ∈ Ω := by
    dsimp [p]
    exact realOpenOrdComponentBase_mem (Ω := Ω) hx
  have hanchor_subset :
      Set.uIcc p (realOpenRightAnchor Ω hΩ_open p) ⊆ Ω := by
    dsimp [p]
    exact realOpenOrdComponentBase_rightAnchor_uIcc_subset
      (Ω := Ω) (hΩ_open := hΩ_open) hx
  have hyΩ : y ∈ Ω := hanchor_subset (by simpa [p] using hy)
  have hyp_subset : Set.uIcc y p ⊆ Ω := by
    have hsub :
        Set.uIcc y p ⊆
          Set.uIcc p (realOpenRightAnchor Ω hΩ_open p) :=
      Set.uIcc_subset_uIcc (by simpa [p] using hy) Set.left_mem_uIcc
    exact hsub.trans hanchor_subset
  have hbase_y : realOpenOrdComponentBase Ω y = p := by
    have hbase :
        realOpenOrdComponentBase Ω y =
          realOpenOrdComponentBase Ω p :=
      realOpenOrdComponentBase_eq_of_uIcc_subset hyΩ hpΩ hyp_subset
    have hbase_p : realOpenOrdComponentBase Ω p = p := by
      dsimp [p]
      exact realOpenOrdComponentBase_idem (Ω := Ω) hx
    exact hbase.trans hbase_p
  rw [realWeakSobolevGluedPrimitiveRepresentative_apply_of_mem
    (Ω := Ω) (hΩ_open := hΩ_open) (u := u) (g := g)
    (hprimitive := hprimitive) hyΩ]
  simp [p, hbase_y]

/--
%%handwave
name:
  On any compact interval in the open set, the glued representative is a
  primitive
statement:
  Let \([a,b]\) be contained in the open region and let \(p\) be the chosen
  base point of its order component.  On \([a,b]\), the candidate glued
  representative is pointwise equal to a primitive based at \(a\), with the
  additive constant obtained by transporting the componentwise constant from
  \(p\) to \(a\).
proof:
  All points of \([a,b]\) have the same chosen component base point.  Therefore
  the glued representative has the form \(C_p+\int_p^y g\).  Additivity of
  interval integrals rewrites this as
  \(C_p+\int_p^a g+\int_a^y g\).
-/
theorem realWeakSobolevGluedPrimitiveRepresentative_eq_primitive_on_uIcc
    {Ω : Set ℝ} {hΩ_open : IsOpen Ω} {u g : ℝ → ℝ}
    (hg_interval :
      ∀ a b : ℝ, Set.uIcc a b ⊆ Ω →
        IntervalIntegrable g MeasureTheory.volume a b)
    {hprimitive :
      ∀ a b : ℝ, Set.uIcc a b ⊆ Ω →
        ∃ C : ℝ,
          u =ᵐ[MeasureTheory.volume.restrict (Set.uIcc a b)]
            fun x : ℝ ↦ C + ∫ t in a..x, g t}
    {a b y : ℝ} (habΩ : Set.uIcc a b ⊆ Ω) (hy : y ∈ Set.uIcc a b) :
    realWeakSobolevGluedPrimitiveRepresentative Ω hΩ_open u g hprimitive y =
      (realOpenComponentPrimitiveConstant Ω hΩ_open u g hprimitive
          (realOpenOrdComponentBase Ω a) +
        ∫ t in realOpenOrdComponentBase Ω a..a, g t) +
        ∫ t in a..y, g t := by
  classical
  let p := realOpenOrdComponentBase Ω a
  have haΩ : a ∈ Ω := habΩ Set.left_mem_uIcc
  have hyΩ : y ∈ Ω := habΩ hy
  have hbase_y : realOpenOrdComponentBase Ω y = p := by
    dsimp [p]
    exact realOpenOrdComponentBase_eq_on_uIcc habΩ hy
  have hpaΩ : Set.uIcc p a ⊆ Ω := by
    dsimp [p]
    exact realOpenOrdComponentBase_uIcc_subset (Ω := Ω) haΩ
  have hayΩ : Set.uIcc a y ⊆ Ω := by
    exact (Set.uIcc_subset_uIcc Set.left_mem_uIcc hy).trans habΩ
  have hpa_int : IntervalIntegrable g MeasureTheory.volume p a :=
    hg_interval p a hpaΩ
  have hay_int : IntervalIntegrable g MeasureTheory.volume a y :=
    hg_interval a y hayΩ
  have hint :
      (∫ t in p..a, g t) + ∫ t in a..y, g t =
        ∫ t in p..y, g t :=
    intervalIntegral.integral_add_adjacent_intervals hpa_int hay_int
  rw [realWeakSobolevGluedPrimitiveRepresentative_apply_of_mem
    (Ω := Ω) (hΩ_open := hΩ_open) (u := u) (g := g)
    (hprimitive := hprimitive) hyΩ]
  dsimp only
  rw [hbase_y]
  dsimp [p] at hint ⊢
  rw [← hint]
  ring

/--
%%handwave
name:
  The glued primitive representative is absolutely continuous on compact
  intervals
statement:
  On every compact interval contained in the open region, the candidate glued
  representative is absolutely continuous.
proof:
  On the interval the candidate is pointwise equal to a primitive of the
  locally integrable derivative.  Primitives of integrable functions are
  absolutely continuous, and absolute continuity only depends on the values
  on the interval.
-/
theorem realWeakSobolevGluedPrimitiveRepresentative_absolutelyContinuousOnInterval
    {Ω : Set ℝ} {hΩ_open : IsOpen Ω} {u g : ℝ → ℝ}
    (hg_interval :
      ∀ a b : ℝ, Set.uIcc a b ⊆ Ω →
        IntervalIntegrable g MeasureTheory.volume a b)
    {hprimitive :
      ∀ a b : ℝ, Set.uIcc a b ⊆ Ω →
        ∃ C : ℝ,
          u =ᵐ[MeasureTheory.volume.restrict (Set.uIcc a b)]
            fun x : ℝ ↦ C + ∫ t in a..x, g t}
    {a b : ℝ} (habΩ : Set.uIcc a b ⊆ Ω) :
    AbsolutelyContinuousOnInterval
      (realWeakSobolevGluedPrimitiveRepresentative Ω hΩ_open u g hprimitive) a b := by
  let C : ℝ :=
    realOpenComponentPrimitiveConstant Ω hΩ_open u g hprimitive
      (realOpenOrdComponentBase Ω a) +
      ∫ t in realOpenOrdComponentBase Ω a..a, g t
  let F : ℝ → ℝ := fun y ↦ C + ∫ t in a..y, g t
  have hF_ac : AbsolutelyContinuousOnInterval F a b := by
    simpa [F, C] using
      (realPrimitive_add_const_acl_on_interval
        (hg_interval a b habΩ)).1
  refine absolutelyContinuousOnInterval_congr_on_uIcc hF_ac ?_
  intro y hy
  dsimp [F, C]
  exact (realWeakSobolevGluedPrimitiveRepresentative_eq_primitive_on_uIcc
    (Ω := Ω) (hΩ_open := hΩ_open) (u := u) (g := g)
    hg_interval (hprimitive := hprimitive) habΩ hy).symm

/--
%%handwave
name:
  The glued primitive representative agrees almost everywhere on compact
  intervals
statement:
  On every compact interval contained in the open region, the candidate
  glued representative agrees almost everywhere with the original function.
proof:
  Enlarge the interval to include the component base point and its
  right-hand anchor.  The primitive chosen on the enlarged interval agrees
  with the component anchor primitive on the nonempty open anchor overlap, so
  the additive constants agree.  Restricting the enlarged-interval
  almost-everywhere identity gives the desired equality on the original
  interval.
-/
theorem realWeakSobolevGluedPrimitiveRepresentative_ae_eq_on_uIcc
    {Ω : Set ℝ} {hΩ_open : IsOpen Ω} {u g : ℝ → ℝ}
    (hg_interval :
      ∀ a b : ℝ, Set.uIcc a b ⊆ Ω →
        IntervalIntegrable g MeasureTheory.volume a b)
    {hprimitive :
      ∀ a b : ℝ, Set.uIcc a b ⊆ Ω →
        ∃ C : ℝ,
          u =ᵐ[MeasureTheory.volume.restrict (Set.uIcc a b)]
            fun x : ℝ ↦ C + ∫ t in a..x, g t}
    {a b : ℝ} (habΩ : Set.uIcc a b ⊆ Ω) :
    realWeakSobolevGluedPrimitiveRepresentative Ω hΩ_open u g hprimitive
      =ᵐ[MeasureTheory.volume.restrict (Set.uIcc a b)] u := by
  classical
  let p := realOpenOrdComponentBase Ω a
  let q := realOpenRightAnchor Ω hΩ_open p
  let l := min (min a b) p
  let r := max (max a b) q
  have haΩ : a ∈ Ω := habΩ Set.left_mem_uIcc
  have hpΩ : p ∈ Ω := by
    dsimp [p]
    exact realOpenOrdComponentBase_mem (Ω := Ω) haΩ
  have hpq_lt : p < q := by
    dsimp [q]
    exact realOpenRightAnchor_gt (Ω := Ω) (hΩ_open := hΩ_open) hpΩ
  have hpq_le : p ≤ q := hpq_lt.le
  have hanchorΩ : Set.uIcc p q ⊆ Ω := by
    dsimp [q]
    exact realOpenRightAnchor_uIcc_subset (Ω := Ω)
      (hΩ_open := hΩ_open) hpΩ
  have hbigΩ : Set.uIcc l r ⊆ Ω := by
    dsimp [l, r, p, q]
    exact realOpenOrdComponentBase_anchor_hull_subset
      (Ω := Ω) (hΩ_open := hΩ_open) habΩ
  have hlp : l ≤ p := by
    dsimp [l]
    exact min_le_right (min a b) p
  have hpr : p ≤ r := by
    dsimp [r, q]
    exact hpq_le.trans (le_max_right (max a b) q)
  have hp_big : p ∈ Set.uIcc l r :=
    Set.mem_uIcc_of_le hlp hpr
  have hq_big : q ∈ Set.uIcc l r := by
    have hlq : l ≤ q := hlp.trans hpq_le
    have hqr : q ≤ r := by
      dsimp [r]
      exact le_max_right (max a b) q
    exact Set.mem_uIcc_of_le hlq hqr
  have ha_big : a ∈ Set.uIcc l r := by
    have hla : l ≤ a := by
      dsimp [l]
      exact (min_le_left (min a b) p).trans (min_le_left a b)
    have har : a ≤ r := by
      dsimp [r]
      exact (le_max_left a b).trans (le_max_left (max a b) q)
    exact Set.mem_uIcc_of_le hla har
  have hb_big : b ∈ Set.uIcc l r := by
    have hlb : l ≤ b := by
      dsimp [l]
      exact (min_le_left (min a b) p).trans (min_le_right a b)
    have hbr : b ≤ r := by
      dsimp [r]
      exact (le_max_right a b).trans (le_max_left (max a b) q)
    exact Set.mem_uIcc_of_le hlb hbr
  have hab_big : Set.uIcc a b ⊆ Set.uIcc l r :=
    Set.uIcc_subset_uIcc ha_big hb_big
  have hpq_big : Set.uIcc p q ⊆ Set.uIcc l r :=
    Set.uIcc_subset_uIcc hp_big hq_big
  have hlΩ : l ∈ Ω := hbigΩ Set.left_mem_uIcc
  have hbase_l : realOpenOrdComponentBase Ω l = p := by
    have hlpΩ : Set.uIcc l p ⊆ Ω :=
      (Set.uIcc_subset_uIcc Set.left_mem_uIcc hp_big).trans hbigΩ
    have hbase :
        realOpenOrdComponentBase Ω l =
          realOpenOrdComponentBase Ω p :=
      realOpenOrdComponentBase_eq_of_uIcc_subset hlΩ hpΩ hlpΩ
    have hbase_p : realOpenOrdComponentBase Ω p = p := by
      dsimp [p]
      exact realOpenOrdComponentBase_idem (Ω := Ω) haΩ
    exact hbase.trans hbase_p
  rcases hprimitive l r hbigΩ with ⟨Cbig, hbig_ae⟩
  have hanchor_ae :
      u =ᵐ[MeasureTheory.volume.restrict (Set.uIcc p q)]
        fun x : ℝ ↦
          realOpenComponentPrimitiveConstant Ω hΩ_open u g hprimitive p +
            ∫ t in p..x, g t := by
    dsimp [q]
    exact realOpenComponentPrimitiveConstant_ae_eq_on_anchor
      (Ω := Ω) (hΩ_open := hΩ_open) (u := u) (g := g)
      (hprimitive := hprimitive) hpΩ
  have hIanchor : Set.Ioo p q ⊆ Set.uIcc p q := by
    intro x hx
    exact Set.Icc_subset_uIcc (Set.Ioo_subset_Icc_self hx)
  have hIbig : Set.Ioo p q ⊆ Set.uIcc l r :=
    hIanchor.trans hpq_big
  have hagree :
      Set.EqOn
        (fun x : ℝ ↦
          realOpenComponentPrimitiveConstant Ω hΩ_open u g hprimitive p +
            ∫ t in p..x, g t)
        (fun x : ℝ ↦ Cbig + ∫ t in l..x, g t) (Set.Ioo p q) :=
    realPrimitive_representatives_agree_on_Ioo_overlap
      (Ω := Ω) (u := u) (g := g)
      hg_interval hanchorΩ hbigΩ hIanchor hIbig hanchor_ae hbig_ae
  let m : ℝ := (p + q) / 2
  have hmI : m ∈ Set.Ioo p q := by
    constructor <;> dsimp [m] <;> linarith
  have hm_big : m ∈ Set.uIcc l r := hIbig hmI
  have hplΩ : Set.uIcc p l ⊆ Ω := by
    exact (Set.uIcc_subset_uIcc hp_big Set.left_mem_uIcc).trans hbigΩ
  have hlmΩ : Set.uIcc l m ⊆ Ω := by
    exact (Set.uIcc_subset_uIcc Set.left_mem_uIcc hm_big).trans hbigΩ
  have hpl_int : IntervalIntegrable g MeasureTheory.volume p l :=
    hg_interval p l hplΩ
  have hlm_int : IntervalIntegrable g MeasureTheory.volume l m :=
    hg_interval l m hlmΩ
  have hint_plm :
      (∫ t in p..l, g t) + ∫ t in l..m, g t =
        ∫ t in p..m, g t :=
    intervalIntegral.integral_add_adjacent_intervals hpl_int hlm_int
  have hD_eq :
      realOpenComponentPrimitiveConstant Ω hΩ_open u g hprimitive p +
          ∫ t in p..l, g t =
        Cbig := by
    have hm_eq := hagree hmI
    have hmain :
        (realOpenComponentPrimitiveConstant Ω hΩ_open u g hprimitive p +
            ∫ t in p..l, g t) +
            ∫ t in l..m, g t =
          Cbig + ∫ t in l..m, g t := by
      calc
        (realOpenComponentPrimitiveConstant Ω hΩ_open u g hprimitive p +
            ∫ t in p..l, g t) +
            ∫ t in l..m, g t
            =
          realOpenComponentPrimitiveConstant Ω hΩ_open u g hprimitive p +
            ∫ t in p..m, g t := by
              rw [← hint_plm]
              ring
        _ = Cbig + ∫ t in l..m, g t := hm_eq
    linarith
  have hglued_big :
      realWeakSobolevGluedPrimitiveRepresentative Ω hΩ_open u g hprimitive
        =ᵐ[MeasureTheory.volume.restrict (Set.uIcc a b)]
          fun y : ℝ ↦ Cbig + ∫ t in l..y, g t := by
    refine ae_restrict_of_forall_mem measurableSet_uIcc ?_
    intro y hy
    have hy_big : y ∈ Set.uIcc l r := hab_big hy
    have hformula :=
      realWeakSobolevGluedPrimitiveRepresentative_eq_primitive_on_uIcc
        (Ω := Ω) (hΩ_open := hΩ_open) (u := u) (g := g)
        hg_interval (hprimitive := hprimitive) hbigΩ hy_big
    dsimp [l, p] at hformula hbase_l hD_eq ⊢
    rw [hformula, hbase_l, hD_eq]
  have hbig_on_ab :
      u =ᵐ[MeasureTheory.volume.restrict (Set.uIcc a b)]
      fun y : ℝ ↦ Cbig + ∫ t in l..y, g t :=
    ae_restrict_of_ae_restrict_of_subset hab_big hbig_ae
  exact hglued_big.trans hbig_on_ab.symm

/--
%%handwave
name:
  The glued primitive representative agrees almost everywhere on the open
  region
statement:
  The candidate glued representative agrees almost everywhere with the
  original function on the whole open real region.
proof:
  Around every point choose a small compact interval contained in the open
  set.  Since the real line is second countable, a countable subfamily of the
  corresponding open interiors covers the region.  The interval
  almost-everywhere agreement holds on each member of this countable cover,
  hence on their union.
-/
theorem realWeakSobolevGluedPrimitiveRepresentative_ae_eq_on_open
    {Ω : Set ℝ} {hΩ_open : IsOpen Ω} {u g : ℝ → ℝ}
    (hg_interval :
      ∀ a b : ℝ, Set.uIcc a b ⊆ Ω →
        IntervalIntegrable g MeasureTheory.volume a b)
    {hprimitive :
      ∀ a b : ℝ, Set.uIcc a b ⊆ Ω →
        ∃ C : ℝ,
          u =ᵐ[MeasureTheory.volume.restrict (Set.uIcc a b)]
            fun x : ℝ ↦ C + ∫ t in a..x, g t} :
    realWeakSobolevGluedPrimitiveRepresentative Ω hΩ_open u g hprimitive
      =ᵐ[MeasureTheory.volume.restrict Ω] u := by
  classical
  let radius : ℝ → ℝ := fun x ↦
    if hx : x ∈ Ω then
      Classical.choose (Metric.isOpen_iff.mp hΩ_open x hx)
    else 1
  let U : ℝ → Set ℝ := fun x ↦
    Set.Ioo (x - radius x / 2) (x + radius x / 2)
  have hradius_pos : ∀ x ∈ Ω, 0 < radius x := by
    intro x hx
    have hchoose :=
      (Classical.choose_spec (Metric.isOpen_iff.mp hΩ_open x hx)).1
    simpa [radius, hx] using hchoose
  have hball_subset : ∀ x ∈ Ω, Metric.ball x (radius x) ⊆ Ω := by
    intro x hx
    have hchoose :=
      (Classical.choose_spec (Metric.isOpen_iff.mp hΩ_open x hx)).2
    simpa [radius, hx] using hchoose
  have hU_uIcc_subset : ∀ x ∈ Ω,
      U x ⊆ Set.uIcc (x - radius x / 2) (x + radius x / 2) := by
    intro x hx y hy
    have hle : x - radius x / 2 ≤ x + radius x / 2 := by
      linarith [hradius_pos x hx]
    exact Set.Icc_subset_uIcc (Set.Ioo_subset_Icc_self hy)
  have huIcc_subsetΩ : ∀ x ∈ Ω,
      Set.uIcc (x - radius x / 2) (x + radius x / 2) ⊆ Ω := by
    intro x hx y hy
    have hle : x - radius x / 2 ≤ x + radius x / 2 := by
      linarith [hradius_pos x hx]
    have hyIcc : y ∈ Set.Icc (x - radius x / 2) (x + radius x / 2) := by
      simpa [Set.uIcc_of_le hle] using hy
    have hdist : dist y x < radius x := by
      rw [Real.dist_eq]
      have hleft : x - radius x / 2 ≤ y := hyIcc.1
      have hright : y ≤ x + radius x / 2 := hyIcc.2
      have habs : |y - x| ≤ radius x / 2 := by
        rw [abs_le]
        constructor <;> linarith
      linarith [hradius_pos x hx]
    exact hball_subset x hx hdist
  have hU_subsetΩ : ∀ x ∈ Ω, U x ⊆ Ω := by
    intro x hx
    exact (hU_uIcc_subset x hx).trans (huIcc_subsetΩ x hx)
  have hnhds : ∀ x ∈ Ω, U x ∈ 𝓝[Ω] x := by
    intro x hx
    have hxU : x ∈ U x := by
      have hpos := hradius_pos x hx
      dsimp [U]
      constructor <;> linarith
    exact mem_nhdsWithin_of_mem_nhds (isOpen_Ioo.mem_nhds hxU)
  rcases TopologicalSpace.countable_cover_nhdsWithin hnhds with
    ⟨t, htΩ, ht_count, hcover⟩
  have hΩ_union : Ω = ⋃ x ∈ t, U x := by
    refine subset_antisymm hcover ?_
    intro y hy
    rcases Set.mem_iUnion.1 hy with ⟨x, hxmem⟩
    rcases Set.mem_iUnion.1 hxmem with ⟨hxt, hyU⟩
    exact hU_subsetΩ x (htΩ hxt) hyU
  have hcover_ae :
      ∀ᵐ y ∂MeasureTheory.volume.restrict (⋃ x ∈ t, U x),
        realWeakSobolevGluedPrimitiveRepresentative Ω hΩ_open u g hprimitive y =
          u y :=
    (MeasureTheory.ae_restrict_biUnion_iff
      (μ := MeasureTheory.volume) U ht_count
      (fun y : ℝ ↦
        realWeakSobolevGluedPrimitiveRepresentative Ω hΩ_open u g hprimitive y =
          u y)).2 (by
      intro x hxt
      have hxΩ : x ∈ Ω := htΩ hxt
      exact ae_restrict_of_ae_restrict_of_subset
        (hU_uIcc_subset x hxΩ)
        (realWeakSobolevGluedPrimitiveRepresentative_ae_eq_on_uIcc
          (Ω := Ω) (hΩ_open := hΩ_open) (u := u) (g := g)
          hg_interval (hprimitive := hprimitive)
          (huIcc_subsetΩ x hxΩ)))
  have hmeasure :
      MeasureTheory.volume.restrict Ω =
        MeasureTheory.volume.restrict (⋃ x ∈ t, U x) := by
    rw [hΩ_union]
  exact hmeasure ▸ hcover_ae

/--
%%handwave
name:
  The glued primitive representative has the prescribed derivative on open
  subintervals
statement:
  On every open interval whose compact closure is contained in the region,
  the candidate glued representative has derivative \(g\) almost everywhere.
proof:
  On the surrounding compact interval, the candidate is pointwise equal to a
  primitive of \(g\).  The primitive has derivative \(g\) almost everywhere,
  and on the open subinterval the pointwise equality holds in a whole
  neighborhood of each point.
-/
theorem realWeakSobolevGluedPrimitiveRepresentative_hasDerivAt_ae_on_Ioo
    {Ω : Set ℝ} {hΩ_open : IsOpen Ω} {u g : ℝ → ℝ}
    (hg_interval :
      ∀ a b : ℝ, Set.uIcc a b ⊆ Ω →
        IntervalIntegrable g MeasureTheory.volume a b)
    {hprimitive :
      ∀ a b : ℝ, Set.uIcc a b ⊆ Ω →
        ∃ C : ℝ,
          u =ᵐ[MeasureTheory.volume.restrict (Set.uIcc a b)]
            fun x : ℝ ↦ C + ∫ t in a..x, g t}
    {a b : ℝ} (habΩ : Set.uIcc a b ⊆ Ω) :
    ∀ᵐ x ∂MeasureTheory.volume.restrict (Set.Ioo a b),
      HasDerivAt
        (realWeakSobolevGluedPrimitiveRepresentative Ω hΩ_open u g hprimitive)
        (g x) x := by
  let C : ℝ :=
    realOpenComponentPrimitiveConstant Ω hΩ_open u g hprimitive
      (realOpenOrdComponentBase Ω a) +
      ∫ t in realOpenOrdComponentBase Ω a..a, g t
  let F : ℝ → ℝ := fun y ↦ C + ∫ t in a..y, g t
  have hEqOn :
      Set.EqOn
        (realWeakSobolevGluedPrimitiveRepresentative Ω hΩ_open u g hprimitive)
        F (Set.uIcc a b) := by
    intro y hy
    dsimp [F, C]
    exact realWeakSobolevGluedPrimitiveRepresentative_eq_primitive_on_uIcc
      (Ω := Ω) (hΩ_open := hΩ_open) (u := u) (g := g)
      hg_interval (hprimitive := hprimitive) habΩ hy
  have hF_deriv :
      ∀ᵐ x ∂(MeasureTheory.volume : Measure ℝ),
        x ∈ Set.uIcc a b → HasDerivAt F (g x) x := by
    simpa [F] using
      (realPrimitive_add_const_acl_on_interval
        (g := g) (a := a) (b := b) (C := C)
        (hg_interval a b habΩ)).2
  filter_upwards [ae_restrict_of_ae hF_deriv,
    ae_restrict_mem measurableSet_Ioo] with x hx_deriv hxIoo
  have hx_uIcc : x ∈ Set.uIcc a b :=
    Set.Icc_subset_uIcc (Set.Ioo_subset_Icc_self hxIoo)
  have hEq_nhds :
      realWeakSobolevGluedPrimitiveRepresentative Ω hΩ_open u g hprimitive
        =ᶠ[𝓝 x] F := by
    filter_upwards [((isOpen_Ioo : IsOpen (Set.Ioo a b)).mem_nhds hxIoo)] with y hy
    exact
      hEqOn (Set.Icc_subset_uIcc (Set.Ioo_subset_Icc_self hy))
  exact (hx_deriv hx_uIcc).congr_of_eventuallyEq hEq_nhds

/--
%%handwave
name:
  The glued primitive representative has the prescribed derivative almost
  everywhere on the open region
statement:
  The candidate glued representative has classical derivative \(g\) for
  almost every point of the open real region.
proof:
  Cover the open region by countably many open intervals whose compact
  closures remain inside the region.  The derivative statement holds almost
  everywhere on each member of the cover, hence on their union.
-/
theorem realWeakSobolevGluedPrimitiveRepresentative_hasDerivAt_ae_on_open
    {Ω : Set ℝ} {hΩ_open : IsOpen Ω} {u g : ℝ → ℝ}
    (hg_interval :
      ∀ a b : ℝ, Set.uIcc a b ⊆ Ω →
        IntervalIntegrable g MeasureTheory.volume a b)
    {hprimitive :
      ∀ a b : ℝ, Set.uIcc a b ⊆ Ω →
        ∃ C : ℝ,
          u =ᵐ[MeasureTheory.volume.restrict (Set.uIcc a b)]
            fun x : ℝ ↦ C + ∫ t in a..x, g t} :
    ∀ᵐ x ∂MeasureTheory.volume.restrict Ω,
      HasDerivAt
        (realWeakSobolevGluedPrimitiveRepresentative Ω hΩ_open u g hprimitive)
        (g x) x := by
  classical
  let radius : ℝ → ℝ := fun x ↦
    if hx : x ∈ Ω then
      Classical.choose (Metric.isOpen_iff.mp hΩ_open x hx)
    else 1
  let U : ℝ → Set ℝ := fun x ↦
    Set.Ioo (x - radius x / 2) (x + radius x / 2)
  have hradius_pos : ∀ x ∈ Ω, 0 < radius x := by
    intro x hx
    have hchoose :=
      (Classical.choose_spec (Metric.isOpen_iff.mp hΩ_open x hx)).1
    simpa [radius, hx] using hchoose
  have hball_subset : ∀ x ∈ Ω, Metric.ball x (radius x) ⊆ Ω := by
    intro x hx
    have hchoose :=
      (Classical.choose_spec (Metric.isOpen_iff.mp hΩ_open x hx)).2
    simpa [radius, hx] using hchoose
  have huIcc_subsetΩ : ∀ x ∈ Ω,
      Set.uIcc (x - radius x / 2) (x + radius x / 2) ⊆ Ω := by
    intro x hx y hy
    have hle : x - radius x / 2 ≤ x + radius x / 2 := by
      linarith [hradius_pos x hx]
    have hyIcc : y ∈ Set.Icc (x - radius x / 2) (x + radius x / 2) := by
      simpa [Set.uIcc_of_le hle] using hy
    have hdist : dist y x < radius x := by
      rw [Real.dist_eq]
      have hleft : x - radius x / 2 ≤ y := hyIcc.1
      have hright : y ≤ x + radius x / 2 := hyIcc.2
      have habs : |y - x| ≤ radius x / 2 := by
        rw [abs_le]
        constructor <;> linarith
      linarith [hradius_pos x hx]
    exact hball_subset x hx hdist
  have hU_subsetΩ : ∀ x ∈ Ω, U x ⊆ Ω := by
    intro x hx y hy
    exact huIcc_subsetΩ x hx
      (Set.Icc_subset_uIcc (Set.Ioo_subset_Icc_self hy))
  have hnhds : ∀ x ∈ Ω, U x ∈ 𝓝[Ω] x := by
    intro x hx
    have hxU : x ∈ U x := by
      have hpos := hradius_pos x hx
      dsimp [U]
      constructor <;> linarith
    exact mem_nhdsWithin_of_mem_nhds (isOpen_Ioo.mem_nhds hxU)
  rcases TopologicalSpace.countable_cover_nhdsWithin hnhds with
    ⟨t, htΩ, ht_count, hcover⟩
  have hΩ_union : Ω = ⋃ x ∈ t, U x := by
    refine subset_antisymm hcover ?_
    intro y hy
    rcases Set.mem_iUnion.1 hy with ⟨x, hxmem⟩
    rcases Set.mem_iUnion.1 hxmem with ⟨hxt, hyU⟩
    exact hU_subsetΩ x (htΩ hxt) hyU
  have hcover_ae :
      ∀ᵐ y ∂MeasureTheory.volume.restrict (⋃ x ∈ t, U x),
        HasDerivAt
          (realWeakSobolevGluedPrimitiveRepresentative Ω hΩ_open u g hprimitive)
          (g y) y :=
    (MeasureTheory.ae_restrict_biUnion_iff
      (μ := MeasureTheory.volume) U ht_count
      (fun y : ℝ ↦
        HasDerivAt
          (realWeakSobolevGluedPrimitiveRepresentative Ω hΩ_open u g hprimitive)
          (g y) y)).2 (by
      intro x hxt
      have hxΩ : x ∈ Ω := htΩ hxt
      exact realWeakSobolevGluedPrimitiveRepresentative_hasDerivAt_ae_on_Ioo
        (Ω := Ω) (hΩ_open := hΩ_open) (u := u) (g := g)
        hg_interval (hprimitive := hprimitive) (huIcc_subsetΩ x hxΩ))
  have hmeasure :
      MeasureTheory.volume.restrict Ω =
        MeasureTheory.volume.restrict (⋃ x ∈ t, U x) := by
    rw [hΩ_union]
  exact hmeasure ▸ hcover_ae

/--
%%handwave
name:
  Local primitive representatives glue on open real regions
statement:
  Suppose that on every compact interval contained in an open real region,
  a locally integrable function agrees almost everywhere with a primitive of
  \(g\), up to an additive constant.  Then these interval representatives
  glue to a single representative on the open region, absolutely continuous
  on every compact subinterval and with derivative \(g\) almost everywhere.
proof:
  On overlapping intervals the two primitives differ by constants and both
  agree almost everywhere with the original function, so the constants agree
  on each connected component.  Since open subsets of the real line are
  countable unions of intervals, the componentwise representatives assemble
  into one representative on the whole region.
-/
theorem realWeakSobolev_local_primitive_representatives_glue_on_open_region
    {Ω : Set ℝ} (hΩ_open : IsOpen Ω)
    {u g : ℝ → ℝ}
    (hg_interval :
      ∀ a b : ℝ, Set.uIcc a b ⊆ Ω →
        IntervalIntegrable g MeasureTheory.volume a b)
    (hprimitive :
      ∀ a b : ℝ, Set.uIcc a b ⊆ Ω →
        ∃ C : ℝ,
          u =ᵐ[MeasureTheory.volume.restrict (Set.uIcc a b)]
            fun x : ℝ ↦ C + ∫ t in a..x, g t) :
    ∃ uacl : ℝ → ℝ,
      uacl =ᵐ[MeasureTheory.volume.restrict Ω] u ∧
        (∀ a b : ℝ, Set.uIcc a b ⊆ Ω →
          AbsolutelyContinuousOnInterval uacl a b) ∧
        ∀ᵐ x ∂MeasureTheory.volume.restrict Ω,
          HasDerivAt uacl (g x) x := by
  let uacl : ℝ → ℝ :=
    realWeakSobolevGluedPrimitiveRepresentative Ω hΩ_open u g hprimitive
  refine ⟨uacl, ?_, ?_, ?_⟩
  · dsimp [uacl]
    exact realWeakSobolevGluedPrimitiveRepresentative_ae_eq_on_open
      (Ω := Ω) (hΩ_open := hΩ_open) (u := u) (g := g)
      hg_interval (hprimitive := hprimitive)
  · intro a b habΩ
    dsimp [uacl]
    exact
      realWeakSobolevGluedPrimitiveRepresentative_absolutelyContinuousOnInterval
        (Ω := Ω) (hΩ_open := hΩ_open) (u := u) (g := g)
        hg_interval (hprimitive := hprimitive) habΩ
  · dsimp [uacl]
    exact
      realWeakSobolevGluedPrimitiveRepresentative_hasDerivAt_ae_on_open
        (Ω := Ω) (hΩ_open := hΩ_open) (u := u) (g := g)
        hg_interval (hprimitive := hprimitive)

/--
%%handwave
name:
  One-dimensional weak Sobolev functions have absolutely continuous
  representatives on open regions
statement:
  If \(u\) has weak derivative \(g\) on an open subset of \(\mathbb R\), then
  there is a representative \(\tilde u\), equal to \(u\) almost everywhere in
  the region, such that \(\tilde u\) is absolutely continuous on every compact
  interval contained in the region and has classical derivative \(g\) almost
  everywhere in the region.
proof:
  The weak derivative identity says that the distributional derivative of
  \(u\) is \(g\).  On each compact interval, subtract the primitive of \(g\).
  The resulting distribution has derivative zero, hence is almost everywhere
  constant on the interval.  These local constants agree on overlaps, giving
  a representative on the open region.  The fundamental theorem for interval
  integrals and the Lebesgue differentiation theorem then give absolute
  continuity and the almost-everywhere classical derivative.
-/
theorem realWeakSobolev_exists_acl_representative_on_open_region
    {Ω : Set ℝ} (hΩ_open : IsOpen Ω)
    {u g : ℝ → ℝ}
    (hweak : IsWeakDerivativeOnRealRegionScalar Ω u g) :
    ∃ uacl : ℝ → ℝ,
      uacl =ᵐ[MeasureTheory.volume.restrict Ω] u ∧
        (∀ a b : ℝ, Set.uIcc a b ⊆ Ω →
          AbsolutelyContinuousOnInterval uacl a b) ∧
        ∀ᵐ x ∂MeasureTheory.volume.restrict Ω,
          HasDerivAt uacl (g x) x := by
  exact realWeakSobolev_local_primitive_representatives_glue_on_open_region
    hΩ_open
    (fun a b habΩ ↦
      realWeakSobolev_derivative_intervalIntegrable_on_uIcc
        hΩ_open hweak habΩ)
    (fun a b habΩ ↦
      realWeakSobolev_eq_primitive_add_const_ae_on_interval
        hΩ_open hweak habΩ)

/--
%%handwave
name:
  One-dimensional weak Sobolev functions have compact absolutely continuous
  representatives
statement:
  Let \(u\) have weak derivative \(g\) on an open subset of \(\mathbb R\).
  On every compact subset \(Q\) of the region on which \(u\) and \(g\) are
  square-integrable, there is a representative \(\tilde u\), equal to \(u\)
  almost everywhere on \(Q\), such that \(\tilde u\) is absolutely continuous
  on every interval contained in \(Q\) and has classical derivative \(g\)
  almost everywhere on \(Q\).
proof:
  On compact intervals, the distributional derivative identity implies that
  \(u\) differs from the primitive of \(g\) by a constant.  Since \(g\) is
  locally integrable, this primitive is absolutely continuous.  The local
  primitives agree up to constants on overlaps, giving a representative whose
  classical derivative is \(g\) almost everywhere.
-/
theorem realWeakSobolev_exists_acl_representative_on_compact
    {Q Ω : Set ℝ} (_hQ : IsCompact Q)
    (hQΩ : Q ⊆ Ω) (hΩ_open : IsOpen Ω)
    {u g : ℝ → ℝ}
    (hweak : IsWeakDerivativeOnRealRegionScalar Ω u g)
    (_hu : MemLp u 2 (MeasureTheory.volume.restrict Q))
    (_hg : MemLp g 2 (MeasureTheory.volume.restrict Q)) :
    ∃ uacl : ℝ → ℝ,
      uacl =ᵐ[MeasureTheory.volume.restrict Q] u ∧
        (∀ a b : ℝ, Set.uIcc a b ⊆ Q →
          AbsolutelyContinuousOnInterval uacl a b) ∧
        ∀ᵐ x ∂MeasureTheory.volume.restrict Q,
          HasDerivAt uacl (g x) x := by
  rcases realWeakSobolev_exists_acl_representative_on_open_region
      hΩ_open hweak with
    ⟨uacl, huacl_eq_region, huacl_ac_region, huacl_deriv_region⟩
  refine ⟨uacl, ?_, ?_, ?_⟩
  · exact ae_restrict_of_ae_restrict_of_subset hQΩ huacl_eq_region
  · intro a b hab
    exact huacl_ac_region a b (hab.trans hQΩ)
  · exact ae_restrict_of_ae_restrict_of_subset hQΩ huacl_deriv_region

/--
%%handwave
name:
  One-dimensional weak Sobolev functions have ACL representatives on almost
  every unit segment
statement:
  Let \(u\) have weak derivative \(g\) on an open subset of \(\mathbb R\).
  If \(u\) and \(g\) are square-integrable on a compact set \(Q\), and every
  unit segment starting from a compact set \(K\) remains in \(Q\), then there
  is a representative \(\tilde u\), equal to \(u\) almost everywhere on \(Q\),
  such that for almost every \(a\in K\), \(\tilde u\) is absolutely continuous
  on \([a,a+1]\) and has classical derivative \(g\) almost everywhere on that
  interval.
proof:
  The distributional derivative identity is localized to compact intervals.
  On each interval it implies that \(u\) differs from the primitive of \(g\)
  by a constant.  Since \(g\) is locally integrable, that primitive is
  absolutely continuous, and the derivative identity holds almost everywhere
  by the Lebesgue differentiation theorem.
-/
theorem realWeakSobolev_exists_acl_representative_with_derivative_on_segments
    {K Q Ω : Set ℝ} (hK : IsCompact K) (hQ : IsCompact Q)
    (hQΩ : Q ⊆ Ω) (hΩ_open : IsOpen Ω)
    {u g : ℝ → ℝ}
    (hweak : IsWeakDerivativeOnRealRegionScalar Ω u g)
    (hu : MemLp u 2 (MeasureTheory.volume.restrict Q))
    (hg : MemLp g 2 (MeasureTheory.volume.restrict Q))
    (hsegments :
      ∀ a ∈ K, ∀ t : ℝ, t ∈ Set.Icc 0 1 → a + t ∈ Q) :
    ∃ uacl : ℝ → ℝ,
      uacl =ᵐ[MeasureTheory.volume.restrict Q] u ∧
        ∀ᵐ a ∂MeasureTheory.volume.restrict K,
          AbsolutelyContinuousOnInterval uacl a (a + 1) ∧
            ∀ᵐ x ∂MeasureTheory.volume,
              x ∈ Set.uIcc a (a + 1) → HasDerivAt uacl (g x) x := by
  rcases realWeakSobolev_exists_acl_representative_on_compact
      hQ hQΩ hΩ_open hweak hu hg with
    ⟨uacl, huacl_eq, huacl_ac, huacl_deriv⟩
  refine ⟨uacl, huacl_eq, ?_⟩
  have hderiv_unrestricted :
      ∀ᵐ x ∂(MeasureTheory.volume : Measure ℝ),
        x ∈ Q → HasDerivAt uacl (g x) x :=
    ae_imp_of_ae_restrict huacl_deriv
  filter_upwards [ae_restrict_mem hK.measurableSet] with a haK
  have hsegment_subset : Set.uIcc a (a + 1) ⊆ Q := by
    intro x hx
    have hle : a ≤ a + 1 := by linarith
    have hxIcc : x ∈ Set.Icc a (a + 1) := by
      rwa [Set.uIcc_of_le hle] at hx
    let t : ℝ := x - a
    have ht : t ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · dsimp [t]
        linarith [hxIcc.1]
      · dsimp [t]
        linarith [hxIcc.2]
    have hx_eq : a + t = x := by
      dsimp [t]
      ring
    simpa [hx_eq] using hsegments a haK t ht
  constructor
  · exact huacl_ac a (a + 1) hsegment_subset
  · filter_upwards [hderiv_unrestricted] with x hxQ hxseg
    exact hxQ (hsegment_subset hxseg)

/--
%%handwave
name:
  One-dimensional weak Sobolev functions satisfy the endpoint fundamental theorem
statement:
  Let \(u\) have weak derivative \(g\) on an open subset of \(\mathbb R\).
  If \(u\) and \(g\) are square-integrable on a compact set \(Q\), and every
  unit segment starting from a compact set \(K\) remains in \(Q\), then
  \[
    u(a+1)-u(a)=\int_0^1 g(a+t)\,dt
  \]
  for almost every \(a\in K\).
proof:
  On compact intervals, the distributional identity implies that \(u\) agrees
  almost everywhere with an absolutely continuous function whose classical
  derivative is \(g\).  The fundamental theorem of calculus for absolutely
  continuous functions gives the identity for that representative; translation
  invariance transfers the two endpoint values back to the original
  representative for almost every starting point.
-/
theorem realWeakSobolev_endpointFTC_ae
    {K Q Ω : Set ℝ} (hK : IsCompact K) (hQ : IsCompact Q)
    (hQΩ : Q ⊆ Ω) (hΩ_open : IsOpen Ω)
    {u g : ℝ → ℝ}
    (hweak : IsWeakDerivativeOnRealRegionScalar Ω u g)
    (hu : MemLp u 2 (MeasureTheory.volume.restrict Q))
    (hg : MemLp g 2 (MeasureTheory.volume.restrict Q))
    (hsegments :
      ∀ a ∈ K, ∀ t : ℝ, t ∈ Set.Icc 0 1 → a + t ∈ Q) :
    ∀ᵐ a ∂MeasureTheory.volume.restrict K,
      u (a + 1) - u a =
        ∫ t in Set.Icc (0 : ℝ) 1, g (a + t) ∂MeasureTheory.volume := by
  rcases realWeakSobolev_exists_acl_representative_with_derivative_on_segments
      hK hQ hQΩ hΩ_open hweak hu hg hsegments with
    ⟨uacl, huacl_eq, huacl_segments⟩
  have hsegments_one :
      ∀ x ∈ K, ∀ t : ℝ, t ∈ Set.Icc 0 1 → x + t • (1 : ℝ) ∈ Q := by
    intro x hx t ht
    simpa [smul_eq_mul] using hsegments x hx t ht
  have hendpoints :
      (fun z : ℝ ↦ u (z + (1 : ℝ)) - u z)
        =ᵐ[MeasureTheory.volume.restrict K]
      fun z : ℝ ↦ uacl (z + (1 : ℝ)) - uacl z := by
    exact ae_eq_endpoint_difference_of_ae_eq_on_segments
      (H := ℝ) (K := K) (Q := Q) (u := u) (v := uacl)
      (h := (1 : ℝ)) huacl_eq hsegments_one
  filter_upwards [hendpoints, huacl_segments] with a ha_endpoint ha_acl
  rcases ha_acl with ⟨hacl, hderiv⟩
  have hderiv_integral :
      (∫ x in a..a + 1, deriv uacl x) =
        ∫ x in a..a + 1, g x := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hderiv] with x hxderiv hxmem
    exact (hxderiv (Set.uIoc_subset_uIcc hxmem)).deriv
  have hshift :
      (∫ t in (0 : ℝ)..1, g (a + t)) =
        ∫ x in a..a + 1, g x := by
    calc
      (∫ t in (0 : ℝ)..1, g (a + t))
          = ∫ t in (0 : ℝ)..1, g (t + a) := by
              refine intervalIntegral.integral_congr_ae ?_
              filter_upwards with t ht
              rw [add_comm]
      _ = ∫ x in (0 : ℝ) + a..1 + a, g x := by
              exact intervalIntegral.integral_comp_add_right (fun x ↦ g x) a
      _ = ∫ x in a..a + 1, g x := by
              simp [add_comm]
  have hIcc :
      (∫ t in Set.Icc (0 : ℝ) 1, g (a + t) ∂MeasureTheory.volume) =
        ∫ t in (0 : ℝ)..1, g (a + t) := by
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]
  have hline :
      uacl (a + 1) - uacl a =
        ∫ t in Set.Icc (0 : ℝ) 1, g (a + t) ∂MeasureTheory.volume := by
    calc
      uacl (a + 1) - uacl a
          = ∫ x in a..a + 1, deriv uacl x := by
              exact hacl.integral_deriv_eq_sub.symm
      _ = ∫ x in a..a + 1, g x := hderiv_integral
      _ = ∫ t in (0 : ℝ)..1, g (a + t) := hshift.symm
      _ = ∫ t in Set.Icc (0 : ℝ) 1, g (a + t) ∂MeasureTheory.volume := hIcc.symm
  exact ha_endpoint.trans hline

/--
%%handwave
name:
  One-dimensional weak Sobolev functions have absolutely continuous representatives
statement:
  Let \(u\) have weak derivative \(g\) on an open subset of \(\mathbb R\).
  If \(u\) and \(g\) are square-integrable on a compact set \(Q\), and every
  unit segment starting from a compact set \(K\) remains in \(Q\), then there is
  a representative \(\tilde u\), equal to \(u\) almost everywhere on \(Q\), such
  that
  \[
    \tilde u(a+1)-\tilde u(a)=\int_0^1 g(a+t)\,dt
  \]
  for almost every \(a\in K\).
proof:
  On compact intervals, the distributional identity implies that \(u\) differs
  from the primitive of \(g\) by a constant.  Since \(g\in L^2\), this primitive
  is absolutely continuous.  Applying the fundamental theorem of calculus to
  that representative gives the identity on almost every unit segment.
-/
theorem realWeakSobolev_exists_acl_representative_on_segments
    {K Q Ω : Set ℝ} (hK : IsCompact K) (hQ : IsCompact Q)
    (hQΩ : Q ⊆ Ω) (hΩ_open : IsOpen Ω)
    {u g : ℝ → ℝ}
    (hweak : IsWeakDerivativeOnRealRegionScalar Ω u g)
    (hu : MemLp u 2 (MeasureTheory.volume.restrict Q))
    (hg : MemLp g 2 (MeasureTheory.volume.restrict Q))
    (hsegments :
      ∀ a ∈ K, ∀ t : ℝ, t ∈ Set.Icc 0 1 → a + t ∈ Q) :
    ∃ uacl : ℝ → ℝ,
      uacl =ᵐ[MeasureTheory.volume.restrict Q] u ∧
        ∀ᵐ a ∂MeasureTheory.volume.restrict K,
          uacl (a + 1) - uacl a =
            ∫ t in Set.Icc (0 : ℝ) 1, g (a + t) ∂MeasureTheory.volume := by
  have hu_loc : LocallyIntegrableOn u Ω (MeasureTheory.volume : Measure ℝ) :=
    realWeakSobolev_function_locallyIntegrableOn hΩ_open hweak
  have hg_loc : LocallyIntegrableOn g Ω (MeasureTheory.volume : Measure ℝ) :=
    realWeakSobolev_derivative_locallyIntegrableOn hΩ_open hweak
  have hu_int_Q : Integrable u (MeasureTheory.volume.restrict Q) :=
    realWeakSobolev_function_integrableOn_compact hQ hQΩ hΩ_open hweak
  have hg_int_Q : Integrable g (MeasureTheory.volume.restrict Q) :=
    realWeakSobolev_derivative_integrableOn_compact hQ hQΩ hΩ_open hweak
  refine ⟨u, Filter.EventuallyEq.rfl, ?_⟩
  exact realWeakSobolev_endpointFTC_ae
    hK hQ hQΩ hΩ_open hweak hu hg hsegments

/--
%%handwave
name:
  One-dimensional weak Sobolev fundamental theorem
statement:
  Let \(u\) have weak derivative \(g\) on an open subset of \(\mathbb R\).
  If \(u\) and \(g\) are square-integrable on a compact set \(Q\), and every
  unit segment starting from a compact set \(K\) remains in \(Q\), then
  \[
    u(a+1)-u(a)=\int_0^1 g(a+t)\,dt
  \]
  for almost every \(a\in K\).
proof:
  The one-dimensional weak derivative theorem gives an absolutely continuous
  representative on compact intervals, with classical derivative \(g\) almost
  everywhere.  The fundamental theorem of calculus gives the displayed identity,
  and the representative agrees with the original function at almost every
  endpoint.
-/
theorem realWeakSobolev_unitSegmentFTC_ae
    {K Q Ω : Set ℝ} (hK : IsCompact K) (hQ : IsCompact Q)
    (hQΩ : Q ⊆ Ω) (hΩ_open : IsOpen Ω)
    {u g : ℝ → ℝ}
    (hweak : IsWeakDerivativeOnRealRegionScalar Ω u g)
    (hu : MemLp u 2 (MeasureTheory.volume.restrict Q))
    (hg : MemLp g 2 (MeasureTheory.volume.restrict Q))
    (hsegments :
      ∀ a ∈ K, ∀ t : ℝ, t ∈ Set.Icc 0 1 → a + t ∈ Q) :
    ∀ᵐ a ∂MeasureTheory.volume.restrict K,
      u (a + 1) - u a =
        ∫ t in Set.Icc (0 : ℝ) 1, g (a + t) ∂MeasureTheory.volume := by
  rcases realWeakSobolev_exists_acl_representative_on_segments
      hK hQ hQΩ hΩ_open hweak hu hg hsegments with
    ⟨uacl, huacl_eq, huacl_line⟩
  have hsegments_one :
      ∀ x ∈ K, ∀ t : ℝ, t ∈ Set.Icc 0 1 → x + t • (1 : ℝ) ∈ Q := by
    intro x hx t ht
    simpa [smul_eq_mul] using hsegments x hx t ht
  have hendpoints :
      (fun z : ℝ ↦ u (z + (1 : ℝ)) - u z)
        =ᵐ[MeasureTheory.volume.restrict K]
      fun z : ℝ ↦ uacl (z + (1 : ℝ)) - uacl z := by
    exact ae_eq_endpoint_difference_of_ae_eq_on_segments
      (H := ℝ) (K := K) (Q := Q) (u := u) (v := uacl)
      (h := (1 : ℝ)) huacl_eq hsegments_one
  filter_upwards [hendpoints, huacl_line] with a ha_endpoint ha_line
  exact ha_endpoint.trans ha_line

/--
%%handwave
name:
  Square-integrable product functions have square-integrable vertical slices
statement:
  If a scalar function is square-integrable on a compact subset
  \(Q\subset\mathbb R\times\mathbb R^d\), then for almost every transverse
  coordinate \(y\), the sliced function \(a\mapsto f(a,y)\) is
  square-integrable on the vertical fiber \(Q_y\).
proof:
  This is Fubini's theorem applied to the square of the function, together with
  the product decomposition of Euclidean measure.
-/
theorem firstCoordinateVerticalFiber_memLp_ae_of_memLp_restrict
    {d : ℕ} {Q : Set (ℝ × (Fin d → ℝ))} (hQ : IsCompact Q)
    {f : (ℝ × (Fin d → ℝ)) → ℝ}
    (hf : MemLp f 2 (MeasureTheory.volume.restrict Q)) :
    ∀ᵐ y ∂(MeasureTheory.volume : Measure (Fin d → ℝ)),
      MemLp (fun a : ℝ ↦ f (a, y)) 2
        (MeasureTheory.volume.restrict (firstCoordinateVerticalFiber Q y)) := by
  classical
  let μa : Measure ℝ := MeasureTheory.volume
  let μy : Measure (Fin d → ℝ) := MeasureTheory.volume
  let F : (Fin d → ℝ) × ℝ → ℝ :=
    fun p ↦ Q.indicator f (p.2, p.1)
  have hQ_meas : MeasurableSet Q := hQ.measurableSet
  have hf_ind_volume :
      MemLp (Q.indicator f) 2
        (MeasureTheory.volume : Measure (ℝ × (Fin d → ℝ))) := by
    rw [memLp_indicator_iff_restrict hQ_meas]
    exact hf
  have hf_ind_prod :
      MemLp (Q.indicator f) 2 (μa.prod μy) := by
    simpa [μa, μy, Measure.volume_eq_prod] using hf_ind_volume
  have hF_mem :
      MemLp F 2 (μy.prod μa) := by
    have hswap :
        MeasurePreserving Prod.swap (μy.prod μa) (μa.prod μy) :=
      Measure.measurePreserving_swap (μ := μy) (ν := μa)
    simpa [F, Function.comp_def] using
      hf_ind_prod.comp_measurePreserving hswap
  have hF_sq_int :
      Integrable (fun p : (Fin d → ℝ) × ℝ ↦ F p ^ 2) (μy.prod μa) :=
    hF_mem.integrable_sq
  have hF_sq_slices :
      ∀ᵐ y ∂μy, Integrable (fun a : ℝ ↦ F (y, a) ^ 2) μa :=
    ((MeasureTheory.integrable_prod_iff hF_sq_int.aestronglyMeasurable).mp
      hF_sq_int).1
  have hF_meas_slices :
      ∀ᵐ y ∂μy, AEStronglyMeasurable (fun a : ℝ ↦ F (y, a)) μa :=
    hF_mem.aestronglyMeasurable.prodMk_left
  filter_upwards [hF_sq_slices, hF_meas_slices] with y hsq_y hmeas_y
  have hmem_indicator :
      MemLp (fun a : ℝ ↦ F (y, a)) 2 μa :=
    (memLp_two_iff_integrable_sq hmeas_y).2 hsq_y
  have hfiber_meas : MeasurableSet (firstCoordinateVerticalFiber Q y) := by
    have hcont : Continuous (fun a : ℝ ↦ ((a, y) : ℝ × (Fin d → ℝ))) := by
      fun_prop
    exact hQ_meas.preimage hcont.measurable
  rw [← memLp_indicator_iff_restrict hfiber_meas]
  refine hmem_indicator.ae_eq ?_
  exact ae_of_all μa fun a ↦ by
    by_cases ha : ((a, y) : ℝ × (Fin d → ℝ)) ∈ Q
    · simp [F, firstCoordinateVerticalFiber, ha]
    · simp [F, firstCoordinateVerticalFiber, ha]

/--
%%handwave
name:
  First-coordinate translation preserves null sets
statement:
  Translation by \((s,0)\) on
  \(\mathbb R\times\mathbb R^d\) is quasi-measure-preserving for Lebesgue
  measure.
proof:
  It is the product of translation by \(s\) on \(\mathbb R\) and translation
  by zero on \(\mathbb R^d\), both measure-preserving.
-/
private theorem firstCoordinate_translation_quasiMeasurePreserving_core
    {d : ℕ} (s : ℝ) :
    Measure.QuasiMeasurePreserving
      (fun z : ℝ × (Fin d → ℝ) ↦ z + ((s : ℝ), (0 : Fin d → ℝ)))
      (MeasureTheory.volume : Measure (ℝ × (Fin d → ℝ)))
      (MeasureTheory.volume : Measure (ℝ × (Fin d → ℝ))) := by
  have hqmp_prod :
      Measure.QuasiMeasurePreserving
        (Prod.map (fun a : ℝ ↦ a + s)
          (fun y : Fin d → ℝ ↦ y + (0 : Fin d → ℝ)))
        ((MeasureTheory.volume : Measure ℝ).prod
          (MeasureTheory.volume : Measure (Fin d → ℝ)))
        ((MeasureTheory.volume : Measure ℝ).prod
          (MeasureTheory.volume : Measure (Fin d → ℝ))) :=
    MeasureTheory.QuasiMeasurePreserving.prodMap
      (MeasureTheory.quasiMeasurePreserving_add_right
        (MeasureTheory.volume : Measure ℝ) s)
      (MeasureTheory.quasiMeasurePreserving_add_right
        (MeasureTheory.volume : Measure (Fin d → ℝ)) (0 : Fin d → ℝ))
  have hqmp_volume :
      Measure.QuasiMeasurePreserving
        (Prod.map (fun a : ℝ ↦ a + s)
          (fun y : Fin d → ℝ ↦ y + (0 : Fin d → ℝ)))
        (MeasureTheory.volume : Measure (ℝ × (Fin d → ℝ)))
        (MeasureTheory.volume : Measure (ℝ × (Fin d → ℝ))) := by
    simpa [Measure.volume_eq_prod] using hqmp_prod
  have hfun :
      (Prod.map (fun a : ℝ ↦ a + s)
          (fun y : Fin d → ℝ ↦ y + (0 : Fin d → ℝ))) =
        (fun z : ℝ × (Fin d → ℝ) ↦ z + ((s : ℝ), (0 : Fin d → ℝ))) := by
    funext z
    ext i <;> simp
  rwa [hfun] at hqmp_volume

/--
%%handwave
name:
  Restricted first-coordinate translation preserves null sets
statement:
  If every unit first-coordinate translate of points of \(K\) lies in \(Q\),
  then \(x\mapsto x+(1,0)\) is quasi-measure-preserving from Lebesgue measure
  restricted to \(K\) to Lebesgue measure restricted to \(Q\).
proof:
  The unrestricted translation is measure-preserving and maps \(K\) into
  \(Q\); restrict its source and target measures.
-/
private theorem firstCoordinate_translation_quasiMeasurePreserving_restrict_core
    {d : ℕ} {K Q : Set (ℝ × (Fin d → ℝ))}
    (hsegments :
      ∀ x ∈ K, ∀ t : ℝ, t ∈ Set.Icc 0 1 →
        x + t • ((1 : ℝ), (0 : Fin d → ℝ)) ∈ Q) :
    Measure.QuasiMeasurePreserving
      (fun z : ℝ × (Fin d → ℝ) ↦ z + ((1 : ℝ), (0 : Fin d → ℝ)))
      (MeasureTheory.volume.restrict K) (MeasureTheory.volume.restrict Q) := by
  have htranslateKQ :
      Set.MapsTo
        (fun z : ℝ × (Fin d → ℝ) ↦ z + ((1 : ℝ), (0 : Fin d → ℝ))) K Q := by
    intro x hx
    simpa using hsegments x hx 1 (by simp)
  exact (firstCoordinate_translation_quasiMeasurePreserving_core (d := d) 1).restrict htranslateKQ

/--
%%handwave
name:
  Restricted first-coordinate segment map preserves null sets
statement:
  If \(x+t(1,0)\in Q\) for \(x\in K\) and \(t\in[0,1]\), then
  \((x,t)\mapsto x+t(1,0)\) is quasi-measure-preserving from
  \((\mathrm{vol}|_K)\times(\mathrm{vol}|_{[0,1]})\) to
  \(\mathrm{vol}|_Q\).
proof:
  For almost every \(t\), translation by \(t(1,0)\) preserves Lebesgue null
  sets and maps \(K\) into \(Q\). Apply the product criterion.
-/
private theorem firstCoordinate_segmentMap_quasiMeasurePreserving_restrict_prod_core
    {d : ℕ} {K Q : Set (ℝ × (Fin d → ℝ))}
    (hsegments :
      ∀ x ∈ K, ∀ t : ℝ, t ∈ Set.Icc 0 1 →
        x + t • ((1 : ℝ), (0 : Fin d → ℝ)) ∈ Q) :
    Measure.QuasiMeasurePreserving
      (fun p : (ℝ × (Fin d → ℝ)) × ℝ ↦
        p.1 + p.2 • ((1 : ℝ), (0 : Fin d → ℝ)))
      ((MeasureTheory.volume.restrict K).prod
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)))
      (MeasureTheory.volume.restrict Q) := by
  refine MeasureTheory.QuasiMeasurePreserving.prod_of_left (τ := MeasureTheory.volume.restrict Q)
    ?_ ?_
  · fun_prop
  · filter_upwards [ae_restrict_mem (measurableSet_Icc : MeasurableSet (Set.Icc (0 : ℝ) 1))]
      with t ht
    have hmap :
        Set.MapsTo
          (fun z : ℝ × (Fin d → ℝ) ↦
            z + t • ((1 : ℝ), (0 : Fin d → ℝ))) K Q := by
      intro z hz
      exact hsegments z hz t ht
    have hqmp :
        Measure.QuasiMeasurePreserving
          (fun z : ℝ × (Fin d → ℝ) ↦
            z + t • ((1 : ℝ), (0 : Fin d → ℝ)))
          (MeasureTheory.volume : Measure (ℝ × (Fin d → ℝ)))
          (MeasureTheory.volume : Measure (ℝ × (Fin d → ℝ))) := by
      simpa [smul_eq_mul] using
        firstCoordinate_translation_quasiMeasurePreserving_core (d := d) t
    exact hqmp.restrict hmap

/--
%%handwave
name:
  Weak Sobolev functions satisfy the vertical finite-difference identity
statement:
  In \(\mathbb R\times\mathbb R^d\), let \(e_1=(1,0)\).  For a scalar weak
  \(W^{1,2}\) function on an open region, assume the function and its weak
  derivative in the direction \(e_1\) are square-integrable on a compact set
  \(P\), assume a positive thickening of a compact set \(Q\) lies in \(P\),
  and assume every vertical unit segment starting from a compact set \(K\)
  remains in \(Q\).  Then, for almost every \(x\in K\),
  \[
    u(x+e_1)-u(x)=\int_0^1 D u(x+t e_1)e_1\,dt .
  \]
proof:
  Apply [the directional weak fundamental theorem on segments](lean:JJMath.Uniformization.scalarWeakSobolev_directional_acl_line_integral_eq_ae_kinnunen)
  in the product space with \(h=e_1\).
-/
theorem scalarWeakSobolev_firstCoordinate_product_line_integral_eq_ae
    {d : ℕ}
    {K Q P Ω : Set (ℝ × (Fin d → ℝ))} (hK : IsCompact K) (hQ : IsCompact Q)
    (hP : IsCompact P)
    (hQP : ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ Q ⊆ P)
    (hPΩ : P ⊆ Ω) (hΩ_open : IsOpen Ω)
    {u : (ℝ × (Fin d → ℝ)) → ℝ}
    {du : (ℝ × (Fin d → ℝ)) → (ℝ × (Fin d → ℝ)) →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionScalar Ω u du)
    (hu : MemLp u 2 (MeasureTheory.volume.restrict P))
    (hdu : MemLp (fun z ↦ du z ((1 : ℝ), (0 : Fin d → ℝ))) 2
      (MeasureTheory.volume.restrict P))
    (hsegments :
      ∀ x ∈ K, ∀ t : ℝ, t ∈ Set.Icc 0 1 →
        x + t • ((1 : ℝ), (0 : Fin d → ℝ)) ∈ Q) :
    ∀ᵐ z ∂MeasureTheory.volume.restrict K,
      u (z + ((1 : ℝ), (0 : Fin d → ℝ))) - u z =
        ∫ t in Set.Icc (0 : ℝ) 1,
          du (z + t • ((1 : ℝ), (0 : Fin d → ℝ)))
            ((1 : ℝ), (0 : Fin d → ℝ)) ∂MeasureTheory.volume := by
  haveI : Measure.IsAddHaarMeasure
      (MeasureTheory.volume : Measure (ℝ × (Fin d → ℝ))) := by
    rw [Measure.volume_eq_prod]
    infer_instance
  exact
    scalarWeakSobolev_directional_acl_line_integral_eq_ae_kinnunen
      (H := ℝ × (Fin d → ℝ)) hK hQ hP hQP hPΩ hΩ_open hweak hu hdu hsegments

/--
%%handwave
name:
  Weak Sobolev functions satisfy the vertical fundamental theorem on almost every fiber
statement:
  In \(\mathbb R\times\mathbb R^d\), let \(e_1=(1,0)\).  For a scalar weak
  \(W^{1,2}\) function on an open region, assume the function and its weak
  derivative in the direction \(e_1\) are square-integrable on a compact set
  \(P\), assume a positive thickening of a compact set \(Q\) lies in \(P\),
  and assume every vertical unit segment starting from a compact set \(K\)
  remains in \(Q\).  Then for almost every transverse coordinate
  \(y\), and for almost every \(a\) in the vertical fiber of \(K\) over
  \(y\),
  \[
    u((a,y)+e_1)-u(a,y)
      =\int_0^1 D u((a,y)+t e_1)e_1\,dt .
  \]
proof:
  First prove [the product almost-everywhere segment identity](lean:JJMath.Uniformization.scalarWeakSobolev_firstCoordinate_product_line_integral_eq_ae).
  Then disintegrate the restricted product measure over vertical fibers to
  obtain the fiberwise almost-everywhere statement.
-/
theorem scalarWeakSobolev_firstCoordinate_fiberwise_line_integral_eq_ae
    {d : ℕ}
    {K Q P Ω : Set (ℝ × (Fin d → ℝ))} (hK : IsCompact K) (hQ : IsCompact Q)
    (hP : IsCompact P)
    (hQP : ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ Q ⊆ P)
    (hPΩ : P ⊆ Ω) (hΩ_open : IsOpen Ω)
    {u : (ℝ × (Fin d → ℝ)) → ℝ}
    {du : (ℝ × (Fin d → ℝ)) → (ℝ × (Fin d → ℝ)) →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionScalar Ω u du)
    (hu : MemLp u 2 (MeasureTheory.volume.restrict P))
    (hdu : MemLp (fun z ↦ du z ((1 : ℝ), (0 : Fin d → ℝ))) 2
      (MeasureTheory.volume.restrict P))
    (hsegments :
      ∀ x ∈ K, ∀ t : ℝ, t ∈ Set.Icc 0 1 →
        x + t • ((1 : ℝ), (0 : Fin d → ℝ)) ∈ Q) :
    ∀ᵐ y ∂(MeasureTheory.volume : Measure (Fin d → ℝ)),
      ∀ᵐ a ∂(MeasureTheory.volume.restrict (firstCoordinateVerticalFiber K y)),
        u (((a, y) : ℝ × (Fin d → ℝ)) + ((1 : ℝ), (0 : Fin d → ℝ))) -
            u (a, y) =
          ∫ t in Set.Icc (0 : ℝ) 1,
            du (((a, y) : ℝ × (Fin d → ℝ)) +
                t • ((1 : ℝ), (0 : Fin d → ℝ)))
              ((1 : ℝ), (0 : Fin d → ℝ)) ∂MeasureTheory.volume := by
  have hprod :
      ∀ᵐ z ∂MeasureTheory.volume.restrict K,
        u (z + ((1 : ℝ), (0 : Fin d → ℝ))) - u z =
          ∫ t in Set.Icc (0 : ℝ) 1,
            du (z + t • ((1 : ℝ), (0 : Fin d → ℝ)))
              ((1 : ℝ), (0 : Fin d → ℝ)) ∂MeasureTheory.volume := by
    exact
      scalarWeakSobolev_firstCoordinate_product_line_integral_eq_ae
        hK hQ hP hQP hPΩ hΩ_open hweak hu hdu hsegments
  exact
    scalarWeakSobolev_firstCoordinate_fiberwise_line_integral_eq_ae_of_product
      hK hprod

/--
%%handwave
name:
  First-coordinate translations preserve null sets
statement:
  In \(\mathbb R\times\mathbb R^d\), translation by \(s e_1\) is
  quasi-measure-preserving for Euclidean measure.
proof:
  Euclidean measure on the product is the product of the one-dimensional and
  transverse Euclidean measures.  The map is the product of translation by
  \(s\) on \(\mathbb R\) and the identity translation on \(\mathbb R^d\), and
  each factor preserves null sets.
-/
theorem firstCoordinate_translation_quasiMeasurePreserving
    {d : ℕ} (s : ℝ) :
    Measure.QuasiMeasurePreserving
      (fun z : ℝ × (Fin d → ℝ) ↦ z + ((s : ℝ), (0 : Fin d → ℝ)))
      (MeasureTheory.volume : Measure (ℝ × (Fin d → ℝ)))
      (MeasureTheory.volume : Measure (ℝ × (Fin d → ℝ))) := by
  exact firstCoordinate_translation_quasiMeasurePreserving_core (d := d) s

/--
%%handwave
name:
  Translation by the first coordinate preserves null sets on restricted compact sets
statement:
  If every translated point \(z+e_1\), \(z\in K\), lies in \(Q\), then
  translation by \(e_1\) sends null sets in \(Q\) to null sets when pulled
  back to \(K\).  Equivalently, the translation map is quasi-measure-preserving
  from Euclidean measure restricted to \(K\) to Euclidean measure restricted
  to \(Q\).
proof:
  Euclidean measure on \(\mathbb R\times\mathbb R^d\) is translation
  invariant, and the containment hypothesis ensures that the restricted
  source measure lands in the restricted target measure.
-/
theorem firstCoordinate_translation_quasiMeasurePreserving_restrict
    {d : ℕ} {K Q : Set (ℝ × (Fin d → ℝ))}
    (hsegments :
      ∀ x ∈ K, ∀ t : ℝ, t ∈ Set.Icc 0 1 →
        x + t • ((1 : ℝ), (0 : Fin d → ℝ)) ∈ Q) :
    Measure.QuasiMeasurePreserving
      (fun z : ℝ × (Fin d → ℝ) ↦ z + ((1 : ℝ), (0 : Fin d → ℝ)))
      (MeasureTheory.volume.restrict K) (MeasureTheory.volume.restrict Q) := by
  exact firstCoordinate_translation_quasiMeasurePreserving_restrict_core
    (K := K) (Q := Q) hsegments

/--
%%handwave
name:
  The vertical segment map preserves null sets
statement:
  If every segment \(z+t e_1\), \(z\in K\), \(0\le t\le1\), lies in \(Q\),
  then the map \((z,t)\mapsto z+t e_1\) is quasi-measure-preserving from
  Euclidean measure restricted to \(K\times[0,1]\) to Euclidean measure
  restricted to \(Q\).
proof:
  For each fixed \(t\in[0,1]\), the map \(z\mapsto z+t e_1\) is a
  first-coordinate translation and hence preserves null sets.  The containment
  hypothesis gives a restricted quasi-measure-preserving map from \(K\) to
  \(Q\).  Fubini, formulated as the product quasi-measure-preservation
  criterion, then gives the result for the segment map.
-/
theorem firstCoordinate_segmentMap_quasiMeasurePreserving_restrict_prod
    {d : ℕ} {K Q : Set (ℝ × (Fin d → ℝ))}
    (hsegments :
      ∀ x ∈ K, ∀ t : ℝ, t ∈ Set.Icc 0 1 →
        x + t • ((1 : ℝ), (0 : Fin d → ℝ)) ∈ Q) :
    Measure.QuasiMeasurePreserving
      (fun p : (ℝ × (Fin d → ℝ)) × ℝ ↦
        p.1 + p.2 • ((1 : ℝ), (0 : Fin d → ℝ)))
      ((MeasureTheory.volume.restrict K).prod
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)))
      (MeasureTheory.volume.restrict Q) := by
  exact firstCoordinate_segmentMap_quasiMeasurePreserving_restrict_prod_core
    (K := K) (Q := Q) hsegments

/--
%%handwave
name:
  The vertical endpoint difference is measurable on the compact set
statement:
  Under the vertical segment containment hypothesis, the function
  \(z\mapsto u(z+e_1)-u(z)\) is measurable up to null sets on \(K\).
proof:
  The \(L^2\) assumption makes \(u\) measurable up to null sets on \(Q\).
  Since \(K\subset Q\) and \(K+e_1\subset Q\), both \(u\) and the translated
  function \(u(\,\cdot+e_1)\) are measurable up to null sets on \(K\).  Their
  difference has the same property.
-/
theorem scalarWeakSobolev_firstCoordinate_endpointDifference_aestronglyMeasurable_restrict
    {d : ℕ}
    {K Q : Set (ℝ × (Fin d → ℝ))}
    {u : (ℝ × (Fin d → ℝ)) → ℝ}
    (hu : MemLp u 2 (MeasureTheory.volume.restrict Q))
    (hsegments :
      ∀ x ∈ K, ∀ t : ℝ, t ∈ Set.Icc 0 1 →
        x + t • ((1 : ℝ), (0 : Fin d → ℝ)) ∈ Q) :
    AEStronglyMeasurable
      (fun z : ℝ × (Fin d → ℝ) ↦
        u (z + ((1 : ℝ), (0 : Fin d → ℝ))) - u z)
      (MeasureTheory.volume.restrict K) := by
  have hKQ : K ⊆ Q := by
    intro x hx
    simpa using hsegments x hx 0 (by simp)
  have hbase :
      AEStronglyMeasurable u (MeasureTheory.volume.restrict K) :=
    (hu.mono_measure (Measure.restrict_mono hKQ le_rfl)).aestronglyMeasurable
  have htranslate_qmp :
      Measure.QuasiMeasurePreserving
        (fun z : ℝ × (Fin d → ℝ) ↦ z + ((1 : ℝ), (0 : Fin d → ℝ)))
        (MeasureTheory.volume.restrict K) (MeasureTheory.volume.restrict Q) :=
    firstCoordinate_translation_quasiMeasurePreserving_restrict
      (K := K) (Q := Q) hsegments
  have htranslate :
      AEStronglyMeasurable
        (fun z : ℝ × (Fin d → ℝ) ↦
          u (z + ((1 : ℝ), (0 : Fin d → ℝ))))
        (MeasureTheory.volume.restrict K) := by
    simpa [Function.comp_def] using
      hu.aestronglyMeasurable.comp_quasiMeasurePreserving htranslate_qmp
  exact htranslate.sub hbase

/--
%%handwave
name:
  The vertical segment integral is measurable on the compact set
statement:
  Under the vertical segment containment hypothesis and the \(L^2\)
  assumption on the sliced weak derivative, the map
  \[
    z\mapsto \int_0^1 D u(z+t e_1)e_1\,dt
  \]
  is measurable up to null sets on \(K\).
proof:
  The integrand \((z,t)\mapsto D u(z+t e_1)e_1\) is measurable up to null
  sets on \(K\times[0,1]\), because the segment map lands in \(Q\) and the
  sliced derivative is \(L^2\) on \(Q\).  Fubini then gives measurability of
  the parameter integral.
-/
theorem scalarWeakSobolev_firstCoordinate_segmentIntegral_aestronglyMeasurable_restrict
    {d : ℕ}
    {K Q : Set (ℝ × (Fin d → ℝ))}
    {du : (ℝ × (Fin d → ℝ)) → (ℝ × (Fin d → ℝ)) →L[ℝ] ℝ}
    (hdu : MemLp (fun z ↦ du z ((1 : ℝ), (0 : Fin d → ℝ))) 2
      (MeasureTheory.volume.restrict Q))
    (hsegments :
      ∀ x ∈ K, ∀ t : ℝ, t ∈ Set.Icc 0 1 →
        x + t • ((1 : ℝ), (0 : Fin d → ℝ)) ∈ Q) :
    AEStronglyMeasurable
      (fun z : ℝ × (Fin d → ℝ) ↦
        ∫ t in Set.Icc (0 : ℝ) 1,
          du (z + t • ((1 : ℝ), (0 : Fin d → ℝ)))
            ((1 : ℝ), (0 : Fin d → ℝ)) ∂MeasureTheory.volume)
      (MeasureTheory.volume.restrict K) := by
  let F : (ℝ × (Fin d → ℝ)) × ℝ → ℝ :=
    fun p ↦ du (p.1 + p.2 • ((1 : ℝ), (0 : Fin d → ℝ)))
      ((1 : ℝ), (0 : Fin d → ℝ))
  have hsegment_qmp :
      Measure.QuasiMeasurePreserving
        (fun p : (ℝ × (Fin d → ℝ)) × ℝ ↦
          p.1 + p.2 • ((1 : ℝ), (0 : Fin d → ℝ)))
        ((MeasureTheory.volume.restrict K).prod
          (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)))
        (MeasureTheory.volume.restrict Q) :=
    firstCoordinate_segmentMap_quasiMeasurePreserving_restrict_prod
      (K := K) (Q := Q) hsegments
  have hF :
      AEStronglyMeasurable F
        ((MeasureTheory.volume.restrict K).prod
          (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))) := by
    simpa [F, Function.comp_def] using
      hdu.aestronglyMeasurable.comp_quasiMeasurePreserving hsegment_qmp
  have hInt :
      AEStronglyMeasurable
        (fun z : ℝ × (Fin d → ℝ) ↦
          ∫ t, F (z, t)
            ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)))
        (MeasureTheory.volume.restrict K) :=
    hF.integral_prod_right'
  simpa [F] using hInt

/--
%%handwave
name:
  The vertical fundamental theorem has a null-measurable exceptional set
statement:
  Under the hypotheses of the vertical weak Sobolev fundamental theorem, the
  subset of \(K\) on which the endpoint identity fails is measurable up to a
  null set.
proof:
  The function and the sliced weak derivative are measurable after modifying
  representatives on null sets, because they are \(L^2\).  The segment
  integral is obtained from a measurable function on the product
  \(K\times[0,1]\), so it is measurable up to null sets by Fubini.  Hence the
  equality-failure set is null-measurable.
-/
theorem scalarWeakSobolev_firstCoordinate_line_integral_failure_nullMeasurableSet
    {d : ℕ}
    {K Q : Set (ℝ × (Fin d → ℝ))} (hK : IsCompact K)
    {u : (ℝ × (Fin d → ℝ)) → ℝ}
    {du : (ℝ × (Fin d → ℝ)) → (ℝ × (Fin d → ℝ)) →L[ℝ] ℝ}
    (hu : MemLp u 2 (MeasureTheory.volume.restrict Q))
    (hdu : MemLp (fun z ↦ du z ((1 : ℝ), (0 : Fin d → ℝ))) 2
      (MeasureTheory.volume.restrict Q))
    (hsegments :
      ∀ x ∈ K, ∀ t : ℝ, t ∈ Set.Icc 0 1 →
        x + t • ((1 : ℝ), (0 : Fin d → ℝ)) ∈ Q) :
    NullMeasurableSet
      {z : ℝ × (Fin d → ℝ) |
        z ∈ K ∧
          ¬ u (z + ((1 : ℝ), (0 : Fin d → ℝ))) - u z =
              ∫ t in Set.Icc (0 : ℝ) 1,
                du (z + t • ((1 : ℝ), (0 : Fin d → ℝ)))
                  ((1 : ℝ), (0 : Fin d → ℝ)) ∂MeasureTheory.volume}
      (MeasureTheory.volume : Measure (ℝ × (Fin d → ℝ))) := by
  let lhs : (ℝ × (Fin d → ℝ)) → ℝ :=
    fun z ↦ u (z + ((1 : ℝ), (0 : Fin d → ℝ))) - u z
  let rhs : (ℝ × (Fin d → ℝ)) → ℝ :=
    fun z ↦
      ∫ t in Set.Icc (0 : ℝ) 1,
        du (z + t • ((1 : ℝ), (0 : Fin d → ℝ)))
          ((1 : ℝ), (0 : Fin d → ℝ)) ∂MeasureTheory.volume
  have hlhs :
      AEStronglyMeasurable lhs (MeasureTheory.volume.restrict K) := by
    simpa [lhs] using
      scalarWeakSobolev_firstCoordinate_endpointDifference_aestronglyMeasurable_restrict
        (K := K) (Q := Q) hu hsegments
  have hrhs :
      AEStronglyMeasurable rhs (MeasureTheory.volume.restrict K) := by
    simpa [rhs] using
      scalarWeakSobolev_firstCoordinate_segmentIntegral_aestronglyMeasurable_restrict
        (K := K) (Q := Q) hdu hsegments
  have heq :
      NullMeasurableSet {z : ℝ × (Fin d → ℝ) | lhs z = rhs z}
        (MeasureTheory.volume.restrict K) :=
    nullMeasurableSet_eq_fun hlhs.aemeasurable hrhs.aemeasurable
  have hfailure_restrict :
      NullMeasurableSet {z : ℝ × (Fin d → ℝ) | ¬ lhs z = rhs z}
        (MeasureTheory.volume.restrict K) :=
    heq.compl
  have hK_meas :
      NullMeasurableSet K
        (MeasureTheory.volume : Measure (ℝ × (Fin d → ℝ))) :=
    hK.isClosed.measurableSet.nullMeasurableSet
  have hfailure_volume :
      NullMeasurableSet ({z : ℝ × (Fin d → ℝ) | ¬ lhs z = rhs z} ∩ K)
        (MeasureTheory.volume : Measure (ℝ × (Fin d → ℝ))) :=
    (nullMeasurableSet_restrict hK_meas).1 hfailure_restrict
  convert hfailure_volume using 1
  ext z
  simp [lhs, rhs, and_comm]

/--
%%handwave
name:
  Fiberwise vertical fundamental theorem gives the product almost-everywhere statement
statement:
  If the vertical fundamental theorem holds for almost every vertical fiber
  of a compact set \(K\subset\mathbb R\times\mathbb R^d\), then it holds for
  almost every point of \(K\) with respect to Euclidean measure restricted to
  \(K\).
proof:
  Euclidean measure on \(\mathbb R\times\mathbb R^d\) is the product of the
  one-dimensional and transverse Euclidean measures.  Applying Fubini to the
  measurable subset of \(K\) where the endpoint identity fails shows that its
  measure is zero, because almost every vertical section has zero
  one-dimensional measure.  This is exactly the desired almost-everywhere
  statement for the restricted measure on \(K\).
-/
theorem scalarWeakSobolev_firstCoordinate_line_integral_eq_ae_of_fiberwise
    {d : ℕ}
    {K : Set (ℝ × (Fin d → ℝ))}
    {u : (ℝ × (Fin d → ℝ)) → ℝ}
    {du : (ℝ × (Fin d → ℝ)) → (ℝ × (Fin d → ℝ)) →L[ℝ] ℝ}
    (hK : MeasurableSet K)
    (hbad :
      NullMeasurableSet
        {z : ℝ × (Fin d → ℝ) |
          z ∈ K ∧
            ¬ u (z + ((1 : ℝ), (0 : Fin d → ℝ))) - u z =
                ∫ t in Set.Icc (0 : ℝ) 1,
                  du (z + t • ((1 : ℝ), (0 : Fin d → ℝ)))
                    ((1 : ℝ), (0 : Fin d → ℝ)) ∂MeasureTheory.volume}
        (MeasureTheory.volume : Measure (ℝ × (Fin d → ℝ))))
    (hfiber :
      ∀ᵐ y ∂(MeasureTheory.volume : Measure (Fin d → ℝ)),
        ∀ᵐ a ∂(MeasureTheory.volume.restrict (firstCoordinateVerticalFiber K y)),
          u (((a, y) : ℝ × (Fin d → ℝ)) + ((1 : ℝ), (0 : Fin d → ℝ))) -
              u (a, y) =
            ∫ t in Set.Icc (0 : ℝ) 1,
              du (((a, y) : ℝ × (Fin d → ℝ)) +
                  t • ((1 : ℝ), (0 : Fin d → ℝ)))
                ((1 : ℝ), (0 : Fin d → ℝ)) ∂MeasureTheory.volume) :
    ∀ᵐ z ∂MeasureTheory.volume.restrict K,
      u (z + ((1 : ℝ), (0 : Fin d → ℝ))) - u z =
        ∫ t in Set.Icc (0 : ℝ) 1,
          du (z + t • ((1 : ℝ), (0 : Fin d → ℝ)))
            ((1 : ℝ), (0 : Fin d → ℝ)) ∂MeasureTheory.volume := by
  exact
    ae_restrict_prod_of_ae_vertical_fibers
      (K := K)
      (P := fun z ↦
        u (z + ((1 : ℝ), (0 : Fin d → ℝ))) - u z =
          ∫ t in Set.Icc (0 : ℝ) 1,
            du (z + t • ((1 : ℝ), (0 : Fin d → ℝ)))
              ((1 : ℝ), (0 : Fin d → ℝ)) ∂MeasureTheory.volume)
      hK hbad hfiber

/--
%%handwave
name:
  Weak Sobolev functions satisfy the vertical fundamental theorem almost everywhere
statement:
  In \(\mathbb R\times\mathbb R^d\), let \(e_1=(1,0)\).  For a scalar weak
  \(W^{1,2}\) function on an open region, assume the function and its weak
  derivative in the direction \(e_1\) are square-integrable on a compact set
  \(P\), assume a positive thickening of a compact set \(Q\) lies in \(P\),
  and assume every vertical unit segment starting from a compact set \(K\)
  remains in \(Q\).  Then for almost every \(x\in K\),
  \[
    u(x+e_1)-u(x)
      =\int_0^1 D u(x+t e_1)e_1\,dt .
  \]
proof:
  This is exactly [the product first-coordinate segment identity](lean:JJMath.Uniformization.scalarWeakSobolev_firstCoordinate_product_line_integral_eq_ae).
-/
theorem scalarWeakSobolev_firstCoordinate_line_integral_eq_ae
    {d : ℕ}
    {K Q P Ω : Set (ℝ × (Fin d → ℝ))} (hK : IsCompact K) (hQ : IsCompact Q)
    (hP : IsCompact P)
    (hQP : ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ Q ⊆ P)
    (hPΩ : P ⊆ Ω) (hΩ_open : IsOpen Ω)
    {u : (ℝ × (Fin d → ℝ)) → ℝ}
    {du : (ℝ × (Fin d → ℝ)) → (ℝ × (Fin d → ℝ)) →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionScalar Ω u du)
    (hu : MemLp u 2 (MeasureTheory.volume.restrict P))
    (hdu : MemLp (fun z ↦ du z ((1 : ℝ), (0 : Fin d → ℝ))) 2
      (MeasureTheory.volume.restrict P))
    (hsegments :
      ∀ x ∈ K, ∀ t : ℝ, t ∈ Set.Icc 0 1 →
        x + t • ((1 : ℝ), (0 : Fin d → ℝ)) ∈ Q) :
    ∀ᵐ z ∂MeasureTheory.volume.restrict K,
      u (z + ((1 : ℝ), (0 : Fin d → ℝ))) - u z =
        ∫ t in Set.Icc (0 : ℝ) 1,
          du (z + t • ((1 : ℝ), (0 : Fin d → ℝ)))
            ((1 : ℝ), (0 : Fin d → ℝ)) ∂MeasureTheory.volume := by
  exact
    scalarWeakSobolev_firstCoordinate_product_line_integral_eq_ae
      hK hQ hP hQP hPΩ hΩ_open hweak hu hdu hsegments

/--
%%handwave
name:
  Sobolev functions have absolutely continuous representatives on vertical lines
statement:
  In \(\mathbb R\times\mathbb R^d\), let \(e_1=(1,0)\).  For a scalar weak
  \(W^{1,2}\) function on an open region, assume the function and its weak
  derivative in the direction \(e_1\) are square-integrable on a compact set
  \(P\), assume a positive thickening of a compact set \(Q\) lies in \(P\),
  and assume every vertical unit segment starting from a compact set \(K\)
  remains in \(Q\).  Then there is a representative agreeing with the
  original function almost everywhere on \(Q\) such that, for almost every
  \(x\in K\),
  \[
    \tilde u(x+e_1)-\tilde u(x)
      =\int_0^1 D u(x+t e_1)e_1\,dt .
  \]
proof:
  Take the original representative and use [the first-coordinate segment identity](lean:JJMath.Uniformization.scalarWeakSobolev_firstCoordinate_line_integral_eq_ae).
-/
theorem scalarWeakSobolev_exists_firstCoordinate_acl_representative_on_segments
    {d : ℕ}
    {K Q P Ω : Set (ℝ × (Fin d → ℝ))} (hK : IsCompact K) (hQ : IsCompact Q)
    (hP : IsCompact P)
    (hQP : ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ Q ⊆ P)
    (hPΩ : P ⊆ Ω) (hΩ_open : IsOpen Ω)
    {u : (ℝ × (Fin d → ℝ)) → ℝ}
    {du : (ℝ × (Fin d → ℝ)) → (ℝ × (Fin d → ℝ)) →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionScalar Ω u du)
    (hu : MemLp u 2 (MeasureTheory.volume.restrict P))
    (hdu : MemLp (fun z ↦ du z ((1 : ℝ), (0 : Fin d → ℝ))) 2
      (MeasureTheory.volume.restrict P))
    (hsegments :
      ∀ x ∈ K, ∀ t : ℝ, t ∈ Set.Icc 0 1 →
        x + t • ((1 : ℝ), (0 : Fin d → ℝ)) ∈ Q) :
    ∃ uacl : (ℝ × (Fin d → ℝ)) → ℝ,
      uacl =ᵐ[MeasureTheory.volume.restrict Q] u ∧
        ∀ᵐ z ∂MeasureTheory.volume.restrict K,
          uacl (z + ((1 : ℝ), (0 : Fin d → ℝ))) - uacl z =
            ∫ t in Set.Icc (0 : ℝ) 1,
              du (z + t • ((1 : ℝ), (0 : Fin d → ℝ)))
                ((1 : ℝ), (0 : Fin d → ℝ)) ∂MeasureTheory.volume := by
  refine ⟨u, Filter.EventuallyEq.rfl, ?_⟩
  exact
    scalarWeakSobolev_firstCoordinate_line_integral_eq_ae
      hK hQ hP hQP hPΩ hΩ_open hweak hu hdu hsegments

/--
%%handwave
name:
  Directional ACL representatives are transported through rectifying coordinates
statement:
  Suppose a continuous linear coordinate equivalence sends a nonzero
  direction \(h\) to the first coordinate direction.  The directional ACL
  representative in \(H\) agrees with the original function almost everywhere
  on \(Q\) and satisfies
  \[
    \tilde u(x+h)-\tilde u(x)
      =\int_0^1 D u(x+t h)h\,dt
  \]
  for almost every \(x\in K\).
proof:
  The rectifying coordinate data is now unused compatibility data.  Take the
  original representative and apply [the directional weak fundamental theorem on segments](lean:JJMath.Uniformization.scalarWeakSobolev_directional_acl_line_integral_eq_ae_kinnunen).
-/
theorem scalarWeakSobolev_exists_directional_acl_representative_of_rectifying_coordinates
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {K Q P Ω : Set H} (hK : IsCompact K) (hQ : IsCompact Q) (hP : IsCompact P)
    (hQP : ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ Q ⊆ P)
    (hPΩ : P ⊆ Ω) (hΩ_open : IsOpen Ω)
    {u : H → ℝ} {du : H → H →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionScalar Ω u du)
    {h : H} {d : ℕ} (_e : H ≃L[ℝ] (ℝ × (Fin d → ℝ)))
    (_he : _e h = ((1 : ℝ), (0 : Fin d → ℝ)))
    (hu : MemLp u 2 (MeasureTheory.volume.restrict P))
    (hdu : MemLp (fun z ↦ du z h) 2 (MeasureTheory.volume.restrict P))
    (hsegments : ∀ x ∈ K, ∀ t : ℝ, t ∈ Set.Icc 0 1 → x + t • h ∈ Q) :
    ∃ uacl : H → ℝ,
      uacl =ᵐ[MeasureTheory.volume.restrict Q] u ∧
        ∀ᵐ z ∂MeasureTheory.volume.restrict K,
          uacl (z + h) - uacl z =
            ∫ t in Set.Icc (0 : ℝ) 1,
              du (z + t • h) h ∂MeasureTheory.volume := by
  refine ⟨u, Filter.EventuallyEq.rfl, ?_⟩
  exact
    scalarWeakSobolev_directional_acl_line_integral_eq_ae_kinnunen
      hK hQ hP hQP hPΩ hΩ_open
      (by
        simpa [KinnunenWeakDerivativeOnEuclideanRegionScalar,
          IsWeakDerivativeOnEuclideanRegionScalar,
          IsWeakDerivativeOnEuclideanRegionWithValues] using hweak)
      hu hdu hsegments

/--
%%handwave
name:
  Sobolev functions have nonzero directional absolutely continuous representatives
statement:
  For a scalar weak \(W^{1,2}\) function on a Euclidean region, assume the
  function and its directional weak derivative in a nonzero direction \(h\)
  are square-integrable on a compact set \(P\), assume a positive thickening
  of a compact set \(Q\) lies in \(P\), and assume every segment from a compact
  set \(K\) in the direction \(h\) remains in \(Q\).  Then there is a
  representative agreeing with the original function almost everywhere on
  \(Q\) such that, for almost every \(x\in K\),
  \[
    \tilde u(x+h)-\tilde u(x)
      =\int_0^1 D u(x+t h)h\,dt .
  \]
proof:
  Choose coordinates sending \(h\) to the first coordinate and use [the directional representative statement transported through those coordinates](lean:JJMath.Uniformization.scalarWeakSobolev_exists_directional_acl_representative_of_rectifying_coordinates).
-/
theorem scalarWeakSobolev_exists_directional_acl_representative_on_nonzero_segments
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {K Q P Ω : Set H} (hK : IsCompact K) (hQ : IsCompact Q) (hP : IsCompact P)
    (hQP : ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ Q ⊆ P)
    (hPΩ : P ⊆ Ω) (hΩ_open : IsOpen Ω)
    {u : H → ℝ} {du : H → H →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionScalar Ω u du)
    {h : H}
    (hh_ne : h ≠ 0)
    (hu : MemLp u 2 (MeasureTheory.volume.restrict P))
    (hdu : MemLp (fun z ↦ du z h) 2 (MeasureTheory.volume.restrict P))
    (hsegments : ∀ x ∈ K, ∀ t : ℝ, t ∈ Set.Icc 0 1 → x + t • h ∈ Q) :
    ∃ uacl : H → ℝ,
      uacl =ᵐ[MeasureTheory.volume.restrict Q] u ∧
        ∀ᵐ z ∂MeasureTheory.volume.restrict K,
          uacl (z + h) - uacl z =
            ∫ t in Set.Icc (0 : ℝ) 1,
              du (z + t • h) h ∂MeasureTheory.volume := by
  rcases exists_continuousLinearEquiv_apply_nonzero_eq_firstCoordinate
      (H := H) hh_ne with
    ⟨d, e, he⟩
  exact
    scalarWeakSobolev_exists_directional_acl_representative_of_rectifying_coordinates
      hK hQ hP hQP hPΩ hΩ_open hweak e he hu hdu hsegments

/--
%%handwave
name:
  Sobolev functions have directional absolutely continuous representatives
statement:
  For a scalar weak \(W^{1,2}\) function on a Euclidean region, assume the
  function and its directional weak derivative in a direction \(h\) are
  square-integrable on a compact set \(P\), assume a positive thickening of a
  compact set \(Q\) lies in \(P\), and assume every segment from a compact set
  \(K\) in the direction \(h\) remains in \(Q\).  Then there is a
  representative agreeing with the original function almost everywhere on
  \(Q\) such that, for almost every \(x\in K\),
  \[
    \tilde u(x+h)-\tilde u(x)
      =\int_0^1 D u(x+t h)h\,dt .
  \]
proof:
  Take the original representative and apply [the directional weak fundamental theorem on segments](lean:JJMath.Uniformization.scalarWeakSobolev_directional_acl_line_integral_eq_ae_kinnunen).
-/
theorem scalarWeakSobolev_exists_directional_acl_representative_on_segments
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {K Q P Ω : Set H} (hK : IsCompact K) (hQ : IsCompact Q) (hP : IsCompact P)
    (hQP : ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ Q ⊆ P)
    (hPΩ : P ⊆ Ω) (hΩ_open : IsOpen Ω)
    {u : H → ℝ} {du : H → H →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionScalar Ω u du)
    {h : H}
    (hu : MemLp u 2 (MeasureTheory.volume.restrict P))
    (hdu : MemLp (fun z ↦ du z h) 2 (MeasureTheory.volume.restrict P))
    (hsegments : ∀ x ∈ K, ∀ t : ℝ, t ∈ Set.Icc 0 1 → x + t • h ∈ Q) :
    ∃ uacl : H → ℝ,
      uacl =ᵐ[MeasureTheory.volume.restrict Q] u ∧
        ∀ᵐ z ∂MeasureTheory.volume.restrict K,
          uacl (z + h) - uacl z =
            ∫ t in Set.Icc (0 : ℝ) 1,
              du (z + t • h) h ∂MeasureTheory.volume := by
  refine ⟨u, Filter.EventuallyEq.rfl, ?_⟩
  exact
    scalarWeakSobolev_directional_acl_line_integral_eq_ae_kinnunen
      hK hQ hP hQP hPΩ hΩ_open hweak hu hdu hsegments

/--
%%handwave
name:
  Weak Sobolev functions satisfy the fundamental theorem on almost every line
statement:
  For a scalar weak \(W^{1,2}\) function on a Euclidean region, if the
  function and its directional weak derivative in a direction \(h\) are
  square-integrable on a compact set \(P\), a positive thickening of \(Q\)
  lies in \(P\), and all segments from \(K\) in that direction remain in
  \(Q\), then for almost every \(x\in K\),
  \[
    u(x+h)-u(x)=\int_0^1 D u(x+t h)h\,dt .
  \]
proof:
  Apply [the weak fundamental theorem on almost every segment](lean:JJMath.Uniformization.scalarWeakSobolev_directional_acl_line_integral_eq_ae_kinnunen).
-/
theorem scalarWeakSobolev_directional_acl_line_integral_eq_ae
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {K Q P Ω : Set H} (hK : IsCompact K) (hQ : IsCompact Q) (hP : IsCompact P)
    (hQP : ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ Q ⊆ P)
    (hPΩ : P ⊆ Ω) (hΩ_open : IsOpen Ω)
    {u : H → ℝ} {du : H → H →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionScalar Ω u du)
    {h : H}
    (hu : MemLp u 2 (MeasureTheory.volume.restrict P))
    (hdu : MemLp (fun z ↦ du z h) 2 (MeasureTheory.volume.restrict P))
    (hsegments : ∀ x ∈ K, ∀ t : ℝ, t ∈ Set.Icc 0 1 → x + t • h ∈ Q) :
    ∀ᵐ z ∂MeasureTheory.volume.restrict K,
      u (z + h) - u z =
        ∫ t in Set.Icc (0 : ℝ) 1,
          du (z + t • h) h ∂MeasureTheory.volume := by
  exact
    scalarWeakSobolev_directional_acl_line_integral_eq_ae_kinnunen
      hK hQ hP hQP hPΩ hΩ_open hweak hu hdu hsegments

/--
%%handwave
name:
  Absolutely continuous line representatives give a segment-integral bound
statement:
  For a scalar weak \(W^{1,2}\) function on a Euclidean region, if the
  function and its directional weak derivative in a direction \(h\) are
  square-integrable on a compact set \(P\), a positive thickening of \(Q\)
  lies in \(P\), and all segments from \(K\) in that direction remain in
  \(Q\), then for almost every \(x\in K\),
  \[
    |u(x+h)-u(x)|
      \le \int_0^1 |D u(x+t h)h|\,dt .
  \]
proof:
  Use [the segment identity for the weak Sobolev function](lean:JJMath.Uniformization.scalarWeakSobolev_directional_acl_line_integral_eq_ae),
  then take norms and apply the triangle inequality for the integral.
-/
theorem scalarWeakSobolev_directional_acl_segmentIntegral_bound_ae
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {K Q P Ω : Set H} (hK : IsCompact K) (hQ : IsCompact Q) (hP : IsCompact P)
    (hQP : ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ Q ⊆ P)
    (hPΩ : P ⊆ Ω) (hΩ_open : IsOpen Ω)
    {u : H → ℝ} {du : H → H →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionScalar Ω u du)
    {h : H}
    (hu : MemLp u 2 (MeasureTheory.volume.restrict P))
    (hdu : MemLp (fun z ↦ du z h) 2 (MeasureTheory.volume.restrict P))
    (hsegments : ∀ x ∈ K, ∀ t : ℝ, t ∈ Set.Icc 0 1 → x + t • h ∈ Q) :
    ∀ᵐ z ∂MeasureTheory.volume.restrict K,
      ‖u (z + h) - u z‖ ≤
        euclideanSegmentIntegralAlong (fun y : H ↦ du y h) h z := by
  have hline :
      ∀ᵐ z ∂MeasureTheory.volume.restrict K,
        u (z + h) - u z =
          ∫ t in Set.Icc (0 : ℝ) 1,
            du (z + t • h) h ∂MeasureTheory.volume :=
    scalarWeakSobolev_directional_acl_line_integral_eq_ae
      hK hQ hP hQP hPΩ hΩ_open hweak hu hdu hsegments
  filter_upwards [hline] with z hz
  rw [hz]
  simpa [euclideanSegmentIntegralAlong] using
    (norm_integral_le_integral_norm
      (μ := MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
      (f := fun t : ℝ ↦ du (z + t • h) h))

/--
%%handwave
name:
  Segment-integral \(L^2\) bound from Fubini and translation invariance
statement:
  If every segment \(x+t h\), \(x\in K\), \(0\le t\le1\), remains in \(Q\),
  then the \(L^2(K)\)-norm of
  \[
    x\mapsto \int_0^1 |f(x+t h)|\,dt
  \]
  is bounded by the \(L^2(Q)\)-norm of \(f\).
proof:
  Cauchy--Schwarz in the segment parameter gives
  \[
    \left(\int_0^1 |f(x+t h)|\,dt\right)^2
      \le \int_0^1 |f(x+t h)|^2\,dt .
  \]
  Integrating over \(K\), applying Tonelli, and translating \(K+t h\) into
  \(Q\) bounds each time slice by the \(L^2(Q)\)-norm of \(f\).  Since the
  interval has length one, this gives the stated estimate.
-/
theorem euclideanSegmentIntegral_eLpNorm_le_of_segments
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {K Q : Set H} (hK : IsCompact K) (hQ : IsCompact Q)
    {f : H → ℝ} {h : H}
    (hf : MemLp f 2 (MeasureTheory.volume.restrict Q))
    (hsegments : ∀ x ∈ K, ∀ t : ℝ, t ∈ Set.Icc 0 1 → x + t • h ∈ Q) :
    eLpNorm (euclideanSegmentIntegralAlong f h)
        2 (MeasureTheory.volume.restrict K) ≤
      eLpNorm f 2 (MeasureTheory.volume.restrict Q) := by
  have hsq :
      ∫⁻ z, ‖euclideanSegmentIntegralAlong f h z‖ₑ ^ (2 : ℝ)
          ∂MeasureTheory.volume.restrict K ≤
        ∫⁻ z, ‖f z‖ₑ ^ (2 : ℝ) ∂MeasureTheory.volume.restrict Q :=
    euclideanSegmentIntegral_lintegral_sq_le_of_segments hK hQ hf hsegments
  have hp0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have hp_top : (2 : ℝ≥0∞) ≠ (∞ : ℝ≥0∞) :=
    ENNReal.coe_ne_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top]
  exact ENNReal.rpow_le_rpow hsq (by norm_num)

/--
%%handwave
name:
  Directional difference quotients for \(L^2\) weak derivatives
statement:
  Suppose \(K,Q,P\) are compact Euclidean sets, a positive thickening of
  \(Q\) lies in \(P\subset\Omega\), and every segment from \(x\in K\) in a
  fixed direction \(h\) remains in \(Q\).  If \(u\) and the directional
  component \(D u(\cdot)h\) are \(L^2\) on \(P\), then the \(L^2(K)\)-norm of
  \(u(\cdot+h)-u\) is bounded by the \(L^2(Q)\)-norm of \(D u(\cdot)h\).
proof:
  Combine [the almost-everywhere segment-integral bound](lean:JJMath.Uniformization.scalarWeakSobolev_directional_acl_segmentIntegral_bound_ae)
  with [the \(L^2\) estimate for segment integrals](lean:JJMath.Uniformization.euclideanSegmentIntegral_eLpNorm_le_of_segments).
-/
theorem scalarWeakSobolev_directional_difference_quotient_eLpNorm_le_of_segments_memLp
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {K Q P Ω : Set H} (hK : IsCompact K) (hQ : IsCompact Q) (hP : IsCompact P)
    (hQP : ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ Q ⊆ P)
    (hPΩ : P ⊆ Ω) (hΩ_open : IsOpen Ω)
    {u : H → ℝ} {du : H → H →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionScalar Ω u du)
    {h : H}
    (hu : MemLp u 2 (MeasureTheory.volume.restrict P))
    (hdu : MemLp (fun z ↦ du z h) 2 (MeasureTheory.volume.restrict P))
    (hsegments : ∀ x ∈ K, ∀ t : ℝ, t ∈ Set.Icc 0 1 → x + t • h ∈ Q) :
    eLpNorm (fun z ↦ u (z + h) - u z) 2
      (MeasureTheory.volume.restrict K) ≤
        eLpNorm (fun z ↦ du z h) 2 (MeasureTheory.volume.restrict Q) := by
  have hacl :
      ∀ᵐ z ∂MeasureTheory.volume.restrict K,
        ‖u (z + h) - u z‖ ≤
          euclideanSegmentIntegralAlong (fun y : H ↦ du y h) h z :=
    scalarWeakSobolev_directional_acl_segmentIntegral_bound_ae
      hK hQ hP hQP hPΩ hΩ_open hweak hu hdu hsegments
  have hQP_subset : Q ⊆ P := subset_of_exists_cthickening_subset hQP
  have hdu_Q : MemLp (fun z ↦ du z h) 2 (MeasureTheory.volume.restrict Q) :=
    hdu.mono_measure (Measure.restrict_mono hQP_subset le_rfl)
  calc
    eLpNorm (fun z ↦ u (z + h) - u z) 2
        (MeasureTheory.volume.restrict K)
        ≤ eLpNorm (euclideanSegmentIntegralAlong (fun y : H ↦ du y h) h)
            2 (MeasureTheory.volume.restrict K) :=
          eLpNorm_mono_ae_real hacl
    _ ≤ eLpNorm (fun z ↦ du z h) 2 (MeasureTheory.volume.restrict Q) :=
          euclideanSegmentIntegral_eLpNorm_le_of_segments
            hK hQ hdu_Q hsegments

/--
%%handwave
name:
  Directional difference quotients are bounded by directional weak derivatives
statement:
  Let \(K,Q,P\) be compact Euclidean sets, with a positive thickening of
  \(Q\) contained in \(P\subset\Omega\), and assume every segment
  \(x+t h\), \(x\in K\), \(0\le t\le 1\), stays in \(Q\).  If \(u\) has weak
  derivative \(D u\), then the \(L^2(K)\)-norm of \(u(\cdot+h)-u\) is bounded
  by the \(L^2(P)\)-norm of the directional derivative \(D u(\cdot)h\).
proof:
  If the directional weak derivative has finite \(L^2(P)\)-norm, apply [the \(L^2\) difference-quotient estimate with an explicit \(L^2\) hypothesis](lean:JJMath.Uniformization.scalarWeakSobolev_directional_difference_quotient_eLpNorm_le_of_segments_memLp)
  and then enlarge the measure from \(Q\) to \(P\).  If the norm is infinite,
  the estimate is trivial.
-/
theorem scalarWeakSobolev_directional_difference_quotient_eLpNorm_le_of_segments
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {K Q P Ω : Set H} (hK : IsCompact K) (hQ : IsCompact Q) (hP : IsCompact P)
    (hQP : ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ Q ⊆ P)
    (hPΩ : P ⊆ Ω) (hΩ_open : IsOpen Ω)
    {u : H → ℝ} {du : H → H →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionScalar Ω u du)
    {h : H}
    (hu : MemLp u 2 (MeasureTheory.volume.restrict P))
    (hsegments : ∀ x ∈ K, ∀ t : ℝ, t ∈ Set.Icc 0 1 → x + t • h ∈ Q) :
    eLpNorm (fun z ↦ u (z + h) - u z) 2
      (MeasureTheory.volume.restrict K) ≤
        eLpNorm (fun z ↦ du z h) 2 (MeasureTheory.volume.restrict P) := by
  by_cases hfinite :
      eLpNorm (fun z ↦ du z h) 2 (MeasureTheory.volume.restrict P) = (∞ : ℝ≥0∞)
  · rw [hfinite]
    exact le_top
  · have hdu_mem :
        MemLp (fun z ↦ du z h) 2 (MeasureTheory.volume.restrict P) :=
      scalarWeakSobolev_directionalDerivative_memLp_of_eLpNorm_ne_top
        hP hPΩ hΩ_open hweak hfinite
    have hinner :
        eLpNorm (fun z ↦ u (z + h) - u z) 2
            (MeasureTheory.volume.restrict K) ≤
          eLpNorm (fun z ↦ du z h) 2 (MeasureTheory.volume.restrict Q) :=
      scalarWeakSobolev_directional_difference_quotient_eLpNorm_le_of_segments_memLp
        hK hQ hP hQP hPΩ hΩ_open hweak hu hdu_mem hsegments
    have hQP_subset : Q ⊆ P := subset_of_exists_cthickening_subset hQP
    exact hinner.trans
      (eLpNorm_mono_measure (fun z ↦ du z h)
        (Measure.restrict_mono hQP_subset le_rfl))

/--
%%handwave
name:
  Difference quotients are bounded by weak derivatives
statement:
  Let \(K,Q,P\) be compact Euclidean sets, with a positive thickening of
  \(Q\) contained in \(P\subset\Omega\), and assume every segment
  \(x+t h\), \(x\in K\), \(0\le t\le 1\), stays in \(Q\).  If \(u\) has weak
  derivative \(D u\), then the \(L^2(K)\)-norm of \(u(\cdot+h)-u\) is bounded
  by \(\|h\|\) times the \(L^2(P)\)-norm of \(D u\).
proof:
  Combine the directional difference-quotient estimate with the pointwise
  operator norm bound \(|D u(x)h|\le \|h\|\,\|D u(x)\|\), then use homogeneity
  of the \(L^2\) seminorm under constant scalar multiplication.
-/
theorem scalarWeakSobolev_difference_quotient_eLpNorm_le_of_segments
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {K Q P Ω : Set H} (hK : IsCompact K) (hQ : IsCompact Q) (hP : IsCompact P)
    (hQP : ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ Q ⊆ P)
    (hPΩ : P ⊆ Ω) (hΩ_open : IsOpen Ω)
    {u : H → ℝ} {du : H → H →L[ℝ] ℝ}
    (hweak : IsWeakDerivativeOnEuclideanRegionScalar Ω u du)
    {h : H}
    (hu : MemLp u 2 (MeasureTheory.volume.restrict P))
    (hsegments : ∀ x ∈ K, ∀ t : ℝ, t ∈ Set.Icc 0 1 → x + t • h ∈ Q) :
    eLpNorm (fun z ↦ u (z + h) - u z) 2
      (MeasureTheory.volume.restrict K) ≤
        ENNReal.ofReal ‖h‖ *
          eLpNorm du 2 (MeasureTheory.volume.restrict P) := by
  calc
    eLpNorm (fun z ↦ u (z + h) - u z) 2
        (MeasureTheory.volume.restrict K)
        ≤ eLpNorm (fun z ↦ du z h) 2
            (MeasureTheory.volume.restrict P) :=
          scalarWeakSobolev_directional_difference_quotient_eLpNorm_le_of_segments
            hK hQ hP hQP hPΩ hΩ_open hweak hu hsegments
    _ ≤ eLpNorm ((‖h‖ : ℝ) • du) 2
          (MeasureTheory.volume.restrict P) := by
          exact eLpNorm_mono (fun z ↦ by
            calc
              ‖du z h‖ ≤ ‖du z‖ * ‖h‖ := (du z).le_opNorm h
              _ = ‖h‖ * ‖du z‖ := mul_comm _ _
              _ = ‖(((‖h‖ : ℝ) • du) z)‖ := by
                    simp [Pi.smul_apply, norm_smul])
    _ = ENNReal.ofReal ‖h‖ *
          eLpNorm du 2 (MeasureTheory.volume.restrict P) := by
          simpa [Real.norm_of_nonneg (norm_nonneg h)] using
            (eLpNorm_const_smul (c := (‖h‖ : ℝ)) (f := du)
              (p := 2) (μ := MeasureTheory.volume.restrict P))

/--
%%handwave
name:
  Weak Sobolev bounds give a linear translation modulus
statement:
  Let a compact Euclidean set lie in the interior of a compact subset of an
  open region.  If a sequence of scalar weak \(W^{1,2}\) functions has
  uniformly bounded weak derivatives on the larger compact set, then its
  translation increments on the smaller compact set are bounded by a finite
  constant times the translation length.
proof:
  Choose a compact thickening of \(K\) inside \(Q\); short segments from \(K\)
  stay in that thickening.  Apply [the difference quotient bound in terms of the weak derivative](lean:JJMath.Uniformization.scalarWeakSobolev_difference_quotient_eLpNorm_le_of_segments)
  and the uniform derivative bound.
-/
theorem scalarWeakSobolevBound_linear_translation_modulus_on_compact
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {K Q Ω : Set H} (hK : IsCompact K) (hKQ : K ⊆ interior Q)
    (hQΩ : Q ⊆ Ω) (hQ : IsCompact Q) (hΩ_open : IsOpen Ω)
    (u : ℕ → H → ℝ) (du : ℕ → H → H →L[ℝ] ℝ)
    (hweak : ∀ n : ℕ, IsWeakDerivativeOnEuclideanRegionScalar Ω (u n) (du n))
    (hu_mem : ∀ n : ℕ, MemLp (u n) 2 (MeasureTheory.volume.restrict Q))
    {C : ℝ≥0∞} (hC_top : C < ⊤)
    (hdu_bound : ∀ n : ℕ,
      eLpNorm (du n) 2 (MeasureTheory.volume.restrict Q) ≤ C) :
    ∃ A : ℝ≥0∞, A < ⊤ ∧
      ∃ ρ : ℝ, 0 < ρ ∧ ∀ h : H, ‖h‖ < ρ → ∀ n : ℕ,
        eLpNorm (fun z ↦ u n (z + h) - u n z) 2
          (MeasureTheory.volume.restrict K) ≤ ENNReal.ofReal ‖h‖ * A := by
  rcases hK.exists_cthickening_subset_open isOpen_interior hKQ with
    ⟨η, hη_pos, hη_sub_intQ⟩
  let S : Set H := Metric.cthickening (η / 2) K
  have hS : IsCompact S := hK.cthickening
  have hη_half_pos : 0 < η / 2 := by linarith
  have hη_half_le : η / 2 ≤ η := by linarith
  have hS_intQ : S ⊆ interior Q := by
    exact (Metric.cthickening_mono hη_half_le K).trans hη_sub_intQ
  rcases hS.exists_cthickening_subset_open isOpen_interior hS_intQ with
    ⟨δ, hδ_pos, hδ_sub_intQ⟩
  have hSQ : ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ S ⊆ Q :=
    ⟨δ, hδ_pos, hδ_sub_intQ.trans interior_subset⟩
  let ρ : ℝ := η / 2
  have hρ_pos : 0 < ρ := by
    simpa [ρ] using hη_half_pos
  refine ⟨C, hC_top, ρ, hρ_pos, fun h hh n ↦ ?_⟩
  have hsegments :
      ∀ x ∈ K, ∀ t : ℝ, t ∈ Set.Icc 0 1 → x + t • h ∈ S := by
    intro x hx t ht
    have ht_abs : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
    have hdist : dist (x + t • h) x ≤ η / 2 := by
      calc
        dist (x + t • h) x = ‖t • h‖ := by
          simp [dist_eq_norm]
        _ = |t| * ‖h‖ := norm_smul t h
        _ ≤ 1 * ‖h‖ := mul_le_mul_of_nonneg_right ht_abs (norm_nonneg h)
        _ = ‖h‖ := one_mul ‖h‖
        _ ≤ η / 2 := by simpa [ρ] using le_of_lt hh
    exact Metric.mem_cthickening_of_dist_le (x + t • h) x (η / 2) K hx hdist
  exact (scalarWeakSobolev_difference_quotient_eLpNorm_le_of_segments
    hK hS hQ hSQ hQΩ hΩ_open (hweak n) (hu_mem n) hsegments).trans
      (mul_le_mul_right (hdu_bound n) (ENNReal.ofReal ‖h‖))

/--
%%handwave
name:
  Weak Sobolev bounds give translation tightness
statement:
  On a compact set lying in the interior of a compact subset of an open
  Euclidean region, a uniform scalar weak \(W^{1,2}\) bound gives uniform
  \(L^2\) translation tightness on the smaller compact set.
proof:
  Apply [the linear translation modulus from the weak Sobolev bound](lean:JJMath.Uniformization.scalarWeakSobolevBound_linear_translation_modulus_on_compact)
  and convert that linear modulus into translation tightness.
-/
theorem scalarWeakSobolevBound_translation_tight_on_compact
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {K Q Ω : Set H} (hK : IsCompact K) (hKQ : K ⊆ interior Q)
    (hQΩ : Q ⊆ Ω) (hQ : IsCompact Q) (hΩ_open : IsOpen Ω)
    (u : ℕ → H → ℝ) (du : ℕ → H → H →L[ℝ] ℝ)
    (hweak : ∀ n : ℕ, IsWeakDerivativeOnEuclideanRegionScalar Ω (u n) (du n))
    (hbounded : BoundedInEuclideanLocalSobolevH1Scalar Q u du) :
    EuclideanL2TranslationTightOnCompact K u := by
  rcases BoundedInEuclideanLocalSobolevH1WithValues.derivative_eLpNorm_bound hbounded with
    ⟨C, hC_top, hdu_bound⟩
  have hu_mem : ∀ n : ℕ, MemLp (u n) 2 (MeasureTheory.volume.restrict Q) := by
    intro n
    exact BoundedInEuclideanLocalSobolevH1WithValues.value_memLp hbounded n
  rcases scalarWeakSobolevBound_linear_translation_modulus_on_compact
      hK hKQ hQΩ hQ hΩ_open u du hweak hu_mem hC_top hdu_bound with
    ⟨A, hA_top, ρ, hρ, hmod⟩
  exact euclideanL2TranslationTightFamilyOnCompactForMeasure_of_linear_modulus
    hA_top hρ hmod

/--
%%handwave
name:
  Compact containment in \(L^2\) gives a convergent subsequence
statement:
  If the \(L^2\)-classes of a sequence of scalar functions all lie in one
  compact subset of \(L^2\) on a set, then the original sequence has a
  subsequence converging strongly in \(L^2\) on that set.
proof:
  Apply sequential compactness of compact subsets of the \(L^2\) metric space
  and translate convergence in \(L^2\) back to convergence of the
  \(L^2\)-seminorm of representatives.
-/
theorem euclideanL2CompactSet_subsequence_on_compact
    {H : Type} [MeasureSpace H]
    {K : Set H} (u : ℕ → H → ℝ)
    (hmem : ∀ n : ℕ, MemLp (u n) 2 (MeasureTheory.volume.restrict K))
    (S : Set (Lp ℝ 2 (MeasureTheory.volume.restrict K)))
    (hS : IsCompact S)
    (hS_mem : ∀ n : ℕ, (hmem n).toLp (u n) ∈ S) :
    ∃ (uLim : H → ℝ) (φ : ℕ → ℕ),
      StrictMono φ ∧
        TendstoInEuclideanLocalL2Scalar K (fun n z ↦ u (φ n) z) uLim := by
  let μ : Measure H := MeasureTheory.volume.restrict K
  let x : ℕ → Lp ℝ 2 μ := fun n ↦ (hmem n).toLp (u n)
  have hx : ∀ n : ℕ, x n ∈ S := by
    intro n
    simpa [x, μ] using hS_mem n
  rcases hS.tendsto_subseq hx with ⟨a, _haS, φ, hφ, hlim⟩
  refine ⟨(a : H → ℝ), φ, hφ, ?_⟩
  dsimp [TendstoInEuclideanLocalL2Scalar, TendstoInEuclideanLocalL2WithValues]
  have hlim' :
      Filter.Tendsto (fun n : ℕ ↦ (hmem (φ n)).toLp (u (φ n))) Filter.atTop (𝓝 a) := by
    simpa [x, μ, Function.comp_def] using hlim
  have hlim'' :
      Filter.Tendsto (fun n : ℕ ↦ (hmem (φ n)).toLp (u (φ n)))
        Filter.atTop (𝓝 ((Lp.memLp a).toLp (a : H → ℝ))) := by
    simpa [Lp.toLp_coeFn] using hlim'
  exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (μ := μ) (p := 2)
    (fun n : ℕ ↦ u (φ n)) (fun n : ℕ ↦ hmem (φ n))
    (a : H → ℝ) (Lp.memLp a)).mp hlim''

/--
%%handwave
name:
  Compact containment in vector-valued \(L^2\) gives a convergent subsequence
statement:
  If the \(L^2(K;E)\)-classes of a sequence of \(E\)-valued functions all lie
  in one compact subset of \(L^2(K;E)\), then the original sequence has a
  subsequence converging strongly in \(L^2(K;E)\).
proof:
  Apply sequential compactness of compact subsets of \(L^2(K;E)\) and
  translate convergence in \(L^2\) back to convergence of the \(L^2\)-seminorm
  of representatives.
-/
theorem euclideanL2CompactSet_subsequence_on_compact_with_values
    {H E : Type} [MeasureSpace H] [NormedAddCommGroup E]
    {K : Set H} (u : ℕ → H → E)
    (hmem : ∀ n : ℕ, MemLp (u n) 2 (MeasureTheory.volume.restrict K))
    (S : Set (Lp E 2 (MeasureTheory.volume.restrict K)))
    (hS : IsCompact S)
    (hS_mem : ∀ n : ℕ, (hmem n).toLp (u n) ∈ S) :
    ∃ (uLim : H → E) (φ : ℕ → ℕ),
      StrictMono φ ∧
        TendstoInEuclideanLocalL2WithValues K (fun n z ↦ u (φ n) z) uLim := by
  let μ : Measure H := MeasureTheory.volume.restrict K
  let x : ℕ → Lp E 2 μ := fun n ↦ (hmem n).toLp (u n)
  have hx : ∀ n : ℕ, x n ∈ S := by
    intro n
    simpa [x, μ] using hS_mem n
  rcases hS.tendsto_subseq hx with ⟨a, _haS, φ, hφ, hlim⟩
  refine ⟨(a : H → E), φ, hφ, ?_⟩
  dsimp [TendstoInEuclideanLocalL2WithValues]
  have hlim' :
      Filter.Tendsto (fun n : ℕ ↦ (hmem (φ n)).toLp (u (φ n))) Filter.atTop (𝓝 a) := by
    simpa [x, μ, Function.comp_def] using hlim
  have hlim'' :
      Filter.Tendsto (fun n : ℕ ↦ (hmem (φ n)).toLp (u (φ n)))
        Filter.atTop (𝓝 ((Lp.memLp a).toLp (a : H → E))) := by
    simpa [Lp.toLp_coeFn] using hlim'
  exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (μ := μ) (p := 2)
    (fun n : ℕ ↦ u (φ n)) (fun n : ℕ ↦ hmem (φ n))
    (a : H → E) (Lp.memLp a)).mp hlim''

/--
%%handwave
name:
  Compact containment in \(L^2(K;E)\) gives a manifold-local subsequence
statement:
  Let \(K\) be a measurable subset of a measured space.  If the
  \(L^2(K;E)\)-classes of a sequence of \(E\)-valued maps all lie in one
  compact subset of \(L^2(K;E)\), then a subsequence converges strongly in
  \(L^2(K;E)\).
proof:
  Apply sequential compactness of the compact subset of \(L^2(K;E)\).  The
  limit is represented by its \(L^2\) function representative, and convergence
  in the \(L^2\) metric is exactly convergence of the \(L^2\)-seminorm of the
  difference of representatives.
-/
theorem l2CompactSet_subsequence_on_set_with_values
    {X E : Type} [MeasurableSpace X] [NormedAddCommGroup E]
    {μ : Measure X} {K : Set X} (u : ℕ → X → E)
    (hmem : ∀ n : ℕ, MemLp (u n) 2 (μ.restrict K))
    (S : Set (Lp E 2 (μ.restrict K)))
    (hS : IsCompact S)
    (hS_mem : ∀ n : ℕ, (hmem n).toLp (u n) ∈ S) :
    ∃ (uLim : X → E) (φ : ℕ → ℕ),
      StrictMono φ ∧
        TendstoInLocalL2OnManifoldWithValues μ K (fun n x ↦ u (φ n) x) uLim := by
  let μK : Measure X := μ.restrict K
  let x : ℕ → Lp E 2 μK := fun n ↦ (hmem n).toLp (u n)
  have hx : ∀ n : ℕ, x n ∈ S := by
    intro n
    simpa [x, μK] using hS_mem n
  rcases hS.tendsto_subseq hx with ⟨a, _haS, φ, hφ, hlim⟩
  refine ⟨(a : X → E), φ, hφ, ?_⟩
  dsimp [TendstoInLocalL2OnManifoldWithValues]
  have hlim' :
      Filter.Tendsto (fun n : ℕ ↦ (hmem (φ n)).toLp (u (φ n))) Filter.atTop (𝓝 a) := by
    simpa [x, μK, Function.comp_def] using hlim
  have hlim'' :
      Filter.Tendsto (fun n : ℕ ↦ (hmem (φ n)).toLp (u (φ n)))
        Filter.atTop (𝓝 ((Lp.memLp a).toLp (a : X → E))) := by
    simpa [Lp.toLp_coeFn] using hlim'
  exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (μ := μK) (p := 2)
    (fun n : ℕ ↦ u (φ n)) (fun n : ℕ ↦ hmem (φ n))
    (a : X → E) (Lp.memLp a)).mp hlim''

/--
%%handwave
name:
  Finite-dimensional approximation gives finite nets
statement:
  Let a family in a normed real vector space be uniformly approximable, at
  every positive scale, by elements lying in a bounded subset of some
  finite-dimensional subspace.  Then the family admits finite nets at every
  positive scale.
proof:
  In a finite-dimensional normed space, closed bounded balls are compact and
  hence totally bounded.  Approximate the finite-dimensional approximants by a
  finite net in that ball, then use the triangle inequality.
-/
theorem finite_L2_net_of_uniform_finiteDimensional_approx
    {ι Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (x : ι → Y)
    (happrox : ∀ ε : ℝ, 0 < ε →
      ∃ V : Submodule ℝ Y, FiniteDimensional ℝ V ∧
        ∃ R : ℝ, 0 ≤ R ∧
          ∀ i : ι, ∃ v : V, ‖(v : Y)‖ ≤ R ∧ dist (x i) (v : Y) < ε) :
    ∀ ε : ℝ, 0 < ε →
      ∃ t : Set Y, t.Finite ∧
        Set.range x ⊆ ⋃ y ∈ t, Metric.ball y ε := by
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  rcases happrox (ε / 2) hε2 with ⟨V, hVfin, R, _hR_nonneg, hVapprox⟩
  letI : FiniteDimensional ℝ V := hVfin
  haveI : ProperSpace V := FiniteDimensional.proper ℝ V
  have hball_totallyBounded : TotallyBounded (Metric.closedBall (0 : V) R) :=
    (isCompact_closedBall (0 : V) R).totallyBounded
  rcases Metric.totallyBounded_iff.mp hball_totallyBounded (ε / 2) hε2 with
    ⟨tV, htV_finite, htV_cover⟩
  let t : Set Y := ((fun v : V ↦ (v : Y)) '' tV)
  refine ⟨t, htV_finite.image _, ?_⟩
  rintro y ⟨i, rfl⟩
  rcases hVapprox i with ⟨v, hv_norm, hv_close⟩
  have hv_ball : v ∈ Metric.closedBall (0 : V) R := by
    rw [Metric.mem_closedBall]
    change dist (v : Y) (0 : Y) ≤ R
    simpa [dist_eq_norm] using hv_norm
  have hv_cover := htV_cover hv_ball
  simp only [Set.mem_iUnion] at hv_cover
  rcases hv_cover with ⟨w, hw_mem, hvw_ball⟩
  have hvw_close : dist (v : Y) (w : Y) < ε / 2 := by
    simpa using hvw_ball
  have hdist_le : dist (x i) (w : Y) ≤ dist (x i) (v : Y) + dist (v : Y) (w : Y) :=
    dist_triangle _ _ _
  have hdist_lt : dist (x i) (w : Y) < ε := by
    exact lt_of_le_of_lt hdist_le (by linarith)
  simp only [Set.mem_iUnion, Set.mem_image, Metric.mem_ball, t]
  exact ⟨(w : Y), ⟨⟨w, hw_mem, rfl⟩, hdist_lt⟩⟩

/--
%%handwave
name:
  Uniform finite-dimensional approximation gives total boundedness
statement:
  Let a family in a normed real vector space be uniformly approximable, at
  every positive scale, by elements lying in a bounded subset of some
  finite-dimensional subspace.  Then the family is totally bounded.
proof:
  The previous finite-net construction gives finite nets at every positive
  scale.  Apply the metric characterization of total boundedness.
-/
theorem totallyBounded_of_uniform_finiteDimensional_approx
    {ι Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (x : ι → Y)
    (happrox : ∀ ε : ℝ, 0 < ε →
      ∃ V : Submodule ℝ Y, FiniteDimensional ℝ V ∧
        ∃ R : ℝ, 0 ≤ R ∧
          ∀ i : ι, ∃ v : V, ‖(v : Y)‖ ≤ R ∧ dist (x i) (v : Y) < ε) :
    TotallyBounded (Set.range x) := by
  exact Metric.totallyBounded_iff.2
    (finite_L2_net_of_uniform_finiteDimensional_approx x happrox)

/--
%%handwave
name:
  Finite-rank approximation gives finite-dimensional approximation
statement:
  Let a sequence in a normed real vector space be uniformly approximable, at
  every positive scale, by finite-rank continuous linear images of itself.
  Then the sequence is uniformly approximable, at every positive scale, by
  finite-dimensional subspaces.
proof:
  For a fixed scale, take the range of the finite-rank operator as the
  finite-dimensional subspace.  Each approximant is the image of the
  corresponding element under that operator.
-/
theorem finiteRank_approx_gives_uniform_finiteDimensional_approx
    {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (x : ℕ → Y)
    (happrox : ∀ ε : ℝ, 0 < ε →
      ∃ A : Y →L[ℝ] Y, FiniteDimensional ℝ A.range ∧
        ∀ n : ℕ, dist (x n) (A (x n)) < ε) :
    ∀ ε : ℝ, 0 < ε →
      ∃ V : Submodule ℝ Y, FiniteDimensional ℝ V ∧
        ∀ n : ℕ, ∃ v : V, dist (x n) (v : Y) < ε := by
  intro ε hε
  rcases happrox ε hε with ⟨A, hAfin, hAapprox⟩
  refine ⟨A.range, hAfin, ?_⟩
  intro n
  refine ⟨⟨A (x n), ?_⟩, ?_⟩
  · exact LinearMap.mem_range_self (A : Y →ₗ[ℝ] Y) (x n)
  · simpa using hAapprox n

/--
%%handwave
name:
  Bounded finite-rank approximation gives finite nets
statement:
  Let a bounded family in a normed real vector space be uniformly
  approximable, at every positive scale, by finite-rank continuous linear
  images of itself.  Then the family admits finite nets at every positive
  scale.
proof:
  For each scale, take the range of the finite-rank operator.  The
  approximants lie in this finite-dimensional range, and the triangle
  inequality bounds their norms by the uniform bound for the original family
  plus the approximation error.  Finite-dimensional bounded balls are totally
  bounded, so the preceding finite-dimensional net construction applies.
-/
theorem finite_L2_net_of_bounded_uniform_finiteRank_approx
    {ι Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (x : ι → Y)
    (hbounded : ∃ R : ℝ, 0 ≤ R ∧ ∀ i : ι, ‖x i‖ ≤ R)
    (happrox : ∀ ε : ℝ, 0 < ε →
      ∃ A : Y →L[ℝ] Y, FiniteDimensional ℝ A.range ∧
        ∀ i : ι, dist (x i) (A (x i)) < ε) :
    ∀ ε : ℝ, 0 < ε →
      ∃ t : Set Y, t.Finite ∧
        Set.range x ⊆ ⋃ y ∈ t, Metric.ball y ε := by
  rcases hbounded with ⟨R, hR_nonneg, hR_bound⟩
  refine finite_L2_net_of_uniform_finiteDimensional_approx x ?_
  intro ε hε
  rcases happrox ε hε with ⟨A, hAfin, hAapprox⟩
  refine ⟨A.range, hAfin, R + ε, add_nonneg hR_nonneg hε.le, ?_⟩
  intro i
  refine ⟨⟨A (x i), LinearMap.mem_range_self (A : Y →ₗ[ℝ] Y) (x i)⟩, ?_, hAapprox i⟩
  have hAx_norm_le : ‖A (x i)‖ ≤ dist (x i) (A (x i)) + ‖x i‖ := by
    have htri : dist (A (x i)) 0 ≤ dist (A (x i)) (x i) + dist (x i) 0 :=
      dist_triangle _ _ _
    simpa [dist_comm, dist_eq_norm] using htri
  calc
    ‖A (x i)‖ ≤ dist (x i) (A (x i)) + ‖x i‖ := hAx_norm_le
    _ ≤ ε + R := add_le_add (le_of_lt (hAapprox i)) (hR_bound i)
    _ = R + ε := by ring

/--
%%handwave
name:
  Cross-space finite-rank approximation gives finite nets
statement:
  Let a sequence in one normed vector space be approximated by the image,
  under finite-rank operators, of a bounded sequence in another normed vector
  space.  Then the original sequence admits finite nets at every positive
  scale.
proof:
  At a given scale, the approximating finite-rank operator maps the bounded
  sequence into a bounded subset of its finite-dimensional range.  A bounded
  subset of a finite-dimensional normed space is totally bounded, and adding
  the uniform approximation error gives a finite net for the original
  sequence.
-/
theorem finite_L2_net_of_bounded_uniform_crossFiniteRank_approx
    {ι Y Z : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (x : ι → Y) (z : ι → Z)
    (hzbounded : ∃ R : ℝ, 0 ≤ R ∧ ∀ i : ι, ‖z i‖ ≤ R)
    (happrox :
      ∀ ε : ℝ, 0 < ε →
        ∃ A : Z →L[ℝ] Y, FiniteDimensional ℝ A.range ∧
          ∀ i : ι, dist (x i) (A (z i)) < ε) :
    ∀ ε : ℝ, 0 < ε →
      ∃ t : Set Y, t.Finite ∧
        Set.range x ⊆ ⋃ y ∈ t, Metric.ball y ε := by
  rcases hzbounded with ⟨R, hR_nonneg, hR_bound⟩
  refine finite_L2_net_of_uniform_finiteDimensional_approx x ?_
  intro ε hε
  rcases happrox ε hε with ⟨A, hAfin, hAapprox⟩
  let R' : ℝ := ‖A‖ * R + ε
  refine ⟨A.range, hAfin, R', ?_, ?_⟩
  · exact add_nonneg (mul_nonneg (norm_nonneg A) hR_nonneg) hε.le
  · intro i
    refine ⟨⟨A (z i), LinearMap.mem_range_self (A : Z →ₗ[ℝ] Y) (z i)⟩, ?_,
      hAapprox i⟩
    calc
      ‖A (z i)‖ ≤ ‖A‖ * ‖z i‖ := A.le_opNorm (z i)
      _ ≤ ‖A‖ * R := mul_le_mul_of_nonneg_left (hR_bound i) (norm_nonneg A)
      _ ≤ ‖A‖ * R + ε := le_add_of_nonneg_right hε.le

/--
%%handwave
name:
  Finite-rank operator represented by finitely many coefficients
statement:
  A finite family of continuous linear coefficient functionals and a finite
  family of vectors define a finite-rank continuous linear operator by taking
  the corresponding finite linear combination.
-/
noncomputable def finiteRankRepresentationOperator {ι Y : Type} [Fintype ι]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (coeff : ι → Y →L[ℝ] ℝ) (vec : ι → Y) : Y →L[ℝ] Y :=
  ∑ i, (coeff i).smulRight (vec i)

/--
%%handwave
name:
  Formula for a finitely represented operator
statement:
  An operator represented by coefficient functionals
  \(\lambda_i:Y\to\mathbb R\) and vectors \(v_i\in Y\) satisfies
  \(A(y)=\sum_i\lambda_i(y)v_i\).
proof:
  Evaluate the finite sum of rank-one continuous linear maps at \(y\).
-/
@[simp]
theorem finiteRankRepresentationOperator_apply {ι Y : Type} [Fintype ι]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (coeff : ι → Y →L[ℝ] ℝ) (vec : ι → Y) (y : Y) :
    finiteRankRepresentationOperator coeff vec y =
      ∑ i, coeff i y • vec i := by
  simp [finiteRankRepresentationOperator, ContinuousLinearMap.sum_apply]

/--
%%handwave
name:
  The represented finite-rank operator has finite-dimensional range
statement:
  The range of an operator represented by finitely many coefficient
  functionals and finitely many vectors is contained in the span of those
  vectors, and hence is finite-dimensional.
proof:
  Every value of the operator is a finite linear combination of the chosen
  vectors.
-/
theorem finiteRankRepresentationOperator_finiteDimensional_range {ι Y : Type}
    [Fintype ι] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (coeff : ι → Y →L[ℝ] ℝ) (vec : ι → Y) :
    FiniteDimensional ℝ (finiteRankRepresentationOperator coeff vec).range := by
  have hle :
      (finiteRankRepresentationOperator coeff vec).range ≤
        Submodule.span ℝ (Set.range vec) := by
    intro y hy
    rcases hy with ⟨x, rfl⟩
    change finiteRankRepresentationOperator coeff vec x ∈
      Submodule.span ℝ (Set.range vec)
    rw [finiteRankRepresentationOperator_apply]
    exact Submodule.sum_mem _ fun i _ ↦
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  letI : FiniteDimensional ℝ (Submodule.span ℝ (Set.range vec)) :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_range vec)
  exact Submodule.finiteDimensional_of_le hle

/--
%%handwave
name:
  Cross-space finite-rank operator represented by finitely many coefficients
statement:
  A finite family of continuous linear coefficient functionals on one normed
  vector space and a finite family of vectors in another normed vector space
  define a finite-rank continuous linear operator between the two spaces.
-/
noncomputable def finiteRankRepresentationOperatorBetween {ι Y Z : Type} [Fintype ι]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (coeff : ι → Y →L[ℝ] ℝ) (vec : ι → Z) : Y →L[ℝ] Z :=
  ∑ i, (coeff i).smulRight (vec i)

/--
%%handwave
name:
  Formula for a finitely represented operator between spaces
statement:
  For coefficient functionals \(\lambda_i:Y\to\mathbb R\) and target vectors
  \(v_i\in Z\), the represented operator satisfies
  \(A(y)=\sum_i\lambda_i(y)v_i\).
proof:
  Evaluate the finite sum of rank-one maps at \(y\).
-/
@[simp]
theorem finiteRankRepresentationOperatorBetween_apply {ι Y Z : Type} [Fintype ι]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (coeff : ι → Y →L[ℝ] ℝ) (vec : ι → Z) (y : Y) :
    finiteRankRepresentationOperatorBetween coeff vec y =
      ∑ i, coeff i y • vec i := by
  simp [finiteRankRepresentationOperatorBetween, ContinuousLinearMap.sum_apply]

/--
%%handwave
name:
  The cross-space represented operator has finite-dimensional range
statement:
  The range of a cross-space operator represented by finitely many
  coefficients and finitely many target vectors is contained in the span of
  the target vectors, and hence is finite-dimensional.
proof:
  Every value is a finite linear combination of the chosen target vectors.
-/
theorem finiteRankRepresentationOperatorBetween_finiteDimensional_range {ι Y Z : Type}
    [Fintype ι] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (coeff : ι → Y →L[ℝ] ℝ) (vec : ι → Z) :
    FiniteDimensional ℝ (finiteRankRepresentationOperatorBetween coeff vec).range := by
  have hle :
      (finiteRankRepresentationOperatorBetween coeff vec).range ≤
        Submodule.span ℝ (Set.range vec) := by
    intro z hz
    rcases hz with ⟨y, rfl⟩
    change finiteRankRepresentationOperatorBetween coeff vec y ∈
      Submodule.span ℝ (Set.range vec)
    rw [finiteRankRepresentationOperatorBetween_apply]
    exact Submodule.sum_mem _ fun i _ ↦
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  letI : FiniteDimensional ℝ (Submodule.span ℝ (Set.range vec)) :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_range vec)
  exact Submodule.finiteDimensional_of_le hle

/--
%%handwave
name:
  Finite nets give finite-dimensional approximation
statement:
  Let a family in a normed real vector space admit finite nets at every
  positive scale.  Then, at every positive scale, the family is uniformly
  approximable by a finite-dimensional linear subspace.
proof:
  At the chosen scale, take the finite net and let \(V\) be its linear span.
  This span is finite-dimensional.  Each element of the family lies within
  the chosen scale of one net point, and that net point belongs to \(V\).
-/
theorem finite_L2_net_gives_uniform_finiteDimensional_approx
    {ι Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (x : ι → Y)
    (hnet : ∀ ε : ℝ, 0 < ε →
      ∃ t : Set Y, t.Finite ∧
        Set.range x ⊆ ⋃ y ∈ t, Metric.ball y ε) :
    ∀ ε : ℝ, 0 < ε →
      ∃ V : Submodule ℝ Y, FiniteDimensional ℝ V ∧
        ∀ i : ι, ∃ v : V, dist (x i) (v : Y) < ε := by
  intro ε hε
  rcases hnet ε hε with ⟨t, ht_finite, hcover⟩
  refine ⟨Submodule.span ℝ t, FiniteDimensional.span_of_finite ℝ ht_finite, ?_⟩
  intro i
  have hx_cover : x i ∈ ⋃ y ∈ t, Metric.ball y ε :=
    hcover ⟨i, rfl⟩
  simp only [Set.mem_iUnion] at hx_cover
  rcases hx_cover with ⟨y, hy_t, hy_ball⟩
  refine ⟨⟨y, Submodule.subset_span hy_t⟩, ?_⟩
  simpa [Metric.mem_ball] using hy_ball

/--
%%handwave
name:
  Finite-dimensional approximation gives finite projection approximation
statement:
  Let a sequence in a real Hilbert space be uniformly approximable, at every
  positive scale, by vectors in a finite-dimensional subspace.  Then it is
  uniformly approximable at the same scale by orthogonal projections onto a
  finite-dimensional subspace.
proof:
  Choose the finite-dimensional approximating subspace.  It is complete, so it
  admits an orthogonal projection.  The projection is the closest point in the
  subspace, hence it is at least as good as any chosen approximant.  Finally
  choose an orthonormal basis of the finite-dimensional subspace.
-/
theorem finiteDimensional_approx_gives_uniform_finiteSubspaceProjection_approx
    {Y : Type} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    (x : ℕ → Y)
    (happrox : ∀ ε : ℝ, 0 < ε →
      ∃ V : Submodule ℝ Y, FiniteDimensional ℝ V ∧
        ∀ n : ℕ, ∃ v : V, dist (x n) (v : Y) < ε) :
    ∀ ε : ℝ, 0 < ε →
      ∃ m : ℕ,
        ∃ S : Submodule ℝ Y,
          ∃ hSproj : S.HasOrthogonalProjection,
            letI : S.HasOrthogonalProjection := hSproj
            ∃ _b : OrthonormalBasis (Fin m) ℝ S,
              ∀ n : ℕ, dist (x n) (S.starProjection (x n)) < ε := by
  intro ε hε
  rcases happrox ε hε with ⟨V, hVfin, hVapprox⟩
  letI : FiniteDimensional ℝ V := hVfin
  haveI : IsUniformAddGroup V := V.toAddSubgroup.isUniformAddGroup
  haveI : CompleteSpace V := FiniteDimensional.complete ℝ V
  let hVproj : V.HasOrthogonalProjection := inferInstance
  refine ⟨Module.finrank ℝ V, V, hVproj, ?_⟩
  letI : V.HasOrthogonalProjection := hVproj
  refine ⟨stdOrthonormalBasis ℝ V, ?_⟩
  intro n
  rcases hVapprox n with ⟨v, hv⟩
  have hproj_le :
      dist (x n) (V.starProjection (x n)) ≤ dist (x n) (v : Y) := by
    rw [dist_eq_norm, dist_eq_norm, V.starProjection_minimal]
    exact ciInf_le ⟨0, Set.forall_mem_range.mpr fun _ ↦ norm_nonneg _⟩ v
  exact lt_of_le_of_lt hproj_le hv

/--
%%handwave
name:
  Sequential Cauchy compactness gives total boundedness
statement:
  In a uniform space, if every sequence in a set has a Cauchy subsequence,
  then the set is totally bounded.
proof:
  If a uniform entourage admitted no finite cover of the set, one could choose
  inductively a sequence whose next term avoids all previous entourage-balls.
  No subsequence of this sequence can be Cauchy, a contradiction.
-/
theorem totallyBounded_of_forall_seq_exists_cauchySeq_subseq {Y : Type}
    [UniformSpace Y] {s : Set Y}
    (hseq : ∀ y : ℕ → Y, (∀ n : ℕ, y n ∈ s) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ CauchySeq (y ∘ φ)) :
    TotallyBounded s := by
  intro V hV
  by_contra hcover
  have hfinite :
      ∀ t : Set Y, t.Finite →
        ∃ y : Y, y ∈ s ∧ y ∉ ⋃ z ∈ t, {x | (x, z) ∈ V} := by
    intro t ht
    by_contra hbad
    apply hcover
    refine ⟨t, ht, ?_⟩
    intro y hy
    by_contra hy_cover
    exact hbad ⟨y, hy, hy_cover⟩
  rcases Set.seq_of_forall_finite_exists hfinite with ⟨y, hy⟩
  rcases hseq y (fun n ↦ (hy n).1) with ⟨φ, hφ_mono, hφ_cauchy⟩
  rcases hφ_cauchy.mem_entourage hV with ⟨N, hN⟩
  have hprev : y (φ N) ∈ y '' Set.Iio (φ (N + 1)) := by
    refine ⟨φ N, hφ_mono (Nat.lt_succ_self N), rfl⟩
  have hnot_ball : y (φ (N + 1)) ∉ {x | (x, y (φ N)) ∈ V} := by
    intro hball
    exact (hy (φ (N + 1))).2
      (by
        simp only [Set.mem_iUnion]
        exact ⟨y (φ N), ⟨hprev, hball⟩⟩)
  exact hnot_ball (hN (N + 1) N (Nat.le_succ N) le_rfl)

/--
%%handwave
name:
  Sequential finite nets give finite nets for a family
statement:
  Let a family take values in a complete pseudometric space.  If every
  sequence selected from the family admits finite nets at every positive
  scale, then the whole family admits finite nets at every positive scale.
proof:
  The finite-net hypothesis makes every selected sequence totally bounded.
  Since the ambient space is complete, the closure of such a sequence is
  compact, hence every selected sequence has a Cauchy subsequence.  The
  preceding criterion then gives total boundedness of the whole family.
-/
theorem finite_net_family_of_sequence_finite_net {ι Y : Type}
    [PseudoMetricSpace Y] [CompleteSpace Y] (x : ι → Y)
    (hseq : ∀ f : ℕ → ι, ∀ ε : ℝ, 0 < ε →
      ∃ t : Set Y, t.Finite ∧
        Set.range (fun n : ℕ ↦ x (f n)) ⊆ ⋃ y ∈ t, Metric.ball y ε) :
    ∀ ε : ℝ, 0 < ε →
      ∃ t : Set Y, t.Finite ∧
        Set.range x ⊆ ⋃ y ∈ t, Metric.ball y ε := by
  have htot : TotallyBounded (Set.range x) := by
    refine totallyBounded_of_forall_seq_exists_cauchySeq_subseq ?_
    intro y hy
    choose f hf using hy
    let z : ℕ → Y := fun n ↦ x (f n)
    have hz_totallyBounded : TotallyBounded (Set.range z) :=
      Metric.totallyBounded_iff.2 (hseq f)
    have hz_compact : IsCompact (closure (Set.range z)) :=
      hz_totallyBounded.closure.isCompact_of_isClosed isClosed_closure
    have hz_seqCompact : IsSeqCompact (closure (Set.range z)) :=
      hz_compact.isSeqCompact
    have hz_mem : ∀ n : ℕ, z n ∈ closure (Set.range z) :=
      fun n ↦ subset_closure ⟨n, rfl⟩
    rcases hz_seqCompact hz_mem with ⟨a, _ha, φ, hφ_mono, hφ_tendsto⟩
    refine ⟨φ, hφ_mono, ?_⟩
    have hy_tendsto : Filter.Tendsto (y ∘ φ) Filter.atTop (𝓝 a) := by
      simpa [z, Function.comp_def, hf] using hφ_tendsto
    exact hy_tendsto.cauchySeq
  exact Metric.totallyBounded_iff.mp htot

/--
%%handwave
name:
  Pointwise representative of a finite sum in an \(L^p\) space
statement:
  For finitely many \(L^p(\mu;E)\) functions \(f_i\), the canonical
  representative of \(\sum_i f_i\) agrees almost everywhere with
  \(x\mapsto\sum_i f_i(x)\).
proof:
  Induct on the finite index set, using almost-everywhere compatibility of
  \(L^p\) representatives with zero and addition.
-/
private theorem lpCoeFn_finset_sum {α ι E : Type} [MeasurableSpace α]
    [NormedAddCommGroup E] {p : ℝ≥0∞} {μ : Measure α}
    (s : Finset ι) (f : ι → Lp E p μ) :
    ⇑(∑ i ∈ s, f i) =ᵐ[μ] fun x ↦ ∑ i ∈ s, f i x := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simpa using (Lp.coeFn_zero E p μ)
  · intro a s ha hs
    have hadd : ⇑(f a + ∑ i ∈ s, f i) =ᵐ[μ]
        fun x ↦ f a x + (∑ i ∈ s, f i) x :=
      Lp.coeFn_add (f a) (∑ i ∈ s, f i)
    filter_upwards [hadd, hs] with x hxadd hxsum
    rw [Finset.sum_insert ha]
    rw [Finset.sum_insert ha]
    exact hxadd.trans (by rw [hxsum])

/--
%%handwave
name:
  Outer box averaging operator
statement:
  Given two measures on the same measurable space and finitely many
  measurable averaging sets of finite measure for both measures, averaging
  over the outer measure and placing the resulting constants in the inner
  \(L^2\)-space defines a continuous finite-rank operator
  \(L^2(\mu_P)\to L^2(\mu_K)\).
-/
noncomputable def finiteOuterCellAveragingOperator {α : Type} [MeasurableSpace α]
    (μP μK : Measure α) {m : ℕ} (D : Fin m → Set α)
    (hD_meas : ∀ i : Fin m, MeasurableSet (D i))
    (hD_finiteP : ∀ i : Fin m, μP (D i) ≠ (⊤ : ℝ≥0∞))
    (hD_finiteK : ∀ i : Fin m, μK (D i) ≠ (⊤ : ℝ≥0∞)) :
    Lp ℝ 2 μP →L[ℝ] Lp ℝ 2 μK :=
  finiteRankRepresentationOperatorBetween
    (fun i : Fin m ↦
      (μP.real (D i))⁻¹ •
        innerSL ℝ (indicatorConstLp 2 (hD_meas i) (hD_finiteP i) (1 : ℝ)))
    (fun i : Fin m ↦ indicatorConstLp 2 (hD_meas i) (hD_finiteK i) (1 : ℝ))

/--
%%handwave
name:
  Formula for the outer averaging operator
statement:
  The outer averaging operator is the sum of the outer-set
  integral coefficients, divided by the outer cell measure, times the
  corresponding indicators in the inner \(L^2\)-space.
proof:
  Expand the cross-space finite-rank representation and use the \(L^2\)
  inner-product formula for indicator functions with respect to the outer
  measure.
-/
theorem finiteOuterCellAveragingOperator_apply {α : Type} [MeasurableSpace α]
    (μP μK : Measure α) {m : ℕ} (D : Fin m → Set α)
    (hD_meas : ∀ i : Fin m, MeasurableSet (D i))
    (hD_finiteP : ∀ i : Fin m, μP (D i) ≠ (⊤ : ℝ≥0∞))
    (hD_finiteK : ∀ i : Fin m, μK (D i) ≠ (⊤ : ℝ≥0∞))
    (f : Lp ℝ 2 μP) :
    finiteOuterCellAveragingOperator μP μK D hD_meas hD_finiteP hD_finiteK f =
      ∑ i : Fin m,
        ((μP.real (D i))⁻¹ * ∫ x in D i, f x ∂μP) •
          indicatorConstLp 2 (hD_meas i) (hD_finiteK i) (1 : ℝ) := by
  rw [finiteOuterCellAveragingOperator, finiteRankRepresentationOperatorBetween_apply]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  have hinner :
      (innerSL ℝ (indicatorConstLp 2 (hD_meas i) (hD_finiteP i) (1 : ℝ))) f =
        ∫ x in D i, f x ∂μP := by
    simpa [innerSL_apply_apply] using
        (L2.inner_indicatorConstLp_one
        (μ := μP) (s := D i) (hs := hD_meas i) (hμs := hD_finiteP i) f)
  simp [ContinuousLinearMap.smul_apply, hinner, mul_smul]

/--
%%handwave
name:
  Outer averaging is the piecewise outer average
statement:
  The outer averaging operator is represented almost everywhere with respect
  to the inner measure by the finite sum of outer averages multiplied by the
  inner cell indicators.
proof:
  Expand the cross-space finite-rank representation, use the
  almost-everywhere formula for cell indicators in the inner \(L^2\)-space,
  and identify the coefficient integrals by the outer measure.
-/
theorem finiteOuterCellAveragingOperator_ae_eq_piecewise
    {α : Type} [MeasurableSpace α]
    (μP μK : Measure α) {m : ℕ} (D : Fin m → Set α)
    (hD_meas : ∀ i : Fin m, MeasurableSet (D i))
    (hD_finiteP : ∀ i : Fin m, μP (D i) ≠ (⊤ : ℝ≥0∞))
    (hD_finiteK : ∀ i : Fin m, μK (D i) ≠ (⊤ : ℝ≥0∞))
    (f : Lp ℝ 2 μP) :
    ⇑(finiteOuterCellAveragingOperator μP μK D hD_meas hD_finiteP hD_finiteK f)
      =ᵐ[μK]
      fun x ↦
        ∑ i : Fin m,
          ((μP.real (D i))⁻¹ * ∫ y in D i, f y ∂μP) *
            (D i).indicator (fun _ ↦ (1 : ℝ)) x := by
  rw [finiteOuterCellAveragingOperator_apply]
  have hsum := lpCoeFn_finset_sum (μ := μK) Finset.univ
    (fun i : Fin m ↦
      ((μP.real (D i))⁻¹ * ∫ y in D i, f y ∂μP) •
        indicatorConstLp 2 (hD_meas i) (hD_finiteK i) (1 : ℝ))
  have hind :
      ∀ᵐ x ∂μK, ∀ i : Fin m,
        indicatorConstLp 2 (hD_meas i) (hD_finiteK i) (1 : ℝ) x =
          (D i).indicator (fun _ ↦ (1 : ℝ)) x :=
    ae_all_iff.2 fun i ↦
      indicatorConstLp_coeFn (p := 2) (hs := hD_meas i)
        (hμs := hD_finiteK i) (c := (1 : ℝ))
  have hsmul :
      ∀ᵐ x ∂μK, ∀ i : Fin m,
        ((((μP.real (D i))⁻¹ * ∫ y in D i, f y ∂μP) •
            indicatorConstLp 2 (hD_meas i) (hD_finiteK i) (1 : ℝ) :
              Lp ℝ 2 μK) x) =
          ((μP.real (D i))⁻¹ * ∫ y in D i, f y ∂μP) *
            indicatorConstLp 2 (hD_meas i) (hD_finiteK i) (1 : ℝ) x :=
    ae_all_iff.2 fun i ↦
      Lp.coeFn_smul
        ((μP.real (D i))⁻¹ * ∫ y in D i, f y ∂μP)
        (indicatorConstLp 2 (hD_meas i) (hD_finiteK i) (1 : ℝ))
  filter_upwards [hsum, hind, hsmul] with x hxsum hxind hxsmul
  rw [hxsum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [hxsmul i, hxind i]

/--
%%handwave
name:
  Pointwise \(L^2\) control gives outer averaging distance control
statement:
  If the \(L^2(\mu_K)\) norm of the pointwise difference between a function
  and the piecewise outer average of an \(L^2(\mu_P)\)-class is below a
  positive scale, then the distance between the \(L^2(\mu_K)\)-class of the
  function and the outer averaging operator applied to the \(L^2(\mu_P)\)
  class is below that scale.
proof:
  The \(L^2\)-distance is the \(L^2\)-seminorm of the difference of
  representatives.  Replace the \(L^2(\mu_K)\)-representative by the original
  function and the averaged \(L^2(\mu_K)\)-representative by its piecewise
  formula, both almost everywhere.
-/
theorem finiteOuterCellAveragingOperator_dist_lt_of_piecewise_eLpNorm_sub_lt
    {α : Type} [MeasurableSpace α]
    (μP μK : Measure α) {m : ℕ} (D : Fin m → Set α)
    (hD_meas : ∀ i : Fin m, MeasurableSet (D i))
    (hD_finiteP : ∀ i : Fin m, μP (D i) ≠ (⊤ : ℝ≥0∞))
    (hD_finiteK : ∀ i : Fin m, μK (D i) ≠ (⊤ : ℝ≥0∞))
    {u : α → ℝ} (huK : MemLp u 2 μK) (fP : Lp ℝ 2 μP) {ε : ℝ}
    (herr :
      eLpNorm
        (fun x ↦
          u x -
            ∑ i : Fin m,
              ((μP.real (D i))⁻¹ * ∫ y in D i, fP y ∂μP) *
                (D i).indicator (fun _ ↦ (1 : ℝ)) x)
        2 μK < ENNReal.ofReal ε) :
    dist (huK.toLp u)
      (finiteOuterCellAveragingOperator μP μK D hD_meas hD_finiteP hD_finiteK fP) < ε := by
  have hpiece :=
    finiteOuterCellAveragingOperator_ae_eq_piecewise
      μP μK D hD_meas hD_finiteP hD_finiteK fP
  have hrepr : ⇑(huK.toLp u) =ᵐ[μK] u := MemLp.coeFn_toLp huK
  have hdiff :
      (⇑(huK.toLp u) -
          ⇑(finiteOuterCellAveragingOperator
            μP μK D hD_meas hD_finiteP hD_finiteK fP)) =ᵐ[μK]
        fun x ↦
          u x -
            ∑ i : Fin m,
              ((μP.real (D i))⁻¹ * ∫ y in D i, fP y ∂μP) *
                (D i).indicator (fun _ ↦ (1 : ℝ)) x := by
    filter_upwards [hrepr, hpiece] with x hux hpx
    simp [Pi.sub_apply, hux, hpx]
  rw [Lp.dist_def]
  exact ENNReal.toReal_lt_of_lt_ofReal ((eLpNorm_congr_ae hdiff).trans_lt herr)

/--
%%handwave
name:
  Outer averaging has finite-dimensional range
statement:
  The outer averaging operator has finite-dimensional range.
proof:
  Its values lie in the span of finitely many inner cell indicators.
-/
theorem finiteOuterCellAveragingOperator_finiteDimensional_range
    {α : Type} [MeasurableSpace α]
    (μP μK : Measure α) {m : ℕ} (D : Fin m → Set α)
    (hD_meas : ∀ i : Fin m, MeasurableSet (D i))
    (hD_finiteP : ∀ i : Fin m, μP (D i) ≠ (⊤ : ℝ≥0∞))
    (hD_finiteK : ∀ i : Fin m, μK (D i) ≠ (⊤ : ℝ≥0∞)) :
    FiniteDimensional ℝ
      (finiteOuterCellAveragingOperator μP μK D hD_meas hD_finiteP hD_finiteK).range := by
  exact finiteRankRepresentationOperatorBetween_finiteDimensional_range
    (fun i : Fin m ↦
      (μP.real (D i))⁻¹ •
        innerSL ℝ (indicatorConstLp 2 (hD_meas i) (hD_finiteP i) (1 : ℝ)))
    (fun i : Fin m ↦ indicatorConstLp 2 (hD_meas i) (hD_finiteK i) (1 : ℝ))

/--
%%handwave
name:
  Value of a disjoint piecewise sum inside one cell
statement:
  Let \(C_i\) be pairwise disjoint. If \(x\in C_k\), then
  \(\sum_i a_i\mathbf1_{C_i}(x)=a_k\).
proof:
  The \(k\)-th indicator is one, while disjointness makes every other
  indicator zero.
-/
private theorem finiteCell_piecewise_sum_apply_of_mem
    {α : Type} {m : ℕ} (C : Fin m → Set α) (a : Fin m → ℝ)
    (hC_disjoint : ∀ i j : Fin m, i ≠ j → Disjoint (C i) (C j))
    {k : Fin m} {x : α} (hx : x ∈ C k) :
    (∑ i : Fin m, a i * (C i).indicator (fun _ ↦ (1 : ℝ)) x) = a k := by
  classical
  calc
    (∑ i : Fin m, a i * (C i).indicator (fun _ ↦ (1 : ℝ)) x)
        = a k * (C k).indicator (fun _ ↦ (1 : ℝ)) x := by
          refine Finset.sum_eq_single
            (s := (Finset.univ : Finset (Fin m)))
            (a := k)
            (f := fun i : Fin m ↦ a i * (C i).indicator (fun _ ↦ (1 : ℝ)) x)
            ?_ ?_
          · intro i _hi hik
            have hnot : x ∉ C i := by
              intro hxi
              exact Set.disjoint_left.mp (hC_disjoint i k hik) hxi hx
            simp [Set.indicator_of_notMem hnot]
          · intro hk
            simp at hk
    _ = a k := by simp [Set.indicator_of_mem hx]

/--
%%handwave
name:
  Value of a piecewise sum outside all cells
statement:
  If \(x\notin\bigcup_i C_i\), then
  \(\sum_i a_i\mathbf1_{C_i}(x)=0\).
proof:
  Every cell indicator vanishes at \(x\), so every summand is zero.
-/
private theorem finiteCell_piecewise_sum_apply_of_not_mem_iUnion
    {α : Type} {m : ℕ} (C : Fin m → Set α) (a : Fin m → ℝ)
    {x : α} (hx : x ∉ ⋃ i : Fin m, C i) :
    (∑ i : Fin m, a i * (C i).indicator (fun _ ↦ (1 : ℝ)) x) = 0 := by
  classical
  refine Finset.sum_eq_zero fun i _hi ↦ ?_
  have hnot : x ∉ C i := by
    intro hxi
    exact hx (Set.mem_iUnion.mpr ⟨i, hxi⟩)
  simp [Set.indicator_of_notMem hnot]

/--
%%handwave
name:
  Cell average is independent of the chosen \(L^2\) representative
statement:
  If \(u\in L^2(\mu)\) and \(s\) is measurable, then the normalized integral
  of the canonical \(L^2\) representative over \(s\) equals that of \(u\).
proof:
  The canonical representative equals \(u\) almost everywhere; restrict that
  equality to \(s\) and use congruence of integrals.
-/
private theorem finiteCell_averageCoeff_congr_toLp
    {α : Type} [MeasurableSpace α] {μ : Measure α}
    {s : Set α} (hs : MeasurableSet s)
    {u : α → ℝ} (hu : MemLp u 2 μ) :
    ((μ.real s)⁻¹ * ∫ y in s, (hu.toLp u : Lp ℝ 2 μ) y ∂μ) =
      ((μ.real s)⁻¹ * ∫ y in s, u y ∂μ) := by
  have hrepr : ⇑(hu.toLp u) =ᵐ[μ] u := MemLp.coeFn_toLp hu
  have hint :
      ∫ y in s, (hu.toLp u : Lp ℝ 2 μ) y ∂μ =
        ∫ y in s, u y ∂μ :=
    setIntegral_congr_ae hs (hrepr.mono fun y hy _hys ↦ hy)
  rw [hint]

/--
%%handwave
name:
  Finite boxes lie in a common regular coordinate grid
statement:
  A finite family of coordinate boxes is a regular grid family if all boxes
  have the same positive side length in every coordinate and their lower
  corners lie in one translated integer lattice.
-/
def RegularGridBoxFamily {d m : ℕ}
    (D : Fin m → BoxIntegral.Box (Fin d)) : Prop :=
  ∃ ℓ : ℝ, 0 < ℓ ∧
    (∀ i : Fin m, ∀ j : Fin d, (D i).upper j - (D i).lower j = ℓ) ∧
      ∃ a : Fin d → ℝ, ∀ i : Fin m, ∀ j : Fin d,
        ∃ k : ℤ, (D i).lower j = a j + ℓ * (k : ℝ)

/--
%%handwave
name:
  Regular grid boxes have a common volume
statement:
  In a regular grid family, all boxes have the same Lebesgue measure.
proof:
  Every side length is the common grid mesh, so the product formula for the
  volume of a coordinate box gives the same product for every box.
-/
theorem RegularGridBoxFamily.volume_eq
    {d m : ℕ} {D : Fin m → BoxIntegral.Box (Fin d)}
    (hD : RegularGridBoxFamily D) (i k : Fin m) :
    MeasureTheory.volume (D i : Set (Fin d → ℝ)) =
      MeasureTheory.volume (D k : Set (Fin d → ℝ)) := by
  rcases hD with ⟨ℓ, _hℓ, hside, _a, _hgrid⟩
  rw [BoxIntegral.Box.coe_eq_pi, Real.volume_pi_Ioc,
    BoxIntegral.Box.coe_eq_pi, Real.volume_pi_Ioc]
  simp_rw [hside]

/--
%%handwave
name:
  Regular cube cover inside an outer compact set
statement:
  If a compact set \(K\) is contained in the interior of a compact set \(P\)
  in \(\mathbb R^d\), then for every positive scale \( \delta \) there is a
  finite disjoint family of regular coordinate boxes contained in \(P\) whose
  union covers \(K\), whose boxes have diameter below \( \delta \), and whose
  measures are positive and finite.
proof:
  Choose a coordinate grid with mesh much smaller than \( \delta \) and also
  smaller than the distance from \(K\) to the complement of \(P\).  Keep the
  finitely many grid boxes meeting \(K\).  Compactness of \(K\) gives
  finiteness, the mesh bound gives the diameter estimate, and the boxes lie
  in \(P\) by the distance-to-the-boundary choice.
-/
theorem euclideanPiCompact_exists_regularCubeCover_between
    {d : ℕ} {K P : Set (Fin d → ℝ)}
    (hK : IsCompact K) (_hP : IsCompact P) (hKP : K ⊆ interior P) :
    ∀ δ : ℝ, 0 < δ →
      ∃ m : ℕ,
        ∃ D : Fin m → BoxIntegral.Box (Fin d),
          K ⊆ ⋃ i : Fin m, (D i : Set (Fin d → ℝ)) ∧
          (∀ i : Fin m, (D i : Set (Fin d → ℝ)) ⊆ P) ∧
          (∀ i : Fin m, 0 < (MeasureTheory.volume.restrict P)
            (D i : Set (Fin d → ℝ))) ∧
          (∀ i : Fin m, (MeasureTheory.volume.restrict P)
            (D i : Set (Fin d → ℝ)) ≠ (⊤ : ℝ≥0∞)) ∧
          (∀ i : Fin m, (MeasureTheory.volume.restrict K)
            (D i : Set (Fin d → ℝ)) ≠ (⊤ : ℝ≥0∞)) ∧
          RegularGridBoxFamily D ∧
          (∀ i j : Fin m, i ≠ j →
            Disjoint (D i : Set (Fin d → ℝ)) (D j : Set (Fin d → ℝ))) ∧
          ∀ i : Fin m, ∀ x ∈ (D i : Set (Fin d → ℝ)),
            ∀ y ∈ (D i : Set (Fin d → ℝ)), dist x y < δ := by
  intro δ hδ
  classical
  rcases hK.exists_cthickening_subset_open isOpen_interior hKP with
    ⟨ε, hε, hεK⟩
  let ρ : ℝ := min ε δ
  have hρ : 0 < ρ := lt_min hε hδ
  rcases exists_nat_one_div_lt hρ with ⟨n, hn⟩
  let N : ℕ := n + 1
  have hN_ne : NeZero N := ⟨Nat.succ_ne_zero n⟩
  letI : NeZero N := hN_ne
  have hNρ : 1 / (N : ℝ) < ρ := by
    simpa [N, Nat.cast_add, Nat.cast_one] using hn
  have hNε : 1 / (N : ℝ) < ε := hNρ.trans_le (min_le_left _ _)
  have hNδ : 1 / (N : ℝ) < δ := hNρ.trans_le (min_le_right _ _)
  rcases BoxIntegral.le_hasIntegralVertices_of_isBounded
      (ι := Fin d) hK.isBounded with
    ⟨B, hB_int, hKB⟩
  let π : BoxIntegral.TaggedPrepartition B :=
    BoxIntegral.unitPartition.prepartition N B
  let S : Finset (BoxIntegral.Box (Fin d)) :=
    π.boxes.filter fun J ↦ Set.Nonempty ((J : Set (Fin d → ℝ)) ∩ K)
  let m : ℕ := S.card
  let D : Fin m → BoxIntegral.Box (Fin d) :=
    fun i ↦ (S.equivFin.symm i).1
  have hD_memS : ∀ i : Fin m, D i ∈ S := by
    intro i
    exact (S.equivFin.symm i).2
  have hD_memπ : ∀ i : Fin m, D i ∈ π := by
    intro i
    exact (Finset.mem_filter.mp (hD_memS i)).1
  have hD_meetsK :
      ∀ i : Fin m, Set.Nonempty ((D i : Set (Fin d → ℝ)) ∩ K) := by
    intro i
    exact (Finset.mem_filter.mp (hD_memS i)).2
  have hD_box :
      ∀ i : Fin m, ∃ ν : Fin d → ℤ,
        BoxIntegral.unitPartition.box N ν = D i := by
    intro i
    rcases BoxIntegral.unitPartition.mem_prepartition_iff.mp (hD_memπ i) with
      ⟨ν, _hν, hνD⟩
    exact ⟨ν, hνD⟩
  have hD_subsetP :
      ∀ i : Fin m, (D i : Set (Fin d → ℝ)) ⊆ P := by
    intro i y hy
    rcases hD_meetsK i with ⟨z, hzJ, hzK⟩
    rcases hD_box i with ⟨ν, hνD⟩
    have hyIcc : y ∈ BoxIntegral.Box.Icc (D i) :=
      BoxIntegral.Box.coe_subset_Icc hy
    have hzIcc : z ∈ BoxIntegral.Box.Icc (D i) :=
      BoxIntegral.Box.coe_subset_Icc hzJ
    have hdist_le : dist y z ≤ 1 / (N : ℝ) := by
      calc
        dist y z ≤ Metric.diam (BoxIntegral.Box.Icc (D i)) :=
          Metric.dist_le_diam_of_mem (BoxIntegral.Box.isBounded_Icc (D i)) hyIcc hzIcc
        _ = Metric.diam (BoxIntegral.Box.Icc (BoxIntegral.unitPartition.box N ν)) := by
          rw [hνD]
        _ ≤ 1 / (N : ℝ) :=
          BoxIntegral.unitPartition.diam_boxIcc N ν
    have hy_thick :
        y ∈ Metric.cthickening ε K :=
      Metric.mem_cthickening_of_dist_le y z ε K hzK
        ((hdist_le.trans_lt hNε).le)
    exact interior_subset (hεK hy_thick)
  refine ⟨m, D, ?_, hD_subsetP, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hxK
    have hpart := BoxIntegral.unitPartition.prepartition_isPartition
      (n := N) (B := B) hB_int
    rcases hpart x (hKB hxK) with ⟨J, hJπ, hxJ⟩
    have hJS : J ∈ S := by
      refine Finset.mem_filter.mpr ⟨hJπ, ?_⟩
      exact ⟨x, hxJ, hxK⟩
    exact Set.mem_iUnion_of_mem (S.equivFin ⟨J, hJS⟩) (by
      simpa [D] using hxJ)
  · intro i
    rcases hD_box i with ⟨ν, hνD⟩
    have hmeas :
        (MeasureTheory.volume.restrict P) (D i : Set (Fin d → ℝ)) =
          MeasureTheory.volume (D i : Set (Fin d → ℝ)) := by
      rw [Measure.restrict_apply (D i).measurableSet_coe]
      rw [Set.inter_eq_self_of_subset_left (hD_subsetP i)]
    rw [hmeas, ← hνD, BoxIntegral.unitPartition.volume_box]
    simp
  · intro i
    rcases hD_box i with ⟨ν, hνD⟩
    have hmeas :
        (MeasureTheory.volume.restrict P) (D i : Set (Fin d → ℝ)) =
          MeasureTheory.volume (D i : Set (Fin d → ℝ)) := by
      rw [Measure.restrict_apply (D i).measurableSet_coe]
      rw [Set.inter_eq_self_of_subset_left (hD_subsetP i)]
    rw [hmeas, ← hνD, BoxIntegral.unitPartition.volume_box]
    simp
  · intro i
    rcases hD_box i with ⟨ν, hνD⟩
    have hle :
        (MeasureTheory.volume.restrict K) (D i : Set (Fin d → ℝ)) ≤
          MeasureTheory.volume (D i : Set (Fin d → ℝ)) :=
      Measure.le_iff'.1 Measure.restrict_le_self _
    refine ne_top_of_le_ne_top ?_ hle
    rw [← hνD, BoxIntegral.unitPartition.volume_box]
    simp
  · refine ⟨1 / (N : ℝ), ?_, ?_, 0, ?_⟩
    · positivity
    · intro i j
      rcases hD_box i with ⟨ν, hνD⟩
      rw [← hνD]
      exact BoxIntegral.unitPartition.box.upper_sub_lower N ν j
    · intro i j
      rcases hD_box i with ⟨ν, hνD⟩
      refine ⟨ν j, ?_⟩
      rw [← hνD]
      simp [BoxIntegral.unitPartition.box, div_eq_mul_inv, mul_comm]
  · intro i j hij
    have hDne : D i ≠ D j := by
      intro hEq
      have hsub : S.equivFin.symm i = S.equivFin.symm j :=
        Subtype.ext hEq
      exact hij (S.equivFin.symm.injective hsub)
    exact π.toPrepartition.disjoint_coe_of_mem (hD_memπ i) (hD_memπ j) hDne
  · intro i x hx y hy
    rcases hD_box i with ⟨ν, hνD⟩
    have hxIcc : x ∈ BoxIntegral.Box.Icc (D i) :=
      BoxIntegral.Box.coe_subset_Icc hx
    have hyIcc : y ∈ BoxIntegral.Box.Icc (D i) :=
      BoxIntegral.Box.coe_subset_Icc hy
    have hdist_le : dist x y ≤ 1 / (N : ℝ) := by
      calc
        dist x y ≤ Metric.diam (BoxIntegral.Box.Icc (D i)) :=
          Metric.dist_le_diam_of_mem (BoxIntegral.Box.isBounded_Icc (D i)) hxIcc hyIcc
        _ = Metric.diam (BoxIntegral.Box.Icc (BoxIntegral.unitPartition.box N ν)) := by
          rw [hνD]
        _ ≤ 1 / (N : ℝ) :=
          BoxIntegral.unitPartition.diam_boxIcc N ν
    exact hdist_le.trans_lt hNδ

/--
%%handwave
name:
  Regular-cube averaging constant
statement:
  The regular-cube averaging estimate carries a positive constant depending
  only on the Euclidean dimension.
-/
def regularCubeOuterAveragingConstant (d : ℕ) : ℝ :=
  (2 : ℝ) ^ d + 1

/--
%%handwave
name:
  Positivity of the regular-cube averaging constant
statement:
  The dimension-dependent constant \(3+2^{d+2}\) used for regular-cube
  averaging is strictly positive for every \(d\).
proof:
  The power \(2^d\) is nonnegative, so the displayed sum is positive.
-/
theorem regularCubeOuterAveragingConstant_pos (d : ℕ) :
    0 < regularCubeOuterAveragingConstant d := by
  have hpow_nonneg : 0 ≤ (2 : ℝ) ^ d := pow_nonneg (by norm_num) d
  dsimp [regularCubeOuterAveragingConstant]
  linarith

/--
%%handwave
name:
  Nonnegativity of the regular-cube averaging constant
statement:
  The regular-cube averaging constant is nonnegative in every dimension.
proof:
  This follows immediately from [its strict positivity](lean:regularCubeOuterAveragingConstant_pos).
-/
theorem regularCubeOuterAveragingConstant_nonneg (d : ℕ) :
    0 ≤ regularCubeOuterAveragingConstant d :=
  (regularCubeOuterAveragingConstant_pos d).le

/--
%%handwave
name:
  Regular-cube averaging constant as an extended nonnegative real
statement:
  The dimension-dependent regular-cube averaging constant may be used as an
  extended nonnegative real multiplier in \(L^2\)-estimates.
-/
noncomputable def regularCubeOuterAveragingENNRealConstant (d : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (regularCubeOuterAveragingConstant d)

/--
%%handwave
name:
  The regular-cube constant absorbs the doubled-box factor
statement:
  The dimension-dependent regular-cube averaging constant is large enough
  that \(2^d\eta^2\) is bounded by \((C_d\eta)^2\).
proof:
  Since \(C_d=2^d+1\), one has \(2^d\le C_d\le C_d^2\).  Multiplying by
  \(\eta^2\) gives the estimate.
-/
theorem two_pow_mul_sq_le_regularCubeOuterAveragingENNRealConstant_mul_sq
    (d : ℕ) (η : ℝ≥0∞) :
    ((2 : ℝ≥0∞) ^ d) * η ^ (2 : ℝ) ≤
      (regularCubeOuterAveragingENNRealConstant d * η) ^ (2 : ℝ) := by
  let C : ℝ≥0∞ := regularCubeOuterAveragingENNRealConstant d
  have hpow_le_C : ((2 : ℝ≥0∞) ^ d) ≤ C := by
    dsimp [C, regularCubeOuterAveragingENNRealConstant,
      regularCubeOuterAveragingConstant]
    have hleft : ((2 : ℝ≥0∞) ^ d) = ((2 ^ d : ℕ) : ℝ≥0∞) := by
      norm_num
    rw [hleft]
    exact (ENNReal.natCast_le_ofReal (pow_ne_zero d (by norm_num : (2 : ℕ) ≠ 0))).2
      (by norm_num [Nat.cast_pow])
  have hone_le_C : (1 : ℝ≥0∞) ≤ C := by
    dsimp [C, regularCubeOuterAveragingENNRealConstant,
      regularCubeOuterAveragingConstant]
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by
      have hpow_nonneg : 0 ≤ (2 : ℝ) ^ d :=
        pow_nonneg (by norm_num : 0 ≤ (2 : ℝ)) d
      linarith)
  have hC_le_C_sq : C ≤ C ^ (2 : ℝ) := by
    rw [ENNReal.rpow_two, pow_two]
    calc
      C = C * 1 := by simp
      _ ≤ C * C := by gcongr
  have hcoeff : ((2 : ℝ≥0∞) ^ d) ≤ C ^ (2 : ℝ) :=
    hpow_le_C.trans hC_le_C_sq
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : 0 ≤ (2 : ℝ))]
  gcongr

/--
%%handwave
name:
  Outer box-average coefficient
statement:
  For a box inside an outer region \(P\), the outer average coefficient of
  a square-integrable function is the integral over the box divided by the
  volume of the box, with the integral taken using the \(L^2(P)\)
  representative.
-/
noncomputable def regularCubeOuterAverageCoeff
    {d : ℕ} (P : Set (Fin d → ℝ))
    (u : ℕ → (Fin d → ℝ) → ℝ)
    (hmemP : ∀ n : ℕ, MemLp (u n) 2 (MeasureTheory.volume.restrict P))
    {m : ℕ} (D : Fin m → BoxIntegral.Box (Fin d))
    (n : ℕ) (i : Fin m) : ℝ :=
  ((MeasureTheory.volume.restrict P).real (D i : Set (Fin d → ℝ)))⁻¹ *
    ∫ y in (D i : Set (Fin d → ℝ)),
      ((hmemP n).toLp (u n) : Lp ℝ 2 (MeasureTheory.volume.restrict P)) y
      ∂(MeasureTheory.volume.restrict P)

/--
%%handwave
name:
  Outer box piecewise average
statement:
  A finite family of boxes inside an outer region \(P\) defines a
  piecewise-constant averaging function by placing the outer box-average
  coefficient on each box.
-/
noncomputable def regularCubeOuterPiecewiseAverage
    {d : ℕ} (P : Set (Fin d → ℝ))
    (u : ℕ → (Fin d → ℝ) → ℝ)
    (hmemP : ∀ n : ℕ, MemLp (u n) 2 (MeasureTheory.volume.restrict P))
    {m : ℕ} (D : Fin m → BoxIntegral.Box (Fin d))
    (n : ℕ) : (Fin d → ℝ) → ℝ :=
  fun x ↦
    ∑ i : Fin m,
      regularCubeOuterAverageCoeff P u hmemP D n i *
        (D i : Set (Fin d → ℝ)).indicator (fun _ ↦ (1 : ℝ)) x

/--
%%handwave
name:
  Outer box averages use the original function almost everywhere
statement:
  The coefficient obtained by integrating an \(L^2(P)\)-representative over
  a box agrees with the coefficient obtained by integrating the original
  function over the same box.
proof:
  The \(L^2(P)\)-representative agrees almost everywhere with the original
  function, so the set integrals over the measurable box agree.
-/
theorem regularCubeOuterAverageCoeff_congr_toLp
    {d : ℕ} {P : Set (Fin d → ℝ)}
    (u : ℕ → (Fin d → ℝ) → ℝ)
    (hmemP : ∀ n : ℕ, MemLp (u n) 2 (MeasureTheory.volume.restrict P))
    {m : ℕ} (D : Fin m → BoxIntegral.Box (Fin d))
    (n : ℕ) (i : Fin m) :
    regularCubeOuterAverageCoeff P u hmemP D n i =
      ((MeasureTheory.volume.restrict P).real (D i : Set (Fin d → ℝ)))⁻¹ *
        ∫ y in (D i : Set (Fin d → ℝ)), u n y
          ∂(MeasureTheory.volume.restrict P) := by
  simpa [regularCubeOuterAverageCoeff] using
    finiteCell_averageCoeff_congr_toLp (D i).measurableSet_coe (hmemP n)

/--
%%handwave
name:
  Box-average coefficient
statement:
  The average coefficient of a function on a box is the integral over the box
  divided by its Lebesgue volume.
-/
noncomputable def regularCubeBoxAverageCoeff
    {d : ℕ} (u : ℕ → (Fin d → ℝ) → ℝ)
    {m : ℕ} (D : Fin m → BoxIntegral.Box (Fin d))
    (n : ℕ) (i : Fin m) : ℝ :=
  (MeasureTheory.volume.real (D i : Set (Fin d → ℝ)))⁻¹ *
    ∫ y in (D i : Set (Fin d → ℝ)), u n y ∂MeasureTheory.volume

/--
%%handwave
name:
  Box-average coefficients are set averages
statement:
  The explicit box-average coefficient is the usual Lebesgue average over the
  box.
proof:
  Unfold the coefficient and the definition of set average; the normalizing volume and the box integral are identical.
-/
theorem regularCubeBoxAverageCoeff_eq_setAverage
    {d : ℕ} (u : ℕ → (Fin d → ℝ) → ℝ)
    {m : ℕ} (D : Fin m → BoxIntegral.Box (Fin d))
    (n : ℕ) (i : Fin m) :
    regularCubeBoxAverageCoeff u D n i =
      ⨍ y in (D i : Set (Fin d → ℝ)), u n y ∂MeasureTheory.volume := by
  rw [regularCubeBoxAverageCoeff, setAverage_eq]
  rfl

/--
%%handwave
name:
  Outer box-average coefficients are ordinary box averages
statement:
  If a box lies inside the outer region \(P\), then its outer average
  coefficient, computed using the restricted measure on \(P\), is the
  ordinary Lebesgue average over the box.
proof:
  The restricted measure agrees with Lebesgue measure on sets contained in
  \(P\).  The same restriction identity applies to the set integral over the
  box.
-/
theorem regularCubeOuterAverageCoeff_eq_boxAverageCoeff_of_subset
    {d : ℕ} {P : Set (Fin d → ℝ)}
    (u : ℕ → (Fin d → ℝ) → ℝ)
    (hmemP : ∀ n : ℕ, MemLp (u n) 2 (MeasureTheory.volume.restrict P))
    {m : ℕ} (D : Fin m → BoxIntegral.Box (Fin d))
    (hD_subsetP : ∀ i : Fin m, (D i : Set (Fin d → ℝ)) ⊆ P)
    (n : ℕ) (i : Fin m) :
    regularCubeOuterAverageCoeff P u hmemP D n i =
      regularCubeBoxAverageCoeff u D n i := by
  rw [regularCubeOuterAverageCoeff_congr_toLp u hmemP D n i]
  have hmeasure :
      (MeasureTheory.volume.restrict P).real (D i : Set (Fin d → ℝ)) =
        MeasureTheory.volume.real (D i : Set (Fin d → ℝ)) := by
    rw [measureReal_restrict_apply (D i).measurableSet_coe]
    have h_inter :
        (D i : Set (Fin d → ℝ)) ∩ P = (D i : Set (Fin d → ℝ)) :=
      Set.inter_eq_left.mpr (hD_subsetP i)
    rw [h_inter]
  have hintegral :
      ∫ y in (D i : Set (Fin d → ℝ)), u n y ∂(MeasureTheory.volume.restrict P) =
        ∫ y in (D i : Set (Fin d → ℝ)), u n y ∂MeasureTheory.volume := by
    change
      ∫ y, u n y ∂((MeasureTheory.volume.restrict P).restrict
          (D i : Set (Fin d → ℝ))) =
        ∫ y, u n y ∂(MeasureTheory.volume.restrict
          (D i : Set (Fin d → ℝ)))
    rw [Measure.restrict_restrict_of_subset (hD_subsetP i)]
  rw [hmeasure, hintegral]
  rfl

/--
%%handwave
name:
  The outer box piecewise average is constant on each disjoint box
statement:
  On a box of a pairwise disjoint finite box family, the piecewise average
  equals the corresponding outer box-average coefficient.
proof:
  At a point of one box, all other box indicators vanish by disjointness,
  while the indicator of the containing box is one.
-/
theorem regularCubeOuterPiecewiseAverage_apply_of_mem
    {d : ℕ} {P : Set (Fin d → ℝ)}
    (u : ℕ → (Fin d → ℝ) → ℝ)
    (hmemP : ∀ n : ℕ, MemLp (u n) 2 (MeasureTheory.volume.restrict P))
    {m : ℕ} (D : Fin m → BoxIntegral.Box (Fin d))
    (hD_disjoint : ∀ i j : Fin m, i ≠ j →
      Disjoint (D i : Set (Fin d → ℝ)) (D j : Set (Fin d → ℝ)))
    (n : ℕ) {k : Fin m} {x : Fin d → ℝ}
    (hx : x ∈ (D k : Set (Fin d → ℝ))) :
    regularCubeOuterPiecewiseAverage P u hmemP D n x =
      regularCubeOuterAverageCoeff P u hmemP D n k := by
  classical
  simpa [regularCubeOuterPiecewiseAverage] using
    finiteCell_piecewise_sum_apply_of_mem
      (fun i : Fin m ↦ (D i : Set (Fin d → ℝ)))
      (fun i : Fin m ↦ regularCubeOuterAverageCoeff P u hmemP D n i)
      hD_disjoint hx

/--
%%handwave
name:
  The outer box piecewise average vanishes off the box union
statement:
  Outside the union of the finite box family, the piecewise average is zero.
proof:
  All box indicators vanish at such a point.
-/
theorem regularCubeOuterPiecewiseAverage_apply_of_not_mem_iUnion
    {d : ℕ} {P : Set (Fin d → ℝ)}
    (u : ℕ → (Fin d → ℝ) → ℝ)
    (hmemP : ∀ n : ℕ, MemLp (u n) 2 (MeasureTheory.volume.restrict P))
    {m : ℕ} (D : Fin m → BoxIntegral.Box (Fin d))
    (n : ℕ) {x : Fin d → ℝ}
    (hx : x ∉ ⋃ i : Fin m, (D i : Set (Fin d → ℝ))) :
    regularCubeOuterPiecewiseAverage P u hmemP D n x = 0 := by
  classical
  simpa [regularCubeOuterPiecewiseAverage] using
    finiteCell_piecewise_sum_apply_of_not_mem_iUnion
      (fun i : Fin m ↦ (D i : Set (Fin d → ℝ)))
      (fun i : Fin m ↦ regularCubeOuterAverageCoeff P u hmemP D n i)
      hx

/--
%%handwave
name:
  Squared piecewise-average error over a disjoint box union is a finite sum
statement:
  For a pairwise disjoint finite family of measurable boxes, the squared
  error integral over their union is the sum of the squared error integrals
  over the individual boxes.
proof:
  This is countable additivity of the Lebesgue integral over a disjoint
  measurable union, followed by the fact that the index set is finite.
-/
theorem regularCubeOuterPiecewiseAverage_lintegral_sq_on_iUnion_eq_sum
    {d : ℕ} {P : Set (Fin d → ℝ)}
    (u : ℕ → (Fin d → ℝ) → ℝ)
    (hmemP : ∀ n : ℕ, MemLp (u n) 2 (MeasureTheory.volume.restrict P))
    {m : ℕ} (D : Fin m → BoxIntegral.Box (Fin d))
    (hD_disjoint : ∀ i j : Fin m, i ≠ j →
      Disjoint (D i : Set (Fin d → ℝ)) (D j : Set (Fin d → ℝ)))
    (n : ℕ) :
    ∫⁻ x in ⋃ i : Fin m, (D i : Set (Fin d → ℝ)),
      ‖u n x - regularCubeOuterPiecewiseAverage P u hmemP D n x‖ₑ ^ (2 : ℝ)
        ∂MeasureTheory.volume =
      ∑ i : Fin m,
        ∫⁻ x in (D i : Set (Fin d → ℝ)),
          ‖u n x - regularCubeOuterPiecewiseAverage P u hmemP D n x‖ₑ ^ (2 : ℝ)
            ∂MeasureTheory.volume := by
  classical
  have hpair :
      Pairwise (fun i j : Fin m ↦
        Disjoint (D i : Set (Fin d → ℝ)) (D j : Set (Fin d → ℝ))) := by
    intro i j hij
    exact hD_disjoint i j hij
  rw [lintegral_iUnion
    (μ := MeasureTheory.volume)
    (s := fun i : Fin m ↦ (D i : Set (Fin d → ℝ)))
    (fun i ↦ (D i).measurableSet_coe)
    hpair]
  simp

/--
%%handwave
name:
  On each box the squared piecewise-average error is the squared variance
statement:
  On a box of a pairwise disjoint finite box family, the squared error
  against the outer piecewise average has the same integral as the squared
  error against the corresponding box-average coefficient.
proof:
  The piecewise average equals the corresponding coefficient at every point
  of the box, so the two nonnegative integrands agree on the domain of
  integration.
-/
theorem regularCubeOuterPiecewiseAverage_lintegral_sq_on_box_eq_averageCoeff
    {d : ℕ} {P : Set (Fin d → ℝ)}
    (u : ℕ → (Fin d → ℝ) → ℝ)
    (hmemP : ∀ n : ℕ, MemLp (u n) 2 (MeasureTheory.volume.restrict P))
    {m : ℕ} (D : Fin m → BoxIntegral.Box (Fin d))
    (hD_disjoint : ∀ i j : Fin m, i ≠ j →
      Disjoint (D i : Set (Fin d → ℝ)) (D j : Set (Fin d → ℝ)))
    (n : ℕ) (i : Fin m) :
    ∫⁻ x in (D i : Set (Fin d → ℝ)),
      ‖u n x - regularCubeOuterPiecewiseAverage P u hmemP D n x‖ₑ ^ (2 : ℝ)
        ∂MeasureTheory.volume =
      ∫⁻ x in (D i : Set (Fin d → ℝ)),
        ‖u n x - regularCubeOuterAverageCoeff P u hmemP D n i‖ₑ ^ (2 : ℝ)
          ∂MeasureTheory.volume := by
  refine setLIntegral_congr_fun (D i).measurableSet_coe ?_
  intro x hx
  change
    ‖u n x - regularCubeOuterPiecewiseAverage P u hmemP D n x‖ₑ ^ (2 : ℝ) =
      ‖u n x - regularCubeOuterAverageCoeff P u hmemP D n i‖ₑ ^ (2 : ℝ)
  rw [regularCubeOuterPiecewiseAverage_apply_of_mem
    u hmemP D hD_disjoint n hx]

/--
%%handwave
name:
  Box pairwise oscillation
statement:
  The pairwise oscillation of a function on a box is the mean, normalized by
  the volume of the box, of the squared difference between two points of the
  box.
-/
noncomputable def regularCubeBoxPairwiseOscillation
    {d : ℕ} (u : ℕ → (Fin d → ℝ) → ℝ)
    {m : ℕ} (D : Fin m → BoxIntegral.Box (Fin d))
    (n : ℕ) (i : Fin m) : ℝ≥0∞ :=
  (MeasureTheory.volume (D i : Set (Fin d → ℝ)))⁻¹ *
    ∫⁻ x in (D i : Set (Fin d → ℝ)),
      ∫⁻ y in (D i : Set (Fin d → ℝ)),
        ‖u n x - u n y‖ₑ ^ (2 : ℝ) ∂MeasureTheory.volume ∂MeasureTheory.volume

/--
%%handwave
name:
  Difference body of a box
statement:
  The difference body of a box consists of the displacements \(h\) for which
  some point of the box and its translate by \(h\) both lie in the box.
-/
def regularCubeBoxDifferenceBody
    {d : ℕ} (D : BoxIntegral.Box (Fin d)) : Set (Fin d → ℝ) :=
  {h | ∃ x ∈ (D : Set (Fin d → ℝ)), x + h ∈ (D : Set (Fin d → ℝ))}

/--
%%handwave
name:
  Difference body of a coordinate box
statement:
  The difference body of a coordinate box is the product of the coordinate
  intervals \((\ell_i-u_i,u_i-\ell_i)\).
proof:
  If both \(x\) and \(x+h\) lie in the box, then each coordinate displacement
  is strictly smaller than the side length in both directions.  Conversely,
  given such a displacement, choose in each coordinate either \(u_i-h_i\) or
  \(u_i\), according to the sign of \(h_i\), to get a point \(x\) with both
  \(x\) and \(x+h\) in the box.
-/
theorem regularCubeBoxDifferenceBody_eq_pi_Ioo
    {d : ℕ} (D : BoxIntegral.Box (Fin d)) :
    regularCubeBoxDifferenceBody D =
      Set.pi Set.univ fun i : Fin d ↦
        Set.Ioo (D.lower i - D.upper i) (D.upper i - D.lower i) := by
  ext h
  constructor
  · rintro ⟨x, hx, hxh⟩ i _hi
    have hxi := hx i
    have hxhi : x i + h i ∈ Set.Ioc (D.lower i) (D.upper i) := by
      simpa [Pi.add_apply] using hxh i
    constructor
    · linarith [hxi.2, hxhi.1]
    · linarith [hxi.1, hxhi.2]
  · intro hh
    let x : Fin d → ℝ :=
      fun i ↦ if 0 ≤ h i then D.upper i - h i else D.upper i
    refine ⟨x, ?_, ?_⟩
    · intro i
      have hi := hh i trivial
      by_cases hnonneg : 0 ≤ h i
      · constructor
        · dsimp [x]
          rw [if_pos hnonneg]
          linarith [hi.2]
        · dsimp [x]
          rw [if_pos hnonneg]
          linarith
      · constructor
        · dsimp [x]
          rw [if_neg hnonneg]
          exact D.lower_lt_upper i
        · dsimp [x]
          rw [if_neg hnonneg]
    · intro i
      have hi := hh i trivial
      by_cases hnonneg : 0 ≤ h i
      · constructor
        · dsimp [x]
          rw [if_pos hnonneg]
          change D.lower i < (D.upper i - h i) + h i
          linarith [D.lower_lt_upper i]
        · dsimp [x]
          rw [if_pos hnonneg]
          change (D.upper i - h i) + h i ≤ D.upper i
          linarith
      · have hneg : h i < 0 := lt_of_not_ge hnonneg
        constructor
        · dsimp [x]
          rw [if_neg hnonneg]
          change D.lower i < D.upper i + h i
          linarith [hi.1]
        · dsimp [x]
          rw [if_neg hnonneg]
          change D.upper i + h i ≤ D.upper i
          linarith

/--
%%handwave
name:
  The difference body of a coordinate box is measurable
statement:
  The set of displacements joining two points of a coordinate box is Borel
  measurable.
proof:
  Use the explicit product-interval description of the difference body.
-/
theorem regularCubeBoxDifferenceBody_measurableSet
    {d : ℕ} (D : BoxIntegral.Box (Fin d)) :
    MeasurableSet (regularCubeBoxDifferenceBody D) := by
  rw [regularCubeBoxDifferenceBody_eq_pi_Ioo D]
  exact MeasurableSet.univ_pi fun i ↦ measurableSet_Ioo

/--
%%handwave
name:
  Displacement slice of a box
statement:
  For a fixed displacement \(h\), the displacement slice of a box consists
  of those base points \(x\) in the box for which the translated point
  \(x+h\) is still in the same box.
-/
def regularCubeBoxDisplacementSlice
    {d : ℕ} (D : BoxIntegral.Box (Fin d)) (h : Fin d → ℝ) :
    Set (Fin d → ℝ) :=
  {x | x ∈ (D : Set (Fin d → ℝ)) ∧ x + h ∈ (D : Set (Fin d → ℝ))}

/--
%%handwave
name:
  Displacement slices are measurable
statement:
  The displacement slice of a coordinate box is a Borel measurable set.
proof:
  It is the intersection of the box with the inverse image of the box under
  the continuous translation map \(x\mapsto x+h\).
-/
theorem regularCubeBoxDisplacementSlice_measurableSet
    {d : ℕ} (D : BoxIntegral.Box (Fin d)) (h : Fin d → ℝ) :
    MeasurableSet (regularCubeBoxDisplacementSlice D h) := by
  have htranslate :
      Measurable fun x : Fin d → ℝ ↦ x + h := by
    fun_prop
  exact (D.measurableSet_coe).inter
    ((D.measurableSet_coe).preimage htranslate)

/--
%%handwave
name:
  A displacement slice lies in its box
statement:
  Every displacement slice is contained in the original box.
proof:
  Membership in the displacement slice includes membership in the original box as one of its defining conditions.
-/
theorem regularCubeBoxDisplacementSlice_subset_box
    {d : ℕ} (D : BoxIntegral.Box (Fin d)) (h : Fin d → ℝ) :
    regularCubeBoxDisplacementSlice D h ⊆
      (D : Set (Fin d → ℝ)) := by
  intro x hx
  exact hx.1

/--
%%handwave
name:
  A nonempty displacement slice determines a difference-body displacement
statement:
  If \(x\) belongs to the displacement slice of a box for displacement \(h\),
  then \(h\) belongs to the difference body of the box.
proof:
  A point (x) in the slice satisfies both (xin B) and (x+hin B).  Thus (h=(x+h)-x) is a difference of two points of (B).
-/
theorem regularCubeBoxDisplacementSlice_mem_differenceBody
    {d : ℕ} (D : BoxIntegral.Box (Fin d)) {h x : Fin d → ℝ}
    (hx : x ∈ regularCubeBoxDisplacementSlice D h) :
    h ∈ regularCubeBoxDifferenceBody D := by
  exact ⟨x, hx.1, hx.2⟩

/--
%%handwave
name:
  Displacement slices inherit disjointness
statement:
  If two boxes are disjoint, then their displacement slices for the same
  displacement are disjoint.
proof:
  Each displacement slice lies inside its box.
-/
theorem regularCubeBoxDisplacementSlice_disjoint
    {d : ℕ} {D E : BoxIntegral.Box (Fin d)} {h : Fin d → ℝ}
    (hDE : Disjoint (D : Set (Fin d → ℝ)) (E : Set (Fin d → ℝ))) :
    Disjoint (regularCubeBoxDisplacementSlice D h)
      (regularCubeBoxDisplacementSlice E h) :=
  hDE.mono (regularCubeBoxDisplacementSlice_subset_box D h)
    (regularCubeBoxDisplacementSlice_subset_box E h)

/--
%%handwave
name:
  Displacement slices of a disjoint box family are disjoint
statement:
  In a disjoint finite family of boxes, the displacement slices for any fixed
  displacement are pairwise disjoint.
proof:
  Each displacement slice is contained in its parent box.  Distinct parent boxes are disjoint, so their slices are disjoint as well.
-/
theorem regularCubeBoxDisplacementSlice_pairwiseDisjoint
    {d m : ℕ} (D : Fin m → BoxIntegral.Box (Fin d))
    (hD_disjoint : ∀ i j : Fin m, i ≠ j →
      Disjoint (D i : Set (Fin d → ℝ)) (D j : Set (Fin d → ℝ)))
    (h : Fin d → ℝ) :
    Pairwise (fun i j : Fin m ↦
      Disjoint (regularCubeBoxDisplacementSlice (D i) h)
        (regularCubeBoxDisplacementSlice (D j) h)) := by
  intro i j hij
  exact regularCubeBoxDisplacementSlice_disjoint (hD_disjoint i j hij)

/--
%%handwave
name:
  Displacement slices have no weighted overlap
statement:
  For a fixed displacement \(h\), the sum of the integrals over the
  displacement slices of a disjoint box family is bounded by the integral
  over the ambient set \(P\), provided all boxes lie in \(P\).
proof:
  The displacement slices are measurable, pairwise disjoint, and each lies
  in its box, hence in \(P\).  Countable additivity over the finite disjoint
  union identifies the sum with the integral over the union, and monotonicity
  of the restricted integral bounds this by the integral over \(P\).
-/
theorem regularCubeBoxDisplacementSlice_sum_lintegral_indicator_le_setLIntegral
    {d m : ℕ} {P : Set (Fin d → ℝ)}
    (D : Fin m → BoxIntegral.Box (Fin d))
    (hD_subsetP : ∀ i : Fin m, (D i : Set (Fin d → ℝ)) ⊆ P)
    (hD_disjoint : ∀ i j : Fin m, i ≠ j →
      Disjoint (D i : Set (Fin d → ℝ)) (D j : Set (Fin d → ℝ)))
    (h : Fin d → ℝ) (f : (Fin d → ℝ) → ℝ≥0∞) :
    ∑ i : Fin m,
        ∫⁻ x,
          (regularCubeBoxDisplacementSlice (D i) h).indicator f x
          ∂MeasureTheory.volume ≤
      ∫⁻ x in P, f x ∂MeasureTheory.volume := by
  classical
  let S : Fin m → Set (Fin d → ℝ) :=
    fun i ↦ regularCubeBoxDisplacementSlice (D i) h
  have hS_meas : ∀ i : Fin m, MeasurableSet (S i) := by
    intro i
    exact regularCubeBoxDisplacementSlice_measurableSet (D i) h
  have hS_disjoint :
      Pairwise (fun i j : Fin m ↦ Disjoint (S i) (S j)) := by
    simpa [S] using
      regularCubeBoxDisplacementSlice_pairwiseDisjoint D hD_disjoint h
  have hS_subsetP : (⋃ i : Fin m, S i) ⊆ P := by
    intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
    exact hD_subsetP i (regularCubeBoxDisplacementSlice_subset_box (D i) h hxi)
  have hsum_indicator :
      ∑ i : Fin m, ∫⁻ x, (S i).indicator f x ∂MeasureTheory.volume =
        ∑ i : Fin m, ∫⁻ x in S i, f x ∂MeasureTheory.volume := by
    refine Finset.sum_congr rfl ?_
    intro i _hi
    rw [lintegral_indicator (hS_meas i)]
  have hunion_eq_sum :
      ∫⁻ x in ⋃ i : Fin m, S i, f x ∂MeasureTheory.volume =
        ∑ i : Fin m, ∫⁻ x in S i, f x ∂MeasureTheory.volume := by
    rw [lintegral_iUnion
      (μ := MeasureTheory.volume)
      (s := S)
      hS_meas
      hS_disjoint]
    simp
  calc
    ∑ i : Fin m,
        ∫⁻ x, (regularCubeBoxDisplacementSlice (D i) h).indicator f x
          ∂MeasureTheory.volume
        = ∑ i : Fin m, ∫⁻ x, (S i).indicator f x ∂MeasureTheory.volume := by
          rfl
    _ = ∑ i : Fin m, ∫⁻ x in S i, f x ∂MeasureTheory.volume :=
          hsum_indicator
    _ = ∫⁻ x in ⋃ i : Fin m, S i, f x ∂MeasureTheory.volume :=
          hunion_eq_sum.symm
    _ ≤ ∫⁻ x in P, f x ∂MeasureTheory.volume :=
          lintegral_mono_set hS_subsetP

/--
%%handwave
name:
  The difference body of a box lies in the doubled side-length box
statement:
  The difference body of a rectangular box is contained in the centered
  closed box whose side lengths are twice the side lengths of the original
  box.
proof:
  If \(x\) and \(x+h\) both lie in the box, then in every coordinate
  \(h_j\) lies between the lower endpoint minus the upper endpoint and the
  upper endpoint minus the lower endpoint.
-/
theorem regularCubeBoxDifferenceBody_subset_Icc
    {d : ℕ} (D : BoxIntegral.Box (Fin d)) :
    regularCubeBoxDifferenceBody D ⊆
      Set.Icc (fun j : Fin d ↦ D.lower j - D.upper j)
        (fun j : Fin d ↦ D.upper j - D.lower j) := by
  intro h hh
  rcases hh with ⟨x, hx, hxh⟩
  constructor
  · intro j
    have hx_upper : x j ≤ D.upper j := (hx j).2
    have hxh_lower : D.lower j < x j + h j := (hxh j).1
    linarith
  · intro j
    have hx_lower : D.lower j < x j := (hx j).1
    have hxh_upper : x j + h j ≤ D.upper j := (hxh j).2
    linarith

/--
%%handwave
name:
  Difference bodies of regular grid boxes lie in one centered box
statement:
  In a regular grid family with mesh \(\ell\), every box difference body is
  contained in the centered coordinate box with side bounds \([-\ell,\ell]\).
proof:
  If \(x\) and \(x+h\) are in the same grid box, then each coordinate of
  \(h\) lies between minus the common side length and plus the common side
  length.
-/
theorem RegularGridBoxFamily.differenceBody_subset_common_box
    {d m : ℕ} {D : Fin m → BoxIntegral.Box (Fin d)}
    (hD : RegularGridBoxFamily D) :
    ∃ ℓ : ℝ, 0 < ℓ ∧ ∀ i : Fin m,
      regularCubeBoxDifferenceBody (D i) ⊆
        Set.Icc (fun _ : Fin d ↦ -ℓ) (fun _ : Fin d ↦ ℓ) := by
  rcases hD with ⟨ℓ, hℓ, hside, _a, _hgrid⟩
  refine ⟨ℓ, hℓ, ?_⟩
  intro i h hh
  have hI := regularCubeBoxDifferenceBody_subset_Icc (D i) hh
  constructor
  · intro j
    have hsideij : (D i).upper j - (D i).lower j = ℓ := hside i j
    have hleft : (D i).lower j - (D i).upper j = -ℓ := by linarith
    simpa [hleft] using hI.1 j
  · intro j
    have hsideij : (D i).upper j - (D i).lower j = ℓ := hside i j
    simpa [hsideij] using hI.2 j

/--
%%handwave
name:
  The common displacement box has controlled volume
statement:
  In a regular grid family with mesh \(\ell\), the centered coordinate box
  \([-\ell,\ell]^d\) has Lebesgue measure \(2^d\) times the measure of any
  grid box.
proof:
  The centered box has side length \(2\ell\) in every coordinate, while each
  grid box has side length \(\ell\) in every coordinate.  The product formula
  for rectangular boxes gives the result.
-/
theorem RegularGridBoxFamily.commonBox_volume_eq_two_pow_mul
    {d m : ℕ} {D : Fin m → BoxIntegral.Box (Fin d)}
    (hD : RegularGridBoxFamily D) (i : Fin m) :
    ∃ ℓ : ℝ, 0 < ℓ ∧
      MeasureTheory.volume (Set.Icc (fun _ : Fin d ↦ -ℓ) (fun _ : Fin d ↦ ℓ)) =
        ((2 : ℝ≥0∞) ^ d) *
          MeasureTheory.volume (D i : Set (Fin d → ℝ)) := by
  rcases hD with ⟨ℓ, hℓ, hside, _a, _hgrid⟩
  refine ⟨ℓ, hℓ, ?_⟩
  rw [Real.volume_Icc_pi, BoxIntegral.Box.coe_eq_pi, Real.volume_pi_Ioc]
  rw [show ℓ - -ℓ = 2 * ℓ by ring]
  simp_rw [show ∀ j : Fin d, (D i).upper j - (D i).lower j = ℓ by
    intro j
    exact hside i j]
  rw [show
      (∏ j : Fin d, ENNReal.ofReal (2 * ℓ)) =
        (∏ _j : Fin d, (2 : ℝ≥0∞)) *
          ∏ j : Fin d, ENNReal.ofReal ℓ by
    simp_rw [ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ))]
    rw [Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl ?_
    intro j _hj
    norm_num]
  simp [Finset.prod_const, Fintype.card_fin]

/--
%%handwave
name:
  A regular grid has a common controlled displacement box
statement:
  For any box in a regular grid family, there is one measurable centered
  coordinate box that contains all box difference bodies and whose measure is
  at most \(2^d\) times the measure of the chosen grid box.
proof:
  Use the common grid mesh \(\ell\).  Every difference body is contained in
  \([-\ell,\ell]^d\), and the product formula gives
  \(\operatorname{vol}([-\ell,\ell]^d)=2^d\operatorname{vol}(D_i)\).
-/
theorem RegularGridBoxFamily.exists_common_differenceBody_volume_le
    {d m : ℕ} {D : Fin m → BoxIntegral.Box (Fin d)}
    (hD : RegularGridBoxFamily D) (i : Fin m) :
    ∃ B : Set (Fin d → ℝ),
      MeasurableSet B ∧
        (∀ k : Fin m, regularCubeBoxDifferenceBody (D k) ⊆ B) ∧
          MeasureTheory.volume B ≤
            ((2 : ℝ≥0∞) ^ d) *
              MeasureTheory.volume (D i : Set (Fin d → ℝ)) := by
  rcases hD with ⟨ℓ, hℓ, hside, a, hgrid⟩
  let B : Set (Fin d → ℝ) :=
    Set.Icc (fun _ : Fin d ↦ -ℓ) (fun _ : Fin d ↦ ℓ)
  have hvol :
      MeasureTheory.volume B =
        ((2 : ℝ≥0∞) ^ d) *
          MeasureTheory.volume (D i : Set (Fin d → ℝ)) := by
    change
      MeasureTheory.volume (Set.Icc (fun _ : Fin d ↦ -ℓ) (fun _ : Fin d ↦ ℓ)) =
        ((2 : ℝ≥0∞) ^ d) *
          MeasureTheory.volume (D i : Set (Fin d → ℝ))
    rw [Real.volume_Icc_pi, BoxIntegral.Box.coe_eq_pi, Real.volume_pi_Ioc]
    rw [show ℓ - -ℓ = 2 * ℓ by ring]
    simp_rw [show ∀ j : Fin d, (D i).upper j - (D i).lower j = ℓ by
      intro j
      exact hside i j]
    rw [show
        (∏ j : Fin d, ENNReal.ofReal (2 * ℓ)) =
          (∏ _j : Fin d, (2 : ℝ≥0∞)) *
            ∏ j : Fin d, ENNReal.ofReal ℓ by
      simp_rw [ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ))]
      rw [Finset.prod_mul_distrib]
      congr 1
      refine Finset.prod_congr rfl ?_
      intro j _hj
      norm_num]
    simp [Finset.prod_const, Fintype.card_fin]
  refine ⟨B, measurableSet_Icc, ?_, hvol.le⟩
  intro k h hh
  have hI := regularCubeBoxDifferenceBody_subset_Icc (D k) hh
  constructor
  · intro j
    have hsidekj : (D k).upper j - (D k).lower j = ℓ := hside k j
    have hleft : (D k).lower j - (D k).upper j = -ℓ := by linarith
    simpa [B, hleft] using hI.1 j
  · intro j
    have hsidekj : (D k).upper j - (D k).lower j = ℓ := hside k j
    simpa [B, hsidekj] using hI.2 j

/--
%%handwave
name:
  The difference body of a box has controlled volume
statement:
  The Lebesgue measure of the difference body of a box in \(\mathbb R^d\) is
  at most \(2^d\) times the measure of the box.
proof:
  The difference body lies in the centered closed box with doubled side
  lengths.  The volume of a rectangular product is the product of its side
  lengths, so doubling each side multiplies the volume by \(2^d\).
-/
theorem regularCubeBoxDifferenceBody_volume_le
    {d : ℕ} (D : BoxIntegral.Box (Fin d)) :
    MeasureTheory.volume (regularCubeBoxDifferenceBody D) ≤
      ((2 : ℝ≥0∞) ^ d) *
        MeasureTheory.volume (D : Set (Fin d → ℝ)) := by
  calc
    MeasureTheory.volume (regularCubeBoxDifferenceBody D) ≤
        MeasureTheory.volume (Set.Icc
          (fun j : Fin d ↦ D.lower j - D.upper j)
          (fun j : Fin d ↦ D.upper j - D.lower j)) := by
          exact measure_mono (regularCubeBoxDifferenceBody_subset_Icc D)
    _ = ((2 : ℝ≥0∞) ^ d) *
          MeasureTheory.volume (D : Set (Fin d → ℝ)) := by
          rw [Real.volume_Icc_pi, BoxIntegral.Box.coe_eq_pi, Real.volume_pi_Ioc]
          simp_rw [show ∀ j : Fin d,
              D.upper j - D.lower j - (D.lower j - D.upper j) =
                2 * (D.upper j - D.lower j) by
            intro j
            ring]
          rw [show
              (∏ i : Fin d,
                  ENNReal.ofReal (2 * (D.upper i - D.lower i))) =
                (∏ _i : Fin d, (2 : ℝ≥0∞)) *
                  ∏ i : Fin d, ENNReal.ofReal (D.upper i - D.lower i) by
            simp_rw [ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ))]
            rw [Finset.prod_mul_distrib]
            congr 1
            refine Finset.prod_congr rfl ?_
            intro i _hi
            norm_num]
          simp [Finset.prod_const, Fintype.card_fin]

/--
%%handwave
name:
  Difference-body displacements are small for a small-diameter box
statement:
  If all pairs of points in a box are less than \(\delta\) apart, then every
  displacement in the difference body of the box has norm less than
  \(\delta\).
proof:
  A displacement \(h\) in the difference body has \(x\) and \(x+h\) in the
  box.  Applying the diameter hypothesis to this pair gives
  \(\|h\|=\operatorname{dist}(x,x+h)<\delta\).
-/
theorem regularCubeBoxDifferenceBody_subset_ball_of_diameter
    {d : ℕ} (D : BoxIntegral.Box (Fin d)) {δ : ℝ}
    (hD_diam : ∀ x ∈ (D : Set (Fin d → ℝ)),
      ∀ y ∈ (D : Set (Fin d → ℝ)), dist x y < δ) :
    regularCubeBoxDifferenceBody D ⊆ Metric.ball 0 δ := by
  intro h hh
  rcases hh with ⟨x, hx, hxh⟩
  have hdist : dist x (x + h) < δ := hD_diam x hx (x + h) hxh
  rw [Metric.mem_ball, dist_eq_norm]
  simpa [dist_eq_norm] using hdist

/--
%%handwave
name:
  Squared extended norm of a real number
statement:
  For \(r\in\mathbb R\),
  \(\lVert r\rVert_{\!e}^{\,2}=\operatorname{ofReal}(r^2)\).
proof:
  Write the extended norm as the nonnegative-real embedding of \(|r|\), move
  the square through that embedding, and use \(|r|^2=r^2\).
-/
private theorem real_enorm_rpow_two_eq_ofReal_sq (r : ℝ) :
    ‖r‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (r ^ 2) := by
  rw [← ofReal_norm]
  rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg r) (by norm_num : 0 ≤ (2 : ℝ))]
  norm_num [Real.rpow_natCast, sq, Real.norm_eq_abs]

/--
%%handwave
name:
  Square-integral bound from an \(L^2\)-norm bound
statement:
  If \(\lVert f\rVert_{L^2(\mu)}\le\eta\), then
  \[\int\lVert f(x)\rVert_{\!e}^{\,2}\,d\mu\le\eta^2.\]
proof:
  Express the \(L^2\)-norm as the square root of the extended square integral,
  then square the inequality using monotonicity of positive powers.
-/
private theorem lintegral_sq_le_of_eLpNorm_two_le
    {α : Type} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} {η : ℝ≥0∞}
    (h : eLpNorm f 2 μ ≤ η) :
    ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ ≤ η ^ (2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞))] at h
  simp only [ENNReal.toReal_ofNat, one_div] at h
  exact (ENNReal.rpow_inv_le_iff (by norm_num : 0 < (2 : ℝ))).1 h

/--
%%handwave
name:
  Variance is bounded by pairwise oscillation on a box
statement:
  On a positive finite-measure box, the squared error from the box average is
  bounded by the normalized mean pairwise squared oscillation on the same
  box.
proof:
  For each fixed \(x\), write \(u(x)-u_D\) as the average over \(y\in D\)
  of \(u(x)-u(y)\).  Jensen's inequality for the convex function
  \(t\mapsto |t|^2\) gives the pointwise bound by the average in \(y\).
  Integrating in \(x\) gives the stated estimate.
-/
theorem regularCubeBoxAverageCoeff_lintegral_sq_le_pairwiseOscillation
    {d : ℕ} {P : Set (Fin d → ℝ)}
    (u : ℕ → (Fin d → ℝ) → ℝ)
    (hmemP : ∀ n : ℕ, MemLp (u n) 2 (MeasureTheory.volume.restrict P))
    {m : ℕ} (D : Fin m → BoxIntegral.Box (Fin d))
    (hD_subsetP : ∀ i : Fin m, (D i : Set (Fin d → ℝ)) ⊆ P)
    (hD_posP : ∀ i : Fin m, 0 < (MeasureTheory.volume.restrict P)
      (D i : Set (Fin d → ℝ)))
    (hD_finiteP : ∀ i : Fin m, (MeasureTheory.volume.restrict P)
      (D i : Set (Fin d → ℝ)) ≠ (⊤ : ℝ≥0∞))
    (n : ℕ) (i : Fin m) :
    ∫⁻ x in (D i : Set (Fin d → ℝ)),
      ‖u n x - regularCubeBoxAverageCoeff u D n i‖ₑ ^ (2 : ℝ)
        ∂MeasureTheory.volume ≤
      regularCubeBoxPairwiseOscillation u D n i := by
  classical
  let s : Set (Fin d → ℝ) := (D i : Set (Fin d → ℝ))
  have hs_meas : MeasurableSet s := (D i).measurableSet_coe
  have hmeasure :
      (MeasureTheory.volume.restrict P) s = MeasureTheory.volume s := by
    rw [Measure.restrict_apply hs_meas]
    have h_inter : s ∩ P = s := Set.inter_eq_left.mpr (hD_subsetP i)
    rw [h_inter]
  have hs_pos : MeasureTheory.volume s ≠ 0 := by
    have hs_pos' : 0 < MeasureTheory.volume s := by
      rw [← hmeasure]
      simpa [s] using hD_posP i
    exact ne_of_gt hs_pos'
  have hs_finite : MeasureTheory.volume s ≠ (⊤ : ℝ≥0∞) := by
    rw [← hmeasure]
    simpa [s] using hD_finiteP i
  haveI : IsFiniteMeasure (MeasureTheory.volume.restrict s) :=
    ⟨by
      simpa using (lt_top_iff_ne_top.mpr hs_finite : MeasureTheory.volume s < ⊤)⟩
  have hμDP :
      MeasureTheory.volume.restrict s ≤ MeasureTheory.volume.restrict P :=
    Measure.restrict_mono (hD_subsetP i) le_rfl
  have hu_memD : MemLp (u n) 2 (MeasureTheory.volume.restrict s) :=
    (hmemP n).mono_measure hμDP
  have hu_intD : IntegrableOn (u n) s MeasureTheory.volume :=
    hu_memD.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hpoint :
      ∀ x ∈ s,
        ‖u n x - regularCubeBoxAverageCoeff u D n i‖ₑ ^ (2 : ℝ) ≤
          (MeasureTheory.volume s)⁻¹ *
            ∫⁻ y in s, ‖u n x - u n y‖ₑ ^ (2 : ℝ) ∂MeasureTheory.volume := by
    intro x _hx
    let g : ℝ → ℝ := fun z ↦ (u n x - z) ^ 2
    have hg_conv : ConvexOn ℝ Set.univ g := by
      let A : ℝ →ᵃ[ℝ] ℝ := AffineMap.const ℝ ℝ (u n x) - AffineMap.id ℝ ℝ
      have hsq : ConvexOn ℝ Set.univ (fun z : ℝ ↦ z ^ (2 : ℕ)) :=
        Even.convexOn_pow (show Even (2 : ℕ) by norm_num)
      simpa [g, A, Function.comp_def] using hsq.comp_affineMap A
    have hg_cont : ContinuousOn g Set.univ := by
      unfold g
      fun_prop
    have hsq_memD : MemLp (fun y ↦ u n x - u n y) 2
        (MeasureTheory.volume.restrict s) := by
      simpa [sub_eq_add_neg] using (memLp_const (u n x)).sub hu_memD
    have hsq_intD : IntegrableOn (fun y ↦ (u n x - u n y) ^ 2)
        s MeasureTheory.volume := by
      simpa [IntegrableOn, g, Function.comp_def] using hsq_memD.integrable_sq
    have hJensen :
        g (⨍ y in s, u n y ∂MeasureTheory.volume) ≤
          ⨍ y in s, g (u n y) ∂MeasureTheory.volume :=
      hg_conv.map_set_average_le hg_cont isClosed_univ hs_pos hs_finite
        (Filter.Eventually.of_forall fun _ ↦ Set.mem_univ _)
        hu_intD
        (by simpa [g, Function.comp_def] using hsq_intD)
    have hJensen' :
        (u n x - regularCubeBoxAverageCoeff u D n i) ^ 2 ≤
          ⨍ y in s, (u n x - u n y) ^ 2 ∂MeasureTheory.volume := by
      simpa [g, s, regularCubeBoxAverageCoeff_eq_setAverage] using hJensen
    have hJensen_en :
        ENNReal.ofReal ((u n x - regularCubeBoxAverageCoeff u D n i) ^ 2) ≤
          ENNReal.ofReal
            (⨍ y in s, (u n x - u n y) ^ 2 ∂MeasureTheory.volume) :=
      ENNReal.ofReal_le_ofReal hJensen'
    have hsq_nonneg :
        0 ≤ᵐ[MeasureTheory.volume.restrict s] fun y ↦ (u n x - u n y) ^ 2 :=
      Filter.Eventually.of_forall fun y ↦ sq_nonneg (u n x - u n y)
    have hsetAvg :
        ENNReal.ofReal
            (⨍ y in s, (u n x - u n y) ^ 2 ∂MeasureTheory.volume) =
          (∫⁻ y in s,
              ENNReal.ofReal ((u n x - u n y) ^ 2) ∂MeasureTheory.volume) /
            MeasureTheory.volume s := by
      simpa using
        (ofReal_setAverage (μ := MeasureTheory.volume) (s := s)
          (f := fun y ↦ (u n x - u n y) ^ 2) hsq_intD hsq_nonneg)
    calc
      ‖u n x - regularCubeBoxAverageCoeff u D n i‖ₑ ^ (2 : ℝ)
          = ENNReal.ofReal ((u n x - regularCubeBoxAverageCoeff u D n i) ^ 2) := by
            exact real_enorm_rpow_two_eq_ofReal_sq _
      _ ≤ ENNReal.ofReal
            (⨍ y in s, (u n x - u n y) ^ 2 ∂MeasureTheory.volume) :=
            hJensen_en
      _ = (MeasureTheory.volume s)⁻¹ *
            ∫⁻ y in s, ‖u n x - u n y‖ₑ ^ (2 : ℝ) ∂MeasureTheory.volume := by
            rw [hsetAvg, div_eq_mul_inv, mul_comm]
            congr 1
            refine setLIntegral_congr_fun hs_meas ?_
            intro y _hy
            exact (real_enorm_rpow_two_eq_ofReal_sq (u n x - u n y)).symm
  calc
    ∫⁻ x in (D i : Set (Fin d → ℝ)),
        ‖u n x - regularCubeBoxAverageCoeff u D n i‖ₑ ^ (2 : ℝ)
        ∂MeasureTheory.volume
        = ∫⁻ x in s,
            ‖u n x - regularCubeBoxAverageCoeff u D n i‖ₑ ^ (2 : ℝ)
            ∂MeasureTheory.volume := rfl
    _ ≤ ∫⁻ x in s,
          (MeasureTheory.volume s)⁻¹ *
            ∫⁻ y in s, ‖u n x - u n y‖ₑ ^ (2 : ℝ) ∂MeasureTheory.volume
          ∂MeasureTheory.volume := by
          exact setLIntegral_mono' hs_meas hpoint
    _ = (MeasureTheory.volume s)⁻¹ *
          ∫⁻ x in s,
            ∫⁻ y in s, ‖u n x - u n y‖ₑ ^ (2 : ℝ) ∂MeasureTheory.volume
          ∂MeasureTheory.volume := by
          rw [lintegral_const_mul' (MeasureTheory.volume s)⁻¹ _
            (ENNReal.inv_ne_top.mpr hs_pos)]
    _ = regularCubeBoxPairwiseOscillation u D n i := by
          simp [regularCubeBoxPairwiseOscillation, s]

/--
%%handwave
name:
  Pairwise oscillation on one box is bounded by displacement integrals
statement:
  The normalized pairwise squared oscillation on a box is bounded by the
  integral of translated squared differences over the box difference body,
  with the spatial integration enlarged to any ambient set containing the
  box.
proof:
  Use the measure-preserving shear \((h,x)\mapsto (x,x+h)\) to rewrite pairs
  of points in the box as a base point and a displacement.  If both \(x\) and
  \(x+h\) lie in the box, then \(h\) belongs to the difference body and
  \(x\) belongs to the ambient set.  Tonelli's inequality then bounds the
  product integral by the iterated displacement integral.
-/
theorem regularCubeBoxPairwiseOscillation_le_differenceBody_lintegral_translation
    {d : ℕ} {P : Set (Fin d → ℝ)}
    (u : ℕ → (Fin d → ℝ) → ℝ)
    (hmemP : ∀ n : ℕ, MemLp (u n) 2 (MeasureTheory.volume.restrict P))
    {m : ℕ} (D : Fin m → BoxIntegral.Box (Fin d))
    (hD_subsetP : ∀ i : Fin m, (D i : Set (Fin d → ℝ)) ⊆ P)
    (n : ℕ) (i : Fin m) :
    regularCubeBoxPairwiseOscillation u D n i ≤
      (MeasureTheory.volume (D i : Set (Fin d → ℝ)))⁻¹ *
        ∫⁻ h in regularCubeBoxDifferenceBody (D i),
          ∫⁻ x in P, ‖u n (x + h) - u n x‖ₑ ^ (2 : ℝ)
            ∂MeasureTheory.volume ∂MeasureTheory.volume := by
  classical
  let V : Type := Fin d → ℝ
  let μ : Measure V := MeasureTheory.volume
  let s : Set V := (D i : Set (Fin d → ℝ))
  let B : Set V := regularCubeBoxDifferenceBody (D i)
  let shear : V × V → V × V := fun q ↦ (q.2, q.2 + q.1)
  let F : V × V → ℝ≥0∞ :=
    fun p ↦ ‖u n p.2 - u n p.1‖ₑ ^ (2 : ℝ)
  let G : V × V → ℝ≥0∞ :=
    fun q ↦ ‖u n (q.2 + q.1) - u n q.2‖ₑ ^ (2 : ℝ)
  have hs_meas : MeasurableSet s := (D i).measurableSet_coe
  have hs_subsetP : s ⊆ P := hD_subsetP i
  have hμsP : μ.restrict s ≤ μ.restrict P :=
    Measure.restrict_mono hs_subsetP le_rfl
  have hu_mem_s : MemLp (u n) 2 (μ.restrict s) :=
    (hmemP n).mono_measure hμsP
  have hu_ae_s : AEMeasurable (u n) (μ.restrict s) :=
    hu_mem_s.aestronglyMeasurable.aemeasurable
  have hF_ae_restrict :
      AEMeasurable F ((μ.prod μ).restrict (s ×ˢ s)) := by
    have hx :
        AEMeasurable (fun p : V × V ↦ u n p.1)
          ((μ.restrict s).prod (μ.restrict s)) :=
      hu_ae_s.comp_fst
    have hy :
        AEMeasurable (fun p : V × V ↦ u n p.2)
          ((μ.restrict s).prod (μ.restrict s)) :=
      hu_ae_s.comp_snd
    have hdiff :
        AEMeasurable (fun p : V × V ↦ u n p.2 - u n p.1)
          ((μ.restrict s).prod (μ.restrict s)) :=
      hy.sub hx
    have hF :
        AEMeasurable (fun p : V × V ↦ ‖u n p.2 - u n p.1‖ₑ ^ (2 : ℝ))
          ((μ.restrict s).prod (μ.restrict s)) :=
      hdiff.enorm.pow_const _
    simpa [μ, s, F, Measure.prod_restrict] using hF
  have hpair_eq_prod :
      (∫⁻ x in s, ∫⁻ y in s,
          ‖u n x - u n y‖ₑ ^ (2 : ℝ) ∂μ ∂μ) =
        ∫⁻ p in s ×ˢ s, F p ∂(μ.prod μ) := by
    calc
      (∫⁻ x in s, ∫⁻ y in s,
          ‖u n x - u n y‖ₑ ^ (2 : ℝ) ∂μ ∂μ)
          = ∫⁻ x in s, ∫⁻ y in s, F (x, y) ∂μ ∂μ := by
            refine setLIntegral_congr_fun hs_meas ?_
            intro x _hx
            refine setLIntegral_congr_fun hs_meas ?_
            intro y _hy
            change ‖u n x - u n y‖ₑ ^ (2 : ℝ) =
              ‖u n y - u n x‖ₑ ^ (2 : ℝ)
            rw [enorm_sub_rev]
      _ = ∫⁻ p in s ×ˢ s, F p ∂(μ.prod μ) := by
            exact (MeasureTheory.setLIntegral_prod (μ := μ) (ν := μ)
              (s := s) (t := s) F hF_ae_restrict).symm
  have hshear_mp :
      MeasurePreserving shear (μ.prod μ) (μ.prod μ) := by
    simpa [μ, shear] using
      (MeasureTheory.measurePreserving_prod_add_swap
        (μ := (MeasureTheory.volume : Measure V))
        (ν := (MeasureTheory.volume : Measure V)))
  have hshear_emb : MeasurableEmbedding shear := by
    simpa [shear] using
      ((MeasurableEquiv.prodComm : V × V ≃ᵐ V × V).trans
        (MeasurableEquiv.shearAddRight V)).measurableEmbedding
  have hshear :
      (∫⁻ q in shear ⁻¹' (s ×ˢ s), F (shear q) ∂(μ.prod μ)) =
        ∫⁻ p in s ×ˢ s, F p ∂(μ.prod μ) :=
    hshear_mp.setLIntegral_comp_preimage_emb hshear_emb F (s ×ˢ s)
  have hpre_meas : MeasurableSet (shear ⁻¹' (s ×ˢ s)) :=
    (hs_meas.prod hs_meas).preimage hshear_emb.measurable
  have hindicator_le :
      ∀ q : V × V,
        (shear ⁻¹' (s ×ˢ s)).indicator (fun q ↦ F (shear q)) q ≤
          B.indicator (fun h ↦
            P.indicator (fun x ↦ G (h, x)) q.2) q.1 := by
    intro q
    by_cases hq : q ∈ shear ⁻¹' (s ×ˢ s)
    · have hx : q.2 ∈ s := hq.1
      have hxh : q.2 + q.1 ∈ s := hq.2
      have hhB : q.1 ∈ B := ⟨q.2, hx, hxh⟩
      have hxP : q.2 ∈ P := hs_subsetP hx
      simp [Set.indicator_of_mem hq, Set.indicator_of_mem hhB,
        Set.indicator_of_mem hxP, F, G, shear]
    · simp [Set.indicator_of_notMem hq]
  have hprod_le :
      ∫⁻ p in s ×ˢ s, F p ∂(μ.prod μ) ≤
        ∫⁻ h in B, ∫⁻ x in P, G (h, x) ∂μ ∂μ := by
    calc
      ∫⁻ p in s ×ˢ s, F p ∂(μ.prod μ)
          = ∫⁻ q in shear ⁻¹' (s ×ˢ s), F (shear q) ∂(μ.prod μ) :=
            hshear.symm
      _ = ∫⁻ q,
            (shear ⁻¹' (s ×ˢ s)).indicator (fun q ↦ F (shear q)) q
            ∂(μ.prod μ) := by
            rw [lintegral_indicator hpre_meas]
      _ ≤ ∫⁻ q,
            B.indicator (fun h ↦
              P.indicator (fun x ↦ G (h, x)) q.2) q.1
            ∂(μ.prod μ) :=
            lintegral_mono hindicator_le
      _ ≤ ∫⁻ h, ∫⁻ x,
            B.indicator (fun h ↦
              P.indicator (fun x ↦ G (h, x)) x) h ∂μ ∂μ :=
            MeasureTheory.lintegral_prod_le
              (μ := μ) (ν := μ)
              (f := fun q : V × V ↦
                B.indicator (fun h ↦
                  P.indicator (fun x ↦ G (h, x)) q.2) q.1)
      _ ≤ ∫⁻ h, B.indicator (fun h ↦
            ∫⁻ x in P, G (h, x) ∂μ) h ∂μ := by
            refine lintegral_mono ?_
            intro h
            by_cases hh : h ∈ B
            · rw [Set.indicator_of_mem hh]
              calc
                ∫⁻ x,
                    B.indicator (fun h ↦
                      P.indicator (fun x ↦ G (h, x)) x) h ∂μ
                    = ∫⁻ x, P.indicator (fun x ↦ G (h, x)) x ∂μ := by
                      simp [Set.indicator_of_mem hh]
                _ ≤ ∫⁻ x in P, G (h, x) ∂μ :=
                      lintegral_indicator_le (fun x ↦ G (h, x)) P
            · rw [Set.indicator_of_notMem hh]
              simp [Set.indicator_of_notMem hh]
      _ ≤ ∫⁻ h in B, ∫⁻ x in P, G (h, x) ∂μ ∂μ :=
            lintegral_indicator_le (fun h ↦ ∫⁻ x in P, G (h, x) ∂μ) B
  calc
    regularCubeBoxPairwiseOscillation u D n i
        = (MeasureTheory.volume (D i : Set (Fin d → ℝ)))⁻¹ *
            ∫⁻ x in s,
              ∫⁻ y in s,
                ‖u n x - u n y‖ₑ ^ (2 : ℝ) ∂μ ∂μ := by
          rfl
    _ ≤ (MeasureTheory.volume (D i : Set (Fin d → ℝ)))⁻¹ *
          ∫⁻ h in B, ∫⁻ x in P, G (h, x) ∂μ ∂μ := by
          exact mul_le_mul_right (hpair_eq_prod.trans_le hprod_le) _
    _ = (MeasureTheory.volume (D i : Set (Fin d → ℝ)))⁻¹ *
        ∫⁻ h in regularCubeBoxDifferenceBody (D i),
          ∫⁻ x in P, ‖u n (x + h) - u n x‖ₑ ^ (2 : ℝ)
            ∂MeasureTheory.volume ∂MeasureTheory.volume := by
          rfl

/--
%%handwave
name:
  Pairwise oscillation on one box is bounded by localized displacement slices
statement:
  The normalized pairwise squared oscillation on a box is bounded by the
  displacement integral over the box difference body, keeping only the base
  points \(x\) for which both \(x\) and \(x+h\) remain in the box.
proof:
  Use the measure-preserving shear \((h,x)\mapsto (x,x+h)\) to rewrite
  pairs of points in the box as a base point and a displacement.  Unlike the
  coarser ambient-set estimate, this keeps the indicator of the exact
  displacement slice, which is the form needed to sum over a disjoint
  regular grid.
-/
theorem regularCubeBoxPairwiseOscillation_le_displacementSlice_lintegral_translation
    {d : ℕ} {P : Set (Fin d → ℝ)}
    (u : ℕ → (Fin d → ℝ) → ℝ)
    (hmemP : ∀ n : ℕ, MemLp (u n) 2 (MeasureTheory.volume.restrict P))
    {m : ℕ} (D : Fin m → BoxIntegral.Box (Fin d))
    (hD_subsetP : ∀ i : Fin m, (D i : Set (Fin d → ℝ)) ⊆ P)
    (n : ℕ) (i : Fin m) :
    regularCubeBoxPairwiseOscillation u D n i ≤
      (MeasureTheory.volume (D i : Set (Fin d → ℝ)))⁻¹ *
        ∫⁻ h in regularCubeBoxDifferenceBody (D i),
          ∫⁻ x,
            (regularCubeBoxDisplacementSlice (D i) h).indicator
              (fun x ↦ ‖u n (x + h) - u n x‖ₑ ^ (2 : ℝ)) x
            ∂MeasureTheory.volume ∂MeasureTheory.volume := by
  classical
  let V : Type := Fin d → ℝ
  let μ : Measure V := MeasureTheory.volume
  let s : Set V := (D i : Set (Fin d → ℝ))
  let B : Set V := regularCubeBoxDifferenceBody (D i)
  let S : V → Set V := fun h ↦ regularCubeBoxDisplacementSlice (D i) h
  let shear : V × V → V × V := fun q ↦ (q.2, q.2 + q.1)
  let F : V × V → ℝ≥0∞ :=
    fun p ↦ ‖u n p.2 - u n p.1‖ₑ ^ (2 : ℝ)
  let G : V × V → ℝ≥0∞ :=
    fun q ↦ ‖u n (q.2 + q.1) - u n q.2‖ₑ ^ (2 : ℝ)
  have hs_meas : MeasurableSet s := (D i).measurableSet_coe
  have hs_subsetP : s ⊆ P := hD_subsetP i
  have hμsP : μ.restrict s ≤ μ.restrict P :=
    Measure.restrict_mono hs_subsetP le_rfl
  have hu_mem_s : MemLp (u n) 2 (μ.restrict s) :=
    (hmemP n).mono_measure hμsP
  have hu_ae_s : AEMeasurable (u n) (μ.restrict s) :=
    hu_mem_s.aestronglyMeasurable.aemeasurable
  have hF_ae_restrict :
      AEMeasurable F ((μ.prod μ).restrict (s ×ˢ s)) := by
    have hx :
        AEMeasurable (fun p : V × V ↦ u n p.1)
          ((μ.restrict s).prod (μ.restrict s)) :=
      hu_ae_s.comp_fst
    have hy :
        AEMeasurable (fun p : V × V ↦ u n p.2)
          ((μ.restrict s).prod (μ.restrict s)) :=
      hu_ae_s.comp_snd
    have hdiff :
        AEMeasurable (fun p : V × V ↦ u n p.2 - u n p.1)
          ((μ.restrict s).prod (μ.restrict s)) :=
      hy.sub hx
    have hF :
        AEMeasurable (fun p : V × V ↦ ‖u n p.2 - u n p.1‖ₑ ^ (2 : ℝ))
          ((μ.restrict s).prod (μ.restrict s)) :=
      hdiff.enorm.pow_const _
    simpa [μ, s, F, Measure.prod_restrict] using hF
  have hpair_eq_prod :
      (∫⁻ x in s, ∫⁻ y in s,
          ‖u n x - u n y‖ₑ ^ (2 : ℝ) ∂μ ∂μ) =
        ∫⁻ p in s ×ˢ s, F p ∂(μ.prod μ) := by
    calc
      (∫⁻ x in s, ∫⁻ y in s,
          ‖u n x - u n y‖ₑ ^ (2 : ℝ) ∂μ ∂μ)
          = ∫⁻ x in s, ∫⁻ y in s, F (x, y) ∂μ ∂μ := by
            refine setLIntegral_congr_fun hs_meas ?_
            intro x _hx
            refine setLIntegral_congr_fun hs_meas ?_
            intro y _hy
            change ‖u n x - u n y‖ₑ ^ (2 : ℝ) =
              ‖u n y - u n x‖ₑ ^ (2 : ℝ)
            rw [enorm_sub_rev]
      _ = ∫⁻ p in s ×ˢ s, F p ∂(μ.prod μ) := by
            exact (MeasureTheory.setLIntegral_prod (μ := μ) (ν := μ)
              (s := s) (t := s) F hF_ae_restrict).symm
  have hshear_mp :
      MeasurePreserving shear (μ.prod μ) (μ.prod μ) := by
    simpa [μ, shear] using
      (MeasureTheory.measurePreserving_prod_add_swap
        (μ := (MeasureTheory.volume : Measure V))
        (ν := (MeasureTheory.volume : Measure V)))
  have hshear_emb : MeasurableEmbedding shear := by
    simpa [shear] using
      ((MeasurableEquiv.prodComm : V × V ≃ᵐ V × V).trans
        (MeasurableEquiv.shearAddRight V)).measurableEmbedding
  have hshear :
      (∫⁻ q in shear ⁻¹' (s ×ˢ s), F (shear q) ∂(μ.prod μ)) =
        ∫⁻ p in s ×ˢ s, F p ∂(μ.prod μ) :=
    hshear_mp.setLIntegral_comp_preimage_emb hshear_emb F (s ×ˢ s)
  have hpre_meas : MeasurableSet (shear ⁻¹' (s ×ˢ s)) :=
    (hs_meas.prod hs_meas).preimage hshear_emb.measurable
  have hindicator_le :
      ∀ q : V × V,
        (shear ⁻¹' (s ×ˢ s)).indicator (fun q ↦ F (shear q)) q ≤
          B.indicator (fun h ↦
            (S h).indicator (fun x ↦ G (h, x)) q.2) q.1 := by
    intro q
    by_cases hq : q ∈ shear ⁻¹' (s ×ˢ s)
    · have hx : q.2 ∈ s := hq.1
      have hxh : q.2 + q.1 ∈ s := hq.2
      have hhB : q.1 ∈ B := ⟨q.2, hx, hxh⟩
      have hxS : q.2 ∈ S q.1 := ⟨hx, hxh⟩
      simp [Set.indicator_of_mem hq, Set.indicator_of_mem hhB,
        Set.indicator_of_mem hxS, F, G, S, B, shear]
    · simp [Set.indicator_of_notMem hq]
  have hprod_le :
      ∫⁻ p in s ×ˢ s, F p ∂(μ.prod μ) ≤
        ∫⁻ h in B, ∫⁻ x, (S h).indicator (fun x ↦ G (h, x)) x ∂μ ∂μ := by
    calc
      ∫⁻ p in s ×ˢ s, F p ∂(μ.prod μ)
          = ∫⁻ q in shear ⁻¹' (s ×ˢ s), F (shear q) ∂(μ.prod μ) :=
            hshear.symm
      _ = ∫⁻ q,
            (shear ⁻¹' (s ×ˢ s)).indicator (fun q ↦ F (shear q)) q
            ∂(μ.prod μ) := by
            rw [lintegral_indicator hpre_meas]
      _ ≤ ∫⁻ q,
            B.indicator (fun h ↦
              (S h).indicator (fun x ↦ G (h, x)) q.2) q.1
            ∂(μ.prod μ) :=
            lintegral_mono hindicator_le
      _ ≤ ∫⁻ h, ∫⁻ x,
            B.indicator (fun h ↦
              (S h).indicator (fun x ↦ G (h, x)) x) h ∂μ ∂μ :=
            MeasureTheory.lintegral_prod_le
              (μ := μ) (ν := μ)
              (f := fun q : V × V ↦
                B.indicator (fun h ↦
                  (S h).indicator (fun x ↦ G (h, x)) q.2) q.1)
      _ ≤ ∫⁻ h, B.indicator (fun h ↦
            ∫⁻ x, (S h).indicator (fun x ↦ G (h, x)) x ∂μ) h ∂μ := by
            refine lintegral_mono ?_
            intro h
            by_cases hh : h ∈ B
            · rw [Set.indicator_of_mem hh]
              simp [Set.indicator_of_mem hh]
            · rw [Set.indicator_of_notMem hh]
              simp [Set.indicator_of_notMem hh]
      _ ≤ ∫⁻ h in B, ∫⁻ x, (S h).indicator (fun x ↦ G (h, x)) x ∂μ ∂μ :=
            lintegral_indicator_le
              (fun h ↦ ∫⁻ x, (S h).indicator (fun x ↦ G (h, x)) x ∂μ) B
  calc
    regularCubeBoxPairwiseOscillation u D n i
        = (MeasureTheory.volume (D i : Set (Fin d → ℝ)))⁻¹ *
            ∫⁻ x in s,
              ∫⁻ y in s,
                ‖u n x - u n y‖ₑ ^ (2 : ℝ) ∂μ ∂μ := by
          rfl
    _ ≤ (MeasureTheory.volume (D i : Set (Fin d → ℝ)))⁻¹ *
          ∫⁻ h in B, ∫⁻ x, (S h).indicator (fun x ↦ G (h, x)) x ∂μ ∂μ := by
          exact mul_le_mul_right (hpair_eq_prod.trans_le hprod_le) _
    _ = (MeasureTheory.volume (D i : Set (Fin d → ℝ)))⁻¹ *
        ∫⁻ h in regularCubeBoxDifferenceBody (D i),
          ∫⁻ x,
            (regularCubeBoxDisplacementSlice (D i) h).indicator
              (fun x ↦ ‖u n (x + h) - u n x‖ₑ ^ (2 : ℝ)) x
            ∂MeasureTheory.volume ∂MeasureTheory.volume := by
          rfl

/--
%%handwave
name:
  One-box pairwise oscillation is bounded by the translation modulus
statement:
  If every displacement allowed by the diameter of a box has squared
  \(L^2(P)\)-translation integral at most \(\eta^2\), then the normalized
  pairwise squared oscillation on that box is at most \(2^d\eta^2\).
proof:
  Apply the displacement form of the pairwise oscillation.  On the difference
  body of the box all displacements are shorter than the prescribed scale,
  so the inner spatial integral is bounded by the translation modulus.  The
  difference body has volume at most \(2^d\) times the box volume, and the
  normalization by the box volume cancels.
-/
theorem regularCubeBoxPairwiseOscillation_le_two_pow_mul_sq_lintegral_translation_bound
    {d : ℕ} {P : Set (Fin d → ℝ)}
    (u : ℕ → (Fin d → ℝ) → ℝ)
    (hmemP : ∀ n : ℕ, MemLp (u n) 2 (MeasureTheory.volume.restrict P))
    {η : ℝ≥0∞} {δ : ℝ}
    {m : ℕ} (D : Fin m → BoxIntegral.Box (Fin d))
    (hD_subsetP : ∀ i : Fin m, (D i : Set (Fin d → ℝ)) ⊆ P)
    (hD_posP : ∀ i : Fin m, 0 < (MeasureTheory.volume.restrict P)
      (D i : Set (Fin d → ℝ)))
    (hD_finiteP : ∀ i : Fin m, (MeasureTheory.volume.restrict P)
      (D i : Set (Fin d → ℝ)) ≠ (⊤ : ℝ≥0∞))
    (hD_diam : ∀ i : Fin m, ∀ x ∈ (D i : Set (Fin d → ℝ)),
      ∀ y ∈ (D i : Set (Fin d → ℝ)), dist x y < δ)
    (htranslationSq :
      ∀ h : Fin d → ℝ, ‖h‖ < δ →
        ∀ n : ℕ,
          ∫⁻ z in P, ‖u n (z + h) - u n z‖ₑ ^ (2 : ℝ)
            ∂MeasureTheory.volume ≤ η ^ (2 : ℝ)) :
    ∀ n : ℕ, ∀ i : Fin m,
      regularCubeBoxPairwiseOscillation u D n i ≤
        ((2 : ℝ≥0∞) ^ d) * η ^ (2 : ℝ) := by
  intro n i
  let s : Set (Fin d → ℝ) := (D i : Set (Fin d → ℝ))
  let B : Set (Fin d → ℝ) := regularCubeBoxDifferenceBody (D i)
  have hs_meas : MeasurableSet s := (D i).measurableSet_coe
  have hmeasure :
      (MeasureTheory.volume.restrict P) s = MeasureTheory.volume s := by
    rw [Measure.restrict_apply hs_meas]
    have h_inter : s ∩ P = s := Set.inter_eq_left.mpr (hD_subsetP i)
    rw [h_inter]
  have hs_pos : MeasureTheory.volume s ≠ 0 := by
    have hs_pos' : 0 < MeasureTheory.volume s := by
      rw [← hmeasure]
      simpa [s] using hD_posP i
    exact ne_of_gt hs_pos'
  have hs_finite : MeasureTheory.volume s ≠ (⊤ : ℝ≥0∞) := by
    rw [← hmeasure]
    simpa [s] using hD_finiteP i
  have hB_translate :
      ∫⁻ h in B,
          ∫⁻ x in P, ‖u n (x + h) - u n x‖ₑ ^ (2 : ℝ)
            ∂MeasureTheory.volume ∂MeasureTheory.volume ≤
        ∫⁻ _h in B, η ^ (2 : ℝ) ∂MeasureTheory.volume := by
    refine setLIntegral_mono measurable_const ?_
    intro h hhB
    have hh_small : ‖h‖ < δ := by
      have hball :=
        regularCubeBoxDifferenceBody_subset_ball_of_diameter
          (D i) (hD_diam i) hhB
      simpa [Metric.mem_ball, dist_eq_norm] using hball
    exact htranslationSq h hh_small n
  have hB_volume :
      MeasureTheory.volume B ≤
        ((2 : ℝ≥0∞) ^ d) * MeasureTheory.volume s := by
    simpa [B, s] using regularCubeBoxDifferenceBody_volume_le (D i)
  calc
    regularCubeBoxPairwiseOscillation u D n i
        ≤ (MeasureTheory.volume s)⁻¹ *
            ∫⁻ h in B,
              ∫⁻ x in P, ‖u n (x + h) - u n x‖ₑ ^ (2 : ℝ)
                ∂MeasureTheory.volume ∂MeasureTheory.volume := by
          simpa [s, B] using
            regularCubeBoxPairwiseOscillation_le_differenceBody_lintegral_translation
              u hmemP D hD_subsetP n i
    _ ≤ (MeasureTheory.volume s)⁻¹ *
          ∫⁻ _h in B, η ^ (2 : ℝ) ∂MeasureTheory.volume := by
          exact mul_le_mul_right hB_translate _
    _ = (MeasureTheory.volume s)⁻¹ *
          (η ^ (2 : ℝ) * MeasureTheory.volume B) := by
          rw [setLIntegral_const]
    _ ≤ (MeasureTheory.volume s)⁻¹ *
          (η ^ (2 : ℝ) *
            (((2 : ℝ≥0∞) ^ d) * MeasureTheory.volume s)) := by
          exact mul_le_mul_right (mul_le_mul_right hB_volume _) _
    _ = ((2 : ℝ≥0∞) ^ d) * η ^ (2 : ℝ) := by
          calc
            (MeasureTheory.volume s)⁻¹ *
                (η ^ (2 : ℝ) *
                  (((2 : ℝ≥0∞) ^ d) * MeasureTheory.volume s))
                = (η ^ (2 : ℝ) * ((2 : ℝ≥0∞) ^ d)) *
                    (MeasureTheory.volume s)⁻¹ * MeasureTheory.volume s := by
                  ac_rfl
            _ = η ^ (2 : ℝ) * ((2 : ℝ≥0∞) ^ d) := by
                  exact ENNReal.inv_mul_cancel_right hs_pos hs_finite
            _ = ((2 : ℝ≥0∞) ^ d) * η ^ (2 : ℝ) := by
                  rw [mul_comm]

/--
%%handwave
name:
  Finite sums pass under the lower Lebesgue integral as an inequality
statement:
  For a finite family of nonnegative functions, the sum of their lower
  Lebesgue integrals over a set is bounded by the lower Lebesgue integral of
  their pointwise sum over that set.
proof:
  This is the finite induction form of superadditivity of the lower
  Lebesgue integral.
-/
private theorem finset_sum_setLIntegral_le_setLIntegral_sum
    {α ι : Type} [MeasurableSpace α] (μ : Measure α) (A : Set α)
    (s : Finset ι) (f : ι → α → ℝ≥0∞) :
    s.sum (fun i ↦ ∫⁻ x in A, f i x ∂μ) ≤
      ∫⁻ x in A, s.sum (fun i ↦ f i x) ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert a s ha ih =>
      calc
        (insert a s).sum (fun i ↦ ∫⁻ x in A, f i x ∂μ)
            = (∫⁻ x in A, f a x ∂μ) +
                s.sum (fun i ↦ ∫⁻ x in A, f i x ∂μ) := by
              rw [Finset.sum_insert ha]
        _ ≤ (∫⁻ x in A, f a x ∂μ) +
              ∫⁻ x in A, s.sum (fun i ↦ f i x) ∂μ := by
              gcongr
        _ ≤ ∫⁻ x in A, f a x + s.sum (fun i ↦ f i x) ∂μ :=
              le_lintegral_add (μ := μ.restrict A)
                (fun x ↦ f a x) (fun x ↦ s.sum (fun i ↦ f i x))
        _ = ∫⁻ x in A, (insert a s).sum (fun i ↦ f i x) ∂μ := by
              congr with x
              rw [Finset.sum_insert ha]

/--
%%handwave
name:
  Regular-grid weighted overlap estimate
statement:
  For a finite disjoint family of boxes in one regular grid, the normalized
  sum of the localized displacement-slice integrals is controlled by the
  square of the dimension-dependent translation modulus.
proof:
  Use the common grid mesh to replace all box volumes by one common volume
  and to place all box difference bodies inside one centered displacement
  box whose volume is controlled by a dimension-only multiple of that common
  volume.  For each fixed displacement, the displacement slices are disjoint
  subsets of \(P\), so their spatial integrals sum to at most the single
  \(L^2(P)\)-translation integral.  Tonelli's theorem then integrates this
  bound over the common displacement box, where all displacements are within
  the allowed translation scale.
-/
theorem regularCubeBoxDisplacementSlice_weightedOverlap_lintegral_le_const_mul_sq_lintegral_translation_bound
    {d : ℕ} {P : Set (Fin d → ℝ)}
    (u : ℕ → (Fin d → ℝ) → ℝ)
    (_hmemP : ∀ n : ℕ, MemLp (u n) 2 (MeasureTheory.volume.restrict P))
    {η : ℝ≥0∞} {δ : ℝ}
    {m : ℕ} (D : Fin m → BoxIntegral.Box (Fin d))
    (hD_grid : RegularGridBoxFamily D)
    (hD_subsetP : ∀ i : Fin m, (D i : Set (Fin d → ℝ)) ⊆ P)
    (hD_posP : ∀ i : Fin m, 0 < (MeasureTheory.volume.restrict P)
      (D i : Set (Fin d → ℝ)))
    (hD_finiteP : ∀ i : Fin m, (MeasureTheory.volume.restrict P)
      (D i : Set (Fin d → ℝ)) ≠ (⊤ : ℝ≥0∞))
    (hD_disjoint : ∀ i j : Fin m, i ≠ j →
      Disjoint (D i : Set (Fin d → ℝ)) (D j : Set (Fin d → ℝ)))
    (hD_diam : ∀ i : Fin m, ∀ x ∈ (D i : Set (Fin d → ℝ)),
      ∀ y ∈ (D i : Set (Fin d → ℝ)), dist x y < δ)
    (htranslationSq :
      ∀ h : Fin d → ℝ, ‖h‖ < δ →
        ∀ n : ℕ,
          ∫⁻ z in P, ‖u n (z + h) - u n z‖ₑ ^ (2 : ℝ)
            ∂MeasureTheory.volume ≤ η ^ (2 : ℝ)) :
    ∀ n : ℕ,
      ∑ i : Fin m,
          (MeasureTheory.volume (D i : Set (Fin d → ℝ)))⁻¹ *
            ∫⁻ h in regularCubeBoxDifferenceBody (D i),
              ∫⁻ x,
                (regularCubeBoxDisplacementSlice (D i) h).indicator
                  (fun x ↦ ‖u n (x + h) - u n x‖ₑ ^ (2 : ℝ)) x
                ∂MeasureTheory.volume ∂MeasureTheory.volume ≤
        (regularCubeOuterAveragingENNRealConstant d * η) ^ (2 : ℝ) := by
  classical
  intro n
  by_cases hm : m = 0
  · subst m
    simp
  let i0 : Fin m := ⟨0, Nat.pos_of_ne_zero hm⟩
  let v0 : ℝ≥0∞ :=
    MeasureTheory.volume (D i0 : Set (Fin d → ℝ))
  let U : Set (Fin d → ℝ) :=
    ⋃ i : Fin m, regularCubeBoxDifferenceBody (D i)
  let F : Fin m → (Fin d → ℝ) → ℝ≥0∞ :=
    fun i h ↦
      ∫⁻ x,
        (regularCubeBoxDisplacementSlice (D i) h).indicator
          (fun x ↦ ‖u n (x + h) - u n x‖ₑ ^ (2 : ℝ)) x
        ∂MeasureTheory.volume
  have hvol_eq : ∀ i : Fin m,
      MeasureTheory.volume (D i : Set (Fin d → ℝ)) = v0 := by
    intro i
    simpa [v0] using RegularGridBoxFamily.volume_eq hD_grid i i0
  have hi0_meas : MeasurableSet (D i0 : Set (Fin d → ℝ)) :=
    (D i0).measurableSet_coe
  have hi0_measure :
      (MeasureTheory.volume.restrict P) (D i0 : Set (Fin d → ℝ)) = v0 := by
    rw [Measure.restrict_apply hi0_meas]
    have h_inter :
        (D i0 : Set (Fin d → ℝ)) ∩ P =
          (D i0 : Set (Fin d → ℝ)) :=
      Set.inter_eq_left.mpr (hD_subsetP i0)
    simp [v0, h_inter]
  have hv0_pos : v0 ≠ 0 := by
    have hpos : 0 < v0 := by
      rw [← hi0_measure]
      exact hD_posP i0
    exact ne_of_gt hpos
  have hv0_finite : v0 ≠ (⊤ : ℝ≥0∞) := by
    rw [← hi0_measure]
    exact hD_finiteP i0
  rcases RegularGridBoxFamily.exists_common_differenceBody_volume_le hD_grid i0 with
    ⟨B, _hB_meas, hB_cover, hB_volume⟩
  have hU_volume :
      MeasureTheory.volume U ≤ ((2 : ℝ≥0∞) ^ d) * v0 := by
    have hU_subsetB : U ⊆ B := by
      intro h hh
      rcases Set.mem_iUnion.mp hh with ⟨i, hhi⟩
      exact hB_cover i hhi
    exact (measure_mono hU_subsetB).trans hB_volume
  have hsum_lintegral_le :
      ∑ i : Fin m, ∫⁻ h in U, F i h ∂MeasureTheory.volume ≤
        ∫⁻ h in U, ∑ i : Fin m, F i h ∂MeasureTheory.volume := by
    simpa using
      finset_sum_setLIntegral_le_setLIntegral_sum
        MeasureTheory.volume U Finset.univ F
  have hoverlap :
      ∫⁻ h in U, ∑ i : Fin m, F i h ∂MeasureTheory.volume ≤
        ∫⁻ h in U,
          ∫⁻ z in P, ‖u n (z + h) - u n z‖ₑ ^ (2 : ℝ)
            ∂MeasureTheory.volume ∂MeasureTheory.volume := by
    refine lintegral_mono ?_
    intro h
    exact regularCubeBoxDisplacementSlice_sum_lintegral_indicator_le_setLIntegral
      D hD_subsetP hD_disjoint h
      (fun z ↦ ‖u n (z + h) - u n z‖ₑ ^ (2 : ℝ))
  have htranslate_U :
      ∫⁻ h in U,
          ∫⁻ z in P, ‖u n (z + h) - u n z‖ₑ ^ (2 : ℝ)
            ∂MeasureTheory.volume ∂MeasureTheory.volume ≤
        ∫⁻ _h in U, η ^ (2 : ℝ) ∂MeasureTheory.volume := by
    refine setLIntegral_mono measurable_const ?_
    intro h hhU
    rcases Set.mem_iUnion.mp hhU with ⟨i, hhi⟩
    have hh_small : ‖h‖ < δ := by
      have hball :=
        regularCubeBoxDifferenceBody_subset_ball_of_diameter
          (D i) (hD_diam i) hhi
      simpa [Metric.mem_ball, dist_eq_norm] using hball
    exact htranslationSq h hh_small n
  have hweighted_le_two_pow :
      ∑ i : Fin m,
          (MeasureTheory.volume (D i : Set (Fin d → ℝ)))⁻¹ *
            ∫⁻ h in regularCubeBoxDifferenceBody (D i), F i h
              ∂MeasureTheory.volume ≤
        ((2 : ℝ≥0∞) ^ d) * η ^ (2 : ℝ) := by
    calc
      ∑ i : Fin m,
          (MeasureTheory.volume (D i : Set (Fin d → ℝ)))⁻¹ *
            ∫⁻ h in regularCubeBoxDifferenceBody (D i), F i h
              ∂MeasureTheory.volume
          = ∑ i : Fin m,
              v0⁻¹ *
                ∫⁻ h in regularCubeBoxDifferenceBody (D i), F i h
                  ∂MeasureTheory.volume := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [hvol_eq i]
      _ ≤ ∑ i : Fin m,
            v0⁻¹ * ∫⁻ h in U, F i h ∂MeasureTheory.volume := by
            refine Finset.sum_le_sum ?_
            intro i _hi
            gcongr
            exact Set.subset_iUnion
              (fun i : Fin m ↦ regularCubeBoxDifferenceBody (D i)) i
      _ = v0⁻¹ * ∑ i : Fin m,
            ∫⁻ h in U, F i h ∂MeasureTheory.volume := by
            rw [Finset.mul_sum]
      _ ≤ v0⁻¹ *
            ∫⁻ h in U, ∑ i : Fin m, F i h ∂MeasureTheory.volume := by
            gcongr
      _ ≤ v0⁻¹ *
            ∫⁻ h in U,
              ∫⁻ z in P, ‖u n (z + h) - u n z‖ₑ ^ (2 : ℝ)
                ∂MeasureTheory.volume ∂MeasureTheory.volume := by
            gcongr
      _ ≤ v0⁻¹ * ∫⁻ _h in U, η ^ (2 : ℝ)
            ∂MeasureTheory.volume := by
            gcongr
      _ = v0⁻¹ * (η ^ (2 : ℝ) * MeasureTheory.volume U) := by
            rw [setLIntegral_const]
      _ ≤ v0⁻¹ * (η ^ (2 : ℝ) * (((2 : ℝ≥0∞) ^ d) * v0)) := by
            gcongr
      _ = ((2 : ℝ≥0∞) ^ d) * η ^ (2 : ℝ) := by
            calc
              v0⁻¹ * (η ^ (2 : ℝ) * (((2 : ℝ≥0∞) ^ d) * v0))
                  = (η ^ (2 : ℝ) * ((2 : ℝ≥0∞) ^ d)) *
                      v0⁻¹ * v0 := by
                    ac_rfl
              _ = η ^ (2 : ℝ) * ((2 : ℝ≥0∞) ^ d) := by
                    exact ENNReal.inv_mul_cancel_right hv0_pos hv0_finite
              _ = ((2 : ℝ≥0∞) ^ d) * η ^ (2 : ℝ) := by
                    rw [mul_comm]
  calc
    ∑ i : Fin m,
        (MeasureTheory.volume (D i : Set (Fin d → ℝ)))⁻¹ *
          ∫⁻ h in regularCubeBoxDifferenceBody (D i),
            ∫⁻ x,
              (regularCubeBoxDisplacementSlice (D i) h).indicator
                (fun x ↦ ‖u n (x + h) - u n x‖ₑ ^ (2 : ℝ)) x
              ∂MeasureTheory.volume ∂MeasureTheory.volume
        = ∑ i : Fin m,
            (MeasureTheory.volume (D i : Set (Fin d → ℝ)))⁻¹ *
              ∫⁻ h in regularCubeBoxDifferenceBody (D i), F i h
                ∂MeasureTheory.volume := by
          rfl
    _ ≤ ((2 : ℝ≥0∞) ^ d) * η ^ (2 : ℝ) :=
        hweighted_le_two_pow
    _ ≤ (regularCubeOuterAveragingENNRealConstant d * η) ^ (2 : ℝ) :=
        two_pow_mul_sq_le_regularCubeOuterAveragingENNRealConstant_mul_sq d η

/--
%%handwave
name:
  Sum of box pairwise oscillations is controlled by squared translation integrals
statement:
  For a finite family of boxes lying in a common regular coordinate grid
  inside \(P\), if every displacement shorter than the box diameter scale has
  squared \(L^2(P)\)-translation integral bounded by \(\eta^2\), then the sum
  of the normalized pairwise oscillations over the boxes is bounded by the
  square of the dimension-dependent constant times \(\eta\).
proof:
  Rewrite each pair \((x,y)\) in a box as \((x,h)\), where \(h=y-x\), and
  integrate first in the displacement variable.  The displacements lie in the
  difference body of the box, which is contained in the allowed translation
  scale.  The box geometry controls the difference-body weights, and
  disjointness lets the fixed-displacement contributions be summed inside
  \(P\).
-/
theorem regularCubeBoxPairwiseOscillation_sum_le_const_mul_sq_lintegral_translation_bound
    {d : ℕ} {P : Set (Fin d → ℝ)}
    (u : ℕ → (Fin d → ℝ) → ℝ)
    (hmemP : ∀ n : ℕ, MemLp (u n) 2 (MeasureTheory.volume.restrict P))
    {η : ℝ≥0∞} {δ : ℝ}
    {m : ℕ} (D : Fin m → BoxIntegral.Box (Fin d))
    (hD_grid : RegularGridBoxFamily D)
    (hD_subsetP : ∀ i : Fin m, (D i : Set (Fin d → ℝ)) ⊆ P)
    (hD_posP : ∀ i : Fin m, 0 < (MeasureTheory.volume.restrict P)
      (D i : Set (Fin d → ℝ)))
    (hD_finiteP : ∀ i : Fin m, (MeasureTheory.volume.restrict P)
      (D i : Set (Fin d → ℝ)) ≠ (⊤ : ℝ≥0∞))
    (hD_disjoint : ∀ i j : Fin m, i ≠ j →
      Disjoint (D i : Set (Fin d → ℝ)) (D j : Set (Fin d → ℝ)))
    (hD_diam : ∀ i : Fin m, ∀ x ∈ (D i : Set (Fin d → ℝ)),
      ∀ y ∈ (D i : Set (Fin d → ℝ)), dist x y < δ)
    (htranslationSq :
      ∀ h : Fin d → ℝ, ‖h‖ < δ →
        ∀ n : ℕ,
          ∫⁻ z in P, ‖u n (z + h) - u n z‖ₑ ^ (2 : ℝ)
            ∂MeasureTheory.volume ≤ η ^ (2 : ℝ)) :
    ∀ n : ℕ,
      ∑ i : Fin m, regularCubeBoxPairwiseOscillation u D n i ≤
        (regularCubeOuterAveragingENNRealConstant d * η) ^ (2 : ℝ) := by
  intro n
  calc
    ∑ i : Fin m, regularCubeBoxPairwiseOscillation u D n i
        ≤ ∑ i : Fin m,
            (MeasureTheory.volume (D i : Set (Fin d → ℝ)))⁻¹ *
              ∫⁻ h in regularCubeBoxDifferenceBody (D i),
                ∫⁻ x,
                  (regularCubeBoxDisplacementSlice (D i) h).indicator
                    (fun x ↦ ‖u n (x + h) - u n x‖ₑ ^ (2 : ℝ)) x
                  ∂MeasureTheory.volume ∂MeasureTheory.volume := by
          refine Finset.sum_le_sum ?_
          intro i _hi
          exact regularCubeBoxPairwiseOscillation_le_displacementSlice_lintegral_translation
            u hmemP D hD_subsetP n i
    _ ≤ (regularCubeOuterAveragingENNRealConstant d * η) ^ (2 : ℝ) :=
        regularCubeBoxDisplacementSlice_weightedOverlap_lintegral_le_const_mul_sq_lintegral_translation_bound
          u hmemP D hD_grid hD_subsetP hD_posP hD_finiteP hD_disjoint hD_diam
          htranslationSq n

/--
%%handwave
name:
  Sum of box pairwise oscillations is bounded by translations
statement:
  For a finite family of boxes lying in a common regular coordinate grid
  inside \(P\), the sum of their normalized pairwise squared oscillations is
  bounded by the square of the dimension-dependent constant times the squared
  translation modulus.
proof:
  Rewrite pairs \((x,y)\in D_i\times D_i\) using the displacement
  \(h=y-x\).  Tonelli's theorem exchanges the order of integration, and
  translation invariance identifies the inner integral with the squared
  \(L^2(P)\)-translation difference at displacement \(h\).  The relevant
  displacements lie in the difference body \(D_i-D_i\), whose Lebesgue
  measure is bounded by a dimension-only multiple of the measure of \(D_i\).
  Disjointness of the boxes lets the fixed-displacement contributions sum
  inside \(P\).
-/
theorem regularCubeBoxPairwiseOscillation_sum_le_const_mul_translation_bound
    {d : ℕ} {P : Set (Fin d → ℝ)}
    (u : ℕ → (Fin d → ℝ) → ℝ)
    (hmemP : ∀ n : ℕ, MemLp (u n) 2 (MeasureTheory.volume.restrict P))
    {η : ℝ≥0∞} {δ : ℝ}
    {m : ℕ} (D : Fin m → BoxIntegral.Box (Fin d))
    (hD_grid : RegularGridBoxFamily D)
    (hD_subsetP : ∀ i : Fin m, (D i : Set (Fin d → ℝ)) ⊆ P)
    (hD_posP : ∀ i : Fin m, 0 < (MeasureTheory.volume.restrict P)
      (D i : Set (Fin d → ℝ)))
    (hD_finiteP : ∀ i : Fin m, (MeasureTheory.volume.restrict P)
      (D i : Set (Fin d → ℝ)) ≠ (⊤ : ℝ≥0∞))
    (hD_disjoint : ∀ i j : Fin m, i ≠ j →
      Disjoint (D i : Set (Fin d → ℝ)) (D j : Set (Fin d → ℝ)))
    (hD_diam : ∀ i : Fin m, ∀ x ∈ (D i : Set (Fin d → ℝ)),
      ∀ y ∈ (D i : Set (Fin d → ℝ)), dist x y < δ)
    (htranslation :
      ∀ h : Fin d → ℝ, ‖h‖ < δ →
        ∀ n : ℕ,
          eLpNorm (fun z ↦ u n (z + h) - u n z) 2
            (MeasureTheory.volume.restrict P) ≤ η) :
    ∀ n : ℕ,
      ∑ i : Fin m, regularCubeBoxPairwiseOscillation u D n i ≤
        (regularCubeOuterAveragingENNRealConstant d * η) ^ (2 : ℝ) := by
  refine
    regularCubeBoxPairwiseOscillation_sum_le_const_mul_sq_lintegral_translation_bound
      u hmemP D hD_grid hD_subsetP hD_posP hD_finiteP hD_disjoint hD_diam ?_
  intro h hh n
  exact lintegral_sq_le_of_eLpNorm_two_le (htranslation h hh n)

/--
%%handwave
name:
  Sum of box variances around Lebesgue averages is bounded by translations
statement:
  For a disjoint finite family of boxes inside \(P\), the sum of the squared
  variances around the ordinary Lebesgue averages on the boxes is bounded by
  the square of the dimension-dependent constant times the squared
  translation modulus.
proof:
  On each box, compare the variance around the box average with the mean
  pairwise oscillation.  Parametrize pairs by their displacement, use
  Tonelli's theorem, and bound the displacement integral by the uniform
  translation modulus.  The difference body of a box has volume bounded by
  \(2^d\) times the box volume, and disjointness lets the fixed-displacement
  contributions sum inside \(P\).
-/
theorem regularCubeBoxAverageCoeff_sum_box_lintegral_sq_le_const_mul_translation_bound
    {d : ℕ} {P : Set (Fin d → ℝ)}
    (u : ℕ → (Fin d → ℝ) → ℝ)
    (hmemP : ∀ n : ℕ, MemLp (u n) 2 (MeasureTheory.volume.restrict P))
    {η : ℝ≥0∞} {δ : ℝ}
    {m : ℕ} (D : Fin m → BoxIntegral.Box (Fin d))
    (hD_grid : RegularGridBoxFamily D)
    (hD_subsetP : ∀ i : Fin m, (D i : Set (Fin d → ℝ)) ⊆ P)
    (hD_posP : ∀ i : Fin m, 0 < (MeasureTheory.volume.restrict P)
      (D i : Set (Fin d → ℝ)))
    (hD_finiteP : ∀ i : Fin m, (MeasureTheory.volume.restrict P)
      (D i : Set (Fin d → ℝ)) ≠ (⊤ : ℝ≥0∞))
    (hD_disjoint : ∀ i j : Fin m, i ≠ j →
      Disjoint (D i : Set (Fin d → ℝ)) (D j : Set (Fin d → ℝ)))
    (hD_diam : ∀ i : Fin m, ∀ x ∈ (D i : Set (Fin d → ℝ)),
      ∀ y ∈ (D i : Set (Fin d → ℝ)), dist x y < δ)
    (htranslation :
      ∀ h : Fin d → ℝ, ‖h‖ < δ →
        ∀ n : ℕ,
          eLpNorm (fun z ↦ u n (z + h) - u n z) 2
            (MeasureTheory.volume.restrict P) ≤ η) :
    ∀ n : ℕ,
      ∑ i : Fin m,
        ∫⁻ x in (D i : Set (Fin d → ℝ)),
          ‖u n x - regularCubeBoxAverageCoeff u D n i‖ₑ ^ (2 : ℝ)
            ∂MeasureTheory.volume ≤
        (regularCubeOuterAveragingENNRealConstant d * η) ^ (2 : ℝ) := by
  intro n
  calc
    ∑ i : Fin m,
        ∫⁻ x in (D i : Set (Fin d → ℝ)),
          ‖u n x - regularCubeBoxAverageCoeff u D n i‖ₑ ^ (2 : ℝ)
            ∂MeasureTheory.volume
        ≤ ∑ i : Fin m, regularCubeBoxPairwiseOscillation u D n i := by
          refine Finset.sum_le_sum ?_
          intro i _hi
          exact regularCubeBoxAverageCoeff_lintegral_sq_le_pairwiseOscillation
            u hmemP D hD_subsetP hD_posP hD_finiteP n i
    _ ≤ (regularCubeOuterAveragingENNRealConstant d * η) ^ (2 : ℝ) :=
        regularCubeBoxPairwiseOscillation_sum_le_const_mul_translation_bound
          u hmemP D hD_grid hD_subsetP hD_posP hD_finiteP hD_disjoint hD_diam
          htranslation n

/--
%%handwave
name:
  Sum of box variances around the outer averages is bounded by translations
statement:
  For a disjoint finite family of boxes inside \(P\), the sum of the squared
  variances around the individual outer box averages is bounded by the square
  of the dimension-dependent constant times the squared translation modulus.
proof:
  Apply the cell variance inequality on each box, rewrite the pairwise
  oscillation by displacements, and use Tonelli together with translation
  invariance of Lebesgue measure.  The difference body of a box is contained
  in a box with side lengths twice as large, so its volume is controlled by
  \(2^d\) times the original box volume.
-/
theorem regularCubeOuterAverageCoeff_sum_box_lintegral_sq_le_const_mul_translation_bound
    {d : ℕ} {P : Set (Fin d → ℝ)}
    (u : ℕ → (Fin d → ℝ) → ℝ)
    (hmemP : ∀ n : ℕ, MemLp (u n) 2 (MeasureTheory.volume.restrict P))
    {η : ℝ≥0∞} {δ : ℝ}
    {m : ℕ} (D : Fin m → BoxIntegral.Box (Fin d))
    (hD_grid : RegularGridBoxFamily D)
    (hD_subsetP : ∀ i : Fin m, (D i : Set (Fin d → ℝ)) ⊆ P)
    (hD_posP : ∀ i : Fin m, 0 < (MeasureTheory.volume.restrict P)
      (D i : Set (Fin d → ℝ)))
    (hD_finiteP : ∀ i : Fin m, (MeasureTheory.volume.restrict P)
      (D i : Set (Fin d → ℝ)) ≠ (⊤ : ℝ≥0∞))
    (hD_disjoint : ∀ i j : Fin m, i ≠ j →
      Disjoint (D i : Set (Fin d → ℝ)) (D j : Set (Fin d → ℝ)))
    (hD_diam : ∀ i : Fin m, ∀ x ∈ (D i : Set (Fin d → ℝ)),
      ∀ y ∈ (D i : Set (Fin d → ℝ)), dist x y < δ)
    (htranslation :
      ∀ h : Fin d → ℝ, ‖h‖ < δ →
        ∀ n : ℕ,
          eLpNorm (fun z ↦ u n (z + h) - u n z) 2
            (MeasureTheory.volume.restrict P) ≤ η) :
    ∀ n : ℕ,
      ∑ i : Fin m,
        ∫⁻ x in (D i : Set (Fin d → ℝ)),
          ‖u n x - regularCubeOuterAverageCoeff P u hmemP D n i‖ₑ ^ (2 : ℝ)
            ∂MeasureTheory.volume ≤
        (regularCubeOuterAveragingENNRealConstant d * η) ^ (2 : ℝ) := by
  intro n
  calc
    ∑ i : Fin m,
        ∫⁻ x in (D i : Set (Fin d → ℝ)),
          ‖u n x - regularCubeOuterAverageCoeff P u hmemP D n i‖ₑ ^ (2 : ℝ)
            ∂MeasureTheory.volume
        = ∑ i : Fin m,
            ∫⁻ x in (D i : Set (Fin d → ℝ)),
              ‖u n x - regularCubeBoxAverageCoeff u D n i‖ₑ ^ (2 : ℝ)
                ∂MeasureTheory.volume := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [regularCubeOuterAverageCoeff_eq_boxAverageCoeff_of_subset
            u hmemP D hD_subsetP n i]
    _ ≤ (regularCubeOuterAveragingENNRealConstant d * η) ^ (2 : ℝ) :=
        regularCubeBoxAverageCoeff_sum_box_lintegral_sq_le_const_mul_translation_bound
          u hmemP D hD_grid hD_subsetP hD_posP hD_finiteP hD_disjoint hD_diam
          htranslation n

/--
%%handwave
name:
  Sum of box variances is bounded by the squared translation modulus
statement:
  For a disjoint finite family of boxes inside \(P\), the sum of the squared
  errors on the individual boxes is bounded by the square of the
  dimension-dependent constant times the squared translation modulus.
proof:
  On each box, compare the variance around the box average with the mean
  pairwise oscillation.  Parametrize pairs by their displacement, use
  Tonelli's theorem, and bound the displacement integral by the uniform
  translation modulus.  The difference body of a box has volume bounded by
  \(2^d\) times the box volume, and disjointness lets the fixed-displacement
  contributions sum inside \(P\).
-/
theorem regularCubeOuterPiecewiseAverage_sum_box_lintegral_sq_le_const_mul_translation_bound
    {d : ℕ} {P : Set (Fin d → ℝ)}
    (u : ℕ → (Fin d → ℝ) → ℝ)
    (hmemP : ∀ n : ℕ, MemLp (u n) 2 (MeasureTheory.volume.restrict P))
    {η : ℝ≥0∞} {δ : ℝ}
    {m : ℕ} (D : Fin m → BoxIntegral.Box (Fin d))
    (hD_grid : RegularGridBoxFamily D)
    (hD_subsetP : ∀ i : Fin m, (D i : Set (Fin d → ℝ)) ⊆ P)
    (hD_posP : ∀ i : Fin m, 0 < (MeasureTheory.volume.restrict P)
      (D i : Set (Fin d → ℝ)))
    (hD_finiteP : ∀ i : Fin m, (MeasureTheory.volume.restrict P)
      (D i : Set (Fin d → ℝ)) ≠ (⊤ : ℝ≥0∞))
    (hD_disjoint : ∀ i j : Fin m, i ≠ j →
      Disjoint (D i : Set (Fin d → ℝ)) (D j : Set (Fin d → ℝ)))
    (hD_diam : ∀ i : Fin m, ∀ x ∈ (D i : Set (Fin d → ℝ)),
      ∀ y ∈ (D i : Set (Fin d → ℝ)), dist x y < δ)
    (htranslation :
      ∀ h : Fin d → ℝ, ‖h‖ < δ →
        ∀ n : ℕ,
          eLpNorm (fun z ↦ u n (z + h) - u n z) 2
            (MeasureTheory.volume.restrict P) ≤ η) :
    ∀ n : ℕ,
      ∑ i : Fin m,
        ∫⁻ x in (D i : Set (Fin d → ℝ)),
          ‖u n x - regularCubeOuterPiecewiseAverage P u hmemP D n x‖ₑ ^ (2 : ℝ)
            ∂MeasureTheory.volume ≤
        (regularCubeOuterAveragingENNRealConstant d * η) ^ (2 : ℝ) := by
  intro n
  calc
    ∑ i : Fin m,
        ∫⁻ x in (D i : Set (Fin d → ℝ)),
          ‖u n x - regularCubeOuterPiecewiseAverage P u hmemP D n x‖ₑ ^ (2 : ℝ)
            ∂MeasureTheory.volume
        = ∑ i : Fin m,
            ∫⁻ x in (D i : Set (Fin d → ℝ)),
              ‖u n x - regularCubeOuterAverageCoeff P u hmemP D n i‖ₑ ^ (2 : ℝ)
                ∂MeasureTheory.volume := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          exact regularCubeOuterPiecewiseAverage_lintegral_sq_on_box_eq_averageCoeff
            u hmemP D hD_disjoint n i
    _ ≤ (regularCubeOuterAveragingENNRealConstant d * η) ^ (2 : ℝ) :=
          regularCubeOuterAverageCoeff_sum_box_lintegral_sq_le_const_mul_translation_bound
            u hmemP D hD_grid hD_subsetP hD_posP hD_finiteP hD_disjoint hD_diam
            htranslation n

/--
%%handwave
name:
  Squared regular-cube averaging error is bounded by the squared translation modulus
statement:
  For a disjoint finite family of boxes inside \(P\), the squared
  \(L^2\)-error of replacing a function by its outer-box piecewise average on
  the box union is bounded by the square of the dimension-dependent constant
  times the squared translation modulus.
proof:
  Decompose the integral over the disjoint box union into a finite sum of
  box integrals.  On each box, use the variance inequality
  \[
    \int_D |u-u_D|^2
      \leq \mu(D)^{-1}\int_D\int_D |u(x)-u(y)|^2\,dy\,dx .
  \]
  Since \(x,y\in D\) imply \(y-x\) has norm below the translation scale,
  rewrite the pairwise oscillation as a translated difference.  Tonelli's
  theorem and translation invariance bound the resulting integral by the
  uniform \(L^2(P)\) translation modulus.  For boxes, the difference body has
  volume at most \(2^d\) times the box volume, giving the
  dimension-dependent summation constant.
-/
theorem regularCubeOuterPiecewiseAverage_lintegral_sq_on_iUnion_le_const_mul_translation_bound
    {d : ℕ} {P : Set (Fin d → ℝ)}
    (u : ℕ → (Fin d → ℝ) → ℝ)
    (hmemP : ∀ n : ℕ, MemLp (u n) 2 (MeasureTheory.volume.restrict P))
    {η : ℝ≥0∞} {δ : ℝ}
    {m : ℕ} (D : Fin m → BoxIntegral.Box (Fin d))
    (hD_grid : RegularGridBoxFamily D)
    (hD_subsetP : ∀ i : Fin m, (D i : Set (Fin d → ℝ)) ⊆ P)
    (hD_posP : ∀ i : Fin m, 0 < (MeasureTheory.volume.restrict P)
      (D i : Set (Fin d → ℝ)))
    (hD_finiteP : ∀ i : Fin m, (MeasureTheory.volume.restrict P)
      (D i : Set (Fin d → ℝ)) ≠ (⊤ : ℝ≥0∞))
    (hD_disjoint : ∀ i j : Fin m, i ≠ j →
      Disjoint (D i : Set (Fin d → ℝ)) (D j : Set (Fin d → ℝ)))
    (hD_diam : ∀ i : Fin m, ∀ x ∈ (D i : Set (Fin d → ℝ)),
      ∀ y ∈ (D i : Set (Fin d → ℝ)), dist x y < δ)
    (htranslation :
      ∀ h : Fin d → ℝ, ‖h‖ < δ →
        ∀ n : ℕ,
          eLpNorm (fun z ↦ u n (z + h) - u n z) 2
            (MeasureTheory.volume.restrict P) ≤ η) :
    ∀ n : ℕ,
      ∫⁻ x in ⋃ i : Fin m, (D i : Set (Fin d → ℝ)),
        ‖u n x - regularCubeOuterPiecewiseAverage P u hmemP D n x‖ₑ ^ (2 : ℝ)
          ∂MeasureTheory.volume ≤
        (regularCubeOuterAveragingENNRealConstant d * η) ^ (2 : ℝ) := by
  intro n
  rw [regularCubeOuterPiecewiseAverage_lintegral_sq_on_iUnion_eq_sum
    u hmemP D hD_disjoint n]
  exact
    regularCubeOuterPiecewiseAverage_sum_box_lintegral_sq_le_const_mul_translation_bound
      u hmemP D hD_grid hD_subsetP hD_posP hD_finiteP hD_disjoint hD_diam
      htranslation n

/--
%%handwave
name:
  Regular cube outer piecewise averages are bounded on the box union
statement:
  For a disjoint family of boxes inside an outer compact set \(P\),
  translation tightness on \(P\) controls the \(L^2\)-distance, on the union
  of the boxes, from a function to its outer-box piecewise average, up to a
  constant depending only on the dimension.
proof:
  On each box, the variance around the box average is bounded by the mean
  pairwise oscillation on the same full box.  Writing pairs of points as
  translations and using Fubini bounds the sum of these oscillations by the
  uniform translation modulus on \(P\).  The box geometry gives the
  dimension-only bound for the volume of each difference box.
-/
theorem regularCubeOuterPiecewiseAverage_eLpNorm_on_iUnion_le_const_mul_translation_bound
    {d : ℕ} {P : Set (Fin d → ℝ)}
    (u : ℕ → (Fin d → ℝ) → ℝ)
    (hmemP : ∀ n : ℕ, MemLp (u n) 2 (MeasureTheory.volume.restrict P))
    {η : ℝ≥0∞} {δ : ℝ}
    {m : ℕ} (D : Fin m → BoxIntegral.Box (Fin d))
    (hD_grid : RegularGridBoxFamily D)
    (hD_subsetP : ∀ i : Fin m, (D i : Set (Fin d → ℝ)) ⊆ P)
    (hD_posP : ∀ i : Fin m, 0 < (MeasureTheory.volume.restrict P)
      (D i : Set (Fin d → ℝ)))
    (hD_finiteP : ∀ i : Fin m, (MeasureTheory.volume.restrict P)
      (D i : Set (Fin d → ℝ)) ≠ (⊤ : ℝ≥0∞))
    (hD_disjoint : ∀ i j : Fin m, i ≠ j →
      Disjoint (D i : Set (Fin d → ℝ)) (D j : Set (Fin d → ℝ)))
    (hD_diam : ∀ i : Fin m, ∀ x ∈ (D i : Set (Fin d → ℝ)),
      ∀ y ∈ (D i : Set (Fin d → ℝ)), dist x y < δ)
    (htranslation :
      ∀ h : Fin d → ℝ, ‖h‖ < δ →
        ∀ n : ℕ,
          eLpNorm (fun z ↦ u n (z + h) - u n z) 2
            (MeasureTheory.volume.restrict P) ≤ η) :
    ∀ n : ℕ,
      eLpNorm
        (fun x ↦ u n x - regularCubeOuterPiecewiseAverage P u hmemP D n x)
        2 (MeasureTheory.volume.restrict
          (⋃ i : Fin m, (D i : Set (Fin d → ℝ)))) ≤
        regularCubeOuterAveragingENNRealConstant d * η := by
  intro n
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞))]
  simp only [ENNReal.toReal_ofNat, one_div]
  change
    (∫⁻ x in ⋃ i : Fin m, (D i : Set (Fin d → ℝ)),
        ‖u n x - regularCubeOuterPiecewiseAverage P u hmemP D n x‖ₑ ^ (2 : ℝ)
          ∂MeasureTheory.volume) ^ ((2 : ℝ)⁻¹) ≤
      regularCubeOuterAveragingENNRealConstant d * η
  exact (ENNReal.rpow_inv_le_iff (by norm_num : 0 < (2 : ℝ))).2
    (regularCubeOuterPiecewiseAverage_lintegral_sq_on_iUnion_le_const_mul_translation_bound
      u hmemP D hD_grid hD_subsetP hD_posP hD_finiteP hD_disjoint hD_diam
      htranslation n)

/--
%%handwave
name:
  Regular cube outer averages are bounded on the box union by the translation modulus
statement:
  For a disjoint regular box family inside an outer compact set \(P\),
  translation tightness on \(P\) controls the \(L^2\)-distance, on the union
  of the boxes, from a function to its outer-box piecewise average, up to a
  constant depending only on the dimension.
proof:
  On each box, the variance around the box average is bounded by the mean
  pairwise oscillation on the same full box.  Writing pairs of points as
  translations and using Fubini bounds the sum of these oscillations by the
  uniform translation modulus on \(P\).  The regular grid geometry of the
  boxes supplies the dimension-only overlap bound needed to sum over boxes.
-/
theorem regularCubeOuterAveraging_piecewise_eLpNorm_on_iUnion_le_const_mul_translation_bound
    {d : ℕ} {P : Set (Fin d → ℝ)}
    (u : ℕ → (Fin d → ℝ) → ℝ)
    (hmemP : ∀ n : ℕ, MemLp (u n) 2 (MeasureTheory.volume.restrict P))
    {η : ℝ≥0∞} {δ : ℝ}
    {m : ℕ} (D : Fin m → BoxIntegral.Box (Fin d))
    (hD_grid : RegularGridBoxFamily D)
    (hD_subsetP : ∀ i : Fin m, (D i : Set (Fin d → ℝ)) ⊆ P)
    (hD_posP : ∀ i : Fin m, 0 < (MeasureTheory.volume.restrict P)
      (D i : Set (Fin d → ℝ)))
    (hD_finiteP : ∀ i : Fin m, (MeasureTheory.volume.restrict P)
      (D i : Set (Fin d → ℝ)) ≠ (⊤ : ℝ≥0∞))
    (hD_disjoint : ∀ i j : Fin m, i ≠ j →
      Disjoint (D i : Set (Fin d → ℝ)) (D j : Set (Fin d → ℝ)))
    (hD_diam : ∀ i : Fin m, ∀ x ∈ (D i : Set (Fin d → ℝ)),
      ∀ y ∈ (D i : Set (Fin d → ℝ)), dist x y < δ)
    (htranslation :
      ∀ h : Fin d → ℝ, ‖h‖ < δ →
        ∀ n : ℕ,
          eLpNorm (fun z ↦ u n (z + h) - u n z) 2
            (MeasureTheory.volume.restrict P) ≤ η) :
    ∀ n : ℕ,
      eLpNorm
        (fun x ↦
          u n x -
            ∑ i : Fin m,
              (((MeasureTheory.volume.restrict P).real
                  (D i : Set (Fin d → ℝ)))⁻¹ *
                ∫ y in (D i : Set (Fin d → ℝ)),
                  ((hmemP n).toLp (u n) :
                    Lp ℝ 2 (MeasureTheory.volume.restrict P)) y
                  ∂(MeasureTheory.volume.restrict P)) *
                (D i : Set (Fin d → ℝ)).indicator (fun _ ↦ (1 : ℝ)) x)
        2 (MeasureTheory.volume.restrict
          (⋃ i : Fin m, (D i : Set (Fin d → ℝ)))) ≤
        regularCubeOuterAveragingENNRealConstant d * η := by
  simpa [regularCubeOuterPiecewiseAverage, regularCubeOuterAverageCoeff] using
    regularCubeOuterPiecewiseAverage_eLpNorm_on_iUnion_le_const_mul_translation_bound
      u hmemP D hD_grid hD_subsetP hD_posP hD_finiteP hD_disjoint hD_diam
      htranslation

/--
%%handwave
name:
  Regular cube outer averages are bounded by the translation modulus
statement:
  For a disjoint regular box family inside an outer compact set \(P\) that
  covers an inner compact set \(K\), translation tightness on \(P\) controls
  the \(L^2(K)\)-distance from a function to its outer-box piecewise average,
  up to a constant depending only on the dimension.
proof:
  Since \(K\) is contained in the union of the boxes, monotonicity of the
  \(L^2\)-seminorm reduces the estimate on \(K\) to the estimate on that
  finite disjoint union.  The latter is the regular-cube variance and
  Fubini estimate.
-/
theorem regularCubeOuterAveraging_piecewise_eLpNorm_le_const_mul_translation_bound
    {d : ℕ} {K P : Set (Fin d → ℝ)}
    (u : ℕ → (Fin d → ℝ) → ℝ)
    (hmemP : ∀ n : ℕ, MemLp (u n) 2 (MeasureTheory.volume.restrict P))
    (_hmemK : ∀ n : ℕ, MemLp (u n) 2 (MeasureTheory.volume.restrict K))
    {η : ℝ≥0∞} {δ : ℝ}
    {m : ℕ} (D : Fin m → BoxIntegral.Box (Fin d))
    (hD_cover : K ⊆ ⋃ i : Fin m, (D i : Set (Fin d → ℝ)))
    (hD_grid : RegularGridBoxFamily D)
    (hD_subsetP : ∀ i : Fin m, (D i : Set (Fin d → ℝ)) ⊆ P)
    (hD_posP : ∀ i : Fin m, 0 < (MeasureTheory.volume.restrict P)
      (D i : Set (Fin d → ℝ)))
    (hD_finiteP : ∀ i : Fin m, (MeasureTheory.volume.restrict P)
      (D i : Set (Fin d → ℝ)) ≠ (⊤ : ℝ≥0∞))
    (_hD_finiteK : ∀ i : Fin m, (MeasureTheory.volume.restrict K)
      (D i : Set (Fin d → ℝ)) ≠ (⊤ : ℝ≥0∞))
    (hD_disjoint : ∀ i j : Fin m, i ≠ j →
      Disjoint (D i : Set (Fin d → ℝ)) (D j : Set (Fin d → ℝ)))
    (hD_diam : ∀ i : Fin m, ∀ x ∈ (D i : Set (Fin d → ℝ)),
      ∀ y ∈ (D i : Set (Fin d → ℝ)), dist x y < δ)
    (htranslation :
      ∀ h : Fin d → ℝ, ‖h‖ < δ →
        ∀ n : ℕ,
          eLpNorm (fun z ↦ u n (z + h) - u n z) 2
            (MeasureTheory.volume.restrict P) ≤ η) :
    ∀ n : ℕ,
      eLpNorm
        (fun x ↦
          u n x -
            ∑ i : Fin m,
              (((MeasureTheory.volume.restrict P).real
                  (D i : Set (Fin d → ℝ)))⁻¹ *
                ∫ y in (D i : Set (Fin d → ℝ)),
                  ((hmemP n).toLp (u n) :
                    Lp ℝ 2 (MeasureTheory.volume.restrict P)) y
                  ∂(MeasureTheory.volume.restrict P)) *
                (D i : Set (Fin d → ℝ)).indicator (fun _ ↦ (1 : ℝ)) x)
        2 (MeasureTheory.volume.restrict K) ≤
        regularCubeOuterAveragingENNRealConstant d * η := by
  intro n
  let U : Set (Fin d → ℝ) := ⋃ i : Fin m, (D i : Set (Fin d → ℝ))
  have hμKU :
      MeasureTheory.volume.restrict K ≤ MeasureTheory.volume.restrict U :=
    Measure.restrict_mono hD_cover le_rfl
  calc
    eLpNorm
        (fun x ↦
          u n x -
            ∑ i : Fin m,
              (((MeasureTheory.volume.restrict P).real
                  (D i : Set (Fin d → ℝ)))⁻¹ *
                ∫ y in (D i : Set (Fin d → ℝ)),
                  ((hmemP n).toLp (u n) :
                    Lp ℝ 2 (MeasureTheory.volume.restrict P)) y
                  ∂(MeasureTheory.volume.restrict P)) *
                (D i : Set (Fin d → ℝ)).indicator (fun _ ↦ (1 : ℝ)) x)
        2 (MeasureTheory.volume.restrict K)
        ≤ eLpNorm
            (fun x ↦
              u n x -
                ∑ i : Fin m,
                  (((MeasureTheory.volume.restrict P).real
                      (D i : Set (Fin d → ℝ)))⁻¹ *
                    ∫ y in (D i : Set (Fin d → ℝ)),
                      ((hmemP n).toLp (u n) :
                        Lp ℝ 2 (MeasureTheory.volume.restrict P)) y
                      ∂(MeasureTheory.volume.restrict P)) *
                    (D i : Set (Fin d → ℝ)).indicator (fun _ ↦ (1 : ℝ)) x)
            2 (MeasureTheory.volume.restrict U) :=
          eLpNorm_mono_measure _ hμKU
    _ ≤ regularCubeOuterAveragingENNRealConstant d * η := by
          simpa [U] using
            regularCubeOuterAveraging_piecewise_eLpNorm_on_iUnion_le_const_mul_translation_bound
              u hmemP D hD_grid hD_subsetP hD_posP hD_finiteP hD_disjoint hD_diam
              htranslation n

/--
%%handwave
name:
  Regular cube outer averages are close in \(L^2\)
statement:
  For a disjoint regular box family inside an outer compact set \(P\) that
  covers an inner compact set \(K\), if the translation modulus is small after
  multiplication by the dimension-dependent regular-cube constant, then the
  outer-box piecewise average is close in \(L^2(K)\).
proof:
  Apply the regular-cube averaging estimate and choose the translation
  modulus small enough to absorb the dimension-dependent constant.
-/
theorem regularCubeOuterAveraging_piecewise_eLpNorm_sub_lt_of_translation_bound
    {d : ℕ} {K P : Set (Fin d → ℝ)}
    (u : ℕ → (Fin d → ℝ) → ℝ)
    (hmemP : ∀ n : ℕ, MemLp (u n) 2 (MeasureTheory.volume.restrict P))
    (_hmemK : ∀ n : ℕ, MemLp (u n) 2 (MeasureTheory.volume.restrict K))
    {η : ℝ≥0∞} {ε δ : ℝ}
    (hηε : regularCubeOuterAveragingENNRealConstant d * η < ENNReal.ofReal ε)
    {m : ℕ} (D : Fin m → BoxIntegral.Box (Fin d))
    (hD_cover : K ⊆ ⋃ i : Fin m, (D i : Set (Fin d → ℝ)))
    (hD_grid : RegularGridBoxFamily D)
    (hD_subsetP : ∀ i : Fin m, (D i : Set (Fin d → ℝ)) ⊆ P)
    (hD_posP : ∀ i : Fin m, 0 < (MeasureTheory.volume.restrict P)
      (D i : Set (Fin d → ℝ)))
    (hD_finiteP : ∀ i : Fin m, (MeasureTheory.volume.restrict P)
      (D i : Set (Fin d → ℝ)) ≠ (⊤ : ℝ≥0∞))
    (_hD_finiteK : ∀ i : Fin m, (MeasureTheory.volume.restrict K)
      (D i : Set (Fin d → ℝ)) ≠ (⊤ : ℝ≥0∞))
    (hD_disjoint : ∀ i j : Fin m, i ≠ j →
      Disjoint (D i : Set (Fin d → ℝ)) (D j : Set (Fin d → ℝ)))
    (hD_diam : ∀ i : Fin m, ∀ x ∈ (D i : Set (Fin d → ℝ)),
      ∀ y ∈ (D i : Set (Fin d → ℝ)), dist x y < δ)
    (htranslation :
      ∀ h : Fin d → ℝ, ‖h‖ < δ →
        ∀ n : ℕ,
          eLpNorm (fun z ↦ u n (z + h) - u n z) 2
            (MeasureTheory.volume.restrict P) ≤ η) :
    ∀ n : ℕ,
      eLpNorm
        (fun x ↦
          u n x -
            ∑ i : Fin m,
              (((MeasureTheory.volume.restrict P).real
                  (D i : Set (Fin d → ℝ)))⁻¹ *
                ∫ y in (D i : Set (Fin d → ℝ)),
                  ((hmemP n).toLp (u n) :
                    Lp ℝ 2 (MeasureTheory.volume.restrict P)) y
                  ∂(MeasureTheory.volume.restrict P)) *
                (D i : Set (Fin d → ℝ)).indicator (fun _ ↦ (1 : ℝ)) x)
        2 (MeasureTheory.volume.restrict K) < ENNReal.ofReal ε := by
  intro n
  exact (regularCubeOuterAveraging_piecewise_eLpNorm_le_const_mul_translation_bound
    u hmemP _hmemK D hD_cover hD_grid hD_subsetP hD_posP hD_finiteP _hD_finiteK
    hD_disjoint hD_diam htranslation n).trans_lt hηε

/--
%%handwave
name:
  Regular cube outer averaging is controlled by translations
statement:
  Let finitely many disjoint regular boxes inside an outer compact set \(P\)
  cover an inner compact set \(K\), and let their diameters be below a
  translation scale \( \delta \).  If every translation shorter than
  \( \delta \) changes each function in a sequence by at most a small
  \(L^2(P)\) amount, then the outer-box averaging operator
  \(L^2(P)\to L^2(K)\) approximates every restriction to \(K\) below the
  prescribed \(L^2(K)\) error.
proof:
  On each box use the variance identity to bound the oscillation around the
  box average by the mean pairwise oscillation on that same full box.  Since
  every pair of points in the box differs by a translation of size below
  \( \delta \), translation tightness on \(P\) controls this oscillation.
  Disjointness of the boxes lets the estimates sum without denominator
  blowup, and regularity of boxes gives a dimension-only summation constant.
-/
theorem regularCubeOuterAveraging_dist_lt_of_translation_bound
    {d : ℕ} {K P : Set (Fin d → ℝ)}
    (u : ℕ → (Fin d → ℝ) → ℝ)
    (hmemP : ∀ n : ℕ, MemLp (u n) 2 (MeasureTheory.volume.restrict P))
    (hmemK : ∀ n : ℕ, MemLp (u n) 2 (MeasureTheory.volume.restrict K))
    {η : ℝ≥0∞} {ε δ : ℝ}
    (hηε : regularCubeOuterAveragingENNRealConstant d * η < ENNReal.ofReal ε)
    {m : ℕ} (D : Fin m → BoxIntegral.Box (Fin d))
    (hD_cover : K ⊆ ⋃ i : Fin m, (D i : Set (Fin d → ℝ)))
    (hD_grid : RegularGridBoxFamily D)
    (hD_subsetP : ∀ i : Fin m, (D i : Set (Fin d → ℝ)) ⊆ P)
    (hD_posP : ∀ i : Fin m, 0 < (MeasureTheory.volume.restrict P)
      (D i : Set (Fin d → ℝ)))
    (hD_finiteP : ∀ i : Fin m, (MeasureTheory.volume.restrict P)
      (D i : Set (Fin d → ℝ)) ≠ (⊤ : ℝ≥0∞))
    (hD_finiteK : ∀ i : Fin m, (MeasureTheory.volume.restrict K)
      (D i : Set (Fin d → ℝ)) ≠ (⊤ : ℝ≥0∞))
    (hD_disjoint : ∀ i j : Fin m, i ≠ j →
      Disjoint (D i : Set (Fin d → ℝ)) (D j : Set (Fin d → ℝ)))
    (hD_diam : ∀ i : Fin m, ∀ x ∈ (D i : Set (Fin d → ℝ)),
      ∀ y ∈ (D i : Set (Fin d → ℝ)), dist x y < δ)
    (htranslation :
      ∀ h : Fin d → ℝ, ‖h‖ < δ →
        ∀ n : ℕ,
          eLpNorm (fun z ↦ u n (z + h) - u n z) 2
            (MeasureTheory.volume.restrict P) ≤ η) :
    ∀ n : ℕ,
      dist ((hmemK n).toLp (u n))
        (finiteOuterCellAveragingOperator
          (MeasureTheory.volume.restrict P) (MeasureTheory.volume.restrict K)
          (fun i : Fin m ↦ (D i : Set (Fin d → ℝ)))
          (fun i : Fin m ↦ (D i).measurableSet_coe)
          hD_finiteP hD_finiteK
          ((hmemP n).toLp (u n))) < ε := by
  intro n
  exact finiteOuterCellAveragingOperator_dist_lt_of_piecewise_eLpNorm_sub_lt
    (MeasureTheory.volume.restrict P) (MeasureTheory.volume.restrict K)
    (fun i : Fin m ↦ (D i : Set (Fin d → ℝ)))
    (fun i : Fin m ↦ (D i).measurableSet_coe)
    hD_finiteP hD_finiteK (hmemK n) ((hmemP n).toLp (u n))
    (regularCubeOuterAveraging_piecewise_eLpNorm_sub_lt_of_translation_bound
      u hmemP hmemK hηε D hD_cover hD_grid hD_subsetP hD_posP hD_finiteP
      hD_finiteK hD_disjoint hD_diam htranslation n)

/--
%%handwave
name:
  Regular-cube finite-rank smoothing on nested Euclidean compacts
statement:
  For scalar functions on \(\mathbb R^d\), uniform \(L^2(P)\)-boundedness and
  uniform translation tightness on an outer compact \(P\) give, for every
  positive scale, a finite-rank continuous operator
  \(L^2(P)\to L^2(K)\) which uniformly approximates the restrictions to the
  inner compact \(K\).
proof:
  Choose the translation scale from translation tightness.  Use [a finite regular box cover between \(K\) and \(P\)](lean:JJMath.Uniformization.euclideanPiCompact_exists_regularCubeCover_between),
  build the outer averaging operator, and apply [the regular-box averaging error estimate](lean:JJMath.Uniformization.regularCubeOuterAveraging_dist_lt_of_translation_bound).
-/
theorem euclideanPiFrechetKolmogorov_smoothing_finiteRank_approx_L2_sequence
    {d : ℕ} {K P : Set (Fin d → ℝ)}
    (hK : IsCompact K) (hP : IsCompact P) (hKP : K ⊆ interior P)
    (u : ℕ → (Fin d → ℝ) → ℝ)
    (hmemP : ∀ n : ℕ, MemLp (u n) 2 (MeasureTheory.volume.restrict P))
    (hmemK : ∀ n : ℕ, MemLp (u n) 2 (MeasureTheory.volume.restrict K))
    (_hboundedP : ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ n : ℕ,
      eLpNorm (u n) 2 (MeasureTheory.volume.restrict P) ≤ C)
    (htranslationP : EuclideanL2TranslationTightOnCompact P u) :
    ∀ ε : ℝ, 0 < ε →
      ∃ A :
          Lp ℝ 2 (MeasureTheory.volume.restrict P) →L[ℝ]
            Lp ℝ 2 (MeasureTheory.volume.restrict K),
        FiniteDimensional ℝ A.range ∧
          ∀ n : ℕ,
            dist ((hmemK n).toLp (u n))
              (A ((hmemP n).toLp (u n))) < ε := by
  intro ε hε
  let C : ℝ := regularCubeOuterAveragingConstant d
  let η : ℝ≥0∞ := ENNReal.ofReal (ε / (2 * C))
  have hC_pos : 0 < C := regularCubeOuterAveragingConstant_pos d
  have hC_nonneg : 0 ≤ C := hC_pos.le
  have hη_pos : 0 < η := by
    rw [ENNReal.ofReal_pos]
    exact div_pos hε (mul_pos (by norm_num) hC_pos)
  have hηε : regularCubeOuterAveragingENNRealConstant d * η < ENNReal.ofReal ε := by
    have hprod :
        regularCubeOuterAveragingENNRealConstant d * η =
          ENNReal.ofReal (C * (ε / (2 * C))) := by
      change
        ENNReal.ofReal C * ENNReal.ofReal (ε / (2 * C)) =
          ENNReal.ofReal (C * (ε / (2 * C)))
      exact (ENNReal.ofReal_mul hC_nonneg).symm
    rw [hprod]
    rw [ENNReal.ofReal_lt_ofReal_iff hε]
    have hC_ne : C ≠ 0 := ne_of_gt hC_pos
    have hcalc : C * (ε / (2 * C)) = ε / 2 := by
      field_simp [hC_ne]
    rw [hcalc]
    linarith
  rcases htranslationP η hη_pos with ⟨δ, hδ, htranslate⟩
  rcases euclideanPiCompact_exists_regularCubeCover_between hK hP hKP δ hδ with
    ⟨m, D, hD_cover, hD_subsetP, hD_posP, hD_finiteP, hD_finiteK,
      hD_grid, hD_disjoint, hD_diam⟩
  let A :
      Lp ℝ 2 (MeasureTheory.volume.restrict P) →L[ℝ]
        Lp ℝ 2 (MeasureTheory.volume.restrict K) :=
    finiteOuterCellAveragingOperator
      (MeasureTheory.volume.restrict P) (MeasureTheory.volume.restrict K)
      (fun i : Fin m ↦ (D i : Set (Fin d → ℝ)))
      (fun i : Fin m ↦ (D i).measurableSet_coe)
      hD_finiteP hD_finiteK
  refine ⟨A, ?_, ?_⟩
  · exact finiteOuterCellAveragingOperator_finiteDimensional_range
      (MeasureTheory.volume.restrict P) (MeasureTheory.volume.restrict K)
      (fun i : Fin m ↦ (D i : Set (Fin d → ℝ)))
      (fun i : Fin m ↦ (D i).measurableSet_coe)
      hD_finiteP hD_finiteK
  · intro n
    simpa [A] using
      regularCubeOuterAveraging_dist_lt_of_translation_bound
        u hmemP hmemK hηε D hD_cover hD_grid hD_subsetP hD_posP hD_finiteP
        hD_finiteK hD_disjoint hD_diam htranslate n

/--
%%handwave
name:
  Finite-rank smoothing property for a measure on nested compact Euclidean sets
statement:
  A scalar sequence on a finite-dimensional real normed space has the local
  finite-rank smoothing property with respect to a measure \(\mu\) if,
  whenever \(K\) is compactly contained in a compact set \(P\), uniform
  \(L^2(P,\mu)\)-boundedness and uniform translation tightness on \(P\)
  give finite-rank continuous operators
  \(L^2(P,\mu)\to L^2(K,\mu)\) approximating all restrictions uniformly.
-/
def EuclideanSmoothingFiniteRankApproxStatementForMeasure (H : Type)
    [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasurableSpace H]
    (μ : Measure H) : Prop :=
  ∀ {K P : Set H}, IsCompact K → IsCompact P → K ⊆ interior P →
    (u : ℕ → H → ℝ) →
    (hmemP : ∀ n : ℕ, MemLp (u n) 2 (μ.restrict P)) →
    (hmemK : ∀ n : ℕ, MemLp (u n) 2 (μ.restrict K)) →
    (∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ n : ℕ,
      eLpNorm (u n) 2 (μ.restrict P) ≤ C) →
    EuclideanL2TranslationTightFamilyOnCompactForMeasure μ P u →
    ∀ ε : ℝ, 0 < ε →
      ∃ A :
          Lp ℝ 2 (μ.restrict P) →L[ℝ]
            Lp ℝ 2 (μ.restrict K),
        FiniteDimensional ℝ A.range ∧
          ∀ n : ℕ,
            dist ((hmemK n).toLp (u n))
              (A ((hmemP n).toLp (u n))) < ε

/--
%%handwave
name:
  Finite-rank smoothing property on nested compact Euclidean sets
statement:
  A scalar sequence on a finite-dimensional real normed space has the local
  finite-rank smoothing property if it has the measure-parametrized smoothing
  property with respect to Haar measure.
-/
def EuclideanSmoothingFiniteRankApproxStatement (H : Type)
    [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H] : Prop :=
  EuclideanSmoothingFiniteRankApproxStatementForMeasure H (volume : Measure H)

/--
%%handwave
name:
  \(L^p\) membership after removing a positive measure scale
statement:
  If \(c>0\) and \(f\in L^p(c\mu)\), then \(f\in L^p(\mu)\).
proof:
  The measure \(\mu\) is bounded by \(c^{-1}(c\mu)\); use monotonicity of
  \(L^p\) membership under domination by a finite scalar multiple.
-/
private theorem memLp_of_smul_measure_nnreal {α E : Type}
    [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {p : ℝ≥0∞} {c : ℝ≥0} (hc : c ≠ 0)
    {f : α → E} (hf : MemLp f p (c • μ)) :
    MemLp f p μ := by
  have hμ_le : μ ≤ ((c : ℝ≥0∞)⁻¹) • (c • μ) := by
    calc
      μ = (1 : ℝ≥0∞) • μ := by simp
      _ = ((c : ℝ≥0∞)⁻¹ * (c : ℝ≥0∞)) • μ := by
        rw [ENNReal.inv_mul_cancel]
        · exact ENNReal.coe_ne_zero.2 hc
        · simp
      _ = ((c : ℝ≥0∞)⁻¹) • ((c : ℝ≥0∞) • μ) := by
        rw [smul_smul]
      _ ≤ ((c : ℝ≥0∞)⁻¹) • (c • μ) := by simp
  exact hf.of_measure_le_smul (by simp [hc]) hμ_le

/--
%%handwave
name:
  Almost-everywhere descent from a positively scaled measure
statement:
  If \(c>0\) and a property holds almost everywhere for \(c\mu\), then it
  holds almost everywhere for \(\mu\).
proof:
  Multiplication of a measure by a nonzero finite constant does not change its
  null sets.
-/
private theorem ae_of_smul_measure_nnreal {α : Type} [MeasurableSpace α]
    {μ : Measure α} {c : ℝ≥0} (hc : c ≠ 0) {p : α → Prop} :
    (∀ᵐ x ∂c • μ, p x) → (∀ᵐ x ∂μ, p x) := by
  intro h
  have hae : ae ((c : ℝ≥0∞) • μ) = ae μ :=
    Measure.ae_ennreal_smul_measure_eq (ENNReal.coe_ne_zero.2 hc) μ
  change ∀ᵐ x ∂(c : ℝ≥0∞) • μ, p x at h
  rwa [hae] at h

/--
%%handwave
name:
  Almost-everywhere ascent to a scaled measure
statement:
  If a property holds \(\mu\)-almost everywhere, then it holds
  \(c\mu\)-almost everywhere for every \(c\ge0\).
proof:
  Every \(\mu\)-null set remains null after multiplying the measure by \(c\).
-/
private theorem ae_smul_measure_nnreal {α : Type} [MeasurableSpace α]
    {μ : Measure α} (c : ℝ≥0) {p : α → Prop} :
    (∀ᵐ x ∂μ, p x) → (∀ᵐ x ∂c • μ, p x) := by
  intro h
  exact Measure.ae_smul_measure h c

private noncomputable def lpRescaleToOriginal {α : Type} [MeasurableSpace α]
    (μ : Measure α) {c : ℝ≥0} (hc : c ≠ 0) :
    Lp ℝ 2 (c • μ) →L[ℝ] Lp ℝ 2 μ := by
  let s : ℝ≥0 := c ^ (2 : ℝ≥0∞).toReal⁻¹
  let T : Lp ℝ 2 (c • μ) →ₗ[ℝ] Lp ℝ 2 μ :=
  { toFun := fun f =>
      (memLp_of_smul_measure_nnreal (μ := μ) (c := c) hc (Lp.memLp f)).toLp f
    map_add' := by
      intro f g
      apply Lp.ext
      have hfg0 : ⇑(f + g) =ᵐ[μ] ⇑f + ⇑g :=
        ae_of_smul_measure_nnreal (μ := μ) (c := c) hc (Lp.coeFn_add f g)
      filter_upwards
        [MemLp.coeFn_toLp
          (memLp_of_smul_measure_nnreal (μ := μ) (c := c) hc (Lp.memLp (f + g))),
        MemLp.coeFn_toLp
          (memLp_of_smul_measure_nnreal (μ := μ) (c := c) hc (Lp.memLp f)),
        MemLp.coeFn_toLp
          (memLp_of_smul_measure_nnreal (μ := μ) (c := c) hc (Lp.memLp g)),
        Lp.coeFn_add
          ((memLp_of_smul_measure_nnreal (μ := μ) (c := c) hc (Lp.memLp f)).toLp f)
          ((memLp_of_smul_measure_nnreal (μ := μ) (c := c) hc (Lp.memLp g)).toLp g),
        hfg0] with x hfg hf hg hsum hfg0
      rw [hfg, hsum]
      simpa [Pi.add_apply, hf, hg] using hfg0
    map_smul' := by
      intro a f
      apply Lp.ext
      have haf0 : ⇑(a • f) =ᵐ[μ] a • ⇑f :=
        ae_of_smul_measure_nnreal (μ := μ) (c := c) hc (Lp.coeFn_smul a f)
      filter_upwards
        [MemLp.coeFn_toLp
          (memLp_of_smul_measure_nnreal (μ := μ) (c := c) hc (Lp.memLp (a • f))),
        MemLp.coeFn_toLp
          (memLp_of_smul_measure_nnreal (μ := μ) (c := c) hc (Lp.memLp f)),
        Lp.coeFn_smul a
          ((memLp_of_smul_measure_nnreal (μ := μ) (c := c) hc (Lp.memLp f)).toLp f),
        haf0] with x haf hf hsmul hsmul0
      rw [haf, hsmul0]
      symm
      simpa [RingHom.id_apply, Pi.smul_apply, hf] using hsmul }
  refine LinearMap.mkContinuous T (((s : ℝ≥0) : ℝ)⁻¹) ?_
  intro f
  dsimp [T]
  rw [Lp.norm_toLp]
  have hscale :=
    eLpNorm_smul_measure_of_ne_zero'
      (μ := μ) (f := (f : α → ℝ)) (p := (2 : ℝ≥0∞)) hc
  have hscale_real := congrArg ENNReal.toReal hscale
  rw [ENNReal.toReal_smul] at hscale_real
  have hscale_real' :
      (eLpNorm (⇑f) 2 (c • μ)).toReal =
        ((s : ℝ≥0) : ℝ) * (eLpNorm (⇑f) 2 μ).toReal := by
    simpa [s, smul_eq_mul] using hscale_real
  have hspos_nn : 0 < s := by
    dsimp [s]
    exact NNReal.rpow_pos (show 0 < c from by positivity)
  have hspos : 0 < ((s : ℝ≥0) : ℝ) := by
    exact_mod_cast hspos_nn
  have hnormeq :
      (eLpNorm (⇑f) 2 μ).toReal = ((s : ℝ≥0) : ℝ)⁻¹ * ‖f‖ := by
    rw [Lp.norm_def f, hscale_real']
    field_simp [hspos.ne']
  exact le_of_eq hnormeq

private noncomputable def lpOriginalToRescale {α : Type} [MeasurableSpace α]
    (μ : Measure α) {c : ℝ≥0} (hc : c ≠ 0) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 (c • μ) := by
  let s : ℝ≥0 := c ^ (2 : ℝ≥0∞).toReal⁻¹
  let T : Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 (c • μ) :=
  { toFun := fun f => ((Lp.memLp f).smul_measure (by simp)).toLp f
    map_add' := by
      intro f g
      let hf : MemLp (f : α → ℝ) 2 (c • μ) := (Lp.memLp f).smul_measure (by simp)
      let hg : MemLp (g : α → ℝ) 2 (c • μ) := (Lp.memLp g).smul_measure (by simp)
      let hfg : MemLp ((f + g : Lp ℝ 2 μ) : α → ℝ) 2 (c • μ) :=
        (Lp.memLp (f + g)).smul_measure (by simp)
      let hsum : MemLp ((f : α → ℝ) + (g : α → ℝ)) 2 (c • μ) := hf.add hg
      have hae :
          ((f + g : Lp ℝ 2 μ) : α → ℝ) =ᵐ[c • μ] (f : α → ℝ) + (g : α → ℝ) :=
        ae_smul_measure_nnreal (μ := μ) c (Lp.coeFn_add f g)
      calc
        hfg.toLp ((f + g : Lp ℝ 2 μ) : α → ℝ)
            = hsum.toLp ((f : α → ℝ) + (g : α → ℝ)) :=
          MemLp.toLp_congr hfg hsum hae
        _ = hf.toLp (f : α → ℝ) + hg.toLp (g : α → ℝ) :=
          MemLp.toLp_add hf hg
    map_smul' := by
      intro a f
      let hf : MemLp (f : α → ℝ) 2 (c • μ) := (Lp.memLp f).smul_measure (by simp)
      let haf : MemLp ((a • f : Lp ℝ 2 μ) : α → ℝ) 2 (c • μ) :=
        (Lp.memLp (a • f)).smul_measure (by simp)
      let hscaled : MemLp (a • (f : α → ℝ)) 2 (c • μ) := hf.const_smul a
      have hae :
          ((a • f : Lp ℝ 2 μ) : α → ℝ) =ᵐ[c • μ] a • (f : α → ℝ) :=
        ae_smul_measure_nnreal (μ := μ) c (Lp.coeFn_smul a f)
      calc
        haf.toLp ((a • f : Lp ℝ 2 μ) : α → ℝ)
            = hscaled.toLp (a • (f : α → ℝ)) :=
          MemLp.toLp_congr haf hscaled hae
        _ = a • hf.toLp (f : α → ℝ) :=
          MemLp.toLp_const_smul a hf }
  refine LinearMap.mkContinuous T ((s : ℝ≥0) : ℝ) ?_
  intro f
  dsimp [T]
  rw [Lp.norm_toLp]
  have hscale :=
    eLpNorm_smul_measure_of_ne_zero'
      (μ := μ) (f := (f : α → ℝ)) (p := (2 : ℝ≥0∞)) hc
  have hscale_real := congrArg ENNReal.toReal hscale
  rw [ENNReal.toReal_smul] at hscale_real
  have hscale_real' :
      (eLpNorm (⇑f) 2 (c • μ)).toReal =
        ((s : ℝ≥0) : ℝ) * (eLpNorm (⇑f) 2 μ).toReal := by
    simpa [s, smul_eq_mul] using hscale_real
  have hnormeq :
      (eLpNorm (⇑f) 2 (c • μ)).toReal = ((s : ℝ≥0) : ℝ) * ‖f‖ := by
    rw [Lp.norm_def f, hscale_real']
  exact le_of_eq hnormeq

/--
%%handwave
name:
  Removing a measure scale from an \(L^2\) representative
statement:
  If \(c>0\) and \(f\in L^2(c\mu)\), the canonical map
  \(L^2(c\mu)\to L^2(\mu)\) sends the class of \(f\) to the class of the same
  function \(f\).
proof:
  Both classes have representatives equal to \(f\) almost everywhere, and
  \(c\mu\) and \(\mu\) have the same null sets.
-/
private theorem lpRescaleToOriginal_toLp {α : Type} [MeasurableSpace α]
    {μ : Measure α} {c : ℝ≥0} (hc : c ≠ 0) {f : α → ℝ}
    (hf : MemLp f 2 (c • μ)) :
    lpRescaleToOriginal μ hc (hf.toLp f) =
      (memLp_of_smul_measure_nnreal (μ := μ) (c := c) hc hf).toLp f := by
  apply Lp.ext
  refine (MemLp.coeFn_toLp
    (memLp_of_smul_measure_nnreal (μ := μ) (c := c) hc (Lp.memLp (hf.toLp f)))).trans ?_
  have h_to_f : (hf.toLp f : α → ℝ) =ᵐ[μ] f :=
    ae_of_smul_measure_nnreal (μ := μ) (c := c) hc (MemLp.coeFn_toLp hf)
  refine h_to_f.trans ?_
  exact (MemLp.coeFn_toLp (memLp_of_smul_measure_nnreal (μ := μ) (c := c) hc hf)).symm

/--
%%handwave
name:
  Adding a measure scale to an \(L^2\) representative
statement:
  If \(c>0\) and \(f\in L^2(\mu)\), the canonical map
  \(L^2(\mu)\to L^2(c\mu)\) sends the class of \(f\) to the class of \(f\)
  for the scaled measure.
proof:
  The two canonical representatives agree with \(f\) outside a
  \(c\mu\)-null set.
-/
private theorem lpOriginalToRescale_toLp {α : Type} [MeasurableSpace α]
    {μ : Measure α} {c : ℝ≥0} (hc : c ≠ 0) {f : α → ℝ}
    (hf : MemLp f 2 μ) :
    lpOriginalToRescale μ hc (hf.toLp f) =
      (hf.smul_measure (by simp)).toLp f := by
  apply Lp.ext
  refine (MemLp.coeFn_toLp ((Lp.memLp (hf.toLp f)).smul_measure (by simp))).trans ?_
  have h_to_f : (hf.toLp f : α → ℝ) =ᵐ[c • μ] f :=
    ae_smul_measure_nnreal (μ := μ) c (MemLp.coeFn_toLp hf)
  refine h_to_f.trans ?_
  exact (MemLp.coeFn_toLp (hf.smul_measure (by simp))).symm

/--
%%handwave
name:
  Norm bound for adding a measure scale
statement:
  For \(c>0\) and \(f\in L^2(\mu)\),
  \[\lVert f\rVert_{L^2(c\mu)}\le\sqrt c\,\lVert f\rVert_{L^2(\mu)}.\]
proof:
  Use the exact scaling formula for the \(L^2\)-norm under multiplication of
  the measure by \(c\), then pass from extended norms to real norms.
-/
private theorem lpOriginalToRescale_norm_le {α : Type} [MeasurableSpace α]
    {μ : Measure α} {c : ℝ≥0} (hc : c ≠ 0) (f : Lp ℝ 2 μ) :
    ‖lpOriginalToRescale μ hc f‖ ≤
      (((c ^ (2 : ℝ≥0∞).toReal⁻¹ : ℝ≥0) : ℝ) * ‖f‖) := by
  dsimp [lpOriginalToRescale]
  rw [Lp.norm_toLp]
  have hscale :=
    eLpNorm_smul_measure_of_ne_zero'
      (μ := μ) (f := (f : α → ℝ)) (p := (2 : ℝ≥0∞)) hc
  have hscale_real := congrArg ENNReal.toReal hscale
  rw [ENNReal.toReal_smul] at hscale_real
  have hscale_real' :
      (eLpNorm (⇑f) 2 (c • μ)).toReal =
        (((c ^ (2 : ℝ≥0∞).toReal⁻¹ : ℝ≥0) : ℝ) *
          (eLpNorm (⇑f) 2 μ).toReal) := by
    simpa [smul_eq_mul, NNReal.coe_rpow] using hscale_real
  rw [Lp.norm_def f, hscale_real']
  rfl

/--
%%handwave
name:
  Distance bound for adding a measure scale
statement:
  For \(c>0\) and \(f,g\in L^2(\mu)\),
  \[d_{L^2(c\mu)}(f,g)\le\sqrt c\,d_{L^2(\mu)}(f,g).\]
proof:
  Apply [the norm scaling bound](lean:lpOriginalToRescale_norm_le) to \(f-g\).
-/
private theorem lpOriginalToRescale_dist_le {α : Type} [MeasurableSpace α]
    {μ : Measure α} {c : ℝ≥0} (hc : c ≠ 0) (f g : Lp ℝ 2 μ) :
    dist (lpOriginalToRescale μ hc f) (lpOriginalToRescale μ hc g) ≤
      (((c ^ (2 : ℝ≥0∞).toReal⁻¹ : ℝ≥0) : ℝ) * dist f g) := by
  simpa [dist_eq_norm, map_sub] using
    lpOriginalToRescale_norm_le (μ := μ) (c := c) hc (f - g)

private noncomputable def lpMeasureEqCLM {α : Type} [MeasurableSpace α]
    {μ ν : Measure α} (h : μ = ν) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 ν := by
  subst h
  exact ContinuousLinearMap.id ℝ (Lp ℝ 2 μ)

/--
%%handwave
name:
  Transport across equal measures preserves an \(L^2\) representative
statement:
  If \(\mu=\nu\) and \(f\in L^2(\mu)\cap L^2(\nu)\), the canonical transport
  \(L^2(\mu)\to L^2(\nu)\) sends the class of \(f\) to the class of \(f\).
proof:
  Substitute the equality of measures and use equality of \(L^2\) classes
  with identical representatives.
-/
private theorem lpMeasureEqCLM_toLp {α : Type} [MeasurableSpace α]
    {μ ν : Measure α} (h : μ = ν) {f : α → ℝ}
    (hfμ : MemLp f 2 μ) (hfν : MemLp f 2 ν) :
    lpMeasureEqCLM h (hfμ.toLp f) = hfν.toLp f := by
  subst h
  exact MemLp.toLp_congr hfμ hfν Filter.EventuallyEq.rfl

/--
%%handwave
name:
  Transport across equal measures is an isometry
statement:
  If \(\mu=\nu\), canonical transport from \(L^2(\mu)\) to \(L^2(\nu)\)
  preserves distances.
proof:
  After substituting \(\mu=\nu\), the transport is the identity map.
-/
private theorem lpMeasureEqCLM_dist {α : Type} [MeasurableSpace α]
    {μ ν : Measure α} (h : μ = ν) (f g : Lp ℝ 2 μ) :
    dist (lpMeasureEqCLM h f) (lpMeasureEqCLM h g) = dist f g := by
  subst h
  rfl

/--
%%handwave
name:
  Finite rank is preserved by precomposition
statement:
  If \(A:E\to F\) has finite-dimensional range and \(B:G\to E\) is linear,
  then \(A\circ B\) has finite-dimensional range.
proof:
  The range of \(A\circ B\) is contained in the range of \(A\).
-/
private theorem finiteDimensional_range_comp_right {E F G : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A : E →L[ℝ] F) (B : G →L[ℝ] E)
    [FiniteDimensional ℝ A.range] :
    FiniteDimensional ℝ (A.comp B).range := by
  exact Submodule.finiteDimensional_of_le (S₂ := A.range) (by
    rintro y ⟨x, rfl⟩
    exact LinearMap.mem_range_self (A : E →ₗ[ℝ] F) (B x))

/--
%%handwave
name:
  Finite rank is preserved by postcomposition
statement:
  If \(A:E\to F\) has finite-dimensional range and \(L:F\to G\) is linear,
  then \(L\circ A\) has finite-dimensional range.
proof:
  Its range lies in the linear image under \(L\) of the finite-dimensional
  range of \(A\).
-/
private theorem finiteDimensional_range_comp_left {E F G : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →L[ℝ] G) (A : E →L[ℝ] F)
    [FiniteDimensional ℝ A.range] :
    FiniteDimensional ℝ (L.comp A).range := by
  let Lr : A.range →ₗ[ℝ] G := (L : F →ₗ[ℝ] G).comp A.range.subtype
  haveI : FiniteDimensional ℝ Lr.range := LinearMap.finiteDimensional_range Lr
  exact Submodule.finiteDimensional_of_le (S₂ := Lr.range) (by
    rintro y ⟨x, rfl⟩
    exact ⟨⟨A x, LinearMap.mem_range_self (A : E →ₗ[ℝ] F) x⟩, rfl⟩)

/--
%%handwave
name:
  Uniform \(L^2\) bounds after removing a measure scale
statement:
  If \(c>0\) and a family has a finite uniform \(L^2(c\mu)\)-norm bound, then
  it has a finite uniform \(L^2(\mu)\)-norm bound.
proof:
  Rescale by \(c^{-1/2}\) using the \(L^2\)-norm scaling formula; the new bound
  is finite because both factors are finite.
-/
private theorem exists_eLpNorm_bound_of_smul_measure {ι α : Type}
    [MeasurableSpace α] {μ : Measure α} {c : ℝ≥0} (hc : c ≠ 0)
    {u : ι → α → ℝ} :
    (∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ i : ι,
      eLpNorm (u i) 2 (c • μ) ≤ C) →
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ i : ι,
      eLpNorm (u i) 2 μ ≤ C := by
  rintro ⟨C, hCtop, hC⟩
  let cinv : ℝ≥0 := c⁻¹
  let s : ℝ≥0 := cinv ^ (2 : ℝ≥0∞).toReal⁻¹
  refine ⟨(s : ℝ≥0∞) * C, ENNReal.mul_lt_top ENNReal.coe_lt_top hCtop, ?_⟩
  intro i
  have hcinv_ne : cinv ≠ 0 := by
    dsimp [cinv]
    exact inv_ne_zero hc
  have hmeasure : cinv • (c • μ) = μ := by
    dsimp [cinv]
    exact inv_smul_smul₀ hc μ
  have hscale :=
    eLpNorm_smul_measure_of_ne_zero'
      (μ := c • μ) (f := u i) (p := (2 : ℝ≥0∞)) hcinv_ne
  rw [← hmeasure, hscale]
  dsimp [s]
  exact mul_le_mul_right (hC i) _

/--
%%handwave
name:
  Translation tightness after removing a measure scale
statement:
  If \(c>0\) and a family is uniformly translation-tight in \(L^2(c\mu)\) on
  \(K\), then it is uniformly translation-tight in \(L^2(\mu)\) on \(K\).
proof:
  The unscaled translation difference norm is \(c^{-1/2}\) times its scaled
  norm. Apply tightness with the tolerance multiplied by \(\sqrt c\).
-/
private theorem translationTightFamilyOnCompact_of_smul_measure {ι H : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasurableSpace H]
    {μ : Measure H} {c : ℝ≥0} (hc : c ≠ 0) {K : Set H}
    {u : ι → H → ℝ} :
    EuclideanL2TranslationTightFamilyOnCompactForMeasure (c • μ) K u →
    EuclideanL2TranslationTightFamilyOnCompactForMeasure μ K u := by
  intro htranslation ε hε
  let cinv : ℝ≥0 := c⁻¹
  let s : ℝ≥0 := cinv ^ (2 : ℝ≥0∞).toReal⁻¹
  have hcinv_ne : cinv ≠ 0 := by
    dsimp [cinv]
    exact inv_ne_zero hc
  have hcpos : 0 < c := pos_iff_ne_zero.2 hc
  have hs_pos : 0 < s := by
    dsimp [s, cinv]
    exact NNReal.rpow_pos (inv_pos.2 hcpos)
  have hs_ne : (s : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 hs_pos.ne'
  have hε' : 0 < (s : ℝ≥0∞)⁻¹ * ε := by
    exact ENNReal.mul_pos (ENNReal.inv_ne_zero.2 ENNReal.coe_ne_top) hε.ne'
  obtain ⟨δ, hδpos, hδ⟩ := htranslation ((s : ℝ≥0∞)⁻¹ * ε) hε'
  refine ⟨δ, hδpos, fun h hh i => ?_⟩
  let f : H → ℝ := fun z ↦ u i (z + h) - u i z
  have hmeasure : cinv • (c • μ.restrict K) = μ.restrict K := by
    dsimp [cinv]
    exact inv_smul_smul₀ hc (μ.restrict K)
  have hscale :=
    eLpNorm_smul_measure_of_ne_zero'
      (μ := c • μ.restrict K) (f := f) (p := (2 : ℝ≥0∞)) hcinv_ne
  calc
    eLpNorm f 2 (μ.restrict K)
        = eLpNorm f 2 (cinv • (c • μ.restrict K)) := by rw [hmeasure]
    _ = (s : ℝ≥0∞) * eLpNorm f 2 (c • μ.restrict K) := by
      simpa [s, smul_eq_mul] using hscale
    _ ≤ (s : ℝ≥0∞) * ((s : ℝ≥0∞)⁻¹ * ε) := by
      exact mul_le_mul_right (by
        simpa [f, Measure.restrict_smul] using hδ h hh i) _
    _ = ε := by
      exact ENNReal.mul_inv_cancel_left hs_ne ENNReal.coe_ne_top

/--
%%handwave
name:
  Finite-rank approximation after scaling both measures
statement:
  Let \(c>0\). If finite-rank maps \(L^2(\mu_P)\to L^2(\mu_K)\) approximate a
  sequence uniformly, then finite-rank maps
  \(L^2(c\mu_P)\to L^2(c\mu_K)\) approximate the same sequence uniformly.
proof:
  Conjugate an approximating map by the canonical rescaling maps on source
  and target, choosing the original tolerance divided by \(\sqrt c\).
  Composition preserves finite rank and the target rescaling multiplies
  errors by at most \(\sqrt c\).
-/
private theorem finiteRankApproximationBetweenMeasures_of_smul_measure
    {H : Type} [MeasurableSpace H] {μP μK : Measure H} {c : ℝ≥0} (hc : c ≠ 0)
    {u : ℕ → H → ℝ}
    (hmemP_smul : ∀ n : ℕ, MemLp (u n) 2 (c • μP))
    (hmemK_smul : ∀ n : ℕ, MemLp (u n) 2 (c • μK))
    (hmemP : ∀ n : ℕ, MemLp (u n) 2 μP)
    (hmemK : ∀ n : ℕ, MemLp (u n) 2 μK)
    (happrox :
      ∀ ε : ℝ, 0 < ε →
        ∃ A : Lp ℝ 2 μP →L[ℝ] Lp ℝ 2 μK,
          FiniteDimensional ℝ A.range ∧
            ∀ n : ℕ,
              dist ((hmemK n).toLp (u n))
                (A ((hmemP n).toLp (u n))) < ε) :
    ∀ ε : ℝ, 0 < ε →
      ∃ A : Lp ℝ 2 (c • μP) →L[ℝ] Lp ℝ 2 (c • μK),
        FiniteDimensional ℝ A.range ∧
          ∀ n : ℕ,
            dist ((hmemK_smul n).toLp (u n))
              (A ((hmemP_smul n).toLp (u n))) < ε := by
  intro ε hε
  let s : ℝ≥0 := c ^ (2 : ℝ≥0∞).toReal⁻¹
  have hcpos : 0 < c := pos_iff_ne_zero.2 hc
  have hspos_nn : 0 < s := by
    dsimp [s]
    exact NNReal.rpow_pos hcpos
  have hspos : 0 < ((s : ℝ≥0) : ℝ) := by
    exact_mod_cast hspos_nn
  have hs_ne : ((s : ℝ≥0) : ℝ) ≠ 0 := ne_of_gt hspos
  obtain ⟨A0, hA0fin, hA0approx⟩ :=
    happrox (ε / ((s : ℝ≥0) : ℝ)) (div_pos hε hspos)
  let Apre : Lp ℝ 2 (c • μP) →L[ℝ] Lp ℝ 2 μK :=
    A0.comp (lpRescaleToOriginal μP hc)
  let A : Lp ℝ 2 (c • μP) →L[ℝ] Lp ℝ 2 (c • μK) :=
    (lpOriginalToRescale μK hc).comp Apre
  refine ⟨A, ?_, ?_⟩
  · letI : FiniteDimensional ℝ A0.range := hA0fin
    have hpre : FiniteDimensional ℝ Apre.range := by
      dsimp [Apre]
      exact finiteDimensional_range_comp_right A0 (lpRescaleToOriginal μP hc)
    letI : FiniteDimensional ℝ Apre.range := hpre
    dsimp [A]
    exact finiteDimensional_range_comp_left (lpOriginalToRescale μK hc) Apre
  · intro n
    have hrescaleIn :
        lpRescaleToOriginal μP hc ((hmemP_smul n).toLp (u n)) =
          (hmemP n).toLp (u n) :=
      (lpRescaleToOriginal_toLp (μ := μP) (c := c) hc (hmemP_smul n)).trans
        (MemLp.toLp_congr
          (memLp_of_smul_measure_nnreal (μ := μP) (c := c) hc (hmemP_smul n))
          (hmemP n) Filter.EventuallyEq.rfl)
    have htarget :
        lpOriginalToRescale μK hc ((hmemK n).toLp (u n)) =
          (hmemK_smul n).toLp (u n) :=
      (lpOriginalToRescale_toLp (μ := μK) (c := c) hc (hmemK n)).trans
        (MemLp.toLp_congr ((hmemK n).smul_measure (by simp))
          (hmemK_smul n) Filter.EventuallyEq.rfl)
    have hscaled_lt :
        ((s : ℝ≥0) : ℝ) *
            dist ((hmemK n).toLp (u n)) (A0 ((hmemP n).toLp (u n))) < ε := by
      have hmul :=
        mul_lt_mul_of_pos_left (hA0approx n) hspos
      have hcancel : ((s : ℝ≥0) : ℝ) * (ε / ((s : ℝ≥0) : ℝ)) = ε := by
        field_simp [hs_ne]
      rwa [hcancel] at hmul
    calc
      dist ((hmemK_smul n).toLp (u n))
          (A ((hmemP_smul n).toLp (u n)))
          =
        dist (lpOriginalToRescale μK hc ((hmemK n).toLp (u n)))
          (lpOriginalToRescale μK hc (A0 ((hmemP n).toLp (u n)))) := by
        rw [← htarget]
        dsimp [A, Apre]
        rw [hrescaleIn]
      _ ≤ ((s : ℝ≥0) : ℝ) *
          dist ((hmemK n).toLp (u n)) (A0 ((hmemP n).toLp (u n))) := by
        simpa [s] using
          lpOriginalToRescale_dist_le (μ := μK) (c := c) hc
            ((hmemK n).toLp (u n)) (A0 ((hmemP n).toLp (u n)))
      _ < ε := hscaled_lt

/--
%%handwave
name:
  Finite-rank approximation transported across equal measures
statement:
  If \(\mu_P=\nu_P\) and \(\mu_K=\nu_K\), a uniform finite-rank approximation
  of a sequence from \(L^2(\nu_P)\) to \(L^2(\nu_K)\) yields one from
  \(L^2(\mu_P)\) to \(L^2(\mu_K)\).
proof:
  Conjugate by the canonical isometries induced by equality of measures.
  These preserve the represented functions and distances, while composition
  preserves finite-dimensional range.
-/
private theorem finiteRankApproximationBetweenMeasures_of_measure_eq
    {H : Type} [MeasurableSpace H] {μP μK νP νK : Measure H}
    (hP : μP = νP) (hK : μK = νK) {u : ℕ → H → ℝ}
    (hmemPμ : ∀ n : ℕ, MemLp (u n) 2 μP)
    (hmemKμ : ∀ n : ℕ, MemLp (u n) 2 μK)
    (hmemPν : ∀ n : ℕ, MemLp (u n) 2 νP)
    (hmemKν : ∀ n : ℕ, MemLp (u n) 2 νK)
    (happrox :
      ∀ ε : ℝ, 0 < ε →
        ∃ A : Lp ℝ 2 νP →L[ℝ] Lp ℝ 2 νK,
          FiniteDimensional ℝ A.range ∧
            ∀ n : ℕ,
              dist ((hmemKν n).toLp (u n))
                (A ((hmemPν n).toLp (u n))) < ε) :
    ∀ ε : ℝ, 0 < ε →
      ∃ A : Lp ℝ 2 μP →L[ℝ] Lp ℝ 2 μK,
        FiniteDimensional ℝ A.range ∧
          ∀ n : ℕ,
            dist ((hmemKμ n).toLp (u n))
              (A ((hmemPμ n).toLp (u n))) < ε := by
  intro ε hε
  obtain ⟨A0, hA0fin, hA0approx⟩ := happrox ε hε
  let inCast : Lp ℝ 2 μP →L[ℝ] Lp ℝ 2 νP := lpMeasureEqCLM hP
  let outCast : Lp ℝ 2 νK →L[ℝ] Lp ℝ 2 μK := lpMeasureEqCLM hK.symm
  let Apre : Lp ℝ 2 μP →L[ℝ] Lp ℝ 2 νK := A0.comp inCast
  let A : Lp ℝ 2 μP →L[ℝ] Lp ℝ 2 μK := outCast.comp Apre
  refine ⟨A, ?_, ?_⟩
  · letI : FiniteDimensional ℝ A0.range := hA0fin
    have hpre : FiniteDimensional ℝ Apre.range := by
      dsimp [Apre]
      exact finiteDimensional_range_comp_right A0 inCast
    letI : FiniteDimensional ℝ Apre.range := hpre
    dsimp [A]
    exact finiteDimensional_range_comp_left outCast Apre
  · intro n
    have hin :
        inCast ((hmemPμ n).toLp (u n)) = (hmemPν n).toLp (u n) := by
      dsimp [inCast]
      exact lpMeasureEqCLM_toLp hP (hmemPμ n) (hmemPν n)
    have hout :
        outCast ((hmemKν n).toLp (u n)) = (hmemKμ n).toLp (u n) := by
      dsimp [outCast]
      exact lpMeasureEqCLM_toLp hK.symm (hmemKν n) (hmemKμ n)
    calc
      dist ((hmemKμ n).toLp (u n)) (A ((hmemPμ n).toLp (u n)))
          =
        dist (outCast ((hmemKν n).toLp (u n)))
          (outCast (A0 (inCast ((hmemPμ n).toLp (u n))))) := by
        rw [hout]
        rfl
      _ =
        dist (outCast ((hmemKν n).toLp (u n)))
          (outCast (A0 ((hmemPν n).toLp (u n)))) := by
        rw [hin]
      _ = dist ((hmemKν n).toLp (u n)) (A0 ((hmemPν n).toLp (u n))) := by
        simpa [outCast] using
          lpMeasureEqCLM_dist hK.symm
            ((hmemKν n).toLp (u n)) (A0 ((hmemPν n).toLp (u n)))
      _ < ε := hA0approx n

/--
%%handwave
name:
  Finite-rank approximation operators are transported by rescaling the measure
statement:
  Suppose finite-rank operators \(L^2(P,\mu)\to L^2(K,\mu)\) approximate a
  sequence of scalar functions uniformly.  If the measure is multiplied by a
  positive constant, then conjugating by the canonical identity maps between
  the corresponding \(L^2\)-spaces gives finite-rank operators
  \(L^2(P,c\mu)\to L^2(K,c\mu)\) with the same uniform approximation property,
  after rescaling the tolerance.
proof:
  The identity maps between the two \(L^2\)-spaces are continuous linear maps
  in both directions, with norms scaled by the square root of the measure
  multiplier.  They send the \(L^2\)-class of an honest representative to the
  same representative for the other measure.  Therefore the conjugated
  operator has finite-dimensional range, and its error is bounded by the
  original error times the fixed square-root scale.
-/
theorem finiteRankApproximationOnNestedCompacts_of_smul_measure
    {H : Type} [MeasurableSpace H] {μ : Measure H} {c : ℝ≥0} (hc : c ≠ 0)
    {K P : Set H} {u : ℕ → H → ℝ}
    (hmemP_smul : ∀ n : ℕ, MemLp (u n) 2 ((c • μ).restrict P))
    (hmemK_smul : ∀ n : ℕ, MemLp (u n) 2 ((c • μ).restrict K))
    (hmemP : ∀ n : ℕ, MemLp (u n) 2 (μ.restrict P))
    (hmemK : ∀ n : ℕ, MemLp (u n) 2 (μ.restrict K))
    (happrox :
      ∀ ε : ℝ, 0 < ε →
        ∃ A :
            Lp ℝ 2 (μ.restrict P) →L[ℝ]
              Lp ℝ 2 (μ.restrict K),
          FiniteDimensional ℝ A.range ∧
            ∀ n : ℕ,
              dist ((hmemK n).toLp (u n))
                (A ((hmemP n).toLp (u n))) < ε) :
    ∀ ε : ℝ, 0 < ε →
      ∃ A :
          Lp ℝ 2 ((c • μ).restrict P) →L[ℝ]
            Lp ℝ 2 ((c • μ).restrict K),
        FiniteDimensional ℝ A.range ∧
            ∀ n : ℕ,
              dist ((hmemK_smul n).toLp (u n))
                (A ((hmemP_smul n).toLp (u n))) < ε := by
  have hmemP_smul' : ∀ n : ℕ, MemLp (u n) 2 (c • μ.restrict P) := by
    intro n
    simpa [Measure.restrict_smul] using hmemP_smul n
  have hmemK_smul' : ∀ n : ℕ, MemLp (u n) 2 (c • μ.restrict K) := by
    intro n
    simpa [Measure.restrict_smul] using hmemK_smul n
  apply finiteRankApproximationBetweenMeasures_of_measure_eq
      (hP := Measure.restrict_smul c μ P)
      (hK := Measure.restrict_smul c μ K)
      hmemP_smul hmemK_smul hmemP_smul' hmemK_smul'
  exact
    finiteRankApproximationBetweenMeasures_of_smul_measure
      (μP := μ.restrict P) (μK := μ.restrict K) (c := c) hc
      hmemP_smul' hmemK_smul' hmemP hmemK happrox

/--
%%handwave
name:
  Finite-rank smoothing is unchanged by rescaling the measure
statement:
  Multiplying the reference measure by a positive constant does not change
  the local finite-rank smoothing property.
proof:
  Positive scalar multiples have the same null sets, so they define the same
  measurable \(L^2\)-classes.  The \(L^2\) norms are all multiplied by the
  same positive square-root factor.  Transport the finite-rank operator
  through these canonical identity maps between the corresponding \(L^2\)
  spaces and choose the approximation tolerance after undoing this common
  scale factor.
-/
theorem EuclideanSmoothingFiniteRankApproxStatementForMeasure.of_smul_measure
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasurableSpace H]
    (μ : Measure H) {c : ℝ≥0} (hc : 0 < c)
    (hμ : EuclideanSmoothingFiniteRankApproxStatementForMeasure H μ) :
    EuclideanSmoothingFiniteRankApproxStatementForMeasure H (c • μ) := by
  intro K P hK hP hKP u hmemP hmemK hboundedP htranslationP ε hε
  have hc_ne : c ≠ 0 := ne_of_gt hc
  have hmemP_smul : ∀ n : ℕ, MemLp (u n) 2 (c • μ.restrict P) := by
    intro n
    simpa [Measure.restrict_smul] using hmemP n
  have hmemK_smul : ∀ n : ℕ, MemLp (u n) 2 (c • μ.restrict K) := by
    intro n
    simpa [Measure.restrict_smul] using hmemK n
  have hmemPμ : ∀ n : ℕ, MemLp (u n) 2 (μ.restrict P) := by
    intro n
    exact memLp_of_smul_measure_nnreal (μ := μ.restrict P) (c := c) hc_ne (hmemP_smul n)
  have hmemKμ : ∀ n : ℕ, MemLp (u n) 2 (μ.restrict K) := by
    intro n
    exact memLp_of_smul_measure_nnreal (μ := μ.restrict K) (c := c) hc_ne (hmemK_smul n)
  have hboundedP_smul :
      ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ n : ℕ,
        eLpNorm (u n) 2 (c • μ.restrict P) ≤ C := by
    simpa [Measure.restrict_smul] using hboundedP
  have hboundedPμ :
      ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ n : ℕ,
        eLpNorm (u n) 2 (μ.restrict P) ≤ C :=
    exists_eLpNorm_bound_of_smul_measure (μ := μ.restrict P) (c := c) hc_ne hboundedP_smul
  have htranslationPμ :
      EuclideanL2TranslationTightFamilyOnCompactForMeasure μ P u :=
    translationTightFamilyOnCompact_of_smul_measure (μ := μ) (c := c) hc_ne htranslationP
  have happrox :=
    hμ hK hP hKP u hmemPμ hmemKμ hboundedPμ htranslationPμ
  exact
    finiteRankApproximationOnNestedCompacts_of_smul_measure
      (μ := μ) (c := c) hc_ne hmemP hmemK hmemPμ hmemKμ happrox ε hε

/--
%%handwave
name:
  A linear equivalence maps compact sets to compact sets
statement:
  If \(e:H\to V\) is a continuous linear equivalence and \(K\subset H\) is
  compact, then \(e(K)\) is compact.
proof:
  Continuous images of compact sets are compact.
-/
private theorem isCompact_image_continuousLinearEquiv {H V : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (e : H ≃L[ℝ] V) {K : Set H} (hK : IsCompact K) :
    IsCompact (e '' K) :=
  hK.image e.continuous

/--
%%handwave
name:
  A linear equivalence preserves containment in an interior
statement:
  If \(K\subset\operatorname{int}P\) and \(e:H\to V\) is a continuous linear
  equivalence, then \(e(K)\subset\operatorname{int}(e(P))\).
proof:
  The underlying homeomorphism carries interiors to interiors; apply
  monotonicity of images to the original inclusion.
-/
private theorem image_subset_interior_image_continuousLinearEquiv {H V : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (e : H ≃L[ℝ] V) {K P : Set H} (hKP : K ⊆ interior P) :
    e '' K ⊆ interior (e '' P) := by
  change e.toHomeomorph '' K ⊆ interior (e.toHomeomorph '' P)
  rw [← e.toHomeomorph.image_interior P]
  exact Set.image_mono hKP

/--
%%handwave
name:
  Finite-rank smoothing is unchanged by linear coordinates
statement:
  Pulling the reference measure back through a continuous linear coordinate
  equivalence does not change the local finite-rank smoothing property.
proof:
  The equivalence carries compact containment to compact containment and
  identifies the restricted pulled-back measures with the corresponding
  restricted measures in coordinates.  The induced maps on \(L^2\) are
  linear isometries, and conjugating the finite-rank smoothing operator by
  these isometries preserves finite-dimensional range and the approximation
  estimates.
-/
theorem EuclideanSmoothingFiniteRankApproxStatementForMeasure.of_map_symm
    {H V : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) (e : H ≃L[ℝ] V)
    (hV : EuclideanSmoothingFiniteRankApproxStatementForMeasure V μ) :
    EuclideanSmoothingFiniteRankApproxStatementForMeasure H (μ.map e.symm) := by
  intro K P hK hP hKP u hmemP hmemK hboundedP htranslationP ε hε
  let em : H ≃ᵐ V := e.toHomeomorph.toMeasurableEquiv
  let K' : Set V := e '' K
  let P' : Set V := e '' P
  let v : ℕ → V → ℝ := fun n y ↦ u n (e.symm y)
  have hK' : IsCompact K' := by
    dsimp [K']
    exact isCompact_image_continuousLinearEquiv e hK
  have hP' : IsCompact P' := by
    dsimp [P']
    exact isCompact_image_continuousLinearEquiv e hP
  have hKP' : K' ⊆ interior P' := by
    dsimp [K', P']
    exact image_subset_interior_image_continuousLinearEquiv e hKP
  have hmp0 : MeasurePreserving em (μ.map e.symm) μ := by
    refine ⟨em.measurable, ?_⟩
    change (μ.map em.symm).map em = μ
    exact MeasurableEquiv.map_map_symm (e := em) (ν := μ)
  have hmpP :
      MeasurePreserving em ((μ.map e.symm).restrict P) (μ.restrict P') := by
    simpa [P', em] using hmp0.restrict_image_emb em.measurableEmbedding P
  have hmpK :
      MeasurePreserving em ((μ.map e.symm).restrict K) (μ.restrict K') := by
    simpa [K', em] using hmp0.restrict_image_emb em.measurableEmbedding K
  have hmpP_symm :
      MeasurePreserving em.symm (μ.restrict P') ((μ.map e.symm).restrict P) := by
    exact MeasurePreserving.symm em hmpP
  have hmpK_symm :
      MeasurePreserving em.symm (μ.restrict K') ((μ.map e.symm).restrict K) := by
    exact MeasurePreserving.symm em hmpK
  have hmemP' : ∀ n : ℕ, MemLp (v n) 2 (μ.restrict P') := by
    intro n
    simpa [v, em, Function.comp_def] using
      (hmemP n).comp_measurePreserving hmpP_symm
  have hmemK' : ∀ n : ℕ, MemLp (v n) 2 (μ.restrict K') := by
    intro n
    simpa [v, em, Function.comp_def] using
      (hmemK n).comp_measurePreserving hmpK_symm
  have hboundedP' :
      ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ n : ℕ,
        eLpNorm (v n) 2 (μ.restrict P') ≤ C := by
    rcases hboundedP with ⟨C, hCtop, hC⟩
    refine ⟨C, hCtop, fun n ↦ ?_⟩
    have hnorm :=
      eLpNorm_comp_measurePreserving (p := (2 : ℝ≥0∞))
        (g := u n) (μ := μ.restrict P')
        (ν := (μ.map e.symm).restrict P)
        (hmemP n).aestronglyMeasurable hmpP_symm
    calc
      eLpNorm (v n) 2 (μ.restrict P')
          = eLpNorm (u n) 2 ((μ.map e.symm).restrict P) := by
        simpa [v, em, Function.comp_def] using hnorm
      _ ≤ C := hC n
  have htranslationP' :
      EuclideanL2TranslationTightFamilyOnCompactForMeasure μ P' v := by
    intro η hη
    rcases htranslationP η hη with ⟨δ, hδ, hδ_translate⟩
    let L : V →L[ℝ] H := (e.symm : V →L[ℝ] H)
    let M : ℝ := ‖L‖ + 1
    have hM_pos : 0 < M := by
      dsimp [M]
      exact lt_of_le_of_lt (norm_nonneg L) (lt_add_one _)
    refine ⟨δ / M, div_pos hδ hM_pos, fun k hk n ↦ ?_⟩
    have hsmall : ‖e.symm k‖ < δ := by
      have hle : ‖e.symm k‖ ≤ ‖L‖ * ‖k‖ := by
        simpa [L] using L.le_opNorm k
      have hnorm_le_M : ‖L‖ ≤ M := by
        dsimp [M]
        linarith
      have hmul_le : ‖L‖ * ‖k‖ ≤ M * ‖k‖ :=
        mul_le_mul_of_nonneg_right hnorm_le_M (norm_nonneg k)
      have hMmul_lt : M * ‖k‖ < δ := by
        have hmul := mul_lt_mul_of_pos_left hk hM_pos
        have hcancel : M * (δ / M) = δ := by
          field_simp [ne_of_gt hM_pos]
        simpa [hcancel] using hmul
      exact hle.trans_lt (hmul_le.trans_lt hMmul_lt)
    let g : H → ℝ := fun z ↦ u n (z + e.symm k) - u n z
    have hnorm_map :
        eLpNorm g 2 ((μ.map e.symm).restrict P) =
          eLpNorm (g ∘ em.symm) 2 (μ.restrict P') := by
      have hmap :=
        em.symm.measurableEmbedding.eLpNorm_map_measure
          (μ := μ.restrict P') (g := g) (p := (2 : ℝ≥0∞))
      rw [hmpP_symm.map_eq] at hmap
      simpa using hmap
    calc
      eLpNorm (fun z ↦ v n (z + k) - v n z) 2 (μ.restrict P')
          = eLpNorm (g ∘ em.symm) 2 (μ.restrict P') := by
        congr 1
        funext z
        simp [g, v, em, map_add]
      _ = eLpNorm g 2 ((μ.map e.symm).restrict P) := hnorm_map.symm
      _ ≤ η := hδ_translate (e.symm k) hsmall n
  rcases hV hK' hP' hKP' v hmemP' hmemK' hboundedP'
      htranslationP' ε hε with
    ⟨A0, hA0fin, hA0approx⟩
  let inIso :
      Lp ℝ 2 ((μ.map e.symm).restrict P) →ₗᵢ[ℝ]
        Lp ℝ 2 (μ.restrict P') :=
    Lp.compMeasurePreservingₗᵢ (𝕜 := ℝ) (E := ℝ) (p := (2 : ℝ≥0∞))
      em.symm hmpP_symm
  let outIso :
      Lp ℝ 2 (μ.restrict K') →ₗᵢ[ℝ]
        Lp ℝ 2 ((μ.map e.symm).restrict K) :=
    Lp.compMeasurePreservingₗᵢ (𝕜 := ℝ) (E := ℝ) (p := (2 : ℝ≥0∞))
      em hmpK
  let Apre :
      Lp ℝ 2 ((μ.map e.symm).restrict P) →L[ℝ]
        Lp ℝ 2 (μ.restrict K') :=
    A0.comp inIso.toContinuousLinearMap
  let A :
      Lp ℝ 2 ((μ.map e.symm).restrict P) →L[ℝ]
        Lp ℝ 2 ((μ.map e.symm).restrict K) :=
    outIso.toContinuousLinearMap.comp Apre
  refine ⟨A, ?_, ?_⟩
  · letI : FiniteDimensional ℝ A0.range := hA0fin
    have hpre : FiniteDimensional ℝ Apre.range := by
      dsimp [Apre]
      exact finiteDimensional_range_comp_right A0 inIso.toContinuousLinearMap
    letI : FiniteDimensional ℝ Apre.range := hpre
    dsimp [A]
    exact finiteDimensional_range_comp_left outIso.toContinuousLinearMap Apre
  · intro n
    have hin :
        inIso.toContinuousLinearMap ((hmemP n).toLp (u n)) =
          (hmemP' n).toLp (v n) := by
      calc
        inIso.toContinuousLinearMap ((hmemP n).toLp (u n))
            =
          ((hmemP n).comp_measurePreserving hmpP_symm).toLp
            ((u n) ∘ em.symm) := by
          simpa [inIso] using
            Lp.toLp_compMeasurePreserving
              (E := ℝ) (p := (2 : ℝ≥0∞)) (hg := hmemP n) hmpP_symm
        _ = (hmemP' n).toLp (v n) := by
          apply MemLp.toLp_congr
          filter_upwards with z
          simp [v, em]
    have hout :
        outIso.toContinuousLinearMap ((hmemK' n).toLp (v n)) =
          (hmemK n).toLp (u n) := by
      calc
        outIso.toContinuousLinearMap ((hmemK' n).toLp (v n))
            =
          ((hmemK' n).comp_measurePreserving hmpK).toLp
            ((v n) ∘ em) := by
          simpa [outIso] using
            Lp.toLp_compMeasurePreserving
              (E := ℝ) (p := (2 : ℝ≥0∞)) (hg := hmemK' n) hmpK
        _ = (hmemK n).toLp (u n) := by
          apply MemLp.toLp_congr
          filter_upwards with z
          simp [v, em]
    calc
      dist ((hmemK n).toLp (u n)) (A ((hmemP n).toLp (u n)))
          =
        dist (outIso.toContinuousLinearMap ((hmemK' n).toLp (v n)))
          (outIso.toContinuousLinearMap
            (A0 ((hmemP' n).toLp (v n)))) := by
        rw [hout, ← hin]
        rfl
      _ =
        dist ((hmemK' n).toLp (v n))
          (A0 ((hmemP' n).toLp (v n))) := by
        simp [LinearIsometry.coe_toContinuousLinearMap,
          outIso.dist_map ((hmemK' n).toLp (v n))
            (A0 ((hmemP' n).toLp (v n)))]
      _ < ε := hA0approx n

/--
%%handwave
name:
  Transporting finite-rank smoothing through a scalar coordinate pullback
statement:
  The local finite-rank smoothing property is unchanged by a continuous linear
  coordinate equivalence and by multiplying the measure by a positive scalar.
proof:
  The coordinate equivalence gives measure-preserving maps between the
  pulled-back restricted measures.  Multiplying a measure by a positive
  scalar leaves null sets unchanged and rescales every \(L^2\) norm by the
  same positive factor.  Hence \(L^2\)-classes, translation estimates,
  finite-dimensional ranges, and finite-rank approximation inequalities
  transfer across the induced \(L^2\) equivalences.
-/
theorem EuclideanSmoothingFiniteRankApproxStatementForMeasure.of_smul_map_symm
    {H V : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) (e : H ≃L[ℝ] V) {c : ℝ≥0} (hc : 0 < c)
    (hV : EuclideanSmoothingFiniteRankApproxStatementForMeasure V μ) :
    EuclideanSmoothingFiniteRankApproxStatementForMeasure H
      (c • (μ.map e.symm)) := by
  have hsmul :
      EuclideanSmoothingFiniteRankApproxStatementForMeasure V (c • μ) :=
    EuclideanSmoothingFiniteRankApproxStatementForMeasure.of_smul_measure
      (H := V) μ hc hV
  have hmap :
      EuclideanSmoothingFiniteRankApproxStatementForMeasure H
        ((c • μ).map e.symm) :=
    EuclideanSmoothingFiniteRankApproxStatementForMeasure.of_map_symm
      (H := H) (V := V) (c • μ) e hsmul
  rw [Measure.map_smul] at hmap
  rw [EuclideanSmoothingFiniteRankApproxStatementForMeasure]
  exact hmap

/--
%%handwave
name:
  Transporting finite-rank smoothing through finite-dimensional coordinates
statement:
  If the local finite-rank smoothing property is known in every coordinate
  space \(\mathbb R^d\), then it holds in every finite-dimensional real
  normed space equipped with a Haar measure.
proof:
  Choose a continuous linear coordinate equivalence with \(\mathbb R^d\).
  The push-forward of a Haar measure under this equivalence is a positive
  scalar multiple of Lebesgue measure.  After the harmless scalar
  renormalization of the \(L^2\) norms, compact containment, translation
  tightness, finite-rank ranges, and the smoothing estimates transport
  through the induced \(L^2\) equivalences.
-/
theorem EuclideanSmoothingFiniteRankApproxStatement.of_finiteDimensionalHaar_of_pi
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    (hPi : ∀ d : ℕ,
      EuclideanSmoothingFiniteRankApproxStatement (Fin d → ℝ)) :
    EuclideanSmoothingFiniteRankApproxStatement H := by
  let d := Module.finrank ℝ H
  let V := Fin d → ℝ
  have hfinrank : Module.finrank ℝ H = Module.finrank ℝ V := by
    simp [V, d]
  let e : H ≃L[ℝ] V := ContinuousLinearEquiv.ofFinrankEq hfinrank
  let c : ℝ≥0 :=
    Measure.addHaarScalarFactor (volume : Measure H)
      ((volume : Measure V).map e.symm)
  have hc : 0 < c := by
    exact Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure
      (volume : Measure H) ((volume : Measure V).map e.symm)
  have hμ :
      (volume : Measure H) = c • ((volume : Measure V).map e.symm) := by
    exact Measure.isAddLeftInvariant_eq_smul
      (volume : Measure H) ((volume : Measure V).map e.symm)
  rw [EuclideanSmoothingFiniteRankApproxStatement, hμ]
  exact
    EuclideanSmoothingFiniteRankApproxStatementForMeasure.of_smul_map_symm
      (H := H) (V := V) (volume : Measure V) e hc (hPi d)

/--
%%handwave
name:
  Regular-cube finite-rank smoothing on nested finite-dimensional Euclidean compacts
statement:
  For scalar functions on a finite-dimensional real normed space, uniform
  \(L^2(P)\)-boundedness and uniform translation tightness on an outer compact
  \(P\) give finite-rank operators \(L^2(P)\to L^2(K)\) that uniformly
  approximate the restrictions to an inner compact \(K\).
proof:
  Choose linear coordinates identifying the finite-dimensional domain with
  \(\mathbb R^d\), apply the regular-cube result there, and transport the
  resulting finite-rank operator back through the induced \(L^2\) equivalences.
-/
theorem euclideanFrechetKolmogorov_smoothing_finiteRank_approx_L2_sequence
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {K P : Set H} (hK : IsCompact K) (hP : IsCompact P) (hKP : K ⊆ interior P)
    (u : ℕ → H → ℝ)
    (hmemP : ∀ n : ℕ, MemLp (u n) 2 (MeasureTheory.volume.restrict P))
    (hmemK : ∀ n : ℕ, MemLp (u n) 2 (MeasureTheory.volume.restrict K))
    (hboundedP : ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ n : ℕ,
      eLpNorm (u n) 2 (MeasureTheory.volume.restrict P) ≤ C)
    (htranslationP : EuclideanL2TranslationTightOnCompact P u) :
    ∀ ε : ℝ, 0 < ε →
      ∃ A :
          Lp ℝ 2 (MeasureTheory.volume.restrict P) →L[ℝ]
            Lp ℝ 2 (MeasureTheory.volume.restrict K),
        FiniteDimensional ℝ A.range ∧
          ∀ n : ℕ,
            dist ((hmemK n).toLp (u n))
              (A ((hmemP n).toLp (u n))) < ε := by
  exact
    (EuclideanSmoothingFiniteRankApproxStatement.of_finiteDimensionalHaar_of_pi
      (H := H)
      (fun d ↦ by
        intro K P hK hP hKP u hmemP hmemK hboundedP htranslationP
        exact
          euclideanPiFrechetKolmogorov_smoothing_finiteRank_approx_L2_sequence
            hK hP hKP u hmemP hmemK hboundedP htranslationP))
      hK hP hKP u hmemP hmemK hboundedP htranslationP

/--
%%handwave
name:
  Local regular-cube Frechet-Kolmogorov total boundedness
statement:
  If scalar functions are uniformly bounded and translation-tight in
  \(L^2\) on an outer compact \(P\), then their restrictions to a compact
  \(K\subset \operatorname{int} P\) form a totally bounded subset of
  \(L^2(K)\).
proof:
  Use the regular-cube finite-rank smoothing operators
  \(L^2(P)\to L^2(K)\).  The original sequence is bounded in \(L^2(P)\), so
  the finite-rank images lie in bounded subsets of finite-dimensional ranges.
  Finite-dimensional bounded sets are totally bounded, and the uniform
  smoothing error transfers finite nets to the restrictions on \(K\).
-/
theorem euclideanFrechetKolmogorov_localRegularCube_totallyBounded_L2_sequence_core
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {K P : Set H} (hK : IsCompact K) (hP : IsCompact P) (hKP : K ⊆ interior P)
    (u : ℕ → H → ℝ)
    (hmemP : ∀ n : ℕ, MemLp (u n) 2 (MeasureTheory.volume.restrict P))
    (hmemK : ∀ n : ℕ, MemLp (u n) 2 (MeasureTheory.volume.restrict K))
    (hboundedP : ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ n : ℕ,
      eLpNorm (u n) 2 (MeasureTheory.volume.restrict P) ≤ C)
    (htranslationP : EuclideanL2TranslationTightOnCompact P u) :
    TotallyBounded (Set.range fun n : ℕ ↦ (hmemK n).toLp (u n)) := by
  let xK : ℕ → Lp ℝ 2 (MeasureTheory.volume.restrict K) :=
    fun n ↦ (hmemK n).toLp (u n)
  let xP : ℕ → Lp ℝ 2 (MeasureTheory.volume.restrict P) :=
    fun n ↦ (hmemP n).toLp (u n)
  have hxPbounded : ∃ R : ℝ, 0 ≤ R ∧ ∀ n : ℕ, ‖xP n‖ ≤ R := by
    rcases hboundedP with ⟨C, hC_top, hC_bound⟩
    refine ⟨C.toReal, ENNReal.toReal_nonneg, fun n ↦ ?_⟩
    dsimp [xP]
    rw [Lp.norm_toLp]
    exact ENNReal.toReal_mono hC_top.ne (hC_bound n)
  have hxapprox :
      ∀ ε : ℝ, 0 < ε →
        ∃ A :
            Lp ℝ 2 (MeasureTheory.volume.restrict P) →L[ℝ]
              Lp ℝ 2 (MeasureTheory.volume.restrict K),
          FiniteDimensional ℝ A.range ∧
            ∀ n : ℕ, dist (xK n) (A (xP n)) < ε := by
    simpa [xK, xP] using
      euclideanFrechetKolmogorov_smoothing_finiteRank_approx_L2_sequence
        hK hP hKP u hmemP hmemK hboundedP htranslationP
  exact Metric.totallyBounded_iff.2
    (finite_L2_net_of_bounded_uniform_crossFiniteRank_approx xK xP hxPbounded hxapprox)

/--
%%handwave
name:
  Local regular-cube Kolmogorov-Riesz compact containment
statement:
  Under the local regular-cube Frechet-Kolmogorov hypotheses on nested
  compact sets \(K\subset\operatorname{int} P\), all restrictions of the
  sequence to \(K\) lie in one compact subset of \(L^2(K)\).
proof:
  The local regular-cube Frechet-Kolmogorov theorem gives total boundedness
  of the \(L^2(K)\)-classes.  The closure of a totally bounded set in the
  complete \(L^2\) space is compact and contains the sequence.
-/
theorem euclideanKolmogorovRiesz_localRegularCube_compact_containment
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {K P : Set H} (hK : IsCompact K) (hP : IsCompact P) (hKP : K ⊆ interior P)
    (u : ℕ → H → ℝ)
    (hmemP : ∀ n : ℕ, MemLp (u n) 2 (MeasureTheory.volume.restrict P))
    (hmemK : ∀ n : ℕ, MemLp (u n) 2 (MeasureTheory.volume.restrict K))
    (hboundedP : ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ n : ℕ,
      eLpNorm (u n) 2 (MeasureTheory.volume.restrict P) ≤ C)
    (htranslationP : EuclideanL2TranslationTightOnCompact P u) :
    ∃ S : Set (Lp ℝ 2 (MeasureTheory.volume.restrict K)),
      IsCompact S ∧ ∀ n : ℕ, (hmemK n).toLp (u n) ∈ S := by
  let x : ℕ → Lp ℝ 2 (MeasureTheory.volume.restrict K) :=
    fun n ↦ (hmemK n).toLp (u n)
  let S : Set (Lp ℝ 2 (MeasureTheory.volume.restrict K)) := closure (Set.range x)
  have hx_totallyBounded : TotallyBounded (Set.range x) := by
    simpa [x] using
      euclideanFrechetKolmogorov_localRegularCube_totallyBounded_L2_sequence_core
        hK hP hKP u hmemP hmemK hboundedP htranslationP
  have hS_totallyBounded : TotallyBounded S := by
    simpa [S] using hx_totallyBounded.closure
  have hS_compact : IsCompact S :=
    hS_totallyBounded.isCompact_of_isClosed (by simp [S])
  refine ⟨S, hS_compact, ?_⟩
  intro n
  exact subset_closure ⟨n, rfl⟩

/--
%%handwave
name:
  Local regular-cube Kolmogorov-Riesz subsequence compactness
statement:
  Under the local regular-cube Frechet-Kolmogorov hypotheses on nested
  compact sets \(K\subset\operatorname{int} P\), the sequence has a
  subsequence converging strongly in \(L^2(K)\).
proof:
  First place all \(L^2(K)\)-classes in one compact subset by the local
  regular-cube compact-containment theorem.  Then apply sequential
  compactness of compact subsets of \(L^2(K)\).
-/
theorem euclideanKolmogorovRiesz_localRegularCube_subsequence_on_compact
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {K P : Set H} (hK : IsCompact K) (hP : IsCompact P) (hKP : K ⊆ interior P)
    (u : ℕ → H → ℝ)
    (hmemP : ∀ n : ℕ, MemLp (u n) 2 (MeasureTheory.volume.restrict P))
    (hmemK : ∀ n : ℕ, MemLp (u n) 2 (MeasureTheory.volume.restrict K))
    (hboundedP : ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ n : ℕ,
      eLpNorm (u n) 2 (MeasureTheory.volume.restrict P) ≤ C)
    (htranslationP : EuclideanL2TranslationTightOnCompact P u) :
    ∃ (uLim : H → ℝ) (φ : ℕ → ℕ),
      StrictMono φ ∧
        TendstoInEuclideanLocalL2Scalar K (fun n z ↦ u (φ n) z) uLim := by
  rcases euclideanKolmogorovRiesz_localRegularCube_compact_containment
      hK hP hKP u hmemP hmemK hboundedP htranslationP with ⟨S, hS, hS_mem⟩
  exact euclideanL2CompactSet_subsequence_on_compact u hmemK S hS hS_mem

/--
%%handwave
name:
  Coordinate functional from a finite-dimensional Hilbert target
statement:
  A finite-dimensional Hilbert target has orthonormal coordinate functionals
  obtained from an orthonormal basis.
-/
noncomputable def euclideanTargetCoordinateMap (E : Type)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (i : Fin (Module.finrank ℝ E)) : E →L[ℝ] ℝ :=
  (EuclideanSpace.proj i).comp (stdOrthonormalBasis ℝ E).repr.toContinuousLinearMap

/--
%%handwave
name:
  Orthonormal coordinate functional
statement:
  The \(i\)-th coordinate functional sends \(v\) to its \(i\)-th coefficient
  in the standard orthonormal basis.
proof:
  This is the definition of the coordinate functional.
-/
@[simp]
theorem euclideanTargetCoordinateMap_apply {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (i : Fin (Module.finrank ℝ E)) (v : E) :
    euclideanTargetCoordinateMap E i v = (stdOrthonormalBasis ℝ E).repr v i := by
  rfl

/--
%%handwave
name:
  Norm bound for an orthonormal coordinate
statement:
  Every orthonormal coordinate satisfies \(|v_i|\le\lVert v\rVert\).
proof:
  A coordinate is bounded by the norm of the full coordinate vector.
-/
theorem euclideanTargetCoordinateMap_norm_le {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (i : Fin (Module.finrank ℝ E)) (v : E) :
    ‖euclideanTargetCoordinateMap E i v‖ ≤ ‖v‖ := by
  have h := PiLp.norm_apply_le ((stdOrthonormalBasis ℝ E).repr v) i
  simpa using h

/--
%%handwave
name:
  Reconstruction from \(L^2\) orthonormal target coordinates
statement:
  A finite-dimensional Hilbert-valued \(L^2\) class is reconstructed from its
  scalar orthonormal-coordinate \(L^2\) classes by summing the scalar classes
  times the corresponding basis vectors.
-/
noncomputable def euclideanTargetCoordinateReconstructionLp {H E : Type}
    [MeasurableSpace H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (μ : Measure H) :
    ((i : Fin (Module.finrank ℝ E)) → Lp ℝ 2 μ) →L[ℝ] Lp E 2 μ :=
  ∑ i : Fin (Module.finrank ℝ E),
    ((ContinuousLinearMap.toSpanSingleton ℝ (stdOrthonormalBasis ℝ E i)).compLpL
        (p := (2 : ℝ≥0∞)) μ).comp
      (ContinuousLinearMap.proj i)

/--
%%handwave
name:
  \(L^2\) reconstruction from the orthonormal coordinates of a function
statement:
  The \(L^2\)-class of an \(E\)-valued function is equal to the reconstruction
  of the \(L^2\)-classes of its scalar orthonormal coordinates.
proof:
  The reconstruction map is a finite sum.  Its \(i\)-th summand is almost
  everywhere the scalar coordinate multiplied by the \(i\)-th basis vector,
  and the finite pointwise sum is the usual orthonormal-basis expansion.
-/
theorem euclideanTargetCoordinateReconstructionLp_toLp {H E : Type}
    [MeasurableSpace H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (μ : Measure H) {f : H → E} (hf : MemLp f 2 μ) :
    euclideanTargetCoordinateReconstructionLp (H := H) (E := E) μ
        (fun i : Fin (Module.finrank ℝ E) ↦
          (((euclideanTargetCoordinateMap E i).comp_memLp' hf).toLp
            (fun x ↦ euclideanTargetCoordinateMap E i (f x)))) =
      hf.toLp f := by
  classical
  let b := stdOrthonormalBasis ℝ E
  let coordLp : Fin (Module.finrank ℝ E) → Lp ℝ 2 μ :=
    fun i ↦ (((euclideanTargetCoordinateMap E i).comp_memLp' hf).toLp
      (fun x ↦ euclideanTargetCoordinateMap E i (f x)))
  let termLp : Fin (Module.finrank ℝ E) → Lp E 2 μ :=
    fun i ↦
      ((ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLpL
        (p := (2 : ℝ≥0∞)) μ) (coordLp i)
  have hterm :
      ∀ i : Fin (Module.finrank ℝ E),
        (termLp i : H → E) =ᵐ[μ]
          fun x ↦ euclideanTargetCoordinateMap E i (f x) • b i := by
    intro i
    have hcomp :
        (termLp i : H → E) =ᵐ[μ]
          fun x ↦ (ContinuousLinearMap.toSpanSingleton ℝ (b i)) ((coordLp i : H → ℝ) x) := by
      simpa [termLp] using
        ((ContinuousLinearMap.toSpanSingleton ℝ (b i)).coeFn_compLpL
          (p := (2 : ℝ≥0∞)) (μ := μ) (coordLp i))
    have hcoord :
        (coordLp i : H → ℝ) =ᵐ[μ] fun x ↦ euclideanTargetCoordinateMap E i (f x) := by
      simpa [coordLp] using
        (((euclideanTargetCoordinateMap E i).comp_memLp' hf).coeFn_toLp)
    exact hcomp.trans <| hcoord.mono fun x hx ↦ by
      simp [hx]
  let lpFinsetSum : Finset (Fin (Module.finrank ℝ E)) → Lp E 2 μ :=
    fun s ↦ ∑ i ∈ s, (termLp i : Lp E 2 μ)
  have hsumCoe :
      ∀ s : Finset (Fin (Module.finrank ℝ E)),
        (lpFinsetSum s : H → E) =ᵐ[μ]
          (fun x ↦ ∑ i ∈ s, (termLp i : H → E) x) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simpa [lpFinsetSum] using (Lp.coeFn_zero E (2 : ℝ≥0∞) μ)
    · intro a s has ih
      simpa [lpFinsetSum, Finset.sum_insert, has, Pi.add_apply] using
        (Lp.coeFn_add (termLp a) (lpFinsetSum s)).trans
          (Filter.EventuallyEq.rfl.add ih)
  rw [Lp.ext_iff]
  have hreconLp :
      euclideanTargetCoordinateReconstructionLp (H := H) (E := E) μ coordLp =
        ∑ i : Fin (Module.finrank ℝ E), (termLp i : Lp E 2 μ) := by
    simp [euclideanTargetCoordinateReconstructionLp, termLp, coordLp, b,
      ContinuousLinearMap.sum_apply]
  have hleft :
      (euclideanTargetCoordinateReconstructionLp (H := H) (E := E) μ coordLp : H → E)
        =ᵐ[μ] fun x ↦ ∑ i : Fin (Module.finrank ℝ E), (termLp i : H → E) x := by
    rw [hreconLp]
    change (lpFinsetSum Finset.univ : H → E)
      =ᵐ[μ] fun x ↦ ∑ i : Fin (Module.finrank ℝ E), (termLp i : H → E) x
    simpa [lpFinsetSum] using hsumCoe Finset.univ
  have hcoords :
      (fun x ↦ ∑ i : Fin (Module.finrank ℝ E), (termLp i : H → E) x)
        =ᵐ[μ] fun x ↦ ∑ i : Fin (Module.finrank ℝ E),
          euclideanTargetCoordinateMap E i (f x) • b i := by
    filter_upwards [Filter.eventually_all.2 hterm] with x hx
    exact Finset.sum_congr rfl fun i _ ↦ hx i
  have hrecon :
      (fun x ↦ ∑ i : Fin (Module.finrank ℝ E),
          euclideanTargetCoordinateMap E i (f x) • b i)
        = fun x ↦ f x := by
    funext x
    simpa [b, euclideanTargetCoordinateMap] using
      (stdOrthonormalBasis ℝ E).sum_repr (f x)
  exact hleft.trans <| hcoords.trans <|
    (Filter.EventuallyEq.of_eq hrecon).trans hf.coeFn_toLp.symm

/--
%%handwave
name:
  Coordinate scalar function of a Hilbert-valued map
statement:
  Composing a Hilbert-valued map with an orthonormal coordinate functional
  gives a scalar function.
-/
noncomputable def euclideanTargetCoordinateFunction {H E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (i : Fin (Module.finrank ℝ E)) (u : H → E) : H → ℝ :=
  fun z ↦ euclideanTargetCoordinateMap E i (u z)

/--
%%handwave
name:
  Coordinate weak derivative field of a Hilbert-valued derivative
statement:
  Composing a Hilbert-valued weak derivative field with an orthonormal
  coordinate functional gives the corresponding scalar weak derivative field.
-/
noncomputable def euclideanTargetCoordinateDerivative {H E : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (i : Fin (Module.finrank ℝ E)) (du : H → H →L[ℝ] E) :
    H → H →L[ℝ] ℝ :=
  fun z ↦ (euclideanTargetCoordinateMap E i).comp (du z)

/--
%%handwave
name:
  Coordinate derivative of a vector-valued differential
statement:
  The \(i\)-th scalar coordinate derivative at \(z\) in direction \(v\) is
  the \(i\)-th orthonormal coordinate of \(du(z)v\).
proof:
  This is the definition of the coordinate derivative.
-/
@[simp]
theorem euclideanTargetCoordinateDerivative_apply {H E : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (i : Fin (Module.finrank ℝ E)) (du : H → H →L[ℝ] E)
    (z v : H) :
    euclideanTargetCoordinateDerivative i du z v =
      euclideanTargetCoordinateMap E i (du z v) := by
  rfl

/--
%%handwave
name:
  Norm bound for a scalar coordinate derivative
statement:
  If \(A:H\to E\) and \(\lambda_i\) is an orthonormal coordinate functional,
  then \(\lVert\lambda_i\circ A\rVert\le\lVert A\rVert\).
proof:
  The coordinate functional has norm at most one and operator norms are
  submultiplicative.
-/
theorem euclideanTargetCoordinateDerivative_norm_le {H E : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (i : Fin (Module.finrank ℝ E)) (A : H →L[ℝ] E) :
    ‖(euclideanTargetCoordinateMap E i).comp A‖ ≤ ‖A‖ := by
  let L : E →L[ℝ] ℝ := euclideanTargetCoordinateMap E i
  have hL_norm : ‖L‖ ≤ 1 := by
    refine L.opNorm_le_bound zero_le_one ?_
    intro v
    simpa [L, one_mul] using euclideanTargetCoordinateMap_norm_le i v
  calc
    ‖L.comp A‖ ≤ ‖L‖ * ‖A‖ := L.opNorm_comp_le A
    _ ≤ 1 * ‖A‖ := by
      exact mul_le_mul_of_nonneg_right hL_norm (norm_nonneg A)
    _ = ‖A‖ := one_mul ‖A‖

/--
%%handwave
name:
  Weak derivatives pass to Hilbert target coordinates
statement:
  If a Hilbert-valued map has a Euclidean weak derivative, then each
  orthonormal target coordinate has the corresponding scalar weak derivative.
proof:
  Apply the continuous coordinate functional to the vector-valued
  integration-by-parts identity and commute the functional with the Bochner
  integral.
-/
theorem euclideanWeakDerivative_coordinate {H E : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {Ω : Set H} {u : H → E} {du : H → H →L[ℝ] E}
    (i : Fin (Module.finrank ℝ E))
    (hweak : IsWeakDerivativeOnEuclideanRegionWithValues Ω u du) :
    IsWeakDerivativeOnEuclideanRegionScalar Ω
      (euclideanTargetCoordinateFunction i u)
      (euclideanTargetCoordinateDerivative i du) := by
  intro φ v
  rcases hweak φ v with ⟨h1, h2, hEq⟩
  let L : E →L[ℝ] ℝ := euclideanTargetCoordinateMap E i
  have h1L : Integrable (fun z ↦ L ((fderiv ℝ (φ : H → ℝ) z v) • u z))
      (MeasureTheory.volume.restrict Ω) := L.integrable_comp h1
  have h2L : Integrable (fun z ↦ L (φ z • du z v))
      (MeasureTheory.volume.restrict Ω) := L.integrable_comp h2
  refine ⟨?_, ?_, ?_⟩
  · simpa [euclideanTargetCoordinateFunction, L, map_smul] using h1L
  · simpa [euclideanTargetCoordinateDerivative, L, map_smul] using h2L
  · have hEqL :
        L (∫ z in Ω,
            (fderiv ℝ (φ : H → ℝ) z v) • u z ∂MeasureTheory.volume) =
          L (-∫ z in Ω, φ z • du z v ∂MeasureTheory.volume) := by
      simpa using congrArg L hEq
    have hInt1 := L.integral_comp_comm (μ := MeasureTheory.volume.restrict Ω) h1
    have hInt2 := L.integral_comp_comm (μ := MeasureTheory.volume.restrict Ω) h2
    have hInt2' :
        L (∫ z in Ω, φ z • du z v ∂MeasureTheory.volume) =
          ∫ z in Ω,
            φ z • euclideanTargetCoordinateDerivative i du z v ∂MeasureTheory.volume := by
      simpa [euclideanTargetCoordinateDerivative, L, map_smul] using hInt2.symm
    calc
      ∫ z in Ω,
          (fderiv ℝ (φ : H → ℝ) z v) •
            euclideanTargetCoordinateFunction i u z ∂MeasureTheory.volume
          = L (∫ z in Ω,
              (fderiv ℝ (φ : H → ℝ) z v) • u z ∂MeasureTheory.volume) := by
            simpa [euclideanTargetCoordinateFunction, L, map_smul] using hInt1
      _ = L (-∫ z in Ω, φ z • du z v ∂MeasureTheory.volume) := hEqL
      _ = -L (∫ z in Ω, φ z • du z v ∂MeasureTheory.volume) := by simp
      _ = -∫ z in Ω,
          φ z • euclideanTargetCoordinateDerivative i du z v ∂MeasureTheory.volume := by
            rw [hInt2']

/--
%%handwave
name:
  Sobolev bounds pass to Hilbert target coordinates
statement:
  A uniform Euclidean local \(W^{1,2}\) bound for Hilbert-valued maps gives a
  uniform Euclidean local \(W^{1,2}\) bound for each orthonormal target
  coordinate.
proof:
  Each orthonormal coordinate functional has operator norm at most one, so the
  scalar value and derivative norms are pointwise bounded by the
  Hilbert-valued value and derivative norms.
-/
theorem euclideanLocalSobolevBound_coordinate {H E : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {Q : Set H} {u : ℕ → H → E} {du : ℕ → H → H →L[ℝ] E}
    (i : Fin (Module.finrank ℝ E))
    (hbounded : BoundedInEuclideanLocalSobolevH1WithValues Q u du) :
    BoundedInEuclideanLocalSobolevH1Scalar Q
      (fun n ↦ euclideanTargetCoordinateFunction i (u n))
      (fun n ↦ euclideanTargetCoordinateDerivative i (du n)) := by
  rcases hbounded with ⟨C, hC_top, hC⟩
  refine ⟨C, hC_top, fun n ↦ ?_⟩
  rcases hC n with ⟨hu, hdu, hbound⟩
  let L : E →L[ℝ] ℝ := euclideanTargetCoordinateMap E i
  let Ld : (H →L[ℝ] E) →L[ℝ] H →L[ℝ] ℝ :=
    (ContinuousLinearMap.compL ℝ H E ℝ) L
  have hcu : MemLp (euclideanTargetCoordinateFunction i (u n))
      2 (MeasureTheory.volume.restrict Q) := by
    have h := L.comp_memLp' hu
    simpa [Function.comp_def, euclideanTargetCoordinateFunction, L] using h
  have hcdu : MemLp (euclideanTargetCoordinateDerivative i (du n))
      2 (MeasureTheory.volume.restrict Q) := by
    have h := Ld.comp_memLp' hdu
    simpa [Function.comp_def, euclideanTargetCoordinateDerivative, Ld, L,
      ContinuousLinearMap.compL_apply] using h
  refine ⟨hcu, hcdu, ?_⟩
  have hvalue :
      eLpNorm (euclideanTargetCoordinateFunction i (u n))
          2 (MeasureTheory.volume.restrict Q) ≤
        eLpNorm (u n) 2 (MeasureTheory.volume.restrict Q) := by
    exact eLpNorm_mono (fun z ↦ euclideanTargetCoordinateMap_norm_le i (u n z))
  have hdiff :
      eLpNorm (euclideanTargetCoordinateDerivative i (du n))
          2 (MeasureTheory.volume.restrict Q) ≤
        eLpNorm (du n) 2 (MeasureTheory.volume.restrict Q) := by
    exact eLpNorm_mono (fun z ↦
      euclideanTargetCoordinateDerivative_norm_le i (du n z))
  exact (add_le_add hvalue hdiff).trans hbound

/--
%%handwave
name:
  Intermediate compact set between a compact set and an open neighborhood
statement:
  In a finite-dimensional real normed space, if a compact set \(K\) lies in
  the interior of a set \(Q\), then there is a compact set \(P\) such that
  \(K\subset \operatorname{int} P\) and \(P\subset \operatorname{int} Q\).
proof:
  Since \(K\) is compact and contained in the open set
  \(\operatorname{int} Q\), choose a positive distance from \(K\) to the
  complement of \(\operatorname{int} Q\).  Take \(P\) to be a sufficiently
  small closed neighborhood of \(K\).  Finite-dimensional closed bounded sets
  are compact, and the distance choice gives both inclusions.
-/
theorem euclideanCompact_exists_compact_between_interior
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [FiniteDimensional ℝ H]
    {K Q : Set H} (hK : IsCompact K) (hKQ : K ⊆ interior Q) :
    ∃ P : Set H, IsCompact P ∧ K ⊆ interior P ∧ P ⊆ interior Q := by
  obtain ⟨P, hP_compact, _hP_closed, hKP, hPQ⟩ :=
    exists_compact_closed_between hK isOpen_interior hKQ
  exact ⟨P, hP_compact, hKP, hPQ⟩

/--
%%handwave
name:
  Scalar Euclidean Rellich compactness
statement:
  Let \(K\subset\operatorname{int} Q\subset Q\subset\Omega\), with \(K,Q\)
  compact and \(\Omega\) open in a finite-dimensional real normed space.  If
  \(u_n\) have weak derivatives \(du_n\) on \(\Omega\) and are uniformly
  bounded in \(W^{1,2}(Q)\), then a subsequence of \(u_n\) converges strongly
  in \(L^2(K)\).
proof:
  Choose an intermediate compact \(P\) with
  \(K\subset\operatorname{int}P\subset P\subset\operatorname{int}Q\).  The
  Sobolev bound on \(Q\) gives [translation tightness on \(P\)](lean:JJMath.Uniformization.scalarWeakSobolevBound_translation_tight_on_compact).
  Then apply [local regular-cube Kolmogorov--Riesz compactness](lean:JJMath.Uniformization.euclideanKolmogorovRiesz_localRegularCube_subsequence_on_compact)
  to the restrictions from \(P\) to \(K\).
-/
theorem scalarEuclideanRellichKondrachov_subsequence_on_compact
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {K Q Ω : Set H} (hK : IsCompact K) (hKQ : K ⊆ interior Q)
    (hQΩ : Q ⊆ Ω) (hQ : IsCompact Q) (hΩ_open : IsOpen Ω)
    (u : ℕ → H → ℝ) (du : ℕ → H → H →L[ℝ] ℝ)
    (hweak : ∀ n : ℕ, IsWeakDerivativeOnEuclideanRegionScalar Ω (u n) (du n))
    (hbounded : BoundedInEuclideanLocalSobolevH1Scalar Q u du) :
    ∃ (uLim : H → ℝ) (φ : ℕ → ℕ),
      StrictMono φ ∧
        TendstoInEuclideanLocalL2Scalar K (fun n z ↦ u (φ n) z) uLim := by
  rcases euclideanCompact_exists_compact_between_interior hK hKQ with
    ⟨P, hP, hKP, hPQ⟩
  have hPQ_set : P ⊆ Q := hPQ.trans interior_subset
  have hboundedP : BoundedInEuclideanLocalSobolevH1Scalar P u du :=
    BoundedInEuclideanLocalSobolevH1WithValues.mono_set hPQ_set hbounded
  have hvalue_memP :
      ∀ n : ℕ, MemLp (u n) 2 (MeasureTheory.volume.restrict P) := by
    intro n
    exact BoundedInEuclideanLocalSobolevH1WithValues.value_memLp hboundedP n
  have hvalue_boundP :
      ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ n : ℕ,
        eLpNorm (u n) 2 (MeasureTheory.volume.restrict P) ≤ C := by
    exact BoundedInEuclideanLocalSobolevH1WithValues.value_eLpNorm_bound hboundedP
  have hKP_set : K ⊆ P := hKP.trans interior_subset
  have hμKP :
      MeasureTheory.volume.restrict K ≤ MeasureTheory.volume.restrict P :=
    Measure.restrict_mono hKP_set le_rfl
  have hvalue_mem :
      ∀ n : ℕ, MemLp (u n) 2 (MeasureTheory.volume.restrict K) := by
    intro n
    exact (hvalue_memP n).mono_measure hμKP
  have htranslation :
      EuclideanL2TranslationTightOnCompact P u :=
    scalarWeakSobolevBound_translation_tight_on_compact
      hP hPQ hQΩ hQ hΩ_open u du hweak hbounded
  exact euclideanKolmogorovRiesz_localRegularCube_subsequence_on_compact
    hK hP hKP u hvalue_memP hvalue_mem hvalue_boundP htranslation

/--
%%handwave
name:
  Euclidean Rellich compactness for one target coordinate
statement:
  Under the scalar Rellich hypotheses \(K\subset\operatorname{int}Q\subset
  Q\subset\Omega\), let \(u_n:\Omega\to E\) be uniformly bounded in
  \(W^{1,2}(Q;E)\), with \(E\) finite-dimensional Hilbert.  For each
  orthonormal coordinate functional \(\ell_i:E\to\mathbb R\), the scalar
  sequence \(\ell_i\circ u_n\) has a subsequence converging strongly in
  \(L^2(K)\).
proof:
  Use [weak derivatives pass to target coordinates](lean:JJMath.Uniformization.euclideanWeakDerivative_coordinate)
  and [Sobolev bounds pass to target coordinates](lean:JJMath.Uniformization.euclideanLocalSobolevBound_coordinate),
  then apply [scalar Euclidean Rellich compactness](lean:JJMath.Uniformization.scalarEuclideanRellichKondrachov_subsequence_on_compact).
-/
theorem euclideanRellichKondrachov_coordinate_subsequence_on_compact
    {H E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ H] [FiniteDimensional ℝ E]
    {K Q Ω : Set H} (hK : IsCompact K) (hKQ : K ⊆ interior Q)
    (hQΩ : Q ⊆ Ω) (hQ : IsCompact Q) (hΩ_open : IsOpen Ω)
    (u : ℕ → H → E) (du : ℕ → H → H →L[ℝ] E)
    (hweak : ∀ n : ℕ, IsWeakDerivativeOnEuclideanRegionWithValues Ω (u n) (du n))
    (hbounded : BoundedInEuclideanLocalSobolevH1WithValues Q u du)
    (i : Fin (Module.finrank ℝ E)) :
    ∃ (uLim : H → ℝ) (φ : ℕ → ℕ),
      StrictMono φ ∧
        TendstoInEuclideanLocalL2Scalar K
          (fun n z ↦ euclideanTargetCoordinateFunction i (u (φ n)) z) uLim := by
  exact scalarEuclideanRellichKondrachov_subsequence_on_compact
    hK hKQ hQΩ hQ hΩ_open
    (fun n ↦ euclideanTargetCoordinateFunction i (u n))
    (fun n ↦ euclideanTargetCoordinateDerivative i (du n))
    (fun n ↦ euclideanWeakDerivative_coordinate i (hweak n))
    (euclideanLocalSobolevBound_coordinate i hbounded)

/--
%%handwave
name:
  Euclidean Rellich compact containment for finite-dimensional Hilbert targets
statement:
  Let \(K\subset\operatorname{int}Q\subset Q\subset\Omega\), with \(K,Q\)
  compact and \(\Omega\) open in a finite-dimensional real normed space.  If
  \(E\) is a finite-dimensional Hilbert space and \(u_n:\Omega\to E\) are
  uniformly bounded in \(W^{1,2}(Q;E)\), then their \(L^2(K;E)\)-classes lie
  in one compact subset of \(L^2(K;E)\).
proof:
  For each orthonormal coordinate \(\ell_i:E\to\mathbb R\), use that [the scalar coordinate classes lie in one compact subset of \(L^2(K)\)](lean:JJMath.Uniformization.euclideanKolmogorovRiesz_localRegularCube_compact_containment).
  The finite product of the coordinate compact sets is compact, and [the \(L^2\)-class is reconstructed from its scalar orthonormal coordinates](lean:JJMath.Uniformization.euclideanTargetCoordinateReconstructionLp_toLp).
  The continuous reconstruction map \((f_i)_i\mapsto\sum_i f_i e_i\) therefore
  sends the product compact set to a compact subset of \(L^2(K;E)\) containing
  the original sequence.
-/
theorem euclideanRellichKondrachov_compact_containment_on_compact
    {H E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ H] [FiniteDimensional ℝ E]
    {K Q Ω : Set H} (hK : IsCompact K) (hKQ : K ⊆ interior Q)
    (hQΩ : Q ⊆ Ω) (hQ : IsCompact Q) (hΩ_open : IsOpen Ω)
    (u : ℕ → H → E) (du : ℕ → H → H →L[ℝ] E)
    (hweak : ∀ n : ℕ, IsWeakDerivativeOnEuclideanRegionWithValues Ω (u n) (du n))
    (hbounded : BoundedInEuclideanLocalSobolevH1WithValues Q u du)
    (hmemK : ∀ n : ℕ, MemLp (u n) 2 (MeasureTheory.volume.restrict K)) :
    ∃ S : Set (Lp E 2 (MeasureTheory.volume.restrict K)),
      IsCompact S ∧ ∀ n : ℕ, (hmemK n).toLp (u n) ∈ S := by
  classical
  let μK : Measure H := MeasureTheory.volume.restrict K
  let ι := Fin (Module.finrank ℝ E)
  rcases euclideanCompact_exists_compact_between_interior hK hKQ with
    ⟨P, hP, hKP, hPQ⟩
  have hPQ_set : P ⊆ Q := hPQ.trans interior_subset
  let hmemKcoord :
      ∀ i : ι, ∀ n : ℕ,
        MemLp (euclideanTargetCoordinateFunction (H := H) i (u n))
          2 (MeasureTheory.volume.restrict K) := by
    intro i n
    simpa [ι, euclideanTargetCoordinateFunction] using
      ((euclideanTargetCoordinateMap E i).comp_memLp' (hmemK n))
  have hcoordCompact :
      ∀ i : ι,
        ∃ S : Set (Lp ℝ 2 μK),
          IsCompact S ∧
            ∀ n : ℕ,
              (hmemKcoord i n).toLp
                  (euclideanTargetCoordinateFunction i (u n)) ∈ S := by
    intro i
    have hbounded_i :
        BoundedInEuclideanLocalSobolevH1Scalar Q
          (fun n ↦ euclideanTargetCoordinateFunction i (u n))
          (fun n ↦ euclideanTargetCoordinateDerivative i (du n)) :=
      euclideanLocalSobolevBound_coordinate i hbounded
    have hboundedP_i :
        BoundedInEuclideanLocalSobolevH1Scalar P
          (fun n ↦ euclideanTargetCoordinateFunction i (u n))
          (fun n ↦ euclideanTargetCoordinateDerivative i (du n)) :=
      BoundedInEuclideanLocalSobolevH1WithValues.mono_set hPQ_set hbounded_i
    have hmemP_i :
        ∀ n : ℕ,
          MemLp (euclideanTargetCoordinateFunction i (u n))
            2 (MeasureTheory.volume.restrict P) := by
      intro n
      exact BoundedInEuclideanLocalSobolevH1WithValues.value_memLp hboundedP_i n
    have hboundP_i :
        ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ n : ℕ,
          eLpNorm (euclideanTargetCoordinateFunction i (u n))
            2 (MeasureTheory.volume.restrict P) ≤ C :=
      BoundedInEuclideanLocalSobolevH1WithValues.value_eLpNorm_bound hboundedP_i
    have htranslation_i :
        EuclideanL2TranslationTightOnCompact P
          (fun n ↦ euclideanTargetCoordinateFunction i (u n)) :=
      scalarWeakSobolevBound_translation_tight_on_compact
        hP hPQ hQΩ hQ hΩ_open
        (fun n ↦ euclideanTargetCoordinateFunction i (u n))
        (fun n ↦ euclideanTargetCoordinateDerivative i (du n))
        (fun n ↦ euclideanWeakDerivative_coordinate i (hweak n))
        hbounded_i
    simpa [μK] using
      euclideanKolmogorovRiesz_localRegularCube_compact_containment
        hK hP hKP
        (fun n ↦ euclideanTargetCoordinateFunction i (u n))
        hmemP_i (hmemKcoord i) hboundP_i htranslation_i
  choose Scoord hScoord hScoord_mem using hcoordCompact
  let T : Set ((i : ι) → Lp ℝ 2 μK) := Set.pi Set.univ Scoord
  have hT : IsCompact T := by
    exact isCompact_univ_pi hScoord
  let R : ((i : ι) → Lp ℝ 2 μK) →L[ℝ] Lp E 2 μK :=
    euclideanTargetCoordinateReconstructionLp (H := H) (E := E) μK
  let S : Set (Lp E 2 μK) := R '' T
  refine ⟨S, ?_, ?_⟩
  · exact hT.image R.continuous
  · intro n
    let ctuple : (i : ι) → Lp ℝ 2 μK :=
      fun i ↦ (hmemKcoord i n).toLp
        (euclideanTargetCoordinateFunction i (u n))
    have hctuple_mem : ctuple ∈ T := by
      intro i _hi
      exact hScoord_mem i n
    have hR_eq : R ctuple = (hmemK n).toLp (u n) := by
      simpa [R, ctuple, μK, ι, euclideanTargetCoordinateFunction] using
        euclideanTargetCoordinateReconstructionLp_toLp
          (H := H) (E := E) μK (hmemK n)
    exact ⟨ctuple, hctuple_mem, hR_eq⟩

/--
%%handwave
name:
  Euclidean Rellich compactness for finite-dimensional Hilbert targets
statement:
  Let \(K\subset\operatorname{int}Q\subset Q\subset\Omega\), with \(K,Q\)
  compact and \(\Omega\) open in a finite-dimensional real normed space.  If
  \(E\) is a finite-dimensional Hilbert space and \(u_n:\Omega\to E\) are
  uniformly bounded in \(W^{1,2}(Q;E)\), then a subsequence converges strongly
  in \(L^2(K;E)\).
proof:
  First put the \(L^2(K;E)\)-classes in one compact subset by [Euclidean Rellich compact containment for finite-dimensional Hilbert targets](lean:JJMath.Uniformization.euclideanRellichKondrachov_compact_containment_on_compact).
  Sequential compactness of that compact subset gives a strongly
  \(L^2(K;E)\)-convergent subsequence.
-/
theorem euclideanRellichKondrachov_subsequence_on_compact
    {H E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasureSpace H]
    [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ H] [FiniteDimensional ℝ E]
    {K Q Ω : Set H} (hK : IsCompact K) (hKQ : K ⊆ interior Q)
    (hQΩ : Q ⊆ Ω) (hQ : IsCompact Q) (hΩ_open : IsOpen Ω)
    (u : ℕ → H → E) (du : ℕ → H → H →L[ℝ] E)
    (hweak : ∀ n : ℕ, IsWeakDerivativeOnEuclideanRegionWithValues Ω (u n) (du n))
    (hbounded : BoundedInEuclideanLocalSobolevH1WithValues Q u du) :
    ∃ (uLim : H → E) (φ : ℕ → ℕ),
      StrictMono φ ∧
        TendstoInEuclideanLocalL2WithValues K (fun n z ↦ u (φ n) z) uLim := by
  have hKQ_set : K ⊆ Q := hKQ.trans interior_subset
  have hμKQ :
      MeasureTheory.volume.restrict K ≤ MeasureTheory.volume.restrict Q :=
    Measure.restrict_mono hKQ_set le_rfl
  have hmemK :
      ∀ n : ℕ, MemLp (u n) 2 (MeasureTheory.volume.restrict K) := by
    intro n
    exact (BoundedInEuclideanLocalSobolevH1WithValues.value_memLp hbounded n).mono_measure hμKQ
  rcases euclideanRellichKondrachov_compact_containment_on_compact
      hK hKQ hQΩ hQ hΩ_open u du hweak hbounded hmemK with
    ⟨S, hS, hS_mem⟩
  exact euclideanL2CompactSet_subsequence_on_compact_with_values u hmemK S hS hS_mem

/--
%%handwave
name:
  Compact containment from total boundedness in \(L^2\)
statement:
  If the \(L^2(K;E)\)-classes of a sequence form a totally bounded subset,
  then they all lie in one compact subset of \(L^2(K;E)\).
proof:
  Take the closure of the range.  The closure of a totally bounded subset of
  the complete \(L^2\) space is compact, and it contains the original range.
-/
theorem l2TotallyBoundedRange_compact_containment_on_set_with_values
    {X E : Type} [MeasurableSpace X] [NormedAddCommGroup E] [CompleteSpace E]
    {μ : Measure X} {K : Set X}
    (u : ℕ → X → E) (hmemK : ∀ n : ℕ, MemLp (u n) 2 (μ.restrict K))
    (htb : TotallyBounded (Set.range fun n : ℕ => (hmemK n).toLp (u n))) :
    ∃ S : Set (Lp E 2 (μ.restrict K)),
      IsCompact S ∧ ∀ n : ℕ, (hmemK n).toLp (u n) ∈ S := by
  let x : ℕ → Lp E 2 (μ.restrict K) := fun n ↦ (hmemK n).toLp (u n)
  let S : Set (Lp E 2 (μ.restrict K)) := closure (Set.range x)
  have hx_totallyBounded : TotallyBounded (Set.range x) := by
    simpa [x] using htb
  have hS_totallyBounded : TotallyBounded S := by
    simpa [S] using hx_totallyBounded.closure
  have hS_compact : IsCompact S :=
    hS_totallyBounded.isCompact_of_isClosed (by simp [S])
  refine ⟨S, hS_compact, ?_⟩
  intro n
  exact subset_closure ⟨n, rfl⟩

/--
%%handwave
name:
  Sequential Cauchy compactness gives total boundedness of a range
statement:
  If every subsequence of a family in a uniform space has a Cauchy
  subsubsequence, then the range of the family is totally bounded.
proof:
  Apply the sequential criterion for total boundedness.  A sequence taking
  values in the range is represented by a sequence of indices; the assumed
  Cauchy subsubsequence of those indices gives a Cauchy subsequence of the
  original sequence.
-/
theorem totallyBounded_range_of_forall_subsequence_cauchy
    {ι Y : Type} [UniformSpace Y] (x : ι → Y)
    (hseq : ∀ f : ℕ → ι,
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ CauchySeq (fun n : ℕ ↦ x (f (φ n)))) :
    TotallyBounded (Set.range x) := by
  refine totallyBounded_of_forall_seq_exists_cauchySeq_subseq ?_
  intro y hy
  choose f hf using hy
  rcases hseq f with ⟨φ, hφ, hφ_cauchy⟩
  refine ⟨φ, hφ, ?_⟩
  have hEq : y ∘ φ = fun n : ℕ ↦ x (f (φ n)) := by
    funext n
    exact (hf (φ n)).symm
  simpa [hEq] using hφ_cauchy

/--
%%handwave
name:
  Compact containment gives Cauchy subsubsequences
statement:
  If a sequence in a uniform space takes all its values in one compact set,
  then every selected subsequence has a Cauchy subsubsequence.
proof:
  Sequential compactness of the compact set gives a convergent subsubsequence,
  and every convergent sequence is Cauchy.
-/
theorem cauchy_subsequence_of_compact_containment
    {Y : Type} [UniformSpace Y] [FirstCountableTopology Y]
    (x : ℕ → Y) {S : Set Y} (hS : IsCompact S) (hx : ∀ n : ℕ, x n ∈ S)
    (f : ℕ → ℕ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ CauchySeq (fun n : ℕ ↦ x (f (φ n))) := by
  have hx_f : ∀ n : ℕ, x (f n) ∈ S := fun n ↦ hx (f n)
  rcases hS.tendsto_subseq hx_f with ⟨a, _ha, φ, hφ_mono, hφ_tendsto⟩
  refine ⟨φ, hφ_mono, ?_⟩
  have htendsto :
      Filter.Tendsto (fun n : ℕ ↦ x (f (φ n))) Filter.atTop (𝓝 a) := by
    simpa [Function.comp_def] using hφ_tendsto
  exact htendsto.cauchySeq

/--
%%handwave
name:
  Finite diagonal extraction for Cauchy subsequences
statement:
  Let finitely many sequences be assigned to every sequence of indices.  If,
  for each one of the finitely many components, every selected subsequence has
  a Cauchy subsubsequence, then every selected subsequence has a single
  subsubsequence which is Cauchy in all components at once.
proof:
  Induct over the finite set of components.  After extracting a subsequence
  which works for the previous components, extract once more for the new
  component.  Cauchyness of the old components is preserved when passing to a
  further strictly increasing subsequence.
-/
theorem finite_cauchy_subsequence_diagonal
    {ι : Type} [Fintype ι] {Y : ι → Type} [∀ i, UniformSpace (Y i)]
    (x : (i : ι) → ℕ → Y i)
    (hsubseq : ∀ i : ι, ∀ f : ℕ → ℕ,
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        CauchySeq (fun n : ℕ ↦ x i (f (φ n)))) :
    ∀ f : ℕ → ℕ,
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∀ i : ι, CauchySeq (fun n : ℕ ↦ x i (f (φ n))) := by
  classical
  have hfin :
      ∀ s : Finset ι, ∀ f : ℕ → ℕ,
        ∃ φ : ℕ → ℕ, StrictMono φ ∧
          ∀ i : ι, i ∈ s → CauchySeq (fun n : ℕ ↦ x i (f (φ n))) := by
    intro s
    refine Finset.induction_on s ?base ?step
    · intro f
      refine ⟨id, strictMono_id, ?_⟩
      intro i hi
      simp at hi
    · intro a s has ih f
      rcases ih f with ⟨ψ, hψ_mono, hψ_cauchy⟩
      rcases hsubseq a (f ∘ ψ) with ⟨θ, hθ_mono, hθ_cauchy⟩
      refine ⟨ψ ∘ θ, hψ_mono.comp hθ_mono, ?_⟩
      intro i hi
      rw [Finset.mem_insert] at hi
      rcases hi with rfl | hi
      · simpa [Function.comp_def] using hθ_cauchy
      · have hc : CauchySeq (fun n : ℕ ↦ x i (f (ψ n))) :=
          hψ_cauchy i hi
        have hθ_tendsto : Filter.Tendsto θ Filter.atTop Filter.atTop :=
          hθ_mono.tendsto_atTop
        simpa [Function.comp_def] using hc.comp_tendsto hθ_tendsto
  intro f
  rcases hfin Finset.univ f with ⟨φ, hφ_mono, hφ_cauchy⟩
  refine ⟨φ, hφ_mono, ?_⟩
  intro i
  exact hφ_cauchy i (Finset.mem_univ i)

/--
%%handwave
name:
  Finite metric controls preserve Cauchy sequences
statement:
  Suppose the distance between two terms of a sequence is bounded by a fixed
  nonnegative constant times the finite sum of distances between the
  corresponding terms of finitely many auxiliary sequences.  If all auxiliary sequences are
  Cauchy, then the original sequence is Cauchy.
proof:
  For each auxiliary sequence choose a tail bound \(b_i(N)\to 0\) which
  bounds all pairwise distances after the index \(N\).  The finite sum
  \(C\sum_i b_i(N)\) is nonnegative, tends to zero, and bounds the pairwise
  distances of the original sequence after \(N\).  The metric Cauchy criterion
  applies.
-/
theorem cauchySeq_of_finite_dist_control
    {ι Y : Type} [Fintype ι] [PseudoMetricSpace Y]
    {Z : ι → Type} [∀ i, PseudoMetricSpace (Z i)]
    (x : ℕ → Y) (z : (i : ι) → ℕ → Z i) {C : ℝ}
    (hC : 0 ≤ C)
    (hcontrol : ∀ m n : ℕ,
      dist (x m) (x n) ≤ C * ∑ i : ι, dist (z i m) (z i n))
    (hz : ∀ i : ι, CauchySeq (z i)) :
    CauchySeq x := by
  classical
  choose b hb_nonneg hb_bound hb_tendsto using
    fun i : ι ↦ cauchySeq_iff_le_tendsto_0.1 (hz i)
  refine cauchySeq_iff_le_tendsto_0.2
    ⟨fun N : ℕ ↦ C * ∑ i : ι, b i N, ?_, ?_, ?_⟩
  · intro N
    exact mul_nonneg hC (Finset.sum_nonneg fun i _hi ↦ hb_nonneg i N)
  · intro n m N hn hm
    calc
      dist (x n) (x m) ≤ C * ∑ i : ι, dist (z i n) (z i m) :=
        hcontrol n m
      _ ≤ C * ∑ i : ι, b i N := by
        exact mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun i _hi ↦ hb_bound i n m N hn hm) hC
  · have hsum :
        Filter.Tendsto (fun N : ℕ ↦ ∑ i : ι, b i N) Filter.atTop
          (𝓝 (∑ _i : ι, (0 : ℝ))) := by
      refine tendsto_finsetSum Finset.univ ?_
      intro i _hi
      exact hb_tendsto i
    have hsum_zero :
        Filter.Tendsto (fun N : ℕ ↦ ∑ i : ι, b i N) Filter.atTop (𝓝 (0 : ℝ)) := by
      simpa using hsum
    simpa using tendsto_const_nhds.mul hsum_zero

/--
%%handwave
name:
  Finite chartwise Cauchy extraction with metric control
statement:
  Let a sequence be controlled by finitely many chartwise sequences in the
  sense that its pairwise distance is bounded by a fixed nonnegative constant
  times the finite sum of the chartwise pairwise distances.  If every selected
  subsequence has, in each chart separately, a Cauchy subsubsequence, then
  every selected subsequence has a single subsubsequence which is Cauchy in
  the controlled space.
proof:
  First apply the finite diagonal extraction to get one subsequence which is
  Cauchy in all chartwise components.  Then apply the finite metric control
  lemma to the selected subsequence.
-/
theorem cauchy_subsequence_of_finite_chartwise_subsequence_and_dist_control
    {ι Y : Type} [Fintype ι] [PseudoMetricSpace Y]
    {Z : ι → Type} [∀ i, PseudoMetricSpace (Z i)]
    (x : ℕ → Y) (z : (i : ι) → ℕ → Z i)
    (hsubseq : ∀ i : ι, ∀ f : ℕ → ℕ,
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        CauchySeq (fun n : ℕ ↦ z i (f (φ n))))
    {C : ℝ}
    (hC : 0 ≤ C)
    (hcontrol : ∀ m n : ℕ,
      dist (x m) (x n) ≤ C * ∑ i : ι, dist (z i m) (z i n))
    (f : ℕ → ℕ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      CauchySeq (fun n : ℕ ↦ x (f (φ n))) := by
  classical
  rcases finite_cauchy_subsequence_diagonal z hsubseq f with
    ⟨φ, hφ_mono, hφ_cauchy⟩
  refine ⟨φ, hφ_mono, ?_⟩
  exact
    cauchySeq_of_finite_dist_control
      (x := fun n : ℕ ↦ x (f (φ n)))
      (z := fun i n ↦ z i (f (φ n)))
      hC
      (fun m n ↦ by
        simpa using hcontrol (f (φ m)) (f (φ n)))
      (fun i ↦ hφ_cauchy i)

/--
%%handwave
name:
  Compact sets admit finite compact chart covers inside a larger set
statement:
  In an \(R_1\) charted space, if a compact set \(K\) is contained in
  \(\operatorname{int}Q\), then \(K\) is a finite union of compact sets
  \(K_i\), each contained in the source of a chart and in
  \(\operatorname{int}Q\).
proof:
  The open sets \((\operatorname{source}\chi_x)\cap\operatorname{int}Q\),
  indexed by \(x\in K\), cover \(K\).  Compactness gives a finite subcover.
  The standard finite compact-cover lemma then shrinks this finite open cover
  to compact pieces whose union is \(K\).
-/
theorem compact_exists_finite_compact_chart_cover_inside
    {H X : Type} [TopologicalSpace H] [TopologicalSpace X] [R1Space X]
    [ChartedSpace H X]
    {K Q : Set X} (hK : IsCompact K) (hKQ : K ⊆ interior Q) :
    ∃ (ι : Type) (_ : Fintype ι) (c : ι → X) (Kc : ι → Set X),
      (∀ i : ι, IsCompact (Kc i)) ∧
        (∀ i : ι, Kc i ⊆ (chartAt H (c i)).source ∩ interior Q) ∧
        K = ⋃ i : ι, Kc i := by
  classical
  let U : X → Set X := fun x ↦ (chartAt H x).source ∩ interior Q
  have hU_open : ∀ x : X, IsOpen (U x) := by
    intro x
    exact (chartAt H x).open_source.inter isOpen_interior
  have hK_cover : K ⊆ ⋃ x : X, U x := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨x, mem_chart_source H x, hKQ hx⟩
  rcases hK.elim_finite_subcover U hU_open hK_cover with ⟨t, ht⟩
  rcases hK.finite_compact_cover t U (fun i _hi ↦ hU_open i) ht with
    ⟨Kpiece, hKpiece_compact, hKpiece_sub, hK_eq⟩
  let ι : Type := {x : X // x ∈ t}
  letI : Fintype ι := by
    dsimp [ι]
    infer_instance
  refine ⟨ι, inferInstance, (fun i : ι ↦ i.1), (fun i : ι ↦ Kpiece i.1), ?_, ?_, ?_⟩
  · intro i
    exact hKpiece_compact i.1
  · intro i
    simpa [U] using hKpiece_sub i.1
  · rw [hK_eq]
    ext x
    constructor
    · intro hx
      rw [Set.mem_iUnion] at hx
      rcases hx with ⟨y, hy⟩
      rw [Set.mem_iUnion] at hy
      rcases hy with ⟨hyt, hxy⟩
      rw [Set.mem_iUnion]
      exact ⟨⟨y, hyt⟩, hxy⟩
    · intro hx
      rw [Set.mem_iUnion] at hx
      rcases hx with ⟨i, hxi⟩
      rw [Set.mem_iUnion]
      refine ⟨(i : X), ?_⟩
      rw [Set.mem_iUnion]
      exact ⟨i.2, hxi⟩

/--
%%handwave
name:
  \(L^2\)-seminorm is subadditive under addition of measures
statement:
  For two measures \(\mu,\nu\), the \(L^2(\mu+\nu)\)-seminorm of a function is
  bounded by the sum of its \(L^2(\mu)\)- and \(L^2(\nu)\)-seminorms.
proof:
  Write the \(L^2\)-seminorm as the square root of
  \(\int\|f\|^2\).  The integral against \(\mu+\nu\) is the sum of the two
  integrals, and the square root is subadditive on \([0,\infty]\).
-/
theorem eLpNorm_two_add_measure_le
    {X E : Type} [MeasurableSpace X] [NormedAddCommGroup E]
    (f : X → E) (μ ν : Measure X) :
    eLpNorm f 2 (μ + ν) ≤ eLpNorm f 2 μ + eLpNorm f 2 ν := by
  have hp0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have hp_top : (2 : ℝ≥0∞) ≠ (∞ : ℝ≥0∞) := ENNReal.coe_ne_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top]
  simp only [ENNReal.toReal_ofNat, one_div]
  rw [lintegral_add_measure]
  exact ENNReal.rpow_add_le_add_rpow _ _ (by norm_num) (by norm_num)

/--
%%handwave
name:
  \(L^2\)-seminorm over a finite sum of measures
statement:
  The \(L^2\)-seminorm with respect to a finite sum of measures is bounded by
  the finite sum of the \(L^2\)-seminorms with respect to the summand
  measures.
proof:
  Induct over the finite set of measures, using subadditivity of the
  \(L^2\)-seminorm under addition of measures at each step.
-/
theorem eLpNorm_two_finset_sum_measure_le_sum
    {X E ι : Type} [MeasurableSpace X] [NormedAddCommGroup E]
    (s : Finset ι) (ν : ι → Measure X) (f : X → E) :
    eLpNorm f 2 (∑ i ∈ s, ν i) ≤ ∑ i ∈ s, eLpNorm f 2 (ν i) := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp
  · intro a s has ih
    rw [Finset.sum_insert has, Finset.sum_insert has]
    calc
      eLpNorm f 2 (ν a + ∑ x ∈ s, ν x)
          ≤ eLpNorm f 2 (ν a) + eLpNorm f 2 (∑ x ∈ s, ν x) :=
            eLpNorm_two_add_measure_le f (ν a) (∑ x ∈ s, ν x)
      _ ≤ eLpNorm f 2 (ν a) + ∑ x ∈ s, eLpNorm f 2 (ν x) :=
            add_le_add_right ih _

/--
%%handwave
name:
  \(L^2\)-seminorm on a finite cover is bounded by local seminorms
statement:
  If \(K=\bigcup_i K_i\) is a finite cover, then the \(L^2\)-seminorm of a
  function over \(K\) is bounded by the sum of its \(L^2\)-seminorms over the
  \(K_i\).
proof:
  The restricted measure on \(K\) is bounded by the finite sum of the
  restricted measures on the \(K_i\).  Expanding the \(L^2\)-seminorm as the
  square root of the integral of \(\|f\|^2\), the integral over \(K\) is
  bounded by the sum of the local integrals, and
  \(\sqrt{\sum_i a_i}\le\sum_i\sqrt{a_i}\).
-/
theorem eLpNorm_two_restrict_finite_iUnion_le_sum
    {X E : Type} [MeasurableSpace X] [NormedAddCommGroup E]
    {μ : Measure X} {K : Set X} {ι : Type} [Fintype ι]
    (Kc : ι → Set X) (hcover : K = ⋃ i : ι, Kc i) (f : X → E) :
    eLpNorm f 2 (μ.restrict K) ≤
      ∑ i : ι, eLpNorm f 2 (μ.restrict (Kc i)) := by
  rw [hcover]
  calc
    eLpNorm f 2 (μ.restrict (⋃ i : ι, Kc i))
        ≤ eLpNorm f 2 (Measure.sum fun i : ι ↦ μ.restrict (Kc i)) :=
          eLpNorm_mono_measure f Measure.restrict_iUnion_le
    _ = eLpNorm f 2 (∑ i : ι, μ.restrict (Kc i)) := by
          rw [Measure.sum_fintype]
    _ ≤ ∑ i : ι, eLpNorm f 2 (μ.restrict (Kc i)) := by
          simpa using
            eLpNorm_two_finset_sum_measure_le_sum
              (X := X) (E := E) (s := (Finset.univ : Finset ι))
              (ν := fun i : ι ↦ μ.restrict (Kc i)) f

/--
%%handwave
name:
  \(L^2\)-distance on a finite cover is bounded by local distances
statement:
  Let \(K=\bigcup_i K_i\) be a finite cover of a measurable space.  For any
  two \(L^2(K;E)\)-classes represented by functions \(u_m,u_n\), their
  \(L^2\)-distance over \(K\) is bounded by the sum of the corresponding
  \(L^2\)-distances over the sets \(K_i\).
proof:
  The restricted measure on \(K\) is bounded by the finite sum of the
  restricted measures on the \(K_i\).  The \(L^2\)-seminorm with respect to a
  finite sum of measures is bounded by the sum of the \(L^2\)-seminorms for
  the summands, giving the estimate after rewriting \(L^2\)-distance as the
  \(L^2\)-seminorm of the difference of representatives.
-/
theorem l2_dist_le_sum_dist_on_finite_cover
    {X E : Type} [MeasurableSpace X] [NormedAddCommGroup E]
    {μ : Measure X} {K : Set X} {ι : Type} [Fintype ι]
    (Kc : ι → Set X) (hcover : K = ⋃ i : ι, Kc i)
    (u : ℕ → X → E)
    (hmemK : ∀ n : ℕ, MemLp (u n) 2 (μ.restrict K))
    (hmemKc : ∀ i : ι, ∀ n : ℕ, MemLp (u n) 2 (μ.restrict (Kc i))) :
    ∀ m n : ℕ,
      dist ((hmemK m).toLp (u m)) ((hmemK n).toLp (u n)) ≤
        ∑ i : ι,
          dist ((hmemKc i m).toLp (u m)) ((hmemKc i n).toLp (u n)) := by
  intro m n
  let f : X → E := fun x ↦ u m x - u n x
  have hglobal_dist :
      dist ((hmemK m).toLp (u m)) ((hmemK n).toLp (u n)) =
        (eLpNorm f 2 (μ.restrict K)).toReal := by
    rw [Lp.dist_def]
    exact congrArg ENNReal.toReal
      (eLpNorm_congr_ae ((hmemK m).coeFn_toLp.sub (hmemK n).coeFn_toLp))
  have hlocal_dist :
      ∀ i : ι,
        dist ((hmemKc i m).toLp (u m)) ((hmemKc i n).toLp (u n)) =
          (eLpNorm f 2 (μ.restrict (Kc i))).toReal := by
    intro i
    rw [Lp.dist_def]
    exact congrArg ENNReal.toReal
      (eLpNorm_congr_ae ((hmemKc i m).coeFn_toLp.sub (hmemKc i n).coeFn_toLp))
  have hlocal_ne_top :
      ∀ i : ι, eLpNorm f 2 (μ.restrict (Kc i)) ≠ (∞ : ℝ≥0∞) := by
    intro i
    exact ((hmemKc i m).sub (hmemKc i n)).eLpNorm_lt_top.ne
  have hsum_ne_top :
      (∑ i : ι, eLpNorm f 2 (μ.restrict (Kc i))) ≠ (∞ : ℝ≥0∞) := by
    simpa using
      (ENNReal.sum_ne_top.2 (by
        intro i _hi
        exact hlocal_ne_top i :
        ∀ i ∈ (Finset.univ : Finset ι),
          eLpNorm f 2 (μ.restrict (Kc i)) ≠ (∞ : ℝ≥0∞)))
  have hsum_toReal :
      (∑ i : ι, eLpNorm f 2 (μ.restrict (Kc i))).toReal =
        ∑ i : ι, (eLpNorm f 2 (μ.restrict (Kc i))).toReal := by
    simpa using
      (ENNReal.toReal_sum
        (s := (Finset.univ : Finset ι))
        (f := fun i : ι ↦ eLpNorm f 2 (μ.restrict (Kc i)))
        (by
          intro i _hi
          exact hlocal_ne_top i))
  calc
    dist ((hmemK m).toLp (u m)) ((hmemK n).toLp (u n))
        = (eLpNorm f 2 (μ.restrict K)).toReal := hglobal_dist
    _ ≤ (∑ i : ι, eLpNorm f 2 (μ.restrict (Kc i))).toReal :=
        ENNReal.toReal_mono hsum_ne_top
          (eLpNorm_two_restrict_finite_iUnion_le_sum Kc hcover f)
    _ = ∑ i : ι, (eLpNorm f 2 (μ.restrict (Kc i))).toReal := hsum_toReal
    _ = ∑ i : ι,
          dist ((hmemKc i m).toLp (u m)) ((hmemKc i n).toLp (u n)) := by
        exact Finset.sum_congr rfl fun i _hi ↦ (hlocal_dist i).symm

/--
%%handwave
name:
  Compact chart pieces have compact Euclidean neighborhoods
statement:
  Let \(K_0\) be a compact subset contained in one chart source and in
  \(\operatorname{int}Q\).  In that chart, its coordinate image \(K'\) is
  compact and lies in the interior of a compact coordinate set \(Q'\) which
  is still over \(Q\).  The coordinate region over any open set \(U\) is
  open.
proof:
  The coordinate chart is continuous on its source, so the coordinate image
  of \(K_0\) is compact.  The image of
  \(\operatorname{source}\chi\cap\operatorname{int}Q\) is an open coordinate
  neighborhood contained in the coordinate region over \(Q\), so \(K'\) lies
  in the interior of that region.  Insert a compact set between \(K'\) and
  this open region by the finite-dimensional compact-neighborhood lemma.
  Openness of the region over \(U\) follows from continuity of the inverse
  chart on its target.
-/
theorem localRellich_compact_chart_piece_euclidean_geometry
    {H X : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [TopologicalSpace X] [ChartedSpace H X] [FiniteDimensional ℝ H]
    {K₀ Q U : Set X} (c : X)
    (hK₀_compact : IsCompact K₀)
    (hK₀_sub : K₀ ⊆ (chartAt H c).source ∩ interior Q)
    (hU_open : IsOpen U) :
    ∃ (K' Q' Ω : Set H),
      K' = (chartAt H c) '' K₀ ∧
        Ω = manifoldChartRegion (chartAt H c) U ∧
        IsCompact K' ∧
        K' ⊆ interior Q' ∧
        Q' ⊆ manifoldChartRegion (chartAt H c) Q ∧
        IsCompact Q' ∧
        IsOpen Ω := by
  classical
  let e : OpenPartialHomeomorph X H := chartAt H c
  let K' : Set H := e '' K₀
  have hK₀_source : K₀ ⊆ e.source := fun x hx ↦ (hK₀_sub hx).1
  have hK'_compact : IsCompact K' :=
    hK₀_compact.image_of_continuousOn (e.continuousOn.mono hK₀_source)
  have hK'_subset_chart_open :
      K' ⊆ e '' (e.source ∩ interior Q) := by
    intro z hz
    rcases hz with ⟨x, hxK, rfl⟩
    exact ⟨x, hK₀_sub hxK, rfl⟩
  have hchart_open : IsOpen (e '' (e.source ∩ interior Q)) := by
    rw [e.image_source_inter_eq']
    exact e.isOpen_inter_preimage_symm isOpen_interior
  have hchart_subset_region :
      e '' (e.source ∩ interior Q) ⊆ manifoldChartRegion e Q := by
    rw [e.image_source_inter_eq']
    intro z hz
    exact ⟨hz.1, show e.symm z ∈ Q from interior_subset hz.2⟩
  have hK'_region_interior : K' ⊆ interior (manifoldChartRegion e Q) := by
    exact hK'_subset_chart_open.trans
      ((hchart_open.subset_interior_iff).2 hchart_subset_region)
  rcases euclideanCompact_exists_compact_between_interior
      hK'_compact hK'_region_interior with
    ⟨Q', hQ'_compact, hK'Q', hQ'_region_int⟩
  let Ω : Set H := manifoldChartRegion e U
  have hΩ_open : IsOpen Ω := by
    dsimp [Ω, manifoldChartRegion]
    exact e.isOpen_inter_preimage_symm hU_open
  refine ⟨K', Q', Ω, rfl, rfl, hK'_compact, hK'Q', ?_, hQ'_compact, hΩ_open⟩
  exact hQ'_region_int.trans interior_subset

/--
%%handwave
name:
  Removing a positive density from an \(L^p\)-estimate
statement:
  Let \(c>0\) and suppose a density \(\delta\) satisfies
  \(c\le\delta\) almost everywhere on a measurable set \(K\).  If a function
  is \(L^p\) on \(K\) for the weighted measure \(\delta\,d\nu\), then it is
  \(L^p\) on \(K\) for \(\nu\).
proof:
  On \(K\), the measure \(\nu\) is bounded by
  \(c^{-1}(\delta\,d\nu)\).  \(L^p\)-membership is monotone under domination
  by a finite scalar multiple of the measure.
-/
theorem memLp_of_withDensity_lower_bound_on_restrict
    {α E : Type} [MeasurableSpace α] [TopologicalSpace E] [ContinuousENorm E]
    {ν : Measure α} {δ : α → ℝ≥0∞} {K : Set α} {c : ℝ≥0∞}
    (hK : MeasurableSet K) (hc0 : c ≠ 0) (hctop : c ≠ (⊤ : ℝ≥0∞))
    (hδ : ∀ᵐ x ∂ν.restrict K, c ≤ δ x)
    {f : α → E} {p : ℝ≥0∞}
    (hf : MemLp f p ((ν.withDensity δ).restrict K)) :
    MemLp f p (ν.restrict K) := by
  have hweighted_eq : (ν.withDensity δ).restrict K = (ν.restrict K).withDensity δ :=
    restrict_withDensity hK δ
  have hconst_le : c • ν.restrict K ≤ (ν.withDensity δ).restrict K := by
    rw [hweighted_eq, ← withDensity_const (μ := ν.restrict K) c]
    exact withDensity_mono hδ
  have hmeasure_le : ν.restrict K ≤ c⁻¹ • ((ν.withDensity δ).restrict K) := by
    calc
      ν.restrict K = (1 : ℝ≥0∞) • ν.restrict K := by simp
      _ = (c⁻¹ * c) • ν.restrict K := by
            rw [ENNReal.inv_mul_cancel hc0 hctop]
      _ = c⁻¹ • (c • ν.restrict K) := by rw [smul_smul]
      _ ≤ c⁻¹ • ((ν.withDensity δ).restrict K) := by
            apply Measure.le_iff.2
            intro s hs
            rw [Measure.smul_apply, Measure.smul_apply]
            exact mul_le_mul_right (Measure.le_iff.1 hconst_le s hs) _
  exact hf.of_measure_le_smul (by simpa [ENNReal.inv_ne_top] using hc0) hmeasure_le

/--
%%handwave
name:
  Removing a positive density from an \(L^2\)-seminorm
statement:
  Let \(c>0\) and suppose a density \(\delta\) satisfies
  \(c\le\delta\) almost everywhere on a measurable set \(K\).  Then the
  \(L^2\)-seminorm for the unweighted measure on \(K\) is bounded by a fixed
  multiple of the \(L^2\)-seminorm for the weighted measure
  \(\delta\,d\nu\).
proof:
  The measure \(\nu\!\restriction K\) is bounded by
  \(c^{-1}(\delta\,d\nu)\!\restriction K\).  Monotonicity of the
  \(L^2\)-seminorm under measure domination and the scaling rule for
  multiplying a measure by a constant give the stated estimate.
-/
theorem eLpNorm_two_of_withDensity_lower_bound_on_restrict_le
    {α E : Type} [MeasurableSpace α] [TopologicalSpace E] [ContinuousENorm E]
    {ν : Measure α} {δ : α → ℝ≥0∞} {K : Set α} {c : ℝ≥0∞}
    (hK : MeasurableSet K) (hc0 : c ≠ 0) (hctop : c ≠ (⊤ : ℝ≥0∞))
    (hδ : ∀ᵐ x ∂ν.restrict K, c ≤ δ x)
    (f : α → E) :
    eLpNorm f 2 (ν.restrict K) ≤
      c⁻¹ ^ ((1 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal *
        eLpNorm f 2 ((ν.withDensity δ).restrict K) := by
  have hweighted_eq : (ν.withDensity δ).restrict K = (ν.restrict K).withDensity δ :=
    restrict_withDensity hK δ
  have hconst_le : c • ν.restrict K ≤ (ν.withDensity δ).restrict K := by
    rw [hweighted_eq, ← withDensity_const (μ := ν.restrict K) c]
    exact withDensity_mono hδ
  have hmeasure_le : ν.restrict K ≤ c⁻¹ • ((ν.withDensity δ).restrict K) := by
    calc
      ν.restrict K = (1 : ℝ≥0∞) • ν.restrict K := by simp
      _ = (c⁻¹ * c) • ν.restrict K := by
            rw [ENNReal.inv_mul_cancel hc0 hctop]
      _ = c⁻¹ • (c • ν.restrict K) := by rw [smul_smul]
      _ ≤ c⁻¹ • ((ν.withDensity δ).restrict K) := by
            apply Measure.le_iff.2
            intro s hs
            rw [Measure.smul_apply, Measure.smul_apply]
            exact mul_le_mul_right (Measure.le_iff.1 hconst_le s hs) _
  calc
    eLpNorm f 2 (ν.restrict K) ≤
        eLpNorm f 2 (c⁻¹ • ((ν.withDensity δ).restrict K)) :=
      eLpNorm_mono_measure f hmeasure_le
    _ = c⁻¹ ^ ((1 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal *
        eLpNorm f 2 ((ν.withDensity δ).restrict K) := by
          rw [eLpNorm_smul_measure_of_ne_zero]
          · rfl
          · exact ENNReal.inv_ne_zero.2 hctop

/--
%%handwave
name:
  Adding a bounded density to an \(L^2\)-seminorm
statement:
  Let \(c>0\) and suppose a density \(\delta\) satisfies
  \(\delta\le c\) almost everywhere on a measurable set \(K\).  Then the
  \(L^2\)-seminorm for the weighted measure \(\delta\,d\nu\) on \(K\) is
  bounded by a fixed multiple of the unweighted \(L^2\)-seminorm on \(K\).
proof:
  The weighted restricted measure is dominated by \(c(\nu\!\restriction K)\).
  Monotonicity of the \(L^2\)-seminorm under measure domination and the
  scaling rule for multiplying a measure by a constant give the estimate.
-/
theorem eLpNorm_two_withDensity_upper_bound_on_restrict_le
    {α E : Type} [MeasurableSpace α] [TopologicalSpace E] [ContinuousENorm E]
    {ν : Measure α} {δ : α → ℝ≥0∞} {K : Set α} {c : ℝ≥0∞}
    (hK : MeasurableSet K) (hc0 : c ≠ 0)
    (hδ : ∀ᵐ x ∂ν.restrict K, δ x ≤ c)
    (f : α → E) :
    eLpNorm f 2 ((ν.withDensity δ).restrict K) ≤
      c ^ ((1 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal *
        eLpNorm f 2 (ν.restrict K) := by
  have hweighted_eq : (ν.withDensity δ).restrict K = (ν.restrict K).withDensity δ :=
    restrict_withDensity hK δ
  have hmeasure_le : (ν.withDensity δ).restrict K ≤ c • ν.restrict K := by
    rw [hweighted_eq, ← withDensity_const (μ := ν.restrict K) c]
    exact withDensity_mono hδ
  calc
    eLpNorm f 2 ((ν.withDensity δ).restrict K) ≤
        eLpNorm f 2 (c • ν.restrict K) :=
      eLpNorm_mono_measure f hmeasure_le
    _ = c ^ ((1 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal *
        eLpNorm f 2 (ν.restrict K) := by
          rw [eLpNorm_smul_measure_of_ne_zero]
          · rfl
          · exact hc0

/--
%%handwave
name:
  Chart pullbacks preserve \(L^2\)-membership on compact pieces
statement:
  Let \(K_0\) be a compact set contained in a chart source and let
  \(K'=\chi(K_0)\).  If \(u\in L^2(K_0,\mu)\), then
  \(u\circ\chi^{-1}\in L^2(K',dx)\), where \(dx\) is Haar measure in
  coordinates and \(\mu\) is a smooth positive measure.
proof:
  In coordinates, the push-forward of \(\mu\) has a continuous positive
  density with respect to Haar measure.  On the compact coordinate image
  this density is bounded below by a positive constant, so \(L^2\)-integrable
  functions for \(\mu\) remain \(L^2\)-integrable after pulling back to
  Haar measure.
-/
theorem localRellich_chartPullback_memLp_on_compact_of_memLp
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [IsIdentityManifoldModel H I] [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := I) X E)]
    [TopologicalSpace.PseudoMetrizableSpace
      (ManifoldDifferentialTotalSpace (I := I) X E)]
    {μ : Measure X} (hμ : SmoothPositiveMeasureOnManifold (I := I) μ)
    {K₀ : Set X} {K' : Set H} (c : X)
    (hK₀_compact : IsCompact K₀)
    (hK₀_source : K₀ ⊆ (chartAt H c).source)
    (hK'_def : K' = (chartAt H c) '' K₀)
    {u : X → E} (hu : MemLp u 2 (μ.restrict K₀)) :
    MemLp (fun z : H ↦ u ((chartAt H c).symm z)) 2
      (MeasureTheory.volume.restrict K') := by
  classical
  let e : OpenPartialHomeomorph X H := chartAt H c
  have he : e ∈ atlas H X := chart_mem_atlas H c
  have hK'_eq : K' = e '' K₀ := by
    simpa [e] using hK'_def
  have hK'_target : K' ⊆ e.target := by
    rw [hK'_eq]
    intro z hz
    rcases hz with ⟨x, hxK, rfl⟩
    exact e.map_source (hK₀_source hxK)
  have hK'_compact : IsCompact K' := by
    rw [hK'_eq]
    exact hK₀_compact.image_of_continuousOn (e.continuousOn.mono hK₀_source)
  have hK'_meas : MeasurableSet K' := hK'_compact.measurableSet
  rcases hμ.chart_density e he with ⟨ρ, hρ_smooth, hρ_pos, hmap⟩
  let ν : Measure H := MeasureTheory.volume.restrict e.target
  let δ : H → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (ρ z)
  rcases K'.eq_empty_or_nonempty with hK'_empty | hK'_nonempty
  · have hzero : MeasureTheory.volume.restrict K' = 0 := by
      simp [hK'_empty]
    rw [hzero]
    exact memLp_measure_zero
  have hρ_cont_K' : ContinuousOn ρ K' :=
    hρ_smooth.continuousOn.mono hK'_target
  rcases hK'_compact.exists_sInf_image_eq_and_le hK'_nonempty hρ_cont_K' with
    ⟨z₀, hz₀K', _hz₀_inf, hz₀_min⟩
  let c₀ : ℝ≥0∞ := ENNReal.ofReal (ρ z₀)
  have hc₀_pos : 0 < ρ z₀ := hρ_pos z₀ (hK'_target hz₀K')
  have hc₀_ne_zero : c₀ ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hc₀_pos)
  have hc₀_ne_top : c₀ ≠ (⊤ : ℝ≥0∞) := by
    simp [c₀]
  have hδ_lower : ∀ᵐ z ∂ν.restrict K', c₀ ≤ δ z := by
    filter_upwards [ae_restrict_mem hK'_meas] with z hzK'
    exact ENNReal.ofReal_le_ofReal (hz₀_min z hzK')
  let μsK : Measure X := (μ.restrict e.source).restrict (e ⁻¹' K')
  let Fpull : H → E := fun z ↦ u (e.symm z)
  have hpre_ae : e ⁻¹' K' =ᵐ[μ.restrict e.source] K₀ := by
    filter_upwards [ae_restrict_mem e.open_source.measurableSet] with x hx_source
    apply propext
    constructor
    · intro hxK'
      rw [hK'_eq] at hxK'
      rcases hxK' with ⟨y, hyK₀, hyx⟩
      have hy_source : y ∈ e.source := hK₀_source hyK₀
      have hy_eq_x : y = x := e.injOn hy_source hx_source hyx
      simpa [hy_eq_x] using hyK₀
    · intro hxK₀
      rw [hK'_eq]
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
  have hsymm_big :
      AEMeasurable e.symm (Measure.map e (μ.restrict e.source)) := by
    have hsymm_vol :
        AEMeasurable e.symm (MeasureTheory.volume.restrict e.target) :=
      openPartialHomeomorph_symm_aemeasurable_restrict_target e MeasureTheory.volume
    have h_ac :
        Measure.map e (μ.restrict e.source) ≪
          MeasureTheory.volume.restrict e.target := by
      rw [hmap]
      exact withDensity_absolutelyContinuous _ _
    exact hsymm_vol.mono_ac h_ac
  have hmap_μsK_le :
      Measure.map e μsK ≤ Measure.map e (μ.restrict e.source) :=
    Measure.map_mono_of_aemeasurable (by
      dsimp [μsK]
      exact Measure.restrict_le_self) he_aemeas_source
  have hsymm_aemeas : AEMeasurable e.symm (Measure.map e μsK) :=
    hsymm_big.mono_measure hmap_μsK_le
  have hmap_symm : Measure.map e.symm (Measure.map e μsK) = μsK := by
    have hmap_comp :
        Measure.map e.symm (Measure.map e μsK) =
          Measure.map (fun x : X ↦ e.symm (e x)) μsK := by
      simpa [Function.comp_def] using
        (AEMeasurable.map_map_of_aemeasurable hsymm_aemeas he_aemeas_μsK)
    have hleft :
        (fun x : X ↦ e.symm (e x)) =ᵐ[μsK] fun x ↦ x := by
      have hsource_ae : ∀ᵐ x ∂μsK, x ∈ e.source := by
        dsimp [μsK]
        exact ae_restrict_of_ae (ae_restrict_mem e.open_source.measurableSet)
      exact hsource_ae.mono fun x hx_source ↦ e.left_inv hx_source
    calc
      Measure.map e.symm (Measure.map e μsK)
          = Measure.map (fun x : X ↦ e.symm (e x)) μsK := hmap_comp
      _ = Measure.map (fun x : X ↦ x) μsK := Measure.map_congr hleft
      _ = μsK := by rw [Measure.map_id']
  have hu_μsK : MemLp u 2 μsK := by
    simpa [hμsK_eq] using hu
  have hu_aestr_map_symm :
      AEStronglyMeasurable u (Measure.map e.symm (Measure.map e μsK)) := by
    simpa [hmap_symm] using hu_μsK.aestronglyMeasurable
  have hFpull_aestr :
      AEStronglyMeasurable Fpull (Measure.map e μsK) := by
    simpa [Fpull, Function.comp_def] using
      hu_aestr_map_symm.comp_aemeasurable hsymm_aemeas
  have hcomp_eq :
      (fun x : X ↦ Fpull (e x)) =ᵐ[μsK] u := by
    have hsource_ae : ∀ᵐ x ∂μsK, x ∈ e.source := by
      dsimp [μsK]
      exact ae_restrict_of_ae (ae_restrict_mem e.open_source.measurableSet)
    exact hsource_ae.mono fun x hx_source ↦ by
      simp [Fpull, e.left_inv hx_source]
  have hcomp_mem : MemLp (fun x : X ↦ Fpull (e x)) 2 μsK :=
    (memLp_congr_ae hcomp_eq).2 hu_μsK
  have hF_map : MemLp Fpull 2 (Measure.map e μsK) :=
    (memLp_map_measure_iff hFpull_aestr he_aemeas_μsK).2 hcomp_mem
  have hmap_restrict :
      (Measure.map e (μ.restrict e.source)).restrict K' = Measure.map e μsK := by
    dsimp [μsK]
    exact Measure.restrict_map_of_aemeasurable he_aemeas_source hK'_meas
  have hweighted_eq :
      (ν.withDensity δ).restrict K' = Measure.map e μsK := by
    calc
      (ν.withDensity δ).restrict K'
          = (Measure.map e (μ.restrict e.source)).restrict K' := by
              simpa [ν, δ] using congrArg (fun m : Measure H ↦ m.restrict K') hmap.symm
      _ = Measure.map e μsK := hmap_restrict
  have hF_weighted_K' : MemLp Fpull 2 ((ν.withDensity δ).restrict K') := by
    simpa [hweighted_eq] using hF_map
  have hF_νK' : MemLp Fpull 2 (ν.restrict K') :=
    memLp_of_withDensity_lower_bound_on_restrict
      (ν := ν) (δ := δ) (K := K') (c := c₀)
      hK'_meas hc₀_ne_zero hc₀_ne_top hδ_lower hF_weighted_K'
  simpa [Fpull, ν, Measure.restrict_restrict_of_subset hK'_target] using hF_νK'

/--
%%handwave
name:
  Chart pullbacks are bounded on compact \(L^2\) pieces
statement:
  Let \(K_0\) be a compact set contained in a chart source and let
  \(K'=\chi(K_0)\).  For a smooth positive measure \(\mu\), the coordinate
  \(L^2(K',dx)\)-seminorm of \(u\circ\chi^{-1}\) is bounded by a finite
  constant times the intrinsic \(L^2(K_0,\mu)\)-seminorm of \(u\).
proof:
  In coordinates, the push-forward of \(\mu\) is a positive smooth density
  times Haar measure.  On the compact coordinate image this density has a
  positive lower bound.  Removing the density therefore costs only a fixed
  finite multiplicative constant, while the chart change of variables
  identifies the weighted coordinate seminorm with the intrinsic seminorm on
  \(K_0\).
-/
theorem localRellich_chartPullback_eLpNorm_two_le_on_compact
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [IsIdentityManifoldModel H I] [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {μ : Measure X} (hμ : SmoothPositiveMeasureOnManifold (I := I) μ)
    {K₀ : Set X} {K' : Set H} (c : X)
    (hK₀_compact : IsCompact K₀)
    (hK₀_source : K₀ ⊆ (chartAt H c).source)
    (hK'_def : K' = (chartAt H c) '' K₀) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ u : X → E, MemLp u 2 (μ.restrict K₀) →
        eLpNorm (fun z : H ↦ u ((chartAt H c).symm z)) 2
            (MeasureTheory.volume.restrict K') ≤
          C * eLpNorm u 2 (μ.restrict K₀) := by
  classical
  let e : OpenPartialHomeomorph X H := chartAt H c
  have he : e ∈ atlas H X := chart_mem_atlas H c
  have hK'_eq : K' = e '' K₀ := by
    simpa [e] using hK'_def
  have hK'_target : K' ⊆ e.target := by
    rw [hK'_eq]
    intro z hz
    rcases hz with ⟨x, hxK, rfl⟩
    exact e.map_source (hK₀_source hxK)
  have hK'_compact : IsCompact K' := by
    rw [hK'_eq]
    exact hK₀_compact.image_of_continuousOn (e.continuousOn.mono hK₀_source)
  have hK'_meas : MeasurableSet K' := hK'_compact.measurableSet
  rcases hμ.chart_density e he with ⟨ρ, hρ_smooth, hρ_pos, hmap⟩
  let ν : Measure H := MeasureTheory.volume.restrict e.target
  let δ : H → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (ρ z)
  rcases K'.eq_empty_or_nonempty with hK'_empty | hK'_nonempty
  · refine ⟨0, by simp, ?_⟩
    intro u hu
    have hzero : MeasureTheory.volume.restrict K' = 0 := by
      simp [hK'_empty]
    simp [hzero]
  have hρ_cont_K' : ContinuousOn ρ K' :=
    hρ_smooth.continuousOn.mono hK'_target
  rcases hK'_compact.exists_sInf_image_eq_and_le hK'_nonempty hρ_cont_K' with
    ⟨z₀, hz₀K', _hz₀_inf, hz₀_min⟩
  let c₀ : ℝ≥0∞ := ENNReal.ofReal (ρ z₀)
  let q : ℝ := ((1 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal
  let C₀ : ℝ≥0∞ := c₀⁻¹ ^ q
  have hc₀_pos : 0 < ρ z₀ := hρ_pos z₀ (hK'_target hz₀K')
  have hc₀_ne_zero : c₀ ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hc₀_pos)
  have hc₀_ne_top : c₀ ≠ (⊤ : ℝ≥0∞) := by
    simp [c₀]
  have hδ_lower : ∀ᵐ z ∂ν.restrict K', c₀ ≤ δ z := by
    filter_upwards [ae_restrict_mem hK'_meas] with z hzK'
    exact ENNReal.ofReal_le_ofReal (hz₀_min z hzK')
  have hq_nonneg : 0 ≤ q := by
    norm_num [q]
  have hC₀_top : C₀ < ⊤ := by
    exact ENNReal.rpow_lt_top_of_nonneg hq_nonneg
      (by simpa using (ENNReal.inv_ne_top.2 hc₀_ne_zero))
  refine ⟨C₀, hC₀_top, ?_⟩
  intro u hu
  let μsK : Measure X := (μ.restrict e.source).restrict (e ⁻¹' K')
  let Fpull : H → E := fun z ↦ u (e.symm z)
  have hpre_ae : e ⁻¹' K' =ᵐ[μ.restrict e.source] K₀ := by
    filter_upwards [ae_restrict_mem e.open_source.measurableSet] with x hx_source
    apply propext
    constructor
    · intro hxK'
      rw [hK'_eq] at hxK'
      rcases hxK' with ⟨y, hyK₀, hyx⟩
      have hy_source : y ∈ e.source := hK₀_source hyK₀
      have hy_eq_x : y = x := e.injOn hy_source hx_source hyx
      simpa [hy_eq_x] using hyK₀
    · intro hxK₀
      rw [hK'_eq]
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
  have hsymm_big :
      AEMeasurable e.symm (Measure.map e (μ.restrict e.source)) := by
    have hsymm_vol :
        AEMeasurable e.symm (MeasureTheory.volume.restrict e.target) :=
      openPartialHomeomorph_symm_aemeasurable_restrict_target e MeasureTheory.volume
    have h_ac :
        Measure.map e (μ.restrict e.source) ≪
          MeasureTheory.volume.restrict e.target := by
      rw [hmap]
      exact withDensity_absolutelyContinuous _ _
    exact hsymm_vol.mono_ac h_ac
  have hmap_μsK_le :
      Measure.map e μsK ≤ Measure.map e (μ.restrict e.source) :=
    Measure.map_mono_of_aemeasurable (by
      dsimp [μsK]
      exact Measure.restrict_le_self) he_aemeas_source
  have hsymm_aemeas : AEMeasurable e.symm (Measure.map e μsK) :=
    hsymm_big.mono_measure hmap_μsK_le
  have hmap_symm : Measure.map e.symm (Measure.map e μsK) = μsK := by
    have hmap_comp :
        Measure.map e.symm (Measure.map e μsK) =
          Measure.map (fun x : X ↦ e.symm (e x)) μsK := by
      simpa [Function.comp_def] using
        (AEMeasurable.map_map_of_aemeasurable hsymm_aemeas he_aemeas_μsK)
    have hleft :
        (fun x : X ↦ e.symm (e x)) =ᵐ[μsK] fun x ↦ x := by
      have hsource_ae : ∀ᵐ x ∂μsK, x ∈ e.source := by
        dsimp [μsK]
        exact ae_restrict_of_ae (ae_restrict_mem e.open_source.measurableSet)
      exact hsource_ae.mono fun x hx_source ↦ e.left_inv hx_source
    calc
      Measure.map e.symm (Measure.map e μsK)
          = Measure.map (fun x : X ↦ e.symm (e x)) μsK := hmap_comp
      _ = Measure.map (fun x : X ↦ x) μsK := Measure.map_congr hleft
      _ = μsK := by rw [Measure.map_id']
  have hu_μsK : MemLp u 2 μsK := by
    simpa [hμsK_eq] using hu
  have hu_aestr_map_symm :
      AEStronglyMeasurable u (Measure.map e.symm (Measure.map e μsK)) := by
    simpa [hmap_symm] using hu_μsK.aestronglyMeasurable
  have hFpull_aestr :
      AEStronglyMeasurable Fpull (Measure.map e μsK) := by
    simpa [Fpull, Function.comp_def] using
      hu_aestr_map_symm.comp_aemeasurable hsymm_aemeas
  have hcomp_eq :
      (fun x : X ↦ Fpull (e x)) =ᵐ[μsK] u := by
    have hsource_ae : ∀ᵐ x ∂μsK, x ∈ e.source := by
      dsimp [μsK]
      exact ae_restrict_of_ae (ae_restrict_mem e.open_source.measurableSet)
    exact hsource_ae.mono fun x hx_source ↦ by
      simp [Fpull, e.left_inv hx_source]
  have hmap_restrict :
      (Measure.map e (μ.restrict e.source)).restrict K' = Measure.map e μsK := by
    dsimp [μsK]
    exact Measure.restrict_map_of_aemeasurable he_aemeas_source hK'_meas
  have hweighted_eq :
      (ν.withDensity δ).restrict K' = Measure.map e μsK := by
    calc
      (ν.withDensity δ).restrict K'
          = (Measure.map e (μ.restrict e.source)).restrict K' := by
              simpa [ν, δ] using congrArg (fun m : Measure H ↦ m.restrict K') hmap.symm
      _ = Measure.map e μsK := hmap_restrict
  have hweighted_norm :
      eLpNorm Fpull 2 ((ν.withDensity δ).restrict K') =
        eLpNorm u 2 (μ.restrict K₀) := by
    calc
      eLpNorm Fpull 2 ((ν.withDensity δ).restrict K')
          = eLpNorm Fpull 2 (Measure.map e μsK) := by rw [hweighted_eq]
      _ = eLpNorm (fun x : X ↦ Fpull (e x)) 2 μsK := by
            exact eLpNorm_map_measure hFpull_aestr he_aemeas_μsK
      _ = eLpNorm u 2 μsK := eLpNorm_congr_ae hcomp_eq
      _ = eLpNorm u 2 (μ.restrict K₀) := by rw [hμsK_eq]
  have hνK'_eq : ν.restrict K' = MeasureTheory.volume.restrict K' := by
    simpa [ν] using
      Measure.restrict_restrict_of_subset (μ := MeasureTheory.volume) hK'_target
  have hcompare :
      eLpNorm Fpull 2 (ν.restrict K') ≤
        C₀ * eLpNorm Fpull 2 ((ν.withDensity δ).restrict K') := by
    simpa [C₀, q] using
      eLpNorm_two_of_withDensity_lower_bound_on_restrict_le
        (ν := ν) (δ := δ) (K := K') (c := c₀)
        hK'_meas hc₀_ne_zero hc₀_ne_top hδ_lower Fpull
  calc
    eLpNorm (fun z : H ↦ u ((chartAt H c).symm z)) 2
        (MeasureTheory.volume.restrict K')
        = eLpNorm Fpull 2 (ν.restrict K') := by
            simp [Fpull, e, hνK'_eq]
    _ ≤ C₀ * eLpNorm Fpull 2 ((ν.withDensity δ).restrict K') := hcompare
    _ = C₀ * eLpNorm u 2 (μ.restrict K₀) := by rw [hweighted_norm]

/--
%%handwave
name:
  \(L^2\)-seminorm from a bounded square integral
statement:
  If \(f\in L^2(\mu)\) and \(\int\|f\|^2\,d\mu\le C\), then the
  \(L^2\)-seminorm of \(f\) is bounded by \(\sqrt C\).
proof:
  The \(L^2\)-seminorm is the square root of the extended nonnegative
  integral of \(\|f\|^2\).  Integrability identifies this extended integral
  with the nonnegative real integral, and the claimed estimate follows by
  monotonicity of the square root.
-/
theorem eLpNorm_two_le_of_integral_sq_le
    {α E : Type} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {f : α → E} {C : ℝ}
    (hf : MemLp f 2 μ) (hC : ∫ x, ‖f x‖ ^ 2 ∂μ ≤ C) :
    eLpNorm f 2 μ ≤
      ENNReal.ofReal C ^ ((1 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal := by
  have hp0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have hptop : (2 : ℝ≥0∞) ≠ (∞ : ℝ≥0∞) := ENNReal.coe_ne_top
  have h_int : Integrable (fun x ↦ ‖f x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).1 hf
  have h_nonneg : 0 ≤ᵐ[μ] fun x ↦ ‖f x‖ ^ 2 :=
    Filter.Eventually.of_forall fun x ↦ sq_nonneg _
  have h_lint_eq :
      ENNReal.ofReal (∫ x, ‖f x‖ ^ 2 ∂μ) =
        ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ :=
    ofReal_integral_eq_lintegral_ofReal h_int h_nonneg
  have h_lint_le : (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ≤ ENNReal.ofReal C := by
    calc
      (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ)
          = ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ := by
              simp
      _ = ENNReal.ofReal (∫ x, ‖f x‖ ^ 2 ∂μ) := h_lint_eq.symm
      _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal hC
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop]
  have hpow :
      (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) ≤
        ENNReal.ofReal C ^ (1 / (2 : ℝ)) :=
    ENNReal.rpow_le_rpow h_lint_le (by norm_num)
  simpa [ENNReal.toReal_ofNat] using hpow

/--
%%handwave
name:
  A finite basis identifies operators with their basis values
statement:
  If \(H\) is finite-dimensional, a continuous linear map \(A:H\to E\) is
  continuously and linearly equivalent to the finite family
  \((A e_i)_i\) of its values on a fixed basis of \(H\).
proof:
  The inverse sends a family \((y_i)\) to the linear map determined by
  \(e_i\mapsto y_i\).  Since the domain is finite-dimensional, this linear
  map is continuous.  The two maps are inverse by the universal property of a
  basis.
-/
noncomputable def continuousLinearMapFiniteBasisEvalEquiv
    (H E : Type) [NormedAddCommGroup H] [NormedSpace ℝ H]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    (H →L[ℝ] E) ≃L[ℝ] (Fin (Module.finrank ℝ H) → E) := by
  classical
  let ι := Fin (Module.finrank ℝ H)
  let b : Module.Basis ι ℝ H := Module.finBasis ℝ H
  let eLin : (H →L[ℝ] E) ≃ₗ[ℝ] (ι → E) :=
    { toFun := fun A i ↦ A (b i)
      invFun := fun y ↦
        { toLinearMap := b.constr ℝ y
          cont := (b.constr ℝ y).continuous_of_finiteDimensional }
      map_add' := by
        intro A B
        ext i
        simp
      map_smul' := by
        intro c A
        ext i
        simp
      left_inv := by
        intro A
        ext v
        change (b.constr ℝ (fun i ↦ A.toLinearMap (b i))) v = A.toLinearMap v
        rw [b.constr_self]
      right_inv := by
        intro y
        ext i
        change (b.constr ℝ y) (b i) = y i
        exact b.constr_basis ℝ y i }
  exact eLin.toContinuousLinearEquiv

/--
%%handwave
name:
  Finite-basis evaluation of a continuous linear map
statement:
  Under \(\mathcal L(H,E)\cong\prod_iE\), the \(i\)-th component of \(A\) is
  \(A(e_i)\).
proof:
  Unfold the evaluation equivalence on the chosen finite basis.
-/
@[simp]
theorem continuousLinearMapFiniteBasisEvalEquiv_apply
    {H E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (A : H →L[ℝ] E) (i : Fin (Module.finrank ℝ H)) :
    continuousLinearMapFiniteBasisEvalEquiv H E A i =
      A (Module.finBasis ℝ H i) := by
  simp [continuousLinearMapFiniteBasisEvalEquiv]

/--
%%handwave
name:
  Operator-valued \(L^2\) bounds from basis-direction bounds
statement:
  Let \(H\) be finite-dimensional.  If an operator-valued field
  \(F:\alpha\to\mathcal L(H,E)\) has all basis-direction evaluations
  \(F(\cdot)e_i\) in \(L^2\), and each of these \(L^2\)-seminorms is bounded
  by \(B\), then \(F\) is \(L^2\) and its \(L^2\)-seminorm is bounded by a
  finite constant times \(B\).
proof:
  Use the continuous linear equivalence
  \(A\mapsto(Ae_i)_i\).  The coordinate field is \(L^2\) because each
  coordinate is \(L^2\).  Applying the inverse continuous linear map gives
  \(L^2\)-membership of \(F\).  The triangle inequality bounds the coordinate
  \(L^2\)-seminorm by the finite sum of the coordinate seminorms.
-/
theorem continuousLinearMap_memLp_and_eLpNorm_le_of_basis_eval_bound
    {α H E : Type} [MeasurableSpace α]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {μ : Measure α} {F : α → H →L[ℝ] E} {B : ℝ≥0∞}
    (_hB_top : B < ⊤)
    (h_eval : ∀ i : Fin (Module.finrank ℝ H),
      MemLp (fun x ↦ F x (Module.finBasis ℝ H i)) 2 μ ∧
        eLpNorm (fun x ↦ F x (Module.finBasis ℝ H i)) 2 μ ≤ B) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      MemLp F 2 μ ∧ eLpNorm F 2 μ ≤ C * B := by
  classical
  let ι := Fin (Module.finrank ℝ H)
  let T := continuousLinearMapFiniteBasisEvalEquiv H E
  let coord : α → ι → E := fun x i ↦ F x (Module.finBasis ℝ H i)
  have hcoord_mem : MemLp coord 2 μ := by
    apply MemLp.of_eval
    intro i
    exact (h_eval i).1
  let L : (ι → E) →L[ℝ] (H →L[ℝ] E) := (T.symm : (ι → E) →L[ℝ] H →L[ℝ] E)
  have hLF_mem : MemLp (fun x ↦ L (coord x)) 2 μ :=
    L.comp_memLp' hcoord_mem
  have hLF_eq : (fun x ↦ L (coord x)) = F := by
    funext x
    have hcoord_eq : coord x = T (F x) := by
      ext i
      simp [coord, T]
    simp [L, hcoord_eq]
  have hF_mem : MemLp F 2 μ := by
    simpa [hLF_eq] using hLF_mem
  have hcoord_sum :
      coord = fun x ↦ ∑ i : ι, Pi.single i (coord x i) := by
    funext x i
    simp
  have hsingle_mem : ∀ i : ι,
      MemLp (fun x ↦ Pi.single i (coord x i) : α → ι → E) 2 μ := by
    intro i
    apply MemLp.of_eval
    intro j
    by_cases hji : j = i
    · subst j
      simpa using (h_eval i).1
    · have hzero :
          (fun x ↦ (Pi.single i (coord x i) : ι → E) j) =
            fun _x : α ↦ (0 : E) := by
        funext x
        simp [Pi.single, hji]
      simpa [hzero] using
        (memLp_zero : MemLp (fun _x : α ↦ (0 : E)) 2 μ)
  have hcoord_eLp_le_sum :
      eLpNorm coord 2 μ ≤
        ∑ i : ι, eLpNorm (fun x ↦ Pi.single i (coord x i) : α → ι → E) 2 μ := by
    have hcoord_sum_ae :
        coord =ᵐ[μ] fun x : α ↦ ∑ i : ι, (Pi.single i (coord x i) : ι → E) :=
      Filter.Eventually.of_forall fun x ↦ by
        ext j
        simp
    have hfun_sum :
        (∑ i : ι, fun x : α ↦ (Pi.single i (coord x i) : ι → E)) =
          fun x : α ↦ ∑ i : ι, (Pi.single i (coord x i) : ι → E) := by
      ext x j
      simp
    calc
      eLpNorm coord 2 μ =
          eLpNorm (fun x : α ↦ ∑ i : ι, (Pi.single i (coord x i) : ι → E)) 2 μ := by
            exact eLpNorm_congr_ae hcoord_sum_ae
      _ = eLpNorm (∑ i : ι, fun x : α ↦ (Pi.single i (coord x i) : ι → E)) 2 μ := by
            rw [hfun_sum]
      _ ≤ ∑ i : ι, eLpNorm (fun x ↦ Pi.single i (coord x i) : α → ι → E) 2 μ := by
            simpa using
              (eLpNorm_sum_le
                (μ := μ) (p := (2 : ℝ≥0∞))
                (f := fun i x ↦ (Pi.single i (coord x i) : ι → E))
                (s := Finset.univ)
                (fun i _ ↦ (hsingle_mem i).aestronglyMeasurable)
                (by norm_num : (1 : ℝ≥0∞) ≤ 2))
  have hsingle_eLp_eq : ∀ i : ι,
      eLpNorm (fun x ↦ Pi.single i (coord x i) : α → ι → E) 2 μ =
        eLpNorm (fun x ↦ coord x i) 2 μ := by
    intro i
    exact eLpNorm_congr_enorm_ae <| Filter.Eventually.of_forall fun x ↦ by
      rw [Pi.enorm_single]
  have hcoord_eLp_le :
      eLpNorm coord 2 μ ≤ (Fintype.card ι : ℝ≥0∞) * B := by
    calc
      eLpNorm coord 2 μ ≤
          ∑ i : ι, eLpNorm (fun x ↦ Pi.single i (coord x i) : α → ι → E) 2 μ :=
        hcoord_eLp_le_sum
      _ = ∑ i : ι, eLpNorm (fun x ↦ coord x i) 2 μ := by
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [hsingle_eLp_eq i]
      _ ≤ ∑ _i : ι, B := by
        refine Finset.sum_le_sum ?_
        intro i _
        exact (h_eval i).2
      _ = (Fintype.card ι : ℝ≥0∞) * B := by
        simp
  have hF_eLp_le_coord :
      eLpNorm F 2 μ ≤ ENNReal.ofReal ‖L‖ * eLpNorm coord 2 μ := by
    calc
      eLpNorm F 2 μ = eLpNorm (fun x ↦ L (coord x)) 2 μ := by
        rw [← hLF_eq]
      _ ≤ ENNReal.ofReal ‖L‖ * eLpNorm coord 2 μ := by
        exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul
          (Filter.Eventually.of_forall fun x ↦ L.le_opNorm (coord x)) 2
  let C : ℝ≥0∞ := ENNReal.ofReal ‖L‖ * (Fintype.card ι : ℝ≥0∞)
  have hC_top : C < ⊤ := by
    exact ENNReal.mul_lt_top (by simp) (by simp)
  refine ⟨C, hC_top, hF_mem, ?_⟩
  calc
    eLpNorm F 2 μ ≤ ENNReal.ofReal ‖L‖ * eLpNorm coord 2 μ := hF_eLp_le_coord
    _ ≤ ENNReal.ofReal ‖L‖ * ((Fintype.card ι : ℝ≥0∞) * B) :=
      mul_le_mul_right hcoord_eLp_le _
    _ = C * B := by
      simp [C, mul_assoc]

/--
%%handwave
name:
  Uniform operator-valued \(L^2\) bounds from finite coordinate bounds
statement:
  Let \(H\) be finite-dimensional.  For a family of operator-valued fields
  \(F_s:\alpha\to\mathcal L(H,E)\), suppose each basis-direction evaluation
  \(F_s(\cdot)e_i\) is in \(L^2\) and has \(L^2\)-seminorm at most
  \(C_i B_s\), with the constants \(C_i\) finite.  Then all \(F_s\) are in
  \(L^2\), and their operator-valued \(L^2\)-seminorms are bounded by one
  finite constant times \(B_s\).
proof:
  Identify \(\mathcal L(H,E)\) with the finite product of basis-direction
  values.  The product field is \(L^2\) coordinatewise, and the \(L^2\)
  triangle inequality bounds its seminorm by the finite sum of the coordinate
  seminorms.  Applying the inverse continuous linear equivalence from the
  product to \(\mathcal L(H,E)\) contributes one fixed operator norm.
-/
theorem continuousLinearMap_sequence_memLp_and_eLpNorm_le_of_basis_eval_const_mul
    {α ιs H E : Type} [MeasurableSpace α]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {μ : Measure α} (Fseq : ιs → α → H →L[ℝ] E)
    (B : ιs → ℝ≥0∞)
    (Ceval : Fin (Module.finrank ℝ H) → ℝ≥0∞)
    (hCeval_top : ∀ i : Fin (Module.finrank ℝ H), Ceval i < ⊤)
    (h_eval : ∀ (s : ιs) (i : Fin (Module.finrank ℝ H)),
      MemLp (fun x ↦ Fseq s x (Module.finBasis ℝ H i)) 2 μ ∧
        eLpNorm (fun x ↦ Fseq s x (Module.finBasis ℝ H i)) 2 μ ≤
          Ceval i * B s) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ s : ιs,
      MemLp (Fseq s) 2 μ ∧ eLpNorm (Fseq s) 2 μ ≤ C * B s := by
  classical
  let ι := Fin (Module.finrank ℝ H)
  let T := continuousLinearMapFiniteBasisEvalEquiv H E
  let L : (ι → E) →L[ℝ] (H →L[ℝ] E) := (T.symm : (ι → E) →L[ℝ] H →L[ℝ] E)
  let C : ℝ≥0∞ := ENNReal.ofReal ‖L‖ * ∑ i : ι, Ceval i
  have hsum_top : (∑ i : ι, Ceval i) < ⊤ := by
    simpa using
      (ENNReal.sum_lt_top.2 (fun i _hi ↦ hCeval_top i) :
        (∑ i : ι, Ceval i) < ⊤)
  have hC_top : C < ⊤ := by
    exact ENNReal.mul_lt_top (by simp) hsum_top
  refine ⟨C, hC_top, ?_⟩
  intro s
  let coord : α → ι → E := fun x i ↦ Fseq s x (Module.finBasis ℝ H i)
  have hcoord_mem : MemLp coord 2 μ := by
    apply MemLp.of_eval
    intro i
    exact (h_eval s i).1
  have hLF_mem : MemLp (fun x ↦ L (coord x)) 2 μ :=
    L.comp_memLp' hcoord_mem
  have hLF_eq : (fun x ↦ L (coord x)) = Fseq s := by
    funext x
    have hcoord_eq : coord x = T (Fseq s x) := by
      ext i
      simp [coord, T]
    simp [L, hcoord_eq]
  have hF_mem : MemLp (Fseq s) 2 μ := by
    simpa [hLF_eq] using hLF_mem
  have hsingle_mem : ∀ i : ι,
      MemLp (fun x ↦ Pi.single i (coord x i) : α → ι → E) 2 μ := by
    intro i
    apply MemLp.of_eval
    intro j
    by_cases hji : j = i
    · subst j
      simpa using (h_eval s i).1
    · have hzero :
          (fun x ↦ (Pi.single i (coord x i) : ι → E) j) =
            fun _x : α ↦ (0 : E) := by
        funext x
        simp [Pi.single, hji]
      simpa [hzero] using
        (memLp_zero : MemLp (fun _x : α ↦ (0 : E)) 2 μ)
  have hcoord_eLp_le_sum :
      eLpNorm coord 2 μ ≤
        ∑ i : ι, eLpNorm (fun x ↦ Pi.single i (coord x i) : α → ι → E) 2 μ := by
    have hcoord_sum_ae :
        coord =ᵐ[μ] fun x : α ↦ ∑ i : ι, (Pi.single i (coord x i) : ι → E) :=
      Filter.Eventually.of_forall fun x ↦ by
        ext j
        simp
    have hfun_sum :
        (∑ i : ι, fun x : α ↦ (Pi.single i (coord x i) : ι → E)) =
          fun x : α ↦ ∑ i : ι, (Pi.single i (coord x i) : ι → E) := by
      ext x j
      simp
    calc
      eLpNorm coord 2 μ =
          eLpNorm (fun x : α ↦ ∑ i : ι, (Pi.single i (coord x i) : ι → E)) 2 μ := by
            exact eLpNorm_congr_ae hcoord_sum_ae
      _ = eLpNorm (∑ i : ι, fun x : α ↦ (Pi.single i (coord x i) : ι → E)) 2 μ := by
            rw [hfun_sum]
      _ ≤ ∑ i : ι, eLpNorm (fun x ↦ Pi.single i (coord x i) : α → ι → E) 2 μ := by
            simpa using
              (eLpNorm_sum_le
                (μ := μ) (p := (2 : ℝ≥0∞))
                (f := fun i x ↦ (Pi.single i (coord x i) : ι → E))
                (s := Finset.univ)
                (fun i _ ↦ (hsingle_mem i).aestronglyMeasurable)
                (by norm_num : (1 : ℝ≥0∞) ≤ 2))
  have hsingle_eLp_eq : ∀ i : ι,
      eLpNorm (fun x ↦ Pi.single i (coord x i) : α → ι → E) 2 μ =
        eLpNorm (fun x ↦ coord x i) 2 μ := by
    intro i
    exact eLpNorm_congr_enorm_ae <| Filter.Eventually.of_forall fun x ↦ by
      rw [Pi.enorm_single]
  have hcoord_eLp_le :
      eLpNorm coord 2 μ ≤ (∑ i : ι, Ceval i) * B s := by
    calc
      eLpNorm coord 2 μ ≤
          ∑ i : ι, eLpNorm (fun x ↦ Pi.single i (coord x i) : α → ι → E) 2 μ :=
        hcoord_eLp_le_sum
      _ = ∑ i : ι, eLpNorm (fun x ↦ coord x i) 2 μ := by
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [hsingle_eLp_eq i]
      _ ≤ ∑ i : ι, Ceval i * B s := by
        refine Finset.sum_le_sum ?_
        intro i _
        exact (h_eval s i).2
      _ = (∑ i : ι, Ceval i) * B s := by
        rw [Finset.sum_mul]
  have hF_eLp_le_coord :
      eLpNorm (Fseq s) 2 μ ≤ ENNReal.ofReal ‖L‖ * eLpNorm coord 2 μ := by
    calc
      eLpNorm (Fseq s) 2 μ = eLpNorm (fun x ↦ L (coord x)) 2 μ := by
        rw [← hLF_eq]
      _ ≤ ENNReal.ofReal ‖L‖ * eLpNorm coord 2 μ := by
        exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul
          (Filter.Eventually.of_forall fun x ↦ L.le_opNorm (coord x)) 2
  refine ⟨hF_mem, ?_⟩
  calc
    eLpNorm (Fseq s) 2 μ ≤ ENNReal.ofReal ‖L‖ * eLpNorm coord 2 μ := hF_eLp_le_coord
    _ ≤ ENNReal.ofReal ‖L‖ * ((∑ i : ι, Ceval i) * B s) :=
      mul_le_mul_right hcoord_eLp_le _
    _ = C * B s := by
      simp [C, mul_assoc]

/--
%%handwave
name:
  Chart pullbacks of values are uniformly \(L^2\)-bounded
statement:
  Let \(Q'\) be a compact coordinate set lying over \(Q\subset U\).  If
  \(u_n\) is locally Sobolev on \(U\) and uniformly bounded in the intrinsic
  \(W^{1,2}(Q)\) seminorm, then the pulled-back value functions
  \(u_n\circ\chi^{-1}\) are \(L^2(Q')\) and have uniformly bounded
  coordinate \(L^2\)-norms.
proof:
  The inverse image of \(Q'\) is a compact subset of \(Q\), hence of \(U\).
  Local Sobolev regularity gives \(L^2\)-membership there.  The smooth
  positive coordinate density is bounded above and below on \(Q'\), so the
  coordinate \(L^2\)-norms are comparable with the intrinsic value norm.
  The value part is bounded by the intrinsic \(W^{1,2}(Q)\) bound.
-/
theorem localRellich_chartPullback_value_eLpNorm_bound_of_local_bound
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [T2Space X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [IsIdentityManifoldModel H I] [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := I) X E)]
    [TopologicalSpace.PseudoMetrizableSpace
      (ManifoldDifferentialTotalSpace (I := I) X E)]
    {g : SmoothRiemannianMetricOnManifold I X} {μ : Measure X}
    (hμ : SmoothPositiveMeasureOnManifold (I := I) μ)
    {Q U : Set X} {Q' : Set H} (c : X)
    (hQU : Q ⊆ U) (hQ : IsCompact Q)
    (hQ'Q : Q' ⊆ manifoldChartRegion (chartAt H c) Q)
    (hQ' : IsCompact Q')
    (u : ℕ → X → E) (du : ℕ → ManifoldDifferentialField I X E)
    (hlocal : ∀ n : ℕ,
      IsLocalSobolevH1OnManifoldWithValues (I := I) g μ U (u n) (du n))
    (hbounded : BoundedInLocalSobolevH1OnManifoldWithValues (I := I) g μ Q u du) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ n : ℕ,
      MemLp (fun z : H ↦ u n ((chartAt H c).symm z)) 2
        (MeasureTheory.volume.restrict Q') ∧
      eLpNorm (fun z : H ↦ u n ((chartAt H c).symm z)) 2
        (MeasureTheory.volume.restrict Q') ≤ C := by
  classical
  let e : OpenPartialHomeomorph X H := chartAt H c
  let K₀ : Set X := e.symm '' Q'
  have hQ'_target : Q' ⊆ e.target := by
    intro z hz
    exact (hQ'Q hz).1
  have hK₀_compact : IsCompact K₀ :=
    hQ'.image_of_continuousOn (e.continuousOn_symm.mono hQ'_target)
  have hK₀_source : K₀ ⊆ e.source := by
    rintro x ⟨z, hzQ', rfl⟩
    exact e.map_target (hQ'_target hzQ')
  have hK₀Q : K₀ ⊆ Q := by
    rintro x ⟨z, hzQ', rfl⟩
    exact (hQ'Q hzQ').2
  have hK₀U : K₀ ⊆ U := hK₀Q.trans hQU
  have hQ'_def : Q' = e '' K₀ := by
    ext z
    constructor
    · intro hzQ'
      refine ⟨e.symm z, ⟨z, hzQ', rfl⟩, ?_⟩
      exact e.right_inv (hQ'_target hzQ')
    · rintro ⟨x, ⟨w, hwQ', rfl⟩, rfl⟩
      simpa [e.right_inv (hQ'_target hwQ')] using hwQ'
  have hmemK₀ : ∀ n : ℕ, MemLp (u n) 2 (μ.restrict K₀) := by
    intro n
    exact ((hlocal n).2 K₀ hK₀_compact hK₀U).1.memLp_trivial
  have hmemQ : ∀ n : ℕ, MemLp (u n) 2 (μ.restrict Q) := by
    intro n
    exact ((hlocal n).2 Q hQ hQU).1.memLp_trivial
  have hmemQ' : ∀ n : ℕ,
      MemLp (fun z : H ↦ u n ((chartAt H c).symm z)) 2
        (MeasureTheory.volume.restrict Q') := by
    intro n
    exact
      localRellich_chartPullback_memLp_on_compact_of_memLp
        (I := I) (μ := μ) hμ c hK₀_compact
        (by simpa [e] using hK₀_source)
        (by simpa [e, K₀] using hQ'_def) (hmemK₀ n)
  rcases localRellich_chartPullback_eLpNorm_two_le_on_compact
      (H := H) (X := X) (E := E) (I := I) (μ := μ) hμ c hK₀_compact
      (by simpa [e] using hK₀_source)
      (by simpa [e, K₀] using hQ'_def) with
    ⟨Cχ, hCχ_top, hCχ⟩
  rcases hbounded.value_l2_bound with ⟨Cv, hCv⟩
  let R : ℝ := max Cv 0
  let B : ℝ≥0∞ :=
    ENNReal.ofReal R ^ ((1 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal
  have hB_top : B < ⊤ := by
    have hq_nonneg :
        0 ≤ ((1 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal := by
      norm_num
    exact ENNReal.rpow_lt_top_of_nonneg hq_nonneg (by simp)
  refine ⟨Cχ * B, ENNReal.mul_lt_top hCχ_top hB_top, ?_⟩
  intro n
  refine ⟨hmemQ' n, ?_⟩
  have hK₀Q_measure : μ.restrict K₀ ≤ μ.restrict Q :=
    Measure.restrict_mono hK₀Q le_rfl
  have hK₀_to_Q :
      eLpNorm (u n) 2 (μ.restrict K₀) ≤
        eLpNorm (u n) 2 (μ.restrict Q) :=
    eLpNorm_mono_measure (u n) hK₀Q_measure
  have hvalue_int_bound :
      ∫ x, ‖u n x‖ ^ 2 ∂(μ.restrict Q) ≤ R := by
    have hCvR : manifoldLocalValueL2SeminormSq μ Q (u n) ≤ R :=
      (hCv n).trans (le_max_left Cv 0)
    simpa [manifoldLocalValueL2SeminormSq, R] using hCvR
  have hQ_norm_bound :
      eLpNorm (u n) 2 (μ.restrict Q) ≤ B := by
    simpa [B, R] using
      eLpNorm_two_le_of_integral_sq_le (hmemQ n) hvalue_int_bound
  calc
    eLpNorm (fun z : H ↦ u n ((chartAt H c).symm z)) 2
        (MeasureTheory.volume.restrict Q')
        ≤ Cχ * eLpNorm (u n) 2 (μ.restrict K₀) :=
          hCχ (u n) (hmemK₀ n)
    _ ≤ Cχ * eLpNorm (u n) 2 (μ.restrict Q) :=
          mul_le_mul_right hK₀_to_Q Cχ
    _ ≤ Cχ * B :=
          mul_le_mul_right hQ_norm_bound Cχ

/--
%%handwave
name:
  Fixed-direction chart pullbacks of differentials are controlled by energy
statement:
  Let \(K_0\) be compact in a chart source, let \(K'=\chi(K_0)\), and suppose
  \(K_0\subset Q\).  For every fixed coordinate direction \(v\in H\), the
  \(L^2(K',dx)\)-seminorm of
  \(z\mapsto D u(\chi^{-1}z)(d\chi^{-1}_z v)\) is bounded by a finite
  constant times the square root of the intrinsic Hilbert--Schmidt energy of
  \(D u\) on \(Q\).
proof:
  On compact coordinate sets, evaluation on the chart tangent vector
  \(d\chi^{-1}_z v\) is pointwise bounded by the Hilbert--Schmidt norm with a
  uniform constant.  The smooth positive coordinate density is bounded below,
  so Haar \(L^2\) on \(K'\) is controlled by the intrinsic measure.  Since
  \(K_0\subset Q\), the energy on \(K_0\) is bounded by the energy on \(Q\).
-/
theorem localRellich_chartPullback_derivative_eval_eLpNorm_le_intrinsic_on_compact
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [T2Space X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [IsIdentityManifoldModel H I] [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := I) X E)]
    [TopologicalSpace.PseudoMetrizableSpace
      (ManifoldDifferentialTotalSpace (I := I) X E)]
    {g : SmoothRiemannianMetricOnManifold I X} {μ : Measure X}
    (hμ : SmoothPositiveMeasureOnManifold (I := I) μ)
    {K₀ Q : Set X} {Kcoord : Set H} (c : X)
    (hK₀_compact : IsCompact K₀)
    (hK₀_source : K₀ ⊆ (chartAt H c).source)
    (hQ_meas : MeasurableSet Q)
    (hK₀Q : K₀ ⊆ Q)
    (hKcoord_def : Kcoord = (chartAt H c) '' K₀)
    (v : H)
    (du : ℕ → ManifoldDifferentialField I X E)
    (hduQ : ∀ n : ℕ,
      ManifoldDifferentialFieldMemHilbertSchmidtL2 (I := I) g
        (μ.restrict Q) (du n)) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ n : ℕ,
      MemLp (fun z : H ↦
          ManifoldDifferentialField.chartPullback (du n) (chartAt H c) z v) 2
        (MeasureTheory.volume.restrict Kcoord) ∧
      eLpNorm (fun z : H ↦
          ManifoldDifferentialField.chartPullback (du n) (chartAt H c) z v) 2
        (MeasureTheory.volume.restrict Kcoord) ≤
          C *
            ENNReal.ofReal (manifoldLocalDifferentialSeminormSq I g μ Q (du n)) ^
              ((1 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal := by
  classical
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  let e : OpenPartialHomeomorph X H := chartAt H c
  have he : e ∈ atlas H X := chart_mem_atlas H c
  have hKcoord_eq : Kcoord = e '' K₀ := by
    simpa [e] using hKcoord_def
  have hKcoord_target : Kcoord ⊆ e.target := by
    rw [hKcoord_eq]
    intro z hz
    rcases hz with ⟨x, hxK, rfl⟩
    exact e.map_source (hK₀_source hxK)
  have hKcoord_region : Kcoord ⊆ manifoldChartRegion e (Set.univ : Set X) := by
    intro z hz
    exact ⟨hKcoord_target hz, trivial⟩
  have hKcoord_compact : IsCompact Kcoord := by
    rw [hKcoord_eq]
    exact hK₀_compact.image_of_continuousOn (e.continuousOn.mono hK₀_source)
  have hKcoord_meas : MeasurableSet Kcoord := hKcoord_compact.measurableSet
  let G :=
    manifoldDifferentialHilbertBundleGeometry
      (I := I) (X := X) (E := E) g
  let metric :=
    manifoldDifferentialHilbertSchmidtContinuousRiemannianMetric
      (I := I) (X := X) (E := E) g
  letI : Bundle.RiemannianBundle
      (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E)) :=
    ⟨metric.toRiemannianMetric⟩
  letI (x : X) :
      NormedAddCommGroup (ManifoldDifferentialBundleFiber
        (I := I) (X := X) (E := E) x) :=
    manifoldDifferentialHilbertSchmidtNormedAddCommGroup
      (I := I) (X := X) (E := E) metric x
  letI (x : X) :
      InnerProductSpace ℝ (ManifoldDifferentialBundleFiber
        (I := I) (X := X) (E := E) x) :=
    manifoldDifferentialHilbertSchmidtInnerProductSpace
      (I := I) (X := X) (E := E) metric x
  have hG_inner :
      ∀ (x : X)
        (A B : ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E) x),
        G.fiberInner x A B = inner ℝ A B := by
    intro x A B
    rfl
  have hG_zero :
      ∀ x : X,
        G.fiberNormSq x ((0 : ManifoldDifferentialField I X E) x) = 0 := by
    intro x
    rw [G.fiberNormSq_eq_inner, hG_inner]
    simp
  rcases manifoldDifferentialCompactEvaluation_eLpNorm_two_on_support_le
      (I := I) (X := X) (E := E) g μ hμ e he Kcoord v
      hKcoord_region hKcoord_compact with
    ⟨Ceval, hCeval⟩
  refine ⟨(Ceval : ℝ≥0∞), by simp, ?_⟩
  intro n
  let duExt : ManifoldDifferentialField I X E := fun x ↦
    if x ∈ Q then du n x else 0
  have htotal_ext_eq :
      HilbertBundleSectionOnSurface.toTotalSpace
          (F := H →L[ℝ] E) duExt =
        Q.piecewise
          (HilbertBundleSectionOnSurface.toTotalSpace
            (F := H →L[ℝ] E) (du n))
          (HilbertBundleSectionOnSurface.toTotalSpace
            (F := H →L[ℝ] E) (0 : ManifoldDifferentialField I X E)) := by
    funext x
    by_cases hx : x ∈ Q
    · simp [HilbertBundleSectionOnSurface.toTotalSpace, duExt, hx, Set.piecewise_eq_of_mem]
    · simp [HilbertBundleSectionOnSurface.toTotalSpace, duExt, hx, Set.piecewise_eq_of_notMem]
  have hzero_mem :
      HilbertBundleSectionMemL2 G (μ.restrict Qᶜ)
        (0 : ManifoldDifferentialField I X E) :=
    hilbertBundleSectionMemL2_zero
      (I := I) (G := G) (by intro x A B; rfl) (μ.restrict Qᶜ)
  have hduExt_mem :
      ManifoldDifferentialFieldMemHilbertSchmidtL2 (I := I) g μ duExt := by
    refine ⟨?_, ?_⟩
    · have hdu_aestr :
          AEStronglyMeasurable
            (HilbertBundleSectionOnSurface.toTotalSpace
              (F := H →L[ℝ] E) (du n)) (μ.restrict Q) :=
        (hduQ n).aemeasurable.aestronglyMeasurable
      have hzero_aestr :
          AEStronglyMeasurable
            (HilbertBundleSectionOnSurface.toTotalSpace
              (F := H →L[ℝ] E) (0 : ManifoldDifferentialField I X E))
            (μ.restrict Qᶜ) :=
        hzero_mem.aemeasurable.aestronglyMeasurable
      exact
        (AEStronglyMeasurable.piecewise hQ_meas hdu_aestr hzero_aestr).aemeasurable.congr
          (Filter.EventuallyEq.of_eq htotal_ext_eq.symm)
    · have hnorm_ext_eq :
          (fun x : X ↦ G.fiberNormSq x (duExt x)) =
            Q.piecewise
              (fun x : X ↦ G.fiberNormSq x (du n x))
              (fun x : X ↦
                G.fiberNormSq x ((0 : ManifoldDifferentialField I X E) x)) := by
        funext x
        by_cases hx : x ∈ Q
        · simp [duExt, hx, Set.piecewise_eq_of_mem]
        · simp [duExt, hx, Set.piecewise_eq_of_notMem]
      have hint :
          Integrable
            (Q.piecewise
              (fun x : X ↦ G.fiberNormSq x (du n x))
              (fun x : X ↦
                G.fiberNormSq x ((0 : ManifoldDifferentialField I X E) x))) μ :=
        Integrable.piecewise hQ_meas (hduQ n).integrable_normSq
          hzero_mem.integrable_normSq
      change Integrable (fun x : X ↦ G.fiberNormSq x (duExt x)) μ
      rw [hnorm_ext_eq]
      exact hint
  let w :
      SquareIntegrableManifoldDifferentialField
        (I := I) (X := X) (E := E) g μ :=
    { toSection := duExt
      memL2 := hduExt_mem }
  rcases hCeval w with ⟨hmem_ext, hbound_ext⟩
  have heq_on_K :
      (fun z : H ↦ ManifoldDifferentialField.evalChart duExt e z v) =ᵐ[
          MeasureTheory.volume.restrict Kcoord]
        fun z : H ↦ ManifoldDifferentialField.evalChart (du n) e z v := by
    filter_upwards [ae_restrict_mem hKcoord_meas] with z hzK
    rcases (by simpa [hKcoord_eq] using hzK) with ⟨x, hxK₀, rfl⟩
    have hxQ : x ∈ Q := hK₀Q hxK₀
    have hxsource : x ∈ e.source := hK₀_source hxK₀
    simp [ManifoldDifferentialField.evalChart, duExt, hxQ, e.left_inv hxsource]
  have hmem :
      MemLp (fun z : H ↦
          ManifoldDifferentialField.chartPullback (du n) (chartAt H c) z v) 2
        (MeasureTheory.volume.restrict Kcoord) := by
    have hmem_eval :
        MemLp (fun z : H ↦ ManifoldDifferentialField.evalChart (du n) e z v) 2
          (MeasureTheory.volume.restrict Kcoord) :=
      (memLp_congr_ae heq_on_K).1 hmem_ext
    simpa [e, ManifoldDifferentialField.chartPullback_apply] using hmem_eval
  refine ⟨hmem, ?_⟩
  have hnorm_ext_sq :
      squareIntegrableHilbertBundleSectionL2NormSq G μ w =
        manifoldLocalDifferentialSeminormSq I g μ Q (du n) := by
    unfold squareIntegrableHilbertBundleSectionL2NormSq
    dsimp [w]
    have hnorm_ext_eq :
        (fun x : X ↦ G.fiberNormSq x (duExt x)) =
          Q.piecewise
            (fun x : X ↦ G.fiberNormSq x (du n x))
            (fun x : X ↦
              G.fiberNormSq x ((0 : ManifoldDifferentialField I X E) x)) := by
      funext x
      by_cases hx : x ∈ Q
      · simp [duExt, hx, Set.piecewise_eq_of_mem]
      · simp [duExt, hx, Set.piecewise_eq_of_notMem]
    have hzero_int :
        ∫ x in Qᶜ,
          G.fiberNormSq x ((0 : ManifoldDifferentialField I X E) x) ∂μ = 0 := by
      have hzero_ae :
          (fun x : X ↦
            G.fiberNormSq x ((0 : ManifoldDifferentialField I X E) x)) =ᵐ[
              μ.restrict Qᶜ] fun _x : X ↦ (0 : ℝ) := by
        filter_upwards [] with x
        exact hG_zero x
      simpa using integral_congr_ae hzero_ae
    rw [hnorm_ext_eq]
    rw [integral_piecewise hQ_meas (hduQ n).integrable_normSq
      hzero_mem.integrable_normSq]
    rw [hzero_int]
    simp [manifoldLocalDifferentialSeminormSq]
  have hsemi_nonneg :
      0 ≤ manifoldLocalDifferentialSeminormSq I g μ Q (du n) :=
    manifoldLocalDifferentialSeminormSq_nonneg I g μ Q (du n)
  have hq_eq :
      ((1 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal = (1 / 2 : ℝ) := by
    norm_num
  have hnorm_to_pow :
      ENNReal.ofReal (squareIntegrableHilbertBundleSectionL2Norm G μ w) =
        ENNReal.ofReal (manifoldLocalDifferentialSeminormSq I g μ Q (du n)) ^
          ((1 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal := by
    unfold squareIntegrableHilbertBundleSectionL2Norm
    rw [hnorm_ext_sq]
    rw [Real.sqrt_eq_rpow, hq_eq,
      ENNReal.ofReal_rpow_of_nonneg hsemi_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ))]
  have hnorm_eq :
      eLpNorm
          (fun z : H ↦ ManifoldDifferentialField.chartPullback (du n) (chartAt H c) z v)
          2 (MeasureTheory.volume.restrict Kcoord) =
        eLpNorm (fun z : H ↦ ManifoldDifferentialField.evalChart (du n) e z v)
          2 (MeasureTheory.volume.restrict Kcoord) := by
    simp [e, ManifoldDifferentialField.chartPullback_apply]
  calc
    eLpNorm
        (fun z : H ↦ ManifoldDifferentialField.chartPullback (du n) (chartAt H c) z v)
        2 (MeasureTheory.volume.restrict Kcoord)
        = eLpNorm (fun z : H ↦ ManifoldDifferentialField.evalChart (du n) e z v)
            2 (MeasureTheory.volume.restrict Kcoord) := hnorm_eq
    _ = eLpNorm (fun z : H ↦ ManifoldDifferentialField.evalChart duExt e z v)
            2 (MeasureTheory.volume.restrict Kcoord) :=
          eLpNorm_congr_ae heq_on_K.symm
    _ ≤ (Ceval : ℝ≥0∞) *
          ENNReal.ofReal
            (squareIntegrableHilbertBundleSectionL2Norm G μ w) := hbound_ext
    _ = (Ceval : ℝ≥0∞) *
          ENNReal.ofReal (manifoldLocalDifferentialSeminormSq I g μ Q (du n)) ^
            ((1 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal := by
          rw [hnorm_to_pow]

/--
%%handwave
name:
  Compact chart pullbacks of differentials are controlled by intrinsic energy
statement:
  Let \(K_0\) be compact in a chart source, let \(K'=\chi(K_0)\), and suppose
  \(K_0\subset Q\).  If differential fields are intrinsically
  square-integrable on \(Q\), then their coordinate pullbacks
  \(D u\circ d\chi^{-1}\) on \(K'\) are bounded in \(L^2(K',dx)\) by a fixed
  multiple of the square root of the intrinsic Hilbert--Schmidt energy on
  \(Q\).
proof:
  On the compact coordinate set, the chart tangent maps and the Riemannian
  metric give a uniform pointwise comparison between the Euclidean operator
  norm of the pulled-back differential and the intrinsic Hilbert--Schmidt
  norm.  The smooth positive coordinate density is bounded below there, so
  the weighted coordinate integral coming from \(\mu\) controls the Haar
  integral.  Since \(K_0\subset Q\), the intrinsic energy on \(K_0\) is
  bounded by the energy on \(Q\).
-/
theorem localRellich_chartPullback_derivative_eLpNorm_le_intrinsic_on_compact
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [T2Space X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [IsIdentityManifoldModel H I] [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := I) X E)]
    [TopologicalSpace.PseudoMetrizableSpace
      (ManifoldDifferentialTotalSpace (I := I) X E)]
    {g : SmoothRiemannianMetricOnManifold I X} {μ : Measure X}
    (hμ : SmoothPositiveMeasureOnManifold (I := I) μ)
    {K₀ Q : Set X} {Kcoord : Set H} (c : X)
    (hK₀_compact : IsCompact K₀)
    (hK₀_source : K₀ ⊆ (chartAt H c).source)
    (hQ_meas : MeasurableSet Q)
    (hK₀Q : K₀ ⊆ Q)
    (hKcoord_def : Kcoord = (chartAt H c) '' K₀)
    (du : ℕ → ManifoldDifferentialField I X E)
    (hduQ : ∀ n : ℕ,
      ManifoldDifferentialFieldMemHilbertSchmidtL2 (I := I) g
        (μ.restrict Q) (du n)) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ n : ℕ,
      MemLp (ManifoldDifferentialField.chartPullback (du n) (chartAt H c)) 2
        (MeasureTheory.volume.restrict Kcoord) ∧
      eLpNorm (ManifoldDifferentialField.chartPullback (du n) (chartAt H c)) 2
        (MeasureTheory.volume.restrict Kcoord) ≤
          C *
            ENNReal.ofReal (manifoldLocalDifferentialSeminormSq I g μ Q (du n)) ^
              ((1 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal := by
  classical
  let ι := Fin (Module.finrank ℝ H)
  have hdir : ∀ i : ι,
      ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ n : ℕ,
        MemLp (fun z : H ↦
            ManifoldDifferentialField.chartPullback (du n) (chartAt H c) z
              (Module.finBasis ℝ H i)) 2
          (MeasureTheory.volume.restrict Kcoord) ∧
        eLpNorm (fun z : H ↦
            ManifoldDifferentialField.chartPullback (du n) (chartAt H c) z
              (Module.finBasis ℝ H i)) 2
          (MeasureTheory.volume.restrict Kcoord) ≤
            C *
              ENNReal.ofReal (manifoldLocalDifferentialSeminormSq I g μ Q (du n)) ^
                ((1 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal := by
    intro i
    exact
      localRellich_chartPullback_derivative_eval_eLpNorm_le_intrinsic_on_compact
        (I := I) (g := g) (μ := μ) hμ c hK₀_compact hK₀_source
        hQ_meas hK₀Q hKcoord_def (Module.finBasis ℝ H i) du hduQ
  choose Ceval hCeval_top hCeval using hdir
  let B : ℕ → ℝ≥0∞ := fun n ↦
    ENNReal.ofReal (manifoldLocalDifferentialSeminormSq I g μ Q (du n)) ^
      ((1 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal
  have h_eval : ∀ (n : ℕ) (i : ι),
      MemLp (fun z ↦
          ManifoldDifferentialField.chartPullback (du n) (chartAt H c) z
            (Module.finBasis ℝ H i)) 2
        (MeasureTheory.volume.restrict Kcoord) ∧
      eLpNorm (fun z ↦
          ManifoldDifferentialField.chartPullback (du n) (chartAt H c) z
            (Module.finBasis ℝ H i)) 2
        (MeasureTheory.volume.restrict Kcoord) ≤ Ceval i * B n := by
    intro n i
    simpa [B] using hCeval i n
  rcases
    continuousLinearMap_sequence_memLp_and_eLpNorm_le_of_basis_eval_const_mul
      (μ := MeasureTheory.volume.restrict Kcoord)
      (Fseq := fun n : ℕ ↦ ManifoldDifferentialField.chartPullback (du n) (chartAt H c))
      (B := B) (Ceval := Ceval) hCeval_top h_eval with
    ⟨C, hC_top, hC⟩
  refine ⟨C, hC_top, ?_⟩
  intro n
  simpa [B] using hC n

/--
%%handwave
name:
  Compact chart pullbacks of differentials are uniformly \(L^2\)-bounded
statement:
  Let \(K_0\) be compact in a chart source, let \(K'=\chi(K_0)\), and suppose
  \(K_0\subset Q\).  If a sequence of differential fields is intrinsically
  square-integrable on \(Q\) and has uniformly bounded intrinsic
  Hilbert--Schmidt energy on \(Q\), then the coordinate pullbacks
  \(D u_n\circ d\chi^{-1}\) are uniformly bounded in \(L^2(K',dx)\).
proof:
  Apply [the compact chart comparison with intrinsic energy](lean:JJMath.Uniformization.localRellich_chartPullback_derivative_eLpNorm_le_intrinsic_on_compact)
  and then use the uniform bound on the intrinsic Hilbert--Schmidt energy.
-/
theorem localRellich_chartPullback_derivative_eLpNorm_bound_of_intrinsic_bound
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [T2Space X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [IsIdentityManifoldModel H I] [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := I) X E)]
    [TopologicalSpace.PseudoMetrizableSpace
      (ManifoldDifferentialTotalSpace (I := I) X E)]
    {g : SmoothRiemannianMetricOnManifold I X} {μ : Measure X}
    (hμ : SmoothPositiveMeasureOnManifold (I := I) μ)
    {K₀ Q : Set X} {Kcoord : Set H} (c : X)
    (hK₀_compact : IsCompact K₀)
    (hK₀_source : K₀ ⊆ (chartAt H c).source)
    (hQ_meas : MeasurableSet Q)
    (hK₀Q : K₀ ⊆ Q)
    (hKcoord_def : Kcoord = (chartAt H c) '' K₀)
    (du : ℕ → ManifoldDifferentialField I X E)
    (hduQ : ∀ n : ℕ,
      ManifoldDifferentialFieldMemHilbertSchmidtL2 (I := I) g
        (μ.restrict Q) (du n))
    (henergy : ∃ C : ℝ, ∀ n : ℕ,
      manifoldLocalDifferentialSeminormSq I g μ Q (du n) ≤ C) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ n : ℕ,
      MemLp (ManifoldDifferentialField.chartPullback (du n) (chartAt H c)) 2
        (MeasureTheory.volume.restrict Kcoord) ∧
      eLpNorm (ManifoldDifferentialField.chartPullback (du n) (chartAt H c)) 2
        (MeasureTheory.volume.restrict Kcoord) ≤ C := by
  classical
  rcases localRellich_chartPullback_derivative_eLpNorm_le_intrinsic_on_compact
      (I := I) (g := g) (μ := μ) hμ c hK₀_compact hK₀_source
      hQ_meas hK₀Q hKcoord_def du hduQ with
    ⟨Cχ, hCχ_top, hCχ⟩
  rcases henergy with ⟨Cd, hCd⟩
  let R : ℝ := max Cd 0
  let B : ℝ≥0∞ :=
    ENNReal.ofReal R ^ ((1 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal
  have hB_top : B < ⊤ := by
    have hq_nonneg :
        0 ≤ ((1 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal := by
      norm_num
    exact ENNReal.rpow_lt_top_of_nonneg hq_nonneg (by simp)
  refine ⟨Cχ * B, ENNReal.mul_lt_top hCχ_top hB_top, ?_⟩
  intro n
  rcases hCχ n with ⟨hmem, hbound⟩
  refine ⟨hmem, ?_⟩
  have hsemi_le_R :
      manifoldLocalDifferentialSeminormSq I g μ Q (du n) ≤ R :=
    (hCd n).trans (le_max_left Cd 0)
  have hpow_le :
      ENNReal.ofReal (manifoldLocalDifferentialSeminormSq I g μ Q (du n)) ^
          ((1 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal ≤ B := by
    have hq_nonneg :
        0 ≤ ((1 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal := by
      norm_num
    exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hsemi_le_R) hq_nonneg
  calc
    eLpNorm (ManifoldDifferentialField.chartPullback (du n) (chartAt H c)) 2
        (MeasureTheory.volume.restrict Kcoord)
        ≤ Cχ *
            ENNReal.ofReal (manifoldLocalDifferentialSeminormSq I g μ Q (du n)) ^
              ((1 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal := hbound
    _ ≤ Cχ * B := mul_le_mul_right hpow_le Cχ

/--
%%handwave
name:
  Chart pullbacks of weak differentials are uniformly \(L^2\)-bounded
statement:
  Let \(Q'\) be a compact coordinate set lying over \(Q\subset U\).  If
  \(u_n\) is locally Sobolev on \(U\) with weak differential \(D u_n\), and
  the sequence is uniformly bounded in the intrinsic \(W^{1,2}(Q)\) seminorm,
  then the chart pullbacks of \(D u_n\) are \(L^2(Q')\) as
  operator-valued maps and have uniformly bounded coordinate \(L^2\)-norms.
proof:
  On the compact coordinate set, the chart tangent maps and the Riemannian
  metric give a uniform comparison between the Euclidean operator norm of the
  pulled-back differential and the intrinsic Hilbert--Schmidt norm of
  \(D u_n\).  The smooth positive coordinate density is uniformly comparable
  with Haar measure on \(Q'\).  These comparisons transfer the intrinsic
  differential \(L^2(Q)\) bound to the coordinate \(L^2(Q')\) bound.
-/
theorem localRellich_chartPullback_derivative_eLpNorm_bound_of_local_bound
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [T2Space X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [IsIdentityManifoldModel H I] [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := I) X E)]
    [TopologicalSpace.PseudoMetrizableSpace
      (ManifoldDifferentialTotalSpace (I := I) X E)]
    {g : SmoothRiemannianMetricOnManifold I X} {μ : Measure X}
    (hμ : SmoothPositiveMeasureOnManifold (I := I) μ)
    {Q U : Set X} {Q' : Set H} (c : X)
    (hQU : Q ⊆ U) (hQ : IsCompact Q)
    (hQ'Q : Q' ⊆ manifoldChartRegion (chartAt H c) Q)
    (hQ' : IsCompact Q')
    (u : ℕ → X → E) (du : ℕ → ManifoldDifferentialField I X E)
    (hlocal : ∀ n : ℕ,
      IsLocalSobolevH1OnManifoldWithValues (I := I) g μ U (u n) (du n))
    (hbounded : BoundedInLocalSobolevH1OnManifoldWithValues (I := I) g μ Q u du) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ n : ℕ,
      MemLp (ManifoldDifferentialField.chartPullback (du n) (chartAt H c)) 2
        (MeasureTheory.volume.restrict Q') ∧
      eLpNorm (ManifoldDifferentialField.chartPullback (du n) (chartAt H c)) 2
        (MeasureTheory.volume.restrict Q') ≤ C := by
  classical
  let e : OpenPartialHomeomorph X H := chartAt H c
  let K₀ : Set X := e.symm '' Q'
  have hQ'_target : Q' ⊆ e.target := by
    intro z hz
    exact (hQ'Q hz).1
  have hK₀_compact : IsCompact K₀ :=
    hQ'.image_of_continuousOn (e.continuousOn_symm.mono hQ'_target)
  have hK₀_source : K₀ ⊆ e.source := by
    rintro x ⟨z, hzQ', rfl⟩
    exact e.map_target (hQ'_target hzQ')
  have hK₀Q : K₀ ⊆ Q := by
    rintro x ⟨z, hzQ', rfl⟩
    exact (hQ'Q hzQ').2
  have hK₀U : K₀ ⊆ U := hK₀Q.trans hQU
  have hQ'_def : Q' = e '' K₀ := by
    ext z
    constructor
    · intro hzQ'
      refine ⟨e.symm z, ⟨z, hzQ', rfl⟩, ?_⟩
      exact e.right_inv (hQ'_target hzQ')
    · rintro ⟨x, ⟨w, hwQ', rfl⟩, rfl⟩
      simpa [e.right_inv (hQ'_target hwQ')] using hwQ'
  have hduQ : ∀ n : ℕ,
      ManifoldDifferentialFieldMemHilbertSchmidtL2 (I := I) g
        (μ.restrict Q) (du n) := by
    intro n
    exact ((hlocal n).2 Q hQ hQU).2
  exact
    localRellich_chartPullback_derivative_eLpNorm_bound_of_intrinsic_bound
      (H := H) (X := X) (E := E) (I := I) (g := g) (μ := μ)
      hμ c hK₀_compact
      (by simpa [e] using hK₀_source)
      hQ.measurableSet
      hK₀Q
      (by simpa [e, K₀] using hQ'_def)
      du hduQ hbounded.differential_l2_bound

/--
%%handwave
name:
  Chart pullbacks inherit local Sobolev bounds
statement:
  If \(Q'\) is a compact coordinate set whose inverse image lies in \(Q\),
  then a sequence uniformly bounded in the intrinsic \(W^{1,2}(Q)\) seminorm
  has pulled-back representatives uniformly bounded in the Euclidean
  \(W^{1,2}(Q')\) seminorm.
proof:
  The smooth positive coordinate density is bounded above on \(Q'\), and the
  Riemannian metric together with the chart tangent maps gives a uniform
  comparison between the intrinsic Hilbert--Schmidt norm and the Euclidean
  operator norm on \(Q'\).  These compactness bounds convert the intrinsic
  value and differential estimates on \(Q\) into Euclidean estimates on
  \(Q'\).
-/
theorem localRellich_chartPullback_h1_bound_of_local_bound
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [T2Space X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [IsIdentityManifoldModel H I] [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := I) X E)]
    [TopologicalSpace.PseudoMetrizableSpace
      (ManifoldDifferentialTotalSpace (I := I) X E)]
    {g : SmoothRiemannianMetricOnManifold I X} {μ : Measure X}
    (hμ : SmoothPositiveMeasureOnManifold (I := I) μ)
    {Q U : Set X} {Q' : Set H} (c : X)
    (hQU : Q ⊆ U) (hQ : IsCompact Q)
    (hQ'Q : Q' ⊆ manifoldChartRegion (chartAt H c) Q)
    (hQ' : IsCompact Q')
    (u : ℕ → X → E) (du : ℕ → ManifoldDifferentialField I X E)
    (hlocal : ∀ n : ℕ,
      IsLocalSobolevH1OnManifoldWithValues (I := I) g μ U (u n) (du n))
    (hbounded : BoundedInLocalSobolevH1OnManifoldWithValues (I := I) g μ Q u du) :
    BoundedInEuclideanLocalSobolevH1WithValues Q'
      (fun n z ↦ u n ((chartAt H c).symm z))
      (fun n ↦ ManifoldDifferentialField.chartPullback (du n) (chartAt H c)) := by
  rcases localRellich_chartPullback_value_eLpNorm_bound_of_local_bound
      (I := I) (g := g) (μ := μ) hμ c hQU hQ hQ'Q hQ'
      u du hlocal hbounded with
    ⟨Cu, hCu_top, hCu⟩
  rcases localRellich_chartPullback_derivative_eLpNorm_bound_of_local_bound
      (I := I) (g := g) (μ := μ) hμ c hQU hQ hQ'Q hQ'
      u du hlocal hbounded with
    ⟨Cd, hCd_top, hCd⟩
  refine ⟨Cu + Cd, ENNReal.add_lt_top.2 ⟨hCu_top, hCd_top⟩, ?_⟩
  intro n
  rcases hCu n with ⟨hu_mem, hu_bound⟩
  rcases hCd n with ⟨hdu_mem, hdu_bound⟩
  exact ⟨hu_mem, hdu_mem, add_le_add hu_bound hdu_bound⟩

/--
%%handwave
name:
  Manifold \(L^2\)-distances are controlled by chart distances
statement:
  Let \(K'=\chi(K_0)\) for a compact chart piece \(K_0\).  For a smooth
  positive measure, there is \(C\ge0\) such that for all \(m,n\),
  \[
    \|u_m-u_n\|_{L^2(K_0,\mu)}
      \le C\,\|(u_m-u_n)\circ\chi^{-1}\|_{L^2(K',dx)} .
  \]
proof:
  The coordinate density of \(\mu\) with respect to Haar measure is
  continuous on \(K'\), hence bounded above there.  The change-of-variables
  formula for the chart writes the left-hand norm as a density-weighted
  coordinate \(L^2\)-norm, and the upper density bound gives the estimate.
-/
theorem localRellich_chartPullback_l2_dist_le
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [T2Space X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [IsIdentityManifoldModel H I] [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := I) X E)]
    [TopologicalSpace.PseudoMetrizableSpace
      (ManifoldDifferentialTotalSpace (I := I) X E)]
    {μ : Measure X} (hμ : SmoothPositiveMeasureOnManifold (I := I) μ)
    {K₀ Q : Set X} {K' : Set H} (c : X)
    (hK₀_compact : IsCompact K₀)
    (hK₀_sub : K₀ ⊆ (chartAt H c).source ∩ interior Q)
    (hK'_def : K' = (chartAt H c) '' K₀)
    (u : ℕ → X → E)
    (hmemK₀ : ∀ n : ℕ, MemLp (u n) 2 (μ.restrict K₀))
    (hmemK' : ∀ n : ℕ,
      MemLp (fun z : H ↦ u n ((chartAt H c).symm z)) 2
        (MeasureTheory.volume.restrict K')) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ m n : ℕ,
        dist ((hmemK₀ m).toLp (u m)) ((hmemK₀ n).toLp (u n)) ≤
          C * dist
            ((hmemK' m).toLp (fun z : H ↦ u m ((chartAt H c).symm z)))
            ((hmemK' n).toLp (fun z : H ↦ u n ((chartAt H c).symm z))) := by
  classical
  let e : OpenPartialHomeomorph X H := chartAt H c
  have he : e ∈ atlas H X := chart_mem_atlas H c
  have hK'_eq : K' = e '' K₀ := by
    simpa [e] using hK'_def
  have hK₀_source : K₀ ⊆ e.source := fun x hx ↦ (hK₀_sub hx).1
  have hK'_target : K' ⊆ e.target := by
    rw [hK'_eq]
    intro z hz
    rcases hz with ⟨x, hxK, rfl⟩
    exact e.map_source (hK₀_source hxK)
  have hK'_compact : IsCompact K' := by
    rw [hK'_eq]
    exact hK₀_compact.image_of_continuousOn (e.continuousOn.mono hK₀_source)
  have hK'_meas : MeasurableSet K' := hK'_compact.measurableSet
  rcases hμ.chart_density e he with ⟨ρ, hρ_smooth, hρ_pos, hmap⟩
  let ν : Measure H := MeasureTheory.volume.restrict e.target
  let δ : H → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (ρ z)
  have hρ_cont_K' : ContinuousOn ρ K' :=
    hρ_smooth.continuousOn.mono hK'_target
  rcases hK'_compact.exists_bound_of_continuousOn hρ_cont_K' with
    ⟨M, hM⟩
  let R : ℝ := max M 1
  let c₁ : ℝ≥0∞ := ENNReal.ofReal R
  let q : ℝ := ((1 : ℝ≥0∞) / (2 : ℝ≥0∞)).toReal
  let C₁ : ℝ≥0∞ := c₁ ^ q
  let C : ℝ := C₁.toReal
  have hR_pos : 0 < R := by
    dsimp [R]
    exact lt_of_lt_of_le zero_lt_one (le_max_right M 1)
  have hc₁_ne_zero : c₁ ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hR_pos)
  have hc₁_ne_top : c₁ ≠ (⊤ : ℝ≥0∞) := by
    simp [c₁]
  have hδ_upper : ∀ᵐ z ∂ν.restrict K', δ z ≤ c₁ := by
    filter_upwards [ae_restrict_mem hK'_meas] with z hzK'
    have hρ_le_norm : ρ z ≤ ‖ρ z‖ := le_abs_self (ρ z)
    have hnorm_le_R : ‖ρ z‖ ≤ R := by
      exact (hM z hzK').trans (le_max_left M 1)
    exact ENNReal.ofReal_le_ofReal (hρ_le_norm.trans hnorm_le_R)
  have hq_nonneg : 0 ≤ q := by
    norm_num [q]
  have hC₁_top : C₁ < ⊤ := by
    exact ENNReal.rpow_lt_top_of_nonneg hq_nonneg hc₁_ne_top
  refine ⟨C, ENNReal.toReal_nonneg, ?_⟩
  intro m n
  let fbase : X → E := fun x ↦ u m x - u n x
  let Fpull : H → E := fun z ↦ u m (e.symm z) - u n (e.symm z)
  let μsK : Measure X := (μ.restrict e.source).restrict (e ⁻¹' K')
  have hpre_ae : e ⁻¹' K' =ᵐ[μ.restrict e.source] K₀ := by
    filter_upwards [ae_restrict_mem e.open_source.measurableSet] with x hx_source
    apply propext
    constructor
    · intro hxK'
      rw [hK'_eq] at hxK'
      rcases hxK' with ⟨y, hyK₀, hyx⟩
      have hy_source : y ∈ e.source := hK₀_source hyK₀
      have hy_eq_x : y = x := e.injOn hy_source hx_source hyx
      simpa [hy_eq_x] using hyK₀
    · intro hxK₀
      rw [hK'_eq]
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
  have hsymm_big :
      AEMeasurable e.symm (Measure.map e (μ.restrict e.source)) := by
    have hsymm_vol :
        AEMeasurable e.symm (MeasureTheory.volume.restrict e.target) :=
      openPartialHomeomorph_symm_aemeasurable_restrict_target e MeasureTheory.volume
    have h_ac :
        Measure.map e (μ.restrict e.source) ≪
          MeasureTheory.volume.restrict e.target := by
      rw [hmap]
      exact withDensity_absolutelyContinuous _ _
    exact hsymm_vol.mono_ac h_ac
  have hmap_μsK_le :
      Measure.map e μsK ≤ Measure.map e (μ.restrict e.source) :=
    Measure.map_mono_of_aemeasurable (by
      dsimp [μsK]
      exact Measure.restrict_le_self) he_aemeas_source
  have hsymm_aemeas : AEMeasurable e.symm (Measure.map e μsK) :=
    hsymm_big.mono_measure hmap_μsK_le
  have hmap_symm : Measure.map e.symm (Measure.map e μsK) = μsK := by
    have hmap_comp :
        Measure.map e.symm (Measure.map e μsK) =
          Measure.map (fun x : X ↦ e.symm (e x)) μsK := by
      simpa [Function.comp_def] using
        (AEMeasurable.map_map_of_aemeasurable hsymm_aemeas he_aemeas_μsK)
    have hleft :
        (fun x : X ↦ e.symm (e x)) =ᵐ[μsK] fun x ↦ x := by
      have hsource_ae : ∀ᵐ x ∂μsK, x ∈ e.source := by
        dsimp [μsK]
        exact ae_restrict_of_ae (ae_restrict_mem e.open_source.measurableSet)
      exact hsource_ae.mono fun x hx_source ↦ e.left_inv hx_source
    calc
      Measure.map e.symm (Measure.map e μsK)
          = Measure.map (fun x : X ↦ e.symm (e x)) μsK := hmap_comp
      _ = Measure.map (fun x : X ↦ x) μsK := Measure.map_congr hleft
      _ = μsK := by rw [Measure.map_id']
  have hfbase_mem : MemLp fbase 2 (μ.restrict K₀) :=
    (hmemK₀ m).sub (hmemK₀ n)
  have hfbase_μsK : MemLp fbase 2 μsK := by
    simpa [hμsK_eq] using hfbase_mem
  have hfbase_aestr_map_symm :
      AEStronglyMeasurable fbase (Measure.map e.symm (Measure.map e μsK)) := by
    simpa [hmap_symm] using hfbase_μsK.aestronglyMeasurable
  have hFpull_aestr :
      AEStronglyMeasurable Fpull (Measure.map e μsK) := by
    simpa [Fpull, fbase, Function.comp_def] using
      hfbase_aestr_map_symm.comp_aemeasurable hsymm_aemeas
  have hcomp_eq :
      (fun x : X ↦ Fpull (e x)) =ᵐ[μsK] fbase := by
    have hsource_ae : ∀ᵐ x ∂μsK, x ∈ e.source := by
      dsimp [μsK]
      exact ae_restrict_of_ae (ae_restrict_mem e.open_source.measurableSet)
    exact hsource_ae.mono fun x hx_source ↦ by
      simp [Fpull, fbase, e.left_inv hx_source]
  have hmap_restrict :
      (Measure.map e (μ.restrict e.source)).restrict K' = Measure.map e μsK := by
    dsimp [μsK]
    exact Measure.restrict_map_of_aemeasurable he_aemeas_source hK'_meas
  have hweighted_eq :
      (ν.withDensity δ).restrict K' = Measure.map e μsK := by
    calc
      (ν.withDensity δ).restrict K'
          = (Measure.map e (μ.restrict e.source)).restrict K' := by
              simpa [ν, δ] using congrArg (fun m : Measure H ↦ m.restrict K') hmap.symm
      _ = Measure.map e μsK := hmap_restrict
  have hweighted_norm :
      eLpNorm Fpull 2 ((ν.withDensity δ).restrict K') =
        eLpNorm fbase 2 (μ.restrict K₀) := by
    calc
      eLpNorm Fpull 2 ((ν.withDensity δ).restrict K')
          = eLpNorm Fpull 2 (Measure.map e μsK) := by rw [hweighted_eq]
      _ = eLpNorm (fun x : X ↦ Fpull (e x)) 2 μsK := by
            exact eLpNorm_map_measure hFpull_aestr he_aemeas_μsK
      _ = eLpNorm fbase 2 μsK := eLpNorm_congr_ae hcomp_eq
      _ = eLpNorm fbase 2 (μ.restrict K₀) := by rw [hμsK_eq]
  have hνK'_eq : ν.restrict K' = MeasureTheory.volume.restrict K' := by
    simpa [ν] using
      Measure.restrict_restrict_of_subset (μ := MeasureTheory.volume) hK'_target
  have hupper :
      eLpNorm Fpull 2 ((ν.withDensity δ).restrict K') ≤
        C₁ * eLpNorm Fpull 2 (ν.restrict K') := by
    simpa [C₁, q] using
      eLpNorm_two_withDensity_upper_bound_on_restrict_le
        (ν := ν) (δ := δ) (K := K') (c := c₁)
        hK'_meas hc₁_ne_zero hδ_upper Fpull
  have hbase_le :
      eLpNorm fbase 2 (μ.restrict K₀) ≤
        C₁ * eLpNorm Fpull 2 (MeasureTheory.volume.restrict K') := by
    calc
      eLpNorm fbase 2 (μ.restrict K₀)
          = eLpNorm Fpull 2 ((ν.withDensity δ).restrict K') := hweighted_norm.symm
      _ ≤ C₁ * eLpNorm Fpull 2 (ν.restrict K') := hupper
      _ = C₁ * eLpNorm Fpull 2 (MeasureTheory.volume.restrict K') := by
            rw [hνK'_eq]
  have hcoord_mem :
      MemLp Fpull 2 (MeasureTheory.volume.restrict K') := by
    simpa [Fpull, e] using (hmemK' m).sub (hmemK' n)
  have hcoord_top :
      eLpNorm Fpull 2 (MeasureTheory.volume.restrict K') < ⊤ :=
    hcoord_mem.eLpNorm_lt_top
  have hprod_top :
      C₁ * eLpNorm Fpull 2 (MeasureTheory.volume.restrict K') < ⊤ :=
    ENNReal.mul_lt_top hC₁_top hcoord_top
  have hbase_real :
      (eLpNorm fbase 2 (μ.restrict K₀)).toReal ≤
        C * (eLpNorm Fpull 2 (MeasureTheory.volume.restrict K')).toReal := by
    have htoReal :=
      ENNReal.toReal_mono hprod_top.ne hbase_le
    simpa [C, C₁, ENNReal.toReal_mul] using htoReal
  have hdist_base :
      dist ((hmemK₀ m).toLp (u m)) ((hmemK₀ n).toLp (u n)) =
        (eLpNorm fbase 2 (μ.restrict K₀)).toReal := by
    rw [Lp.dist_def]
    exact congrArg ENNReal.toReal
      (eLpNorm_congr_ae ((hmemK₀ m).coeFn_toLp.sub (hmemK₀ n).coeFn_toLp))
  have hdist_coord :
      dist
          ((hmemK' m).toLp (fun z : H ↦ u m ((chartAt H c).symm z)))
          ((hmemK' n).toLp (fun z : H ↦ u n ((chartAt H c).symm z))) =
        (eLpNorm Fpull 2 (MeasureTheory.volume.restrict K')).toReal := by
    rw [Lp.dist_def]
    exact congrArg ENNReal.toReal
      (eLpNorm_congr_ae ((hmemK' m).coeFn_toLp.sub (hmemK' n).coeFn_toLp))
  calc
    dist ((hmemK₀ m).toLp (u m)) ((hmemK₀ n).toLp (u n))
        = (eLpNorm fbase 2 (μ.restrict K₀)).toReal := hdist_base
    _ ≤ C * (eLpNorm Fpull 2 (MeasureTheory.volume.restrict K')).toReal := hbase_real
    _ =
        C * dist
          ((hmemK' m).toLp (fun z : H ↦ u m ((chartAt H c).symm z)))
          ((hmemK' n).toLp (fun z : H ↦ u n ((chartAt H c).symm z))) := by
            rw [hdist_coord]

/--
%%handwave
name:
  Chartwise Sobolev bounds and \(L^2\)-distance comparison
statement:
  Let \(K'\subset\operatorname{int}Q'\) be compact coordinate data over a
  compact manifold set \(K_0\subset Q\).  For the pulled-back maps
  \(v_n=u_n\circ\chi^{-1}\) and pulled-back differential fields, the
  intrinsic \(W^{1,2}(Q)\) bound gives a uniform Euclidean
  \(W^{1,2}(Q')\) bound, the \(v_n\) are in \(L^2(K')\), and the
  \(L^2(K_0)\)-distance of \(u_m,u_n\) is bounded by a fixed multiple of the
  \(L^2(K')\)-distance of \(v_m,v_n\).
proof:
  On the compact coordinate sets the smooth positive measure has a density
  bounded above and below with respect to Haar measure.  The Riemannian
  metric and the chart tangent maps are uniformly comparable with the
  Euclidean Hilbert--Schmidt norm.  These compactness bounds transfer the
  intrinsic value and differential \(L^2\) estimates to the coordinate
  estimates, and the lower density bound gives the displayed comparison of
  \(L^2\)-distances.
-/
theorem localRellich_compact_chart_piece_euclidean_bounds_of_geometry
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [T2Space X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [IsIdentityManifoldModel H I] [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := I) X E)]
    [TopologicalSpace.PseudoMetrizableSpace
      (ManifoldDifferentialTotalSpace (I := I) X E)]
    {g : SmoothRiemannianMetricOnManifold I X} {μ : Measure X}
    (hμ : SmoothPositiveMeasureOnManifold (I := I) μ)
    {K₀ Q U : Set X} (c : X)
    (hK₀_compact : IsCompact K₀)
    (hK₀_sub : K₀ ⊆ (chartAt H c).source ∩ interior Q)
    (hQU : Q ⊆ U) (hQ : IsCompact Q)
    (u : ℕ → X → E) (du : ℕ → ManifoldDifferentialField I X E)
    (hlocal : ∀ n : ℕ,
      IsLocalSobolevH1OnManifoldWithValues (I := I) g μ U (u n) (du n))
    (hbounded : BoundedInLocalSobolevH1OnManifoldWithValues (I := I) g μ Q u du)
    (hmemK₀ : ∀ n : ℕ, MemLp (u n) 2 (μ.restrict K₀))
    {K' Q' : Set H}
    (hK'_def : K' = (chartAt H c) '' K₀)
    (hQ'Q : Q' ⊆ manifoldChartRegion (chartAt H c) Q)
    (hQ' : IsCompact Q') :
    BoundedInEuclideanLocalSobolevH1WithValues Q'
      (fun n z ↦ u n ((chartAt H c).symm z))
      (fun n ↦ ManifoldDifferentialField.chartPullback (du n) (chartAt H c)) ∧
      ∃ (hmemK' : ∀ n : ℕ,
          MemLp (fun z : H ↦ u n ((chartAt H c).symm z)) 2
            (MeasureTheory.volume.restrict K')) (C : ℝ),
        0 ≤ C ∧
        ∀ m n : ℕ,
          dist ((hmemK₀ m).toLp (u m)) ((hmemK₀ n).toLp (u n)) ≤
            C * dist
              ((hmemK' m).toLp (fun z : H ↦ u m ((chartAt H c).symm z)))
              ((hmemK' n).toLp (fun z : H ↦ u n ((chartAt H c).symm z))) := by
  classical
  have hbounded' :
      BoundedInEuclideanLocalSobolevH1WithValues Q'
        (fun n z ↦ u n ((chartAt H c).symm z))
        (fun n ↦ ManifoldDifferentialField.chartPullback (du n) (chartAt H c)) :=
    localRellich_chartPullback_h1_bound_of_local_bound
      (I := I) (g := g) (μ := μ) hμ c
      (Q := Q) (Q' := Q') (U := U)
      hQU hQ hQ'Q hQ' u du hlocal hbounded
  have hmemK' : ∀ n : ℕ,
      MemLp (fun z : H ↦ u n ((chartAt H c).symm z)) 2
        (MeasureTheory.volume.restrict K') := by
    intro n
    exact
      localRellich_chartPullback_memLp_on_compact_of_memLp
        (I := I) (μ := μ) hμ c hK₀_compact
        (fun x hx ↦ (hK₀_sub hx).1) hK'_def (hmemK₀ n)
  rcases localRellich_chartPullback_l2_dist_le
      (I := I) (μ := μ) hμ c hK₀_compact hK₀_sub hK'_def u
      hmemK₀ hmemK' with
    ⟨C, hC, hdist⟩
  exact ⟨hbounded', hmemK', C, hC, hdist⟩

/--
%%handwave
name:
  A compact chart piece produces Euclidean Rellich data
statement:
  Let \(K_0\) be a compact subset of one coordinate chart and of
  \(\operatorname{int}Q\).  From a uniformly \(W^{1,2}\)-bounded manifold
  sequence \(u_n\) on \(Q\), one obtains compact Euclidean sets
  \(K'\subset\operatorname{int}Q'\subset Q'\subset\Omega\), pulled-back maps
  \(v_n\), pulled-back weak derivatives \(D v_n\), the Euclidean weak
  derivative identities on \(\Omega\), a uniform Euclidean \(W^{1,2}(Q')\)
  bound, \(L^2(K')\)-membership of the \(v_n\), and a constant \(C\ge0\)
  such that the manifold \(L^2(K_0)\)-distance of \(u_m,u_n\) is bounded by
  \(C\) times the Euclidean \(L^2(K')\)-distance of \(v_m,v_n\).
proof:
  Choose \(K'\) as the coordinate image of \(K_0\), choose a compact
  coordinate neighborhood \(Q'\) still inside the image of the chart portion
  lying over \(Q\), and let \(\Omega\) be the coordinate image of the chart
  portion lying over \(U\).  The chartwise definition of weak derivative gives
  the Euclidean weak derivative identities.  Smooth positivity of the measure
  and compactness give upper and lower bounds for the coordinate density, and
  continuity of the Riemannian metric gives norm comparability for the
  differential.  These comparisons transfer the intrinsic \(W^{1,2}(Q)\)
  bound and give the displayed \(L^2\)-distance estimate.
-/
theorem localRellich_compact_chart_piece_euclidean_data_of_memLp
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [T2Space X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [IsIdentityManifoldModel H I] [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := I) X E)]
    [TopologicalSpace.PseudoMetrizableSpace
      (ManifoldDifferentialTotalSpace (I := I) X E)]
    {g : SmoothRiemannianMetricOnManifold I X} {μ : Measure X}
    (hμ : SmoothPositiveMeasureOnManifold (I := I) μ)
    {K₀ Q U : Set X} (c : X)
    (hK₀_compact : IsCompact K₀)
    (hK₀_sub : K₀ ⊆ (chartAt H c).source ∩ interior Q)
    (hQU : Q ⊆ U) (hQ : IsCompact Q) (hU_open : IsOpen U)
    (u : ℕ → X → E) (du : ℕ → ManifoldDifferentialField I X E)
    (hlocal : ∀ n : ℕ,
      IsLocalSobolevH1OnManifoldWithValues (I := I) g μ U (u n) (du n))
    (hbounded : BoundedInLocalSobolevH1OnManifoldWithValues (I := I) g μ Q u du)
    (hmemK₀ : ∀ n : ℕ, MemLp (u n) 2 (μ.restrict K₀)) :
    ∃ (K' Q' Ω : Set H) (v : ℕ → H → E) (dv : ℕ → H → H →L[ℝ] E)
      (_ : IsCompact K') (_ : K' ⊆ interior Q')
      (_ : Q' ⊆ Ω) (_ : IsCompact Q') (_ : IsOpen Ω)
      (_ : ∀ n : ℕ, IsWeakDerivativeOnEuclideanRegionWithValues Ω (v n) (dv n))
      (_ : BoundedInEuclideanLocalSobolevH1WithValues Q' v dv)
      (hmemK' : ∀ n : ℕ, MemLp (v n) 2 (MeasureTheory.volume.restrict K'))
      (C : ℝ),
        0 ≤ C ∧
          ∀ m n : ℕ,
            dist ((hmemK₀ m).toLp (u m)) ((hmemK₀ n).toLp (u n)) ≤
              C * dist ((hmemK' m).toLp (v m)) ((hmemK' n).toLp (v n)) := by
  classical
  let e : OpenPartialHomeomorph X H := chartAt H c
  let v : ℕ → H → E := fun n z ↦ u n (e.symm z)
  let dv : ℕ → H → H →L[ℝ] E :=
    fun n ↦ ManifoldDifferentialField.chartPullback (du n) e
  rcases localRellich_compact_chart_piece_euclidean_geometry
      (H := H) (X := X) (K₀ := K₀) (Q := Q) (U := U)
      c hK₀_compact hK₀_sub hU_open with
    ⟨K', Q', Ω, hK'_def, hΩ_def, hK'_compact, hK'Q', hQ'Q, hQ'_compact,
      hΩ_open⟩
  have hQ'Ω : Q' ⊆ Ω := by
    intro z hz
    have hzQ : z ∈ manifoldChartRegion e Q := by
      simpa [e] using hQ'Q hz
    have hzU : z ∈ manifoldChartRegion e U := by
      rcases hzQ with ⟨hz_target, hz_base⟩
      exact ⟨hz_target, hQU hz_base⟩
    simpa [e, hΩ_def] using hzU
  have he : e ∈ atlas H X := chart_mem_atlas H c
  have hweak : ∀ n : ℕ,
      IsWeakDerivativeOnEuclideanRegionWithValues Ω (v n) (dv n) := by
    intro n
    have hchart :=
      IsWeakDerivativeOnManifoldRegionBundle.chartPullback
        (I := I) (hlocal n).1 e he
    simpa [v, dv, e, hΩ_def] using hchart
  rcases localRellich_compact_chart_piece_euclidean_bounds_of_geometry
      (I := I) (g := g) (μ := μ) hμ c hK₀_compact hK₀_sub hQU hQ
      u du hlocal hbounded hmemK₀
      (K' := K') (Q' := Q') hK'_def hQ'Q hQ'_compact with
    ⟨hbounded', hmemK', C, hC, hdist⟩
  refine ⟨K', Q', Ω, v, dv, hK'_compact, hK'Q', hQ'Ω, hQ'_compact,
    hΩ_open, hweak, ?_, ?_, C, hC, ?_⟩
  · simpa [v, dv, e] using hbounded'
  · intro n
    simpa [v, e] using hmemK' n
  · intro m n
    simpa [v, e] using hdist m n

/--
%%handwave
name:
  One compact chart piece gives local Rellich control
statement:
  Let \(M\) be a finite-dimensional Riemannian manifold modeled by the
  ordinary real identity model, equipped with a smooth positive measure, and
  let \(E\) be a finite-dimensional Hilbert space.  If a compact set \(K_0\)
  lies inside one coordinate chart and inside \(\operatorname{int}Q\), and
  if \(u_n\) is uniformly \(W^{1,2}\)-bounded on \(Q\), then the
  \(L^2(K_0;E)\)-classes of \(u_n\) are controlled by a compact chartwise
  metric target: there are a pseudo-metric space \(Z\), points \(z_n\in Z\),
  a compact set \(S\subset Z\) containing all \(z_n\), and \(C\ge 0\) such
  that the \(L^2(K_0;E)\)-distance between \(u_m\) and \(u_n\) is at most
  \(C\,d_Z(z_m,z_n)\).
proof:
  Choose a slightly larger compact coordinate neighborhood still contained in
  the chart and in \(Q\).  In that chart, the weak derivative identity pulls
  back to the Euclidean weak derivative identity.  Smooth positivity of the
  measure and continuity of the Riemannian Hilbert--Schmidt metric compare
  the pulled-back Euclidean \(W^{1,2}\)-bounds with the intrinsic bound on
  \(Q\).  Euclidean Rellich gives a compact set containing the chartwise
  \(L^2\)-classes, and the same density comparison bounds the
  \(L^2(K_0;E)\)-distance by the chartwise distance.
-/
theorem localRellich_compact_chart_piece_compact_control_of_memLp
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [T2Space X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [IsIdentityManifoldModel H I] [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := I) X E)]
    [TopologicalSpace.PseudoMetrizableSpace
      (ManifoldDifferentialTotalSpace (I := I) X E)]
    {g : SmoothRiemannianMetricOnManifold I X} {μ : Measure X}
    (hμ : SmoothPositiveMeasureOnManifold (I := I) μ)
    {K₀ Q U : Set X} (c : X)
    (hK₀_compact : IsCompact K₀)
    (hK₀_sub : K₀ ⊆ (chartAt H c).source ∩ interior Q)
    (hQU : Q ⊆ U) (hQ : IsCompact Q) (hU_open : IsOpen U)
    (u : ℕ → X → E) (du : ℕ → ManifoldDifferentialField I X E)
    (hlocal : ∀ n : ℕ,
      IsLocalSobolevH1OnManifoldWithValues (I := I) g μ U (u n) (du n))
    (hbounded : BoundedInLocalSobolevH1OnManifoldWithValues (I := I) g μ Q u du)
    (hmemK₀ : ∀ n : ℕ, MemLp (u n) 2 (μ.restrict K₀)) :
    ∃ (Z : Type) (_ : PseudoMetricSpace Z) (z : ℕ → Z) (S : Set Z) (C : ℝ),
      0 ≤ C ∧ IsCompact S ∧ (∀ n : ℕ, z n ∈ S) ∧
        (∀ m n : ℕ,
          dist ((hmemK₀ m).toLp (u m)) ((hmemK₀ n).toLp (u n)) ≤
            C * dist (z m) (z n)) := by
  classical
  rcases localRellich_compact_chart_piece_euclidean_data_of_memLp
      (I := I) (g := g) (μ := μ) hμ c hK₀_compact hK₀_sub
      hQU hQ hU_open u du hlocal hbounded hmemK₀ with
    ⟨K', Q', Ω, v, dv, hK', hK'Q', hQ'Ω, hQ', hΩ_open,
      hweak, hbounded', hmemK', C, hC, hdist⟩
  rcases euclideanRellichKondrachov_compact_containment_on_compact
      hK' hK'Q' hQ'Ω hQ' hΩ_open v dv hweak hbounded' hmemK' with
    ⟨S, hS_compact, hS_mem⟩
  exact ⟨Lp E 2 (MeasureTheory.volume.restrict K'), inferInstance,
    (fun n : ℕ ↦ (hmemK' n).toLp (v n)), S, C, hC, hS_compact, hS_mem, hdist⟩

/--
%%handwave
name:
  Finite compact chart covers give chartwise Rellich control
statement:
  Let \(M\) be a finite-dimensional Riemannian manifold modeled by the
  ordinary real identity model, equipped with a smooth positive measure, and
  let \(E\) be a finite-dimensional Hilbert space.  Suppose compact sets
  \(K_i\) form a finite cover of \(K\), and each \(K_i\) lies inside one
  coordinate chart and inside \(\operatorname{int}Q\).  If
  \(Q\subset U\), \(Q\) is compact, \(U\) is open, and \(u_n\) is uniformly
  \(W^{1,2}\)-bounded on \(Q\), then there are chartwise compact target sets
  \(S_i\) and a constant \(C\ge 0\) such that the \(L^2(K;E)\)-distance
  between \(u_m\) and \(u_n\) is bounded by \(C\) times the finite sum of the
  chartwise distances.
proof:
  On each compact chart piece, pull the weak derivative identity to Euclidean
  coordinates.  Smooth positivity of the measure and continuity of the
  Riemannian metric compare the chartwise \(W^{1,2}\)-norms with the
  intrinsic norm on \(Q\).  Thus [the Euclidean \(L^2\)-classes lie in compact sets](lean:JJMath.Uniformization.euclideanRellichKondrachov_compact_containment_on_compact)
  in every chart.  A finite measurable decomposition subordinate to the
  compact chart cover gives the stated finite-sum distance estimate.
-/
theorem localRellich_finite_compact_chart_cover_compact_control_of_memLp
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [T2Space X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [IsIdentityManifoldModel H I] [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := I) X E)]
    [TopologicalSpace.PseudoMetrizableSpace
      (ManifoldDifferentialTotalSpace (I := I) X E)]
    {g : SmoothRiemannianMetricOnManifold I X} {μ : Measure X}
    (hμ : SmoothPositiveMeasureOnManifold (I := I) μ)
    {K Q U : Set X} {ι : Type} [Fintype ι]
    (c : ι → X) (Kc : ι → Set X)
    (hKc_compact : ∀ i : ι, IsCompact (Kc i))
    (hKc_sub : ∀ i : ι, Kc i ⊆ (chartAt H (c i)).source ∩ interior Q)
    (hK_cover : K = ⋃ i : ι, Kc i)
    (hQU : Q ⊆ U) (hQ : IsCompact Q) (hU_open : IsOpen U)
    (u : ℕ → X → E) (du : ℕ → ManifoldDifferentialField I X E)
    (hlocal : ∀ n : ℕ,
      IsLocalSobolevH1OnManifoldWithValues (I := I) g μ U (u n) (du n))
    (hbounded : BoundedInLocalSobolevH1OnManifoldWithValues (I := I) g μ Q u du)
    (hmemK : ∀ n : ℕ, MemLp (u n) 2 (μ.restrict K)) :
    ∃ (Z : ι → Type) (_ : ∀ i : ι, PseudoMetricSpace (Z i))
      (z : (i : ι) → ℕ → Z i) (S : (i : ι) → Set (Z i)) (C : ℝ),
        0 ≤ C ∧
          (∀ i : ι, IsCompact (S i)) ∧
          (∀ i : ι, ∀ n : ℕ, z i n ∈ S i) ∧
          (∀ m n : ℕ,
            dist ((hmemK m).toLp (u m)) ((hmemK n).toLp (u n)) ≤
              C * ∑ i : ι, dist (z i m) (z i n)) := by
  classical
  have hKc_subset_K : ∀ i : ι, Kc i ⊆ K := by
    intro i x hx
    rw [hK_cover]
    exact Set.mem_iUnion.mpr ⟨i, hx⟩
  have hmemKc : ∀ i : ι, ∀ n : ℕ, MemLp (u n) 2 (μ.restrict (Kc i)) := by
    intro i n
    exact (hmemK n).mono_measure (Measure.restrict_mono (hKc_subset_K i) le_rfl)
  have hpiece :
      ∀ i : ι,
        ∃ (Z : Type) (_ : PseudoMetricSpace Z) (z : ℕ → Z) (S : Set Z) (C : ℝ),
          0 ≤ C ∧ IsCompact S ∧ (∀ n : ℕ, z n ∈ S) ∧
            (∀ m n : ℕ,
              dist ((hmemKc i m).toLp (u m)) ((hmemKc i n).toLp (u n)) ≤
                C * dist (z m) (z n)) := by
    intro i
    exact localRellich_compact_chart_piece_compact_control_of_memLp
      (I := I) (g := g) (μ := μ) hμ (c i) (hKc_compact i)
      (hKc_sub i) hQU hQ hU_open u du hlocal hbounded (hmemKc i)
  choose Z hZ z S C hC hS_compact hS_mem hpiece_control using hpiece
  letI : ∀ i : ι, PseudoMetricSpace (Z i) := hZ
  refine ⟨Z, hZ, z, S, ∑ i : ι, C i, ?_, hS_compact, hS_mem, ?_⟩
  · exact Finset.sum_nonneg fun i _hi ↦ hC i
  · intro m n
    have hcover_dist :=
      l2_dist_le_sum_dist_on_finite_cover
        (μ := μ) Kc hK_cover u hmemK hmemKc m n
    calc
      dist ((hmemK m).toLp (u m)) ((hmemK n).toLp (u n))
          ≤ ∑ i : ι,
              dist ((hmemKc i m).toLp (u m)) ((hmemKc i n).toLp (u n)) :=
            hcover_dist
      _ ≤ ∑ i : ι, C i * dist (z i m) (z i n) := by
            exact Finset.sum_le_sum fun i _hi ↦ hpiece_control i m n
      _ ≤ (∑ i : ι, C i) * ∑ i : ι, dist (z i m) (z i n) := by
            have hC_le_sum : ∀ i : ι, C i ≤ ∑ j : ι, C j := by
              intro i
              exact Finset.single_le_sum (fun j _hj ↦ hC j) (Finset.mem_univ i)
            calc
              ∑ i : ι, C i * dist (z i m) (z i n)
                  ≤ ∑ i : ι, (∑ j : ι, C j) * dist (z i m) (z i n) := by
                    exact Finset.sum_le_sum fun i _hi ↦
                      mul_le_mul_of_nonneg_right (hC_le_sum i) dist_nonneg
              _ = (∑ j : ι, C j) * ∑ i : ι, dist (z i m) (z i n) := by
                    rw [Finset.mul_sum]

/--
%%handwave
name:
  Finite chartwise compact containment and distance control
statement:
  Let \(M\) be a finite-dimensional Riemannian manifold modeled by the
  ordinary real identity model, equipped with a smooth positive measure, and
  let \(E\) be a finite-dimensional Hilbert space.  If
  \(K\subset\operatorname{int}Q\subset Q\subset U\), with \(K,Q\) compact and
  \(U\) open, and \(u_n\) is uniformly \(W^{1,2}\)-bounded on \(Q\), then
  there are finitely many chartwise \(L^2\)-spaces, chartwise representatives
  \(v_{i,n}\), compact sets \(S_i\) containing all \(v_{i,n}\), and a constant
  \(C\ge 0\) such that the \(L^2(K;E)\)-distance between \(u_m\) and \(u_n\)
  is bounded by \(C\) times the finite sum of chartwise distances between
  \(v_{i,m}\) and \(v_{i,n}\).
proof:
  Cover \(K\) by finitely many compact coordinate patches lying inside \(Q\).
  The chart pullback of the weak differential gives Euclidean weak
  derivatives on the patches.  Smooth positivity of the manifold measure and
  continuity of the Riemannian metric make the chartwise \(W^{1,2}\) norms
  uniformly controlled by the intrinsic \(W^{1,2}(Q)\) bound.  Hence [the Euclidean \(L^2\)-classes lie in compact sets](lean:JJMath.Uniformization.euclideanRellichKondrachov_compact_containment_on_compact)
  in each chart.  A finite partition of \(K\) subordinate to the chart patches
  gives the stated finite-sum distance control.
-/
theorem localRellich_exists_finite_chartwise_compact_control_of_memLp
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [R1Space X] [T2Space X]
    [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [IsIdentityManifoldModel H I] [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := I) X E)]
    [TopologicalSpace.PseudoMetrizableSpace
      (ManifoldDifferentialTotalSpace (I := I) X E)]
    {g : SmoothRiemannianMetricOnManifold I X} {μ : Measure X}
    (hμ : SmoothPositiveMeasureOnManifold (I := I) μ)
    {K Q U : Set X} (hK : IsCompact K) (hKQ : K ⊆ interior Q)
    (hQU : Q ⊆ U) (hQ : IsCompact Q) (hU_open : IsOpen U)
    (u : ℕ → X → E) (du : ℕ → ManifoldDifferentialField I X E)
    (hlocal : ∀ n : ℕ,
      IsLocalSobolevH1OnManifoldWithValues (I := I) g μ U (u n) (du n))
    (hbounded : BoundedInLocalSobolevH1OnManifoldWithValues (I := I) g μ Q u du)
    (hmemK : ∀ n : ℕ, MemLp (u n) 2 (μ.restrict K)) :
    ∃ (ι : Type) (_ : Fintype ι)
      (Z : ι → Type) (_ : ∀ i : ι, PseudoMetricSpace (Z i))
      (z : (i : ι) → ℕ → Z i) (S : (i : ι) → Set (Z i)) (C : ℝ),
        0 ≤ C ∧
          (∀ i : ι, IsCompact (S i)) ∧
          (∀ i : ι, ∀ n : ℕ, z i n ∈ S i) ∧
          (∀ m n : ℕ,
            dist ((hmemK m).toLp (u m)) ((hmemK n).toLp (u n)) ≤
              C * ∑ i : ι, dist (z i m) (z i n)) := by
  classical
  rcases compact_exists_finite_compact_chart_cover_inside (H := H) hK hKQ with
    ⟨ι, hι, c, Kc, hKc_compact, hKc_sub, hK_cover⟩
  letI : Fintype ι := hι
  rcases localRellich_finite_compact_chart_cover_compact_control_of_memLp
      (I := I) (g := g) (μ := μ) hμ c Kc
      hKc_compact hKc_sub hK_cover hQU hQ hU_open
      u du hlocal hbounded hmemK with
    ⟨Z, hZ, z, S, C, hC, hS_compact, hS_mem, hcontrol⟩
  exact ⟨ι, hι, Z, hZ, z, S, C, hC, hS_compact, hS_mem, hcontrol⟩

/--
%%handwave
name:
  Finite chartwise Rellich control data on a compact manifold set
statement:
  Let \(M\) be a finite-dimensional Riemannian manifold modeled by the
  ordinary real identity model, equipped with a smooth positive measure, and
  let \(E\) be a finite-dimensional Hilbert space.  If
  \(K\subset\operatorname{int}Q\subset Q\subset U\), with \(K,Q\) compact and
  \(U\) open, and \(u_n\) is uniformly \(W^{1,2}\)-bounded on \(Q\), then
  there are finitely many chartwise \(L^2\)-spaces, chartwise representatives
  \(v_{i,n}\), and a constant \(C\ge 0\) such that:
  every selected subsequence of each \(v_{i,n}\) has a Cauchy subsubsequence,
  and the \(L^2(K;E)\)-distance between \(u_m\) and \(u_n\) is bounded by
  \(C\) times the finite sum of the chartwise distances between
  \(v_{i,m}\) and \(v_{i,n}\).
proof:
  Cover \(K\) by finitely many chart neighborhoods whose larger compact
  coordinate neighborhoods are contained in \(Q\).  In each chart, the
  manifold weak derivative identity becomes [the Euclidean weak derivative identity for the pulled-back map and differential](lean:JJMath.Uniformization.IsWeakDerivativeOnManifoldRegionBundle.chartPullback).
  The smooth positive coordinate density and the Riemannian metric are
  uniformly comparable with Euclidean data on each compact chart patch, so
  the global \(W^{1,2}(Q)\) bound gives uniform Euclidean \(W^{1,2}\) bounds
  on every patch.  Euclidean Rellich gives the chartwise Cauchy
  subsubsequences.  A partition of \(K\) subordinate to the finitely many
  chart patches gives the finite-sum \(L^2\)-distance control.
-/
theorem localRellich_exists_finite_chartwise_cauchy_control_of_memLp
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [R1Space X] [T2Space X]
    [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [IsIdentityManifoldModel H I] [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := I) X E)]
    [TopologicalSpace.PseudoMetrizableSpace
      (ManifoldDifferentialTotalSpace (I := I) X E)]
    {g : SmoothRiemannianMetricOnManifold I X} {μ : Measure X}
    (hμ : SmoothPositiveMeasureOnManifold (I := I) μ)
    {K Q U : Set X} (hK : IsCompact K) (hKQ : K ⊆ interior Q)
    (hQU : Q ⊆ U) (hQ : IsCompact Q) (hU_open : IsOpen U)
    (u : ℕ → X → E) (du : ℕ → ManifoldDifferentialField I X E)
    (hlocal : ∀ n : ℕ,
      IsLocalSobolevH1OnManifoldWithValues (I := I) g μ U (u n) (du n))
    (hbounded : BoundedInLocalSobolevH1OnManifoldWithValues (I := I) g μ Q u du)
    (hmemK : ∀ n : ℕ, MemLp (u n) 2 (μ.restrict K)) :
    ∃ (ι : Type) (_ : Fintype ι)
      (Z : ι → Type) (_ : ∀ i : ι, PseudoMetricSpace (Z i))
      (z : (i : ι) → ℕ → Z i) (C : ℝ),
        0 ≤ C ∧
          (∀ i : ι, ∀ f : ℕ → ℕ,
            ∃ φ : ℕ → ℕ, StrictMono φ ∧
              CauchySeq (fun n : ℕ ↦ z i (f (φ n)))) ∧
          (∀ m n : ℕ,
            dist ((hmemK m).toLp (u m)) ((hmemK n).toLp (u n)) ≤
              C * ∑ i : ι, dist (z i m) (z i n)) := by
  rcases localRellich_exists_finite_chartwise_compact_control_of_memLp
      hμ hK hKQ hQU hQ hU_open u du hlocal hbounded hmemK with
    ⟨ι, hι, Z, hZ, z, S, C, hC, hS_compact, hS_mem, hcontrol⟩
  letI : Fintype ι := hι
  letI : ∀ i : ι, PseudoMetricSpace (Z i) := hZ
  refine ⟨ι, hι, Z, hZ, z, C, hC, ?_, hcontrol⟩
  intro i f
  exact cauchy_subsequence_of_compact_containment
    (x := z i) (S := S i) (hS_compact i) (hS_mem i) f

/--
%%handwave
name:
  Chartwise Euclidean Cauchy subsequences on manifolds
statement:
  Let \(M\) be a finite-dimensional Riemannian manifold modeled by the
  ordinary real identity model, equipped with a smooth positive measure, and
  let \(E\) be a finite-dimensional Hilbert space.  If
  \(K\subset\operatorname{int}Q\subset Q\subset U\), with \(K,Q\) compact and
  \(U\) open, and \(u_n\) is uniformly \(W^{1,2}\)-bounded on \(Q\), then
  every selected subsequence of the \(L^2(K;E)\)-classes of \(u_n\) has a
  Cauchy subsubsequence.
proof:
  Use [finitely many chartwise spaces whose distances control the \(L^2(K;E)\)-distance](lean:JJMath.Uniformization.localRellich_exists_finite_chartwise_cauchy_control_of_memLp).
  A finite diagonal extraction gives one subsequence which is Cauchy in all
  chartwise spaces, and [finite metric control preserves Cauchyness](lean:JJMath.Uniformization.cauchySeq_of_finite_dist_control) in
  \(L^2(K;E)\).
-/
theorem localRellich_chartwise_cauchy_subsequence_of_memLp
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [R1Space X] [T2Space X]
    [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [IsIdentityManifoldModel H I] [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := I) X E)]
    [TopologicalSpace.PseudoMetrizableSpace
      (ManifoldDifferentialTotalSpace (I := I) X E)]
    {g : SmoothRiemannianMetricOnManifold I X} {μ : Measure X}
    (hμ : SmoothPositiveMeasureOnManifold (I := I) μ)
    {K Q U : Set X} (hK : IsCompact K) (hKQ : K ⊆ interior Q)
    (hQU : Q ⊆ U) (hQ : IsCompact Q) (hU_open : IsOpen U)
    (u : ℕ → X → E) (du : ℕ → ManifoldDifferentialField I X E)
    (hlocal : ∀ n : ℕ,
      IsLocalSobolevH1OnManifoldWithValues (I := I) g μ U (u n) (du n))
    (hbounded : BoundedInLocalSobolevH1OnManifoldWithValues (I := I) g μ Q u du)
    (hmemK : ∀ n : ℕ, MemLp (u n) 2 (μ.restrict K))
    (f : ℕ → ℕ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      CauchySeq (fun n : ℕ ↦ (hmemK (f (φ n))).toLp (u (f (φ n)))) := by
  rcases localRellich_exists_finite_chartwise_cauchy_control_of_memLp
      hμ hK hKQ hQU hQ hU_open u du hlocal hbounded hmemK with
    ⟨ι, hι, Z, hZ, z, C, hC, hsubseq, hcontrol⟩
  letI : Fintype ι := hι
  letI : ∀ i : ι, PseudoMetricSpace (Z i) := hZ
  exact
    cauchy_subsequence_of_finite_chartwise_subsequence_and_dist_control
      (x := fun n : ℕ ↦ (hmemK n).toLp (u n))
      (z := z) hsubseq hC hcontrol f

/--
%%handwave
name:
  Chartwise Euclidean total boundedness for manifold \(L^2\)-classes
statement:
  Let \(M\) be a finite-dimensional Riemannian manifold modeled by the
  ordinary real identity model, equipped with a smooth
  positive measure, let \(E\) be a finite-dimensional Hilbert space, and let
  \(K\subset\operatorname{int}Q\subset Q\subset U\), with \(K,Q\) compact and
  \(U\) open.  Suppose the \(E\)-valued maps \(u_n\) are locally Sobolev on
  \(U\), uniformly \(W^{1,2}\)-bounded on \(Q\), and define classes in
  \(L^2(K;E)\).  Then these \(L^2(K;E)\)-classes form a totally bounded
  subset of \(L^2(K;E)\).
proof:
  Use the sequential criterion for total boundedness.  Every selected
  subsequence has [a Cauchy subsubsequence](lean:JJMath.Uniformization.localRellich_chartwise_cauchy_subsequence_of_memLp),
  so the range of the \(L^2(K;E)\)-classes is totally bounded.
-/
theorem localRellich_chartwise_totallyBounded_range_of_memLp
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [R1Space X] [T2Space X]
    [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [IsIdentityManifoldModel H I] [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := I) X E)]
    [TopologicalSpace.PseudoMetrizableSpace
      (ManifoldDifferentialTotalSpace (I := I) X E)]
    {g : SmoothRiemannianMetricOnManifold I X} {μ : Measure X}
    (hμ : SmoothPositiveMeasureOnManifold (I := I) μ)
    {K Q U : Set X} (hK : IsCompact K) (hKQ : K ⊆ interior Q)
    (hQU : Q ⊆ U) (hQ : IsCompact Q) (hU_open : IsOpen U)
    (u : ℕ → X → E) (du : ℕ → ManifoldDifferentialField I X E)
    (hlocal : ∀ n : ℕ,
      IsLocalSobolevH1OnManifoldWithValues (I := I) g μ U (u n) (du n))
    (hbounded : BoundedInLocalSobolevH1OnManifoldWithValues (I := I) g μ Q u du)
    (hmemK : ∀ n : ℕ, MemLp (u n) 2 (μ.restrict K)) :
    TotallyBounded (Set.range fun n : ℕ => (hmemK n).toLp (u n)) := by
  exact
    totallyBounded_range_of_forall_subsequence_cauchy
      (fun n : ℕ ↦ (hmemK n).toLp (u n))
      (fun f ↦
        localRellich_chartwise_cauchy_subsequence_of_memLp
          hμ hK hKQ hQU hQ hU_open u du hlocal hbounded hmemK f)

/--
%%handwave
name:
  Chartwise Euclidean compact containment for manifold \(L^2\)-classes
statement:
  Let \(M\) be a finite-dimensional Riemannian manifold modeled by the
  ordinary real identity model, equipped with a smooth
  positive measure, let \(E\) be a finite-dimensional Hilbert space, and let
  \(K\subset\operatorname{int}Q\subset Q\subset U\), with \(K,Q\) compact and
  \(U\) open.  Suppose the \(E\)-valued maps \(u_n\) are locally Sobolev on
  \(U\), uniformly \(W^{1,2}\)-bounded on \(Q\), and define classes in
  \(L^2(K;E)\).  Then these \(L^2(K;E)\)-classes lie in one compact subset of
  \(L^2(K;E)\).
proof:
  First prove that [the \(L^2(K;E)\)-classes form a totally bounded set](lean:JJMath.Uniformization.localRellich_chartwise_totallyBounded_range_of_memLp)
  by the chartwise Euclidean Rellich argument.  Then take the closure of this
  range in \(L^2(K;E)\); total boundedness and completeness make that closure
  compact.
-/
theorem localRellich_chartwise_compact_containment_of_memLp
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [R1Space X] [T2Space X]
    [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [IsIdentityManifoldModel H I] [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := I) X E)]
    [TopologicalSpace.PseudoMetrizableSpace
      (ManifoldDifferentialTotalSpace (I := I) X E)]
    {g : SmoothRiemannianMetricOnManifold I X} {μ : Measure X}
    (hμ : SmoothPositiveMeasureOnManifold (I := I) μ)
    {K Q U : Set X} (hK : IsCompact K) (hKQ : K ⊆ interior Q)
    (hQU : Q ⊆ U) (hQ : IsCompact Q) (hU_open : IsOpen U)
    (u : ℕ → X → E) (du : ℕ → ManifoldDifferentialField I X E)
    (hlocal : ∀ n : ℕ,
      IsLocalSobolevH1OnManifoldWithValues (I := I) g μ U (u n) (du n))
    (hbounded : BoundedInLocalSobolevH1OnManifoldWithValues (I := I) g μ Q u du)
    (hmemK : ∀ n : ℕ, MemLp (u n) 2 (μ.restrict K)) :
    ∃ S : Set (Lp E 2 (μ.restrict K)),
      IsCompact S ∧ ∀ n : ℕ, (hmemK n).toLp (u n) ∈ S := by
  exact l2TotallyBoundedRange_compact_containment_on_set_with_values
    u hmemK
    (localRellich_chartwise_totallyBounded_range_of_memLp
      hμ hK hKQ hQU hQ hU_open u du hlocal hbounded hmemK)

/--
%%handwave
name:
  Chartwise Euclidean compact containment globalizes on manifolds
statement:
  Let \(M\) be a finite-dimensional Riemannian manifold modeled by the
  ordinary real identity model, equipped with a smooth
  positive measure, let \(E\) be a finite-dimensional Hilbert space, and let
  \(K\subset\operatorname{int}Q\subset Q\subset U\), with \(K,Q\) compact and
  \(U\) open.  If \(u_n:U\to E\) are uniformly bounded in \(W^{1,2}(Q;E)\),
  then their \(L^2(K;E)\)-classes are defined and all lie in one compact
  subset of \(L^2(K;E)\).
proof:
  First prove that every selected subsequence has [a Cauchy subsubsequence](lean:JJMath.Uniformization.localRellich_chartwise_cauchy_subsequence_of_memLp)
  in \(L^2(K;E)\).  The sequential criterion gives total boundedness of the
  range of the \(L^2(K;E)\)-classes, and its closure is compact because
  \(L^2(K;E)\) is complete.
-/
theorem localRellich_compact_containment_from_chartwise_euclidean
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [R1Space X] [T2Space X]
    [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [IsIdentityManifoldModel H I] [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := I) X E)]
    [TopologicalSpace.PseudoMetrizableSpace
      (ManifoldDifferentialTotalSpace (I := I) X E)]
    {g : SmoothRiemannianMetricOnManifold I X} {μ : Measure X}
    (hμ : SmoothPositiveMeasureOnManifold (I := I) μ)
    {K Q U : Set X} (hK : IsCompact K) (hKQ : K ⊆ interior Q)
    (hQU : Q ⊆ U) (hQ : IsCompact Q) (hU_open : IsOpen U)
    (u : ℕ → X → E) (du : ℕ → ManifoldDifferentialField I X E)
    (hlocal : ∀ n : ℕ,
      IsLocalSobolevH1OnManifoldWithValues (I := I) g μ U (u n) (du n))
    (hbounded : BoundedInLocalSobolevH1OnManifoldWithValues (I := I) g μ Q u du) :
    ∃ (hmemK : ∀ n : ℕ, MemLp (u n) 2 (μ.restrict K))
      (S : Set (Lp E 2 (μ.restrict K))),
        IsCompact S ∧ ∀ n : ℕ, (hmemK n).toLp (u n) ∈ S := by
  have hKU : K ⊆ U := hKQ.trans (interior_subset.trans hQU)
  have hmemK : ∀ n : ℕ, MemLp (u n) 2 (μ.restrict K) := by
    intro n
    exact ((hlocal n).2 K hK hKU).1.memLp_trivial
  rcases localRellich_chartwise_compact_containment_of_memLp
      hμ hK hKQ hQU hQ hU_open u du hlocal hbounded hmemK with
    ⟨S, hS, hS_mem⟩
  exact ⟨hmemK, S, hS, hS_mem⟩

/--
%%handwave
name:
  Chartwise Euclidean Rellich globalizes on manifolds
statement:
  Let \(M\) be a finite-dimensional Riemannian manifold modeled by the
  ordinary real identity model, equipped with a smooth
  positive measure, let \(E\) be a finite-dimensional Hilbert space, and let
  \(K\subset\operatorname{int}Q\subset Q\subset U\) with \(K,Q\) compact and
  \(U\) open.  If \(u_n:U\to E\) are uniformly bounded in \(W^{1,2}(Q;E)\),
  then a subsequence converges strongly in \(L^2(K;E)\).
proof:
  The local Sobolev hypotheses give \(L^2(K;E)\)-classes.  Apply [the finite chart diagonal Cauchy extraction](lean:JJMath.Uniformization.localRellich_chartwise_cauchy_subsequence_of_memLp)
  to the original sequence.  Completeness of \(L^2(K;E)\) turns the Cauchy
  subsequence into a strongly convergent subsequence.
-/
theorem localRellich_subsequence_on_compact_from_chartwise_euclidean
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [R1Space X] [T2Space X]
    [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [IsIdentityManifoldModel H I] [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := I) X E)]
    [TopologicalSpace.PseudoMetrizableSpace
      (ManifoldDifferentialTotalSpace (I := I) X E)]
    {g : SmoothRiemannianMetricOnManifold I X} {μ : Measure X}
    (hμ : SmoothPositiveMeasureOnManifold (I := I) μ)
    {K Q U : Set X} (hK : IsCompact K) (hKQ : K ⊆ interior Q)
    (hQU : Q ⊆ U) (hQ : IsCompact Q) (hU_open : IsOpen U)
    (u : ℕ → X → E) (du : ℕ → ManifoldDifferentialField I X E)
    (hlocal : ∀ n : ℕ,
      IsLocalSobolevH1OnManifoldWithValues (I := I) g μ U (u n) (du n))
    (hbounded : BoundedInLocalSobolevH1OnManifoldWithValues (I := I) g μ Q u du) :
    ∃ (uLim : X → E) (φ : ℕ → ℕ),
      StrictMono φ ∧
        TendstoInLocalL2OnManifoldWithValues μ K (fun n x ↦ u (φ n) x) uLim := by
  have hKU : K ⊆ U := hKQ.trans (interior_subset.trans hQU)
  have hmemK : ∀ n : ℕ, MemLp (u n) 2 (μ.restrict K) := by
    intro n
    exact ((hlocal n).2 K hK hKU).1.memLp_trivial
  rcases localRellich_chartwise_cauchy_subsequence_of_memLp
      hμ hK hKQ hQU hQ hU_open u du hlocal hbounded hmemK (fun n : ℕ ↦ n) with
    ⟨φ, hφ, hφ_cauchy⟩
  rcases cauchySeq_tendsto_of_complete hφ_cauchy with ⟨a, ha⟩
  refine ⟨(a : X → E), φ, hφ, ?_⟩
  dsimp [TendstoInLocalL2OnManifoldWithValues]
  have ha' :
      Filter.Tendsto (fun n : ℕ ↦ (hmemK (φ n)).toLp (u (φ n)))
        Filter.atTop (𝓝 ((Lp.memLp a).toLp (a : X → E))) := by
    simpa [Lp.toLp_coeFn] using ha
  exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (μ := μ.restrict K) (p := 2)
    (fun n : ℕ ↦ u (φ n)) (fun n : ℕ ↦ hmemK (φ n))
    (a : X → E) (Lp.memLp a)).mp ha'

/--
%%handwave
name:
  Local Rellich compactness on manifolds
statement:
  Let \(M\) be a finite-dimensional Riemannian manifold modeled by the
  ordinary real identity model, equipped with a smooth
  positive measure, let \(E\) be a finite-dimensional Hilbert space, and let
  \(K\subset\operatorname{int}Q\subset Q\subset U\) with \(K,Q\) compact and
  \(U\) open.  If \(u_n:U\to E\) are uniformly bounded in \(W^{1,2}(Q;E)\),
  then a subsequence converges strongly in \(L^2(K;E)\).
proof:
  Apply [chartwise Euclidean Rellich globalizes on manifolds](lean:JJMath.Uniformization.localRellich_subsequence_on_compact_from_chartwise_euclidean).
tags:
  milestone
-/
theorem localRellich_subsequence_on_compact
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [R1Space X] [T2Space X]
    [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [IsIdentityManifoldModel H I] [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := I) X E)]
    [TopologicalSpace.PseudoMetrizableSpace
      (ManifoldDifferentialTotalSpace (I := I) X E)]
    {g : SmoothRiemannianMetricOnManifold I X} {μ : Measure X}
    (hμ : SmoothPositiveMeasureOnManifold (I := I) μ)
    {K Q U : Set X} (hK : IsCompact K) (hKQ : K ⊆ interior Q)
    (hQU : Q ⊆ U) (hQ : IsCompact Q) (hU_open : IsOpen U)
    (u : ℕ → X → E) (du : ℕ → ManifoldDifferentialField I X E)
    (hlocal : ∀ n : ℕ,
      IsLocalSobolevH1OnManifoldWithValues (I := I) g μ U (u n) (du n))
    (hbounded : BoundedInLocalSobolevH1OnManifoldWithValues (I := I) g μ Q u du) :
    ∃ (uLim : X → E) (φ : ℕ → ℕ),
      StrictMono φ ∧
        TendstoInLocalL2OnManifoldWithValues μ K (fun n x ↦ u (φ n) x) uLim := by
  exact
    localRellich_subsequence_on_compact_from_chartwise_euclidean
      hμ hK hKQ hQU hQ hU_open u du hlocal hbounded

/--
%%handwave
name:
  Local Rellich compactness with an \(L^2\)-representative
statement:
  Under the local Rellich hypotheses, one can choose the subsequential limit
  as an honest \(L^2\) representative on the compact set where convergence is
  asserted.
proof:
  Repeat the final Rellich extraction.  The Cauchy subsequence converges in
  the complete \(L^2(K)\) space to an \(L^2\)-class, and the chosen
  representative of that class comes with square-integrability on \(K\).
-/
theorem localRellich_subsequence_on_compact_with_memLp
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [R1Space X] [T2Space X]
    [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [IsManifold I 1 X]
    [IsIdentityManifoldModel H I] [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := I) X E)]
    [TopologicalSpace.PseudoMetrizableSpace
      (ManifoldDifferentialTotalSpace (I := I) X E)]
    {g : SmoothRiemannianMetricOnManifold I X} {μ : Measure X}
    (hμ : SmoothPositiveMeasureOnManifold (I := I) μ)
    {K Q U : Set X} (hK : IsCompact K) (hKQ : K ⊆ interior Q)
    (hQU : Q ⊆ U) (hQ : IsCompact Q) (hU_open : IsOpen U)
    (u : ℕ → X → E) (du : ℕ → ManifoldDifferentialField I X E)
    (hlocal : ∀ n : ℕ,
      IsLocalSobolevH1OnManifoldWithValues (I := I) g μ U (u n) (du n))
    (hbounded : BoundedInLocalSobolevH1OnManifoldWithValues (I := I) g μ Q u du) :
    ∃ (uLim : X → E) (φ : ℕ → ℕ),
      MemLp uLim 2 (μ.restrict K) ∧ StrictMono φ ∧
        TendstoInLocalL2OnManifoldWithValues μ K (fun n x ↦ u (φ n) x) uLim := by
  have hKU : K ⊆ U := hKQ.trans (interior_subset.trans hQU)
  have hmemK : ∀ n : ℕ, MemLp (u n) 2 (μ.restrict K) := by
    intro n
    exact ((hlocal n).2 K hK hKU).1.memLp_trivial
  rcases localRellich_chartwise_cauchy_subsequence_of_memLp
      hμ hK hKQ hQU hQ hU_open u du hlocal hbounded hmemK (fun n : ℕ ↦ n) with
    ⟨φ, hφ, hφ_cauchy⟩
  rcases cauchySeq_tendsto_of_complete hφ_cauchy with ⟨a, ha⟩
  refine ⟨(a : X → E), φ, Lp.memLp a, hφ, ?_⟩
  dsimp [TendstoInLocalL2OnManifoldWithValues]
  have ha' :
      Filter.Tendsto (fun n : ℕ ↦ (hmemK (φ n)).toLp (u (φ n)))
        Filter.atTop (𝓝 ((Lp.memLp a).toLp (a : X → E))) := by
    simpa [Lp.toLp_coeFn] using ha
  exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (μ := μ.restrict K) (p := 2)
    (fun n : ℕ ↦ u (φ n)) (fun n : ℕ ↦ hmemK (φ n))
    (a : X → E) (Lp.memLp a)).mp ha'

/--
%%handwave
name:
  Agreement of almost-everywhere constants on a positive overlap
statement:
  If \(u=a\) almost everywhere on \(s\), \(u=b\) almost everywhere on \(t\),
  and \(\mu(s\cap t)>0\), then \(a=b\).
proof:
  Restrict both equalities to the intersection. Distinct constants would
  imply false almost everywhere on a set of positive measure.
-/
private theorem ae_eq_const_on_positive_inter_eq_of_measure
    {X : Type} [MeasurableSpace X] {μ : Measure X}
    {s t : Set X} {u : X → ℝ} {a b : ℝ}
    (hs : ∀ᵐ x ∂μ.restrict s, u x = a)
    (ht : ∀ᵐ x ∂μ.restrict t, u x = b)
    (hst_pos : μ (s ∩ t) ≠ 0) :
    a = b := by
  have hs_inter : ∀ᵐ x ∂μ.restrict (s ∩ t), u x = a :=
    ae_restrict_of_ae_restrict_of_subset Set.inter_subset_left hs
  have ht_inter : ∀ᵐ x ∂μ.restrict (s ∩ t), u x = b :=
    ae_restrict_of_ae_restrict_of_subset Set.inter_subset_right ht
  have hab_ae : ∀ᵐ _x ∂μ.restrict (s ∩ t), a = b := by
    filter_upwards [hs_inter, ht_inter] with x hxa hxb
    exact hxa.symm.trans hxb
  by_contra hab
  have hfalse : ∀ᵐ _x ∂μ.restrict (s ∩ t), False :=
    hab_ae.mono fun _x hx ↦ hab hx
  have hbot : ae (μ.restrict (s ∩ t)) = ⊥ :=
    Filter.eventually_false_iff_eq_bot.mp hfalse
  have hnebot : (ae (μ.restrict (s ∩ t))).NeBot :=
    ae_restrict_neBot.2 hst_pos
  exact hnebot.ne hbot

/--
%%handwave
name:
  Local almost-everywhere constants glue on preconnected Euclidean regions
statement:
  Let \(U\) be a preconnected open subset of a finite-dimensional real
  coordinate space.  If a function is almost everywhere constant in a
  neighborhood of every point of \(U\), then it is equal almost everywhere on
  \(U\) to one constant.
proof:
  Lebesgue measure gives positive measure to every nonempty open set.  Hence
  two local constants agree whenever their neighborhoods overlap.  The
  relation saying that two points have the same local constant is locally
  true, symmetric, and transitive, so preconnectedness propagates it through
  \(U\).  A countable subcover of the local neighborhoods then combines the
  local almost-everywhere equalities over \(U\).
-/
theorem euclidean_ae_local_constants_glue_on_preconnected
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {U : Set H} {u : H → ℝ}
    (_hU_open : IsOpen U) (hU_preconnected : IsPreconnected U)
    (hlocal_const :
      ∀ x ∈ U, ∃ V : Set H, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
        ∃ a : ℝ, ∀ᵐ y ∂MeasureTheory.volume.restrict V, u y = a) :
    ∃ a : ℝ, ∀ᵐ x ∂MeasureTheory.volume.restrict U, u x = a := by
  classical
  haveI : ProperSpace H := FiniteDimensional.proper ℝ H
  by_cases hU_nonempty : U.Nonempty
  · rcases hU_nonempty with ⟨x₀, hx₀U⟩
    let LocalConstAt : H → ℝ → Prop :=
      fun x a ↦ ∃ V : Set H, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
        ∀ᵐ y ∂MeasureTheory.volume.restrict V, u y = a
    have hLocal_exists : ∀ x ∈ U, ∃ a : ℝ, LocalConstAt x a := by
      intro x hxU
      rcases hlocal_const x hxU with ⟨V, hV_open, hxV, hVU, a, ha⟩
      exact ⟨a, V, hV_open, hxV, hVU, ha⟩
    let SameLocalConstant : H → H → Prop :=
      fun x y ↦ ∀ a b : ℝ, LocalConstAt x a → LocalConstAt y b → a = b
    have hsame_near :
        ∀ x ∈ U, ∀ᶠ y in 𝓝[U] x, SameLocalConstant x y := by
      intro x hxU
      rcases hlocal_const x hxU with ⟨V₀, hV₀_open, hxV₀, hV₀U, c, hc⟩
      filter_upwards [mem_nhdsWithin_of_mem_nhds (hV₀_open.mem_nhds hxV₀)] with y hyV₀
      intro a b hxa hyb
      rcases hxa with ⟨Vx, hVx_open, hxVx, _hVxU, hVx_ae⟩
      rcases hyb with ⟨Vy, hVy_open, hyVy, _hVyU, hVy_ae⟩
      have hx_inter_nonempty : (Vx ∩ V₀).Nonempty := ⟨x, hxVx, hxV₀⟩
      have hy_inter_nonempty : (V₀ ∩ Vy).Nonempty := ⟨y, hyV₀, hyVy⟩
      have hx_inter_pos : volume (Vx ∩ V₀) ≠ 0 :=
        ne_of_gt <| (hVx_open.inter hV₀_open).measure_pos
          (MeasureTheory.volume : Measure H) hx_inter_nonempty
      have hy_inter_pos : volume (V₀ ∩ Vy) ≠ 0 :=
        ne_of_gt <| (hV₀_open.inter hVy_open).measure_pos
          (MeasureTheory.volume : Measure H) hy_inter_nonempty
      have hac : a = c :=
        ae_eq_const_on_positive_inter_eq_of_measure hVx_ae hc hx_inter_pos
      have hcb : c = b :=
        ae_eq_const_on_positive_inter_eq_of_measure hc hVy_ae hy_inter_pos
      exact hac.trans hcb
    have hsame_trans :
        ∀ x y z, x ∈ U → y ∈ U → z ∈ U →
          SameLocalConstant x y → SameLocalConstant y z → SameLocalConstant x z := by
      intro x y z hxU hyU hzU hxy hyz a c hxa hzc
      rcases hLocal_exists y hyU with ⟨b, hyb⟩
      exact (hxy a b hxa hyb).trans (hyz b c hyb hzc)
    have hsame_symm :
        ∀ x y, x ∈ U → y ∈ U →
          SameLocalConstant x y → SameLocalConstant y x := by
      intro x y hxU hyU hxy a b hya hxb
      exact (hxy b a hxb hya).symm
    have hsame_all :
        ∀ x ∈ U, SameLocalConstant x₀ x := by
      intro x hxU
      exact hU_preconnected.induction₂ SameLocalConstant
        hsame_near hsame_trans hsame_symm hx₀U hxU
    rcases hLocal_exists x₀ hx₀U with ⟨a₀, hx₀a₀⟩
    let LocalData : Type _ :=
      {p : H × Set H × ℝ //
        p.1 ∈ U ∧ IsOpen p.2.1 ∧ p.1 ∈ p.2.1 ∧ p.2.1 ⊆ U ∧
          ∀ᵐ y ∂MeasureTheory.volume.restrict p.2.1, u y = p.2.2}
    let localCenter : LocalData → H := fun p ↦ p.val.1
    let localSet : LocalData → Set H := fun p ↦ p.val.2.1
    let localConst : LocalData → ℝ := fun p ↦ p.val.2.2
    have hlocalSet_open : ∀ p : LocalData, IsOpen (localSet p) := by
      intro p
      exact p.property.2.1
    have hcover : U ⊆ ⋃ p : LocalData, localSet p := by
      intro x hxU
      rcases hlocal_const x hxU with ⟨V, hV_open, hxV, hVU, a, ha⟩
      refine Set.mem_iUnion.2 ?_
      exact ⟨⟨(x, V, a), hxU, hV_open, hxV, hVU, ha⟩, hxV⟩
    have hU_lindelof : IsLindelof U :=
      HereditarilyLindelofSpace.isLindelof U
    rcases hU_lindelof.elim_countable_subcover localSet hlocalSet_open hcover with
      ⟨T, hT_countable, hT_cover⟩
    refine ⟨a₀, ?_⟩
    have hcover_ae :
        ∀ᵐ x ∂MeasureTheory.volume.restrict (⋃ p ∈ T, localSet p),
          u x = a₀ := by
      rw [ae_restrict_biUnion_iff localSet hT_countable (fun x ↦ u x = a₀)]
      intro p hpT
      have hpU : localCenter p ∈ U := p.property.1
      have hpLocal : LocalConstAt (localCenter p) (localConst p) :=
        ⟨localSet p, p.property.2.1, p.property.2.2.1,
          p.property.2.2.2.1, p.property.2.2.2.2⟩
      have hconst_eq : a₀ = localConst p :=
        hsame_all (localCenter p) hpU a₀ (localConst p) hx₀a₀ hpLocal
      filter_upwards [p.property.2.2.2.2] with x hx
      rwa [hconst_eq]
    exact ae_restrict_of_ae_restrict_of_subset hT_cover hcover_ae
  · refine ⟨0, ?_⟩
    have hU_empty : U = ∅ := Set.not_nonempty_iff_eq_empty.mp hU_nonempty
    simp [hU_empty]

/--
%%handwave
name:
  Zero translation increments force a coordinate-box constant
statement:
  Let \(D\) be a coordinate box contained in a measurable ambient set \(P\).
  If \(u\in L^2(P)\), and every displacement appearing between two points of
  \(D\) has zero \(L^2(P)\)-translation increment, then \(u\) is equal almost
  everywhere on \(D\) to its average over \(D\).
proof:
  The variance of \(u\) from its box average is bounded by the pairwise
  oscillation on \(D\).  The pairwise oscillation is rewritten by the shear
  \((h,x)\mapsto(x,x+h)\) as an integral of translated differences over the
  difference body of \(D\).  The translation hypothesis makes this integral
  zero, so the variance is zero, and hence \(u\) equals its average almost
  everywhere on the box.
-/
theorem euclideanPiBox_ae_const_of_zero_translation_eLpNorm
    {d : ℕ} {P : Set (Fin d → ℝ)} {u : (Fin d → ℝ) → ℝ}
    {D : BoxIntegral.Box (Fin d)}
    (hu : MemLp u 2 (MeasureTheory.volume.restrict P))
    (hD_subsetP : (D : Set (Fin d → ℝ)) ⊆ P)
    (hD_posP : 0 < (MeasureTheory.volume.restrict P)
      (D : Set (Fin d → ℝ)))
    (hD_finiteP : (MeasureTheory.volume.restrict P)
      (D : Set (Fin d → ℝ)) ≠ (⊤ : ℝ≥0∞))
    (htranslation :
      ∀ h ∈ regularCubeBoxDifferenceBody D,
        eLpNorm (fun z ↦ u (z + h) - u z) 2
          (MeasureTheory.volume.restrict P) = 0) :
    ∃ a : ℝ,
      ∀ᵐ y ∂MeasureTheory.volume.restrict (D : Set (Fin d → ℝ)), u y = a := by
  classical
  let U : ℕ → (Fin d → ℝ) → ℝ := fun _ ↦ u
  let D₁ : Fin 1 → BoxIntegral.Box (Fin d) := fun _ ↦ D
  let i₀ : Fin 1 := 0
  have hmemP : ∀ n : ℕ, MemLp (U n) 2 (MeasureTheory.volume.restrict P) :=
    fun _ ↦ hu
  have hD_subsetP₁ : ∀ i : Fin 1, (D₁ i : Set (Fin d → ℝ)) ⊆ P := by
    intro i
    simpa [D₁] using hD_subsetP
  have hD_posP₁ :
      ∀ i : Fin 1, 0 < (MeasureTheory.volume.restrict P)
        (D₁ i : Set (Fin d → ℝ)) := by
    intro i
    simpa [D₁] using hD_posP
  have hD_finiteP₁ :
      ∀ i : Fin 1, (MeasureTheory.volume.restrict P)
        (D₁ i : Set (Fin d → ℝ)) ≠ (⊤ : ℝ≥0∞) := by
    intro i
    simpa [D₁] using hD_finiteP
  have hpair_le :
      regularCubeBoxPairwiseOscillation U D₁ 0 i₀ ≤
        (MeasureTheory.volume (D₁ i₀ : Set (Fin d → ℝ)))⁻¹ *
          ∫⁻ h in regularCubeBoxDifferenceBody (D₁ i₀),
            ∫⁻ x in P, ‖U 0 (x + h) - U 0 x‖ₑ ^ (2 : ℝ)
              ∂MeasureTheory.volume ∂MeasureTheory.volume :=
    regularCubeBoxPairwiseOscillation_le_differenceBody_lintegral_translation
      U hmemP D₁ hD_subsetP₁ 0 i₀
  have hinner_zero :
      ∀ h ∈ regularCubeBoxDifferenceBody D,
        ∫⁻ x in P, ‖u (x + h) - u x‖ₑ ^ (2 : ℝ)
          ∂MeasureTheory.volume = 0 := by
    intro h hh
    have hle :
        ∫⁻ x, ‖u (x + h) - u x‖ₑ ^ (2 : ℝ)
            ∂MeasureTheory.volume.restrict P ≤ 0 := by
      have hnorm_le :
          eLpNorm (fun z ↦ u (z + h) - u z) 2
              (MeasureTheory.volume.restrict P) ≤ 0 := by
        simpa [htranslation h hh] using
          (le_of_eq (htranslation h hh) : eLpNorm
            (fun z ↦ u (z + h) - u z) 2
              (MeasureTheory.volume.restrict P) ≤ 0)
      simpa using
        lintegral_sq_le_of_eLpNorm_two_le
          (μ := MeasureTheory.volume.restrict P)
          (f := fun z ↦ u (z + h) - u z)
          (η := 0) hnorm_le
    exact le_antisymm (by simpa using hle) bot_le
  have houter_zero :
      ∫⁻ h in regularCubeBoxDifferenceBody (D₁ i₀),
        ∫⁻ x in P, ‖U 0 (x + h) - U 0 x‖ₑ ^ (2 : ℝ)
          ∂MeasureTheory.volume ∂MeasureTheory.volume = 0 := by
    have hzero_ae :
        (fun h : Fin d → ℝ ↦
          ∫⁻ x in P, ‖U 0 (x + h) - U 0 x‖ₑ ^ (2 : ℝ)
            ∂MeasureTheory.volume)
          =ᵐ[MeasureTheory.volume.restrict
              (regularCubeBoxDifferenceBody (D₁ i₀))]
          fun _ ↦ 0 := by
      filter_upwards
        [ae_restrict_mem (regularCubeBoxDifferenceBody_measurableSet (D₁ i₀))]
        with h hh
      simpa [U, D₁] using hinner_zero h hh
    exact lintegral_eq_zero_of_ae_eq_zero hzero_ae
  have hpair_zero : regularCubeBoxPairwiseOscillation U D₁ 0 i₀ = 0 := by
    apply le_antisymm
    · calc
        regularCubeBoxPairwiseOscillation U D₁ 0 i₀
            ≤ (MeasureTheory.volume (D₁ i₀ : Set (Fin d → ℝ)))⁻¹ *
                ∫⁻ h in regularCubeBoxDifferenceBody (D₁ i₀),
                  ∫⁻ x in P, ‖U 0 (x + h) - U 0 x‖ₑ ^ (2 : ℝ)
                    ∂MeasureTheory.volume ∂MeasureTheory.volume := hpair_le
        _ = 0 := by rw [houter_zero, mul_zero]
    · exact bot_le
  have hvar_le :
      ∫⁻ x in (D₁ i₀ : Set (Fin d → ℝ)),
        ‖U 0 x - regularCubeBoxAverageCoeff U D₁ 0 i₀‖ₑ ^ (2 : ℝ)
          ∂MeasureTheory.volume ≤
        regularCubeBoxPairwiseOscillation U D₁ 0 i₀ :=
    regularCubeBoxAverageCoeff_lintegral_sq_le_pairwiseOscillation
      U hmemP D₁ hD_subsetP₁ hD_posP₁ hD_finiteP₁ 0 i₀
  let a : ℝ := regularCubeBoxAverageCoeff U D₁ 0 i₀
  refine ⟨a, ?_⟩
  have hvar_zero :
      ∫⁻ x, ‖u x - a‖ₑ ^ (2 : ℝ)
          ∂MeasureTheory.volume.restrict (D : Set (Fin d → ℝ)) = 0 := by
    apply le_antisymm
    · simpa [U, D₁, i₀, a] using hvar_le.trans_eq hpair_zero
    · exact bot_le
  have hμDP :
      MeasureTheory.volume.restrict (D : Set (Fin d → ℝ)) ≤
        MeasureTheory.volume.restrict P :=
    Measure.restrict_mono hD_subsetP le_rfl
  have huD : MemLp u 2
      (MeasureTheory.volume.restrict (D : Set (Fin d → ℝ))) :=
    hu.mono_measure hμDP
  have hdiff_ae :
      AEMeasurable (fun y : Fin d → ℝ ↦ u y - a)
        (MeasureTheory.volume.restrict (D : Set (Fin d → ℝ))) :=
    huD.aestronglyMeasurable.aemeasurable.sub aemeasurable_const
  have hsq_zero :
      (fun y : Fin d → ℝ ↦ ‖u y - a‖ₑ ^ (2 : ℝ))
        =ᵐ[MeasureTheory.volume.restrict (D : Set (Fin d → ℝ))]
        fun _ ↦ 0 :=
    (lintegral_eq_zero_iff' (hdiff_ae.enorm.pow_const (2 : ℝ))).1 hvar_zero
  filter_upwards [hsq_zero] with y hy
  have hnorm_zero : ‖u y - a‖ₑ = 0 := by
    simpa [ENNReal.rpow_eq_zero_iff] using hy
  exact sub_eq_zero.mp (by simpa using (enorm_eq_zero.mp hnorm_zero))

/--
%%handwave
name:
  Positivity of the volume of a Euclidean box
statement:
  A box in \(\mathbb R^d\) with positive side lengths has positive Lebesgue
  volume.
proof:
  Its volume is the product of the positive side lengths.
-/
private theorem euclideanPiBox_volume_pos
    {d : ℕ} (D : BoxIntegral.Box (Fin d)) :
    0 < MeasureTheory.volume (D : Set (Fin d → ℝ)) := by
  classical
  have htoReal_pos :
      0 < (MeasureTheory.volume (D : Set (Fin d → ℝ))).toReal := by
    rw [BoxIntegral.Box.volume_apply']
    exact Finset.prod_pos fun i _ ↦ sub_pos.mpr (D.lower_lt_upper i)
  exact (ENNReal.toReal_pos_iff.mp htoReal_pos).1

/--
%%handwave
name:
  Finiteness of the volume of a Euclidean box
statement:
  Every bounded coordinate box in \(\mathbb R^d\) has finite Lebesgue volume.
proof:
  Its volume is a finite product of finite side lengths.
-/
private theorem euclideanPiBox_volume_ne_top
    {d : ℕ} (D : BoxIntegral.Box (Fin d)) :
    MeasureTheory.volume (D : Set (Fin d → ℝ)) ≠ (⊤ : ℝ≥0∞) :=
  ne_of_lt (D.measure_coe_lt_top MeasureTheory.volume)

/--
%%handwave
name:
  Local zero translation increments give coordinate-neighborhood constants
statement:
  Let \(U\subset \mathbb R^d\) be open and let \(u\in L^2(U)\).  Suppose
  that for every compact \(K\subset U\), all sufficiently small translations
  have zero \(L^2(K)\)-difference.  Then every point of \(U\) has an open
  coordinate-box neighborhood on which \(u\) is equal almost everywhere to a
  constant.
proof:
  Around the point choose a closed ball compactly contained in \(U\).  The
  translation hypothesis gives a radius of exact \(L^2\)-invariance on that
  closed ball.  Choose a smaller coordinate box whose difference body lies in
  that translation radius and whose closure lies in the ball.  The box
  variance estimate then forces \(u\) to equal its box average almost
  everywhere on the box, hence also on its open interior.
-/
theorem ae_local_const_of_zero_local_translation_eLpNorm_on_open_pi
    {d : ℕ} {Ω : Set (Fin d → ℝ)} {u : (Fin d → ℝ) → ℝ}
    (hΩ_open : IsOpen Ω)
    (hu : MemLp u 2 (MeasureTheory.volume.restrict Ω))
    (htranslation :
      ∀ K : Set (Fin d → ℝ), IsCompact K → K ⊆ Ω →
        ∃ ρ : ℝ, 0 < ρ ∧ ∀ h : Fin d → ℝ, ‖h‖ < ρ →
          eLpNorm (fun z ↦ u (z + h) - u z) 2
            (MeasureTheory.volume.restrict K) = 0) :
    ∀ x ∈ Ω,
      ∃ V : Set (Fin d → ℝ), IsOpen V ∧ x ∈ V ∧ V ⊆ Ω ∧
        ∃ a : ℝ, ∀ᵐ y ∂MeasureTheory.volume.restrict V, u y = a := by
  classical
  intro x hxΩ
  rcases Metric.isOpen_iff.mp hΩ_open x hxΩ with
    ⟨R₀, hR₀_pos, hball_subset⟩
  let R : ℝ := R₀ / 2
  have hR_pos : 0 < R := by
    dsimp [R]
    positivity
  have hR_lt_R₀ : R < R₀ := by
    dsimp [R]
    linarith
  let P : Set (Fin d → ℝ) := Metric.closedBall x R
  have hP_compact : IsCompact P := by
    dsimp [P]
    exact isCompact_closedBall x R
  have hP_subsetΩ : P ⊆ Ω := by
    intro y hy
    apply hball_subset
    have hydist : dist y x ≤ R := by
      simpa [P, Metric.mem_closedBall] using hy
    exact lt_of_le_of_lt hydist hR_lt_R₀
  rcases htranslation P hP_compact hP_subsetΩ with
    ⟨ρ, hρ_pos, hρ⟩
  let s : ℝ := min (R / 2) (ρ / 4)
  have hs_pos : 0 < s := by
    dsimp [s]
    exact lt_min (by positivity) (by positivity)
  have hs_le_R_half : s ≤ R / 2 := by
    dsimp [s]
    exact min_le_left _ _
  have hs_le_R : s ≤ R := by
    linarith
  have htwo_s_lt_ρ : 2 * s < ρ := by
    have hs_le_ρ_quarter : s ≤ ρ / 4 := by
      dsimp [s]
      exact min_le_right _ _
    linarith
  let D : BoxIntegral.Box (Fin d) :=
    { lower := fun i ↦ x i - s
      upper := fun i ↦ x i + s
      lower_lt_upper := by
        intro i
        linarith }
  let V : Set (Fin d → ℝ) := BoxIntegral.Box.Ioo D
  have hV_open : IsOpen V := by
    dsimp [V, BoxIntegral.Box.Ioo]
    exact isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_Ioo
  have hxV : x ∈ V := by
    intro i hi
    dsimp [V, D, BoxIntegral.Box.Ioo]
    constructor <;> linarith
  have hD_subsetP : (D : Set (Fin d → ℝ)) ⊆ P := by
    intro y hy
    have hynorm_le : ‖y - x‖ ≤ s := by
      rw [pi_norm_le_iff_of_nonneg hs_pos.le]
      intro i
      have hyi := hy i
      rw [Pi.sub_apply, Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [hyi.1], by linarith [hyi.2]⟩
    have hdist_le : dist y x ≤ R := by
      calc
        dist y x = ‖y - x‖ := dist_eq_norm y x
        _ ≤ s := hynorm_le
        _ ≤ R := hs_le_R
    simpa [P, Metric.mem_closedBall] using hdist_le
  have hV_subsetΩ : V ⊆ Ω :=
    (BoxIntegral.Box.Ioo_subset_coe D).trans (hD_subsetP.trans hP_subsetΩ)
  have huP : MemLp u 2 (MeasureTheory.volume.restrict P) :=
    hu.mono_measure (Measure.restrict_mono hP_subsetΩ le_rfl)
  have hD_posP :
      0 < (MeasureTheory.volume.restrict P) (D : Set (Fin d → ℝ)) := by
    have hmeas :
        (MeasureTheory.volume.restrict P) (D : Set (Fin d → ℝ)) =
          MeasureTheory.volume (D : Set (Fin d → ℝ)) := by
      rw [Measure.restrict_apply (D.measurableSet_coe)]
      rw [Set.inter_eq_self_of_subset_left hD_subsetP]
    simpa [hmeas] using euclideanPiBox_volume_pos D
  have hD_finiteP :
      (MeasureTheory.volume.restrict P) (D : Set (Fin d → ℝ)) ≠
        (⊤ : ℝ≥0∞) := by
    have hmeas :
        (MeasureTheory.volume.restrict P) (D : Set (Fin d → ℝ)) =
          MeasureTheory.volume (D : Set (Fin d → ℝ)) := by
      rw [Measure.restrict_apply (D.measurableSet_coe)]
      rw [Set.inter_eq_self_of_subset_left hD_subsetP]
    simpa [hmeas] using euclideanPiBox_volume_ne_top D
  have hdiff_small :
      ∀ h ∈ regularCubeBoxDifferenceBody D, ‖h‖ < ρ := by
    intro h hh
    have hcoord : ∀ i : Fin d, ‖h i‖ < 2 * s := by
      intro i
      have hhi :
          h i ∈ Set.Ioo (D.lower i - D.upper i)
            (D.upper i - D.lower i) := by
        rw [regularCubeBoxDifferenceBody_eq_pi_Ioo D] at hh
        exact hh i trivial
      have hhi' : h i ∈ Set.Ioo (-(2 * s)) (2 * s) := by
        constructor
        · have hleft : D.lower i - D.upper i = -(2 * s) := by
            dsimp [D]
            ring
          simpa [hleft] using hhi.1
        · have hright : D.upper i - D.lower i = 2 * s := by
            dsimp [D]
            ring
          simpa [hright] using hhi.2
      rw [Real.norm_eq_abs]
      exact abs_lt.mpr hhi'
    exact ((pi_norm_lt_iff (by linarith : 0 < 2 * s)).2 hcoord).trans htwo_s_lt_ρ
  have htranslationD :
      ∀ h ∈ regularCubeBoxDifferenceBody D,
        eLpNorm (fun z ↦ u (z + h) - u z) 2
          (MeasureTheory.volume.restrict P) = 0 := by
    intro h hh
    exact hρ h (hdiff_small h hh)
  rcases
    euclideanPiBox_ae_const_of_zero_translation_eLpNorm
      (P := P) (u := u) (D := D) huP hD_subsetP
      hD_posP hD_finiteP htranslationD with
    ⟨a, haD⟩
  refine ⟨V, hV_open, hxV, hV_subsetΩ, a, ?_⟩
  exact ae_restrict_of_ae_restrict_of_subset
    (BoxIntegral.Box.Ioo_subset_coe D) haD

/--
%%handwave
name:
  Local translation invariance gives neighborhood constants in a ball
statement:
  Let \(u\in L^2(B(c,r))\).  Suppose that on every compact subset of the ball
  there is a positive radius such that every translation shorter than that
  radius has zero \(L^2\)-difference from \(u\) on the compact set.  Then
  around every point of the ball there is an open neighborhood, still inside
  the ball, on which \(u\) is equal almost everywhere to one real constant.
proof:
  Choose a compact neighborhood of the point inside the ball.  The translation
  hypothesis gives exact \(L^2\)-invariance under all sufficiently small
  translations on that compact set.  On a smaller coordinate box, the
  pairwise oscillation estimate rewrites the variance from the box average as
  an integral of translated differences; this integral is zero.  Hence \(u\)
  agrees almost everywhere with the box average on the smaller neighborhood.
-/
theorem ae_local_const_of_zero_local_translation_eLpNorm_finiteDimensional
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {u : H → ℝ} {c : H} {r : ℝ}
    (_hr_pos : 0 < r)
    (hu : MemLp u 2 (MeasureTheory.volume.restrict (Metric.ball c r)))
    (htranslation :
      ∀ K : Set H, IsCompact K → K ⊆ Metric.ball c r →
        ∃ ρ : ℝ, 0 < ρ ∧ ∀ h : H, ‖h‖ < ρ →
          eLpNorm (fun z ↦ u (z + h) - u z) 2
            (MeasureTheory.volume.restrict K) = 0) :
    ∀ x ∈ Metric.ball c r,
      ∃ V : Set H, IsOpen V ∧ x ∈ V ∧ V ⊆ Metric.ball c r ∧
        ∃ a : ℝ, ∀ᵐ y ∂MeasureTheory.volume.restrict V, u y = a := by
  classical
  let ΩH : Set H := Metric.ball c r
  let d := Module.finrank ℝ H
  let Vcoord := Fin d → ℝ
  have hfinrank : Module.finrank ℝ H = Module.finrank ℝ Vcoord := by
    simp [Vcoord, d]
  let e : H ≃L[ℝ] Vcoord := ContinuousLinearEquiv.ofFinrankEq hfinrank
  let em : H ≃ᵐ Vcoord := e.toHomeomorph.toMeasurableEquiv
  let ΩV : Set Vcoord := e '' ΩH
  let v : Vcoord → ℝ := fun y ↦ u (e.symm y)
  let cμ : ℝ≥0 :=
    Measure.addHaarScalarFactor (volume : Measure H)
      ((volume : Measure Vcoord).map e.symm)
  have hcμ_pos : 0 < cμ := by
    exact Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure
      (volume : Measure H) ((volume : Measure Vcoord).map e.symm)
  have hcμ_ne : cμ ≠ 0 := ne_of_gt hcμ_pos
  have hμ :
      (volume : Measure H) =
        cμ • ((volume : Measure Vcoord).map e.symm) := by
    exact Measure.isAddLeftInvariant_eq_smul
      (volume : Measure H) ((volume : Measure Vcoord).map e.symm)
  have hmp0_symm :
      MeasurePreserving em.symm (volume : Measure Vcoord)
        ((volume : Measure Vcoord).map e.symm) := by
    refine ⟨em.symm.measurable, ?_⟩
    rfl
  have hΩV_open : IsOpen ΩV := by
    dsimp [ΩV, ΩH]
    exact e.isOpenMap _ Metric.isOpen_ball
  have himageΩ : em.symm '' ΩV = ΩH := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      rcases hy with ⟨x, hx, rfl⟩
      simpa [ΩH, ΩV, em] using hx
    · intro hz
      exact ⟨e z, ⟨z, hz, rfl⟩, by simp [em]⟩
  have hmpΩ_symm :
      MeasurePreserving em.symm
        ((volume : Measure Vcoord).restrict ΩV)
        (((volume : Measure Vcoord).map e.symm).restrict ΩH) := by
    have hraw :=
      hmp0_symm.restrict_image_emb em.symm.measurableEmbedding ΩV
    rwa [himageΩ] at hraw
  have hu_smul_map :
      MemLp u 2
        (cμ • (((volume : Measure Vcoord).map e.symm).restrict ΩH)) := by
    have hu' :
        MemLp u 2
          ((cμ • ((volume : Measure Vcoord).map e.symm)).restrict ΩH) := by
      simpa [ΩH, hμ] using hu
    simpa [Measure.restrict_smul] using hu'
  have hu_map :
      MemLp u 2 (((volume : Measure Vcoord).map e.symm).restrict ΩH) :=
    memLp_of_smul_measure_nnreal
      (μ := ((volume : Measure Vcoord).map e.symm).restrict ΩH)
      (c := cμ) hcμ_ne hu_smul_map
  have hv : MemLp v 2 ((volume : Measure Vcoord).restrict ΩV) := by
    simpa [v, em, Function.comp_def] using
      hu_map.comp_measurePreserving hmpΩ_symm
  have htranslationV :
      ∀ K : Set Vcoord, IsCompact K → K ⊆ ΩV →
        ∃ ρ : ℝ, 0 < ρ ∧ ∀ h : Vcoord, ‖h‖ < ρ →
          eLpNorm (fun z ↦ v (z + h) - v z) 2
            ((volume : Measure Vcoord).restrict K) = 0 := by
    intro K hK_compact hKΩ
    let KH : Set H := e.symm '' K
    have hKH_compact : IsCompact KH := by
      dsimp [KH]
      exact hK_compact.image e.symm.continuous
    have hKH_subset : KH ⊆ ΩH := by
      intro z hz
      rcases hz with ⟨y, hyK, rfl⟩
      have hyΩ : y ∈ ΩV := hKΩ hyK
      rcases hyΩ with ⟨x, hxΩ, rfl⟩
      simpa [ΩH] using hxΩ
    rcases htranslation KH hKH_compact hKH_subset with
      ⟨ρ, hρ_pos, hρ⟩
    let L : Vcoord →L[ℝ] H := (e.symm : Vcoord →L[ℝ] H)
    let M : ℝ := ‖L‖ + 1
    have hM_pos : 0 < M := by
      dsimp [M]
      exact lt_of_le_of_lt (norm_nonneg L) (lt_add_one _)
    refine ⟨ρ / M, div_pos hρ_pos hM_pos, ?_⟩
    intro k hk
    have hkH_small : ‖e.symm k‖ < ρ := by
      have hle : ‖e.symm k‖ ≤ ‖L‖ * ‖k‖ := by
        simpa [L] using L.le_opNorm k
      have hnorm_le_M : ‖L‖ ≤ M := by
        dsimp [M]
        linarith
      have hmul_le : ‖L‖ * ‖k‖ ≤ M * ‖k‖ :=
        mul_le_mul_of_nonneg_right hnorm_le_M (norm_nonneg k)
      have hMmul_lt : M * ‖k‖ < ρ := by
        have hmul := mul_lt_mul_of_pos_left hk hM_pos
        have hcancel : M * (ρ / M) = ρ := by
          field_simp [ne_of_gt hM_pos]
        simpa [hcancel] using hmul
      exact hle.trans_lt (hmul_le.trans_lt hMmul_lt)
    let gH : H → ℝ := fun z ↦ u (z + e.symm k) - u z
    have hzeroH :
        eLpNorm gH 2 ((volume : Measure H).restrict KH) = 0 := by
      simpa [gH] using hρ (e.symm k) hkH_small
    let μKmap : Measure H := ((volume : Measure Vcoord).map e.symm).restrict KH
    have hμK :
        (volume : Measure H).restrict KH = cμ • μKmap := by
      dsimp [μKmap]
      simp [hμ, Measure.restrict_smul]
    have hzero_smul : eLpNorm gH 2 (cμ • μKmap) = 0 := by
      simpa [hμK] using hzeroH
    have hscale :=
      eLpNorm_smul_measure_of_ne_zero'
        (μ := μKmap) (f := gH) (p := (2 : ℝ≥0∞)) hcμ_ne
    have hzero_map : eLpNorm gH 2 μKmap = 0 := by
      rw [hscale] at hzero_smul
      have hscale_ne :
          (((cμ ^ (2 : ℝ≥0∞).toReal⁻¹ : ℝ≥0) : ℝ≥0∞)) ≠ 0 := by
        exact ENNReal.coe_ne_zero.2 (NNReal.rpow_pos hcμ_pos).ne'
      exact (mul_eq_zero.mp hzero_smul).resolve_left hscale_ne
    have hmpK_symm :
        MeasurePreserving em.symm
          ((volume : Measure Vcoord).restrict K) μKmap := by
      have hraw :=
        hmp0_symm.restrict_image_emb em.symm.measurableEmbedding K
      simpa [KH, μKmap, em] using hraw
    have hnorm_map :
        eLpNorm gH 2 μKmap =
          eLpNorm (gH ∘ em.symm) 2
            ((volume : Measure Vcoord).restrict K) := by
      have hmap :=
        em.symm.measurableEmbedding.eLpNorm_map_measure
          (μ := (volume : Measure Vcoord).restrict K)
          (g := gH) (p := (2 : ℝ≥0∞))
      rw [hmpK_symm.map_eq] at hmap
      exact hmap
    calc
      eLpNorm (fun z ↦ v (z + k) - v z) 2
          ((volume : Measure Vcoord).restrict K)
          = eLpNorm (gH ∘ em.symm) 2
              ((volume : Measure Vcoord).restrict K) := by
            congr 1
            funext z
            simp [v, gH, em, map_add]
      _ = eLpNorm gH 2 μKmap := hnorm_map.symm
      _ = 0 := hzero_map
  have hlocalV :=
    ae_local_const_of_zero_local_translation_eLpNorm_on_open_pi
      (Ω := ΩV) (u := v) hΩV_open hv htranslationV
  intro x hxΩ
  have hexΩ : e x ∈ ΩV := ⟨x, by simpa [ΩH] using hxΩ, rfl⟩
  rcases hlocalV (e x) hexΩ with
    ⟨W, hW_open, hexW, hWΩ, a, haW⟩
  let U : Set H := e.symm '' W
  have hU_open : IsOpen U := by
    dsimp [U]
    exact e.symm.isOpenMap W hW_open
  have hxU : x ∈ U := by
    exact ⟨e x, hexW, by simp⟩
  have hU_subsetΩ : U ⊆ ΩH := by
    intro z hz
    rcases hz with ⟨y, hyW, rfl⟩
    have hyΩ : y ∈ ΩV := hWΩ hyW
    rcases hyΩ with ⟨z, hzΩ, rfl⟩
    simpa [ΩH] using hzΩ
  have hmpW_symm :
      MeasurePreserving em.symm
        ((volume : Measure Vcoord).restrict W)
        (((volume : Measure Vcoord).map e.symm).restrict U) := by
    have hraw :=
      hmp0_symm.restrict_image_emb em.symm.measurableEmbedding W
    simpa [U, em] using hraw
  have hmap_ae :
      ∀ᵐ z ∂((volume : Measure Vcoord).map e.symm).restrict U, u z = a := by
    have hsource :
        ∀ᵐ z ∂Measure.map em.symm ((volume : Measure Vcoord).restrict W),
          u z = a := by
      rw [em.symm.measurableEmbedding.ae_map_iff]
      simpa [v, em] using haW
    simpa [hmpW_symm.map_eq] using hsource
  have hsmul_ae :
      ∀ᵐ z ∂cμ • (((volume : Measure Vcoord).map e.symm).restrict U),
        u z = a :=
    ae_smul_measure_nnreal (μ := ((volume : Measure Vcoord).map e.symm).restrict U)
      cμ hmap_ae
  have hU_ae :
      ∀ᵐ z ∂(volume : Measure H).restrict U, u z = a := by
    have hmeasure :
        (volume : Measure H).restrict U =
          cμ • (((volume : Measure Vcoord).map e.symm).restrict U) := by
      simp [hμ, Measure.restrict_smul]
    simpa [hmeasure] using hsmul_ae
  exact ⟨U, hU_open, hxU, by simpa [ΩH] using hU_subsetΩ, a, hU_ae⟩

/--
%%handwave
name:
  Local translation invariance gives one almost-everywhere constant on a ball
statement:
  Let \(u\in L^2(B(c,r))\).  Suppose that on every compact subset of the ball
  there is a positive radius such that every translation shorter than that
  radius has zero \(L^2\)-difference from \(u\) on the compact set.  Then
  \(u\) is equal almost everywhere on the ball to one real constant.
proof:
  The hypothesis says that the \(L^2\)-class of \(u\) is locally invariant
  under all sufficiently small translations, which gives local
  almost-everywhere constants.  Since the ball is preconnected, [local almost-everywhere constants glue to one constant on a preconnected Euclidean region](lean:JJMath.Uniformization.euclidean_ae_local_constants_glue_on_preconnected).
-/
theorem ae_const_on_ball_of_zero_local_translation_eLpNorm_finiteDimensional
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {u : H → ℝ} {c : H} {r : ℝ}
    (hr_pos : 0 < r)
    (hu : MemLp u 2 (MeasureTheory.volume.restrict (Metric.ball c r)))
    (htranslation :
      ∀ K : Set H, IsCompact K → K ⊆ Metric.ball c r →
        ∃ ρ : ℝ, 0 < ρ ∧ ∀ h : H, ‖h‖ < ρ →
          eLpNorm (fun z ↦ u (z + h) - u z) 2
            (MeasureTheory.volume.restrict K) = 0) :
    ∃ a : ℝ,
      ∀ᵐ y ∂MeasureTheory.volume.restrict (Metric.ball c r), u y = a := by
  exact
    euclidean_ae_local_constants_glue_on_preconnected
      (U := Metric.ball c r) (u := u)
      Metric.isOpen_ball Metric.isPreconnected_ball
      (ae_local_const_of_zero_local_translation_eLpNorm_finiteDimensional
        hr_pos hu htranslation)

/--
%%handwave
name:
  Zero weak gradient gives one almost-everywhere constant on a compactly
  contained Euclidean ball
statement:
  Let \(B(c,r)\) be a ball whose closed ball is contained in an open
  finite-dimensional Euclidean region.  If a locally \(W^{1,2}\) scalar
  function has weak derivative \(D u\) on the region and \(D u=0\) almost
  everywhere there, then \(u\) is equal almost everywhere on \(B(c,r)\) to one
  real constant.
proof:
  The difference-quotient estimate for weak Sobolev functions bounds each
  sufficiently short translation difference by the \(L^2\)-norm of the weak
  derivative on a compact collar.  Since the weak derivative is zero almost
  everywhere, all such local translation differences have zero \(L^2\)-norm.
  Apply [the local translation-invariance criterion](lean:JJMath.Uniformization.ae_const_on_ball_of_zero_local_translation_eLpNorm_finiteDimensional).
-/
theorem euclideanSobolev_zero_gradient_constant_on_ball_finiteDimensional
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Ω : Set H} {u : H → ℝ} {du : H → H →L[ℝ] ℝ}
    {c : H} {r : ℝ}
    (hΩ_open : IsOpen Ω)
    (hr_pos : 0 < r)
    (hclosedBall_subset : Metric.closedBall c r ⊆ Ω)
    (hweak : IsWeakDerivativeOnEuclideanRegionScalar Ω u du)
    (hmem :
      ∀ K : Set H, IsCompact K → K ⊆ Ω →
        MemLp u 2 (MeasureTheory.volume.restrict K) ∧
          MemLp du 2 (MeasureTheory.volume.restrict K))
    (hdu_zero : ∀ᵐ z ∂MeasureTheory.volume.restrict Ω, du z = 0) :
    ∃ a : ℝ,
      ∀ᵐ y ∂MeasureTheory.volume.restrict (Metric.ball c r), u y = a := by
  haveI : ProperSpace H := FiniteDimensional.proper ℝ H
  let B : Set H := Metric.ball c r
  let P : Set H := Metric.closedBall c r
  have hP_compact : IsCompact P := by
    dsimp [P]
    exact isCompact_closedBall c r
  have hmem_P :
      MemLp u 2 (MeasureTheory.volume.restrict P) ∧
        MemLp du 2 (MeasureTheory.volume.restrict P) :=
    hmem P hP_compact hclosedBall_subset
  have hu_B : MemLp u 2 (MeasureTheory.volume.restrict B) := by
    have hμ :
        MeasureTheory.volume.restrict B ≤
          MeasureTheory.volume.restrict P :=
      Measure.restrict_mono Metric.ball_subset_closedBall le_rfl
    exact hmem_P.1.mono_measure hμ
  refine ae_const_on_ball_of_zero_local_translation_eLpNorm_finiteDimensional
    (H := H) (u := u) (c := c) (r := r) hr_pos hu_B ?_
  intro K hK hKB
  rcases hK.exists_cthickening_subset_open Metric.isOpen_ball hKB with
    ⟨η, hη_pos, hη_ball⟩
  let Q : Set H := Metric.cthickening (η / 2) K
  have hη_half_pos : 0 < η / 2 := by linarith
  have hη_half_le : η / 2 ≤ η := by linarith
  have hQ_compact : IsCompact Q := by
    dsimp [Q]
    exact hK.cthickening
  have hQ_ball : Q ⊆ B := by
    dsimp [Q, B]
    exact (Metric.cthickening_mono hη_half_le K).trans hη_ball
  rcases hQ_compact.exists_cthickening_subset_open Metric.isOpen_ball hQ_ball with
    ⟨δ, hδ_pos, hδ_ball⟩
  have hQP : ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ Q ⊆ P := by
    exact ⟨δ, hδ_pos, hδ_ball.trans Metric.ball_subset_closedBall⟩
  refine ⟨η / 2, hη_half_pos, ?_⟩
  intro h hh
  have hsegments :
      ∀ x ∈ K, ∀ t : ℝ, t ∈ Set.Icc 0 1 → x + t • h ∈ Q := by
    intro x hx t ht
    have ht_abs : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
    have hdist : dist (x + t • h) x ≤ η / 2 := by
      calc
        dist (x + t • h) x = ‖t • h‖ := by
          simp [dist_eq_norm]
        _ = |t| * ‖h‖ := norm_smul t h
        _ ≤ 1 * ‖h‖ := mul_le_mul_of_nonneg_right ht_abs (norm_nonneg h)
        _ = ‖h‖ := one_mul ‖h‖
        _ ≤ η / 2 := le_of_lt hh
    exact Metric.mem_cthickening_of_dist_le (x + t • h) x (η / 2) K hx hdist
  have hdiff_le :
      eLpNorm (fun z ↦ u (z + h) - u z) 2
          (MeasureTheory.volume.restrict K) ≤
        ENNReal.ofReal ‖h‖ *
          eLpNorm du 2 (MeasureTheory.volume.restrict P) :=
    scalarWeakSobolev_difference_quotient_eLpNorm_le_of_segments
      hK hQ_compact hP_compact hQP hclosedBall_subset hΩ_open
      hweak hmem_P.1 hsegments
  have hdu_zero_P : du =ᵐ[MeasureTheory.volume.restrict P] 0 :=
    ae_restrict_of_ae_restrict_of_subset hclosedBall_subset hdu_zero
  have hdu_norm_zero :
      eLpNorm du 2 (MeasureTheory.volume.restrict P) = 0 := by
    calc
      eLpNorm du 2 (MeasureTheory.volume.restrict P)
          = eLpNorm (0 : H → H →L[ℝ] ℝ) 2
              (MeasureTheory.volume.restrict P) :=
            eLpNorm_congr_ae hdu_zero_P
      _ = 0 := by
            rw [eLpNorm_zero (α := H) (ε := H →L[ℝ] ℝ)
              (p := (2 : ℝ≥0∞)) (μ := MeasureTheory.volume.restrict P)]
  have hdiff_le_zero :
      eLpNorm (fun z ↦ u (z + h) - u z) 2
          (MeasureTheory.volume.restrict K) ≤ 0 := by
    simpa [hdu_norm_zero] using hdiff_le
  exact le_antisymm hdiff_le_zero bot_le

/--
%%handwave
name:
  Zero weak gradient gives local constants in Euclidean regions
statement:
  Let \(U\) be an open subset of a finite-dimensional real coordinate space.
  A locally \(W^{1,2}\) scalar weak Sobolev function whose weak derivative
  vanishes almost everywhere is almost everywhere constant in a neighborhood
  of every point of \(U\).
proof:
  Around the point choose a ball whose closed ball is still contained in the
  open region.  Apply [the compactly contained ball rigidity](lean:JJMath.Uniformization.euclideanSobolev_zero_gradient_constant_on_ball_finiteDimensional)
  on that ball.
-/
theorem euclideanSobolev_zero_gradient_locally_constant_finiteDimensional
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Ω : Set H} {u : H → ℝ} {du : H → H →L[ℝ] ℝ}
    (hΩ_open : IsOpen Ω)
    (hweak : IsWeakDerivativeOnEuclideanRegionScalar Ω u du)
    (hmem :
      ∀ K : Set H, IsCompact K → K ⊆ Ω →
        MemLp u 2 (MeasureTheory.volume.restrict K) ∧
          MemLp du 2 (MeasureTheory.volume.restrict K))
    (hdu_zero : ∀ᵐ z ∂MeasureTheory.volume.restrict Ω, du z = 0) :
    ∀ x ∈ Ω, ∃ V : Set H, IsOpen V ∧ x ∈ V ∧ V ⊆ Ω ∧
      ∃ a : ℝ, ∀ᵐ y ∂MeasureTheory.volume.restrict V, u y = a := by
  intro x hxΩ
  rcases Metric.isOpen_iff.mp hΩ_open x hxΩ with ⟨R, hR_pos, hball_subset⟩
  let r : ℝ := R / 2
  have hr_pos : 0 < r := by
    positivity
  have hr_lt_R : r < R := by
    dsimp [r]
    linarith
  have hclosedBall_subset : Metric.closedBall x r ⊆ Ω := by
    intro y hy
    apply hball_subset
    have hydist : dist y x ≤ r := by
      simpa [Metric.mem_closedBall] using hy
    exact lt_of_le_of_lt hydist hr_lt_R
  rcases euclideanSobolev_zero_gradient_constant_on_ball_finiteDimensional
      (Ω := Ω) (u := u) (du := du) (c := x) (r := r)
      hΩ_open hr_pos hclosedBall_subset hweak hmem hdu_zero with
    ⟨a, ha⟩
  refine ⟨Metric.ball x r, Metric.isOpen_ball, Metric.mem_ball_self hr_pos, ?_, a, ha⟩
  exact Metric.ball_subset_closedBall.trans hclosedBall_subset

/--
%%handwave
name:
  Euclidean zero weak gradient rigidity in finite-dimensional coordinate spaces
statement:
  On a preconnected open subset of a finite-dimensional real coordinate
  space, a locally \(W^{1,2}\) real-valued weak Sobolev function whose weak
  derivative field vanishes almost everywhere is equal almost everywhere to
  one real constant.
proof:
  This is the Euclidean analytic input: distributional first derivatives
  vanish, so the Sobolev representative is constant on each connected
  component, and preconnectedness leaves only one component.
-/
theorem euclideanSobolev_zero_gradient_constant_on_preconnected_finiteDimensional
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    [FiniteDimensional ℝ H]
    {Ω : Set H} {u : H → ℝ} {du : H → H →L[ℝ] ℝ}
    (hΩ_open : IsOpen Ω)
    (hΩ_preconnected : IsPreconnected Ω)
    (hweak : IsWeakDerivativeOnEuclideanRegionScalar Ω u du)
    (hmem :
      ∀ K : Set H, IsCompact K → K ⊆ Ω →
        MemLp u 2 (MeasureTheory.volume.restrict K) ∧
          MemLp du 2 (MeasureTheory.volume.restrict K))
    (hdu_zero : ∀ᵐ z ∂MeasureTheory.volume.restrict Ω, du z = 0) :
    ∃ a : ℝ, ∀ᵐ z ∂MeasureTheory.volume.restrict Ω, u z = a := by
  exact
    euclidean_ae_local_constants_glue_on_preconnected
      hΩ_open hΩ_preconnected
      (euclideanSobolev_zero_gradient_locally_constant_finiteDimensional
        hΩ_open hweak hmem hdu_zero)

/--
%%handwave
name:
  Euclidean zero weak gradient rigidity principle in the coordinate plane
statement:
  On a preconnected open subset of the coordinate plane, a locally
  \(W^{1,2}\) real-valued weak Sobolev function whose weak derivative field
  vanishes almost everywhere is equal almost everywhere to one real constant.
-/
def EuclideanZeroGradientRigidityOnPlane : Prop :=
  ∀ {Ω : Set ℂ} {u : ℂ → ℝ} {du : ℂ → ℂ →L[ℝ] ℝ},
    IsOpen Ω →
      IsPreconnected Ω →
        IsWeakDerivativeOnEuclideanRegionScalar Ω u du →
          (∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
            MemLp u 2 (MeasureTheory.volume.restrict K) ∧
              MemLp du 2 (MeasureTheory.volume.restrict K)) →
            (∀ᵐ z ∂MeasureTheory.volume.restrict Ω, du z = 0) →
              ∃ a : ℝ, ∀ᵐ z ∂MeasureTheory.volume.restrict Ω, u z = a

/--
%%handwave
name:
  Euclidean zero weak gradient rigidity
statement:
  On a preconnected open subset of the coordinate plane, a locally
  \(W^{1,2}\) real-valued weak Sobolev function whose weak derivative field
  vanishes almost everywhere is equal almost everywhere to one real constant.
proof:
  This is the Euclidean analytic input: distributional first derivatives
  vanish, so the Sobolev representative is constant on each connected
  component, and preconnectedness leaves only one component.
-/
theorem euclideanSobolev_zero_gradient_constant_on_preconnected :
    EuclideanZeroGradientRigidityOnPlane := by
  intro Ω u du hΩ_open hΩ_preconnected hweak hmem hdu_zero
  exact
    euclideanSobolev_zero_gradient_constant_on_preconnected_finiteDimensional
      hΩ_open hΩ_preconnected hweak hmem hdu_zero

/--
%%handwave
name:
  Equality of local constants on a positive-measure intersection
statement:
  If \(u=a\) almost everywhere on \(s\), \(u=b\) almost everywhere on \(t\),
  and \(\mu(s\cap t)>0\), then \(a=b\).
proof:
  Restrict both statements to the intersection; distinct constants would make
  that positive-measure set null.
-/
private theorem ae_eq_const_on_positive_inter_eq
    {X : Type} [MeasurableSpace X] {μ : Measure X}
    {s t : Set X} {u : X → ℝ} {a b : ℝ}
    (hs : ∀ᵐ x ∂μ.restrict s, u x = a)
    (ht : ∀ᵐ x ∂μ.restrict t, u x = b)
    (hst_pos : μ (s ∩ t) ≠ 0) :
    a = b := by
  have hs_inter : ∀ᵐ x ∂μ.restrict (s ∩ t), u x = a :=
    ae_restrict_of_ae_restrict_of_subset Set.inter_subset_left hs
  have ht_inter : ∀ᵐ x ∂μ.restrict (s ∩ t), u x = b :=
    ae_restrict_of_ae_restrict_of_subset Set.inter_subset_right ht
  have hab_ae : ∀ᵐ _x ∂μ.restrict (s ∩ t), a = b := by
    filter_upwards [hs_inter, ht_inter] with x hxa hxb
    exact hxa.symm.trans hxb
  by_contra hab
  have hfalse : ∀ᵐ _x ∂μ.restrict (s ∩ t), False :=
    hab_ae.mono fun _x hx ↦ hab hx
  have hbot : ae (μ.restrict (s ∩ t)) = ⊥ :=
    Filter.eventually_false_iff_eq_bot.mp hfalse
  have hnebot : (ae (μ.restrict (s ∩ t))).NeBot :=
    ae_restrict_neBot.2 hst_pos
  exact hnebot.ne hbot

/--
%%handwave
name:
  Smooth positive manifold measures give positive mass to open sets
statement:
  On a smooth real manifold equipped with a smooth positive measure, every
  nonempty open set has positive measure.
proof:
  Choose a chart meeting the open set.  In that chart the measure is Lebesgue
  measure multiplied by a strictly positive smooth density.  A nonempty
  coordinate-open subset has positive Lebesgue measure, hence positive
  weighted measure, and pushing it back gives positive measure in the original
  open set.
-/
theorem smoothPositiveMeasureOnManifold_open_measure_pos
    {H X : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    [IsManifold I 1 X]
    {μ : Measure X} (hμ : SmoothPositiveMeasureOnManifold (I := I) μ)
    {W : Set X} (hW_open : IsOpen W) (hW_nonempty : W.Nonempty) :
    0 < μ W := by
  classical
  rcases hW_nonempty with ⟨x, hxW⟩
  let e : OpenPartialHomeomorph X H := chartAt H x
  let O : Set H := e.target ∩ e.symm ⁻¹' W
  have hx_source : x ∈ e.source := by
    simpa [e] using mem_chart_source H x
  have he_atlas : e ∈ atlas H X := by
    simpa [e] using chart_mem_atlas H x
  have hO_open : IsOpen O := by
    simpa [O] using e.isOpen_inter_preimage_symm hW_open
  have hxO : e x ∈ O := by
    refine ⟨e.map_source hx_source, ?_⟩
    simpa [e.left_inv hx_source] using hxW
  have hO_nonempty : O.Nonempty := ⟨e x, hxO⟩
  have hO_meas : MeasurableSet O := hO_open.measurableSet
  obtain ⟨ρ, hρ_smooth, hρ_pos, hmap⟩ := hμ.chart_density e he_atlas
  let f : H → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (ρ z)
  have hf_aemeas :
      AEMeasurable f (MeasureTheory.volume.restrict e.target) := by
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      (hρ_smooth.continuousOn.aemeasurable e.open_target.measurableSet)
  let ν : Measure H := MeasureTheory.volume.restrict e.target
  have hνO_pos : 0 < ν O := by
    have hO_subset : O ⊆ e.target := Set.inter_subset_left
    change 0 < (MeasureTheory.volume.restrict e.target) O
    rw [Measure.restrict_apply' e.open_target.measurableSet]
    simpa [Set.inter_eq_self_of_subset_left hO_subset] using
      hO_open.measure_pos (MeasureTheory.volume : Measure H) hO_nonempty
  have hweighted_pos : 0 < (ν.withDensity f) O := by
    rw [withDensity_apply _ hO_meas]
    by_contra hnot
    have hzero : ∫⁻ z in O, f z ∂ν = 0 :=
      le_antisymm (not_lt.mp hnot) bot_le
    have hae_zero :
        ∀ᵐ z ∂ν, z ∈ O → f z = 0 :=
      (setLIntegral_eq_zero_iff' (μ := ν) hO_meas
        (hf_aemeas.mono_measure Measure.restrict_le_self)).1 hzero
    have hfalse : ∀ᵐ _z ∂ν.restrict O, False := by
      filter_upwards [ae_restrict_of_ae hae_zero, ae_restrict_mem hO_meas] with z hz hzO
      have hz_target : z ∈ e.target := hzO.1
      have hfz_ne : f z ≠ 0 := by
        exact ne_of_gt (ENNReal.ofReal_pos.mpr (hρ_pos z hz_target))
      exact hfz_ne (hz hzO)
    have hbot : ae (ν.restrict O) = ⊥ :=
      Filter.eventually_false_iff_eq_bot.mp hfalse
    have hnebot : (ae (ν.restrict O)).NeBot :=
      ae_restrict_neBot.2 (ne_of_gt hνO_pos)
    exact hnebot.ne hbot
  have hmapO_pos : 0 < Measure.map e (μ.restrict e.source) O := by
    simpa [ν, f, hmap] using hweighted_pos
  have he_aemeas : AEMeasurable e (μ.restrict e.source) :=
    openPartialHomeomorph_aemeasurable_restrict_source e μ
  have hmapO_eq :
      Measure.map e (μ.restrict e.source) O =
        μ.restrict e.source (e ⁻¹' O) :=
    Measure.map_apply_of_aemeasurable he_aemeas hO_meas
  have hrestrict_eq :
      μ.restrict e.source (e ⁻¹' O) =
        μ ((e ⁻¹' O) ∩ e.source) :=
    Measure.restrict_apply' e.open_source.measurableSet
  have hpre_subset : (e ⁻¹' O) ∩ e.source ⊆ W := by
    intro y hy
    have hyO : e y ∈ O := hy.1
    simpa [e.left_inv hy.2] using hyO.2
  have hmapO_le : Measure.map e (μ.restrict e.source) O ≤ μ W := by
    rw [hmapO_eq, hrestrict_eq]
    exact measure_mono hpre_subset
  exact hmapO_pos.trans_le hmapO_le

/--
%%handwave
name:
  Local almost-everywhere constants glue on preconnected manifolds
statement:
  Let \(M\) be a second-countable \(C^1\) real manifold equipped with a smooth
  positive measure.  On a preconnected open region \(U\subset M\), if a
  function is almost everywhere constant in a neighborhood of every point of
  \(U\), then it is equal almost everywhere on \(U\) to one constant.
proof:
  A smooth positive measure gives positive measure to every nonempty open set.
  Hence two local almost-everywhere constants agree whenever their
  neighborhoods overlap.  The relation saying that the local constants at two
  points agree is locally true, symmetric, and transitive, so preconnectedness
  propagates it across \(U\).  Second countability supplies a countable
  subcover of \(U\) by the local neighborhoods, and the local
  almost-everywhere equalities combine over that countable cover.
-/
theorem ae_local_constants_glue_on_preconnected_of_smooth_positive_measure
    {H X : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    [IsManifold I 1 X]
    {μ : Measure X} (hμ : SmoothPositiveMeasureOnManifold (I := I) μ)
    {U : Set X} {u : X → ℝ}
    (_hU_open : IsOpen U) (hU_preconnected : IsPreconnected U)
    (hlocal_const :
      ∀ x ∈ U, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
        ∃ a : ℝ, ∀ᵐ y ∂μ.restrict V, u y = a) :
    ∃ a : ℝ, ∀ᵐ x ∂μ.restrict U, u x = a := by
  classical
  by_cases hU_nonempty : U.Nonempty
  · rcases hU_nonempty with ⟨x₀, hx₀U⟩
    let LocalConstAt : X → ℝ → Prop :=
      fun x a ↦ ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
        ∀ᵐ y ∂μ.restrict V, u y = a
    have hLocal_exists : ∀ x ∈ U, ∃ a : ℝ, LocalConstAt x a := by
      intro x hxU
      rcases hlocal_const x hxU with ⟨V, hV_open, hxV, hVU, a, ha⟩
      exact ⟨a, V, hV_open, hxV, hVU, ha⟩
    let SameLocalConstant : X → X → Prop :=
      fun x y ↦ ∀ a b : ℝ, LocalConstAt x a → LocalConstAt y b → a = b
    have hsame_near :
        ∀ x ∈ U, ∀ᶠ y in 𝓝[U] x, SameLocalConstant x y := by
      intro x hxU
      rcases hlocal_const x hxU with ⟨V₀, hV₀_open, hxV₀, hV₀U, c, hc⟩
      filter_upwards [mem_nhdsWithin_of_mem_nhds (hV₀_open.mem_nhds hxV₀)] with y hyV₀
      intro a b hxa hyb
      rcases hxa with ⟨Vx, hVx_open, hxVx, _hVxU, hVx_ae⟩
      rcases hyb with ⟨Vy, hVy_open, hyVy, _hVyU, hVy_ae⟩
      have hx_inter_nonempty : (Vx ∩ V₀).Nonempty := ⟨x, hxVx, hxV₀⟩
      have hy_inter_nonempty : (V₀ ∩ Vy).Nonempty := ⟨y, hyV₀, hyVy⟩
      have hx_inter_pos : μ (Vx ∩ V₀) ≠ 0 :=
        ne_of_gt <| smoothPositiveMeasureOnManifold_open_measure_pos hμ
          (hVx_open.inter hV₀_open) hx_inter_nonempty
      have hy_inter_pos : μ (V₀ ∩ Vy) ≠ 0 :=
        ne_of_gt <| smoothPositiveMeasureOnManifold_open_measure_pos hμ
          (hV₀_open.inter hVy_open) hy_inter_nonempty
      have hac : a = c :=
        ae_eq_const_on_positive_inter_eq hVx_ae hc hx_inter_pos
      have hcb : c = b :=
        ae_eq_const_on_positive_inter_eq hc hVy_ae hy_inter_pos
      exact hac.trans hcb
    have hsame_trans :
        ∀ x y z, x ∈ U → y ∈ U → z ∈ U →
          SameLocalConstant x y → SameLocalConstant y z → SameLocalConstant x z := by
      intro x y z hxU hyU hzU hxy hyz a c hxa hzc
      rcases hLocal_exists y hyU with ⟨b, hyb⟩
      exact (hxy a b hxa hyb).trans (hyz b c hyb hzc)
    have hsame_symm :
        ∀ x y, x ∈ U → y ∈ U →
          SameLocalConstant x y → SameLocalConstant y x := by
      intro x y hxU hyU hxy a b hya hxb
      exact (hxy b a hxb hya).symm
    have hsame_all :
        ∀ x ∈ U, SameLocalConstant x₀ x := by
      intro x hxU
      exact hU_preconnected.induction₂ SameLocalConstant
        hsame_near hsame_trans hsame_symm hx₀U hxU
    rcases hLocal_exists x₀ hx₀U with ⟨a₀, hx₀a₀⟩
    let LocalData : Type _ :=
      {p : X × Set X × ℝ //
        p.1 ∈ U ∧ IsOpen p.2.1 ∧ p.1 ∈ p.2.1 ∧ p.2.1 ⊆ U ∧
          ∀ᵐ y ∂μ.restrict p.2.1, u y = p.2.2}
    let localCenter : LocalData → X := fun p ↦ p.val.1
    let localSet : LocalData → Set X := fun p ↦ p.val.2.1
    let localConst : LocalData → ℝ := fun p ↦ p.val.2.2
    have hlocalSet_open : ∀ p : LocalData, IsOpen (localSet p) := by
      intro p
      exact p.property.2.1
    have hcover : U ⊆ ⋃ p : LocalData, localSet p := by
      intro x hxU
      rcases hlocal_const x hxU with ⟨V, hV_open, hxV, hVU, a, ha⟩
      refine Set.mem_iUnion.2 ?_
      exact ⟨⟨(x, V, a), hxU, hV_open, hxV, hVU, ha⟩, hxV⟩
    have hU_lindelof : IsLindelof U :=
      HereditarilyLindelofSpace.isLindelof U
    rcases hU_lindelof.elim_countable_subcover localSet hlocalSet_open hcover with
      ⟨T, hT_countable, hT_cover⟩
    refine ⟨a₀, ?_⟩
    have hcover_ae :
        ∀ᵐ x ∂μ.restrict (⋃ p ∈ T, localSet p), u x = a₀ := by
      rw [ae_restrict_biUnion_iff localSet hT_countable (fun x ↦ u x = a₀)]
      intro p hpT
      have hpU : localCenter p ∈ U := p.property.1
      have hpLocal : LocalConstAt (localCenter p) (localConst p) :=
        ⟨localSet p, p.property.2.1, p.property.2.2.1,
          p.property.2.2.2.1, p.property.2.2.2.2⟩
      have hconst_eq : a₀ = localConst p :=
        hsame_all (localCenter p) hpU a₀ (localConst p) hx₀a₀ hpLocal
      filter_upwards [p.property.2.2.2.2] with x hx
      rwa [hconst_eq]
    exact ae_restrict_of_ae_restrict_of_subset hT_cover hcover_ae
  · refine ⟨0, ?_⟩
    have hU_empty : U = ∅ := Set.not_nonempty_iff_eq_empty.mp hU_nonempty
    simp [hU_empty]

/--
%%handwave
name:
  Local almost-everywhere constants glue on preconnected surface regions
statement:
  On a preconnected open surface region equipped with a smooth positive area
  measure, if a function is almost everywhere constant in a neighborhood of
  every point, then it is equal almost everywhere on the whole region to one
  constant.
proof:
  Regard the smooth positive area measure as a smooth positive measure for
  the real surface model, then apply
  [local almost-everywhere constants glue on preconnected manifolds](lean:JJMath.Uniformization.ae_local_constants_glue_on_preconnected_of_smooth_positive_measure).
-/
theorem ae_local_constants_glue_on_preconnected_of_smooth_positive_area
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [SecondCountableTopology X] [IsManifold SurfaceRealModel 1 X]
    {μ : Measure X} (hμ : SmoothPositiveAreaMeasureOnSurface X μ)
    {U : Set X} {u : X → ℝ}
    (hU_open : IsOpen U) (hU_preconnected : IsPreconnected U)
    (hlocal_const :
      ∀ x ∈ U, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
        ∃ a : ℝ, ∀ᵐ y ∂μ.restrict V, u y = a) :
    ∃ a : ℝ, ∀ᵐ x ∂μ.restrict U, u x = a := by
  let hμ' : SmoothPositiveMeasureOnManifold (I := SurfaceRealModel) μ :=
    { finite_on_compact := hμ.finite_on_compact
      chart_density := hμ.chart_density }
  exact
    ae_local_constants_glue_on_preconnected_of_smooth_positive_measure
      (I := SurfaceRealModel) hμ' hU_open hU_preconnected hlocal_const

set_option maxHeartbeats 800000

/--
%%handwave
name:
  Vanishing differentials transfer to coordinates
statement:
  If a manifold weak differential vanishes almost everywhere on an open
  region with respect to a smooth positive measure, then its coordinate
  representative vanishes almost everywhere on the corresponding coordinate region with
  respect to Lebesgue measure.
proof:
  In a chart, the smooth positive measure is Lebesgue measure multiplied by a
  strictly positive smooth density, so the coordinate and manifold null sets
  are the same.  The pulled-back differential is obtained from the manifold
  differential by composing with the chart tangent map, hence it is zero
  whenever the manifold differential is zero.
-/
theorem smoothPositiveMeasureOnManifold_chartPullback_ae_zero
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold I 1 X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure X} (hμ : SmoothPositiveMeasureOnManifold (I := I) μ)
    (e : OpenPartialHomeomorph X H) (he : e ∈ atlas H X)
    {U : Set X} {du : ManifoldDifferentialField I X E}
    (hU_open : IsOpen U)
    (hdu_zero : ∀ᵐ x ∂μ.restrict U, du x = 0) :
    ∀ᵐ z ∂MeasureTheory.volume.restrict (manifoldChartRegion e U),
      ManifoldDifferentialField.chartPullback du e z = 0 := by
  classical
  let Ω : Set H := manifoldChartRegion e U
  let V : Set X := e.source ∩ U
  have hΩ_open : IsOpen Ω := by
    simpa [Ω, manifoldChartRegion] using e.isOpen_inter_preimage_symm hU_open
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  have hΩ_target : Ω ⊆ e.target := Set.inter_subset_left
  have hV_meas : MeasurableSet V := (e.open_source.inter hU_open).measurableSet
  have hV_subset_source : V ⊆ e.source := Set.inter_subset_left
  have hV_subset_U : V ⊆ U := Set.inter_subset_right
  have hduV : ∀ᵐ y ∂μ.restrict V, du y = 0 :=
    ae_restrict_of_ae_restrict_of_subset hV_subset_U hdu_zero
  obtain ⟨ρ, hρ_smooth, hρ_pos, hmap⟩ := hμ.chart_density e he
  let δ : H → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (ρ z)
  have he_aemeas_source : AEMeasurable e (μ.restrict e.source) :=
    openPartialHomeomorph_aemeasurable_restrict_source e μ
  have he_aemeas_V : AEMeasurable e (μ.restrict V) :=
    he_aemeas_source.mono_measure (Measure.restrict_mono hV_subset_source le_rfl)
  have hmap_source_ac :
      Measure.map e (μ.restrict e.source) ≪ MeasureTheory.volume.restrict e.target := by
    rw [hmap]
    exact withDensity_absolutelyContinuous _ _
  have hsymm_source :
      AEMeasurable e.symm (Measure.map e (μ.restrict e.source)) := by
    exact
      (openPartialHomeomorph_symm_aemeasurable_restrict_target e MeasureTheory.volume).mono_ac
        hmap_source_ac
  have hmapV_le_source :
      Measure.map e (μ.restrict V) ≤ Measure.map e (μ.restrict e.source) :=
    Measure.map_mono_of_aemeasurable
      (Measure.restrict_mono hV_subset_source le_rfl) he_aemeas_source
  have hsymm_V :
      AEMeasurable e.symm (Measure.map e (μ.restrict V)) :=
    hsymm_source.mono_measure hmapV_le_source
  have hmap_symmV :
      Measure.map e.symm (Measure.map e (μ.restrict V)) = μ.restrict V := by
    have hmap_comp :
        Measure.map e.symm (Measure.map e (μ.restrict V)) =
          Measure.map (fun y : X ↦ e.symm (e y)) (μ.restrict V) := by
      simpa [Function.comp_def] using
        (AEMeasurable.map_map_of_aemeasurable hsymm_V he_aemeas_V)
    have hleft :
        (fun y : X ↦ e.symm (e y)) =ᵐ[μ.restrict V] fun y ↦ y :=
      ae_restrict_of_forall_mem hV_meas fun y hyV ↦
        e.left_inv (hV_subset_source hyV)
    calc
      Measure.map e.symm (Measure.map e (μ.restrict V))
          = Measure.map (fun y : X ↦ e.symm (e y)) (μ.restrict V) := hmap_comp
      _ = Measure.map (fun y : X ↦ y) (μ.restrict V) :=
          Measure.map_congr hleft
      _ = μ.restrict V := by rw [Measure.map_id']
  have hdu_symm_map :
      ∀ᵐ z ∂Measure.map e (μ.restrict V), du (e.symm z) = 0 := by
    have hpull :
        ∀ᵐ y ∂Measure.map e.symm (Measure.map e (μ.restrict V)), du y = 0 := by
      simpa [hmap_symmV] using hduV
    exact ae_of_ae_map hsymm_V hpull
  have hmap_restrict :
      (Measure.map e (μ.restrict e.source)).restrict Ω =
        Measure.map e ((μ.restrict e.source).restrict (e ⁻¹' Ω)) :=
    Measure.restrict_map_of_aemeasurable he_aemeas_source hΩ_meas
  have hpre_ae :
      e ⁻¹' Ω =ᵐ[μ.restrict e.source] V := by
    filter_upwards [ae_restrict_mem e.open_source.measurableSet] with y hy_source
    apply propext
    constructor
    · intro hyΩ
      exact ⟨hy_source, by simpa [e.left_inv hy_source] using hyΩ.2⟩
    · intro hyV
      exact ⟨e.map_source hy_source, by simpa [e.left_inv hy_source] using hyV.2⟩
  have hsource_restrict_pre :
      (μ.restrict e.source).restrict (e ⁻¹' Ω) = μ.restrict V := by
    calc
      (μ.restrict e.source).restrict (e ⁻¹' Ω)
          = (μ.restrict e.source).restrict V :=
              Measure.restrict_congr_set hpre_ae
      _ = μ.restrict V := Measure.restrict_restrict_of_subset hV_subset_source
  have hmapV_eq :
      Measure.map e (μ.restrict V) =
        (Measure.map e (μ.restrict e.source)).restrict Ω := by
    rw [hmap_restrict, hsource_restrict_pre]
  have hmapV_density :
      Measure.map e (μ.restrict V) =
        (MeasureTheory.volume.restrict Ω).withDensity δ := by
    calc
      Measure.map e (μ.restrict V)
          = (Measure.map e (μ.restrict e.source)).restrict Ω := hmapV_eq
      _ = ((MeasureTheory.volume.restrict e.target).withDensity δ).restrict Ω := by
          simpa [δ] using congrArg (fun ν : Measure H ↦ ν.restrict Ω) hmap
      _ = ((MeasureTheory.volume.restrict e.target).restrict Ω).withDensity δ := by
          rw [restrict_withDensity hΩ_meas]
      _ = (MeasureTheory.volume.restrict Ω).withDensity δ := by
          rw [Measure.restrict_restrict_of_subset hΩ_target]
  have hδ_aemeas : AEMeasurable δ (MeasureTheory.volume.restrict Ω) := by
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      ((hρ_smooth.continuousOn.mono hΩ_target).aemeasurable hΩ_meas)
  have hδ_ne_zero :
      ∀ᵐ z ∂MeasureTheory.volume.restrict Ω, δ z ≠ 0 :=
    ae_restrict_of_forall_mem hΩ_meas fun z hzΩ ↦
      ne_of_gt (ENNReal.ofReal_pos.mpr (hρ_pos z (hΩ_target hzΩ)))
  have hdu_symm_density :
      ∀ᵐ z ∂(MeasureTheory.volume.restrict Ω).withDensity δ, du (e.symm z) = 0 := by
    simpa [hmapV_density] using hdu_symm_map
  have hdu_symm_volume :
      ∀ᵐ z ∂MeasureTheory.volume.restrict Ω, du (e.symm z) = 0 :=
    (withDensity_absolutelyContinuous' hδ_aemeas hδ_ne_zero).ae_le hdu_symm_density
  filter_upwards [hdu_symm_volume] with z hz
  simp [ManifoldDifferentialField.chartPullback, hz]

set_option maxHeartbeats 800000

/--
%%handwave
name:
  Coordinate almost-everywhere constants transfer back to the manifold
statement:
  Let \(W\) be an open coordinate set contained in the target of a
  chart, and let \(V\) be its inverse image in the chart source.  If a
  pulled-back function is almost everywhere equal to a constant on \(W\) with
  respect to Lebesgue measure, then the original function is almost
  everywhere equal to the same constant on \(V\) with respect to any smooth
  positive manifold measure.
proof:
  The chart push-forward of the smooth positive measure is Lebesgue measure
  multiplied by a strictly positive smooth density.  Thus coordinate null
  sets are null for the pushed-forward manifold measure, and pulling the
  almost-everywhere equality back through the chart gives the claim.
-/
theorem smoothPositiveMeasureOnManifold_ae_const_of_chart_ae_const
    {H X : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold I 1 X]
    {μ : Measure X} (hμ : SmoothPositiveMeasureOnManifold (I := I) μ)
    (e : OpenPartialHomeomorph X H) (he : e ∈ atlas H X)
    {W : Set H} (hW_open : IsOpen W) (hW_target : W ⊆ e.target)
    {u : X → ℝ} {a : ℝ}
    (hcoord : ∀ᵐ z ∂MeasureTheory.volume.restrict W, u (e.symm z) = a) :
    ∀ᵐ y ∂μ.restrict (e.source ∩ e ⁻¹' W), u y = a := by
  classical
  let V : Set X := e.source ∩ e ⁻¹' W
  have hV_subset_source : V ⊆ e.source := Set.inter_subset_left
  have hW_meas : MeasurableSet W := hW_open.measurableSet
  have hV_meas : MeasurableSet V :=
    (e.isOpen_inter_preimage hW_open).measurableSet
  have he_aemeas_source : AEMeasurable e (μ.restrict e.source) :=
    openPartialHomeomorph_aemeasurable_restrict_source e μ
  have he_aemeas_V : AEMeasurable e (μ.restrict V) :=
    he_aemeas_source.mono_measure (Measure.restrict_mono hV_subset_source le_rfl)
  obtain ⟨ρ, hρ_smooth, _hρ_pos, hmap⟩ := hμ.chart_density e he
  let δ : H → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (ρ z)
  let ν : Measure H := MeasureTheory.volume.restrict e.target
  have hmap_source_ac :
      Measure.map e (μ.restrict e.source) ≪ ν := by
    rw [hmap]
    exact withDensity_absolutelyContinuous _ _
  have hmap_restrict :
      (Measure.map e (μ.restrict e.source)).restrict W =
        Measure.map e ((μ.restrict e.source).restrict (e ⁻¹' W)) :=
    Measure.restrict_map_of_aemeasurable he_aemeas_source hW_meas
  have hpre_ae :
      e ⁻¹' W =ᵐ[μ.restrict e.source] V := by
    filter_upwards [ae_restrict_mem e.open_source.measurableSet] with y hy_source
    apply propext
    constructor
    · intro hyW
      exact ⟨hy_source, hyW⟩
    · intro hyV
      exact hyV.2
  have hsource_restrict_pre :
      (μ.restrict e.source).restrict (e ⁻¹' W) = μ.restrict V := by
    calc
      (μ.restrict e.source).restrict (e ⁻¹' W)
          = (μ.restrict e.source).restrict V :=
              Measure.restrict_congr_set hpre_ae
      _ = μ.restrict V := Measure.restrict_restrict_of_subset hV_subset_source
  have hmapV_eq :
      Measure.map e (μ.restrict V) =
        (Measure.map e (μ.restrict e.source)).restrict W := by
    rw [hmap_restrict, hsource_restrict_pre]
  have hνW_eq : ν.restrict W = MeasureTheory.volume.restrict W := by
    simpa [ν] using
      Measure.restrict_restrict_of_subset (μ := MeasureTheory.volume) hW_target
  have hmapV_ac :
      Measure.map e (μ.restrict V) ≪ MeasureTheory.volume.restrict W := by
    rw [hmapV_eq, ← hνW_eq]
    exact hmap_source_ac.restrict W
  have hcoord_map :
      (fun z : H ↦ u (e.symm z)) =ᵐ[Measure.map e (μ.restrict V)] fun _ ↦ a :=
    hmapV_ac.ae_eq hcoord
  have hpull :
      ∀ᵐ y ∂μ.restrict V, u (e.symm (e y)) = a :=
    ae_of_ae_map he_aemeas_V hcoord_map
  filter_upwards [hpull, ae_restrict_mem hV_meas] with y hy hyV
  simpa [V, e.left_inv hyV.1] using hy

/--
%%handwave
name:
  Coordinate pullbacks preserve compact \(L^2\)-membership
statement:
  Let \(K_0\) be a compact subset of one chart source and let
  \(K=\chi(K_0)\).  If a function is square-integrable on \(K_0\) for a
  smooth positive measure, then its coordinate pullback
  \(f\circ\chi^{-1}\) is square-integrable on \(K\) for Lebesgue measure.
proof:
  In the chart, the push-forward of the smooth positive measure is Lebesgue
  measure multiplied by a strictly positive smooth density.  On the compact
  set \(K\), this density has a positive lower bound, so removing the density
  preserves \(L^2\)-membership.
-/
theorem smoothPositiveMeasureOnManifold_chartPullback_memLp_on_compact_of_memLp
    {H X F : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace F] [ContinuousENorm F]
    {μ : Measure X} (hμ : SmoothPositiveMeasureOnManifold (I := I) μ)
    (e : OpenPartialHomeomorph X H) (he : e ∈ atlas H X)
    {K₀ : Set X} {K : Set H}
    (hK₀_compact : IsCompact K₀)
    (hK₀_source : K₀ ⊆ e.source)
    (hK_def : K = e '' K₀)
    {f : X → F} (hf : MemLp f 2 (μ.restrict K₀)) :
    MemLp (fun z : H ↦ f (e.symm z)) 2
      (MeasureTheory.volume.restrict K) := by
  classical
  have hK_target : K ⊆ e.target := by
    rw [hK_def]
    intro z hz
    rcases hz with ⟨x, hxK, rfl⟩
    exact e.map_source (hK₀_source hxK)
  have hK_compact : IsCompact K := by
    rw [hK_def]
    exact hK₀_compact.image_of_continuousOn (e.continuousOn.mono hK₀_source)
  have hK_meas : MeasurableSet K := hK_compact.measurableSet
  rcases hμ.chart_density e he with ⟨ρ, hρ_smooth, hρ_pos, hmap⟩
  let ν : Measure H := MeasureTheory.volume.restrict e.target
  let δ : H → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (ρ z)
  rcases K.eq_empty_or_nonempty with hK_empty | hK_nonempty
  · have hzero : MeasureTheory.volume.restrict K = 0 := by
      simp [hK_empty]
    rw [hzero]
    exact memLp_measure_zero
  have hρ_cont_K : ContinuousOn ρ K :=
    hρ_smooth.continuousOn.mono hK_target
  rcases hK_compact.exists_sInf_image_eq_and_le hK_nonempty hρ_cont_K with
    ⟨z₀, hz₀K, _hz₀_inf, hz₀_min⟩
  let c₀ : ℝ≥0∞ := ENNReal.ofReal (ρ z₀)
  have hc₀_pos : 0 < ρ z₀ := hρ_pos z₀ (hK_target hz₀K)
  have hc₀_ne_zero : c₀ ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hc₀_pos)
  have hc₀_ne_top : c₀ ≠ (⊤ : ℝ≥0∞) := by
    simp [c₀]
  have hδ_lower : ∀ᵐ z ∂ν.restrict K, c₀ ≤ δ z := by
    filter_upwards [ae_restrict_mem hK_meas] with z hzK
    exact ENNReal.ofReal_le_ofReal (hz₀_min z hzK)
  let μsK : Measure X := (μ.restrict e.source).restrict (e ⁻¹' K)
  let Fpull : H → F := fun z ↦ f (e.symm z)
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
  have hsymm_big :
      AEMeasurable e.symm (Measure.map e (μ.restrict e.source)) := by
    have hsymm_vol :
        AEMeasurable e.symm (MeasureTheory.volume.restrict e.target) :=
      openPartialHomeomorph_symm_aemeasurable_restrict_target e MeasureTheory.volume
    have h_ac :
        Measure.map e (μ.restrict e.source) ≪
          MeasureTheory.volume.restrict e.target := by
      rw [hmap]
      exact withDensity_absolutelyContinuous _ _
    exact hsymm_vol.mono_ac h_ac
  have hmap_μsK_le :
      Measure.map e μsK ≤ Measure.map e (μ.restrict e.source) :=
    Measure.map_mono_of_aemeasurable (by
      dsimp [μsK]
      exact Measure.restrict_le_self) he_aemeas_source
  have hsymm_aemeas : AEMeasurable e.symm (Measure.map e μsK) :=
    hsymm_big.mono_measure hmap_μsK_le
  have hmap_symm : Measure.map e.symm (Measure.map e μsK) = μsK := by
    have hmap_comp :
        Measure.map e.symm (Measure.map e μsK) =
          Measure.map (fun x : X ↦ e.symm (e x)) μsK := by
      simpa [Function.comp_def] using
        (AEMeasurable.map_map_of_aemeasurable hsymm_aemeas he_aemeas_μsK)
    have hleft :
        (fun x : X ↦ e.symm (e x)) =ᵐ[μsK] fun x ↦ x := by
      have hsource_ae : ∀ᵐ x ∂μsK, x ∈ e.source := by
        dsimp [μsK]
        exact ae_restrict_of_ae (ae_restrict_mem e.open_source.measurableSet)
      exact hsource_ae.mono fun x hx_source ↦ e.left_inv hx_source
    calc
      Measure.map e.symm (Measure.map e μsK)
          = Measure.map (fun x : X ↦ e.symm (e x)) μsK := hmap_comp
      _ = Measure.map (fun x : X ↦ x) μsK := Measure.map_congr hleft
      _ = μsK := by rw [Measure.map_id']
  have hf_μsK : MemLp f 2 μsK := by
    simpa [hμsK_eq] using hf
  have hf_aestr_map_symm :
      AEStronglyMeasurable f (Measure.map e.symm (Measure.map e μsK)) := by
    simpa [hmap_symm] using hf_μsK.aestronglyMeasurable
  have hFpull_aestr :
      AEStronglyMeasurable Fpull (Measure.map e μsK) := by
    simpa [Fpull, Function.comp_def] using
      hf_aestr_map_symm.comp_aemeasurable hsymm_aemeas
  have hcomp_eq :
      (fun x : X ↦ Fpull (e x)) =ᵐ[μsK] f := by
    have hsource_ae : ∀ᵐ x ∂μsK, x ∈ e.source := by
      dsimp [μsK]
      exact ae_restrict_of_ae (ae_restrict_mem e.open_source.measurableSet)
    exact hsource_ae.mono fun x hx_source ↦ by
      simp [Fpull, e.left_inv hx_source]
  have hcomp_mem : MemLp (fun x : X ↦ Fpull (e x)) 2 μsK :=
    (memLp_congr_ae hcomp_eq).2 hf_μsK
  have hF_map : MemLp Fpull 2 (Measure.map e μsK) :=
    (memLp_map_measure_iff hFpull_aestr he_aemeas_μsK).2 hcomp_mem
  have hmap_restrict :
      (Measure.map e (μ.restrict e.source)).restrict K = Measure.map e μsK := by
    dsimp [μsK]
    exact Measure.restrict_map_of_aemeasurable he_aemeas_source hK_meas
  have hweighted_eq :
      (ν.withDensity δ).restrict K = Measure.map e μsK := by
    calc
      (ν.withDensity δ).restrict K
          = (Measure.map e (μ.restrict e.source)).restrict K := by
              simpa [ν, δ] using congrArg (fun m : Measure H ↦ m.restrict K) hmap.symm
      _ = Measure.map e μsK := hmap_restrict
  have hF_weighted_K : MemLp Fpull 2 ((ν.withDensity δ).restrict K) := by
    simpa [hweighted_eq] using hF_map
  have hF_νK : MemLp Fpull 2 (ν.restrict K) :=
    memLp_of_withDensity_lower_bound_on_restrict
      (ν := ν) (δ := δ) (K := K) (c := c₀)
      hK_meas hc₀_ne_zero hc₀_ne_top hδ_lower hF_weighted_K
  simpa [Fpull, ν, Measure.restrict_restrict_of_subset hK_target] using hF_νK

/--
%%handwave
name:
  Zero weak gradient gives local coordinate constants on manifolds
statement:
  Let \(M\) be a finite-dimensional second-countable \(C^1\) real Riemannian
  manifold equipped with a smooth positive measure.  If a real-valued locally
  \(W^{1,2}\) function has weak differential zero almost everywhere on an
  open region, then near every point of the region it is almost everywhere
  equal to a constant.
proof:
  This is the local analytic input: in coordinates it follows from the
  Euclidean zero-gradient theorem, with smooth positive density transferring
  \(L^2\) and null-set statements between the manifold measure and Lebesgue
  measure.
-/
theorem localSobolev_zero_gradient_locally_constant_on_manifold
    {H X : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    [IsManifold I 1 X] [FiniteDimensional ℝ H]
    {g : SmoothRiemannianMetricOnManifold I X} {μ : Measure X}
    (hμ : SmoothPositiveMeasureOnManifold (I := I) μ)
    {U : Set X} {u : X → ℝ} {du : ManifoldDifferentialField I X ℝ}
    (hU_open : IsOpen U)
    (hu : IsLocalSobolevH1OnManifoldWithValues (I := I) g μ U u du)
    (hdu_zero : ∀ᵐ x ∂μ.restrict U, du x = 0) :
    ∀ x ∈ U, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ∃ a : ℝ, ∀ᵐ y ∂μ.restrict V, u y = a := by
  classical
  intro x hxU
  let e : OpenPartialHomeomorph X H := chartAt H x
  let Ω : Set H := manifoldChartRegion e U
  have he : e ∈ atlas H X := chart_mem_atlas H x
  have hx_source : x ∈ e.source := by
    simpa [e] using mem_chart_source H x
  have hzΩ : e x ∈ Ω := by
    refine ⟨e.map_source hx_source, ?_⟩
    simpa [e.left_inv hx_source] using hxU
  have hΩ_open : IsOpen Ω := by
    simpa [Ω, manifoldChartRegion] using e.isOpen_inter_preimage_symm hU_open
  have hweak_coord :
      IsWeakDerivativeOnEuclideanRegionScalar Ω
        (fun z : H ↦ u (e.symm z))
        (ManifoldDifferentialField.chartPullback du e) := by
    simpa [Ω] using
      IsWeakDerivativeOnManifoldRegionBundle.chartPullback
        (I := I) hu.1 e he
  have hdu_coord_zero :
      ∀ᵐ z ∂MeasureTheory.volume.restrict Ω,
        ManifoldDifferentialField.chartPullback du e z = 0 := by
    simpa [Ω] using
      smoothPositiveMeasureOnManifold_chartPullback_ae_zero
        (I := I) (μ := μ) hμ e he hU_open hdu_zero
  have hmem_coord :
      ∀ K : Set H, IsCompact K → K ⊆ Ω →
        MemLp (fun z : H ↦ u (e.symm z)) 2
            (MeasureTheory.volume.restrict K) ∧
          MemLp (ManifoldDifferentialField.chartPullback du e) 2
            (MeasureTheory.volume.restrict K) := by
    intro K hK_compact hKΩ
    let K₀ : Set X := e.symm '' K
    have hK_target : K ⊆ e.target := fun z hz ↦ (hKΩ hz).1
    have hK₀_compact : IsCompact K₀ :=
      hK_compact.image_of_continuousOn (e.continuousOn_symm.mono hK_target)
    have hK₀_source : K₀ ⊆ e.source := by
      rintro y ⟨z, hzK, rfl⟩
      exact e.map_target (hK_target hzK)
    have hK₀U : K₀ ⊆ U := by
      rintro y ⟨z, hzK, rfl⟩
      exact (hKΩ hzK).2
    have hK_def : K = e '' K₀ := by
      ext z
      constructor
      · intro hzK
        refine ⟨e.symm z, ⟨z, hzK, rfl⟩, ?_⟩
        exact e.right_inv (hK_target hzK)
      · rintro ⟨y, ⟨w, hwK, rfl⟩, rfl⟩
        simpa [e.right_inv (hK_target hwK)] using hwK
    have hu_K₀ : MemLp u 2 (μ.restrict K₀) :=
      ((hu.2 K₀ hK₀_compact hK₀U).1).memLp_trivial
    have hvalue :
        MemLp (fun z : H ↦ u (e.symm z)) 2
          (MeasureTheory.volume.restrict K) :=
      smoothPositiveMeasureOnManifold_chartPullback_memLp_on_compact_of_memLp
        (I := I) (μ := μ) hμ e he hK₀_compact hK₀_source hK_def hu_K₀
    have hduK_zero :
        ManifoldDifferentialField.chartPullback du e
          =ᵐ[MeasureTheory.volume.restrict K] 0 :=
      ae_restrict_of_ae_restrict_of_subset hKΩ hdu_coord_zero
    have hzero_mem :
        MemLp (0 : H → H →L[ℝ] ℝ) 2
          (MeasureTheory.volume.restrict K) := by
      refine ⟨aestronglyMeasurable_zero, ?_⟩
      change
        eLpNorm (0 : H → H →L[ℝ] ℝ) (2 : ℝ≥0∞)
          (MeasureTheory.volume.restrict K) < ⊤
      rw [eLpNorm_zero (α := H) (ε := H →L[ℝ] ℝ)
        (p := (2 : ℝ≥0∞)) (μ := MeasureTheory.volume.restrict K)]
      exact ENNReal.zero_lt_top
    have hderiv :
        MemLp (ManifoldDifferentialField.chartPullback du e) 2
          (MeasureTheory.volume.restrict K) :=
      (memLp_congr_ae hduK_zero).2 hzero_mem
    exact ⟨hvalue, hderiv⟩
  rcases
      euclideanSobolev_zero_gradient_locally_constant_finiteDimensional
        hΩ_open hweak_coord hmem_coord hdu_coord_zero (e x) hzΩ with
    ⟨W, hW_open, hzW, hWΩ, a, haW⟩
  let V : Set X := e.source ∩ e ⁻¹' W
  have hV_open : IsOpen V := by
    simpa [V] using e.isOpen_inter_preimage hW_open
  have hxV : x ∈ V := by
    exact ⟨hx_source, hzW⟩
  have hVU : V ⊆ U := by
    intro y hy
    have hyΩ : e y ∈ Ω := hWΩ hy.2
    simpa [Ω, manifoldChartRegion, e.left_inv hy.1] using hyΩ.2
  have hW_target : W ⊆ e.target := by
    intro z hz
    exact (hWΩ hz).1
  refine ⟨V, hV_open, hxV, hVU, a, ?_⟩
  simpa [V] using
    smoothPositiveMeasureOnManifold_ae_const_of_chart_ae_const
      (I := I) (μ := μ) hμ e he hW_open hW_target haW

/--
%%handwave
name:
  Zero weak gradient forces a constant on preconnected manifolds
statement:
  Let \(M\) be a finite-dimensional second-countable \(C^1\) real Riemannian
  manifold equipped with a smooth positive measure.  On a preconnected open
  region \(U\), if \(u\) is locally \(W^{1,2}\) and its weak differential
  vanishes almost everywhere on \(U\), then \(u\) is equal almost everywhere
  on \(U\) to one real constant.
proof:
  First obtain local almost-everywhere constants from
  [zero weak gradient gives local coordinate constants on manifolds](lean:JJMath.Uniformization.localSobolev_zero_gradient_locally_constant_on_manifold).
  Then glue those local constants across the preconnected region using
  [local almost-everywhere constants glue on preconnected manifolds](lean:JJMath.Uniformization.ae_local_constants_glue_on_preconnected_of_smooth_positive_measure).
tags:
  milestone
-/
theorem localSobolev_zero_gradient_constant_on_preconnected
    {H X : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    [IsManifold I 1 X] [FiniteDimensional ℝ H]
    {g : SmoothRiemannianMetricOnManifold I X} {μ : Measure X}
    (hμ : SmoothPositiveMeasureOnManifold (I := I) μ)
    {U : Set X} {u : X → ℝ} {du : ManifoldDifferentialField I X ℝ}
    (hU_open : IsOpen U) (hU_preconnected : IsPreconnected U)
    (hu : IsLocalSobolevH1OnManifoldWithValues (I := I) g μ U u du)
    (hdu_zero : ∀ᵐ x ∂μ.restrict U, du x = 0) :
    ∃ a : ℝ, ∀ᵐ x ∂μ.restrict U, u x = a := by
  exact
    ae_local_constants_glue_on_preconnected_of_smooth_positive_measure
      hμ hU_open hU_preconnected
      (localSobolev_zero_gradient_locally_constant_on_manifold
        hμ hU_open hu hdu_zero)

/--
%%handwave
name:
  Euclidean rigidity gives local coordinate constants
statement:
  On a surface with a smooth positive area measure, a locally \(W^{1,2}\)
  function whose weak gradient vanishes almost everywhere is locally almost
  everywhere constant in coordinate neighborhoods, provided the Euclidean
  zero-gradient rigidity principle is available in the coordinate plane.
proof:
  Around a point, choose a coordinate disk contained in the given open region.
  Pull the function and its weak gradient to that disk.  The coordinate
  distributional identity is exactly the Euclidean weak-derivative identity,
  and smooth positivity transfers the \(L^2\) and null-set hypotheses between
  the surface measure and Lebesgue measure.  Applying
  [the Euclidean zero-gradient conclusion](lean:JJMath.Uniformization.euclideanSobolev_zero_gradient_constant_on_preconnected)
  gives one constant on the coordinate disk, which is then pushed back to the
  surface neighborhood.
-/
theorem localSobolev_zero_gradient_locally_constant_of_euclidean
    (heuclid : EuclideanZeroGradientRigidityOnPlane)
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [SecondCountableTopology X] [IsManifold SurfaceRealModel 1 X]
    {μ : Measure X} (hμ : SmoothPositiveAreaMeasureOnSurface X μ)
    {U : Set X} {u : X → ℝ} {du : X → ℂ →L[ℝ] ℝ}
    (hU_open : IsOpen U)
    (hu : IsLocalSobolevH1OnSurface μ U u du)
    (hdu_zero : ∀ᵐ x ∂μ.restrict U, du x = 0) :
    ∀ x ∈ U, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ∃ a : ℝ, ∀ᵐ y ∂μ.restrict V, u y = a := by
  classical
  intro x hxU
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ x
  let Ω : Set ℂ := surfaceChartRegion e U
  let D : ℂ → ℂ →L[ℝ] ℝ :=
    ManifoldDifferentialField.chartPullback (I := SurfaceRealModel) du e
  let hμ' : SmoothPositiveMeasureOnManifold (I := SurfaceRealModel) μ :=
    { finite_on_compact := hμ.finite_on_compact
      chart_density := hμ.chart_density }
  have he : e ∈ atlas ℂ X := chart_mem_atlas ℂ x
  have hx_source : x ∈ e.source := by
    simpa [e] using mem_chart_source ℂ x
  have hzΩ : e x ∈ Ω := by
    refine ⟨e.map_source hx_source, ?_⟩
    simpa [e.left_inv hx_source] using hxU
  have hΩ_open : IsOpen Ω := by
    simpa [Ω, surfaceChartRegion] using e.isOpen_inter_preimage_symm hU_open
  have hweak_Ω :
      IsWeakDerivativeOnEuclideanRegionScalar Ω
        (fun z : ℂ ↦ u (e.symm z)) D := by
    intro φ v
    let ψ : SmoothCompactlySupportedCoordinateFunction Ω :=
      { toFun := φ
        smooth := φ.smooth
        support_subset := φ.support_subset
        compact_support := φ.compact_support }
    have h := hu.1 e he ψ v
    simpa [D, Ω, ψ, IsWeakDerivativeOnEuclideanRegionScalar,
      IsWeakDerivativeOnEuclideanRegionWithValues,
      ManifoldDifferentialField.chartPullback, surfaceChartRegion,
      surfaceChartTangentMap, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using h
  have hdu_Ω_zero :
      ∀ᵐ z ∂MeasureTheory.volume.restrict Ω, D z = 0 := by
    simpa [D, Ω, surfaceChartRegion, manifoldChartRegion] using
      smoothPositiveMeasureOnManifold_chartPullback_ae_zero
        (I := SurfaceRealModel) (μ := μ) hμ' e he hU_open hdu_zero
  rcases Metric.isOpen_iff.1 hΩ_open (e x) hzΩ with ⟨r, hr_pos, hballΩ⟩
  let B : Set ℂ := Metric.ball (e x) r
  have hweak_B :
      IsWeakDerivativeOnEuclideanRegionScalar B
        (fun z : ℂ ↦ u (e.symm z)) D :=
    IsWeakDerivativeOnEuclideanRegionWithValues.mono_set hweak_Ω hballΩ
  have hdu_B_zero : ∀ᵐ z ∂MeasureTheory.volume.restrict B, D z = 0 :=
    ae_restrict_of_ae_restrict_of_subset hballΩ hdu_Ω_zero
  have hmem_B :
      ∀ K : Set ℂ, IsCompact K → K ⊆ B →
        MemLp (fun z : ℂ ↦ u (e.symm z)) 2
            (MeasureTheory.volume.restrict K) ∧
          MemLp D 2 (MeasureTheory.volume.restrict K) := by
    intro K hK_compact hKB
    have hKΩ : K ⊆ Ω := hKB.trans hballΩ
    let K₀ : Set X := e.symm '' K
    have hK_target : K ⊆ e.target := fun z hz ↦ (hKΩ hz).1
    have hK₀_compact : IsCompact K₀ :=
      hK_compact.image_of_continuousOn (e.continuousOn_symm.mono hK_target)
    have hK₀_source : K₀ ⊆ e.source := by
      rintro y ⟨z, hzK, rfl⟩
      exact e.map_target (hK_target hzK)
    have hK₀U : K₀ ⊆ U := by
      rintro y ⟨z, hzK, rfl⟩
      exact (hKΩ hzK).2
    have hK_def : K = e '' K₀ := by
      ext z
      constructor
      · intro hzK
        refine ⟨e.symm z, ⟨z, hzK, rfl⟩, ?_⟩
        exact e.right_inv (hK_target hzK)
      · rintro ⟨y, ⟨w, hwK, rfl⟩, rfl⟩
        simpa [e.right_inv (hK_target hwK)] using hwK
    have hu_K₀ : MemLp u 2 (μ.restrict K₀) :=
      (hu.2 K₀ hK₀_compact hK₀U).1
    have hvalue :
        MemLp (fun z : ℂ ↦ u (e.symm z)) 2
          (MeasureTheory.volume.restrict K) :=
      smoothPositiveMeasureOnManifold_chartPullback_memLp_on_compact_of_memLp
        (I := SurfaceRealModel) (μ := μ) hμ' e he
        hK₀_compact hK₀_source hK_def hu_K₀
    have hduK_zero : D =ᵐ[MeasureTheory.volume.restrict K] 0 :=
      ae_restrict_of_ae_restrict_of_subset hKB hdu_B_zero
    have hzero_mem :
        MemLp (0 : ℂ → ℂ →L[ℝ] ℝ) 2
          (MeasureTheory.volume.restrict K) := by
      refine ⟨aestronglyMeasurable_zero, ?_⟩
      change
        eLpNorm (0 : ℂ → ℂ →L[ℝ] ℝ) (2 : ℝ≥0∞)
          (MeasureTheory.volume.restrict K) < ⊤
      rw [eLpNorm_zero (α := ℂ) (ε := ℂ →L[ℝ] ℝ)
        (p := (2 : ℝ≥0∞)) (μ := MeasureTheory.volume.restrict K)]
      exact ENNReal.zero_lt_top
    have hderiv : MemLp D 2 (MeasureTheory.volume.restrict K) :=
      (memLp_congr_ae hduK_zero).2 hzero_mem
    exact ⟨hvalue, hderiv⟩
  rcases
      heuclid Metric.isOpen_ball Metric.isPreconnected_ball
        hweak_B hmem_B hdu_B_zero with
    ⟨a, haB⟩
  let V : Set X := e.source ∩ e ⁻¹' B
  have hV_open : IsOpen V := by
    simpa [V, B] using e.isOpen_inter_preimage Metric.isOpen_ball
  have hxV : x ∈ V := by
    exact ⟨hx_source, by simpa [B, Metric.mem_ball] using hr_pos⟩
  have hVU : V ⊆ U := by
    intro y hy
    have hyΩ : e y ∈ Ω := hballΩ hy.2
    simpa [Ω, surfaceChartRegion, e.left_inv hy.1] using hyΩ.2
  have hB_target : B ⊆ e.target := by
    intro z hz
    exact (hballΩ hz).1
  refine ⟨V, hV_open, hxV, hVU, a, ?_⟩
  simpa [V] using
    smoothPositiveMeasureOnManifold_ae_const_of_chart_ae_const
      (I := SurfaceRealModel) (μ := μ) hμ' e he
      (by simpa [B] using Metric.isOpen_ball) hB_target haB

/--
%%handwave
name:
  Zero weak gradient rigidity for smooth positive area measures
statement:
  On a preconnected open surface region equipped with a smooth positive area
  measure, a locally \(W^{1,2}\) function whose weak gradient vanishes almost
  everywhere is equal almost everywhere to one real constant.
proof:
  First obtain local constants from
  [the Euclidean zero-gradient theorem in coordinate disks](lean:JJMath.Uniformization.localSobolev_zero_gradient_locally_constant_of_euclidean).
  Then apply
  [the preconnected gluing theorem for local almost-everywhere constants](lean:JJMath.Uniformization.ae_local_constants_glue_on_preconnected_of_smooth_positive_area).
-/
theorem localSobolev_zero_gradient_constant_on_preconnected_of_smooth_positive_area
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [SecondCountableTopology X] [IsManifold SurfaceRealModel 1 X]
    {μ : Measure X} (hμ : SmoothPositiveAreaMeasureOnSurface X μ)
    {U : Set X} {u : X → ℝ} {du : X → ℂ →L[ℝ] ℝ}
    (hU_open : IsOpen U) (hU_preconnected : IsPreconnected U)
    (hu : IsLocalSobolevH1OnSurface μ U u du)
    (hdu_zero : ∀ᵐ x ∂μ.restrict U, du x = 0) :
    ∃ a : ℝ, ∀ᵐ x ∂μ.restrict U, u x = a := by
  exact
    ae_local_constants_glue_on_preconnected_of_smooth_positive_area
      hμ hU_open hU_preconnected
      (localSobolev_zero_gradient_locally_constant_of_euclidean
        euclideanSobolev_zero_gradient_constant_on_preconnected
        hμ hU_open hu hdu_zero)

/--
%%handwave
name:
  Zero weak gradient forces a constant on surfaces
statement:
  On a preconnected open surface region \(U\), if \(u\in W^{1,2}_{loc}(U)\)
  and its weak gradient \(D u\) satisfies \(D u=0\) almost everywhere on
  \(U\), then there is \(a\in\mathbb R\) such that \(u=a\) almost everywhere
  on \(U\).
proof:
  Apply [the smooth-positive-area statement that zero weak gradient forces one almost-everywhere constant](lean:JJMath.Uniformization.localSobolev_zero_gradient_constant_on_preconnected_of_smooth_positive_area)
  to the Riemannian area measure, which is smooth and positive in coordinates.
-/
theorem localSobolev_zero_gradient_constant_on_preconnected_on_surface
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    {g : BackgroundSurfaceMetricOnSurface X} {U : Set X} {u : X → ℝ}
    {du : X → ℂ →L[ℝ] ℝ}
    (hU_open : IsOpen U) (hU_preconnected : IsPreconnected U)
    (hu : IsLocalSobolevH1OnSurface g.volume U u du)
    (hdu_zero : ∀ᵐ x ∂g.volume.restrict U, du x = 0) :
    ∃ a : ℝ, ∀ᵐ x ∂g.volume.restrict U, u x = a := by
  letI : IsManifold SurfaceRealModel ∞ X := g.metric.isManifold_real
  letI : IsManifold SurfaceRealModel 1 X := inferInstance
  exact
    localSobolev_zero_gradient_constant_on_preconnected_of_smooth_positive_area
      (μ := g.volume) (BackgroundSurfaceMetricOnSurface.volume_smooth_positive g)
      hU_open hU_preconnected hu hdu_zero

/--
%%handwave
name:
  A zero-gradient \(L^2\)-limit is a constant limit on compact subsets
statement:
  Let \(K\subset U\), with \(U\) open and preconnected.  If a sequence
  converges in \(L^2(K)\) to a locally Sobolev function whose weak
  differential is zero on \(U\), then the same sequence converges in
  \(L^2(K)\) to one constant.
proof:
  Zero-gradient rigidity on \(U\) identifies the limit with a constant almost
  everywhere on \(U\).  Restrict this almost-everywhere identity to \(K\) and
  replace the \(L^2(K)\)-limit representative by that constant.
-/
theorem localRellich_zeroGradient_constant_limit_on_compact
    {H X : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasureSpace H] [BorelSpace H]
    [Measure.IsAddHaarMeasure (volume : Measure H)]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    [IsManifold I 1 X] [FiniteDimensional ℝ H]
    {g : SmoothRiemannianMetricOnManifold I X} {μ : Measure X}
    (hμ : SmoothPositiveMeasureOnManifold (I := I) μ)
    {K U : Set X} (hKU : K ⊆ U) (hU_open : IsOpen U)
    (hU_preconnected : IsPreconnected U)
    {uSeq : ℕ → X → ℝ} {uLim : X → ℝ}
    (hlim : TendstoInLocalL2OnManifoldWithValues μ K uSeq uLim)
    (huLim : IsLocalSobolevH1OnManifoldWithValues (I := I) g μ U uLim
      (0 : ManifoldDifferentialField I X ℝ)) :
    ∃ a : ℝ, TendstoInLocalL2OnManifoldWithValues μ K uSeq (fun _ ↦ a) := by
  rcases
    localSobolev_zero_gradient_constant_on_preconnected
      (I := I) (g := g) (μ := μ) hμ hU_open hU_preconnected
      huLim (Filter.Eventually.of_forall fun _x ↦ rfl) with
    ⟨a, haU⟩
  refine ⟨a, ?_⟩
  have haK : ∀ᵐ x ∂μ.restrict K, uLim x = a :=
    ae_restrict_of_ae_restrict_of_subset hKU haU
  dsimp [TendstoInLocalL2OnManifoldWithValues] at hlim ⊢
  refine Filter.Tendsto.congr' ?_ hlim
  exact Filter.Eventually.of_forall fun n ↦ by
    exact eLpNorm_congr_ae <|
      haK.mono fun x hx ↦ by
        simp [hx]

/--
%%handwave
name:
  Vanishing-gradient Rellich limits satisfy the weak identity
statement:
  In the two-collar Rellich setting, if a subsequence converges in \(L^2(P)\)
  and the differential energy tends to zero on \(Q\), then the limiting
  function satisfies the weak-derivative identities on \(\operatorname{int}P\)
  with zero differential.
proof:
  Fix a compactly supported coordinate test in \(\operatorname{int}P\).  Its
  support is contained in \(P\), so the value pairing passes to the
  \(L^2(P)\)-limit.  The differential pairing tends to zero by the
  \(L^2(Q)\)-decay of the differentials and the compact support estimate for
  differential coordinate tests.  Passing to the limit in the weak identities
  for the approximating sequence gives the zero-differential identity.
-/
theorem localRellich_limit_zeroGradient_weakDerivative_on_interior_of_compact
    {H X : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [R1Space X] [T2Space X]
    [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [SecondCountableTopology X]
    [SecondCountableTopology (Bundle.TotalSpace ℝ (Bundle.Trivial X ℝ))]
    [TopologicalSpace.PseudoMetrizableSpace
      (Bundle.TotalSpace ℝ (Bundle.Trivial X ℝ))]
    [IsManifold I 1 X] [IsIdentityManifoldModel H I] [FiniteDimensional ℝ H]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := I) X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (ManifoldDifferentialTotalSpace (I := I) X ℝ)]
    {g : SmoothRiemannianMetricOnManifold I X} {μ : Measure X}
    (hμ : SmoothPositiveMeasureOnManifold (I := I) μ)
    {P Q U : Set X} (hP : IsCompact P) (hPQ : P ⊆ interior Q)
    (hQU : Q ⊆ U) (hQ : IsCompact Q) (hU_open : IsOpen U)
    (u : ℕ → X → ℝ) (du : ℕ → ManifoldDifferentialField I X ℝ)
    (hlocal : ∀ n : ℕ,
      IsLocalSobolevH1OnManifoldWithValues (I := I) g μ U (u n) (du n))
    (hbounded : BoundedInLocalSobolevH1OnManifoldWithValues (I := I) g μ Q u du)
    (hgrad_tendsto :
      Filter.Tendsto (fun n : ℕ ↦ manifoldLocalDifferentialSeminormSq I g μ Q (du n))
        Filter.atTop (𝓝 0))
    {uLim : X → ℝ} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hmemLimP : MemLp uLim 2 (μ.restrict P))
    (hlimP : TendstoInLocalL2OnManifoldWithValues μ P
      (fun n x ↦ u (φ n) x) uLim) :
    IsWeakDerivativeOnManifoldRegionBundle (I := I) (interior P) uLim
      (0 : ManifoldDifferentialField I X ℝ) := by
  classical
  letI : NormedAddCommGroup (ValueL2Section (X := X) (E := ℝ) μ) :=
    valueL2SectionNormedAddCommGroup (I := I) (X := X) (E := ℝ) μ
  letI : NormedAddCommGroup
      (ManifoldDifferentialL2Section (I := I) (X := X) (E := ℝ) g μ) :=
    manifoldDifferentialL2SectionNormedAddCommGroup
      (I := I) (X := X) (E := ℝ) g μ
  have hP_meas : MeasurableSet P := hP.measurableSet
  have hQ_meas : MeasurableSet Q := hQ.measurableSet
  have hPU : P ⊆ U := hPQ.trans (interior_subset.trans hQU)
  have hIntP_U : interior P ⊆ U := interior_subset.trans hPU
  have hmemSeqP :
      ∀ n : ℕ, MemLp (u (φ n)) 2 (μ.restrict P) := by
    intro n
    exact ((hlocal (φ n)).2 P hP hPU).1.memLp_trivial
  have hvalue_tendsto :
      Filter.Tendsto
        (fun n : ℕ ↦
          (Quotient.mk
            (SquareIntegrableValueSection.aeSetoid
              (X := X) (E := ℝ) (μ := μ))
            (squareIntegrableValueSectionIndicator hP_meas (u (φ n)) (hmemSeqP n)) :
            ValueL2Section (X := X) (E := ℝ) μ))
        Filter.atTop
        (𝓝
          (Quotient.mk
            (SquareIntegrableValueSection.aeSetoid
              (X := X) (E := ℝ) (μ := μ))
            (squareIntegrableValueSectionIndicator hP_meas uLim hmemLimP) :
            ValueL2Section (X := X) (E := ℝ) μ)) :=
    valueL2Section_indicator_tendsto_of_restrict_eLpNorm_tendsto_zero
      (I := I) (μ := μ) hP_meas hmemSeqP hmemLimP hlimP
  have hduSeqQ :
      ∀ n : ℕ,
        ManifoldDifferentialFieldMemHilbertSchmidtL2 (I := I) g
          (μ.restrict Q) (du (φ n)) := by
    intro n
    exact ((hlocal (φ n)).2 Q hQ hQU).2
  have hgrad_subseq :
      Filter.Tendsto
        (fun n : ℕ ↦
          manifoldLocalDifferentialSeminormSq I g μ Q (du (φ n)))
        Filter.atTop (𝓝 0) :=
    hgrad_tendsto.comp hφ.tendsto_atTop
  have hdifferential_tendsto :
      Filter.Tendsto
        (fun n : ℕ ↦
          (Quotient.mk
            (SquareIntegrableManifoldDifferentialField.aeSetoid
              (I := I) (X := X) (E := ℝ) (g := g) (μ := μ))
            ({ toSection := manifoldDifferentialFieldZeroExtend I Q (du (φ n))
               memL2 :=
                manifoldDifferentialFieldMemHilbertSchmidtL2_zero_extend_of_restrict
                  (I := I) (g := g) (μ := μ) hQ_meas (hduSeqQ n) } :
              SquareIntegrableManifoldDifferentialField
                (I := I) (X := X) (E := ℝ) g μ) :
            ManifoldDifferentialL2Section (I := I) (X := X) (E := ℝ) g μ))
        Filter.atTop
        (𝓝 (0 :
          ManifoldDifferentialL2Section (I := I) (X := X) (E := ℝ) g μ)) :=
    manifoldDifferentialL2Section_zeroExtend_tendsto_zero_of_localSeminormSq_tendsto_zero
      (I := I) (g := g) (μ := μ) hQ_meas (fun n : ℕ ↦ du (φ n))
      hduSeqQ hgrad_subseq
  intro e he test v
  let ΩP : Set H := manifoldChartRegion e (interior P)
  let ΩU : Set H := manifoldChartRegion e U
  let ΩAll : Set H := manifoldChartRegion e (Set.univ : Set X)
  have hΩP_U : ΩP ⊆ ΩU := by
    intro z hz
    exact ⟨hz.1, hIntP_U hz.2⟩
  have hΩP_univ : ΩP ⊆ ΩAll := by
    intro z hz
    exact ⟨hz.1, trivial⟩
  let psiAll : SmoothCompactlySupportedManifoldCoordinateFunction ΩAll :=
    { toFun := test
      smooth := test.smooth
      support_subset := by
        intro z hz
        exact hΩP_univ (test.support_subset hz)
      compact_support := test.compact_support }
  let ψU : SmoothCompactlySupportedManifoldCoordinateFunction ΩU :=
    { toFun := test
      smooth := test.smooth
      support_subset := by
        intro z hz
        exact hΩP_U (test.support_subset hz)
      compact_support := test.compact_support }
  let valueSeq : ℕ → SquareIntegrableValueSection (X := X) (E := ℝ) μ :=
    fun n ↦ squareIntegrableValueSectionIndicator hP_meas (u (φ n)) (hmemSeqP n)
  let valueLim : SquareIntegrableValueSection (X := X) (E := ℝ) μ :=
    squareIntegrableValueSectionIndicator hP_meas uLim hmemLimP
  let diffSeq :
      ℕ → SquareIntegrableManifoldDifferentialField
        (I := I) (X := X) (E := ℝ) g μ :=
    fun n ↦
      { toSection := manifoldDifferentialFieldZeroExtend I Q (du (φ n))
        memL2 :=
          manifoldDifferentialFieldMemHilbertSchmidtL2_zero_extend_of_restrict
            (I := I) (g := g) (μ := μ) hQ_meas (hduSeqQ n) }
  let G :=
    manifoldDifferentialHilbertBundleGeometry
      (I := I) (X := X) (E := ℝ) g
  let metric :=
    manifoldDifferentialHilbertSchmidtContinuousRiemannianMetric
      (I := I) (X := X) (E := ℝ) g
  letI : Bundle.RiemannianBundle
      (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := ℝ)) :=
    ⟨metric.toRiemannianMetric⟩
  letI (x : X) :
      NormedAddCommGroup (ManifoldDifferentialBundleFiber
        (I := I) (X := X) (E := ℝ) x) :=
    manifoldDifferentialHilbertSchmidtNormedAddCommGroup
      (I := I) (X := X) (E := ℝ) metric x
  letI (x : X) :
      InnerProductSpace ℝ (ManifoldDifferentialBundleFiber
        (I := I) (X := X) (E := ℝ) x) :=
    manifoldDifferentialHilbertSchmidtInnerProductSpace
      (I := I) (X := X) (E := ℝ) metric x
  let diffZero :
      SquareIntegrableManifoldDifferentialField
        (I := I) (X := X) (E := ℝ) g μ :=
    { toSection := 0
      memL2 := hilbertBundleSectionMemL2_zero
        (I := I) (G := G) (by intro x A B; rfl) μ }
  rcases
    manifoldValueCoordinateTestPairing_tendsto_of_tendsto_l2_sections
      (I := I) (X := X) (E := ℝ) μ hμ
      (u := valueSeq) (uLim := valueLim)
      (uLimClass :=
        (Quotient.mk
          (SquareIntegrableValueSection.aeSetoid
            (X := X) (E := ℝ) (μ := μ)) valueLim :
          ValueL2Section (X := X) (E := ℝ) μ))
      rfl (by simpa [valueSeq, valueLim] using hvalue_tendsto)
      e he psiAll v with
    ⟨hleftLim_ext_int, hleft_ext_tendsto⟩
  have hdiffZero_eq :
      (Quotient.mk
        (SquareIntegrableManifoldDifferentialField.aeSetoid
          (I := I) (X := X) (E := ℝ) (g := g) (μ := μ)) diffZero :
        ManifoldDifferentialL2Section (I := I) (X := X) (E := ℝ) g μ) =
        (0 : ManifoldDifferentialL2Section (I := I) (X := X) (E := ℝ) g μ) := by
    rfl
  rcases
    manifoldDifferentialCoordinateTestPairing_tendsto_of_tendsto_l2_sections
      (I := I) (X := X) (E := ℝ) g μ hμ
      (du := diffSeq) (duLim := diffZero)
      (duLimClass :=
        (0 : ManifoldDifferentialL2Section (I := I) (X := X) (E := ℝ) g μ))
      hdiffZero_eq (by simpa [diffSeq] using hdifferential_tendsto)
      e he psiAll v with
    ⟨_hrightLim_ext_int, hright_ext_tendsto⟩
  let leftLim : H → ℝ :=
    fun z ↦ (fderiv ℝ (test : H → ℝ) z v) • uLim (e.symm z)
  let rightZero : H → ℝ :=
    fun z ↦ test z • ManifoldDifferentialField.evalChart
      (0 : ManifoldDifferentialField I X ℝ) e z v
  let leftExt : ℕ → H → ℝ :=
    fun n z ↦
      (fderiv ℝ (psiAll : H → ℝ) z v) • (valueSeq n).toFunction (e.symm z)
  let leftOrig : ℕ → H → ℝ :=
    fun n z ↦ (fderiv ℝ (test : H → ℝ) z v) • u (φ n) (e.symm z)
  let rightExt : ℕ → H → ℝ :=
    fun n z ↦
      psiAll z • ManifoldDifferentialField.evalChart (diffSeq n).toField e z v
  let rightOrig : ℕ → H → ℝ :=
    fun n z ↦ test z • ManifoldDifferentialField.evalChart (du (φ n)) e z v
  have leftOrig_zero_P :
      ∀ z : H, z ∉ ΩP → leftLim z = 0 := by
    intro z hzP
    have hz_not :
        z ∉ tsupport (fun y : H ↦ fderiv ℝ (test : H → ℝ) y v) := by
      intro hz
      exact hzP <| test.support_subset <|
        (tsupport_fderiv_apply_subset (𝕜 := ℝ)
          (f := (test : H → ℝ)) v) hz
    have hzero :
        fderiv ℝ (test : H → ℝ) z v = 0 :=
      image_eq_zero_of_notMem_tsupport
        (f := fun y : H ↦ fderiv ℝ (test : H → ℝ) y v) hz_not
    simp [leftLim, hzero]
  have hleftLim_ext_eq :
      (fun z : H ↦
        (fderiv ℝ (psiAll : H → ℝ) z v) • valueLim.toFunction (e.symm z)) =
        leftLim := by
    funext z
    by_cases hzP : z ∈ ΩP
    · have hxP : e.symm z ∈ P := interior_subset hzP.2
      simp [leftLim, valueLim, squareIntegrableValueSectionIndicator,
        SquareIntegrableValueSection.toFunction, psiAll, hxP]
    · have hz_not :
          z ∉ tsupport (fun y : H ↦ fderiv ℝ (test : H → ℝ) y v) := by
        intro hz
        exact hzP <| test.support_subset <|
          (tsupport_fderiv_apply_subset (𝕜 := ℝ)
            (f := (test : H → ℝ)) v) hz
      have hderiv_zero :
          fderiv ℝ (test : H → ℝ) z v = 0 :=
        image_eq_zero_of_notMem_tsupport
          (f := fun y : H ↦ fderiv ℝ (test : H → ℝ) y v) hz_not
      simp [leftLim, valueLim, squareIntegrableValueSectionIndicator,
        SquareIntegrableValueSection.toFunction, psiAll, hderiv_zero]
  have hleftLim_int_P : Integrable leftLim (MeasureTheory.volume.restrict ΩP) := by
    have hres := hleftLim_ext_int.restrict (s := ΩP)
    have hres' :
        Integrable
          (fun z : H ↦
            (fderiv ℝ (psiAll : H → ℝ) z v) • valueLim.toFunction (e.symm z))
          (MeasureTheory.volume.restrict ΩP) := by
      simpa [ΩP, ΩAll, Measure.restrict_restrict_of_subset hΩP_univ] using hres
    exact hres'.congr (Filter.EventuallyEq.of_eq hleftLim_ext_eq)
  have hrightZero_int_P :
      Integrable rightZero (MeasureTheory.volume.restrict ΩP) := by
    have hzero : rightZero = fun _ : H ↦ (0 : ℝ) := by
      funext z
      simp [rightZero, ManifoldDifferentialField.evalChart]
    rw [hzero]
    exact integrable_zero H ℝ (MeasureTheory.volume.restrict ΩP)
  have hrightZero_integral :
      ∫ z in ΩP, rightZero z ∂MeasureTheory.volume = 0 := by
    have hzero : rightZero = fun _ : H ↦ (0 : ℝ) := by
      funext z
      simp [rightZero, ManifoldDifferentialField.evalChart]
    rw [hzero]
    simp
  have hleftLim_global_eq_local :
      ∫ z in ΩAll,
          (fderiv ℝ (psiAll : H → ℝ) z v) • valueLim.toFunction (e.symm z)
          ∂MeasureTheory.volume =
        ∫ z in ΩP, leftLim z ∂MeasureTheory.volume := by
    rw [integral_congr_ae (Filter.Eventually.of_forall fun z ↦
      congrFun hleftLim_ext_eq z)]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun z hz ↦ leftOrig_zero_P z (fun hzP ↦ hz (hΩP_univ hzP))),
      setIntegral_eq_integral_of_forall_compl_eq_zero leftOrig_zero_P]
  have hrightZero_global :
      ∫ z in ΩAll,
          psiAll z • ManifoldDifferentialField.evalChart diffZero.toField e z v
          ∂MeasureTheory.volume = 0 := by
    have hzero :
        (fun z : H ↦
          psiAll z • ManifoldDifferentialField.evalChart diffZero.toField e z v) =
          fun _ : H ↦ (0 : ℝ) := by
      funext z
      simp [diffZero, SquareIntegrableManifoldDifferentialField.toField,
        ManifoldDifferentialField.evalChart]
    rw [hzero]
    simp
  have hleft_ext_eq_orig :
      ∀ n : ℕ, leftExt n = leftOrig n := by
    intro n
    funext z
    by_cases hzP : z ∈ ΩP
    · have hxP : e.symm z ∈ P := interior_subset hzP.2
      simp [leftExt, leftOrig, valueSeq, squareIntegrableValueSectionIndicator,
        SquareIntegrableValueSection.toFunction, psiAll, hxP]
    · have hz_not :
          z ∉ tsupport (fun y : H ↦ fderiv ℝ (test : H → ℝ) y v) := by
        intro hz
        exact hzP <| test.support_subset <|
          (tsupport_fderiv_apply_subset (𝕜 := ℝ)
            (f := (test : H → ℝ)) v) hz
      have hderiv_zero :
          fderiv ℝ (test : H → ℝ) z v = 0 :=
        image_eq_zero_of_notMem_tsupport
          (f := fun y : H ↦ fderiv ℝ (test : H → ℝ) y v) hz_not
      simp [leftExt, leftOrig, valueSeq, squareIntegrableValueSectionIndicator,
        SquareIntegrableValueSection.toFunction, psiAll, hderiv_zero]
  have hright_ext_eq_orig :
      ∀ n : ℕ, rightExt n = rightOrig n := by
    intro n
    funext z
    by_cases hzP : z ∈ ΩP
    · have hxQ : e.symm z ∈ Q :=
        interior_subset (hPQ (interior_subset hzP.2))
      have heval_eq :
          ManifoldDifferentialField.evalChart (diffSeq n).toField e z v =
            ManifoldDifferentialField.evalChart (du (φ n)) e z v := by
        simp [diffSeq, SquareIntegrableManifoldDifferentialField.toField,
          manifoldDifferentialFieldZeroExtend, ManifoldDifferentialField.evalChart, hxQ]
      change
        psiAll z • ManifoldDifferentialField.evalChart (diffSeq n).toField e z v =
          test z • ManifoldDifferentialField.evalChart (du (φ n)) e z v
      rw [heval_eq]
    · have hz_not : z ∉ tsupport (test : H → ℝ) := by
        intro hz
        exact hzP (test.support_subset hz)
      have htest_zero : test z = 0 :=
        image_eq_zero_of_notMem_tsupport hz_not
      simp [rightExt, rightOrig, diffSeq, psiAll, htest_zero]
  have hleftOrig_zero :
      ∀ n : ℕ, ∀ z : H, z ∉ ΩP → leftOrig n z = 0 := by
    intro n z hzP
    have hz_not :
        z ∉ tsupport (fun y : H ↦ fderiv ℝ (test : H → ℝ) y v) := by
      intro hz
      exact hzP <| test.support_subset <|
        (tsupport_fderiv_apply_subset (𝕜 := ℝ)
          (f := (test : H → ℝ)) v) hz
    have hderiv_zero :
        fderiv ℝ (test : H → ℝ) z v = 0 :=
      image_eq_zero_of_notMem_tsupport
        (f := fun y : H ↦ fderiv ℝ (test : H → ℝ) y v) hz_not
    simp [leftOrig, hderiv_zero]
  have hrightOrig_zero :
      ∀ n : ℕ, ∀ z : H, z ∉ ΩP → rightOrig n z = 0 := by
    intro n z hzP
    have hz_not : z ∉ tsupport (test : H → ℝ) := by
      intro hz
      exact hzP (test.support_subset hz)
    have htest_zero : test z = 0 :=
      image_eq_zero_of_notMem_tsupport hz_not
    simp [rightOrig, htest_zero]
  have hleft_ext_eq_U :
      ∀ n : ℕ,
        ∫ z in ΩAll, leftExt n z ∂MeasureTheory.volume =
          ∫ z in ΩU, leftOrig n z ∂MeasureTheory.volume := by
    intro n
    rw [hleft_ext_eq_orig n]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun z hz ↦ hleftOrig_zero n z (fun hzP ↦ hz (hΩP_univ hzP))),
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun z hz ↦ hleftOrig_zero n z (fun hzP ↦ hz (hΩP_U hzP)))]
  have hright_ext_eq_U :
      ∀ n : ℕ,
        ∫ z in ΩAll, rightExt n z ∂MeasureTheory.volume =
          ∫ z in ΩU, rightOrig n z ∂MeasureTheory.volume := by
    intro n
    rw [hright_ext_eq_orig n]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun z hz ↦ hrightOrig_zero n z (fun hzP ↦ hz (hΩP_univ hzP))),
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun z hz ↦ hrightOrig_zero n z (fun hzP ↦ hz (hΩP_U hzP)))]
  have hweak_ext :
      ∀ n : ℕ,
        ∫ z in ΩAll, leftExt n z ∂MeasureTheory.volume =
          -∫ z in ΩAll, rightExt n z ∂MeasureTheory.volume := by
    intro n
    rcases (hlocal (φ n)).1 e he ψU v with ⟨_hL, _hR, hweak⟩
    calc
      ∫ z in ΩAll, leftExt n z ∂MeasureTheory.volume
          = ∫ z in ΩU, leftOrig n z ∂MeasureTheory.volume :=
            hleft_ext_eq_U n
      _ = -∫ z in ΩU, rightOrig n z ∂MeasureTheory.volume := by
            simpa [leftOrig, rightOrig, ψU, ΩU] using hweak
      _ = -∫ z in ΩAll, rightExt n z ∂MeasureTheory.volume := by
            rw [hright_ext_eq_U n]
  have hleft_tendsto :
      Filter.Tendsto
        (fun n : ℕ ↦ ∫ z in ΩAll, leftExt n z ∂MeasureTheory.volume)
        Filter.atTop
        (𝓝 (∫ z in ΩAll,
          (fderiv ℝ (psiAll : H → ℝ) z v) • valueLim.toFunction (e.symm z)
          ∂MeasureTheory.volume)) := by
    simpa [leftExt, valueSeq, ΩAll] using hleft_ext_tendsto
  have hright_tendsto_zero :
      Filter.Tendsto
        (fun n : ℕ ↦ ∫ z in ΩAll, rightExt n z ∂MeasureTheory.volume)
        Filter.atTop (𝓝 0) := by
    have hright_tendsto :
        Filter.Tendsto
          (fun n : ℕ ↦ ∫ z in ΩAll, rightExt n z ∂MeasureTheory.volume)
          Filter.atTop
          (𝓝 (∫ z in ΩAll,
            psiAll z • ManifoldDifferentialField.evalChart diffZero.toField e z v
            ∂MeasureTheory.volume)) := by
      simpa [rightExt, diffSeq, ΩAll] using hright_ext_tendsto
    rw [hrightZero_global] at hright_tendsto
    exact hright_tendsto
  have hleft_global_zero :
      ∫ z in ΩAll,
          (fderiv ℝ (psiAll : H → ℝ) z v) • valueLim.toFunction (e.symm z)
          ∂MeasureTheory.volume =
        -(0 : ℝ) := by
    have hneg_tendsto_left :
        Filter.Tendsto
          (fun n : ℕ ↦ -∫ z in ΩAll, rightExt n z ∂MeasureTheory.volume)
          Filter.atTop
          (𝓝 (∫ z in ΩAll,
            (fderiv ℝ (psiAll : H → ℝ) z v) • valueLim.toFunction (e.symm z)
            ∂MeasureTheory.volume)) := by
      exact Filter.Tendsto.congr'
        (Filter.Eventually.of_forall fun n ↦ hweak_ext n) hleft_tendsto
    have hneg_tendsto_zero :
        Filter.Tendsto
          (fun n : ℕ ↦ -∫ z in ΩAll, rightExt n z ∂MeasureTheory.volume)
          Filter.atTop (𝓝 (-(0 : ℝ))) :=
      hright_tendsto_zero.neg
    exact tendsto_nhds_unique hneg_tendsto_left hneg_tendsto_zero
  refine ⟨?_, ?_, ?_⟩
  · simpa [leftLim, ΩP] using hleftLim_int_P
  · simpa [rightZero, ΩP] using hrightZero_int_P
  · calc
      ∫ z in manifoldChartRegion e (interior P),
          (fderiv ℝ (test : H → ℝ) z v) • uLim (e.symm z)
          ∂MeasureTheory.volume
          = ∫ z in ΩP, leftLim z ∂MeasureTheory.volume := rfl
      _ = ∫ z in ΩAll,
          (fderiv ℝ (psiAll : H → ℝ) z v) • valueLim.toFunction (e.symm z)
          ∂MeasureTheory.volume := hleftLim_global_eq_local.symm
      _ = -(0 : ℝ) := hleft_global_zero
      _ = -∫ z in ΩP, rightZero z ∂MeasureTheory.volume := by
            rw [hrightZero_integral]
      _ = -∫ z in manifoldChartRegion e (interior P),
          test z • ManifoldDifferentialField.evalChart
            (0 : ManifoldDifferentialField I X ℝ) e z v
          ∂MeasureTheory.volume := rfl

/--
%%handwave
name:
  Rellich limits with vanishing differentials have zero weak differential
statement:
  Let \(P\subset\operatorname{int}Q\subset Q\subset U\), with \(P,Q\)
  compact.  Suppose \(u_n\) is locally \(W^{1,2}\) on \(U\), uniformly
  \(W^{1,2}\)-bounded on \(Q\), and its differential energy on \(Q\) tends to
  zero.  If a subsequence converges in \(L^2(P)\) to \(u\), then \(u\) is
  locally Sobolev on \(\operatorname{int}P\) and has zero weak differential
  there.
proof:
  This is the localized closed-graph step.  Test functions supported in
  \(\operatorname{int}P\) have compact support contained in \(P\).  The value
  pairings pass to the \(L^2(P)\)-limit, while the differential pairings tend
  to zero because the differential \(L^2(Q)\)-norm tends to zero and
  \(P\subset\operatorname{int}Q\).
-/
theorem localRellich_limit_zeroGradient_on_interior_of_compact
    {H X : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [R1Space X] [T2Space X]
    [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [SecondCountableTopology X]
    [SecondCountableTopology (Bundle.TotalSpace ℝ (Bundle.Trivial X ℝ))]
    [TopologicalSpace.PseudoMetrizableSpace
      (Bundle.TotalSpace ℝ (Bundle.Trivial X ℝ))]
    [IsManifold I 1 X] [IsIdentityManifoldModel H I] [FiniteDimensional ℝ H]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := I) X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (ManifoldDifferentialTotalSpace (I := I) X ℝ)]
    {g : SmoothRiemannianMetricOnManifold I X} {μ : Measure X}
    (hμ : SmoothPositiveMeasureOnManifold (I := I) μ)
    {P Q U : Set X} (hP : IsCompact P) (hPQ : P ⊆ interior Q)
    (hQU : Q ⊆ U) (hQ : IsCompact Q) (hU_open : IsOpen U)
    (u : ℕ → X → ℝ) (du : ℕ → ManifoldDifferentialField I X ℝ)
    (hlocal : ∀ n : ℕ,
      IsLocalSobolevH1OnManifoldWithValues (I := I) g μ U (u n) (du n))
    (hbounded : BoundedInLocalSobolevH1OnManifoldWithValues (I := I) g μ Q u du)
    (hgrad_tendsto :
      Filter.Tendsto (fun n : ℕ ↦ manifoldLocalDifferentialSeminormSq I g μ Q (du n))
        Filter.atTop (𝓝 0))
    {uLim : X → ℝ} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hmemLimP : MemLp uLim 2 (μ.restrict P))
    (hlimP : TendstoInLocalL2OnManifoldWithValues μ P
      (fun n x ↦ u (φ n) x) uLim) :
    IsLocalSobolevH1OnManifoldWithValues (I := I) g μ (interior P) uLim
      (0 : ManifoldDifferentialField I X ℝ) := by
  refine ⟨?_, ?_⟩
  · exact
      localRellich_limit_zeroGradient_weakDerivative_on_interior_of_compact
        (I := I) (g := g) (μ := μ) hμ hP hPQ hQU hQ hU_open
        u du hlocal hbounded hgrad_tendsto hφ hmemLimP hlimP
  · intro K hK hK_subset
    have hKP : K ⊆ P := hK_subset.trans interior_subset
    have hmemLimK : MemLp uLim 2 (μ.restrict K) :=
      hmemLimP.mono_measure (Measure.restrict_mono hKP le_rfl)
    let G :=
      manifoldDifferentialHilbertBundleGeometry
        (I := I) (X := X) (E := ℝ) g
    let metric :=
      manifoldDifferentialHilbertSchmidtContinuousRiemannianMetric
        (I := I) (X := X) (E := ℝ) g
    letI : Bundle.RiemannianBundle
        (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := ℝ)) :=
      ⟨metric.toRiemannianMetric⟩
    letI (x : X) :
        NormedAddCommGroup (ManifoldDifferentialBundleFiber
          (I := I) (X := X) (E := ℝ) x) :=
      manifoldDifferentialHilbertSchmidtNormedAddCommGroup
        (I := I) (X := X) (E := ℝ) metric x
    letI (x : X) :
        InnerProductSpace ℝ (ManifoldDifferentialBundleFiber
          (I := I) (X := X) (E := ℝ) x) :=
      manifoldDifferentialHilbertSchmidtInnerProductSpace
        (I := I) (X := X) (E := ℝ) metric x
    refine ⟨trivial_real_hilbertBundleSectionMemL2_of_memLp hmemLimK, ?_⟩
    exact
      hilbertBundleSectionMemL2_zero
        (I := I) (G := G) (by intro x A B; rfl) (μ.restrict K)

/--
%%handwave
name:
  Two-collar Rellich compactness with vanishing gradients gives constants
statement:
  Let \(K\subset\operatorname{int}P\subset P\subset
  \operatorname{int}Q\subset Q\subset U\), where \(K,P,Q\) are compact and
  \(\operatorname{int}P\) is preconnected.  If a sequence of real-valued
  locally \(W^{1,2}\) functions is uniformly \(W^{1,2}\)-bounded on \(Q\) and
  its weak differentials tend to zero in \(L^2(Q)\), then a subsequence
  converges in \(L^2(K)\) to a constant function.
proof:
  Apply local Rellich compactness to obtain a subsequence converging in
  \(L^2(P)\).  The localized closed-graph step shows that the \(P\)-limit has
  zero weak differential on \(\operatorname{int}P\).  Since
  \(\operatorname{int}P\) is preconnected, zero-gradient rigidity makes the
  limit a single constant there, and the \(L^2(P)\)-convergence restricts to
  \(K\).
-/
theorem localRellich_zeroGradient_subsequence_constant_on_preconnected_interior
    {H X : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [R1Space X] [T2Space X]
    [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [SecondCountableTopology X]
    [SecondCountableTopology (Bundle.TotalSpace ℝ (Bundle.Trivial X ℝ))]
    [TopologicalSpace.PseudoMetrizableSpace
      (Bundle.TotalSpace ℝ (Bundle.Trivial X ℝ))]
    [IsManifold I 1 X] [IsIdentityManifoldModel H I] [FiniteDimensional ℝ H]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := I) X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (ManifoldDifferentialTotalSpace (I := I) X ℝ)]
    {g : SmoothRiemannianMetricOnManifold I X} {μ : Measure X}
    (hμ : SmoothPositiveMeasureOnManifold (I := I) μ)
    {K P Q U : Set X} (_hK : IsCompact K) (hKP : K ⊆ interior P)
    (hP : IsCompact P) (hPQ : P ⊆ interior Q) (hQU : Q ⊆ U)
    (hQ : IsCompact Q) (hU_open : IsOpen U)
    (hP_preconnected : IsPreconnected (interior P))
    (u : ℕ → X → ℝ) (du : ℕ → ManifoldDifferentialField I X ℝ)
    (hlocal : ∀ n : ℕ,
      IsLocalSobolevH1OnManifoldWithValues (I := I) g μ U (u n) (du n))
    (hbounded : BoundedInLocalSobolevH1OnManifoldWithValues (I := I) g μ Q u du)
    (hgrad_tendsto :
      Filter.Tendsto (fun n : ℕ ↦ manifoldLocalDifferentialSeminormSq I g μ Q (du n))
        Filter.atTop (𝓝 0)) :
    ∃ (a : ℝ) (φ : ℕ → ℕ),
      StrictMono φ ∧
        TendstoInLocalL2OnManifoldWithValues μ K (fun n x ↦ u (φ n) x)
          (fun _ ↦ a) := by
  rcases
    localRellich_subsequence_on_compact_with_memLp
      (I := I) (g := g) (μ := μ) hμ
      hP hPQ hQU hQ hU_open u du hlocal hbounded with
    ⟨uLim, φ, hmemLimP, hφ, hlimP⟩
  have huLim_zero :
      IsLocalSobolevH1OnManifoldWithValues (I := I) g μ (interior P) uLim
        (0 : ManifoldDifferentialField I X ℝ) :=
    localRellich_limit_zeroGradient_on_interior_of_compact
      (I := I) (g := g) (μ := μ) hμ
      hP hPQ hQU hQ hU_open u du hlocal hbounded hgrad_tendsto
      hφ hmemLimP hlimP
  have hlimK :
      TendstoInLocalL2OnManifoldWithValues μ K
        (fun n x ↦ u (φ n) x) uLim :=
    hlimP.mono_set (hKP.trans interior_subset)
  rcases
    localRellich_zeroGradient_constant_limit_on_compact
      (I := I) (g := g) (μ := μ) hμ hKP isOpen_interior hP_preconnected
      hlimK huLim_zero with
    ⟨a, hlim_const⟩
  exact ⟨a, φ, hφ, hlim_const⟩

/--
%%handwave
name:
  Rellich compactness with vanishing gradients gives constants
statement:
  Let \(M\) be a finite-dimensional second-countable \(C^1\) real Riemannian
  manifold, equipped with a smooth positive measure.  Let
  \(K\subset\operatorname{int}P\subset P\subset\operatorname{int}Q\subset
  Q\subset U\), where \(K,P,Q\) are compact, \(U\) is open, and
  \(\operatorname{int}P\) is preconnected.  If a sequence of real-valued
  locally \(W^{1,2}\) functions is uniformly \(W^{1,2}\)-bounded on \(Q\) and
  its weak differentials tend to zero in \(L^2(Q)\), then a subsequence
  converges in \(L^2(K)\) to a constant function.
proof:
  Apply [the two-collar Rellich extraction principle](lean:JJMath.Uniformization.localRellich_zeroGradient_subsequence_constant_on_preconnected_interior).
-/
theorem localRellich_zeroGradient_subsequence_constant
    {H X : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [R1Space X] [T2Space X]
    [ChartedSpace H X]
    [MeasureSpace H] [BorelSpace H] [Measure.IsAddHaarMeasure (volume : Measure H)]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X] [SecondCountableTopology X]
    [SecondCountableTopology (Bundle.TotalSpace ℝ (Bundle.Trivial X ℝ))]
    [TopologicalSpace.PseudoMetrizableSpace
      (Bundle.TotalSpace ℝ (Bundle.Trivial X ℝ))]
    [IsManifold I 1 X] [IsIdentityManifoldModel H I] [FiniteDimensional ℝ H]
    [SecondCountableTopology (ManifoldDifferentialTotalSpace (I := I) X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (ManifoldDifferentialTotalSpace (I := I) X ℝ)]
    {g : SmoothRiemannianMetricOnManifold I X} {μ : Measure X}
    (hμ : SmoothPositiveMeasureOnManifold (I := I) μ)
    {K P Q U : Set X} (hK : IsCompact K) (hKP : K ⊆ interior P)
    (hP : IsCompact P) (hPQ : P ⊆ interior Q) (hQU : Q ⊆ U)
    (hQ : IsCompact Q) (hU_open : IsOpen U)
    (hP_preconnected : IsPreconnected (interior P))
    (u : ℕ → X → ℝ) (du : ℕ → ManifoldDifferentialField I X ℝ)
    (hlocal : ∀ n : ℕ,
      IsLocalSobolevH1OnManifoldWithValues (I := I) g μ U (u n) (du n))
    (hbounded : BoundedInLocalSobolevH1OnManifoldWithValues (I := I) g μ Q u du)
    (hgrad_tendsto :
      Filter.Tendsto (fun n : ℕ ↦ manifoldLocalDifferentialSeminormSq I g μ Q (du n))
        Filter.atTop (𝓝 0)) :
    ∃ (a : ℝ) (φ : ℕ → ℕ),
      StrictMono φ ∧
        TendstoInLocalL2OnManifoldWithValues μ K (fun n x ↦ u (φ n) x)
          (fun _ ↦ a) := by
  exact
    localRellich_zeroGradient_subsequence_constant_on_preconnected_interior
      (I := I) (g := g) (μ := μ) hμ hK hKP hP hPQ hQU hQ hU_open
      hP_preconnected u du hlocal hbounded hgrad_tendsto

end

end Uniformization

end JJMath
