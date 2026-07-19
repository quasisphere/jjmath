import JJMath.PotentialTheory.EnergyMethod.Regularity
import JJMath.PotentialTheory.EnergyMethod.MazurLemma
import JJMath.Uniformization.GreenFunctionCompactSuperlevel
import JJMath.AnalyticContinuation.LocalBranch
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Energy method: simply connected zero trace at infinity

This file isolates the remaining topological-capacitary input for the energy
method.  The intended use is to replace a too-strong cocompact vanishing leaf
by the exact property needed downstream: compactness of positive superlevel
sets of the regular Green potential.
-/

namespace JJMath

open MeasureTheory
open scoped Manifold Topology ENNReal ContDiff Convolution

namespace Uniformization

open ContinuousLinearMap

/--
%%handwave
name:
  Smooth positive area measures have no atoms
statement:
  If \(\mu\) is a smooth positive area measure on a surface \(X\), then
  \(\mu(\{p\})=0\) for every \(p\in X\).
proof:
  In a chart about \(p\), the pushforward of \(\mu\) has a smooth density with
  respect to planar Lebesgue measure.  A singleton has Lebesgue measure zero,
  and injectivity of the chart transfers this back to \(\{p\}\).
-/
theorem smoothPositiveAreaMeasureOnSurface_measure_singleton
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    (μ : Measure X) (hμ : SmoothPositiveAreaMeasureOnSurface X μ)
    (p : X) :
    μ {p} = 0 := by
  classical
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ p
  have he : e ∈ atlas ℂ X := chart_mem_atlas ℂ p
  have hp_source : p ∈ e.source := by
    simpa [e] using chartAt_source_mem ℂ p
  rcases hμ.chart_density e he with ⟨ρ, _hρ_smooth, _hρ_pos, hmap⟩
  have hmap_singleton :
      (Measure.map e (μ.restrict e.source)) ({e p} : Set ℂ) = 0 := by
    rw [hmap]
    exact measure_singleton (x := e p)
  have he_aemeas : AEMeasurable e (μ.restrict e.source) :=
    openPartialHomeomorph_aemeasurable_restrict_source e μ
  have hpre_zero :
      (μ.restrict e.source) (e ⁻¹' ({e p} : Set ℂ)) = 0 := by
    rw [Measure.map_apply_of_aemeasurable he_aemeas
          (measurableSet_singleton (e p))] at hmap_singleton
    exact hmap_singleton
  have hsingle_restrict_zero :
      (μ.restrict e.source) ({p} : Set X) = 0 := by
    exact measure_mono_null (by
      intro x hx
      have hxp : x = p := by simpa using hx
      simp [hxp]) hpre_zero
  have hrestrict_singleton :
      (μ.restrict e.source) ({p} : Set X) = μ {p} := by
    rw [Measure.restrict_apply (measurableSet_singleton p)]
    congr 1
    ext x
    simp [hp_source]
  exact hrestrict_singleton ▸ hsingle_restrict_zero

/--
%%handwave
name:
  Nonempty open sets have positive smooth area
statement:
  If \(\mu\) is a smooth positive area measure on a second-countable smooth
  surface and \(W\subseteq X\) is nonempty and open, then \(\mu(W)>0\).
proof:
  Regard \(\mu\) as a smooth positive measure on the underlying real manifold
  and apply positivity of such measures on nonempty open sets.
-/
private theorem smoothPositiveAreaMeasureOnSurface_open_measure_pos
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    [IsManifold SurfaceRealModel ∞ X]
    {μ : Measure X} (hμ : SmoothPositiveAreaMeasureOnSurface X μ)
    {W : Set X} (hW_open : IsOpen W) (hW_nonempty : W.Nonempty) :
    0 < μ W := by
  letI : IsManifold SurfaceRealModel 1 X := inferInstance
  let hμ' : SmoothPositiveMeasureOnManifold (I := SurfaceRealModel) μ :=
    { finite_on_compact := hμ.finite_on_compact
      chart_density := hμ.chart_density }
  exact
    smoothPositiveMeasureOnManifold_open_measure_pos
      (I := SurfaceRealModel) hμ' hW_open hW_nonempty

/--
%%handwave
name:
  Open surface sets contain compact sets of positive area
statement:
  If \(W\) is a nonempty open subset of a surface carrying a smooth positive
  area measure \(\mu\), then there is a compact \(K\subseteq W\) with \(\mu(K)>0\).
proof:
  Local compactness gives a compact \(K\subseteq W\) whose interior contains a
  chosen point of \(W\).  The interior has positive area, so monotonicity gives \(\mu(K)>0\).
-/
private theorem smoothPositiveAreaMeasureOnSurface_exists_compact_pos_measure_subset_open
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X]
    {μ : Measure X} (hμ : SmoothPositiveAreaMeasureOnSurface X μ)
    {W : Set X} (hW_open : IsOpen W) (hW_nonempty : W.Nonempty) :
    ∃ K : Set X, IsCompact K ∧ K ⊆ W ∧ 0 < μ K := by
  classical
  haveI : LocallyCompactSpace X := ComplexOneManifold.locallyCompactSpace X
  rcases hW_nonempty with ⟨x, hxW⟩
  rcases exists_compact_subset hW_open hxW with
    ⟨K, hK_compact, hx_int, hKW⟩
  have hKint_nonempty : (interior K).Nonempty := ⟨x, hx_int⟩
  have hKint_pos : 0 < μ (interior K) :=
    smoothPositiveAreaMeasureOnSurface_open_measure_pos hμ
      isOpen_interior hKint_nonempty
  have hK_pos : 0 < μ K :=
    lt_of_lt_of_le hKint_pos (measure_mono interior_subset)
  exact ⟨K, hK_compact, hKW, hK_pos⟩

/--
%%handwave
name:
  A real Lipschitz bound implies continuity
statement:
  If \(L\ge0\) and \(T:\mathbb R\to\mathbb R\) satisfies
  \(\lvert T(s)-T(t)\rvert\le L\lvert s-t\rvert\) for all \(s,t\), then \(T\) is continuous.
proof:
  The displayed inequality is precisely the Lipschitz condition with
  nonnegative constant \(L\), and every Lipschitz map is continuous.
-/
private theorem continuous_of_real_lipschitz_bound
    {T : ℝ → ℝ} {L : ℝ}
    (hL_nonneg : 0 ≤ L)
    (hT_lipschitz : ∀ s t : ℝ, |T s - T t| ≤ L * |s - t|) :
    Continuous T := by
  have hLip : LipschitzWith (Real.toNNReal L) T := by
    refine LipschitzWith.of_dist_le' (f := T) ?_
    intro s t
    have hpoint := hT_lipschitz s t
    have hcoe : ((Real.toNNReal L : NNReal) : ℝ) = L := by
      have hnn : Real.toNNReal L = (⟨L, hL_nonneg⟩ : NNReal) :=
        Real.toNNReal_of_nonneg hL_nonneg
      exact congrArg Subtype.val hnn
    simpa [Real.dist_eq, hcoe] using hpoint
  exact hLip.continuous

/--
%%handwave
name:
  Smooth primitive with its pure differential class
statement:
  A compactly supported smooth function determines an element of the smooth
  pure Dirichlet core by taking its differential class.
-/
noncomputable def greenSmoothCoreElement {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (F : SmoothCompactlySupportedGlobalSurfaceFunction X)
    (hF : SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
      (SurfaceDifferentialField.ofCoordinateField F.gradient)) :
    (greenSobolevH10SmoothCompactSupportCore g).Core := by
  let D : GreenDifferentialL2Intrinsic g :=
    greenSmoothDifferentialClass (g := g) F hF
  have hD : IsSmoothCompactlySupportedGreenDifferentialClass g D := by
    exact ⟨F, hF, rfl⟩
  exact ⟨D, smoothCompactlySupportedGreenDifferentialClass_mem_core hD⟩

/--
%%handwave
name:
  Underlying class of a smooth core element
statement:
  For a smooth compactly supported \(F\) with \(L^2\) differential, the
  underlying intrinsic cotangent class of its associated core element is \([dF]\).
proof:
  This is the defining first component of the core element.
-/
@[simp]
theorem greenSmoothCoreElement_coe {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (F : SmoothCompactlySupportedGlobalSurfaceFunction X)
    (hF : SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
      (SurfaceDifferentialField.ofCoordinateField F.gradient)) :
    (greenSmoothCoreElement (g := g) F hF).1 =
      greenSmoothDifferentialClass (g := g) F hF :=
  rfl

/--
%%handwave
name:
  The chosen primitive recovers the original core class
statement:
  If a smooth core element is represented by its chosen smooth primitive, the
  resulting primitive-with-differential core element is the original core
  element.
proof:
  The chosen primitive was selected precisely so that its differential class is
  the core element's differential class.
-/
theorem greenSmoothCoreElement_chosenPrimitive_eq {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (u : (greenSobolevH10SmoothCompactSupportCore g).Core) :
    greenSmoothCoreElement (g := g)
        (greenSobolevH10SmoothCompactSupportCorePrimitive u)
        (greenSobolevH10SmoothCompactSupportCorePrimitive_memL2 u) =
      u := by
  apply Subtype.ext
  exact greenSobolevH10SmoothCompactSupportCorePrimitive_class_eq u

/--
%%handwave
name:
  Pure homogeneous scalar representative
statement:
  A scalar function represents a point of the pure homogeneous zero-trace
  completion if it is the compact-local \(L^2\) limit of an explicit sequence
  of compactly supported smooth primitives whose pure differential classes
  converge to that completed class.
-/
def HasPureH10ScalarRepresentative {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (u : GreenSobolevH10SmoothCompactSupport g) (f : X → ℝ) : Prop :=
  ∃ F : ℕ → SmoothCompactlySupportedGlobalSurfaceFunction X,
  ∃ hF : ∀ n : ℕ,
    SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
      (SurfaceDifferentialField.ofCoordinateField (F n).gradient),
    Filter.Tendsto
      (fun n : ℕ ↦
        (greenSobolevH10SmoothCompactSupportCore g).toCompletion
          (greenSmoothCoreElement (g := g) (F n) (hF n)))
      Filter.atTop (𝓝 u) ∧
      ∀ K : Set X, IsCompact K →
        TendstoInLocalL2OnSurface g.volume K
          (fun n : ℕ ↦ (F n).toFun)
          f

/--
%%handwave
name:
  Subtracting a constant preserves weak gradients
statement:
  If \(du\) is the weak gradient of a function \(u\) on a surface region,
  then \(du\) is also the weak gradient of \(u-a\) for any real constant
  \(a\).
proof:
  In a coordinate chart, the only new term is the integral of the derivative
  of a compactly supported smooth test against a constant.  This integral is
  zero by the Euclidean integration-by-parts identity for compactly supported
  functions.
-/
theorem IsWeakGradientOnRegion.sub_const_real {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    {U : Set X} {u : X → ℝ} {du : X → ℂ →L[ℝ] ℝ}
    (a : ℝ) (hweak : IsWeakGradientOnRegion U u du) :
    IsWeakGradientOnRegion U (fun x : X ↦ u x - a) du := by
  intro e he φ v
  rcases hweak e he φ v with ⟨hu_int, hdu_int, h_eq⟩
  let Ω : Set ℂ := surfaceChartRegion e U
  let dφ : ℂ → ℝ := fun z : ℂ ↦ fderiv ℝ (φ : ℂ → ℝ) z v
  have hφ_compact : HasCompactSupport (φ : ℂ → ℝ) := φ.compact_support
  have hφ_cont : Continuous (φ : ℂ → ℝ) := φ.smooth.continuous
  have hdφ_compact : HasCompactSupport dφ := by
    simpa [dφ] using hφ_compact.fderiv_apply (𝕜 := ℝ) v
  have hdφ_cont : Continuous dφ := by
    simpa [dφ] using
      (φ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdφ_int : Integrable dφ (MeasureTheory.volume : Measure ℂ) :=
    hdφ_cont.integrable_of_hasCompactSupport hdφ_compact
  have hconst_intΩ :
      Integrable (fun z : ℂ ↦ dφ z • a)
        (MeasureTheory.volume.restrict Ω) :=
    (hdφ_int.smul_const a).mono_measure Measure.restrict_le_self
  have hconst_zeroΩ :
      ∫ z in Ω, dφ z • a ∂MeasureTheory.volume = 0 := by
    have hsupport :
        ∀ z : ℂ, z ∉ Ω → dφ z • a = 0 := by
      intro z hzΩ
      have hz_not_tsupport : z ∉ tsupport dφ := by
        intro hz
        exact hzΩ <| φ.support_subset <|
          (tsupport_fderiv_apply_subset (𝕜 := ℝ)
            (f := (φ : ℂ → ℝ)) v) (by simpa [dφ] using hz)
      have hdφ_zero : dφ z = 0 :=
        image_eq_zero_of_notMem_tsupport hz_not_tsupport
      simp [hdφ_zero]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hsupport]
    have hφ_int : Integrable (φ : ℂ → ℝ)
        (MeasureTheory.volume : Measure ℂ) :=
      hφ_cont.integrable_of_hasCompactSupport hφ_compact
    have hibp :
        ∫ z, (φ : ℂ → ℝ) z •
            fderiv ℝ (fun _ : ℂ ↦ a) z v ∂MeasureTheory.volume =
          -∫ z, fderiv ℝ (φ : ℂ → ℝ) z v • a
            ∂MeasureTheory.volume :=
      integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
        (μ := (MeasureTheory.volume : Measure ℂ))
        (f := (φ : ℂ → ℝ)) (g := fun _ : ℂ ↦ a) (v := v)
        (by simpa [dφ] using hdφ_int.smul_const a)
        (by simp)
        (hφ_int.smul_const a)
        (fun z _hz ↦ (φ.smooth.differentiable (by simp)) z)
        (fun z _hz ↦ differentiableAt_const a)
    have hzero_neg :
        (0 : ℝ) =
          -∫ z, fderiv ℝ (φ : ℂ → ℝ) z v • a
            ∂MeasureTheory.volume := by
      simpa using hibp
    simpa [dφ] using neg_eq_zero.mp hzero_neg.symm
  refine ⟨?_, hdu_int, ?_⟩
  · convert hu_int.sub hconst_intΩ using 1
    ext z
    simp [dφ]
    ring
  · calc
      ∫ z in surfaceChartRegion e U,
          (u (e.symm z) - a) * fderiv ℝ (φ : ℂ → ℝ) z v
          ∂MeasureTheory.volume
          =
        ∫ z in Ω,
          (u (e.symm z) * fderiv ℝ (φ : ℂ → ℝ) z v -
            fderiv ℝ (φ : ℂ → ℝ) z v • a) ∂MeasureTheory.volume := by
            congr 1
            ext z
            simp
            ring
      _ =
        ∫ z in Ω, u (e.symm z) * fderiv ℝ (φ : ℂ → ℝ) z v
          ∂MeasureTheory.volume -
        ∫ z in Ω, fderiv ℝ (φ : ℂ → ℝ) z v • a
          ∂MeasureTheory.volume := by
            simpa [dφ] using integral_sub hu_int hconst_intΩ
      _ = -∫ z in Ω,
          du (e.symm z) (surfaceChartTangentMap e z v) * φ z
          ∂MeasureTheory.volume - 0 := by
            rw [h_eq, hconst_zeroΩ]
      _ = -∫ z in surfaceChartRegion e U,
          du (e.symm z) (surfaceChartTangentMap e z v) * φ z
          ∂MeasureTheory.volume := by
            simp [Ω]

/--
%%handwave
name:
  Subtracting a constant preserves intrinsic local Sobolev regularity
statement:
  If a function is locally \(W^{1,2}\) on a surface region, then subtracting
  a real constant keeps it locally \(W^{1,2}\) with the same weak
  differential.
proof:
  The weak-gradient identity is unchanged by the previous constant-subtraction
  lemma.  On each compact subset of the region, constants are \(L^2\) because
  the background area measure is finite on compact sets, so local
  square-integrability is preserved.
-/
theorem IsIntrinsicLocalSobolevH1OnSurface.sub_const_real {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [IsManifold SurfaceRealModel 1 X]
    {g : BackgroundSurfaceMetricOnSurface X} {U : Set X}
    {u : X → ℝ} {du : X → ℂ →L[ℝ] ℝ}
    (a : ℝ) (hlocal : IsIntrinsicLocalSobolevH1OnSurface g U u du) :
    IsIntrinsicLocalSobolevH1OnSurface g U (fun x : X ↦ u x - a) du := by
  refine ⟨IsWeakGradientOnRegion.sub_const_real a hlocal.1, ?_⟩
  intro K hK hKU
  rcases hlocal.2 K hK hKU with ⟨hu_mem, hdu_mem⟩
  haveI : IsFiniteMeasureOnCompacts g.volume :=
    BackgroundSurfaceMetricOnSurface.volume_isFiniteMeasureOnCompacts g
  haveI : IsFiniteMeasure (g.volume.restrict K) :=
    isFiniteMeasure_restrict.2 (hK.measure_lt_top (μ := g.volume)).ne
  have hconst_mem :
      MemLp (fun _ : X ↦ a) 2 (g.volume.restrict K) :=
    memLp_const a
  exact ⟨hu_mem.sub hconst_mem, hdu_mem⟩

/--
%%handwave
name:
  Subtracting a constant preserves weak harmonicity
statement:
  If a function is weakly harmonic on a surface region, then subtracting a
  real constant leaves it weakly harmonic on the same region.
proof:
  The local weak differential is unchanged by subtracting a constant, and the
  weak harmonic test pairings only involve that differential.
-/
theorem IsWeaklyHarmonicOnSurface.sub_const_real {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [IsManifold SurfaceRealModel 1 X]
    {g : BackgroundSurfaceMetricOnSurface X} {U : Set X}
    {u : X → ℝ} (a : ℝ)
    (hweak : IsWeaklyHarmonicOnSurface g U u) :
    IsWeaklyHarmonicOnSurface g U (fun x : X ↦ u x - a) := by
  rcases hweak with ⟨hU_open, du, hlocal, htest⟩
  exact ⟨hU_open, du, hlocal.sub_const_real a, htest⟩

/--
%%handwave
name:
  Smooth-core source represented by a completed pure class
statement:
  A completed homogeneous zero-trace class defines a continuous source on the
  smooth Dirichlet core by pairing core elements with that completed class.
-/
noncomputable def greenSobolevH10SmoothCompactSupportCoreSourceOfVector
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (v : GreenSobolevH10SmoothCompactSupport g) :
    (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ := by
  let C := greenSobolevH10SmoothCompactSupportCore g
  exact (innerSL ℝ v).comp
    (UniformSpace.Completion.toComplL :
      C.Core →L[ℝ] GreenSobolevH10SmoothCompactSupport g)

/--
%%handwave
name:
  The core source of a vector extends to its inner-product functional
statement:
  Extending the smooth-core source represented by a completed pure class gives
  the inner-product functional against that class on the whole completed
  homogeneous space.
proof:
  Both continuous linear functionals agree on the dense image of the smooth
  core in the completion, so uniqueness of continuous extension gives the
  result.
-/
theorem greenSobolevH10SmoothCompactSupportCoreSourceOfVector_extend_eq
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (v : GreenSobolevH10SmoothCompactSupport g) :
    (greenSobolevH10SmoothCompactSupportCore g).extendSource
        (greenSobolevH10SmoothCompactSupportCoreSourceOfVector (g := g) v) =
      innerSL ℝ v := by
  let C := greenSobolevH10SmoothCompactSupportCore g
  let e : C.Core →L[ℝ] GreenSobolevH10SmoothCompactSupport g :=
    (UniformSpace.Completion.toComplL :
      C.Core →L[ℝ] GreenSobolevH10SmoothCompactSupport g)
  change
    (greenSobolevH10SmoothCompactSupportCoreSourceOfVector (g := g) v).extend e =
      innerSL ℝ v
  have hdense : DenseRange e := by
    simpa [e, UniformSpace.Completion.coe_toComplL] using
      (UniformSpace.Completion.denseRange_coe : DenseRange
        ((↑) : C.Core → UniformSpace.Completion C.Core))
  have hind : IsUniformInducing e := by
    simpa [e, UniformSpace.Completion.coe_toComplL] using
      (UniformSpace.Completion.isUniformInducing_coe C.Core)
  exact
    ContinuousLinearMap.extend_unique
      (greenSobolevH10SmoothCompactSupportCoreSourceOfVector (g := g) v)
      hdense hind (innerSL ℝ v) (by
        ext u
        rfl)

/--
%%handwave
name:
  The Riesz vector of the core source of a vector is the vector
statement:
  If a smooth-core source is defined by pairing with a completed pure class,
  then its Riesz vector in the completed homogeneous space is exactly that
  class.
proof:
  The extended source is the inner-product functional against the class.
  The Riesz representative of that functional is the class itself.
-/
theorem greenSobolevH10SmoothCompactSupportRieszVector_coreSourceOfVector
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (v : GreenSobolevH10SmoothCompactSupport g) :
    greenSobolevH10SmoothCompactSupportRieszVector
        (greenSobolevH10SmoothCompactSupportCoreSourceOfVector (g := g) v) =
      v := by
  let H := GreenSobolevH10SmoothCompactSupport g
  have hsrc :
      (greenSobolevH10SmoothCompactSupportCore g).extendSource
          (greenSobolevH10SmoothCompactSupportCoreSourceOfVector (g := g) v) =
        innerSL ℝ v :=
    greenSobolevH10SmoothCompactSupportCoreSourceOfVector_extend_eq
      (g := g) v
  dsimp [greenSobolevH10SmoothCompactSupportRieszVector]
  rw [hsrc]
  change greenSobolevH10RieszRepresentative (innerSL ℝ v) = v
  change
    (InnerProductSpace.toDual ℝ H).symm
        ((InnerProductSpace.toDual ℝ H) v) = v
  exact
    LinearEquiv.symm_apply_apply
      (InnerProductSpace.toDual ℝ H).toLinearEquiv v

/--
%%handwave
name:
  Core norms tend to zero when completions tend to zero
statement:
  If smooth pure Dirichlet-core elements converge to zero in the completed
  homogeneous \(H^1_0\) space, then their pure Dirichlet core norms tend to
  zero.
proof:
  The canonical map from the core to its completion is an isometry.  Therefore
  the distance from the completed image of \(U_n\) to zero is exactly
  \(\|U_n\|\).
-/
theorem greenSobolevH10SmoothCompactSupportCore_norm_tendsto_zero_of_tendsto_zero_completion
    {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (U : ℕ → (greenSobolevH10SmoothCompactSupportCore g).Core)
    (hU :
      Filter.Tendsto
        (fun n : ℕ ↦
          (greenSobolevH10SmoothCompactSupportCore g).toCompletion (U n))
        Filter.atTop (𝓝 (0 : GreenSobolevH10SmoothCompactSupport g))) :
    Filter.Tendsto (fun n : ℕ ↦ ‖U n‖) Filter.atTop (𝓝 0) := by
  classical
  let C := greenSobolevH10SmoothCompactSupportCore g
  refine Metric.tendsto_nhds.mpr ?_
  intro ε hε
  have hnear :
      ∀ᶠ n : ℕ in Filter.atTop,
        dist (C.toCompletion (U n))
          (0 : GreenSobolevH10SmoothCompactSupport g) < ε := by
    simpa [C] using Metric.tendsto_nhds.mp hU ε hε
  refine hnear.mono ?_
  intro n hn
  have hdist_eq :
      dist (C.toCompletion (U n))
          (0 : GreenSobolevH10SmoothCompactSupport g) =
        ‖U n‖ := by
    change
      dist ((U n : C.Core) : UniformSpace.Completion C.Core)
          ((0 : C.Core) : UniformSpace.Completion C.Core) =
        ‖U n‖
    rw [UniformSpace.Completion.dist_eq, dist_eq_norm, sub_zero]
  simpa [hdist_eq] using hn

/--
%%handwave
name:
  Smooth representatives of the zero pure class vanish locally in \(L^2\)
statement:
  If compactly supported smooth primitives converge to the zero element in
  the pure homogeneous Dirichlet completion, then, under positive pure
  capacity at infinity, the primitives converge to zero in \(L^2\) on every
  compact set.
proof:
  Pure capacity bounds the local \(L^2\)-mass of each primitive by a compact
  constant times its pure Dirichlet energy.  The completion convergence to
  zero is isometric, hence the pure Dirichlet norms of the corresponding
  core elements tend to zero.
-/
theorem smoothCoreRepresentatives_tendsto_localL2_zero_of_tendsto_zero_completion
    {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (hcap : HasPureDirichletCapacityAtInfinity g)
    (F : ℕ → SmoothCompactlySupportedGlobalSurfaceFunction X)
    (hF : ∀ n : ℕ,
      SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
        (SurfaceDifferentialField.ofCoordinateField (F n).gradient))
    (hF_tendsto :
      Filter.Tendsto
        (fun n : ℕ ↦
          (greenSobolevH10SmoothCompactSupportCore g).toCompletion
            (greenSmoothCoreElement (g := g) (F n) (hF n)))
        Filter.atTop (𝓝 (0 : GreenSobolevH10SmoothCompactSupport g))) :
    ∀ K : Set X, IsCompact K →
      TendstoInLocalL2OnSurface g.volume K
        (fun n : ℕ ↦ (F n).toFun) (fun _ : X ↦ 0) := by
  classical
  intro K hK
  let C := greenSobolevH10SmoothCompactSupportCore g
  let U : ℕ → C.Core :=
    fun n : ℕ ↦ greenSmoothCoreElement (g := g) (F n) (hF n)
  have hU_norm :
      Filter.Tendsto (fun n : ℕ ↦ ‖U n‖) Filter.atTop (𝓝 0) :=
    greenSobolevH10SmoothCompactSupportCore_norm_tendsto_zero_of_tendsto_zero_completion
      (g := g) U (by simpa [C, U] using hF_tendsto)
  rcases hcap K hK with ⟨P, hP_nonneg, hP_bound⟩
  let I : ℕ → ℝ := fun n : ℕ ↦
    ∫ x in K, ‖(F n).toFun x‖ ^ (2 : ℕ) ∂g.volume
  have hI_nonneg : ∀ n : ℕ, 0 ≤ I n := by
    intro n
    dsimp [I]
    exact integral_nonneg fun x ↦ sq_nonneg ‖(F n).toFun x‖
  have hI_le : ∀ n : ℕ, I n ≤ P * ‖U n‖ ^ (2 : ℕ) := by
    intro n
    let J : ℝ :=
      ∫ x, g.gradientInner x ((F n).gradient x) ((F n).gradient x)
        ∂g.volume
    have hJ_nonneg : 0 ≤ J := by
      dsimp [J]
      exact
        integral_nonneg fun x ↦
          BackgroundSurfaceMetricOnSurface.gradientInner_nonneg
            g x ((F n).gradient x)
    have hJ_eq_normSq : J = ‖U n‖ ^ (2 : ℕ) := by
      have hnorm :
          ‖U n‖ = Real.sqrt J := by
        simpa [U, J] using
          greenSmoothDifferentialClass_norm_eq_sqrt_dirichlet
            (g := g) (F n) (hF n)
      have hs : ‖U n‖ ^ (2 : ℕ) = J := by
        rw [hnorm, Real.sq_sqrt hJ_nonneg]
      exact hs.symm
    calc
      I n ≤ P * J := by
        simpa [I, J] using hP_bound (F n)
      _ = P * ‖U n‖ ^ (2 : ℕ) := by
        rw [hJ_eq_normSq]
  have hupper_tendsto :
      Filter.Tendsto
        (fun n : ℕ ↦ P * ‖U n‖ ^ (2 : ℕ))
        Filter.atTop (𝓝 0) := by
    have hpow :
        Filter.Tendsto (fun n : ℕ ↦ ‖U n‖ ^ (2 : ℕ))
          Filter.atTop (𝓝 0) := by
      simpa using hU_norm.pow 2
    have hconstP :
        Filter.Tendsto (fun _ : ℕ ↦ P) Filter.atTop (𝓝 P) :=
      tendsto_const_nhds
    have hmul := hconstP.mul hpow
    simpa using hmul
  have hI_tendsto :
      Filter.Tendsto I Filter.atTop (𝓝 0) := by
    exact
      tendsto_of_tendsto_of_tendsto_of_le_of_le
        (show Filter.Tendsto (fun _ : ℕ ↦ (0 : ℝ)) Filter.atTop (𝓝 0) from
          tendsto_const_nhds)
        hupper_tendsto
        (fun n ↦ hI_nonneg n)
        hI_le
  unfold TendstoInLocalL2OnSurface
  let μK := g.volume.restrict K
  have htoReal_tendsto :
      Filter.Tendsto
        (fun n : ℕ ↦
          (eLpNorm (fun x : X ↦ (F n).toFun x - 0)
            2 μK).toReal)
        Filter.atTop (𝓝 0) := by
    have hsqrt :
        Filter.Tendsto (fun n : ℕ ↦ Real.sqrt (I n))
          Filter.atTop (𝓝 0) := by
      simpa using hI_tendsto.sqrt
    refine Filter.Tendsto.congr' ?_ hsqrt
    filter_upwards [] with n
    have hmem :
        MemLp (fun x : X ↦ (F n).toFun x - 0) 2 μK := by
      simpa [μK] using (F n).memLp_restrict_compact (g := g) hK
    have hnorm :
        (eLpNorm (fun x : X ↦ (F n).toFun x - 0) 2 μK).toReal =
          Real.sqrt (∫ x, ‖(F n).toFun x - 0‖ ^ (2 : ℕ) ∂μK) := by
      rw [MeasureTheory.toReal_eLpNorm hmem.aestronglyMeasurable]
      rw [MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal
        (p := (2 : ℝ≥0∞))
        (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞))
        hmem.aestronglyMeasurable]
      norm_num [Real.rpow_natCast, Real.sqrt_eq_rpow]
    have hInt :
        (∫ x, ‖(F n).toFun x - 0‖ ^ (2 : ℕ) ∂μK) = I n := by
      simp [I, μK]
    rw [hnorm, hInt]
  have hne_top :
      ∀ n : ℕ,
        eLpNorm (fun x : X ↦ (F n).toFun x - 0) 2 μK ≠ (⊤ : ℝ≥0∞) := by
    intro n
    have hmem :
        MemLp (fun x : X ↦ (F n).toFun x - 0) 2 μK := by
      simpa [μK] using (F n).memLp_restrict_compact (g := g) hK
    exact hmem.eLpNorm_ne_top
  simpa [μK] using
    (ENNReal.tendsto_toReal_zero_iff hne_top).mp htoReal_tendsto

/--
%%handwave
name:
  A zero pure class has zero compact-local scalar representative
statement:
  If a scalar function represents the zero element of the pure homogeneous
  Dirichlet completion, then under positive pure capacity it is the
  compact-local \(L^2\) limit of the zero function.
proof:
  Choose smooth compactly supported primitives representing the scalar
  function.  Their pure classes converge to zero, so pure capacity makes the
  primitives converge compact-locally to zero.  The same primitives also
  converge compact-locally to the representative; the triangle inequality in
  \(L^2\) identifies the representative with zero locally.
-/
theorem HasPureH10ScalarRepresentative.tendsto_localL2_zero_of_eq_zero
    {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableEq X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (hcap : HasPureDirichletCapacityAtInfinity g)
    {u : GreenSobolevH10SmoothCompactSupport g} {f : X → ℝ}
    (hrep : HasPureH10ScalarRepresentative u f) (hu_zero : u = 0)
    (hf_meas :
      ∀ K : Set X, IsCompact K →
        AEStronglyMeasurable f (g.volume.restrict K)) :
    ∀ K : Set X, IsCompact K →
      TendstoInLocalL2OnSurface g.volume K
        (fun _ : ℕ ↦ fun _ : X ↦ 0) f := by
  classical
  rcases hrep with ⟨F, hF, hF_tendsto, hF_local⟩
  have hF_zero :
      ∀ K : Set X, IsCompact K →
        TendstoInLocalL2OnSurface g.volume K
          (fun n : ℕ ↦ (F n).toFun) (fun _ : X ↦ 0) :=
    smoothCoreRepresentatives_tendsto_localL2_zero_of_tendsto_zero_completion
      (g := g) hcap F hF (by simpa [hu_zero] using hF_tendsto)
  intro K hK
  unfold TendstoInLocalL2OnSurface at hF_zero hF_local ⊢
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  have hhalf_pos : 0 < ε / 2 :=
    ENNReal.div_pos_iff.mpr ⟨hε.ne', ENNReal.ofNat_ne_top⟩
  have hzero_eventually :
      ∀ᶠ n : ℕ in Filter.atTop,
        eLpNorm (fun x : X ↦ (F n).toFun x - 0)
            2 (g.volume.restrict K) ≤ ε / 2 :=
    ENNReal.tendsto_nhds_zero.mp (hF_zero K hK) (ε / 2) hhalf_pos
  have hlimit_eventually :
      ∀ᶠ n : ℕ in Filter.atTop,
        eLpNorm (fun x : X ↦ (F n).toFun x - f x)
            2 (g.volume.restrict K) ≤ ε / 2 :=
    ENNReal.tendsto_nhds_zero.mp (hF_local K hK) (ε / 2) hhalf_pos
  rcases
      Filter.eventually_atTop.1
        (hzero_eventually.and hlimit_eventually) with
    ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  let μK := g.volume.restrict K
  have hpack := hN n hn
  have hzero_n :
      eLpNorm (fun x : X ↦ 0 - (F n).toFun x) 2 μK ≤ ε / 2 := by
    have hneg :
        eLpNorm (fun x : X ↦ 0 - (F n).toFun x) 2 μK =
          eLpNorm (fun x : X ↦ (F n).toFun x - 0) 2 μK := by
      have hfun :
          (fun x : X ↦ 0 - (F n).toFun x) =
            - fun x : X ↦ (F n).toFun x - 0 := by
        funext x
        simp
      rw [hfun, eLpNorm_neg]
    rw [hneg]
    simpa [μK] using hpack.1
  have hlimit_n :
      eLpNorm (fun x : X ↦ (F n).toFun x - f x) 2 μK ≤ ε / 2 := by
    simpa [μK] using hpack.2
  have hzeroF_meas :
      AEStronglyMeasurable
        (fun x : X ↦ 0 - (F n).toFun x) μK := by
    have hFn :
        AEStronglyMeasurable (F n).toFun μK :=
      ((F n).memLp_restrict_compact (g := g) hK).aestronglyMeasurable
    exact aestronglyMeasurable_const.sub hFn
  have hFf_meas :
      AEStronglyMeasurable
        (fun x : X ↦ (F n).toFun x - f x) μK := by
    have hFn :
        AEStronglyMeasurable (F n).toFun μK :=
      ((F n).memLp_restrict_compact (g := g) hK).aestronglyMeasurable
    exact hFn.sub (by simpa [μK] using hf_meas K hK)
  have htri :
      eLpNorm (fun x : X ↦ 0 - f x) 2 μK ≤
        eLpNorm (fun x : X ↦ 0 - (F n).toFun x) 2 μK +
          eLpNorm (fun x : X ↦ (F n).toFun x - f x) 2 μK := by
    have hbase :=
      eLpNorm_add_le hzeroF_meas hFf_meas
        (by norm_num : (1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞))
    have hfun :
        ((fun x : X ↦ 0 - (F n).toFun x) +
            fun x : X ↦ (F n).toFun x - f x) =
          fun x : X ↦ 0 - f x := by
      funext x
      simp [Pi.add_apply]
      ring
    rw [← hfun]
    exact hbase
  calc
    eLpNorm (fun x : X ↦ (fun _ : X ↦ 0) x - f x) 2
        (g.volume.restrict K)
        =
        eLpNorm (fun x : X ↦ 0 - f x) 2 μK := rfl
    _ ≤
        eLpNorm (fun x : X ↦ 0 - (F n).toFun x) 2 μK +
          eLpNorm (fun x : X ↦ (F n).toFun x - f x) 2 μK := htri
    _ ≤ ε / 2 + ε / 2 := add_le_add hzero_n hlimit_n
    _ = ε := ENNReal.add_halves ε

/--
%%handwave
name:
  Compact-local \(L^2\) convergence to zero gives almost-everywhere zero
statement:
  If the constant zero sequence converges to a measurable function in
  compact-local \(L^2\) on a compact set, then that function is zero almost
  everywhere on the compact set.
proof:
  The \(L^2\)-seminorm of the difference is a constant sequence.  Since this
  constant sequence tends to zero, the seminorm itself is zero.  The standard
  characterization of zero \(L^p\)-seminorms gives almost-everywhere
  equality to zero.
-/
theorem TendstoInLocalL2OnSurface.ae_eq_zero_of_const_zero
    {X : Type} [MeasurableSpace X]
    {μ : Measure X} {K : Set X} {f : X → ℝ}
    (hf_meas : AEStronglyMeasurable f (μ.restrict K))
    (hlocal :
      TendstoInLocalL2OnSurface μ K
        (fun _ : ℕ ↦ fun _ : X ↦ 0) f) :
    f =ᵐ[μ.restrict K] 0 := by
  classical
  unfold TendstoInLocalL2OnSurface at hlocal
  let μK := μ.restrict K
  have hnorm_zero :
      eLpNorm (fun x : X ↦ 0 - f x) 2 μK = 0 := by
    have hconst :
        Filter.Tendsto
          (fun _ : ℕ ↦ eLpNorm (fun x : X ↦ 0 - f x) 2 μK)
          Filter.atTop (𝓝 0) := by
      simpa [μK] using hlocal
    exact tendsto_const_nhds_iff.mp hconst
  have hdiff_meas :
      AEStronglyMeasurable (fun x : X ↦ 0 - f x) μK :=
    aestronglyMeasurable_const.sub hf_meas
  have hdiff_zero :
      (fun x : X ↦ 0 - f x) =ᵐ[μK] 0 :=
    (eLpNorm_eq_zero_iff hdiff_meas
      (by norm_num : (2 : ℝ≥0∞) ≠ 0)).mp hnorm_zero
  filter_upwards [hdiff_zero] with x hx
  simpa using hx

/--
%%handwave
name:
  A smooth core element is represented by its primitive
statement:
  If \(F\) is smooth and compactly supported with \(L^2\) differential, then
  the image of \([dF]\) in the pure \(H^1_0\) completion has scalar
  representative \(F\).
proof:
  Use the constant approximating sequence \(F_n=F\).  It converges to the core
  element in the completion, and \(F_n-F=0\) has zero local \(L^2\)-seminorm on every compact set.
-/
theorem HasPureH10ScalarRepresentative.of_smoothCompactlySupported
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (F : SmoothCompactlySupportedGlobalSurfaceFunction X)
    (hF : SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
      (SurfaceDifferentialField.ofCoordinateField F.gradient)) :
    HasPureH10ScalarRepresentative
      ((greenSobolevH10SmoothCompactSupportCore g).toCompletion
        (greenSmoothCoreElement (g := g) F hF))
      F.toFun := by
  refine ⟨fun _ : ℕ ↦ F, fun _ : ℕ ↦ hF, ?_, ?_⟩
  · exact tendsto_const_nhds
  · intro K hK
    unfold TendstoInLocalL2OnSurface
    have hzero :
        (fun _ : ℕ ↦
          eLpNorm (fun x : X ↦ F.toFun x - F.toFun x)
            2 (g.volume.restrict K)) =
          fun _ : ℕ ↦ (0 : ℝ≥0∞) := by
      funext n
      simp
    simpa [hzero] using (tendsto_const_nhds : Filter.Tendsto
      (fun _ : ℕ ↦ (0 : ℝ≥0∞)) Filter.atTop (𝓝 0))

/--
%%handwave
name:
  Pure scalar representatives are unchanged by compact-local almost-everywhere equality
statement:
  If a pure homogeneous zero-trace class is represented by \(f\), and \(f\)
  agrees almost everywhere with \(h\) on every compact subset, then the same
  class is represented by \(h\).
proof:
  Use the same compactly supported smooth approximating primitives.  The pure
  completion convergence is unchanged.  On each compact set, the \(L^2\)
  distance from the approximants to \(f\) equals the \(L^2\) distance from the
  approximants to \(h\), because the two limits agree almost everywhere on
  that restricted measure.
-/
theorem HasPureH10ScalarRepresentative.ae_eq
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    {u : GreenSobolevH10SmoothCompactSupport g} {f h : X → ℝ}
    (hrep : HasPureH10ScalarRepresentative u f)
    (hae :
      ∀ K : Set X, IsCompact K →
        f =ᵐ[g.volume.restrict K] h) :
    HasPureH10ScalarRepresentative u h := by
  rcases hrep with ⟨F, hF, hF_tendsto, hF_local⟩
  refine ⟨F, hF, hF_tendsto, ?_⟩
  intro K hK
  unfold TendstoInLocalL2OnSurface at hF_local ⊢
  have hseq :
      (fun n : ℕ ↦
        eLpNorm (fun x : X ↦ (F n).toFun x - h x)
          2 (g.volume.restrict K)) =
      fun n : ℕ ↦
        eLpNorm (fun x : X ↦ (F n).toFun x - f x)
          2 (g.volume.restrict K) := by
    funext n
    refine eLpNorm_congr_ae ?_
    filter_upwards [hae K hK] with x hx
    rw [hx]
  simpa [hseq] using hF_local K hK

/--
%%handwave
name:
  Pure scalar representatives are stable under scalar multiplication
statement:
  If a pure zero-trace class is represented by a scalar function \(f\), then
  the scalar multiple of the class is represented by the scalar multiple of
  \(f\).
proof:
  Multiply each compactly supported smooth primitive in the representing
  sequence by the fixed scalar.  Smoothness, compact support, and
  square-integrability of the differential are preserved by scalar
  multiplication.  The pure completion convergence follows from continuity of
  scalar multiplication, and compact-local \(L^2\)-convergence follows from
  homogeneity of the \(L^2\)-seminorm.
-/
theorem HasPureH10ScalarRepresentative.smul
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    {u : GreenSobolevH10SmoothCompactSupport g} {f : X → ℝ}
    (hrep : HasPureH10ScalarRepresentative u f) (c : ℝ) :
    HasPureH10ScalarRepresentative (c • u) (fun x : X ↦ c * f x) := by
  classical
  rcases hrep with ⟨F, hF, hF_tendsto, hF_local⟩
  let C := greenSobolevH10SmoothCompactSupportCore g
  let V : ℕ → SmoothCompactlySupportedGlobalSurfaceFunction X :=
    fun n : ℕ ↦ SmoothCompactlySupportedGlobalSurfaceFunction.smul c (F n)
  have hV : ∀ n : ℕ,
      SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
        (SurfaceDifferentialField.ofCoordinateField (V n).gradient) := by
    intro n
    let dF : SquareIntegrableSurfaceDifferentialField
        (X := X) (E := ℝ) g.metric g.volume :=
      { toSection := SurfaceDifferentialField.ofCoordinateField (F n).gradient
        memL2 := hF n }
    let dcF : SquareIntegrableSurfaceDifferentialField
        (X := X) (E := ℝ) g.metric g.volume :=
      squareIntegrableSurfaceDifferentialFieldSmul g.metric g.volume c dF
    change SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
      dcF.toSection
    exact dcF.memL2
  refine ⟨V, hV, ?_, ?_⟩
  · have hcore : ∀ n : ℕ,
        greenSmoothCoreElement (g := g) (V n) (hV n) =
          c • greenSmoothCoreElement (g := g) (F n) (hF n) := by
      intro n
      apply Subtype.ext
      simpa [V] using
        greenSmoothDifferentialClass_smul
          (g := g) c (F n) (hF n) (hV n)
    have hseq :
        (fun n : ℕ ↦
          C.toCompletion
            (greenSmoothCoreElement (g := g) (V n) (hV n))) =
          fun n : ℕ ↦
            c • C.toCompletion
              (greenSmoothCoreElement (g := g) (F n) (hF n)) := by
      funext n
      rw [hcore n]
      simp [C, GreenSobolevH10DirichletCore.toCompletion]
    rw [hseq]
    exact hF_tendsto.const_smul c
  · intro K hK
    unfold TendstoInLocalL2OnSurface at hF_local ⊢
    have hbase := hF_local K hK
    have hmul :
        Filter.Tendsto
          (fun n : ℕ ↦
            ‖c‖ₑ *
              eLpNorm (fun x : X ↦ (F n).toFun x - f x)
                2 (g.volume.restrict K))
          Filter.atTop (𝓝 0) := by
      simpa using
        ENNReal.Tendsto.const_mul hbase
          (Or.inr (by simp : ‖c‖ₑ ≠ (⊤ : ℝ≥0∞)))
    have hnorm :
        (fun n : ℕ ↦
          eLpNorm
            (fun x : X ↦ (V n).toFun x - c * f x)
            2 (g.volume.restrict K)) =
          fun n : ℕ ↦
            ‖c‖ₑ *
              eLpNorm (fun x : X ↦ (F n).toFun x - f x)
                2 (g.volume.restrict K) := by
      funext n
      have hfun :
          (fun x : X ↦ (V n).toFun x - c * f x) =
            c • (fun x : X ↦ (F n).toFun x - f x) := by
        funext x
        simp [V, SmoothCompactlySupportedGlobalSurfaceFunction.smul,
          Pi.smul_apply, mul_sub]
      rw [hfun]
      exact eLpNorm_const_smul c (fun x : X ↦ (F n).toFun x - f x)
        2 (g.volume.restrict K)
    simpa [hnorm] using hmul

/--
%%handwave
name:
  Pure scalar representatives are stable under addition
statement:
  If two pure zero-trace classes are represented by locally measurable scalar
  functions \(f\) and \(h\), then their sum is represented by \(f+h\).
proof:
  Add the two compactly supported smooth primitive sequences termwise.
  Linearity of differentials identifies the pure differential classes with
  the termwise sums, so convergence in the pure completion follows from
  continuity of addition.  On each compact set, the \(L^2\) triangle
  inequality gives convergence of the termwise scalar sums to \(f+h\).
-/
theorem HasPureH10ScalarRepresentative.add
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    {u v : GreenSobolevH10SmoothCompactSupport g}
    {f h : X → ℝ}
    (hrep_f : HasPureH10ScalarRepresentative u f)
    (hrep_h : HasPureH10ScalarRepresentative v h)
    (hf_meas :
      ∀ K : Set X, IsCompact K →
        AEStronglyMeasurable f (g.volume.restrict K))
    (hh_meas :
      ∀ K : Set X, IsCompact K →
        AEStronglyMeasurable h (g.volume.restrict K)) :
    HasPureH10ScalarRepresentative (u + v) (fun x : X ↦ f x + h x) := by
  classical
  rcases hrep_f with ⟨F, hF, hF_tendsto, hF_local⟩
  rcases hrep_h with ⟨H, hH, hH_tendsto, hH_local⟩
  let C := greenSobolevH10SmoothCompactSupportCore g
  let V : ℕ → SmoothCompactlySupportedGlobalSurfaceFunction X :=
    fun n : ℕ ↦ SmoothCompactlySupportedGlobalSurfaceFunction.add (F n) (H n)
  have hV : ∀ n : ℕ,
      SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
        (SurfaceDifferentialField.ofCoordinateField (V n).gradient) := by
    intro n
    let dF : SquareIntegrableSurfaceDifferentialField
        (X := X) (E := ℝ) g.metric g.volume :=
      { toSection := SurfaceDifferentialField.ofCoordinateField (F n).gradient
        memL2 := hF n }
    let dH : SquareIntegrableSurfaceDifferentialField
        (X := X) (E := ℝ) g.metric g.volume :=
      { toSection := SurfaceDifferentialField.ofCoordinateField (H n).gradient
        memL2 := hH n }
    let dFH : SquareIntegrableSurfaceDifferentialField
        (X := X) (E := ℝ) g.metric g.volume :=
      squareIntegrableSurfaceDifferentialFieldAdd g.metric g.volume dF dH
    change SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
      dFH.toSection
    exact dFH.memL2
  refine ⟨V, hV, ?_, ?_⟩
  · have hcore : ∀ n : ℕ,
        greenSmoothCoreElement (g := g) (V n) (hV n) =
          greenSmoothCoreElement (g := g) (F n) (hF n) +
            greenSmoothCoreElement (g := g) (H n) (hH n) := by
      intro n
      apply Subtype.ext
      simpa [V] using
        greenSmoothDifferentialClass_add
          (g := g) (F n) (H n) (hF n) (hH n) (hV n)
    have hseq :
        (fun n : ℕ ↦
          C.toCompletion
            (greenSmoothCoreElement (g := g) (V n) (hV n))) =
          fun n : ℕ ↦
            C.toCompletion
              (greenSmoothCoreElement (g := g) (F n) (hF n)) +
              C.toCompletion
                (greenSmoothCoreElement (g := g) (H n) (hH n)) := by
      funext n
      rw [hcore n]
      change
        (((greenSmoothCoreElement (g := g) (F n) (hF n) +
              greenSmoothCoreElement (g := g) (H n) (hH n)) : C.Core) :
            UniformSpace.Completion C.Core) =
          ((greenSmoothCoreElement (g := g) (F n) (hF n) : C.Core) :
            UniformSpace.Completion C.Core) +
          ((greenSmoothCoreElement (g := g) (H n) (hH n) : C.Core) :
            UniformSpace.Completion C.Core)
      exact UniformSpace.Completion.coe_add _ _
    rw [hseq]
    exact hF_tendsto.add hH_tendsto
  · intro K hK
    unfold TendstoInLocalL2OnSurface at hF_local hH_local ⊢
    rw [ENNReal.tendsto_atTop_zero]
    intro ε hε
    have hhalf_pos : 0 < ε / 2 :=
      ENNReal.div_pos_iff.mpr ⟨hε.ne', ENNReal.ofNat_ne_top⟩
    have hF_eventually :
        ∀ᶠ n : ℕ in Filter.atTop,
          eLpNorm (fun x : X ↦ (F n).toFun x - f x)
              2 (g.volume.restrict K) ≤ ε / 2 :=
      ENNReal.tendsto_nhds_zero.mp (hF_local K hK) (ε / 2) hhalf_pos
    have hH_eventually :
        ∀ᶠ n : ℕ in Filter.atTop,
          eLpNorm (fun x : X ↦ (H n).toFun x - h x)
              2 (g.volume.restrict K) ≤ ε / 2 :=
      ENNReal.tendsto_nhds_zero.mp (hH_local K hK) (ε / 2) hhalf_pos
    rcases Filter.eventually_atTop.1 (hF_eventually.and hH_eventually) with
      ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    let μK := g.volume.restrict K
    have hpack := hN n hn
    have hF_n : eLpNorm (fun x : X ↦ (F n).toFun x - f x) 2 μK ≤ ε / 2 := by
      simpa [μK] using hpack.1
    have hH_n : eLpNorm (fun x : X ↦ (H n).toFun x - h x) 2 μK ≤ ε / 2 := by
      simpa [μK] using hpack.2
    have hF_meas :
        AEStronglyMeasurable (fun x : X ↦ (F n).toFun x - f x) μK := by
      have hFn :
          AEStronglyMeasurable (F n).toFun μK :=
        ((F n).memLp_restrict_compact (g := g) hK).aestronglyMeasurable
      exact hFn.sub (by simpa [μK] using hf_meas K hK)
    have hH_meas :
        AEStronglyMeasurable (fun x : X ↦ (H n).toFun x - h x) μK := by
      have hHn :
          AEStronglyMeasurable (H n).toFun μK :=
        ((H n).memLp_restrict_compact (g := g) hK).aestronglyMeasurable
      exact hHn.sub (by simpa [μK] using hh_meas K hK)
    have htri :
        eLpNorm
          (fun x : X ↦ (V n).toFun x - (f x + h x)) 2 μK ≤
          eLpNorm (fun x : X ↦ (F n).toFun x - f x) 2 μK +
            eLpNorm (fun x : X ↦ (H n).toFun x - h x) 2 μK := by
      have hbase :=
        eLpNorm_add_le hF_meas hH_meas
          (by norm_num : (1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞))
      have hfun :
          ((fun x : X ↦ (F n).toFun x - f x) +
              fun x : X ↦ (H n).toFun x - h x) =
            fun x : X ↦ (V n).toFun x - (f x + h x) := by
        funext x
        simp [V, SmoothCompactlySupportedGlobalSurfaceFunction.add,
          Pi.add_apply]
        ring
      simpa [hfun] using hbase
    calc
      eLpNorm
          (fun x : X ↦ (V n).toFun x - (f x + h x))
          2 (g.volume.restrict K)
          =
          eLpNorm
            (fun x : X ↦ (V n).toFun x - (f x + h x)) 2 μK := rfl
      _ ≤
          eLpNorm (fun x : X ↦ (F n).toFun x - f x) 2 μK +
            eLpNorm (fun x : X ↦ (H n).toFun x - h x) 2 μK := htri
      _ ≤ ε / 2 + ε / 2 := add_le_add hF_n hH_n
      _ = ε := ENNReal.add_halves ε

/--
%%handwave
name:
  Compact-local \(L^2\) convergence is stable under bounded smooth multipliers
statement:
  If \(F_n\to f\) in \(L^2(K)\), and \(M\) is continuous, then
  \(M F_n\to Mf\) in \(L^2(K)\).
proof:
  The function \(M\) is bounded on the compact set \(K\).  Hence
  \[
    |M(F_n-f)|\le C_K |F_n-f|
  \]
  on \(K\), and the \(L^2\)-seminorm estimate follows from monotonicity and
  constant multiplication.
-/
theorem TendstoInLocalL2OnSurface.mul_left_continuous
    {X : Type} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} {K : Set X} {H : ℕ → X → ℝ} {f M : X → ℝ}
    (h : TendstoInLocalL2OnSurface μ K H f)
    (hK : IsCompact K) (hM : Continuous M) :
    TendstoInLocalL2OnSurface μ K
      (fun n : ℕ ↦ fun x : X ↦ M x * H n x)
      (fun x : X ↦ M x * f x) := by
  unfold TendstoInLocalL2OnSurface at h ⊢
  rcases hK.exists_bound_of_continuousOn hM.continuousOn with
    ⟨C0, hC0⟩
  let C : ℝ := max 0 C0
  have hbound : ∀ n : ℕ,
      eLpNorm
          (fun x : X ↦ M x * H n x - M x * f x)
          2 (μ.restrict K) ≤
        ENNReal.ofReal C *
          eLpNorm (fun x : X ↦ H n x - f x) 2 (μ.restrict K) := by
    intro n
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul ?_ 2
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hxK
    have hMx_le : ‖M x‖ ≤ C :=
      (hC0 x hxK).trans (le_max_right 0 C0)
    calc
      ‖M x * H n x - M x * f x‖ =
          ‖M x * (H n x - f x)‖ := by ring_nf
      _ = ‖M x‖ * ‖H n x - f x‖ := by
          rw [norm_mul]
      _ ≤ C * ‖H n x - f x‖ :=
          mul_le_mul_of_nonneg_right hMx_le (norm_nonneg _)
  have hmul :
      Filter.Tendsto
        (fun n : ℕ ↦
          ENNReal.ofReal C *
            eLpNorm (fun x : X ↦ H n x - f x) 2 (μ.restrict K))
        Filter.atTop (𝓝 0) := by
    have hC_ne_top : ENNReal.ofReal C ≠ ⊤ := ENNReal.ofReal_ne_top
    simpa using ENNReal.Tendsto.const_mul h (Or.inr hC_ne_top)
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      (g := fun _ : ℕ ↦ (0 : ℝ≥0∞))
      (h := fun n : ℕ ↦
        ENNReal.ofReal C *
          eLpNorm (fun x : X ↦ H n x - f x) 2 (μ.restrict K))
      tendsto_const_nhds hmul
      (fun _ ↦ bot_le) hbound

/--
%%handwave
name:
  Compact-local \(L^2\) convergence gives compact-local \(L^2\)-Cauchy convergence
statement:
  If \(H_n\to f\) in \(L^2(K)\), and the functions involved are locally
  measurable on \(K\), then \(H_n-H_m\to0\) in \(L^2(K)\) as
  \(n,m\to\infty\).
proof:
  Write \(H_n-H_m=(H_n-f)+(f-H_m)\).  The \(L^2\) triangle inequality bounds
  the norm by the two distances to the limit, and both terms are eventually
  smaller than half of the prescribed tolerance.
-/
theorem TendstoInLocalL2OnSurface.cauchy_eLpNorm
    {X : Type} [MeasurableSpace X]
    {μ : Measure X} {K : Set X} {H : ℕ → X → ℝ} {f : X → ℝ}
    (h : TendstoInLocalL2OnSurface μ K H f)
    (hH_meas :
      ∀ n : ℕ, AEStronglyMeasurable (H n) (μ.restrict K))
    (hf_meas : AEStronglyMeasurable f (μ.restrict K)) :
    ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
        eLpNorm (fun x : X ↦ H n x - H m x) 2 (μ.restrict K) ≤ ε := by
  unfold TendstoInLocalL2OnSurface at h
  intro ε hε
  have hhalf_pos : 0 < ε / 2 :=
    ENNReal.div_pos_iff.mpr ⟨hε.ne', ENNReal.ofNat_ne_top⟩
  have hnear :
      ∀ᶠ n : ℕ in Filter.atTop,
        eLpNorm (fun x : X ↦ H n x - f x) 2 (μ.restrict K) ≤
          ε / 2 :=
    ENNReal.tendsto_nhds_zero.mp h (ε / 2) hhalf_pos
  rcases Filter.eventually_atTop.1 hnear with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n m hn hm
  let μK := μ.restrict K
  have hn_le :
      eLpNorm (fun x : X ↦ H n x - f x) 2 μK ≤ ε / 2 := by
    simpa [μK] using hN n hn
  have hm_le :
      eLpNorm (fun x : X ↦ H m x - f x) 2 μK ≤ ε / 2 := by
    simpa [μK] using hN m hm
  have htri :
      eLpNorm (fun x : X ↦ H n x - H m x) 2 μK ≤
        eLpNorm (fun x : X ↦ H n x - f x) 2 μK +
          eLpNorm (fun x : X ↦ f x - H m x) 2 μK := by
    have hadd :=
      eLpNorm_add_le ((hH_meas n).sub hf_meas)
        (hf_meas.sub (hH_meas m))
        (by norm_num : (1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞))
    have hfun :
        ((fun x : X ↦ H n x - f x) +
            fun x : X ↦ f x - H m x) =
          fun x : X ↦ H n x - H m x := by
      funext x
      change (H n x - f x) + (f x - H m x) = H n x - H m x
      ring
    simpa [μK, hfun] using hadd
  have hsymm :
      eLpNorm (fun x : X ↦ f x - H m x) 2 μK =
        eLpNorm (fun x : X ↦ H m x - f x) 2 μK := by
    simpa [Pi.sub_apply] using eLpNorm_sub_comm f (H m) 2 μK
  calc
    eLpNorm (fun x : X ↦ H n x - H m x) 2 (μ.restrict K)
        = eLpNorm (fun x : X ↦ H n x - H m x) 2 μK := rfl
    _ ≤ eLpNorm (fun x : X ↦ H n x - f x) 2 μK +
        eLpNorm (fun x : X ↦ f x - H m x) 2 μK := htri
    _ = eLpNorm (fun x : X ↦ H n x - f x) 2 μK +
        eLpNorm (fun x : X ↦ H m x - f x) 2 μK := by rw [hsymm]
    _ ≤ ε / 2 + ε / 2 := add_le_add hn_le hm_le
    _ = ε := ENNReal.add_halves ε

/--
%%handwave
name:
  The decoded Riesz correction has its pure zero-trace scalar representative
statement:
  The scalar local correction stored in the pure Riesz construction is
  represented by the same compactly supported smooth primitive sequence that
  converges to the Riesz vector in the pure Dirichlet completion.
proof:
  Use the approximating core sequence stored in the decoded scalar data.  Its
  chosen smooth primitives represent the same core elements, converge to the
  Riesz vector in the pure completion, and converge compact-locally in
  \(L^2\) to the stored scalar correction.
-/
theorem rieszLocalCorrection_has_pureH10_scalarRepresentative
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    {φ : LogarithmicCutoffPoleModel g p}
    {source : (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ}
    (hdata :
      GreenSobolevH10SmoothCompactSupportLocalWeakCorrectionData
        φ source) :
    HasPureH10ScalarRepresentative
      (greenSobolevH10SmoothCompactSupportRieszVector source)
      hdata.correction.toFun := by
  classical
  let C := greenSobolevH10SmoothCompactSupportCore g
  let U : ℕ → C.Core := hdata.scalar.approximants
  let F : ℕ → SmoothCompactlySupportedGlobalSurfaceFunction X :=
    fun n : ℕ ↦ greenSobolevH10SmoothCompactSupportCorePrimitive (U n)
  let hF : ∀ n : ℕ,
      SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
        (SurfaceDifferentialField.ofCoordinateField (F n).gradient) :=
    fun n : ℕ ↦
      greenSobolevH10SmoothCompactSupportCorePrimitive_memL2 (U n)
  refine ⟨F, hF, ?_, ?_⟩
  · have hseq :
        (fun n : ℕ ↦
          C.toCompletion
            (greenSmoothCoreElement (g := g) (F n) (hF n))) =
          fun n : ℕ ↦ C.toCompletion (U n) := by
      funext n
      have hcore :
          greenSmoothCoreElement (g := g) (F n) (hF n) = U n := by
        simpa [F, hF, U] using
          greenSmoothCoreElement_chosenPrimitive_eq (g := g) (U n)
      rw [hcore]
    rw [hseq]
    simpa [C, U] using hdata.scalar.approximants_tendsto
  · intro K hK
    simpa [F, U, hdata.correction_toFun_eq_scalar] using
      hdata.scalar.primitive_tendsto_localL2 K hK

/--
%%handwave
name:
  Chartwise regular representatives agree almost everywhere on compact sets
statement:
  If a regular representative agrees almost everywhere in every coordinate
  chart with the local energy potential away from the pole, then it agrees
  almost everywhere with that local energy potential on every compact subset
  of the surface.
proof:
  Use a countable chart cover.  In each chart, the smooth positive surface
  measure has the same null sets as Lebesgue measure with a smooth positive
  density.  The missing pole is a singleton, hence has zero area measure.
  Pull the chartwise almost-everywhere agreement back to the surface and
  glue the countably many source pieces.
-/
theorem localEnergyGreenPotential_chartwise_ae_eq_compact
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [SecondCountableTopology X] [IsManifold SurfaceRealModel ∞ X]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    (φ : LogarithmicCutoffPoleModel g p)
    (h : GreenSobolevH10LocalCorrection g) (G : X → ℝ)
    (hrep :
      ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X),
        (fun w : ℂ ↦ localEnergyGreenPotential φ h (e.symm w))
          =ᵐ[MeasureTheory.volume.restrict
            (e.target ∩ e.symm ⁻¹' {x : X | x ≠ p})]
            (fun w : ℂ ↦ G (e.symm w))) :
    ∀ K : Set X, IsCompact K →
      localEnergyGreenPotential φ h =ᵐ[g.volume.restrict K] G := by
  classical
  let raw : X → ℝ := localEnergyGreenPotential φ h
  have hμ : SmoothPositiveAreaMeasureOnSurface X g.volume :=
    BackgroundSurfaceMetricOnSurface.volume_smooth_positive g
  have hchart_eq :
      ∀ (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X),
        raw =ᵐ[g.volume.restrict e.source] G := by
    intro e he
    let S : Set ℂ := e.target ∩ e.symm ⁻¹' {x : X | x ≠ p}
    let f : ℂ → ℝ := fun z : ℂ ↦ raw (e.symm z)
    let q : ℂ → ℝ := fun z : ℂ ↦ G (e.symm z)
    have hS_subset_target : S ⊆ e.target := Set.inter_subset_left
    have hpunct_target :
        f =ᵐ[(MeasureTheory.volume.restrict e.target).restrict S] q := by
      rw [Measure.restrict_restrict_of_subset (μ := MeasureTheory.volume)
        hS_subset_target]
      simpa [S, f, q, raw] using hrep e he
    have hScompl_subset :
        Sᶜ ⊆ ({e p} : Set ℂ) ∪ e.targetᶜ := by
      intro z hzS
      by_cases hz_target : z ∈ e.target
      · left
        have hnot_ne : ¬ e.symm z ≠ p := by
          intro hz_ne
          exact hzS ⟨hz_target, hz_ne⟩
        have hsymm : e.symm z = p := by
          exact not_not.mp hnot_ne
        have hright : e (e.symm z) = z := e.right_inv hz_target
        have hep : e p = z := by
          simpa [hsymm] using hright
        simp [hep]
      · right
        exact hz_target
    have hsingleton_zero :
        (MeasureTheory.volume.restrict e.target) ({e p} : Set ℂ) = 0 := by
      exact le_antisymm
        (by
          simpa using
            (Measure.restrict_le_self
              (μ := MeasureTheory.volume) (s := e.target) ({e p} : Set ℂ)))
        bot_le
    have htarget_compl_zero :
        (MeasureTheory.volume.restrict e.target) (e.targetᶜ) = 0 := by
      have htarget_ae :
          ∀ᵐ z ∂MeasureTheory.volume.restrict e.target, z ∈ e.target :=
        ae_restrict_mem e.open_target.measurableSet
      simpa [ae_iff] using htarget_ae
    have hScompl_zero :
        (MeasureTheory.volume.restrict e.target) Sᶜ = 0 := by
      exact measure_mono_null hScompl_subset
        (measure_union_null hsingleton_zero htarget_compl_zero)
    have htrivial :
        f =ᵐ[(MeasureTheory.volume.restrict e.target).restrict Sᶜ] q := by
      change ∀ᵐ z ∂(MeasureTheory.volume.restrict e.target).restrict Sᶜ,
        f z = q z
      rw [ae_iff]
      have htotal :
          ((MeasureTheory.volume.restrict e.target).restrict Sᶜ)
              (Set.univ : Set ℂ) = 0 := by
        rw [Measure.restrict_apply MeasurableSet.univ]
        simpa using hScompl_zero
      exact le_antisymm
        (by
          simpa [htotal] using
            (measure_mono
              (Set.subset_univ {z : ℂ | f z ≠ q z}) :
              ((MeasureTheory.volume.restrict e.target).restrict Sᶜ)
                {z : ℂ | f z ≠ q z} ≤
              ((MeasureTheory.volume.restrict e.target).restrict Sᶜ)
                (Set.univ : Set ℂ)))
        bot_le
    have htarget_full :
        f =ᵐ[MeasureTheory.volume.restrict e.target] q :=
      ae_of_ae_restrict_of_ae_restrict_compl S hpunct_target htrivial
    have hmap_full :
        f =ᵐ[Measure.map e (g.volume.restrict e.source)] q :=
      (smoothPositiveAreaMeasureOnSurface_chart_ae_eq
        g.volume hμ e he).2 htarget_full
    have he_aemeas : AEMeasurable e (g.volume.restrict e.source) :=
      openPartialHomeomorph_aemeasurable_restrict_source e g.volume
    have hpull :
        ∀ᵐ x ∂g.volume.restrict e.source,
          f (e x) = q (e x) :=
      ae_of_ae_map he_aemeas hmap_full
    filter_upwards [hpull, ae_restrict_mem e.open_source.measurableSet] with
      x hx hx_source
    simpa [f, q, raw, e.left_inv hx_source] using hx
  obtain ⟨S, hS_countable, hS_cover⟩ :=
    exists_countable_chartAt_source_cover X
  have hcover_restrict :
      raw =ᵐ[g.volume.restrict (⋃ x ∈ S, (chartAt ℂ x).source)] G := by
    refine (ae_restrict_biUnion_iff
      (μ := g.volume) (s := fun x : X ↦ (chartAt ℂ x).source)
      hS_countable (fun y : X ↦ raw y = G y)).2 ?_
    intro x _hxS
    exact hchart_eq (chartAt ℂ x) (chart_mem_atlas ℂ x)
  have hglobal_restrict :
      raw =ᵐ[g.volume.restrict (Set.univ : Set X)] G := by
    simpa [hS_cover] using hcover_restrict
  have hglobal : raw =ᵐ[g.volume] G := by
    simpa using hglobal_restrict
  intro K _hK
  simpa [raw] using ae_restrict_of_ae hglobal

/--
%%handwave
name:
  Finite sums of pure scalar representatives
statement:
  Let \(s\) be a nonempty finite set.  If each \(u_i\), \(i\in s\), has scalar
  representative \(\varphi_i\), locally measurable on compact sets, then
  \(\sum_{i\in s}u_i\) has representative \(\sum_{i\in s}\varphi_i\), which is
  again locally measurable on compact sets.
proof:
  Induct on the nonempty finite set, using closure of scalar representatives
  and almost-everywhere strong measurability under addition.
-/
private theorem HasPureH10ScalarRepresentative.finset_sum_nonempty
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    {ι : Type} [DecidableEq ι]
    (s : Finset ι) (hs : s.Nonempty)
    {U : ι → GreenSobolevH10SmoothCompactSupport g}
    {φ : ι → X → ℝ}
    (hrep :
      ∀ i : ι, i ∈ s →
        HasPureH10ScalarRepresentative (U i) (φ i))
    (hmeas :
      ∀ i : ι, i ∈ s → ∀ K : Set X, IsCompact K →
        AEStronglyMeasurable (φ i) (g.volume.restrict K)) :
    HasPureH10ScalarRepresentative
        (∑ i ∈ s, U i)
        (fun x : X ↦ ∑ i ∈ s, φ i x) ∧
      (∀ K : Set X, IsCompact K →
        AEStronglyMeasurable
          (fun x : X ↦ ∑ i ∈ s, φ i x) (g.volume.restrict K)) := by
  classical
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a =>
      have hrep_a :
          HasPureH10ScalarRepresentative (U a) (φ a) :=
        hrep a (by simp)
      have hmeas_a :
          ∀ K : Set X, IsCompact K →
            AEStronglyMeasurable (φ a) (g.volume.restrict K) :=
        fun K hK ↦ hmeas a (by simp) K hK
      constructor
      · simpa using hrep_a
      · intro K hK
        simpa using hmeas_a K hK
  | cons a s ha hs ih =>
      have hrep_a :
          HasPureH10ScalarRepresentative (U a) (φ a) :=
        hrep a (Finset.mem_cons_self a s)
      have hmeas_a :
          ∀ K : Set X, IsCompact K →
            AEStronglyMeasurable (φ a) (g.volume.restrict K) :=
        fun K hK ↦ hmeas a (Finset.mem_cons_self a s) K hK
      have hrep_s :
          ∀ i : ι, i ∈ s →
            HasPureH10ScalarRepresentative (U i) (φ i) := by
        intro i hi
        exact hrep i (Finset.mem_cons_of_mem hi)
      have hmeas_s :
          ∀ i : ι, i ∈ s → ∀ K : Set X, IsCompact K →
            AEStronglyMeasurable (φ i) (g.volume.restrict K) := by
        intro i hi K hK
        exact hmeas i (Finset.mem_cons_of_mem hi) K hK
      rcases ih hrep_s hmeas_s with ⟨hs_rep, hs_meas⟩
      constructor
      · have hadd :
            HasPureH10ScalarRepresentative
              (U a + ∑ i ∈ s, U i)
              (fun x : X ↦ φ a x + ∑ i ∈ s, φ i x) :=
          HasPureH10ScalarRepresentative.add
            hrep_a hs_rep hmeas_a hs_meas
        simpa [Finset.cons_eq_insert, ha, Pi.add_apply] using hadd
      · intro K hK
        have hadd_meas :
            AEStronglyMeasurable
              (fun x : X ↦ φ a x + ∑ i ∈ s, φ i x)
              (g.volume.restrict K) :=
          (hmeas_a K hK).add (hs_meas K hK)
        simpa [Finset.cons_eq_insert, ha, Pi.add_apply] using hadd_meas

/--
%%handwave
name:
  Lipschitz maps preserve compact-local \(L^2\) convergence
statement:
  If \(H_n\to f\) in \(L^2\) on a compact set and \(T:\mathbb R\to\mathbb R\)
  is Lipschitz, then \(T\circ H_n\to T\circ f\) in \(L^2\) on that compact
  set.
proof:
  The pointwise Lipschitz inequality gives
  \[
    |T(H_n)-T(f)|\le L |H_n-f|.
  \]
  Monotonicity of the \(L^2\)-seminorm and multiplication by the fixed
  constant \(L\) preserve convergence to zero.
-/
theorem TendstoInLocalL2OnSurface.comp_lipschitz
    {X : Type} [MeasurableSpace X]
    {μ : Measure X} {K : Set X} {H : ℕ → X → ℝ} {f : X → ℝ}
    (h : TendstoInLocalL2OnSurface μ K H f)
    {T : ℝ → ℝ} {L : ℝ}
    (_hL_nonneg : 0 ≤ L)
    (hT_lipschitz : ∀ s t : ℝ, |T s - T t| ≤ L * |s - t|) :
    TendstoInLocalL2OnSurface μ K
      (fun n : ℕ ↦ fun x : X ↦ T (H n x))
      (fun x : X ↦ T (f x)) := by
  unfold TendstoInLocalL2OnSurface at h ⊢
  have hbound : ∀ n : ℕ,
      eLpNorm (fun x : X ↦ T (H n x) - T (f x)) 2 (μ.restrict K) ≤
        ENNReal.ofReal L *
          eLpNorm (fun x : X ↦ H n x - f x) 2 (μ.restrict K) := by
    intro n
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul ?_ 2
    filter_upwards [] with x
    have hpoint := hT_lipschitz (H n x) (f x)
    simpa [Real.norm_eq_abs, abs_sub_comm, mul_comm] using hpoint
  have hmul :
      Filter.Tendsto
        (fun n : ℕ ↦
          ENNReal.ofReal L *
            eLpNorm (fun x : X ↦ H n x - f x) 2 (μ.restrict K))
        Filter.atTop (𝓝 0) := by
    have hL_ne_top : ENNReal.ofReal L ≠ ⊤ := ENNReal.ofReal_ne_top
    simpa using
      ENNReal.Tendsto.const_mul h (Or.inr hL_ne_top)
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      (g := fun _ : ℕ ↦ (0 : ℝ≥0∞))
      (h := fun n : ℕ ↦
        ENNReal.ofReal L *
          eLpNorm (fun x : X ↦ H n x - f x) 2 (μ.restrict K))
      tendsto_const_nhds hmul
      (fun _ ↦ bot_le) hbound

/--
%%handwave
name:
  Smooth zero-preserving uniform approximation of a Lipschitz map
statement:
  If \(T:\mathbb R\to\mathbb R\) is Lipschitz and \(T(0)=0\), then for every
  \(\varepsilon>0\) there is a smooth function \(S:\mathbb R\to\mathbb R\)
  with \(S(0)=0\) and \(|S(t)-T(t)|<\varepsilon\) for all \(t\).
proof:
  Use the standard smooth approximation theorem for uniformly continuous
  functions.  Since the approximant need not fix zero, subtract its value at
  zero.  This changes the uniform error by at most the approximation error at
  zero, so starting with error \(\varepsilon/2\) gives the result.
-/
theorem lipschitzZero_has_smooth_zero_uniform_approx
    {T : ℝ → ℝ} {L ε : ℝ}
    (hL_nonneg : 0 ≤ L)
    (hT_zero : T 0 = 0)
    (hT_lipschitz : ∀ s t : ℝ, |T s - T t| ≤ L * |s - t|)
    (hε : 0 < ε) :
    ∃ S : ℝ → ℝ, ContDiff ℝ ∞ S ∧ S 0 = 0 ∧
      ∀ t : ℝ, |S t - T t| < ε := by
  have hLip : LipschitzWith (Real.toNNReal L) T := by
    refine LipschitzWith.of_dist_le' (f := T) ?_
    intro s t
    have hpoint := hT_lipschitz s t
    have hcoe : ((Real.toNNReal L : NNReal) : ℝ) = L := by
      have hnn : Real.toNNReal L = (⟨L, hL_nonneg⟩ : NNReal) :=
        Real.toNNReal_of_nonneg hL_nonneg
      exact congrArg Subtype.val hnn
    simpa [Real.dist_eq, hcoe] using hpoint
  have hε2 : 0 < ε / 2 := by positivity
  rcases hLip.uniformContinuous.exists_contDiff_dist_le hε2 with
    ⟨S, hS_smooth, hS_close⟩
  refine ⟨fun t : ℝ ↦ S t - S 0, ?_, ?_, ?_⟩
  · exact hS_smooth.sub contDiff_const
  · simp
  · intro t
    have ht : ‖S t - T t‖ < ε / 2 := by
      simpa [Real.dist_eq] using hS_close t
    have h0 : ‖S 0 - T 0‖ < ε / 2 := by
      simpa [Real.dist_eq] using hS_close 0
    have hle : ‖(S t - S 0) - T t‖ ≤
        ‖S t - T t‖ + ‖S 0 - T 0‖ := by
      calc
        ‖(S t - S 0) - T t‖ =
            ‖(S t - T t) - (S 0 - T 0)‖ := by
          rw [hT_zero]
          ring_nf
        _ ≤ ‖S t - T t‖ + ‖S 0 - T 0‖ := norm_sub_le _ _
    have hlt : ‖(S t - S 0) - T t‖ < ε := by
      calc
        ‖(S t - S 0) - T t‖ ≤
            ‖S t - T t‖ + ‖S 0 - T 0‖ := hle
        _ < ε / 2 + ε / 2 := add_lt_add ht h0
        _ = ε := by ring
    simpa [Real.norm_eq_abs] using hlt

/--
%%handwave
name:
  Mollification preserves a Lipschitz constant
statement:
  Let \(k\ge0\) be a normalized smooth compactly supported bump on \(\mathbb R\).
  If \(\lvert T(s)-T(t)\rvert\le L\lvert s-t\rvert\) with \(L\ge0\), then
  \(k*T\) is also \(L\)-Lipschitz.
proof:
  Subtract the two convolution integrals, use the Lipschitz estimate for \(T\),
  and integrate against \(k\).  Positivity and \(\int k=1\) leave the same constant \(L\).
-/
private theorem normedBump_convolution_lipschitz
    (φ : ContDiffBump (0 : ℝ))
    {T : ℝ → ℝ} {L : ℝ}
    (hL_nonneg : 0 ≤ L)
    (hT_lipschitz : ∀ s t : ℝ, |T s - T t| ≤ L * |s - t|) :
    LipschitzWith (Real.toNNReal L)
      ((φ.normed (MeasureTheory.volume : Measure ℝ) ⋆[lsmul ℝ ℝ,
        (MeasureTheory.volume : Measure ℝ)] T : ℝ → ℝ)) := by
  let μ : Measure ℝ := MeasureTheory.volume
  let k : ℝ → ℝ := φ.normed μ
  let M : ℝ → ℝ := (k ⋆[lsmul ℝ ℝ, μ] T : ℝ → ℝ)
  have hcoe : ((Real.toNNReal L : NNReal) : ℝ) = L := by
    have hnn : Real.toNNReal L = (⟨L, hL_nonneg⟩ : NNReal) :=
      Real.toNNReal_of_nonneg hL_nonneg
    exact congrArg Subtype.val hnn
  have hLipT : LipschitzWith (Real.toNNReal L) T := by
    refine LipschitzWith.of_dist_le' (f := T) ?_
    intro s t
    have hpoint := hT_lipschitz s t
    simpa [Real.dist_eq, hcoe] using hpoint
  have hT_locInt : LocallyIntegrable T μ :=
    hLipT.continuous.locallyIntegrable
  have hconv : ConvolutionExists k T (lsmul ℝ ℝ) μ :=
    φ.hasCompactSupport_normed.convolutionExists_left
      (L := lsmul ℝ ℝ) φ.continuous_normed hT_locInt
  refine LipschitzWith.of_dist_le' (f := M) ?_
  intro x y
  have hx_int : Integrable (fun u : ℝ ↦ k u • T (x - u)) μ := by
    simpa [ConvolutionExistsAt, k, M] using hconv x
  have hy_int : Integrable (fun u : ℝ ↦ k u • T (y - u)) μ := by
    simpa [ConvolutionExistsAt, k, M] using hconv y
  have hsub :
      M x - M y =
        ∫ u : ℝ, k u * (T (x - u) - T (y - u)) ∂μ := by
    calc
      M x - M y =
          (∫ u : ℝ, k u • T (x - u) ∂μ) -
            ∫ u : ℝ, k u • T (y - u) ∂μ := by
        simp [M, convolution_def, k]
      _ = ∫ u : ℝ, k u • T (x - u) - k u • T (y - u) ∂μ := by
        rw [← integral_sub hx_int hy_int]
      _ = ∫ u : ℝ, k u * (T (x - u) - T (y - u)) ∂μ := by
        congr 1
        ext u
        simp [smul_eq_mul, mul_sub]
  have hmajor_int :
      Integrable (fun u : ℝ ↦ k u * (L * |x - y|)) μ := by
    simpa [k, mul_assoc] using
      (φ.integrable_normed (μ := μ)).mul_const (L * |x - y|)
  have hbound_ae :
      ∀ᵐ u ∂μ,
        ‖k u * (T (x - u) - T (y - u))‖ ≤
          k u * (L * |x - y|) := by
    filter_upwards [] with u
    have hk_nonneg : 0 ≤ k u := by
      simpa [k] using φ.nonneg_normed (μ := μ) u
    have hpoint := hT_lipschitz (x - u) (y - u)
    have hdist_arg : |(x - u) - (y - u)| = |x - y| := by
      ring_nf
    have hdiff : |T (x - u) - T (y - u)| ≤ L * |x - y| := by
      simpa [hdist_arg] using hpoint
    calc
      ‖k u * (T (x - u) - T (y - u))‖ =
          k u * |T (x - u) - T (y - u)| := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hk_nonneg]
      _ ≤ k u * (L * |x - y|) :=
        mul_le_mul_of_nonneg_left hdiff hk_nonneg
  have hnorm :
      ‖M x - M y‖ ≤ ∫ u : ℝ, k u * (L * |x - y|) ∂μ := by
    rw [hsub]
    exact norm_integral_le_of_norm_le hmajor_int hbound_ae
  have hintegral :
      ∫ u : ℝ, k u * (L * |x - y|) ∂μ = L * |x - y| := by
    calc
      ∫ u : ℝ, k u * (L * |x - y|) ∂μ =
          (∫ u : ℝ, k u ∂μ) * (L * |x - y|) := by
        rw [integral_mul_const]
      _ = 1 * (L * |x - y|) := by
        rw [φ.integral_normed (μ := μ)]
      _ = L * |x - y| := by ring
  have hdist : dist (M x) (M y) ≤ L * dist x y := by
    calc
      dist (M x) (M y) = ‖M x - M y‖ := by
        rw [dist_eq_norm]
      _ ≤ ∫ u : ℝ, k u * (L * |x - y|) ∂μ := hnorm
      _ = L * dist x y := by
        rw [hintegral]
        simp [Real.dist_eq]
  simpa [M, k, hcoe] using hdist

/--
%%handwave
name:
  Smooth mollifier approximants with controlled slope
statement:
  If \(T:\mathbb R\to\mathbb R\) is \(L\)-Lipschitz and \(T(0)=0\), then for
  every \(\varepsilon>0\) there is a smooth function \(S\) with \(S(0)=0\),
  \(|S-T|<\varepsilon\) everywhere, and \(\|dS\|\le L\) everywhere.
proof:
  Convolve \(T\) with a normalized nonnegative smooth bump of sufficiently
  small radius and subtract the value at \(0\).  The bump average gives
  uniform convergence.  Since the kernel is nonnegative and has integral
  \(1\), the average of translated differences preserves the Lipschitz
  constant exactly; the derivative bound follows from the converse Lipschitz
  estimate for the Fréchet derivative.
-/
theorem lipschitzZero_has_smooth_zero_mollifier_approx_deriv_bound
    {T : ℝ → ℝ} {L ε : ℝ}
    (hL_nonneg : 0 ≤ L)
    (hT_zero : T 0 = 0)
    (hT_lipschitz : ∀ s t : ℝ, |T s - T t| ≤ L * |s - t|)
    (hε : 0 < ε) :
    ∃ S : ℝ → ℝ,
      ContDiff ℝ ∞ S ∧
      S 0 = 0 ∧
      (∀ t : ℝ, |S t - T t| < ε) ∧
      ∀ t : ℝ, ‖fderiv ℝ S t‖ ≤ L := by
  let δ : ℝ := ε / (4 * (L + 1))
  have hL1_pos : 0 < L + 1 := by linarith
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  let φ : ContDiffBump (0 : ℝ) :=
    { rIn := δ / 2
      rOut := δ
      rIn_pos := by positivity
      rIn_lt_rOut := by
        have hpos : 0 < δ := hδ_pos
        nlinarith }
  let μ : Measure ℝ := MeasureTheory.volume
  let k : ℝ → ℝ := φ.normed μ
  let M : ℝ → ℝ := (k ⋆[lsmul ℝ ℝ, μ] T : ℝ → ℝ)
  have hcoe : ((Real.toNNReal L : NNReal) : ℝ) = L := by
    have hnn : Real.toNNReal L = (⟨L, hL_nonneg⟩ : NNReal) :=
      Real.toNNReal_of_nonneg hL_nonneg
    exact congrArg Subtype.val hnn
  have hLipT : LipschitzWith (Real.toNNReal L) T := by
    refine LipschitzWith.of_dist_le' (f := T) ?_
    intro s t
    have hpoint := hT_lipschitz s t
    simpa [Real.dist_eq, hcoe] using hpoint
  have hT_locInt : LocallyIntegrable T μ :=
    hLipT.continuous.locallyIntegrable
  have hM_smooth : ContDiff ℝ ∞ M := by
    dsimp [M, k]
    exact
      φ.hasCompactSupport_normed.contDiff_convolution_left
        (lsmul ℝ ℝ) φ.contDiff_normed hT_locInt
  have hT_meas : AEStronglyMeasurable T μ :=
    hLipT.continuous.aestronglyMeasurable
  have hM_close : ∀ t : ℝ, ‖M t - T t‖ ≤ L * δ := by
    intro t
    have hdist :
        dist (M t) (T t) ≤ L * δ := by
      simpa [M, k] using
        φ.dist_normed_convolution_le
          (μ := μ) (g := T) (x₀ := t) (ε := L * δ)
          hT_meas
          (by
            intro z hz
            have hz_le : |z - t| ≤ δ := by
              have hz_lt : dist z t < δ := by
                simpa [φ] using hz
              simpa [Real.dist_eq] using hz_lt.le
            calc
              dist (T z) (T t) = |T z - T t| := by
                rw [Real.dist_eq]
              _ ≤ L * |z - t| := hT_lipschitz z t
              _ ≤ L * δ := mul_le_mul_of_nonneg_left hz_le hL_nonneg)
    simpa [Real.dist_eq] using hdist
  have hsmall : L * δ + L * δ < ε := by
    have hden_pos : 0 < 2 * (L + 1) := by positivity
    have hfrac_lt_one : L / (2 * (L + 1)) < 1 := by
      rw [div_lt_one hden_pos]
      nlinarith
    have hmul_lt : ε * (L / (2 * (L + 1))) < ε * 1 :=
      mul_lt_mul_of_pos_left hfrac_lt_one hε
    calc
      L * δ + L * δ = ε * (L / (2 * (L + 1))) := by
        dsimp [δ]
        field_simp [hL1_pos.ne']
        ring
      _ < ε * 1 := hmul_lt
      _ = ε := by ring
  have hM_lip :
      LipschitzWith (Real.toNNReal L) M := by
    simpa [M, k] using
      normedBump_convolution_lipschitz φ hL_nonneg hT_lipschitz
  let S : ℝ → ℝ := fun t : ℝ ↦ M t - M 0
  have hS_smooth : ContDiff ℝ ∞ S := by
    dsimp [S]
    exact hM_smooth.sub contDiff_const
  have hS_lip : LipschitzWith (Real.toNNReal L) S := by
    refine LipschitzWith.of_dist_le' (f := S) ?_
    intro s t
    have hdist := hM_lip.dist_le_mul s t
    simpa [S, Real.dist_eq, hcoe] using hdist
  refine ⟨S, hS_smooth, ?_, ?_, ?_⟩
  · dsimp [S]
    simp
  · intro t
    have ht := hM_close t
    have h0 := hM_close 0
    have hle : ‖S t - T t‖ ≤ ‖M t - T t‖ + ‖M 0 - T 0‖ := by
      calc
        ‖S t - T t‖ = ‖(M t - T t) - (M 0 - T 0)‖ := by
          dsimp [S]
          rw [hT_zero]
          ring_nf
        _ ≤ ‖M t - T t‖ + ‖M 0 - T 0‖ := norm_sub_le _ _
    have hlt : ‖S t - T t‖ < ε := by
      calc
        ‖S t - T t‖ ≤ ‖M t - T t‖ + ‖M 0 - T 0‖ := hle
        _ ≤ L * δ + L * δ := add_le_add ht h0
        _ < ε := hsmall
    simpa [Real.norm_eq_abs] using hlt
  · intro t
    have hderiv :
        ‖fderiv ℝ S t‖ ≤ ((Real.toNNReal L : NNReal) : ℝ) :=
      norm_fderiv_le_of_lipschitz (𝕜 := ℝ) (x₀ := t) hS_lip
    simpa [hcoe] using hderiv

namespace SmoothCompactlySupportedGlobalSurfaceFunction

/--
%%handwave
name:
  Smooth zero-preserving outer composition
statement:
  If \(S:\mathbb R\to\mathbb R\) is smooth and \(S(0)=0\), then composing a
  smooth compactly supported surface test function with \(S\) again gives a
  smooth compactly supported surface test function.
proof:
  Smoothness is local in charts and follows from the ordinary smooth chain
  rule.  The differential is the chain-rule differential.  Since \(S(0)=0\),
  the support of the composite is contained in the support of the original
  function, hence remains compact.
-/
noncomputable def compSmoothZero
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (F : SmoothCompactlySupportedGlobalSurfaceFunction X)
    (S : ℝ → ℝ) (hS_smooth : ContDiff ℝ ∞ S) (hS_zero : S 0 = 0) :
    SmoothCompactlySupportedGlobalSurfaceFunction X where
  toFun := fun x : X ↦ S (F.toFun x)
  gradient := fun x : X ↦
    (fderiv ℝ S (F.toFun x)).comp (F.gradient x)
  smooth := by
    intro e he
    simpa [Function.comp_def] using hS_smooth.comp_contDiffOn (F.smooth e he)
  gradient_eq := by
    intro e he z hz v
    have hFdiff :
        DifferentiableAt ℝ (fun w : ℂ ↦ F.toFun (e.symm w)) z :=
      surfaceFunctionChartRepresentative_differentiableAt e he F.toFun F.smooth z hz
    have hSdiff : DifferentiableAt ℝ S (F.toFun (e.symm z)) :=
      (hS_smooth.differentiable (by simp)).differentiableAt
    have hchain :
        fderiv ℝ (fun w : ℂ ↦ S (F.toFun (e.symm w))) z =
          (fderiv ℝ S (F.toFun (e.symm z))).comp
            (fderiv ℝ (fun w : ℂ ↦ F.toFun (e.symm w)) z) := by
      simpa [Function.comp_def] using fderiv_comp z hSdiff hFdiff
    calc
      ((fderiv ℝ S (F.toFun (e.symm z))).comp (F.gradient (e.symm z)))
          (surfaceChartTangentMap e z v)
          =
          fderiv ℝ S (F.toFun (e.symm z))
            (F.gradient (e.symm z) (surfaceChartTangentMap e z v)) := by
            rfl
      _ =
          fderiv ℝ S (F.toFun (e.symm z))
            (fderiv ℝ (fun w : ℂ ↦ F.toFun (e.symm w)) z v) := by
            rw [F.gradient_eq e he z hz v]
      _ =
          ((fderiv ℝ S (F.toFun (e.symm z))).comp
            (fderiv ℝ (fun w : ℂ ↦ F.toFun (e.symm w)) z)) v := by
            rfl
      _ =
          fderiv ℝ (fun w : ℂ ↦ S (F.toFun (e.symm w))) z v := by
            rw [hchain]
  compact_support := by
    have hF : HasCompactSupport F.toFun := by
      simpa [HasCompactSupportOnSurface, HasCompactSupport] using F.compact_support
    have hcomp : HasCompactSupport (S ∘ F.toFun) :=
      hF.comp_left hS_zero
    simpa [HasCompactSupportOnSurface, HasCompactSupport, Function.comp_def] using hcomp

/--
%%handwave
name:
  Value of smooth composition
statement:
  If \(F\) is a smooth compactly supported surface function and
  \(S:\mathbb R\to\mathbb R\) is smooth with \(S(0)=0\), then the compactly
  supported composition satisfies \((S\circ F)(x)=S(F(x))\).
proof:
  This is the defining value of the composition construction.
-/
@[simp]
theorem compSmoothZero_toFun
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (F : SmoothCompactlySupportedGlobalSurfaceFunction X)
    (S : ℝ → ℝ) (hS_smooth : ContDiff ℝ ∞ S) (hS_zero : S 0 = 0)
    (x : X) :
    (F.compSmoothZero S hS_smooth hS_zero).toFun x = S (F.toFun x) :=
  rfl

/--
%%handwave
name:
  Differential of smooth composition
statement:
  Under the same hypotheses, the stored differential of \(S\circ F\) at \(x\)
  is \(DS_{F(x)}\circ dF_x\).
proof:
  This is the chain-rule formula built into the composition construction.
-/
@[simp]
theorem compSmoothZero_gradient
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (F : SmoothCompactlySupportedGlobalSurfaceFunction X)
    (S : ℝ → ℝ) (hS_smooth : ContDiff ℝ ∞ S) (hS_zero : S 0 = 0)
    (x : X) :
    (F.compSmoothZero S hS_smooth hS_zero).gradient x =
      (fderiv ℝ S (F.toFun x)).comp (F.gradient x) :=
  rfl

/--
%%handwave
name:
  One-dimensional linear maps act by their value on one
statement:
  Composing a real-valued differential with a continuous linear map
  \(\mathbb R\to\mathbb R\) is the same as multiplying the differential by
  the scalar value of that map on \(1\).
proof:
  A real-linear map is determined by the image of \(1\).
-/
theorem realContinuousLinearMap_comp_eq_smul
    (A : ℝ →L[ℝ] ℝ) (B : ℂ →L[ℝ] ℝ) :
    A.comp B = (A 1) • B := by
  ext v
  calc
    A (B v) = A ((B v) • (1 : ℝ)) := by simp
    _ = (B v) • A 1 := by rw [A.map_smul]
    _ = (A 1) • B v := by
      simp [mul_comm]

/--
%%handwave
name:
  Smooth composition gradient is scalar multiplication
statement:
  The differential of \(S\circ F\) is the differential of \(F\) multiplied by
  the ordinary derivative of \(S\) evaluated at \(F\).
proof:
  Combine the chain-rule formula for the stored differential with the fact
  that a real one-dimensional linear map is multiplication by its value on
  \(1\).
-/
theorem compSmoothZero_gradient_eq_smul_derivative
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (F : SmoothCompactlySupportedGlobalSurfaceFunction X)
    (S : ℝ → ℝ) (hS_smooth : ContDiff ℝ ∞ S) (hS_zero : S 0 = 0)
    (x : X) :
    (F.compSmoothZero S hS_smooth hS_zero).gradient x =
      (fderiv ℝ S (F.toFun x) 1) • F.gradient x := by
  simpa using
    realContinuousLinearMap_comp_eq_smul
      (fderiv ℝ S (F.toFun x)) (F.gradient x)

end SmoothCompactlySupportedGlobalSurfaceFunction

/--
%%handwave
name:
  The chart tangent map at its base point is the identity
statement:
  For every \(x\) on a complex surface, the tangent map of the chart transition
  from the chart at \(x\) to itself, evaluated at the coordinate of \(x\), is
  \(\operatorname{id}_{\mathbb C}\).
proof:
  On the chart target, the chart followed by its inverse is the identity.
  Differentiate this equality within the open target.
-/
private theorem surfaceChartTangentMap_chartAt_self
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (x : X) :
    surfaceChartTangentMap (chartAt ℂ x) ((chartAt ℂ x) x) =
      ContinuousLinearMap.id ℝ ℂ := by
  let e := chartAt ℂ x
  have hxsource : x ∈ e.source := by
    simp [e]
  have hz : e x ∈ e.target := e.map_source hxsource
  have hsymm : e.symm (e x) = x := e.left_inv hxsource
  have hcongr :
      Set.EqOn
        (fun w : ℂ ↦ chartAt ℂ (e.symm (e x)) (e.symm w))
        (fun w : ℂ ↦ w) e.target := by
    intro w hw
    simpa [e, hsymm] using e.right_inv hw
  rw [surfaceChartTangentMap]
  rw [fderivWithin_congr' hcongr hz]
  exact fderivWithin_id (e.open_target.uniqueDiffWithinAt hz)

/--
%%handwave
name:
  The stored gradient is the exterior differential
statement:
  For every smooth compactly supported real function \(F\) on a surface, its
  stored cotangent field equals its exterior differential: \(\nabla F=dF\).
proof:
  Evaluate both fields in the chart at each point.  The self-transition tangent
  map there is the identity, so their coordinate derivative formulas coincide.
-/
theorem SmoothCompactlySupportedGlobalSurfaceFunction.gradient_eq_surfaceExteriorDerivative
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X]
    (F : SmoothCompactlySupportedGlobalSurfaceFunction X) :
    F.gradient = surfaceExteriorDerivative F.toFun := by
  funext x
  ext v
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ x
  have he : e ∈ atlas ℂ X := by
    simp [e]
  have hxsource : x ∈ e.source := by
    simp [e]
  have hz : e x ∈ e.target := e.map_source hxsource
  have hsymm : e.symm (e x) = x := e.left_inv hxsource
  have hmap :
      surfaceChartTangentMap e (e x) =
        ContinuousLinearMap.id ℝ ℂ := by
    simpa [e] using surfaceChartTangentMap_chartAt_self (X := X) x
  have hF :=
    F.gradient_eq e he (e x) hz v
  have hcanonical :=
    surfaceExteriorDerivative_apply_chartTangentMap_of_smooth
      e he F.toFun F.smooth (e x) hz v
  simpa [hmap, hsymm] using hF.trans hcanonical.symm

/--
%%handwave
name:
  Smooth compactly supported functions have square-integrable differential
statement:
  The classical differential of a compactly supported smooth surface function
  is square-integrable for any smooth background surface metric.
proof:
  The stored differential agrees with the canonical exterior derivative.  The
  exterior derivative section of a smooth function is continuous, hence its
  metric norm square is continuous.  Outside the support of the function the
  differential is locally zero, so the norm square has compact support; finite
  measure on compact sets gives integrability.
-/
theorem SmoothCompactlySupportedGlobalSurfaceFunction.differential_memHilbertSchmidtL2
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (F : SmoothCompactlySupportedGlobalSurfaceFunction X) :
    SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
      (SurfaceDifferentialField.ofCoordinateField F.gradient) := by
  let G :=
    manifoldDifferentialHilbertBundleGeometry
      (I := SurfaceRealModel) (X := X) (E := ℝ) g.metric.toManifoldMetric
  change HilbertBundleSectionMemL2 G g.volume
    (SurfaceDifferentialField.ofCoordinateField F.gradient)
  have hgrad_eq :
      F.gradient = surfaceExteriorDerivative F.toFun :=
    F.gradient_eq_surfaceExteriorDerivative
  refine ⟨?_, ?_⟩
  · have hf_contMDiff : ContMDiff SurfaceRealModel 𝓘(ℝ, ℝ) ∞ F.toFun :=
      isSmoothOnSurface_univ_contMDiff F.smooth
    have hcont :
        Continuous
          (fun x : X ↦
            (Bundle.TotalSpace.mk' (ℂ →L[ℝ] ℝ) x
              ((SurfaceDifferentialField.ofCoordinateField F.gradient) x) :
                SurfaceDifferentialTotalSpace X ℝ)) := by
      simpa [hgrad_eq, SurfaceDifferentialField.ofCoordinateField] using
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
      simpa [hgrad_eq, SurfaceDifferentialField.ofCoordinateField] using
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
          simpa [hgrad_eq] using hdiff
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
  Gradient energy density is bounded on compact support
statement:
  For a smooth compactly supported surface function \(F\), there is \(C\ge0\)
  such that \(\langle\nabla F,\nabla F\rangle_g(x)\le C\) for every
  \(x\in\operatorname{tsupp}F\).
proof:
  The squared fiber norm of \(dF\) is continuous and equals the metric gradient
  pairing.  It is bounded on the compact topological support; enlarge the bound to be nonnegative.
-/
private theorem SmoothCompactlySupportedGlobalSurfaceFunction.gradientInner_self_bound_on_tsupport
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (F : SmoothCompactlySupportedGlobalSurfaceFunction X) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ tsupport F.toFun,
        g.gradientInner x (F.gradient x) (F.gradient x) ≤ C := by
  let G :=
    manifoldDifferentialHilbertBundleGeometry
      (I := SurfaceRealModel) (X := X) (E := ℝ) g.metric.toManifoldMetric
  let M :=
    manifoldDifferentialHilbertSchmidtContinuousRiemannianMetric
      (I := SurfaceRealModel) (X := X) (E := ℝ) g.metric.toManifoldMetric
  let ψ : X → ℝ := fun x ↦
    G.fiberNormSq x
      ((SurfaceDifferentialField.ofCoordinateField F.gradient) x)
  have hgrad_eq :
      F.gradient = surfaceExteriorDerivative F.toFun :=
    F.gradient_eq_surfaceExteriorDerivative
  have hsec :
      Continuous
        (fun x : X ↦
          (Bundle.TotalSpace.mk' (ℂ →L[ℝ] ℝ) x
            ((SurfaceDifferentialField.ofCoordinateField F.gradient) x) :
              SurfaceDifferentialTotalSpace X ℝ)) := by
    have hf_contMDiff : ContMDiff SurfaceRealModel 𝓘(ℝ, ℝ) ∞ F.toFun :=
      isSmoothOnSurface_univ_contMDiff F.smooth
    simpa [hgrad_eq, SurfaceDifferentialField.ofCoordinateField] using
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
  rcases F.compact_support.exists_bound_of_continuousOn hψ_cont.continuousOn with
    ⟨C₀, hC₀⟩
  let C : ℝ := max C₀ 0
  have hC_nonneg : 0 ≤ C := le_max_right C₀ 0
  refine ⟨C, hC_nonneg, ?_⟩
  intro x hx
  have hψ_eq :
      ψ x = g.gradientInner x (F.gradient x) (F.gradient x) := by
    simpa [ψ] using
      surface_coordinate_cotangent_fiberNormSq_eq_gradientInner
        g x (F.gradient x)
  have hgrad_nonneg : 0 ≤ g.gradientInner x (F.gradient x) (F.gradient x) :=
    BackgroundSurfaceMetricOnSurface.gradientInner_nonneg g x (F.gradient x)
  have hψ_abs_le : ‖ψ x‖ ≤ C₀ := hC₀ x hx
  have hψ_le : ψ x ≤ C₀ := by
    simpa [hψ_eq, Real.norm_eq_abs, abs_of_nonneg hgrad_nonneg] using
      hψ_abs_le
  rw [← hψ_eq]
  exact hψ_le.trans (le_max_left C₀ 0)

/--
%%handwave
name:
  The gradient vanishes off the topological support
statement:
  If \(x\notin\operatorname{tsupp}F\) for a smooth compactly supported function
  \(F\), then \(\nabla F(x)=0\).
proof:
  The exterior differential of a smooth function vanishes away from its
  topological support, and the stored gradient equals that exterior differential.
-/
private theorem SmoothCompactlySupportedGlobalSurfaceFunction.gradient_eq_zero_of_notMem_tsupport
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X]
    (F : SmoothCompactlySupportedGlobalSurfaceFunction X) {x : X}
    (hx : x ∉ tsupport F.toFun) :
    F.gradient x = 0 := by
  have hgrad_eq :
      F.gradient = surfaceExteriorDerivative F.toFun :=
    F.gradient_eq_surfaceExteriorDerivative
  have hdiff :
      surfaceExteriorDerivative F.toFun x = 0 :=
    surfaceDifferential_eq_zero_of_notMem_tsupport
      (surfaceExteriorDerivative_isSurfaceDifferential F.smooth) hx
  simpa [hgrad_eq] using hdiff

/--
%%handwave
name:
  Quadratic bound for the sum of two cotangent vectors
statement:
  For cotangent vectors \(\xi,\eta\) at \(x\),
  \[
    \langle\xi+\eta,\xi+\eta\rangle_g
    \le 2\langle\xi,\xi\rangle_g+2\langle\eta,\eta\rangle_g.
  \]
proof:
  Identify the metric pairing with squared Hilbert norm, apply
  \(\lVert\xi+\eta\rVert\le\lVert\xi\rVert+\lVert\eta\rVert\), and use
  \((a+b)^2\le2a^2+2b^2\).
-/
private theorem BackgroundSurfaceMetricOnSurface.gradientInner_add_le_two
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold SurfaceRealModel 1 X]
    (g : BackgroundSurfaceMetricOnSurface X) (x : X)
    (ξ η : ℂ →L[ℝ] ℝ) :
    g.gradientInner x (ξ + η) (ξ + η) ≤
      2 * g.gradientInner x ξ ξ + 2 * g.gradientInner x η η := by
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
  let V := ManifoldDifferentialBundleFiber
    (I := SurfaceRealModel) (X := X) (E := ℝ) x
  let ξV : V := ξ
  let ηV : V := η
  have hinner_eq :
      ∀ ζ : V, inner ℝ ζ ζ =
        g.gradientInner x (ζ : ℂ →L[ℝ] ℝ) (ζ : ℂ →L[ℝ] ℝ) := by
    intro ζ
    change
      manifoldDifferentialHilbertSchmidtInnerCLMAt
        (I := SurfaceRealModel) (X := X) (E := ℝ)
        g.metric.toManifoldMetric x ζ ζ =
          g.gradientInner x (ζ : ℂ →L[ℝ] ℝ) (ζ : ℂ →L[ℝ] ℝ)
    exact surface_coordinate_cotangent_fiberInner_eq_gradientInner
      g x (ζ : ℂ →L[ℝ] ℝ) (ζ : ℂ →L[ℝ] ℝ)
  have hnorm_sq :
      ∀ ζ : V,
        g.gradientInner x (ζ : ℂ →L[ℝ] ℝ) (ζ : ℂ →L[ℝ] ℝ) =
          ‖ζ‖ ^ (2 : ℕ) := by
    intro ζ
    rw [← hinner_eq ζ]
    exact real_inner_self_eq_norm_sq ζ
  have hleft :
      g.gradientInner x (ξ + η) (ξ + η) =
        ‖ξV + ηV‖ ^ (2 : ℕ) := by
    simpa [ξV, ηV] using hnorm_sq (ξV + ηV)
  have hξ :
      g.gradientInner x ξ ξ = ‖ξV‖ ^ (2 : ℕ) := by
    simpa [ξV] using hnorm_sq ξV
  have hη :
      g.gradientInner x η η = ‖ηV‖ ^ (2 : ℕ) := by
    simpa [ηV] using hnorm_sq ηV
  rw [hleft, hξ, hη]
  have hnorm_add : ‖ξV + ηV‖ ≤ ‖ξV‖ + ‖ηV‖ := norm_add_le ξV ηV
  have hnonneg : 0 ≤ ‖ξV‖ + ‖ηV‖ :=
    add_nonneg (norm_nonneg ξV) (norm_nonneg ηV)
  have hsquare :
      ‖ξV + ηV‖ ^ (2 : ℕ) ≤ (‖ξV‖ + ‖ηV‖) ^ (2 : ℕ) :=
    sq_le_sq.mpr (by
      rw [abs_of_nonneg (norm_nonneg (ξV + ηV)),
        abs_of_nonneg hnonneg]
      exact hnorm_add)
  have htwice :
      (‖ξV‖ + ‖ηV‖) ^ (2 : ℕ) ≤
        2 * ‖ξV‖ ^ (2 : ℕ) + 2 * ‖ηV‖ ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (‖ξV‖ - ‖ηV‖)]
  exact hsquare.trans htwice

/--
%%handwave
name:
  Squared \(L^2\)-seminorm equals the integral of the square
statement:
  If \(u:X\to\mathbb R\) belongs to \(L^2(\mu|_K)\), then
  \[
    \lVert u\rVert_{L^2(\mu|_K)}^2=\int_K u(x)^2\,d\mu(x).
  \]
proof:
  Use the integral formula for the finite \(L^2\)-norm, identify the exponent
  \(1/2\) with the square root, and square it using nonnegativity of the integral.
-/
private theorem eLpNorm_two_toReal_sq_eq_integral_norm_sq_restrict
    {X : Type} [MeasurableSpace X] {μ : Measure X} {K : Set X}
    {u : X → ℝ}
    (hu : MemLp u 2 (μ.restrict K)) :
    (eLpNorm u 2 (μ.restrict K)).toReal ^ (2 : ℕ) =
      ∫ x in K, u x ^ (2 : ℕ) ∂μ := by
  let μK : Measure X := μ.restrict K
  have h_int_norm : Integrable (fun x : X ↦ ‖u x‖ ^ (2 : ℕ)) μK :=
    (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).1 hu
  have h_int_sq : Integrable (fun x : X ↦ u x ^ (2 : ℕ)) μK := by
    refine h_int_norm.congr ?_
    filter_upwards [] with x
    simp [Real.norm_eq_abs, sq_abs]
  have h_nonneg :
      0 ≤ ∫ x, u x ^ (2 : ℕ) ∂μK :=
    integral_nonneg fun x ↦ sq_nonneg (u x)
  have h_norm_sq_eq :
      ∫ x, ‖u x‖ ^ (2 : ℕ) ∂μK =
        ∫ x, u x ^ (2 : ℕ) ∂μK :=
    integral_congr_ae (by
      filter_upwards [] with x
      simp [Real.norm_eq_abs, sq_abs])
  have hnorm :
      (eLpNorm u 2 μK).toReal =
        Real.sqrt (∫ x, u x ^ (2 : ℕ) ∂μK) := by
    have hlp :=
      lpNorm_eq_integral_norm_rpow_toReal
        (μ := μK) (f := u) (p := (2 : ℝ≥0∞))
        (by norm_num) (by norm_num) hu.aestronglyMeasurable
    have htoReal := toReal_eLpNorm
      (μ := μK) (f := u) (p := (2 : ℝ≥0∞)) hu.aestronglyMeasurable
    calc
      (eLpNorm u 2 μK).toReal = lpNorm u 2 μK := htoReal
      _ = (∫ x, ‖u x‖ ^ (2 : ℝ≥0∞).toReal ∂μK) ^
            ((2 : ℝ≥0∞).toReal)⁻¹ := hlp
      _ = (∫ x, ‖u x‖ ^ (2 : ℕ) ∂μK) ^ (1 / (2 : ℝ)) := by
            norm_num
      _ = (∫ x, u x ^ (2 : ℕ) ∂μK) ^ (1 / (2 : ℝ)) := by
            rw [h_norm_sq_eq]
      _ = Real.sqrt (∫ x, u x ^ (2 : ℕ) ∂μK) := by
            rw [Real.sqrt_eq_rpow]
  calc
    (eLpNorm u 2 (μ.restrict K)).toReal ^ (2 : ℕ)
        = (Real.sqrt (∫ x, u x ^ (2 : ℕ) ∂μK)) ^ (2 : ℕ) := by
          rw [hnorm]
    _ = ∫ x, u x ^ (2 : ℕ) ∂μK := by
          rw [Real.sq_sqrt h_nonneg]
    _ = ∫ x in K, u x ^ (2 : ℕ) ∂μ := rfl

private noncomputable def smoothCompactProduct
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X]
    (M F : SmoothCompactlySupportedGlobalSurfaceFunction X) :
    SmoothCompactlySupportedGlobalSurfaceFunction X :=
  SmoothCompactlySupportedGlobalSurfaceFunction.mul_of_left_support_subset_open
    (V := Set.univ)
    isOpen_univ
    M.smooth
    (by simpa using F.smooth)
    F.compact_support
    (by intro x _hx; exact Set.mem_univ x)

/--
%%handwave
name:
  Product rule for compactly supported surface functions
statement:
  For smooth compactly supported functions \(M,F\) on a surface,
  \[
    \nabla(MF)=M\,\nabla F+F\,\nabla M.
  \]
proof:
  Express the stored gradients in the chart at \(x\), apply the ordinary
  Fréchet product rule, and identify the self-transition tangent map with the identity.
-/
private theorem smoothCompactProduct_gradient_eq
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X]
    (M F : SmoothCompactlySupportedGlobalSurfaceFunction X)
    (x : X) :
    (smoothCompactProduct M F).gradient x =
      M.toFun x • F.gradient x + F.toFun x • M.gradient x := by
  ext v
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ x
  have he : e ∈ atlas ℂ X := by
    simp [e]
  have hxsource : x ∈ e.source := by
    simp [e]
  have hz : e x ∈ e.target := e.map_source hxsource
  have hsymm : e.symm (e x) = x := e.left_inv hxsource
  have hmap :
      surfaceChartTangentMap e (e x) =
        ContinuousLinearMap.id ℝ ℂ := by
    simpa [e] using surfaceChartTangentMap_chartAt_self (X := X) x
  have hMdiff :
      DifferentiableAt ℝ (fun w : ℂ ↦ M.toFun (e.symm w)) (e x) :=
    surfaceFunctionChartRepresentative_differentiableAt
      e he M.toFun M.smooth (e x) hz
  have hFdiff :
      DifferentiableAt ℝ (fun w : ℂ ↦ F.toFun (e.symm w)) (e x) :=
    surfaceFunctionChartRepresentative_differentiableAt
      e he F.toFun F.smooth (e x) hz
  have hprod_grad :
      (smoothCompactProduct M F).gradient x v =
        fderiv ℝ
          (fun w : ℂ ↦
            M.toFun (e.symm w) * F.toFun (e.symm w)) (e x) v := by
    have h :=
      (smoothCompactProduct M F).gradient_eq e he (e x) hz v
    simpa [smoothCompactProduct, hsymm, hmap] using h
  have hM_grad :
      M.gradient x v =
        fderiv ℝ (fun w : ℂ ↦ M.toFun (e.symm w)) (e x) v := by
    have h := M.gradient_eq e he (e x) hz v
    simpa [hsymm, hmap] using h
  have hF_grad :
      F.gradient x v =
        fderiv ℝ (fun w : ℂ ↦ F.toFun (e.symm w)) (e x) v := by
    have h := F.gradient_eq e he (e x) hz v
    simpa [hsymm, hmap] using h
  calc
    (smoothCompactProduct M F).gradient x v =
        fderiv ℝ
          (fun w : ℂ ↦
            M.toFun (e.symm w) * F.toFun (e.symm w)) (e x) v :=
      hprod_grad
    _ =
        fderiv ℝ (fun w : ℂ ↦ M.toFun (e.symm w)) (e x) v *
          F.toFun x +
        M.toFun x *
          fderiv ℝ (fun w : ℂ ↦ F.toFun (e.symm w)) (e x) v := by
      rw [fderiv_fun_mul hMdiff hFdiff]
      simp [hsymm]
      ring
    _ = (M.toFun x • F.gradient x + F.toFun x • M.gradient x) v := by
      rw [← hM_grad, ← hF_grad]
      simp [mul_comm, add_comm]

/--
%%handwave
name:
  Gradient of a multiplied difference
statement:
  For smooth compactly supported \(M,F,H\),
  \[
    \nabla\!\bigl(M(F-H)\bigr)=M(\nabla F-\nabla H)+(F-H)\nabla M.
  \]
proof:
  Apply the product rule to \(MF\) and \(MH\), subtract, and collect terms.
-/
private theorem smoothCompactProduct_difference_gradient_eq
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X]
    (M F H : SmoothCompactlySupportedGlobalSurfaceFunction X)
    (x : X) :
    (SmoothCompactlySupportedGlobalSurfaceFunction.add
        (smoothCompactProduct M F)
        (SmoothCompactlySupportedGlobalSurfaceFunction.smul (-1 : ℝ)
          (smoothCompactProduct M H))).gradient x =
      M.toFun x • (F.gradient x - H.gradient x) +
        (F.toFun x - H.toFun x) • M.gradient x := by
  ext v
  have hMF := congrArg (fun L : ℂ →L[ℝ] ℝ ↦ L v)
    (smoothCompactProduct_gradient_eq M F x)
  have hMH := congrArg (fun L : ℂ →L[ℝ] ℝ ↦ L v)
    (smoothCompactProduct_gradient_eq M H x)
  simp [SmoothCompactlySupportedGlobalSurfaceFunction.add,
    SmoothCompactlySupportedGlobalSurfaceFunction.smul, hMF, hMH,
    sub_eq_add_neg]
  ring

/--
%%handwave
name:
  Arithmetic estimate for small multiplier energy
statement:
  Let \(A,B\ge0\), \(C=A+B+1\), \(0\le r\le1\), and
  \(r\le\varepsilon^2/(4C)\).  If
  \(I\le A I_H+B I_{L^2}\), \(I_H<r^2\), and \(I_{L^2}\le r^2\), then
  \(I<\varepsilon^2\).
proof:
  Bound \(I\) by \((A+B)r^2\le Cr\), then by
  \(\varepsilon^2/4<\varepsilon^2\).
-/
private theorem smoothCompactMultiplier_energy_small_arithmetic
    {A B C ε r IH IL2 Iprod : ℝ}
    (hA_nonneg : 0 ≤ A) (hB_nonneg : 0 ≤ B)
    (hC_def : C = A + B + 1) (hC_pos : 0 < C) (hε : 0 < ε)
    (hr_nonneg : 0 ≤ r) (hr_le_one : r ≤ 1)
    (hr_le_eps : r ≤ ε ^ (2 : ℕ) / (4 * C))
    (hIprod_le : Iprod ≤ A * IH + B * IL2)
    (hIH_lt : IH < r ^ (2 : ℕ)) (hIL2_le : IL2 ≤ r ^ (2 : ℕ)) :
    Iprod < ε ^ (2 : ℕ) := by
  have hr_sq_le : r ^ (2 : ℕ) ≤ r := by
    nlinarith
  have hεsq_pos : 0 < ε ^ (2 : ℕ) := sq_pos_of_pos hε
  have hsum1 :
      A * IH + B * IL2 ≤ A * r ^ (2 : ℕ) + B * r ^ (2 : ℕ) := by
    nlinarith [le_of_lt hIH_lt, hIL2_le, hA_nonneg, hB_nonneg]
  have hsum2 :
      A * r ^ (2 : ℕ) + B * r ^ (2 : ℕ) ≤ (A + B) * r := by
    have hAB_nonneg : 0 ≤ A + B := add_nonneg hA_nonneg hB_nonneg
    calc
      A * r ^ (2 : ℕ) + B * r ^ (2 : ℕ) =
          (A + B) * r ^ (2 : ℕ) := by ring
      _ ≤ (A + B) * r :=
          mul_le_mul_of_nonneg_left hr_sq_le hAB_nonneg
  have hsum3 : (A + B) * r ≤ C * r := by
    have hle : A + B ≤ C := by
      rw [hC_def]
      exact le_add_of_nonneg_right zero_le_one
    exact mul_le_mul_of_nonneg_right hle hr_nonneg
  have hsum4 : C * r ≤ ε ^ (2 : ℕ) / 4 := by
    calc
      C * r ≤ C * (ε ^ (2 : ℕ) / (4 * C)) :=
        mul_le_mul_of_nonneg_left hr_le_eps (le_of_lt hC_pos)
      _ = ε ^ (2 : ℕ) / 4 := by
        field_simp [ne_of_gt hC_pos]
  have hquarter : ε ^ (2 : ℕ) / 4 < ε ^ (2 : ℕ) := by
    nlinarith
  calc
    Iprod ≤ A * IH + B * IL2 := hIprod_le
    _ ≤ A * r ^ (2 : ℕ) + B * r ^ (2 : ℕ) := hsum1
    _ ≤ (A + B) * r := hsum2
    _ ≤ C * r := hsum3
    _ ≤ ε ^ (2 : ℕ) / 4 := hsum4
    _ < ε ^ (2 : ℕ) := hquarter

/--
%%handwave
name:
  Quantitative smooth multiplier estimate for pure differentials
statement:
  For a fixed compactly supported smooth multiplier \(M\), making both the
  pure Dirichlet norm of \(F_n-F_m\) and the \(L^2\)-norm of
  \(F_n-F_m\) on the support of \(M\) sufficiently small makes the pure
  Dirichlet norm of \(M F_n-M F_m\) arbitrarily small.
proof:
  Expand \(d(M(F_n-F_m))\) by the product rule.  The term
  \(M\,d(F_n-F_m)\) is controlled by the supremum of \(M\), and the term
  \((F_n-F_m)\,dM\) is controlled by the supremum of \(dM\) on the compact
  support of \(M\).
-/
theorem smoothCompactMultiplier_core_norm_small_of_core_norm_small_and_localL2_small
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [SecondCountableTopology X] [ComplexOneManifold X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (M : SmoothCompactlySupportedGlobalSurfaceFunction X)
    (F : ℕ → SmoothCompactlySupportedGlobalSurfaceFunction X)
    (hF : ∀ n : ℕ,
      SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
        (SurfaceDifferentialField.ofCoordinateField (F n).gradient)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧
        ∃ η : ℝ≥0∞, 0 < η ∧
          ∀ n m : ℕ,
            ‖greenSmoothCoreElement (g := g) (F n) (hF n) -
              greenSmoothCoreElement (g := g) (F m) (hF m)‖ < δ →
            eLpNorm
              (fun x : X ↦ (F n).toFun x - (F m).toFun x)
              2 (g.volume.restrict (tsupport M.toFun)) ≤ η →
            ‖greenSmoothCoreElement (g := g)
                (smoothCompactProduct M (F n))
                ((smoothCompactProduct M (F n)).differential_memHilbertSchmidtL2) -
              greenSmoothCoreElement (g := g)
                (smoothCompactProduct M (F m))
                ((smoothCompactProduct M (F m)).differential_memHilbertSchmidtL2)‖ <
              ε := by
  classical
  have hM_cont : Continuous M.toFun :=
    isSmoothOnSurface_univ_continuous M.smooth
  rcases M.compact_support.exists_bound_of_continuousOn
      hM_cont.continuousOn with
    ⟨CM₀, hCM₀⟩
  let CM : ℝ := max 0 CM₀
  have hCM_nonneg : 0 ≤ CM := le_max_left 0 CM₀
  have hM_bound : ∀ x : X, ‖M.toFun x‖ ≤ CM := by
    intro x
    by_cases hx : x ∈ tsupport M.toFun
    · exact (hCM₀ x hx).trans (le_max_right 0 CM₀)
    · have hz : M.toFun x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [hz, CM, hCM_nonneg]
  rcases
      SmoothCompactlySupportedGlobalSurfaceFunction.gradientInner_self_bound_on_tsupport
        (g := g) M with
    ⟨CD, hCD_nonneg, hCD_bound_support⟩
  have hDM_bound : ∀ x : X,
      g.gradientInner x (M.gradient x) (M.gradient x) ≤ CD := by
    intro x
    by_cases hx : x ∈ tsupport M.toFun
    · exact hCD_bound_support x hx
    · have hgrad_zero :
        M.gradient x = 0 :=
          M.gradient_eq_zero_of_notMem_tsupport hx
      have hzero :
          g.gradientInner x (0 : ℂ →L[ℝ] ℝ) 0 = 0 := by
        simpa using
          BackgroundSurfaceMetricOnSurface.gradientInner_smul_smul
            g x (0 : ℂ →L[ℝ] ℝ) (0 : ℝ)
      simpa [hgrad_zero, hzero] using hCD_nonneg
  let A : ℝ := 2 * CM ^ (2 : ℕ)
  let B : ℝ := 2 * CD
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  let C : ℝ := A + B + 1
  have hC_pos : 0 < C := by
    dsimp [C]
    nlinarith
  intro ε hε
  let r : ℝ := min 1 (ε ^ (2 : ℕ) / (4 * C))
  have hr_pos : 0 < r := by
    dsimp [r]
    refine lt_min (by norm_num) ?_
    have hεsq_pos : 0 < ε ^ (2 : ℕ) := sq_pos_of_pos hε
    positivity
  have hr_nonneg : 0 ≤ r := le_of_lt hr_pos
  have hr_le_one : r ≤ 1 := by
    dsimp [r]
    exact min_le_left 1 (ε ^ (2 : ℕ) / (4 * C))
  have hr_le_eps : r ≤ ε ^ (2 : ℕ) / (4 * C) := by
    dsimp [r]
    exact min_le_right 1 (ε ^ (2 : ℕ) / (4 * C))
  refine ⟨r, hr_pos, ENNReal.ofReal r, ENNReal.ofReal_pos.mpr hr_pos, ?_⟩
  intro n m hcore hlocal
  let Pn : SmoothCompactlySupportedGlobalSurfaceFunction X :=
    smoothCompactProduct M (F n)
  let Pm : SmoothCompactlySupportedGlobalSurfaceFunction X :=
    smoothCompactProduct M (F m)
  let negPm : SmoothCompactlySupportedGlobalSurfaceFunction X :=
    SmoothCompactlySupportedGlobalSurfaceFunction.smul (-1 : ℝ) Pm
  let PD : SmoothCompactlySupportedGlobalSurfaceFunction X :=
    SmoothCompactlySupportedGlobalSurfaceFunction.add Pn negPm
  let hPn : SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
      (SurfaceDifferentialField.ofCoordinateField Pn.gradient) :=
    Pn.differential_memHilbertSchmidtL2
  let hPm : SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
      (SurfaceDifferentialField.ofCoordinateField Pm.gradient) :=
    Pm.differential_memHilbertSchmidtL2
  let hNegPm : SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
      (SurfaceDifferentialField.ofCoordinateField negPm.gradient) :=
    negPm.differential_memHilbertSchmidtL2
  let hPD : SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
      (SurfaceDifferentialField.ofCoordinateField PD.gradient) :=
    PD.differential_memHilbertSchmidtL2
  have hPD_class :
      greenSmoothDifferentialClass (g := g) PD hPD =
        greenSmoothDifferentialClass (g := g) Pn hPn -
          greenSmoothDifferentialClass (g := g) Pm hPm := by
    calc
      greenSmoothDifferentialClass (g := g) PD hPD =
          greenSmoothDifferentialClass (g := g) Pn hPn +
            greenSmoothDifferentialClass (g := g) negPm hNegPm :=
        greenSmoothDifferentialClass_add Pn negPm hPn hNegPm hPD
      _ = greenSmoothDifferentialClass (g := g) Pn hPn +
            (-1 : ℝ) • greenSmoothDifferentialClass (g := g) Pm hPm := by
        rw [greenSmoothDifferentialClass_smul (-1 : ℝ) Pm hPm hNegPm]
      _ = greenSmoothDifferentialClass (g := g) Pn hPn -
            greenSmoothDifferentialClass (g := g) Pm hPm := by
        simp [sub_eq_add_neg]
  let negFm : SmoothCompactlySupportedGlobalSurfaceFunction X :=
    SmoothCompactlySupportedGlobalSurfaceFunction.smul (-1 : ℝ) (F m)
  let H : SmoothCompactlySupportedGlobalSurfaceFunction X :=
    SmoothCompactlySupportedGlobalSurfaceFunction.add (F n) negFm
  let hNegFm : SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
      (SurfaceDifferentialField.ofCoordinateField negFm.gradient) :=
    negFm.differential_memHilbertSchmidtL2
  let hH : SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
      (SurfaceDifferentialField.ofCoordinateField H.gradient) :=
    H.differential_memHilbertSchmidtL2
  have hH_class :
      greenSmoothDifferentialClass (g := g) H hH =
        greenSmoothDifferentialClass (g := g) (F n) (hF n) -
          greenSmoothDifferentialClass (g := g) (F m) (hF m) := by
    calc
      greenSmoothDifferentialClass (g := g) H hH =
          greenSmoothDifferentialClass (g := g) (F n) (hF n) +
            greenSmoothDifferentialClass (g := g) negFm hNegFm :=
        greenSmoothDifferentialClass_add (F n) negFm (hF n) hNegFm hH
      _ = greenSmoothDifferentialClass (g := g) (F n) (hF n) +
            (-1 : ℝ) • greenSmoothDifferentialClass (g := g) (F m) (hF m) := by
        rw [greenSmoothDifferentialClass_smul (-1 : ℝ) (F m) (hF m) hNegFm]
      _ = greenSmoothDifferentialClass (g := g) (F n) (hF n) -
            greenSmoothDifferentialClass (g := g) (F m) (hF m) := by
        simp [sub_eq_add_neg]
  have hH_norm_lt :
      ‖greenSmoothDifferentialClass (g := g) H hH‖ < r := by
    rw [hH_class]
    simpa [greenSmoothCoreElement] using hcore
  let IH : ℝ :=
    ∫ x, g.gradientInner x (H.gradient x) (H.gradient x) ∂g.volume
  have hIH_nonneg : 0 ≤ IH := by
    dsimp [IH]
    exact integral_nonneg fun x ↦
      BackgroundSurfaceMetricOnSurface.gradientInner_nonneg g x (H.gradient x)
  have hIH_eq_normSq :
      IH = ‖greenSmoothDifferentialClass (g := g) H hH‖ ^ (2 : ℕ) := by
    have hnorm :
        ‖greenSmoothDifferentialClass (g := g) H hH‖ = Real.sqrt IH := by
      simpa [IH] using greenSmoothDifferentialClass_norm_eq_sqrt_dirichlet H hH
    have hs :
        ‖greenSmoothDifferentialClass (g := g) H hH‖ ^ (2 : ℕ) = IH := by
      rw [hnorm, Real.sq_sqrt hIH_nonneg]
    exact hs.symm
  have hIH_lt : IH < r ^ (2 : ℕ) := by
    rw [hIH_eq_normSq]
    nlinarith [hH_norm_lt,
      norm_nonneg (greenSmoothDifferentialClass (g := g) H hH), hr_pos]
  let K : Set X := tsupport M.toFun
  have hK_compact : IsCompact K := by
    simpa [K] using M.compact_support
  have hK_meas : MeasurableSet K := hK_compact.measurableSet
  let u : X → ℝ := fun x : X ↦ (F n).toFun x - (F m).toFun x
  have hu_mem : MemLp u 2 (g.volume.restrict K) := by
    have hn : MemLp (F n).toFun 2 (g.volume.restrict K) :=
      (F n).memLp_restrict_compact (g := g) hK_compact
    have hm : MemLp (F m).toFun 2 (g.volume.restrict K) :=
      (F m).memLp_restrict_compact (g := g) hK_compact
    exact hn.sub hm
  have hlocal_toReal :
      (eLpNorm u 2 (g.volume.restrict K)).toReal ≤ r := by
    have hmono :
        (eLpNorm u 2 (g.volume.restrict K)).toReal ≤
          (ENNReal.ofReal r).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top (by simpa [u, K] using hlocal)
    simpa [ENNReal.toReal_ofReal hr_nonneg] using hmono
  let IL2 : ℝ := ∫ x in K, u x ^ (2 : ℕ) ∂g.volume
  have hIL2_eq :
      IL2 = (eLpNorm u 2 (g.volume.restrict K)).toReal ^ (2 : ℕ) := by
    simpa [IL2] using
      (eLpNorm_two_toReal_sq_eq_integral_norm_sq_restrict
        (μ := g.volume) (K := K) hu_mem).symm
  have hIL2_le : IL2 ≤ r ^ (2 : ℕ) := by
    rw [hIL2_eq]
    have hto_nonneg :
        0 ≤ (eLpNorm u 2 (g.volume.restrict K)).toReal :=
      ENNReal.toReal_nonneg
    nlinarith [hlocal_toReal, hto_nonneg, hr_nonneg]
  let Iprod : ℝ :=
    ∫ x, g.gradientInner x (PD.gradient x) (PD.gradient x) ∂g.volume
  have hPD_int :
      Integrable
        (fun x ↦ g.gradientInner x (PD.gradient x) (PD.gradient x))
        g.volume := by
    have hnorm :
        Integrable
          (fun x ↦
            (manifoldDifferentialHilbertBundleGeometry
              (I := SurfaceRealModel) (X := X) (E := ℝ)
              g.metric.toManifoldMetric).fiberNormSq x
              ((SurfaceDifferentialField.ofCoordinateField PD.gradient) x))
          g.volume :=
      hPD.integrable_normSq
    refine hnorm.congr ?_
    filter_upwards [] with x
    simpa using
      (surface_coordinate_cotangent_fiberNormSq_eq_gradientInner
        g x (PD.gradient x))
  have hH_int :
      Integrable
        (fun x ↦ g.gradientInner x (H.gradient x) (H.gradient x))
        g.volume := by
    have hnorm :
        Integrable
          (fun x ↦
            (manifoldDifferentialHilbertBundleGeometry
              (I := SurfaceRealModel) (X := X) (E := ℝ)
              g.metric.toManifoldMetric).fiberNormSq x
              ((SurfaceDifferentialField.ofCoordinateField H.gradient) x))
          g.volume :=
      hH.integrable_normSq
    refine hnorm.congr ?_
    filter_upwards [] with x
    simpa using
      (surface_coordinate_cotangent_fiberNormSq_eq_gradientInner
        g x (H.gradient x))
  have hu_sq_int_restrict :
      Integrable (fun x : X ↦ u x ^ (2 : ℕ)) (g.volume.restrict K) := by
    have hnorm_int :
        Integrable (fun x : X ↦ ‖u x‖ ^ (2 : ℕ)) (g.volume.restrict K) :=
      (memLp_two_iff_integrable_sq_norm hu_mem.aestronglyMeasurable).1 hu_mem
    refine hnorm_int.congr ?_
    filter_upwards [] with x
    simp [Real.norm_eq_abs, sq_abs]
  have hu_indicator_int :
      Integrable (K.indicator fun x : X ↦ u x ^ (2 : ℕ)) g.volume := by
    exact (integrable_indicator_iff hK_meas).2 hu_sq_int_restrict
  have hpoint :
      ∀ x : X,
        g.gradientInner x (PD.gradient x) (PD.gradient x) ≤
          A * g.gradientInner x (H.gradient x) (H.gradient x) +
            B * K.indicator (fun y : X ↦ u y ^ (2 : ℕ)) x := by
    intro x
    let ξ : ℂ →L[ℝ] ℝ :=
      M.toFun x • ((F n).gradient x - (F m).gradient x)
    let η : ℂ →L[ℝ] ℝ :=
      u x • M.gradient x
    have hPD_grad : PD.gradient x = ξ + η := by
      simpa [PD, Pn, Pm, negPm, ξ, η, u] using
        smoothCompactProduct_difference_gradient_eq M (F n) (F m) x
    have hH_grad : H.gradient x = (F n).gradient x - (F m).gradient x := by
      ext v
      simp [H, negFm, SmoothCompactlySupportedGlobalSurfaceFunction.add,
        SmoothCompactlySupportedGlobalSurfaceFunction.smul, sub_eq_add_neg]
    have hfirst :
        2 * g.gradientInner x ξ ξ ≤
          A * g.gradientInner x (H.gradient x) (H.gradient x) := by
      have hM_abs : |M.toFun x| ≤ CM := by
        simpa [Real.norm_eq_abs] using hM_bound x
      have hM_sq : (M.toFun x) ^ (2 : ℕ) ≤ CM ^ (2 : ℕ) :=
        sq_le_sq.mpr (by
          simpa [abs_of_nonneg hCM_nonneg] using hM_abs)
      have hG_nonneg :
          0 ≤ g.gradientInner x (H.gradient x) (H.gradient x) :=
        BackgroundSurfaceMetricOnSurface.gradientInner_nonneg g x (H.gradient x)
      calc
        2 * g.gradientInner x ξ ξ =
            2 * ((M.toFun x) ^ (2 : ℕ) *
              g.gradientInner x (H.gradient x) (H.gradient x)) := by
              rw [hH_grad]
              simp [ξ]
              rw [BackgroundSurfaceMetricOnSurface.gradientInner_smul_smul]
        _ ≤ 2 * (CM ^ (2 : ℕ) *
              g.gradientInner x (H.gradient x) (H.gradient x)) := by
              nlinarith
        _ = A * g.gradientInner x (H.gradient x) (H.gradient x) := by
              ring
    have hsecond :
        2 * g.gradientInner x η η ≤
          B * K.indicator (fun y : X ↦ u y ^ (2 : ℕ)) x := by
      by_cases hxK : x ∈ K
      · have hDM_nonneg :
            0 ≤ g.gradientInner x (M.gradient x) (M.gradient x) :=
          BackgroundSurfaceMetricOnSurface.gradientInner_nonneg g x (M.gradient x)
        calc
          2 * g.gradientInner x η η =
              2 * (u x ^ (2 : ℕ) *
                g.gradientInner x (M.gradient x) (M.gradient x)) := by
                simp [η]
                rw [BackgroundSurfaceMetricOnSurface.gradientInner_smul_smul]
          _ ≤ 2 * (u x ^ (2 : ℕ) * CD) := by
                nlinarith [hDM_bound x, sq_nonneg (u x), hDM_nonneg]
          _ = B * K.indicator (fun y : X ↦ u y ^ (2 : ℕ)) x := by
                simp [B, hxK]
                ring
      · have hgrad_zero : M.gradient x = 0 := by
          exact M.gradient_eq_zero_of_notMem_tsupport (by simpa [K] using hxK)
        have hzero :
            g.gradientInner x (0 : ℂ →L[ℝ] ℝ) 0 = 0 := by
          simpa using
            BackgroundSurfaceMetricOnSurface.gradientInner_smul_smul
              g x (0 : ℂ →L[ℝ] ℝ) (0 : ℝ)
        simp [η, hgrad_zero, hzero, hxK]
    calc
      g.gradientInner x (PD.gradient x) (PD.gradient x) =
          g.gradientInner x (ξ + η) (ξ + η) := by
            rw [hPD_grad]
      _ ≤ 2 * g.gradientInner x ξ ξ +
          2 * g.gradientInner x η η :=
            BackgroundSurfaceMetricOnSurface.gradientInner_add_le_two
              g x ξ η
      _ ≤ A * g.gradientInner x (H.gradient x) (H.gradient x) +
          B * K.indicator (fun y : X ↦ u y ^ (2 : ℕ)) x :=
            add_le_add hfirst hsecond
  have hR_int :
      Integrable
        (fun x : X ↦
          A * g.gradientInner x (H.gradient x) (H.gradient x) +
            B * K.indicator (fun y : X ↦ u y ^ (2 : ℕ)) x)
        g.volume :=
    (hH_int.const_mul A).add (hu_indicator_int.const_mul B)
  have hIprod_le : Iprod ≤ A * IH + B * IL2 := by
    dsimp [Iprod, IH, IL2]
    calc
      ∫ x, g.gradientInner x (PD.gradient x) (PD.gradient x) ∂g.volume
          ≤ ∫ x, (A * g.gradientInner x (H.gradient x) (H.gradient x) +
              B * K.indicator (fun y : X ↦ u y ^ (2 : ℕ)) x) ∂g.volume :=
            integral_mono hPD_int hR_int hpoint
      _ =
          A * ∫ x, g.gradientInner x (H.gradient x) (H.gradient x) ∂g.volume +
            B * ∫ x, K.indicator (fun y : X ↦ u y ^ (2 : ℕ)) x ∂g.volume := by
            rw [integral_add (hH_int.const_mul A) (hu_indicator_int.const_mul B),
              integral_const_mul, integral_const_mul]
      _ =
          A * ∫ x, g.gradientInner x (H.gradient x) (H.gradient x) ∂g.volume +
            B * ∫ x in K, u x ^ (2 : ℕ) ∂g.volume := by
            rw [integral_indicator hK_meas]
  have hIprod_nonneg : 0 ≤ Iprod := by
    dsimp [Iprod]
    exact integral_nonneg fun x ↦
      BackgroundSurfaceMetricOnSurface.gradientInner_nonneg g x (PD.gradient x)
  have hIprod_lt : Iprod < ε ^ (2 : ℕ) := by
    exact
      smoothCompactMultiplier_energy_small_arithmetic
        hA_nonneg hB_nonneg (by rfl) hC_pos hε hr_nonneg
        hr_le_one hr_le_eps hIprod_le hIH_lt hIL2_le
  have hPD_norm :
      ‖greenSmoothDifferentialClass (g := g) PD hPD‖ = Real.sqrt Iprod := by
    simpa [Iprod] using greenSmoothDifferentialClass_norm_eq_sqrt_dirichlet PD hPD
  have hPD_norm_lt :
      ‖greenSmoothDifferentialClass (g := g) PD hPD‖ < ε := by
    rw [hPD_norm]
    calc
      Real.sqrt Iprod < Real.sqrt (ε ^ (2 : ℕ)) :=
        Real.sqrt_lt_sqrt hIprod_nonneg hIprod_lt
      _ = ε := by
        rw [Real.sqrt_sq_eq_abs, abs_of_pos hε]
  change
    ‖greenSmoothDifferentialClass (g := g) Pn hPn -
      greenSmoothDifferentialClass (g := g) Pm hPm‖ < ε
  rw [← hPD_class]
  exact hPD_norm_lt

/--
%%handwave
name:
  Smooth multiplier product-rule estimate for pure-Cauchy representatives
statement:
  Let \(F_n\) be compactly supported smooth functions which are Cauchy in
  pure Dirichlet norm and Cauchy in \(L^2\) on the compact support of a fixed
  compactly supported smooth multiplier \(M\).  Then the products \(MF_n\)
  are Cauchy in pure Dirichlet norm.
proof:
  Use the product rule
  \(d(M(F_n-F_m))=M\,d(F_n-F_m)+(F_n-F_m)\,dM\).  The first term is controlled
  by the pure Dirichlet Cauchy property of \(F_n\); the second is controlled
  on the compact support of \(dM\) by compact-local \(L^2\)-Cauchy convergence
  of the primitives.
-/
theorem smoothCompactMultiplier_core_norm_cauchy
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [SecondCountableTopology X] [ComplexOneManifold X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (M : SmoothCompactlySupportedGlobalSurfaceFunction X)
    (F : ℕ → SmoothCompactlySupportedGlobalSurfaceFunction X)
    (hF : ∀ n : ℕ,
      SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
        (SurfaceDifferentialField.ofCoordinateField (F n).gradient))
    (hF_core_cauchy :
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
          ‖greenSmoothCoreElement (g := g) (F n) (hF n) -
            greenSmoothCoreElement (g := g) (F m) (hF m)‖ < ε)
    (hF_local_cauchy :
      ∀ ε : ℝ≥0∞, 0 < ε →
        ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
          eLpNorm
            (fun x : X ↦ (F n).toFun x - (F m).toFun x)
            2 (g.volume.restrict (tsupport M.toFun)) ≤ ε) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
        ‖greenSmoothCoreElement (g := g)
            (smoothCompactProduct M (F n))
            ((smoothCompactProduct M (F n)).differential_memHilbertSchmidtL2) -
          greenSmoothCoreElement (g := g)
            (smoothCompactProduct M (F m))
            ((smoothCompactProduct M (F m)).differential_memHilbertSchmidtL2)‖ <
          ε := by
  intro ε hε
  rcases
      smoothCompactMultiplier_core_norm_small_of_core_norm_small_and_localL2_small
        (g := g) M F hF ε hε with
    ⟨δ, hδ_pos, η, hη_pos, hsmall⟩
  rcases hF_core_cauchy δ hδ_pos with ⟨N₁, hN₁⟩
  rcases hF_local_cauchy η hη_pos with ⟨N₂, hN₂⟩
  refine ⟨max N₁ N₂, ?_⟩
  intro n m hn hm
  have hn₁ : N₁ ≤ n := le_trans (le_max_left N₁ N₂) hn
  have hm₁ : N₁ ≤ m := le_trans (le_max_left N₁ N₂) hm
  have hn₂ : N₂ ≤ n := le_trans (le_max_right N₁ N₂) hn
  have hm₂ : N₂ ≤ m := le_trans (le_max_right N₁ N₂) hm
  exact hsmall n m (hN₁ n m hn₁ hm₁) (hN₂ n m hn₂ hm₂)

/--
%%handwave
name:
  Smooth multipliers preserve pure-Cauchy representative sequences
statement:
  Let \(F_n\) be a compactly supported smooth primitive sequence converging in
  the pure homogeneous Dirichlet completion and compact-locally in \(L^2\).
  For a fixed compactly supported smooth multiplier \(M\), the products
  \(MF_n\) form a Cauchy sequence in the pure homogeneous Dirichlet
  completion.
proof:
  Completion convergence makes the differentials \(dF_n\) Cauchy in the pure
  norm.  Compact-local \(L^2\)-convergence gives \(F_n\) Cauchy in \(L^2\) on
  the compact support of the multiplier.  Apply the smooth product-rule
  estimate and then use the isometric inclusion of the smooth core into its
  completion.
-/
theorem smoothCompactMultiplier_coreSequence_cauchy
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [SecondCountableTopology X] [ComplexOneManifold X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (M : SmoothCompactlySupportedGlobalSurfaceFunction X)
    {u : GreenSobolevH10SmoothCompactSupport g} {f : X → ℝ}
    (F : ℕ → SmoothCompactlySupportedGlobalSurfaceFunction X)
    (hF : ∀ n : ℕ,
      SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
        (SurfaceDifferentialField.ofCoordinateField (F n).gradient))
    (hF_tendsto :
      Filter.Tendsto
        (fun n : ℕ ↦
          (greenSobolevH10SmoothCompactSupportCore g).toCompletion
            (greenSmoothCoreElement (g := g) (F n) (hF n)))
        Filter.atTop (𝓝 u))
    (hF_local :
      ∀ K : Set X, IsCompact K →
        TendstoInLocalL2OnSurface g.volume K
          (fun n : ℕ ↦ (F n).toFun)
          f)
    (hf_meas :
      ∀ K : Set X, IsCompact K →
        AEStronglyMeasurable f (g.volume.restrict K)) :
    CauchySeq
      (fun n : ℕ ↦
        (greenSobolevH10SmoothCompactSupportCore g).toCompletion
          (greenSmoothCoreElement (g := g)
            (smoothCompactProduct M (F n))
            ((smoothCompactProduct M (F n)).differential_memHilbertSchmidtL2))) := by
  classical
  let C := greenSobolevH10SmoothCompactSupportCore g
  let U : ℕ → C.Core :=
    fun n : ℕ ↦ greenSmoothCoreElement (g := g) (F n) (hF n)
  have hF_core_cauchy :
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
          ‖greenSmoothCoreElement (g := g) (F n) (hF n) -
            greenSmoothCoreElement (g := g) (F m) (hF m)‖ < ε := by
    simpa [U] using
      greenSobolevH10SmoothCompactSupportCore_norm_cauchy_of_tendsto_completion
        (g := g) U u hF_tendsto
  have hF_local_cauchy :
      ∀ ε : ℝ≥0∞, 0 < ε →
        ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
          eLpNorm
            (fun x : X ↦ (F n).toFun x - (F m).toFun x)
            2 (g.volume.restrict (tsupport M.toFun)) ≤ ε := by
    have hbase :
        TendstoInLocalL2OnSurface g.volume (tsupport M.toFun)
          (fun n : ℕ ↦ (F n).toFun) f :=
      hF_local (tsupport M.toFun) M.compact_support
    have hF_meas :
        ∀ n : ℕ,
          AEStronglyMeasurable (F n).toFun
            (g.volume.restrict (tsupport M.toFun)) := by
      intro n
      have hmem :
          MemLp (F n).toFun 2
            (g.volume.restrict (tsupport M.toFun)) :=
        (F n).memLp_restrict_compact (g := g) M.compact_support
      exact hmem.aestronglyMeasurable
    exact
      hbase.cauchy_eLpNorm hF_meas
        (hf_meas (tsupport M.toFun) M.compact_support)
  have hprod_norm_cauchy :
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
          ‖greenSmoothCoreElement (g := g)
              (smoothCompactProduct M (F n))
              ((smoothCompactProduct M (F n)).differential_memHilbertSchmidtL2) -
            greenSmoothCoreElement (g := g)
              (smoothCompactProduct M (F m))
              ((smoothCompactProduct M (F m)).differential_memHilbertSchmidtL2)‖ <
            ε :=
    smoothCompactMultiplier_core_norm_cauchy
      (g := g) M F hF hF_core_cauchy hF_local_cauchy
  refine Metric.cauchySeq_iff.2 ?_
  intro ε hε
  rcases hprod_norm_cauchy ε hε with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn m hm
  let V : ℕ → C.Core :=
    fun k : ℕ ↦
      greenSmoothCoreElement (g := g)
        (smoothCompactProduct M (F k))
        ((smoothCompactProduct M (F k)).differential_memHilbertSchmidtL2)
  have hdist_eq :
      dist (C.toCompletion (V n)) (C.toCompletion (V m)) =
        dist (V n) (V m) := by
    change
      dist ((V n : C.Core) : UniformSpace.Completion C.Core)
        ((V m : C.Core) : UniformSpace.Completion C.Core) =
          dist (V n) (V m)
    exact UniformSpace.Completion.dist_eq (V n) (V m)
  have hnorm_eq : ‖V n - V m‖ = dist (V n) (V m) := by
    rw [dist_eq_norm]
  have hnorm_lt : ‖V n - V m‖ < ε := by
    simpa [V] using hN n m hn hm
  rw [hdist_eq]
  simpa [hnorm_eq] using hnorm_lt

/--
%%handwave
name:
  Compact smooth multipliers preserve pure zero trace
statement:
  Multiplying a pure homogeneous zero-trace scalar representative by a compactly
  supported smooth surface function again gives a pure homogeneous zero-trace
  scalar representative.
proof:
  Multiply the compactly supported smooth approximating primitives by the
  fixed smooth multiplier.  The product rule controls the pure differential:
  one term is bounded by the multiplier times the original differential, and
  the other is controlled on the compact support of the multiplier's
  differential by compact-local \(L^2\)-convergence of the primitives.  Hence
  the product sequence is Cauchy in the pure completion and converges locally
  in \(L^2\) to the multiplied representative.
-/
theorem pureH10_smoothCompactlySupportedMultiplier_has_scalarRepresentative
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [SecondCountableTopology X] [ComplexOneManifold X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (M : SmoothCompactlySupportedGlobalSurfaceFunction X)
    {u : GreenSobolevH10SmoothCompactSupport g} {f : X → ℝ}
    (hrep : HasPureH10ScalarRepresentative u f)
    (_hf_meas :
      ∀ K : Set X, IsCompact K →
        AEStronglyMeasurable f (g.volume.restrict K)) :
    ∃ v : GreenSobolevH10SmoothCompactSupport g,
      HasPureH10ScalarRepresentative v
        (fun x : X ↦ M.toFun x * f x) := by
  classical
  rcases hrep with ⟨F, hF, hF_tendsto, hF_local⟩
  let V : ℕ → SmoothCompactlySupportedGlobalSurfaceFunction X :=
    fun n : ℕ ↦ smoothCompactProduct M (F n)
  let hV : ∀ n : ℕ,
      SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
        (SurfaceDifferentialField.ofCoordinateField (V n).gradient) :=
    fun n : ℕ ↦ (V n).differential_memHilbertSchmidtL2
  have hV_cauchy :
      CauchySeq
        (fun n : ℕ ↦
          (greenSobolevH10SmoothCompactSupportCore g).toCompletion
            (greenSmoothCoreElement (g := g) (V n) (hV n))) := by
    simpa [V, hV] using
      smoothCompactMultiplier_coreSequence_cauchy
        (g := g) M F hF hF_tendsto hF_local _hf_meas
  rcases cauchySeq_tendsto_of_complete hV_cauchy with ⟨v, hv_tendsto⟩
  refine ⟨v, ⟨V, hV, hv_tendsto, ?_⟩⟩
  intro K hK
  have hM_cont : Continuous M.toFun :=
    isSmoothOnSurface_univ_continuous M.smooth
  have hlocal :=
    (hF_local K hK).mul_left_continuous hK hM_cont
  simpa [V, smoothCompactProduct,
    SmoothCompactlySupportedGlobalSurfaceFunction.mul_of_left_support_subset_open]
    using hlocal

/--
%%handwave
name:
  Pole model killed by a smooth vanishing factor is pure zero trace
statement:
  If a globally smooth factor vanishes in a neighbourhood of the logarithmic
  pole, then its product with the cutoff pole model is represented by a pure
  homogeneous zero-trace class.
proof:
  The support condition removes the pole singularity, so the product is a
  smooth compactly supported surface test.  Such tests define pure
  homogeneous zero-trace representatives by taking their differentials.
-/
theorem poleModel_smoothLocalizedProduct_has_pureH10_scalarRepresentative
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [RiemannSurface X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    (φ : LogarithmicCutoffPoleModel g p)
    {η : X → ℝ}
    (hη_smooth : IsSmoothOnSurface (Set.univ : Set X) η)
    (hη_support : closure {x : X | η x ≠ 0} ⊆ {x : X | x ≠ p}) :
    ∃ v : GreenSobolevH10SmoothCompactSupport g,
      HasPureH10ScalarRepresentative v
        (fun x : X ↦ η x * φ.toFun x) := by
  let F : SmoothCompactlySupportedGlobalSurfaceFunction X :=
    SmoothCompactlySupportedGlobalSurfaceFunction.mul_of_left_support_subset_open
      (V := {x : X | x ≠ p})
      (isOpen_ne (x := p))
      hη_smooth φ.smooth_away_pole φ.compact_support hη_support
  let hF : SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
      (SurfaceDifferentialField.ofCoordinateField F.gradient) :=
    F.differential_memHilbertSchmidtL2
  refine
    ⟨(greenSobolevH10SmoothCompactSupportCore g).toCompletion
        (greenSmoothCoreElement (g := g) F hF), ?_⟩
  change
    HasPureH10ScalarRepresentative
      ((greenSobolevH10SmoothCompactSupportCore g).toCompletion
        (greenSmoothCoreElement (g := g) F hF))
      F.toFun
  exact HasPureH10ScalarRepresentative.of_smoothCompactlySupported F hF

/--
%%handwave
name:
  Smooth composed tests belong to the pure core
statement:
  The differential of a smooth zero-preserving composition of a compactly
  supported smooth surface test function represents an element of the pure
  Dirichlet core.
proof:
  The composite is a compactly supported smooth surface test function, so its
  differential is one of the generators of the smooth Dirichlet core.
-/
theorem smoothCompactlySupported_compSmoothZero_mem_core
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (F : SmoothCompactlySupportedGlobalSurfaceFunction X)
    (S : ℝ → ℝ) (hS_smooth : ContDiff ℝ ∞ S) (hS_zero : S 0 = 0)
    (hSF : SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
      (SurfaceDifferentialField.ofCoordinateField
        (F.compSmoothZero S hS_smooth hS_zero).gradient)) :
    greenSmoothDifferentialClass (g := g)
        (F.compSmoothZero S hS_smooth hS_zero) hSF ∈
      greenSobolevH10SmoothCompactSupportCoreSubmodule g := by
  refine smoothCompactlySupportedGreenDifferentialClass_mem_core ?_
  refine ⟨F.compSmoothZero S hS_smooth hS_zero, hSF, ?_⟩
  rfl

/--
%%handwave
name:
  Smooth zero-compositions have square-integrable differential
statement:
  If a compactly supported smooth surface function is composed with a smooth
  scalar function fixing zero, then the composed compactly supported smooth
  function has square-integrable classical differential.
proof:
  The composition is again a compactly supported smooth surface function, so
  the general square-integrability theorem for compactly supported smooth
  differentials applies.
-/
theorem smoothCompactlySupported_compSmoothZero_memHilbertSchmidtL2
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (F : SmoothCompactlySupportedGlobalSurfaceFunction X)
    (S : ℝ → ℝ) (hS_smooth : ContDiff ℝ ∞ S) (hS_zero : S 0 = 0) :
    SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
      (SurfaceDifferentialField.ofCoordinateField
        (F.compSmoothZero S hS_smooth hS_zero).gradient) :=
  (F.compSmoothZero S hS_smooth hS_zero).differential_memHilbertSchmidtL2

/--
%%handwave
name:
  Smooth zero-preserving compositions satisfy the Dirichlet bound
statement:
  If \(S\) is smooth, fixes zero, and has derivative bounded by \(L\), then
  the pure Dirichlet norm of \(S\circ F\) is at most \(L\) times the pure
  Dirichlet norm of \(F\).
proof:
  Use the chain rule \(d(S\circ F)=S'(F)dF\) and the pointwise cotangent norm
  inequality, then integrate.  This is the quantitative form of the first
  smooth approximation step.
-/
theorem smoothCompactlySupported_compSmoothZero_norm_le
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (F : SmoothCompactlySupportedGlobalSurfaceFunction X)
    (hF : SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
      (SurfaceDifferentialField.ofCoordinateField F.gradient))
    (S : ℝ → ℝ) (hS_smooth : ContDiff ℝ ∞ S) (hS_zero : S 0 = 0)
    {L : ℝ} (hL_nonneg : 0 ≤ L)
    (hS_deriv_bound : ∀ t : ℝ, ‖fderiv ℝ S t‖ ≤ L)
    (hSF : SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
      (SurfaceDifferentialField.ofCoordinateField
        (F.compSmoothZero S hS_smooth hS_zero).gradient)) :
    ‖greenSmoothDifferentialClass (g := g)
        (F.compSmoothZero S hS_smooth hS_zero) hSF‖ ≤
      L * ‖greenSmoothDifferentialClass (g := g) F hF‖ := by
  let SF := F.compSmoothZero S hS_smooth hS_zero
  let IF : ℝ :=
    ∫ x, g.gradientInner x (F.gradient x) (F.gradient x) ∂g.volume
  let ISF : ℝ :=
    ∫ x, g.gradientInner x (SF.gradient x) (SF.gradient x) ∂g.volume
  have hIF_nonneg : 0 ≤ IF := by
    dsimp [IF]
    exact integral_nonneg fun x ↦
      BackgroundSurfaceMetricOnSurface.gradientInner_nonneg g x (F.gradient x)
  have hISF_nonneg : 0 ≤ ISF := by
    dsimp [ISF]
    exact integral_nonneg fun x ↦
      BackgroundSurfaceMetricOnSurface.gradientInner_nonneg g x (SF.gradient x)
  have hF_int :
      Integrable
        (fun x ↦ g.gradientInner x (F.gradient x) (F.gradient x))
        g.volume := by
    have hnorm :
        Integrable
          (fun x ↦
            (manifoldDifferentialHilbertBundleGeometry
              (I := SurfaceRealModel) (X := X) (E := ℝ)
              g.metric.toManifoldMetric).fiberNormSq x
              ((SurfaceDifferentialField.ofCoordinateField F.gradient) x))
          g.volume :=
      hF.integrable_normSq
    refine hnorm.congr ?_
    filter_upwards [] with x
    simpa using
      (surface_coordinate_cotangent_fiberNormSq_eq_gradientInner
        g x (F.gradient x))
  have hSF_int :
      Integrable
        (fun x ↦ g.gradientInner x (SF.gradient x) (SF.gradient x))
        g.volume := by
    have hnorm :
        Integrable
          (fun x ↦
            (manifoldDifferentialHilbertBundleGeometry
              (I := SurfaceRealModel) (X := X) (E := ℝ)
              g.metric.toManifoldMetric).fiberNormSq x
              ((SurfaceDifferentialField.ofCoordinateField SF.gradient) x))
          g.volume :=
      hSF.integrable_normSq
    refine hnorm.congr ?_
    filter_upwards [] with x
    simpa using
      (surface_coordinate_cotangent_fiberNormSq_eq_gradientInner
        g x (SF.gradient x))
  have hL_sq_nonneg : 0 ≤ L ^ (2 : ℕ) := sq_nonneg L
  have hpoint :
      ∀ x : X,
        g.gradientInner x (SF.gradient x) (SF.gradient x) ≤
          L ^ (2 : ℕ) *
            g.gradientInner x (F.gradient x) (F.gradient x) := by
    intro x
    let c : ℝ := fderiv ℝ S (F.toFun x) 1
    have hc_abs : |c| ≤ L := by
      have happly : ‖fderiv ℝ S (F.toFun x) 1‖ ≤
          ‖fderiv ℝ S (F.toFun x)‖ * ‖(1 : ℝ)‖ :=
        (fderiv ℝ S (F.toFun x)).le_opNorm (1 : ℝ)
      have happly' : |c| ≤ ‖fderiv ℝ S (F.toFun x)‖ := by
        simpa [c, Real.norm_eq_abs] using happly
      exact happly'.trans (hS_deriv_bound (F.toFun x))
    have hc_abs' : |c| ≤ |L| := by
      simpa [abs_of_nonneg hL_nonneg] using hc_abs
    have hc_sq : c ^ (2 : ℕ) ≤ L ^ (2 : ℕ) :=
      sq_le_sq.mpr hc_abs'
    have hgrad : SF.gradient x = c • F.gradient x := by
      simpa [SF, c] using
        SmoothCompactlySupportedGlobalSurfaceFunction.compSmoothZero_gradient_eq_smul_derivative
          F S hS_smooth hS_zero x
    calc
      g.gradientInner x (SF.gradient x) (SF.gradient x) =
          c ^ (2 : ℕ) *
            g.gradientInner x (F.gradient x) (F.gradient x) := by
            rw [hgrad]
            exact
              BackgroundSurfaceMetricOnSurface.gradientInner_smul_smul
                g x (F.gradient x) c
      _ ≤ L ^ (2 : ℕ) *
            g.gradientInner x (F.gradient x) (F.gradient x) :=
            mul_le_mul_of_nonneg_right hc_sq
              (BackgroundSurfaceMetricOnSurface.gradientInner_nonneg
                g x (F.gradient x))
  have hISF_le : ISF ≤ L ^ (2 : ℕ) * IF := by
    dsimp [ISF, IF]
    calc
      ∫ x, g.gradientInner x (SF.gradient x) (SF.gradient x) ∂g.volume
          ≤
          ∫ x, L ^ (2 : ℕ) *
            g.gradientInner x (F.gradient x) (F.gradient x) ∂g.volume :=
            integral_mono hSF_int (hF_int.const_mul _) hpoint
      _ = L ^ (2 : ℕ) *
          ∫ x, g.gradientInner x (F.gradient x) (F.gradient x) ∂g.volume := by
            rw [integral_const_mul]
  have hnormF :
      ‖greenSmoothDifferentialClass (g := g) F hF‖ = Real.sqrt IF := by
    simpa [IF] using greenSmoothDifferentialClass_norm_eq_sqrt_dirichlet F hF
  have hnormSF :
      ‖greenSmoothDifferentialClass (g := g) SF hSF‖ = Real.sqrt ISF := by
    simpa [ISF, SF] using
      greenSmoothDifferentialClass_norm_eq_sqrt_dirichlet SF hSF
  calc
    ‖greenSmoothDifferentialClass (g := g)
        (F.compSmoothZero S hS_smooth hS_zero) hSF‖ =
        Real.sqrt ISF := by
          simpa [SF] using hnormSF
    _ ≤ Real.sqrt (L ^ (2 : ℕ) * IF) :=
        Real.sqrt_le_sqrt hISF_le
    _ = L * Real.sqrt IF := by
        rw [Real.sqrt_mul hL_sq_nonneg IF]
        rw [Real.sqrt_sq hL_nonneg]
    _ = L * ‖greenSmoothDifferentialClass (g := g) F hF‖ := by
        rw [hnormF]

/--
%%handwave
name:
  Smooth zero-compositions satisfy the Dirichlet bound
statement:
  If \(S\) is smooth, fixes zero, and has derivative bounded by \(L\), then
  the pure Dirichlet norm of \(S\circ F\) is at most \(L\) times the pure
  Dirichlet norm of \(F\).
proof:
  Use square-integrability of the composed differential and apply the
  pointwise chain-rule Dirichlet estimate.
-/
theorem smoothCompactlySupported_compSmoothZero_norm_le'
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (F : SmoothCompactlySupportedGlobalSurfaceFunction X)
    (hF : SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
      (SurfaceDifferentialField.ofCoordinateField F.gradient))
    (S : ℝ → ℝ) (hS_smooth : ContDiff ℝ ∞ S) (hS_zero : S 0 = 0)
    {L : ℝ} (hL_nonneg : 0 ≤ L)
    (hS_deriv_bound : ∀ t : ℝ, ‖fderiv ℝ S t‖ ≤ L) :
    ‖greenSmoothDifferentialClass (g := g)
        (F.compSmoothZero S hS_smooth hS_zero)
        (smoothCompactlySupported_compSmoothZero_memHilbertSchmidtL2
          (g := g) F S hS_smooth hS_zero)‖ ≤
      L * ‖greenSmoothDifferentialClass (g := g) F hF‖ :=
  smoothCompactlySupported_compSmoothZero_norm_le
    (g := g) F hF S hS_smooth hS_zero hL_nonneg hS_deriv_bound
    (smoothCompactlySupported_compSmoothZero_memHilbertSchmidtL2
      (g := g) F S hS_smooth hS_zero)

/--
%%handwave
name:
  Contracted core primitives converge locally
statement:
  If smooth core primitives \(F_n\) converge compact-locally in \(L^2\) to
  \(f\), then \(T\circ F_n\) converges compact-locally in \(L^2\) to
  \(T\circ f\) for every Lipschitz \(T\).
proof:
  Apply the pointwise Lipschitz inequality and the \(L^2\)-convergence
  estimate for Lipschitz postcomposition on each compact set.
-/
theorem pureH10_coreSequence_lipschitzComposition_tendsto_localL2
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    {f : X → ℝ}
    (U : ℕ → (greenSobolevH10SmoothCompactSupportCore g).Core)
    (hU_local :
      ∀ K : Set X, IsCompact K →
        TendstoInLocalL2OnSurface g.volume K
          (fun n : ℕ ↦
            (greenSobolevH10SmoothCompactSupportCorePrimitive
              (U n)).toFun)
          f)
    {T : ℝ → ℝ} {L : ℝ}
    (hL_nonneg : 0 ≤ L)
    (hT_lipschitz : ∀ s t : ℝ, |T s - T t| ≤ L * |s - t|)
    (K : Set X) (hK : IsCompact K) :
    TendstoInLocalL2OnSurface g.volume K
      (fun n : ℕ ↦ fun x : X ↦
        T ((greenSobolevH10SmoothCompactSupportCorePrimitive
          (U n)).toFun x))
      (fun x : X ↦ T (f x)) :=
  (hU_local K hK).comp_lipschitz hL_nonneg hT_lipschitz

/--
%%handwave
name:
  Boundedness of pure Cauchy smooth core sequences
statement:
  If compactly supported smooth primitives are Cauchy in the pure Dirichlet
  norm, then their images in the pure Hilbert completion are norm-bounded.
proof:
  A Cauchy sequence in a metric space is bounded.  The completion embedding
  preserves distances and norms.
-/
theorem greenSmoothCoreElement_toCompletion_norm_bounded_of_core_norm_cauchy
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (F : ℕ → SmoothCompactlySupportedGlobalSurfaceFunction X)
    (hF : ∀ n : ℕ,
      SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
        (SurfaceDifferentialField.ofCoordinateField (F n).gradient))
    (hF_cauchy :
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
          ‖greenSmoothCoreElement (g := g) (F n) (hF n) -
            greenSmoothCoreElement (g := g) (F m) (hF m)‖ < ε) :
    ∃ C : ℝ, ∀ n : ℕ,
      ‖(greenSobolevH10SmoothCompactSupportCore g).toCompletion
        (greenSmoothCoreElement (g := g) (F n) (hF n))‖ ≤ C := by
  let Ccore := greenSobolevH10SmoothCompactSupportCore g
  let u : ℕ → Ccore.Core :=
    fun n : ℕ ↦ greenSmoothCoreElement (g := g) (F n) (hF n)
  let v : ℕ → GreenSobolevH10DirichletCompletion Ccore :=
    fun n : ℕ ↦ Ccore.toCompletion (u n)
  have hv_cauchy : CauchySeq v := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    rcases hF_cauchy ε hε with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn m hm
    have hcore : ‖u n - u m‖ < ε := hN n m hn hm
    have hdist_eq : dist (v n) (v m) = dist (u n) (u m) := by
      change
        dist ((u n : Ccore.Core) : UniformSpace.Completion Ccore.Core)
          ((u m : Ccore.Core) : UniformSpace.Completion Ccore.Core) =
            dist (u n) (u m)
      exact UniformSpace.Completion.dist_eq (u n) (u m)
    rw [hdist_eq, dist_eq_norm]
    exact hcore
  rcases isBounded_iff_forall_norm_le.1 hv_cauchy.isBounded_range with
    ⟨Cnorm, hCnorm⟩
  refine ⟨Cnorm, ?_⟩
  intro n
  simpa [v, u, Ccore] using hCnorm (v n) (Set.mem_range_self n)

/--
%%handwave
name:
  Tail convex averages have represented scalar averages
statement:
  Suppose \(u_n\) are pure \(H^1_0\) classes represented by scalar functions
  \(\psi_n\), and \(\psi_n\to\psi\) compact-locally in \(L^2\).  If \(w_k\)
  lies in the finite convex hull of the tail \(\{u_n:n\ge k\}\), then there
  are scalar representatives \(\xi_k\) of \(w_k\) and the functions
  \(\xi_k\) converge compact-locally in \(L^2\) to \(\psi\).
proof:
  Use the finite-convex-hull representation of \(w_k\).  For each finitely
  many tail element \(u_n\), choose a smooth scalar representative sequence
  for \(\psi_n\).  Finite sums of compactly supported smooth primitives are
  again compactly supported and smooth, and their differential classes are the
  corresponding finite sums in the pure Hilbert completion.  The scalar
  representative of \(w_k\) is the same convex combination of the \(\psi_n\)'s.
  Since all selected indices satisfy \(n\ge k\), compact-local convergence of
  \(\psi_n\to\psi\) and Jensen's inequality for nonnegative weights summing to
  one give \(\xi_k\to\psi\) on every compact set.
-/
theorem pureH10_tailConvexAverages_representedScalarSequence
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [SecondCountableTopology X] [ComplexOneManifold X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    {ψSeq : ℕ → X → ℝ} {ψ : X → ℝ}
    (u : ℕ → GreenSobolevH10SmoothCompactSupport g)
    (hrep : ∀ n : ℕ, HasPureH10ScalarRepresentative (u n) (ψSeq n))
    (hψSeq_meas :
      ∀ n : ℕ, ∀ K : Set X, IsCompact K →
        AEStronglyMeasurable (ψSeq n) (g.volume.restrict K))
    (hψ_meas :
      ∀ K : Set X, IsCompact K →
        AEStronglyMeasurable ψ (g.volume.restrict K))
    (hlocal :
      ∀ K : Set X, IsCompact K →
        TendstoInLocalL2OnSurface g.volume K ψSeq ψ)
    (w : ℕ → GreenSobolevH10SmoothCompactSupport g)
    (hw_mem : ∀ k : ℕ, w k ∈ convexHull ℝ (u '' Set.Ici k)) :
    ∃ ξ : ℕ → X → ℝ,
      (∀ k : ℕ, HasPureH10ScalarRepresentative (w k) (ξ k)) ∧
      (∀ k : ℕ, ∀ K : Set X, IsCompact K →
        AEStronglyMeasurable (ξ k) (g.volume.restrict K)) ∧
      (∀ K : Set X, IsCompact K →
        AEStronglyMeasurable ψ (g.volume.restrict K)) ∧
      ∀ K : Set X, IsCompact K →
        TendstoInLocalL2OnSurface g.volume K ξ ψ := by
  classical
  have hchoose :
      ∀ k : ℕ,
        ∃ ξk : X → ℝ,
          HasPureH10ScalarRepresentative (w k) ξk ∧
          (∀ K : Set X, IsCompact K →
            AEStronglyMeasurable ξk (g.volume.restrict K)) ∧
          ∀ K : Set X, IsCompact K → ∀ ε : ℝ≥0∞, 0 < ε →
            (∀ n : ℕ,
              k ≤ n →
                eLpNorm (fun x : X ↦ ψSeq n x - ψ x) 2
                  (g.volume.restrict K) ≤ ε) →
            eLpNorm (fun x : X ↦ ξk x - ψ x) 2
              (g.volume.restrict K) ≤ ε := by
    intro k
    rcases
        (mem_convexHull_iff_exists_fintype
          (R := ℝ) (s := u '' Set.Ici k) (x := w k)).1
          (hw_mem k) with
      ⟨ι, hι, coeff, point, hcoeff_nonneg, hcoeff_sum, hpoint_mem,
        hpoint_sum⟩
    letI : Fintype ι := hι
    letI : DecidableEq ι := Classical.decEq ι
    have huniv_nonempty : (Finset.univ : Finset ι).Nonempty := by
      by_contra hne
      have huniv_empty : (Finset.univ : Finset ι) = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hne
      have hsum_zero : (∑ i : ι, coeff i) = 0 := by
        simpa [huniv_empty] using
          (Finset.sum_empty : (∑ i ∈ (∅ : Finset ι), coeff i) = 0)
      have hbad : (0 : ℝ) = 1 := by
        calc
          (0 : ℝ) = ∑ i : ι, coeff i := hsum_zero.symm
          _ = 1 := hcoeff_sum
      exact zero_ne_one hbad
    have hpoint_mem' :
        ∀ i : ι, ∃ n : ℕ, n ∈ Set.Ici k ∧ u n = point i := by
      intro i
      simpa using hpoint_mem i
    choose ν hν_tail hν_eq using hpoint_mem'
    let ξk : X → ℝ :=
      fun x : X ↦ ∑ i : ι, coeff i * ψSeq (ν i) x
    have hsum_u_eq :
        (∑ i : ι, coeff i • u (ν i)) = w k := by
      calc
        (∑ i : ι, coeff i • u (ν i))
            = ∑ i : ι, coeff i • point i := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [hν_eq i]
        _ = w k := hpoint_sum
    have hrep_terms :
        ∀ i : ι, i ∈ (Finset.univ : Finset ι) →
          HasPureH10ScalarRepresentative
            (coeff i • u (ν i))
            (fun x : X ↦ coeff i * ψSeq (ν i) x) := by
      intro i _hi
      simpa [Pi.smul_apply, smul_eq_mul] using
        (hrep (ν i)).smul (coeff i)
    have hmeas_terms :
        ∀ i : ι, i ∈ (Finset.univ : Finset ι) →
          ∀ K : Set X, IsCompact K →
            AEStronglyMeasurable
              (fun x : X ↦ coeff i * ψSeq (ν i) x)
              (g.volume.restrict K) := by
      intro i _hi K hK
      simpa [Pi.smul_apply, smul_eq_mul] using
        (hψSeq_meas (ν i) K hK).const_smul (coeff i)
    rcases
        HasPureH10ScalarRepresentative.finset_sum_nonempty
          (g := g) (s := (Finset.univ : Finset ι)) huniv_nonempty
          hrep_terms hmeas_terms with
      ⟨hξ_rep_sum, hξ_meas_sum⟩
    have hξ_rep :
        HasPureH10ScalarRepresentative (w k) ξk := by
      simpa [ξk, hsum_u_eq] using hξ_rep_sum
    have hξ_meas :
        ∀ K : Set X, IsCompact K →
          AEStronglyMeasurable ξk (g.volume.restrict K) := by
      intro K hK
      simpa [ξk] using hξ_meas_sum K hK
    refine ⟨ξk, hξ_rep, hξ_meas, ?_⟩
    intro K hK ε _hε htail
    let μK := g.volume.restrict K
    have hξ_sub :
        (fun x : X ↦ ξk x - ψ x) =
          (∑ i : ι,
            fun x : X ↦ coeff i * (ψSeq (ν i) x - ψ x)) := by
      funext x
      dsimp [ξk]
      calc
        (∑ i : ι, coeff i * ψSeq (ν i) x) - ψ x
            =
            (∑ i : ι, coeff i * ψSeq (ν i) x) -
              (∑ i : ι, coeff i) * ψ x := by
          rw [hcoeff_sum]
          simp
        _ =
            (∑ i : ι, coeff i * ψSeq (ν i) x) -
              ∑ i : ι, coeff i * ψ x := by
          rw [Finset.sum_mul]
        _ =
            ∑ i : ι, (coeff i * ψSeq (ν i) x - coeff i * ψ x) := by
          rw [Finset.sum_sub_distrib]
        _ =
            ∑ i : ι, coeff i * (ψSeq (ν i) x - ψ x) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          ring
        _ =
            (∑ i : ι,
              fun y : X ↦ coeff i * (ψSeq (ν i) y - ψ y)) x := by
          simp
    have hdiff_meas :
        ∀ i : ι, i ∈ (Finset.univ : Finset ι) →
          AEStronglyMeasurable
            (fun x : X ↦ coeff i * (ψSeq (ν i) x - ψ x)) μK := by
      intro i _hi
      have hseq_meas :
          AEStronglyMeasurable (ψSeq (ν i)) μK := by
        simpa [μK] using hψSeq_meas (ν i) K hK
      have hψK_meas :
          AEStronglyMeasurable ψ μK := by
        simpa [μK] using hψ_meas K hK
      have hbase :
          AEStronglyMeasurable
            (fun x : X ↦ ψSeq (ν i) x - ψ x) μK :=
        hseq_meas.sub hψK_meas
      simpa [Pi.smul_apply, smul_eq_mul] using
        hbase.const_smul (coeff i)
    have htri :
        eLpNorm (fun x : X ↦ ξk x - ψ x) 2 μK ≤
          ∑ i : ι,
            eLpNorm
              (fun x : X ↦ coeff i * (ψSeq (ν i) x - ψ x)) 2 μK := by
      rw [hξ_sub]
      exact
        eLpNorm_sum_le
          (s := (Finset.univ : Finset ι)) hdiff_meas
          (by norm_num : (1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞))
    have hterm_eq :
        ∀ i : ι,
          eLpNorm
              (fun x : X ↦ coeff i * (ψSeq (ν i) x - ψ x)) 2 μK =
            ‖coeff i‖ₑ *
              eLpNorm (fun x : X ↦ ψSeq (ν i) x - ψ x) 2 μK := by
      intro i
      have hfun :
          (fun x : X ↦ coeff i * (ψSeq (ν i) x - ψ x)) =
            coeff i • (fun x : X ↦ ψSeq (ν i) x - ψ x) := by
        funext x
        simp [Pi.smul_apply, smul_eq_mul]
      rw [hfun]
      exact eLpNorm_const_smul (coeff i)
        (fun x : X ↦ ψSeq (ν i) x - ψ x) 2 μK
    have hcoeff_enorm_sum : (∑ i : ι, ‖coeff i‖ₑ) = 1 := by
      calc
        (∑ i : ι, ‖coeff i‖ₑ)
            = ∑ i : ι, ENNReal.ofReal (coeff i) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          exact Real.enorm_eq_ofReal (hcoeff_nonneg i)
        _ = ENNReal.ofReal (∑ i : ι, coeff i) := by
          rw [ENNReal.ofReal_sum_of_nonneg]
          intro i _hi
          exact hcoeff_nonneg i
        _ = 1 := by
          rw [hcoeff_sum]
          norm_num
    calc
      eLpNorm (fun x : X ↦ ξk x - ψ x) 2 (g.volume.restrict K)
          =
          eLpNorm (fun x : X ↦ ξk x - ψ x) 2 μK := rfl
      _ ≤
          ∑ i : ι,
            eLpNorm
              (fun x : X ↦ coeff i * (ψSeq (ν i) x - ψ x)) 2 μK := htri
      _ =
          ∑ i : ι,
            ‖coeff i‖ₑ *
              eLpNorm (fun x : X ↦ ψSeq (ν i) x - ψ x) 2 μK := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        exact hterm_eq i
      _ ≤ ∑ i : ι, ‖coeff i‖ₑ * ε := by
        refine Finset.sum_le_sum ?_
        intro i _hi
        exact mul_le_mul_right
          (htail (ν i) (by simpa using hν_tail i)) ‖coeff i‖ₑ
      _ = ε := by
        rw [← Finset.sum_mul, hcoeff_enorm_sum, one_mul]
  choose ξ hξ_rep hξ_meas hξ_tail_bound using hchoose
  refine ⟨ξ, hξ_rep, hξ_meas, hψ_meas, ?_⟩
  intro K hK
  unfold TendstoInLocalL2OnSurface
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  have hbase :
      TendstoInLocalL2OnSurface g.volume K ψSeq ψ :=
    hlocal K hK
  unfold TendstoInLocalL2OnSurface at hbase
  have hevent :
      ∀ᶠ n : ℕ in Filter.atTop,
        eLpNorm (fun x : X ↦ ψSeq n x - ψ x) 2
          (g.volume.restrict K) ≤ ε :=
    ENNReal.tendsto_nhds_zero.mp hbase ε hε
  rcases Filter.eventually_atTop.1 hevent with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro k hk
  exact
    hξ_tail_bound k K hK ε hε
      (fun n hn ↦ hN n (le_trans hk hn))

/--
%%handwave
name:
  Strong limits of represented classes have diagonal scalar representatives
statement:
  If \(w_k\to w\) strongly in the pure \(H^1_0\) completion, each \(w_k\) is
  represented by a scalar function \(\xi_k\), and \(\xi_k\to\psi\)
  compact-locally in \(L^2\), then \(w\) is represented by compactly
  supported smooth primitives converging compact-locally to \(\psi\).
proof:
  Choose a compact exhaustion of the surface.  For the \(k\)-th step, choose a
  smooth primitive from the representative sequence of \(w_k\) close to
  \(w_k\) in the pure completion and close to \(\xi_k\) on the first \(k\)
  exhaustion pieces.  Because \(w_k\to w\) and \(\xi_k\to\psi\) locally, this
  diagonal smooth sequence converges to \(w\) in the completion and
  compact-locally in \(L^2\) to \(\psi\).
-/
theorem pureH10_strongLimit_of_scalarRepresentatives_with_localL2_limit
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [SecondCountableTopology X] [ComplexOneManifold X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    {ξ : ℕ → X → ℝ} {ψ : X → ℝ}
    {wLim : GreenSobolevH10SmoothCompactSupport g}
    (w : ℕ → GreenSobolevH10SmoothCompactSupport g)
    (hrep : ∀ k : ℕ, HasPureH10ScalarRepresentative (w k) (ξ k))
    (hξ_meas :
      ∀ k : ℕ, ∀ K : Set X, IsCompact K →
        AEStronglyMeasurable (ξ k) (g.volume.restrict K))
    (hψ_meas :
      ∀ K : Set X, IsCompact K →
        AEStronglyMeasurable ψ (g.volume.restrict K))
    (hlocal :
      ∀ K : Set X, IsCompact K →
        TendstoInLocalL2OnSurface g.volume K ξ ψ)
    (hw_tendsto : Filter.Tendsto w Filter.atTop (𝓝 wLim)) :
    HasPureH10ScalarRepresentative wLim ψ := by
  classical
  let C := greenSobolevH10SmoothCompactSupportCore g
  choose F hF hF_tendsto hF_local using hrep
  let δ : ℕ → ℝ := fun k : ℕ ↦ 1 / ((k : ℝ) + 1)
  have hδ_pos : ∀ k : ℕ, 0 < δ k := by
    intro k
    dsimp [δ]
    positivity
  haveI : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace ℂ X
  letI : SigmaCompactSpace X := inferInstance
  let Kex : CompactExhaustion X := CompactExhaustion.choice X
  have hselect :
      ∀ k : ℕ,
        ∃ m : ℕ,
          dist
            (C.toCompletion
              (greenSmoothCoreElement (g := g) (F k m) (hF k m)))
            (w k) < δ k ∧
          ∀ j : ℕ, j ∈ Finset.range (k + 1) →
            eLpNorm
              (fun x : X ↦ (F k m).toFun x - ξ k x)
              2 (g.volume.restrict (Kex j)) ≤
            ENNReal.ofReal (δ k) := by
    intro k
    have hdist_eventually :
        ∀ᶠ m : ℕ in Filter.atTop,
          dist
            (C.toCompletion
              (greenSmoothCoreElement (g := g) (F k m) (hF k m)))
            (w k) < δ k := by
      exact
        (Metric.tendsto_nhds.mp (hF_tendsto k))
          (δ k) (hδ_pos k)
    have hloc_eventually :
        ∀ᶠ m : ℕ in Filter.atTop,
          ∀ j : ℕ, j ∈ Finset.range (k + 1) →
            eLpNorm
              (fun x : X ↦ (F k m).toFun x - ξ k x)
              2 (g.volume.restrict (Kex j)) ≤
            ENNReal.ofReal (δ k) := by
      rw [Filter.eventually_all_finset]
      intro j hj
      have ht :
          TendstoInLocalL2OnSurface g.volume (Kex j)
            (fun m : ℕ ↦ (F k m).toFun) (ξ k) :=
        hF_local k (Kex j) (Kex.isCompact j)
      unfold TendstoInLocalL2OnSurface at ht
      exact
        ENNReal.tendsto_nhds_zero.mp ht
          (ENNReal.ofReal (δ k))
          (ENNReal.ofReal_pos.mpr (hδ_pos k))
    rcases (hdist_eventually.and hloc_eventually).exists with
      ⟨m, hm_dist, hm_loc⟩
    exact ⟨m, hm_dist, hm_loc⟩
  choose diag hdiag_dist hdiag_loc using hselect
  let V : ℕ → SmoothCompactlySupportedGlobalSurfaceFunction X :=
    fun k : ℕ ↦ F k (diag k)
  let hV : ∀ k : ℕ,
      SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
        (SurfaceDifferentialField.ofCoordinateField (V k).gradient) :=
    fun k : ℕ ↦ hF k (diag k)
  refine ⟨V, hV, ?_, ?_⟩
  · rw [Metric.tendsto_nhds]
    intro ε hε
    have hhalf_pos : 0 < ε / 2 := by positivity
    have hw_eventually :
        ∀ᶠ k : ℕ in Filter.atTop,
          dist (w k) wLim < ε / 2 :=
      (Metric.tendsto_nhds.mp hw_tendsto) (ε / 2) hhalf_pos
    have hδ_tendsto :
        Filter.Tendsto (fun k : ℕ ↦ δ k) Filter.atTop (𝓝 0) := by
      simpa [δ] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hδ_eventually :
        ∀ᶠ k : ℕ in Filter.atTop, δ k < ε / 2 :=
      hδ_tendsto.eventually (gt_mem_nhds hhalf_pos)
    filter_upwards [hw_eventually, hδ_eventually] with k hwk hδk
    have htri :
        dist
          (C.toCompletion
            (greenSmoothCoreElement (g := g) (V k) (hV k)))
          wLim ≤
        dist
          (C.toCompletion
            (greenSmoothCoreElement (g := g) (V k) (hV k)))
          (w k) + dist (w k) wLim :=
      dist_triangle _ _ _
    have happrox :
        dist
          (C.toCompletion
            (greenSmoothCoreElement (g := g) (V k) (hV k)))
          (w k) < ε / 2 := by
      exact (hdiag_dist k).trans hδk
    calc
      dist
          (C.toCompletion
            (greenSmoothCoreElement (g := g) (V k) (hV k)))
          wLim
          ≤
          dist
            (C.toCompletion
              (greenSmoothCoreElement (g := g) (V k) (hV k)))
            (w k) + dist (w k) wLim := htri
      _ < ε / 2 + ε / 2 := add_lt_add happrox hwk
      _ = ε := by ring
  · intro K hK
    unfold TendstoInLocalL2OnSurface
    rw [ENNReal.tendsto_atTop_zero]
    intro ε hε
    rcases Kex.exists_superset_of_isCompact hK with ⟨j, hK_subset⟩
    have hξψ :
        TendstoInLocalL2OnSurface g.volume K ξ ψ := hlocal K hK
    unfold TendstoInLocalL2OnSurface at hξψ
    have hξψ_eventually :
        ∀ᶠ k : ℕ in Filter.atTop,
          eLpNorm (fun x : X ↦ ξ k x - ψ x) 2
              (g.volume.restrict K) ≤ ε / 2 :=
      ENNReal.tendsto_nhds_zero.mp hξψ (ε / 2)
        (ENNReal.div_pos_iff.mpr ⟨hε.ne', ENNReal.ofNat_ne_top⟩)
    have hδ_enn_tendsto :
        Filter.Tendsto
          (fun k : ℕ ↦ ENNReal.ofReal (δ k))
          Filter.atTop (𝓝 0) := by
      have hδ_real :
          Filter.Tendsto (fun k : ℕ ↦ δ k) Filter.atTop (𝓝 0) := by
        simpa [δ, one_div] using
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      simpa [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hδ_real
    have hδ_eventually :
        ∀ᶠ k : ℕ in Filter.atTop,
          ENNReal.ofReal (δ k) ≤ ε / 2 :=
      ENNReal.tendsto_nhds_zero.mp hδ_enn_tendsto (ε / 2)
        (ENNReal.div_pos_iff.mpr ⟨hε.ne', ENNReal.ofNat_ne_top⟩)
    have hj_eventually : ∀ᶠ k : ℕ in Filter.atTop, j ≤ k :=
      Filter.eventually_atTop.2 ⟨j, fun k hk ↦ hk⟩
    rcases
        Filter.eventually_atTop.1
          (hξψ_eventually.and (hδ_eventually.and hj_eventually)) with
      ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    have hpack := hN n hn
    have hξψ_n :
        eLpNorm (fun x : X ↦ ξ n x - ψ x) 2
            (g.volume.restrict K) ≤ ε / 2 := by
      exact hpack.1
    have hδ_n : ENNReal.ofReal (δ n) ≤ ε / 2 := hpack.2.1
    have hjn : j ≤ n := hpack.2.2
    have hj_mem : j ∈ Finset.range (n + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le hjn)
    have hmeasure_mono :
        g.volume.restrict K ≤ g.volume.restrict (Kex j) :=
      Measure.restrict_mono hK_subset le_rfl
    have hVξ_K :
        eLpNorm (fun x : X ↦ (V n).toFun x - ξ n x) 2
            (g.volume.restrict K) ≤ ε / 2 := by
      calc
        eLpNorm (fun x : X ↦ (V n).toFun x - ξ n x) 2
            (g.volume.restrict K)
            ≤
            eLpNorm (fun x : X ↦ (V n).toFun x - ξ n x) 2
              (g.volume.restrict (Kex j)) :=
          eLpNorm_mono_measure _ hmeasure_mono
        _ ≤ ENNReal.ofReal (δ n) := by
          simpa [V] using hdiag_loc n j hj_mem
        _ ≤ ε / 2 := hδ_n
    let μK := g.volume.restrict K
    have hV_meas :
        AEStronglyMeasurable (V n).toFun μK :=
      ((V n).memLp_restrict_compact (g := g) hK).aestronglyMeasurable
    have hξn_meas : AEStronglyMeasurable (ξ n) μK := by
      simpa [μK] using hξ_meas n K hK
    have hψK_meas : AEStronglyMeasurable ψ μK := by
      simpa [μK] using hψ_meas K hK
    have htri :
        eLpNorm (fun x : X ↦ (V n).toFun x - ψ x) 2 μK ≤
          eLpNorm (fun x : X ↦ (V n).toFun x - ξ n x) 2 μK +
            eLpNorm (fun x : X ↦ ξ n x - ψ x) 2 μK := by
      have hVξ_meas :
          AEStronglyMeasurable
            (fun x : X ↦ (V n).toFun x - ξ n x) μK :=
        hV_meas.sub hξn_meas
      have hξψ_meas :
          AEStronglyMeasurable
            (fun x : X ↦ ξ n x - ψ x) μK :=
        hξn_meas.sub hψK_meas
      have hbase :=
        eLpNorm_add_le hξψ_meas hVξ_meas
          (by norm_num : (1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞))
      have hbase' :
          eLpNorm (fun x : X ↦ (V n).toFun x - ψ x) 2 μK ≤
            eLpNorm (fun x : X ↦ ξ n x - ψ x) 2 μK +
              eLpNorm (fun x : X ↦ (V n).toFun x - ξ n x) 2 μK := by
        have hfun :
            ((fun x : X ↦ ξ n x - ψ x) +
                fun x : X ↦ (V n).toFun x - ξ n x) =
              fun x : X ↦ (V n).toFun x - ψ x := by
          funext x
          simp [Pi.add_apply]
        simpa [hfun] using hbase
      calc
        eLpNorm (fun x : X ↦ (V n).toFun x - ψ x) 2 μK
            ≤
            eLpNorm (fun x : X ↦ ξ n x - ψ x) 2 μK +
              eLpNorm (fun x : X ↦ (V n).toFun x - ξ n x) 2 μK := hbase'
        _ =
            eLpNorm (fun x : X ↦ (V n).toFun x - ξ n x) 2 μK +
              eLpNorm (fun x : X ↦ ξ n x - ψ x) 2 μK := by
          rw [add_comm]
    calc
      eLpNorm (fun x : X ↦ (V n).toFun x - ψ x) 2
          (g.volume.restrict K)
          =
          eLpNorm (fun x : X ↦ (V n).toFun x - ψ x) 2 μK := rfl
      _ ≤
          eLpNorm (fun x : X ↦ (V n).toFun x - ξ n x) 2 μK +
            eLpNorm (fun x : X ↦ ξ n x - ψ x) 2 μK := htri
      _ ≤ ε / 2 + ε / 2 := by
        exact add_le_add (by simpa [μK] using hVξ_K) (by simpa [μK] using hξψ_n)
      _ = ε := ENNReal.add_halves ε

/--
%%handwave
name:
  Diagonal scalar representative for Mazur convexified tail averages
statement:
  Suppose \(u_n\) are pure \(H^1_0\) classes represented by scalar functions
  \(\psi_n\), and \(\psi_n\to\psi\) compact-locally in \(L^2\).  If \(w_k\)
  are finite convex combinations of arbitrarily far tails of the \(u_n\) and
  \(w_k\to w\) strongly in the pure Hilbert completion, then \(w\) is
  represented by compactly supported smooth primitives converging
  compact-locally to \(\psi\).
proof:
  For each \(k\), write \(w_k\) as a finite convex combination of tail
  elements \(u_n\).  Choose smooth representative primitives for the finitely
  many \(u_n\)'s far enough along their representative sequences so that the
  same convex combination is close to \(w_k\) in the pure completion and close
  to \(\psi\) on the first \(k\) compact sets of a fixed compact exhaustion.
  Nonnegative weights summing to one preserve the compact-local \(L^2\) bound
  by Jensen's inequality.  Since \(w_k\to w\), a diagonal choice over \(k\)
  gives a single compactly supported smooth representative sequence for \(w\).
-/
theorem pureH10_mazurTailConvexAverages_diagonal_scalarRepresentative
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [SecondCountableTopology X] [ComplexOneManifold X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    {ψSeq : ℕ → X → ℝ} {ψ : X → ℝ}
    (u : ℕ → GreenSobolevH10SmoothCompactSupport g)
    (hrep : ∀ n : ℕ, HasPureH10ScalarRepresentative (u n) (ψSeq n))
    (hψSeq_meas :
      ∀ n : ℕ, ∀ K : Set X, IsCompact K →
        AEStronglyMeasurable (ψSeq n) (g.volume.restrict K))
    (hψ_meas :
      ∀ K : Set X, IsCompact K →
        AEStronglyMeasurable ψ (g.volume.restrict K))
    (hlocal :
      ∀ K : Set X, IsCompact K →
        TendstoInLocalL2OnSurface g.volume K ψSeq ψ)
    {wLim : GreenSobolevH10SmoothCompactSupport g}
    (w : ℕ → GreenSobolevH10SmoothCompactSupport g)
    (hw_mem : ∀ k : ℕ, w k ∈ convexHull ℝ (u '' Set.Ici k))
    (hw_tendsto : Filter.Tendsto w Filter.atTop (𝓝 wLim)) :
    HasPureH10ScalarRepresentative wLim ψ := by
  rcases
    pureH10_tailConvexAverages_representedScalarSequence
      (g := g) (ψSeq := ψSeq) (ψ := ψ)
      u hrep hψSeq_meas hψ_meas hlocal w hw_mem with
    ⟨ξ, hξ_rep, hξ_meas, hψ_meas, hξ_local⟩
  exact
    pureH10_strongLimit_of_scalarRepresentatives_with_localL2_limit
      (g := g) (ξ := ξ) (ψ := ψ) w hξ_rep
      hξ_meas hψ_meas hξ_local hw_tendsto

/--
%%handwave
name:
  Smooth realization of Mazur convexified tail averages
statement:
  Suppose \(u_n\) are pure \(H^1_0\) classes represented by scalar functions
  \(\psi_n\), and \(\psi_n\to\psi\) compact-locally in \(L^2\).  If
  \(w_k\) are finite convex combinations of arbitrarily far tails of the
  \(u_n\) and \(w_k\to w\) strongly in the pure Hilbert completion, then \(w\)
  has a compactly supported smooth representative sequence converging
  compact-locally to \(\psi\).
proof:
  Each \(w_k\) lies in the finite convex hull of tail elements \(u_n\), so it
  is a finite convex combination of pure classes represented by \(\psi_n\).
  Approximate the finitely many representatives by smooth compactly supported
  primitives and take the same convex combination of those primitives.  Since
  all indices are in a far tail, compact-local \(L^2\) convergence to \(\psi\)
  is preserved by Jensen's inequality.  A diagonal choice along the strong
  convergence \(w_k\to w\) gives one smooth core sequence converging in the
  pure completion and compact-locally in \(L^2\).
-/
theorem pureH10_mazurTailConvexAverages_smoothCoreApproximation
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [SecondCountableTopology X] [ComplexOneManifold X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    {ψSeq : ℕ → X → ℝ} {ψ : X → ℝ}
    (u : ℕ → GreenSobolevH10SmoothCompactSupport g)
    (hrep : ∀ n : ℕ, HasPureH10ScalarRepresentative (u n) (ψSeq n))
    (hψSeq_meas :
      ∀ n : ℕ, ∀ K : Set X, IsCompact K →
        AEStronglyMeasurable (ψSeq n) (g.volume.restrict K))
    (hψ_meas :
      ∀ K : Set X, IsCompact K →
        AEStronglyMeasurable ψ (g.volume.restrict K))
    (hlocal :
      ∀ K : Set X, IsCompact K →
        TendstoInLocalL2OnSurface g.volume K ψSeq ψ)
    {wLim : GreenSobolevH10SmoothCompactSupport g}
    (w : ℕ → GreenSobolevH10SmoothCompactSupport g)
    (hw_mem : ∀ k : ℕ, w k ∈ convexHull ℝ (u '' Set.Ici k))
    (hw_tendsto : Filter.Tendsto w Filter.atTop (𝓝 wLim)) :
  ∃ V : ℕ → SmoothCompactlySupportedGlobalSurfaceFunction X,
  ∃ hV : ∀ n : ℕ,
    SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
      (SurfaceDifferentialField.ofCoordinateField (V n).gradient),
    CauchySeq
      (fun n : ℕ ↦
        (greenSobolevH10SmoothCompactSupportCore g).toCompletion
          (greenSmoothCoreElement (g := g) (V n) (hV n))) ∧
      ∀ K : Set X, IsCompact K →
        TendstoInLocalL2OnSurface g.volume K
          (fun n : ℕ ↦ (V n).toFun)
          ψ := by
  rcases
    pureH10_mazurTailConvexAverages_diagonal_scalarRepresentative
      (g := g) (ψSeq := ψSeq) (ψ := ψ)
      u hrep hψSeq_meas hψ_meas hlocal w hw_mem hw_tendsto with
    ⟨V, hV, hV_tendsto, hV_local⟩
  exact ⟨V, hV, hV_tendsto.cauchySeq, hV_local⟩

/--
%%handwave
name:
  Fixed smooth core composition by smooth mollification
statement:
  Let \(F\) be compactly supported and smooth.  Every Lipschitz map \(T\)
  fixing zero sends \(F\) to a pure \(H^1_0\) element represented by
  compactly supported smooth approximants, with the expected Dirichlet norm
  bound.
proof:
  Approximate \(T\) by smooth zero-preserving mollifications with the same
  Lipschitz bound.  The resulting smooth compositions have uniformly bounded
  pure Dirichlet norm and converge compact-locally in \(L^2\) to \(T\circ F\).
  Apply Mazur convexification in the pure Hilbert completion and diagonalize
  the scalar representatives of the convexified tails.
-/
theorem smoothCompactlySupported_lipschitzZeroComposition_coreApproximation_of_mollification
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [SecondCountableTopology X] [ComplexOneManifold X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (F : SmoothCompactlySupportedGlobalSurfaceFunction X)
    (hF : SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
      (SurfaceDifferentialField.ofCoordinateField F.gradient))
    {T : ℝ → ℝ} {L : ℝ}
    (hL_nonneg : 0 ≤ L)
    (hT_zero : T 0 = 0)
    (hT_lipschitz : ∀ s t : ℝ, |T s - T t| ≤ L * |s - t|) :
    ∃ V : ℕ → SmoothCompactlySupportedGlobalSurfaceFunction X,
    ∃ hV : ∀ n : ℕ,
      SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
        (SurfaceDifferentialField.ofCoordinateField (V n).gradient),
      CauchySeq
        (fun n : ℕ ↦
          (greenSobolevH10SmoothCompactSupportCore g).toCompletion
            (greenSmoothCoreElement (g := g) (V n) (hV n))) ∧
        (∀ K : Set X, IsCompact K →
          TendstoInLocalL2OnSurface g.volume K
            (fun n : ℕ ↦ (V n).toFun)
            (fun x : X ↦ T (F.toFun x))) ∧
        ∃ v : GreenSobolevH10SmoothCompactSupport g,
          Filter.Tendsto
            (fun n : ℕ ↦
              (greenSobolevH10SmoothCompactSupportCore g).toCompletion
                (greenSmoothCoreElement (g := g) (V n) (hV n)))
            Filter.atTop (𝓝 v) ∧
            ‖v‖ ≤ L *
              ‖(greenSobolevH10SmoothCompactSupportCore g).toCompletion
                (greenSmoothCoreElement (g := g) F hF)‖ := by
  classical
  let Ccore := greenSobolevH10SmoothCompactSupportCore g
  let uF : GreenSobolevH10SmoothCompactSupport g :=
    Ccore.toCompletion (greenSmoothCoreElement (g := g) F hF)
  let δ : ℕ → ℝ := fun n : ℕ ↦ 1 / ((n : ℝ) + 1)
  have hδ_pos : ∀ n : ℕ, 0 < δ n := by
    intro n
    dsimp [δ]
    positivity
  have happrox :
      ∀ n : ℕ,
        ∃ S : ℝ → ℝ,
          ContDiff ℝ (⊤ : ℕ∞) S ∧
          S 0 = 0 ∧
          (∀ t : ℝ, |S t - T t| < δ n) ∧
          ∀ t : ℝ, ‖fderiv ℝ S t‖ ≤ L := by
    intro n
    exact
      lipschitzZero_has_smooth_zero_mollifier_approx_deriv_bound
        hL_nonneg hT_zero hT_lipschitz (hδ_pos n)
  choose S hS_smooth hS_zero hS_close hS_deriv_bound using happrox
  let W : ℕ → SmoothCompactlySupportedGlobalSurfaceFunction X :=
    fun n : ℕ ↦ F.compSmoothZero (S n) (hS_smooth n) (hS_zero n)
  let hW : ∀ n : ℕ,
      SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
        (SurfaceDifferentialField.ofCoordinateField (W n).gradient) :=
    fun n : ℕ ↦
      smoothCompactlySupported_compSmoothZero_memHilbertSchmidtL2
        (g := g) F (S n) (hS_smooth n) (hS_zero n)
  let u : ℕ → GreenSobolevH10SmoothCompactSupport g :=
    fun n : ℕ ↦
      Ccore.toCompletion
        (greenSmoothCoreElement (g := g) (W n) (hW n))
  have hrep :
      ∀ n : ℕ, HasPureH10ScalarRepresentative (u n) (W n).toFun := by
    intro n
    exact
      HasPureH10ScalarRepresentative.of_smoothCompactlySupported
        (g := g) (W n) (hW n)
  have hW_meas :
      ∀ n : ℕ, ∀ K : Set X, IsCompact K →
        AEStronglyMeasurable (W n).toFun (g.volume.restrict K) := by
    intro n K hK
    exact ((W n).memLp_restrict_compact (g := g) hK).aestronglyMeasurable
  have hT_cont : Continuous T :=
    continuous_of_real_lipschitz_bound hL_nonneg hT_lipschitz
  have hTF_meas :
      ∀ K : Set X, IsCompact K →
        AEStronglyMeasurable
          (fun x : X ↦ T (F.toFun x)) (g.volume.restrict K) := by
    intro K hK
    exact
      hT_cont.comp_aestronglyMeasurable
        (F.memLp_restrict_compact (g := g) hK).aestronglyMeasurable
  have hδ_tendsto :
      Filter.Tendsto (fun n : ℕ ↦ δ n) Filter.atTop (𝓝 0) := by
    simpa [δ] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hδ_enn_tendsto :
      Filter.Tendsto (fun n : ℕ ↦ ENNReal.ofReal (δ n))
        Filter.atTop (𝓝 0) := by
    simpa [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hδ_tendsto
  have hW_local :
      ∀ K : Set X, IsCompact K →
        TendstoInLocalL2OnSurface g.volume K
          (fun n : ℕ ↦ (W n).toFun)
          (fun x : X ↦ T (F.toFun x)) := by
    intro K hK
    unfold TendstoInLocalL2OnSurface
    let μK := g.volume.restrict K
    haveI : IsFiniteMeasureOnCompacts g.volume :=
      BackgroundSurfaceMetricOnSurface.volume_isFiniteMeasureOnCompacts g
    have hμK_ne_top : μK Set.univ ≠ (∞ : ℝ≥0∞) := by
      have hK_ne_top : g.volume K ≠ (∞ : ℝ≥0∞) := hK.measure_ne_top
      simpa [μK, Measure.restrict_apply MeasurableSet.univ] using hK_ne_top
    let A : ℝ≥0∞ := μK Set.univ ^ ((2 : ℝ≥0∞).toReal)⁻¹
    have hA_ne_top : A ≠ (∞ : ℝ≥0∞) := by
      have hpow_lt :
          μK Set.univ ^ ((2 : ℝ≥0∞).toReal)⁻¹ < (∞ : ℝ≥0∞) :=
        ENNReal.rpow_lt_top_of_nonneg (by positivity) hμK_ne_top
      exact hpow_lt.ne
    have hbound :
        ∀ n : ℕ,
          eLpNorm
            (fun x : X ↦ (W n).toFun x - T (F.toFun x))
            2 μK ≤ A * ENNReal.ofReal (δ n) := by
      intro n
      have hae :
          ∀ᵐ x ∂μK,
            ‖(W n).toFun x - T (F.toFun x)‖ ≤ δ n := by
        filter_upwards [] with x
        have hclose := hS_close n (F.toFun x)
        simpa [W, SmoothCompactlySupportedGlobalSurfaceFunction.compSmoothZero_toFun,
          Real.norm_eq_abs] using hclose.le
      simpa [A, one_div, mul_comm] using
        (eLpNorm_le_of_ae_bound
          (μ := μK) (p := (2 : ℝ≥0∞)) hae)
    have hupper_tendsto :
        Filter.Tendsto
          (fun n : ℕ ↦ A * ENNReal.ofReal (δ n))
          Filter.atTop (𝓝 0) := by
      simpa using
        ENNReal.Tendsto.const_mul hδ_enn_tendsto (Or.inr hA_ne_top)
    exact
      tendsto_of_tendsto_of_tendsto_of_le_of_le
        (g := fun _ : ℕ ↦ (0 : ℝ≥0∞))
        (h := fun n : ℕ ↦ A * ENNReal.ofReal (δ n))
        tendsto_const_nhds hupper_tendsto
        (fun _ ↦ bot_le) hbound
  have hnorm_u :
      ∀ n : ℕ, ‖u n‖ ≤ L * ‖uF‖ := by
    intro n
    have hsmooth_bound :
        ‖greenSmoothDifferentialClass (g := g)
            (W n) (hW n)‖ ≤
          L * ‖greenSmoothDifferentialClass (g := g) F hF‖ := by
      simpa [W, hW] using
        smoothCompactlySupported_compSmoothZero_norm_le'
          (g := g) F hF (S n) (hS_smooth n) (hS_zero n)
          hL_nonneg (hS_deriv_bound n)
    have hcore_bound :
        ‖greenSmoothCoreElement (g := g) (W n) (hW n)‖ ≤
          L * ‖greenSmoothCoreElement (g := g) F hF‖ := by
      simpa [greenSmoothCoreElement] using hsmooth_bound
    simpa [u, uF, Ccore,
      GreenSobolevH10DirichletCore.norm_toCompletion] using hcore_bound
  have hbounded : ∃ B : ℝ, ∀ n : ℕ, ‖u n‖ ≤ B :=
    ⟨L * ‖uF‖, hnorm_u⟩
  rcases
    hilbert_bounded_sequence_has_strongly_convergent_tail_convex_averages
      (H := GreenSobolevH10SmoothCompactSupport g) u hbounded with
    ⟨uLim, uAvg, huAvg_mem, huAvg_tendsto⟩
  have hu_ball :
      ∀ n : ℕ, u n ∈ Metric.closedBall (0 : GreenSobolevH10SmoothCompactSupport g)
        (L * ‖uF‖) := by
    intro n
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm_u n
  have huAvg_ball :
      ∀ k : ℕ,
        uAvg k ∈ Metric.closedBall (0 : GreenSobolevH10SmoothCompactSupport g)
          (L * ‖uF‖) := by
    intro k
    exact
      (convexHull_min
        (s := u '' Set.Ici k)
        (t := Metric.closedBall
          (0 : GreenSobolevH10SmoothCompactSupport g) (L * ‖uF‖))
        (by
          intro y hy
          rcases hy with ⟨n, _hn, rfl⟩
          exact hu_ball n)
        (convex_closedBall (0 : GreenSobolevH10SmoothCompactSupport g)
          (L * ‖uF‖))) (huAvg_mem k)
  have huLim_ball :
      uLim ∈ Metric.closedBall (0 : GreenSobolevH10SmoothCompactSupport g)
        (L * ‖uF‖) :=
    Metric.isClosed_closedBall.mem_of_tendsto huAvg_tendsto
      (Filter.Eventually.of_forall huAvg_ball)
  have huLim_norm :
      ‖uLim‖ ≤ L * ‖uF‖ := by
    simpa [Metric.mem_closedBall, dist_zero_right] using huLim_ball
  rcases
    pureH10_mazurTailConvexAverages_diagonal_scalarRepresentative
      (g := g)
      (ψSeq := fun n : ℕ ↦ (W n).toFun)
      (ψ := fun x : X ↦ T (F.toFun x))
      u hrep hW_meas hTF_meas hW_local
      uAvg huAvg_mem huAvg_tendsto with
    ⟨V, hV, hV_tendsto, hV_local⟩
  refine ⟨V, hV, hV_tendsto.cauchySeq, hV_local, uLim, hV_tendsto, ?_⟩
  simpa [uF, Ccore] using huLim_norm

/--
%%handwave
name:
  Fixed smooth core function is stable under a Lipschitz zero-composition
statement:
  If \(F\) is compactly supported and smooth, and \(T:\mathbb R\to\mathbb R\)
  is Lipschitz with \(T(0)=0\), then \(T\circ F\) is represented by a Cauchy
  sequence of compactly supported smooth functions in the pure Dirichlet
  completion.  The representing sequence converges compact-locally in \(L^2\)
  to \(T\circ F\), and the pure Dirichlet norm is bounded by the Lipschitz
  constant times the norm of \(F\).
proof:
  Apply the fixed-smooth mollification result.
-/
theorem smoothCompactlySupported_lipschitzZeroComposition_coreApproximation
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [SecondCountableTopology X] [ComplexOneManifold X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (F : SmoothCompactlySupportedGlobalSurfaceFunction X)
    (hF : SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
      (SurfaceDifferentialField.ofCoordinateField F.gradient))
    {T : ℝ → ℝ} {L : ℝ}
    (hL_nonneg : 0 ≤ L)
    (hT_zero : T 0 = 0)
    (hT_lipschitz : ∀ s t : ℝ, |T s - T t| ≤ L * |s - t|) :
    ∃ V : ℕ → SmoothCompactlySupportedGlobalSurfaceFunction X,
    ∃ hV : ∀ n : ℕ,
      SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
        (SurfaceDifferentialField.ofCoordinateField (V n).gradient),
      CauchySeq
        (fun n : ℕ ↦
          (greenSobolevH10SmoothCompactSupportCore g).toCompletion
            (greenSmoothCoreElement (g := g) (V n) (hV n))) ∧
        (∀ K : Set X, IsCompact K →
          TendstoInLocalL2OnSurface g.volume K
            (fun n : ℕ ↦ (V n).toFun)
            (fun x : X ↦ T (F.toFun x))) ∧
        ∃ v : GreenSobolevH10SmoothCompactSupport g,
          Filter.Tendsto
            (fun n : ℕ ↦
              (greenSobolevH10SmoothCompactSupportCore g).toCompletion
                (greenSmoothCoreElement (g := g) (V n) (hV n)))
            Filter.atTop (𝓝 v) ∧
            ‖v‖ ≤ L *
              ‖(greenSobolevH10SmoothCompactSupportCore g).toCompletion
                (greenSmoothCoreElement (g := g) F hF)‖ := by
  exact
    smoothCompactlySupported_lipschitzZeroComposition_coreApproximation_of_mollification
      (g := g) F hF
      hL_nonneg hT_zero hT_lipschitz

/--
%%handwave
name:
  Pure normal-contraction core approximation via convexified tails
statement:
  If compactly supported smooth functions are Cauchy in the pure Dirichlet
  norm and converge compact-locally in \(L^2\) to \(f\), then composing with a
  Lipschitz map fixing zero gives a new compactly supported smooth sequence
  which is Cauchy in the pure Dirichlet norm and converges compact-locally to
  \(T\circ f\).
proof:
  First apply the fixed-smooth-function result to each \(F_n\), obtaining
  pure \(H^1_0\) elements represented by \(T\circ F_n\) with the uniform
  Dirichlet bound \(\|T\circ F_n\|_D\le L\|F_n\|_D\).  The original sequence
  is Cauchy, hence bounded, so these contracted elements form a bounded
  sequence in the Hilbert completion.  Mazur's lemma gives strongly
  convergent finite convex combinations of far tails.  The far-tail convex
  combinations still converge compact-locally in \(L^2\) to \(T\circ f\) by
  the Lipschitz inequality.  Finally approximate each finite convex
  combination by compactly supported smooth representatives and diagonalize.
-/
theorem pureH10_lipschitzZeroComposition_coreCauchyApproximation_via_mollification_mazur
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [SecondCountableTopology X] [ComplexOneManifold X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    {f : X → ℝ}
    (F : ℕ → SmoothCompactlySupportedGlobalSurfaceFunction X)
    (hF : ∀ n : ℕ,
      SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
        (SurfaceDifferentialField.ofCoordinateField (F n).gradient))
    (hF_cauchy :
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
          ‖greenSmoothCoreElement (g := g) (F n) (hF n) -
            greenSmoothCoreElement (g := g) (F m) (hF m)‖ < ε)
    (hF_local :
      ∀ K : Set X, IsCompact K →
        TendstoInLocalL2OnSurface g.volume K
          (fun n : ℕ ↦ (F n).toFun)
          f)
    (hf_meas :
      ∀ K : Set X, IsCompact K →
        AEStronglyMeasurable f (g.volume.restrict K))
    {T : ℝ → ℝ} {L : ℝ}
    (hL_nonneg : 0 ≤ L)
    (hT_zero : T 0 = 0)
    (hT_lipschitz : ∀ s t : ℝ, |T s - T t| ≤ L * |s - t|) :
  ∃ V : ℕ → SmoothCompactlySupportedGlobalSurfaceFunction X,
  ∃ hV : ∀ n : ℕ,
    SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
      (SurfaceDifferentialField.ofCoordinateField (V n).gradient),
    CauchySeq
      (fun n : ℕ ↦
        (greenSobolevH10SmoothCompactSupportCore g).toCompletion
          (greenSmoothCoreElement (g := g) (V n) (hV n))) ∧
      ∀ K : Set X, IsCompact K →
        TendstoInLocalL2OnSurface g.volume K
          (fun n : ℕ ↦ (V n).toFun)
          (fun x : X ↦ T (f x)) := by
  let H : Type _ := GreenSobolevH10SmoothCompactSupport g
  have hfixed :
      ∀ n : ℕ,
        ∃ v : H,
          HasPureH10ScalarRepresentative v
            (fun x : X ↦ T ((F n).toFun x)) ∧
            ‖v‖ ≤ L *
              ‖(greenSobolevH10SmoothCompactSupportCore g).toCompletion
                (greenSmoothCoreElement (g := g) (F n) (hF n))‖ := by
    intro n
    rcases
      smoothCompactlySupported_lipschitzZeroComposition_coreApproximation
        (g := g) (F n) (hF n) hL_nonneg hT_zero hT_lipschitz with
      ⟨Vn, hVn, hVn_cauchy, hVn_local, v, hv_tendsto, hv_norm⟩
    refine ⟨v, ?_, hv_norm⟩
    exact ⟨Vn, hVn, hv_tendsto, hVn_local⟩
  choose uT huT using hfixed
  have huT_rep :
      ∀ n : ℕ,
        HasPureH10ScalarRepresentative (uT n)
          (fun x : X ↦ T ((F n).toFun x)) := by
    intro n
    exact (huT n).1
  have huT_norm :
      ∀ n : ℕ,
        ‖uT n‖ ≤ L *
          ‖(greenSobolevH10SmoothCompactSupportCore g).toCompletion
            (greenSmoothCoreElement (g := g) (F n) (hF n))‖ := by
    intro n
    exact (huT n).2
  rcases
    greenSmoothCoreElement_toCompletion_norm_bounded_of_core_norm_cauchy
      (g := g) F hF hF_cauchy with
    ⟨C0, hC0⟩
  have huT_bounded : ∃ C : ℝ, ∀ n : ℕ, ‖uT n‖ ≤ C := by
    refine ⟨max 0 (L * C0), ?_⟩
    intro n
    have hmul :
        L *
          ‖(greenSobolevH10SmoothCompactSupportCore g).toCompletion
            (greenSmoothCoreElement (g := g) (F n) (hF n))‖ ≤
          L * C0 :=
      mul_le_mul_of_nonneg_left (hC0 n) hL_nonneg
    exact (huT_norm n).trans (hmul.trans (le_max_right _ _))
  rcases
    hilbert_bounded_sequence_has_strongly_convergent_tail_convex_averages
      (H := H) uT huT_bounded with
    ⟨uLim, uAvg, huAvg_mem, huAvg_tendsto⟩
  have hTF_local :
      ∀ K : Set X, IsCompact K →
        TendstoInLocalL2OnSurface g.volume K
          (fun n : ℕ ↦ fun x : X ↦ T ((F n).toFun x))
          (fun x : X ↦ T (f x)) := by
    intro K hK
    exact (hF_local K hK).comp_lipschitz hL_nonneg hT_lipschitz
  have hT_cont : Continuous T :=
    continuous_of_real_lipschitz_bound hL_nonneg hT_lipschitz
  have hTFSeq_meas :
      ∀ n : ℕ, ∀ K : Set X, IsCompact K →
        AEStronglyMeasurable
          (fun x : X ↦ T ((F n).toFun x)) (g.volume.restrict K) := by
    intro n K hK
    exact
      hT_cont.comp_aestronglyMeasurable
        (((F n).memLp_restrict_compact (g := g) hK).aestronglyMeasurable)
  have hTf_meas :
      ∀ K : Set X, IsCompact K →
        AEStronglyMeasurable
          (fun x : X ↦ T (f x)) (g.volume.restrict K) := by
    intro K hK
    exact hT_cont.comp_aestronglyMeasurable (hf_meas K hK)
  exact
    pureH10_mazurTailConvexAverages_smoothCoreApproximation
      (g := g)
      (ψSeq := fun n : ℕ ↦ fun x : X ↦ T ((F n).toFun x))
      (ψ := fun x : X ↦ T (f x))
      uT huT_rep hTFSeq_meas hTf_meas hTF_local
      uAvg huAvg_mem huAvg_tendsto

/--
%%handwave
name:
  Lipschitz composition preserves pure-Cauchy smooth core sequences
statement:
  If compactly supported smooth primitives are Cauchy in the pure Dirichlet
  norm and converge compact-locally in \(L^2\) to \(f\), then composing with a
  Lipschitz map fixing zero gives a new smooth core sequence which is Cauchy in
  the pure Dirichlet norm and converges compact-locally to \(T\circ f\).
proof:
  First close the fixed smooth-core composition using smooth zero-preserving
  mollifiers with the same Lipschitz bound.  The contracted smooth-core
  sequence is bounded in the pure Hilbert completion.
  Mazur's lemma turns a weakly convergent subsequence into strongly
  convergent finite convex combinations of tails.  These tail averages retain
  the compact-local \(L^2\) limit \(T\circ f\), and a final diagonal
  approximation by compactly supported smooth primitives gives the desired
  Cauchy sequence.
-/
theorem pureH10_lipschitzZeroComposition_coreCauchyApproximation
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [SecondCountableTopology X] [ComplexOneManifold X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    {f : X → ℝ}
    (F : ℕ → SmoothCompactlySupportedGlobalSurfaceFunction X)
    (hF : ∀ n : ℕ,
      SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
        (SurfaceDifferentialField.ofCoordinateField (F n).gradient))
    (hF_cauchy :
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
          ‖greenSmoothCoreElement (g := g) (F n) (hF n) -
            greenSmoothCoreElement (g := g) (F m) (hF m)‖ < ε)
    (hF_local :
      ∀ K : Set X, IsCompact K →
        TendstoInLocalL2OnSurface g.volume K
          (fun n : ℕ ↦ (F n).toFun)
          f)
    (hf_meas :
      ∀ K : Set X, IsCompact K →
        AEStronglyMeasurable f (g.volume.restrict K))
    {T : ℝ → ℝ} {L : ℝ}
    (hL_nonneg : 0 ≤ L)
    (hT_zero : T 0 = 0)
    (hT_lipschitz : ∀ s t : ℝ, |T s - T t| ≤ L * |s - t|) :
  ∃ V : ℕ → SmoothCompactlySupportedGlobalSurfaceFunction X,
  ∃ hV : ∀ n : ℕ,
    SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
      (SurfaceDifferentialField.ofCoordinateField (V n).gradient),
    CauchySeq
      (fun n : ℕ ↦
        (greenSobolevH10SmoothCompactSupportCore g).toCompletion
          (greenSmoothCoreElement (g := g) (V n) (hV n))) ∧
      ∀ K : Set X, IsCompact K →
        TendstoInLocalL2OnSurface g.volume K
          (fun n : ℕ ↦ (V n).toFun)
          (fun x : X ↦ T (f x)) := by
  exact
    pureH10_lipschitzZeroComposition_coreCauchyApproximation_via_mollification_mazur
      (g := g) (f := f) F hF hF_cauchy hF_local hf_meas
      hL_nonneg hT_zero hT_lipschitz

/--
%%handwave
name:
  Contracted core approximation theorem
statement:
  Given a smooth-core representative sequence for a pure homogeneous
  zero-trace class and a Lipschitz map fixing zero, there is another smooth
  core sequence which is Cauchy in the pure completion and whose primitives
  converge compact-locally to the contracted scalar limit.
proof:
  Approximate the Lipschitz contraction by smooth zero-preserving contractions,
  apply the smooth chain rule and Dirichlet contraction estimate, and pass to
  a diagonal smooth-core sequence.
-/
theorem pureH10_normalContraction_exists_coreApproximation
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [SecondCountableTopology X] [ComplexOneManifold X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    {u : GreenSobolevH10SmoothCompactSupport g} {f : X → ℝ}
    (F : ℕ → SmoothCompactlySupportedGlobalSurfaceFunction X)
    (hF : ∀ n : ℕ,
      SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
        (SurfaceDifferentialField.ofCoordinateField (F n).gradient))
    (hF_tendsto :
      Filter.Tendsto
        (fun n : ℕ ↦
          (greenSobolevH10SmoothCompactSupportCore g).toCompletion
            (greenSmoothCoreElement (g := g) (F n) (hF n)))
        Filter.atTop (𝓝 u))
    (hF_local :
      ∀ K : Set X, IsCompact K →
        TendstoInLocalL2OnSurface g.volume K
          (fun n : ℕ ↦ (F n).toFun)
          f)
    (hf_meas :
      ∀ K : Set X, IsCompact K →
        AEStronglyMeasurable f (g.volume.restrict K))
    {T : ℝ → ℝ} {L : ℝ}
    (hL_nonneg : 0 ≤ L)
    (hT_zero : T 0 = 0)
    (hT_lipschitz : ∀ s t : ℝ, |T s - T t| ≤ L * |s - t|) :
  ∃ V : ℕ → SmoothCompactlySupportedGlobalSurfaceFunction X,
  ∃ hV : ∀ n : ℕ,
    SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
      (SurfaceDifferentialField.ofCoordinateField (V n).gradient),
    CauchySeq
      (fun n : ℕ ↦
        (greenSobolevH10SmoothCompactSupportCore g).toCompletion
          (greenSmoothCoreElement (g := g) (V n) (hV n))) ∧
      ∀ K : Set X, IsCompact K →
        TendstoInLocalL2OnSurface g.volume K
          (fun n : ℕ ↦ (V n).toFun)
          (fun x : X ↦ T (f x)) := by
  exact
    pureH10_lipschitzZeroComposition_coreCauchyApproximation
      (g := g) (f := f) F hF
      (greenSobolevH10SmoothCompactSupportCore_norm_cauchy_of_tendsto_completion
        (fun n : ℕ ↦ greenSmoothCoreElement (g := g) (F n) (hF n))
        u hF_tendsto)
      hF_local hf_meas hL_nonneg hT_zero hT_lipschitz

/--
%%handwave
name:
  Lipschitz composition passes to pure approximating sequences
statement:
  Let a completed pure zero-trace class be represented by compactly supported
  smooth primitives \(F_n\) converging in pure Dirichlet norm and compact-local
  \(L^2\) to \(f\).  If \(T\) is Lipschitz and \(T(0)=0\), then the functions
  \(T\circ F_n\) converge to a completed pure zero-trace class whose scalar
  representative is \(T\circ f\).
proof:
  Apply the one-function Lipschitz composition theorem to each approximant.
  The Sobolev chain-rule continuity for normal contractions shows the
  composed approximants are Cauchy in the pure Dirichlet norm, and compact
  local \(L^2\) convergence follows from the pointwise Lipschitz inequality.
-/
theorem pureH10_normalContraction_coreSequence_has_scalarRepresentative
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [SecondCountableTopology X] [ComplexOneManifold X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    {u : GreenSobolevH10SmoothCompactSupport g} {f : X → ℝ}
    (F : ℕ → SmoothCompactlySupportedGlobalSurfaceFunction X)
    (hF : ∀ n : ℕ,
      SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
        (SurfaceDifferentialField.ofCoordinateField (F n).gradient))
    (hF_tendsto :
      Filter.Tendsto
        (fun n : ℕ ↦
          (greenSobolevH10SmoothCompactSupportCore g).toCompletion
            (greenSmoothCoreElement (g := g) (F n) (hF n)))
        Filter.atTop (𝓝 u))
    (hF_local :
      ∀ K : Set X, IsCompact K →
        TendstoInLocalL2OnSurface g.volume K
          (fun n : ℕ ↦ (F n).toFun)
          f)
    (hf_meas :
      ∀ K : Set X, IsCompact K →
        AEStronglyMeasurable f (g.volume.restrict K))
    {T : ℝ → ℝ} {L : ℝ}
    (hL_nonneg : 0 ≤ L)
    (hT_zero : T 0 = 0)
    (hT_lipschitz : ∀ s t : ℝ, |T s - T t| ≤ L * |s - t|) :
    ∃ v : GreenSobolevH10SmoothCompactSupport g,
      HasPureH10ScalarRepresentative v (fun x : X ↦ T (f x)) := by
  rcases
    pureH10_normalContraction_exists_coreApproximation
      (g := g) (u := u) (f := f) F hF hF_tendsto hF_local hf_meas
      hL_nonneg hT_zero hT_lipschitz with
    ⟨V, hV, hV_cauchy, hV_local⟩
  rcases cauchySeq_tendsto_of_complete hV_cauchy with
    ⟨v, hv_tendsto⟩
  exact ⟨v, ⟨V, hV, hv_tendsto, by
    intro K hK
    simpa using hV_local K hK⟩⟩

/--
%%handwave
name:
  Normal contractions preserve pure zero trace
statement:
  If \(u\) has a pure homogeneous zero-trace scalar representative \(f\) and
  \(T:\mathbb R\to\mathbb R\) is Lipschitz with \(T(0)=0\), then \(T\circ f\)
  also represents a pure homogeneous zero-trace class.
proof:
  Choose the explicit compactly supported smooth primitive sequence in the
  scalar representative of \(u\).  Apply the core approximation theorem based
  on fixed smooth-core composition, boundedness in the pure Hilbert
  completion, Mazur convexification of far tails, and compact-local \(L^2\)
  stability under Lipschitz composition.  Completeness of the pure Hilbert
  completion supplies the class represented by \(T\circ f\).
-/
theorem pureH10_normalContraction_has_scalarRepresentative
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [SecondCountableTopology X] [ComplexOneManifold X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    {u : GreenSobolevH10SmoothCompactSupport g} {f : X → ℝ}
    (hrep : HasPureH10ScalarRepresentative u f)
    (hf_meas :
      ∀ K : Set X, IsCompact K →
        AEStronglyMeasurable f (g.volume.restrict K))
    {T : ℝ → ℝ} {L : ℝ}
    (hL_nonneg : 0 ≤ L)
    (hT_zero : T 0 = 0)
    (hT_lipschitz : ∀ s t : ℝ, |T s - T t| ≤ L * |s - t|) :
    ∃ v : GreenSobolevH10SmoothCompactSupport g,
      HasPureH10ScalarRepresentative v (fun x : X ↦ T (f x)) := by
  rcases hrep with ⟨F, hF, hF_tendsto, hF_local⟩
  exact
    pureH10_normalContraction_coreSequence_has_scalarRepresentative
      (g := g) (u := u) (f := f) F hF hF_tendsto hF_local hf_meas
      hL_nonneg hT_zero hT_lipschitz

/--
%%handwave
name:
  Fixed-level clipping function
statement:
  The fixed-level clipping function for \(0<b<a\) is zero below level \(b\),
  affine between \(b\) and \(a\), and one above level \(a\).
-/
noncomputable def fixedLevelClip (b a : ℝ) : ℝ → ℝ :=
  fun t : ℝ ↦ min (1 : ℝ) (max (0 : ℝ) ((t - b) / (a - b)))

/--
%%handwave
name:
  Fixed-level clipping vanishes below the lower level
statement:
  The fixed-level clipping function is zero at every point whose value is at
  most the lower level.
proof:
  The affine middle expression is nonpositive there, so the positive part is
  zero and the final minimum is still zero.
-/
theorem fixedLevelClip_eq_zero_of_le
    {b a t : ℝ} (hba : b < a) (ht : t ≤ b) :
    fixedLevelClip b a t = 0 := by
  have hden_nonneg : 0 ≤ a - b := sub_nonneg.mpr hba.le
  have hfrac_nonpos : (t - b) / (a - b) ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) hden_nonneg
  have hmax : max (0 : ℝ) ((t - b) / (a - b)) = 0 :=
    max_eq_left hfrac_nonpos
  simp [fixedLevelClip, hmax]

/--
%%handwave
name:
  Fixed-level clipping is one above the upper level
statement:
  The fixed-level clipping function is one at every point whose value is at
  least the upper level.
proof:
  The affine middle expression is at least one there, so the positive part is
  at least one and the final minimum is one.
-/
theorem fixedLevelClip_eq_one_of_ge
    {b a t : ℝ} (hba : b < a) (ht : a ≤ t) :
    fixedLevelClip b a t = 1 := by
  have hden_pos : 0 < a - b := sub_pos.mpr hba
  have hden_ne : a - b ≠ 0 := hden_pos.ne'
  have hnum_ge : a - b ≤ t - b := sub_le_sub_right ht b
  have hone : (1 : ℝ) = (a - b) / (a - b) := by
    field_simp [hden_ne]
  have hfrac_ge : (1 : ℝ) ≤ (t - b) / (a - b) := by
    rw [hone]
    exact div_le_div_of_nonneg_right hnum_ge hden_pos.le
  have hle_max :
      (1 : ℝ) ≤ max (0 : ℝ) ((t - b) / (a - b)) :=
    le_trans hfrac_ge (le_max_right _ _)
  simp [fixedLevelClip, min_eq_left hle_max]

/--
%%handwave
name:
  Fixed-level clipping is one only above the upper level
statement:
  If \(b<a\) and the fixed-level clipping function has value one at \(t\),
  then \(t\) is at least the upper clipping level.
proof:
  The value one can only come from the affine middle expression being at
  least one.  Multiplying by the positive denominator \(a-b\) gives
  \(a\le t\).
-/
theorem fixedLevelClip_eq_one_iff_ge
    {b a t : ℝ} (hba : b < a) :
    fixedLevelClip b a t = 1 ↔ a ≤ t := by
  constructor
  · intro hclip
    have hden_pos : 0 < a - b := sub_pos.mpr hba
    have hden_ne : a - b ≠ 0 := hden_pos.ne'
    have hmax_ge :
        1 ≤ max (0 : ℝ) ((t - b) / (a - b)) := by
      have hmin :
          min (1 : ℝ) (max (0 : ℝ) ((t - b) / (a - b))) = 1 := by
        simpa [fixedLevelClip] using hclip
      have hmin_le :
          min (1 : ℝ) (max (0 : ℝ) ((t - b) / (a - b))) ≤
            max (0 : ℝ) ((t - b) / (a - b)) :=
        min_le_right _ _
      simpa [hmin] using hmin_le
    have hfrac_ge : 1 ≤ (t - b) / (a - b) := by
      by_contra hnot
      have hfrac_lt : (t - b) / (a - b) < 1 := lt_of_not_ge hnot
      have hmax_lt : max (0 : ℝ) ((t - b) / (a - b)) < 1 :=
        max_lt (by norm_num) hfrac_lt
      linarith
    have hmul :
        (1 : ℝ) * (a - b) ≤
          ((t - b) / (a - b)) * (a - b) :=
      mul_le_mul_of_nonneg_right hfrac_ge hden_pos.le
    have hmul_simp : a - b ≤ t - b := by
      simpa [hden_ne] using hmul
    linarith
  · exact fixedLevelClip_eq_one_of_ge hba

/--
%%handwave
name:
  Fixed-level clipping is zero only below the lower level
statement:
  If \(b<a\) and the fixed-level clipping function has value zero at \(t\),
  then \(t\) is at most the lower clipping level.
proof:
  The positive part of the affine middle expression must vanish.  Therefore
  that affine expression is nonpositive, and multiplying by \(a-b>0\) gives
  \(t\le b\).
-/
theorem fixedLevelClip_eq_zero_iff_le
    {b a t : ℝ} (hba : b < a) :
    fixedLevelClip b a t = 0 ↔ t ≤ b := by
  constructor
  · intro hclip
    have hden_pos : 0 < a - b := sub_pos.mpr hba
    have hden_ne : a - b ≠ 0 := hden_pos.ne'
    have hmax_nonpos :
        max (0 : ℝ) ((t - b) / (a - b)) ≤ 0 := by
      have hmin :
          min (1 : ℝ) (max (0 : ℝ) ((t - b) / (a - b))) = 0 := by
        simpa [fixedLevelClip] using hclip
      have hmax_nonneg :
          0 ≤ max (0 : ℝ) ((t - b) / (a - b)) :=
        le_max_left _ _
      by_contra hnot
      have hmax_pos : 0 < max (0 : ℝ) ((t - b) / (a - b)) :=
        lt_of_not_ge hnot
      have hmin_pos :
          0 < min (1 : ℝ) (max (0 : ℝ) ((t - b) / (a - b))) :=
        lt_min (by norm_num) hmax_pos
      linarith
    have hfrac_nonpos : (t - b) / (a - b) ≤ 0 :=
      le_trans (le_max_right _ _) hmax_nonpos
    have hmul :
        ((t - b) / (a - b)) * (a - b) ≤ 0 * (a - b) :=
      mul_le_mul_of_nonneg_right hfrac_nonpos hden_pos.le
    have hmul_simp : t - b ≤ 0 := by
      simpa [hden_ne] using hmul
    linarith
  · exact fixedLevelClip_eq_zero_of_le hba

/--
%%handwave
name:
  Fixed-level clipping is a normal contraction
statement:
  For \(0<b<a\), the fixed-level clipping function fixes zero and is
  Lipschitz.
proof:
  The affine middle part has slope \((a-b)^{-1}\), and the operations
  \(t\mapsto\max(0,t)\) and \(t\mapsto\min(1,t)\) are one-Lipschitz.
-/
theorem fixedLevelClip_normalContraction
    {b a : ℝ} (hb_pos : 0 < b) (hba : b < a) :
    fixedLevelClip b a 0 = 0 ∧
      ∃ L : ℝ, 0 ≤ L ∧
        ∀ s t : ℝ,
          |fixedLevelClip b a s - fixedLevelClip b a t| ≤ L * |s - t| := by
  have hden_pos : 0 < a - b := sub_pos.mpr hba
  have hden_ne : a - b ≠ 0 := hden_pos.ne'
  let L : ℝ := 1 / (a - b)
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    simpa [one_div] using inv_nonneg.mpr hden_pos.le
  have hzero_frac : (0 - b) / (a - b) ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hden_pos.le
  have hzero_max : max (0 : ℝ) ((0 - b) / (a - b)) = 0 :=
    max_eq_left hzero_frac
  have hzero : fixedLevelClip b a 0 = 0 := by
    have hzero_max' : max (0 : ℝ) (-b / (a - b)) = 0 := by
      simpa using hzero_max
    simp [fixedLevelClip, hzero_max']
  have haffine :
      LipschitzWith (Real.toNNReal L)
        (fun s : ℝ ↦ (s - b) / (a - b)) := by
    refine LipschitzWith.of_dist_le' ?_
    intro s t
    refine le_of_eq ?_
    calc
      dist ((s - b) / (a - b)) ((t - b) / (a - b)) =
          |(s - b) / (a - b) - (t - b) / (a - b)| := by
        rw [Real.dist_eq]
      _ = |(s - t) / (a - b)| := by
        congr 1
        field_simp [hden_ne]
        ring
      _ = |s - t| / |a - b| := by
        rw [abs_div]
      _ = |s - t| / (a - b) := by
        rw [abs_of_pos hden_pos]
      _ = L * dist s t := by
        rw [Real.dist_eq]
        ring
  have hclip : LipschitzWith (Real.toNNReal L) (fixedLevelClip b a) := by
    simpa [fixedLevelClip, L] using
      (haffine.const_max (0 : ℝ)).const_min (1 : ℝ)
  refine ⟨hzero, ⟨L, hL_nonneg, ?_⟩⟩
  intro s t
  have hdist := hclip.dist_le_mul s t
  have hL_coe : (↑(Real.toNNReal L) : ℝ) = L := by
    exact congrArg (fun r : NNReal ↦ (r : ℝ))
      (Real.toNNReal_of_nonneg hL_nonneg)
  simpa [Real.dist_eq, hL_coe] using hdist

/--
%%handwave
name:
  Global signed fixed-level clip
statement:
  The global signed fixed-level clip of a function is obtained by applying
  the fixed-level clipping function to either \(G\) or \(-G\).
-/
noncomputable def fixedLevelSignedClip {X : Type}
    (G : X → ℝ) (σ : ℝ) (b a : ℝ) : X → ℝ :=
  fun x : X ↦ fixedLevelClip b a (σ * G x)

/--
%%handwave
name:
  Fixed-level clipping is nonnegative
statement:
  The fixed-level clipping function takes nonnegative values.
proof:
  Unfold the clipping function.  It is the minimum of one and the maximum of zero with an affine expression, hence is nonnegative.
-/
theorem fixedLevelClip_nonneg
    {b a t : ℝ} :
    0 ≤ fixedLevelClip b a t := by
  unfold fixedLevelClip
  exact le_min zero_le_one (le_max_left _ _)

/--
%%handwave
name:
  Fixed-level clipping is positive above the lower level
statement:
  If \(b<a\) and \(t>b\), then the fixed-level clipping function is strictly
  positive at \(t\).
proof:
  The clipping function is nonnegative.  If its value were zero, the
  zero-level characterization would force \(t\le b\), contradicting \(t>b\).
-/
theorem fixedLevelClip_pos_of_lt
    {b a t : ℝ} (hba : b < a) (hlt : b < t) :
    0 < fixedLevelClip b a t := by
  have hnonneg : 0 ≤ fixedLevelClip b a t :=
    fixedLevelClip_nonneg (b := b) (a := a) (t := t)
  have hne : fixedLevelClip b a t ≠ 0 := by
    intro hzero
    have ht_le : t ≤ b :=
      (fixedLevelClip_eq_zero_iff_le (b := b) (a := a) (t := t) hba).1
        hzero
    linarith
  exact lt_of_le_of_ne hnonneg hne.symm

/--
%%handwave
name:
  Signed fixed-level clipping is positive above the lower signed level
statement:
  If the signed value \(\sigma G(x)\) is larger than \(b\), then the signed
  fixed-level clip is strictly positive at \(x\).
proof:
  The strict signed-level inequality places the value above the lower clipping threshold, so the corresponding branch of the clip is strictly positive.
-/
theorem fixedLevelSignedClip_pos_of_signed_level_gt
    {X : Type} {G : X → ℝ} {σ b a : ℝ} {x : X}
    (hba : b < a) (hx : b < σ * G x) :
    0 < fixedLevelSignedClip G σ b a x := by
  simpa [fixedLevelSignedClip] using
    fixedLevelClip_pos_of_lt (b := b) (a := a)
      (t := σ * G x) hba hx

/--
%%handwave
name:
  Fixed-level clipping is unchanged by a plateau splice
statement:
  Let \(0<b<a\) and let the cutoff \(F\) take values in \([0,1]\).  If
  \(F\) is supported where the signed fixed-level clip of \(G\) is already
  equal to its pole plateau, then replacing \(G\) by the convex splice with
  the corresponding plateau anchor does not change the signed fixed-level
  clip, away from the pole and at points where the raw representative agrees
  with \(G\).
proof:
  Off the support of \(F\) the splice is the original value.  On the support,
  the positive clip case has \(G\ge a\), so the convex splice between \(G\)
  and \(a\) remains at least \(a\).  The negative clip case has \(-G\le b\),
  so the convex splice between \(-G\) and \(0\) remains at most \(b\).
-/
theorem fixedLevelSignedClip_splice_eq_of_raw_eq
    {X : Type} [TopologicalSpace X] {p : X} {raw G F : X → ℝ}
    {σ b a : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hb_pos : 0 < b) (hba : b < a)
    (hF_bounds : ∀ x : X, 0 ≤ F x ∧ F x ≤ 1)
    (hsupport_const :
      closure {x : X | F x ≠ 0} ⊆
        {x : X | x = p ∨
          fixedLevelSignedClip G σ b a x =
            if σ = 1 then (1 : ℝ) else 0})
    {x : X} (hx_ne : x ≠ p) (hraw_eq : raw x = G x) :
    fixedLevelSignedClip
        (fun y : X ↦
          (1 - F y) * raw y +
            (if σ = 1 then a else 0) * F y)
        σ b a x =
      fixedLevelSignedClip G σ b a x := by
  rcases hσ with rfl | rfl
  · by_cases hFx : F x = 0
    · simp [fixedLevelSignedClip, hFx, hraw_eq]
    · have hclipG :
          fixedLevelSignedClip G 1 b a x = 1 := by
        have hx_support : x ∈ closure {y : X | F y ≠ 0} :=
          subset_closure hFx
        have hx_or := hsupport_const hx_support
        rcases hx_or with hxp | hclip
        · exact False.elim (hx_ne hxp)
        · simpa using hclip
      have hG_ge : a ≤ G x := by
        exact (fixedLevelClip_eq_one_iff_ge (b := b) (a := a)
          (t := G x) hba).1 (by
            simpa [fixedLevelSignedClip] using hclipG)
      have hsplice_ge :
          a ≤ (1 - F x) * raw x + a * F x := by
        rw [hraw_eq]
        have hF0 : 0 ≤ F x := (hF_bounds x).1
        have hF1 : F x ≤ 1 := (hF_bounds x).2
        nlinarith
      have hclip_splice :
          fixedLevelSignedClip
              (fun y : X ↦ (1 - F y) * raw y + a * F y)
              1 b a x = 1 := by
        simpa [fixedLevelSignedClip] using
          fixedLevelClip_eq_one_of_ge (b := b) (a := a) hba hsplice_ge
      simpa [fixedLevelSignedClip] using hclip_splice.trans hclipG.symm
  · by_cases hFx : F x = 0
    · simp [fixedLevelSignedClip, hFx, hraw_eq]
    · have hclipG :
          fixedLevelSignedClip G (-1) b a x = 0 := by
        have hx_support : x ∈ closure {y : X | F y ≠ 0} :=
          subset_closure hFx
        have hx_or := hsupport_const hx_support
        rcases hx_or with hxp | hclip
        · exact False.elim (hx_ne hxp)
        · have hne : (-1 : ℝ) ≠ 1 := by norm_num
          simpa [hne] using hclip
      have hnegG_le : (-1 : ℝ) * G x ≤ b := by
        exact (fixedLevelClip_eq_zero_iff_le (b := b) (a := a)
          (t := (-1 : ℝ) * G x) hba).1 (by
            simpa [fixedLevelSignedClip] using hclipG)
      have hsplice_le :
          (-1 : ℝ) *
              ((1 - F x) * raw x + (0 : ℝ) * F x) ≤ b := by
        rw [hraw_eq]
        have hF0 : 0 ≤ F x := (hF_bounds x).1
        have hF1 : F x ≤ 1 := (hF_bounds x).2
        have hone_minus_nonneg : 0 ≤ 1 - F x := by linarith
        have hone_minus_le_one : 1 - F x ≤ 1 := by linarith
        have hmul1 :
            (1 - F x) * ((-1 : ℝ) * G x) ≤
              (1 - F x) * b :=
          mul_le_mul_of_nonneg_left hnegG_le hone_minus_nonneg
        have hmul2 : (1 - F x) * b ≤ b := by
          have hmul :=
            mul_le_mul_of_nonneg_right hone_minus_le_one hb_pos.le
          simpa using hmul
        calc
          (-1 : ℝ) * ((1 - F x) * G x + (0 : ℝ) * F x)
              = (1 - F x) * ((-1 : ℝ) * G x) := by ring
          _ ≤ (1 - F x) * b := hmul1
          _ ≤ b := hmul2
      have hclip_splice :
          fixedLevelSignedClip
              (fun y : X ↦ (1 - F y) * raw y + (0 : ℝ) * F y)
              (-1) b a x = 0 := by
        simpa [fixedLevelSignedClip] using
          fixedLevelClip_eq_zero_of_le (b := b) (a := a) hba hsplice_le
      have hne : (-1 : ℝ) ≠ 1 := by norm_num
      simpa [fixedLevelSignedClip, hne] using hclip_splice.trans hclipG.symm

/--
%%handwave
name:
  Signed fixed-level clipping preserves pure zero trace away from singularities
statement:
  If a scalar function represents a pure homogeneous zero-trace class, then
  its signed fixed-level clip also represents a pure homogeneous zero-trace
  class.
proof:
  The signed fixed-level clipping map is a Lipschitz map of the scalar
  variable which fixes zero.  Apply the normal-contraction theorem for the
  pure homogeneous space.
-/
theorem fixedLevelSignedClip_of_pureH10_scalarRepresentative
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [SecondCountableTopology X] [ComplexOneManifold X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    {u : GreenSobolevH10SmoothCompactSupport g} {f : X → ℝ}
    (hrep : HasPureH10ScalarRepresentative u f)
    (hf_meas :
      ∀ K : Set X, IsCompact K →
        AEStronglyMeasurable f (g.volume.restrict K))
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    {b a : ℝ} (hb_pos : 0 < b) (hba : b < a) :
    ∃ v : GreenSobolevH10SmoothCompactSupport g,
      HasPureH10ScalarRepresentative v
        (fixedLevelSignedClip f σ b a) := by
  rcases fixedLevelClip_normalContraction hb_pos hba with
    ⟨hclip_zero, L, hL_nonneg, hclip_lipschitz⟩
  rcases hσ with rfl | rfl
  · have hres :
        ∃ v : GreenSobolevH10SmoothCompactSupport g,
          HasPureH10ScalarRepresentative v
            (fun x : X ↦ fixedLevelClip b a (f x)) :=
      pureH10_normalContraction_has_scalarRepresentative
        (g := g) (u := u) (f := f) hrep hf_meas
        hL_nonneg hclip_zero hclip_lipschitz
    rcases hres with ⟨v, hv⟩
    refine ⟨v, ?_⟩
    change
      HasPureH10ScalarRepresentative v
        (fun x : X ↦ fixedLevelClip b a ((1 : ℝ) * f x))
    simpa using hv
  · let T : ℝ → ℝ := fun t : ℝ ↦ fixedLevelClip b a (-t)
    have hT_zero : T 0 = 0 := by
      simpa [T] using hclip_zero
    have hT_lipschitz :
        ∀ s t : ℝ, |T s - T t| ≤ L * |s - t| := by
      intro s t
      have hraw := hclip_lipschitz (-s) (-t)
      have hσ_abs : |-s + t| = |s - t| := by
        have hlin : -s + t = -(s - t) := by
          ring
        rw [hlin, abs_neg]
      simpa [T, hσ_abs] using hraw
    have hres :
        ∃ v : GreenSobolevH10SmoothCompactSupport g,
          HasPureH10ScalarRepresentative v
            (fun x : X ↦ T (f x)) :=
      pureH10_normalContraction_has_scalarRepresentative
        (g := g) (u := u) (f := f) hrep hf_meas
        hL_nonneg hT_zero hT_lipschitz
    rcases hres with ⟨v, hv⟩
    refine ⟨v, ?_⟩
    change
      HasPureH10ScalarRepresentative v
        (fun x : X ↦ fixedLevelClip b a ((-1 : ℝ) * f x))
    simpa [T] using hv

/--
%%handwave
name:
  Signed fixed-level clips of the Riesz correction are pure zero-trace representatives
statement:
  The signed fixed-level clip of the scalar Riesz correction represents a
  pure homogeneous zero-trace class.
proof:
  The decoded Riesz correction has a pure homogeneous zero-trace scalar
  representative.  The fixed-level signed clip is a Lipschitz normal
  contraction, so it preserves the pure homogeneous class.
-/
theorem fixedLevelSignedClip_correction_has_pureH10_scalarRepresentative
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [RiemannSurface X]
    [MeasurableEq X] [SecondCountableTopology X] [ComplexOneManifold X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    {φ : LogarithmicCutoffPoleModel g p}
    {source : (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ}
    (hdata :
      GreenSobolevH10SmoothCompactSupportLocalWeakCorrectionData
        φ source)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    {b a : ℝ} (hb_pos : 0 < b) (hba : b < a) :
    ∃ v : GreenSobolevH10SmoothCompactSupport g,
      HasPureH10ScalarRepresentative v
        (fixedLevelSignedClip hdata.correction.toFun σ b a) := by
  have hcorr_rep :
      HasPureH10ScalarRepresentative
        (greenSobolevH10SmoothCompactSupportRieszVector source)
        hdata.correction.toFun :=
    rieszLocalCorrection_has_pureH10_scalarRepresentative hdata
  have hcorr_meas :
      ∀ K : Set X, IsCompact K →
        AEStronglyMeasurable hdata.correction.toFun
          (g.volume.restrict K) := by
    intro K hK
    have hm : MemLp hdata.scalar.toFun 2 (g.volume.restrict K) :=
      hdata.scalar.primitive_memLp_local K hK
    simpa [hdata.correction_toFun_eq_scalar] using
      hm.aestronglyMeasurable
  exact
    fixedLevelSignedClip_of_pureH10_scalarRepresentative
      (g := g) hcorr_rep hcorr_meas hσ hb_pos hba

/--
%%handwave
name:
  Spliced fixed-level clips are pure zero-trace representatives
statement:
  Let a smooth compactly supported cutoff be equal to one near the logarithmic
  pole.  The signed fixed-level clip of the potential obtained by replacing
  the local energy potential near the pole by the corresponding clipping
  plateau anchor represents a pure homogeneous zero-trace test.
proof:
  The factor \(1-F\) kills the logarithmic pole, so \((1-F)\phi\) is a
  compactly supported smooth surface test.  The Riesz correction has a pure
  zero-trace scalar representative, and multiplication by the compactly
  supported smooth cutoff preserves pure zero trace.  Therefore the spliced
  potential has a pure representative.  Applying the normal-contraction
  theorem to the signed fixed-level clipping map gives the claimed clipped
  representative.
-/
theorem
    fixedLevelSignedClip_spliced_localEnergyPotential_has_pureH10_scalarRepresentative
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [RiemannSurface X]
    [MeasurableEq X] [SecondCountableTopology X] [ComplexOneManifold X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    (φ : LogarithmicCutoffPoleModel g p)
    (source : (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ)
    (hdata :
      GreenSobolevH10SmoothCompactSupportLocalWeakCorrectionData
        φ source)
    (F : SmoothCompactlySupportedGlobalSurfaceFunction X)
    (coordinate : PointedSurfaceCoordinate X p) {innerRadius : ℝ}
    (hinner_pos : 0 < innerRadius)
    (hF_eq_one :
      ∀ x ∈ coordinate.chart.source,
        ‖coordinate.chart x - coordinate.chart p‖ < innerRadius →
          F.toFun x = 1)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    {b a : ℝ} (hb_pos : 0 < b) (hba : b < a) :
    ∃ v : GreenSobolevH10SmoothCompactSupport g,
      HasPureH10ScalarRepresentative v
        (fixedLevelSignedClip
          (fun x : X ↦
            (1 - F.toFun x) *
              localEnergyGreenPotential φ hdata.correction x +
              (if σ = 1 then a else 0) * F.toFun x)
          σ b a) := by
  classical
  let d : ℝ := if σ = 1 then a else 0
  let corr : X → ℝ := hdata.correction.toFun
  let raw : X → ℝ := localEnergyGreenPotential φ hdata.correction
  have hcorr_rep :
      HasPureH10ScalarRepresentative
        (greenSobolevH10SmoothCompactSupportRieszVector source)
        corr := by
    simpa [corr] using
      rieszLocalCorrection_has_pureH10_scalarRepresentative hdata
  have hcorr_meas :
      ∀ K : Set X, IsCompact K →
        AEStronglyMeasurable corr (g.volume.restrict K) := by
    intro K hK
    have hm : MemLp hdata.scalar.toFun 2 (g.volume.restrict K) :=
      hdata.scalar.primitive_memLp_local K hK
    simpa [corr, hdata.correction_toFun_eq_scalar] using
      hm.aestronglyMeasurable
  rcases
      pureH10_smoothCompactlySupportedMultiplier_has_scalarRepresentative
        (g := g) F hcorr_rep hcorr_meas with
    ⟨uFcorr, hFcorr_rep⟩
  have hF_meas :
      ∀ K : Set X, IsCompact K →
        AEStronglyMeasurable F.toFun (g.volume.restrict K) := by
    intro K hK
    exact (F.memLp_restrict_compact (g := g) hK).aestronglyMeasurable
  have hFcorr_meas :
      ∀ K : Set X, IsCompact K →
        AEStronglyMeasurable
          (fun x : X ↦ F.toFun x * corr x)
          (g.volume.restrict K) := by
    intro K hK
    exact (hF_meas K hK).mul (hcorr_meas K hK)
  have hnegFcorr_rep :
      HasPureH10ScalarRepresentative ((-1 : ℝ) • uFcorr)
        (fun x : X ↦ (-1 : ℝ) * (F.toFun x * corr x)) :=
    HasPureH10ScalarRepresentative.smul hFcorr_rep (-1 : ℝ)
  have hnegFcorr_meas :
      ∀ K : Set X, IsCompact K →
        AEStronglyMeasurable
          (fun x : X ↦ (-1 : ℝ) * (F.toFun x * corr x))
          (g.volume.restrict K) := by
    intro K hK
    exact (hFcorr_meas K hK).const_mul (-1 : ℝ)
  have hcorr_minus_rep :
      HasPureH10ScalarRepresentative
        (greenSobolevH10SmoothCompactSupportRieszVector source +
          (-1 : ℝ) • uFcorr)
        (fun x : X ↦ corr x +
          (-1 : ℝ) * (F.toFun x * corr x)) :=
    HasPureH10ScalarRepresentative.add
      hcorr_rep hnegFcorr_rep hcorr_meas hnegFcorr_meas
  have hcorr_minus_meas :
      ∀ K : Set X, IsCompact K →
        AEStronglyMeasurable
          (fun x : X ↦ corr x +
            (-1 : ℝ) * (F.toFun x * corr x))
          (g.volume.restrict K) := by
    intro K hK
    exact (hcorr_meas K hK).add (hnegFcorr_meas K hK)
  let η : X → ℝ := fun x : X ↦ (1 : ℝ) - F.toFun x
  have hη_smooth : IsSmoothOnSurface (Set.univ : Set X) η := by
    intro e he
    have hF_smooth := F.smooth e he
    simpa [η] using (contDiffOn_const.sub hF_smooth)
  have hη_support :
      closure {x : X | η x ≠ 0} ⊆ {x : X | x ≠ p} := by
    simpa [η] using
      one_sub_cutoff_support_away_pole_of_eq_one_near_pole
        F coordinate hinner_pos hF_eq_one
  let PolePiece : SmoothCompactlySupportedGlobalSurfaceFunction X :=
    SmoothCompactlySupportedGlobalSurfaceFunction.mul_of_left_support_subset_open
      (V := {x : X | x ≠ p})
      (isOpen_ne (x := p))
      hη_smooth φ.smooth_away_pole φ.compact_support hη_support
  let hPolePiece :
      SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
        (SurfaceDifferentialField.ofCoordinateField PolePiece.gradient) :=
    PolePiece.differential_memHilbertSchmidtL2
  have hPolePiece_rep :
      HasPureH10ScalarRepresentative
        ((greenSobolevH10SmoothCompactSupportCore g).toCompletion
          (greenSmoothCoreElement (g := g) PolePiece hPolePiece))
        PolePiece.toFun :=
    HasPureH10ScalarRepresentative.of_smoothCompactlySupported
      PolePiece hPolePiece
  have hPolePiece_meas :
      ∀ K : Set X, IsCompact K →
        AEStronglyMeasurable PolePiece.toFun (g.volume.restrict K) := by
    intro K hK
    exact
      (PolePiece.memLp_restrict_compact (g := g) hK).aestronglyMeasurable
  have hPole_corr_rep :
      HasPureH10ScalarRepresentative
        (((greenSobolevH10SmoothCompactSupportCore g).toCompletion
            (greenSmoothCoreElement (g := g) PolePiece hPolePiece)) +
          (greenSobolevH10SmoothCompactSupportRieszVector source +
            (-1 : ℝ) • uFcorr))
        (fun x : X ↦ PolePiece.toFun x +
          (corr x + (-1 : ℝ) * (F.toFun x * corr x))) :=
    HasPureH10ScalarRepresentative.add
      hPolePiece_rep hcorr_minus_rep hPolePiece_meas hcorr_minus_meas
  have hPole_corr_meas :
      ∀ K : Set X, IsCompact K →
        AEStronglyMeasurable
          (fun x : X ↦ PolePiece.toFun x +
            (corr x + (-1 : ℝ) * (F.toFun x * corr x)))
          (g.volume.restrict K) := by
    intro K hK
    exact (hPolePiece_meas K hK).add (hcorr_minus_meas K hK)
  let dF : SmoothCompactlySupportedGlobalSurfaceFunction X :=
    SmoothCompactlySupportedGlobalSurfaceFunction.smul d F
  let hdF :
      SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
        (SurfaceDifferentialField.ofCoordinateField dF.gradient) :=
    dF.differential_memHilbertSchmidtL2
  have hdF_rep :
      HasPureH10ScalarRepresentative
        ((greenSobolevH10SmoothCompactSupportCore g).toCompletion
          (greenSmoothCoreElement (g := g) dF hdF))
        dF.toFun :=
    HasPureH10ScalarRepresentative.of_smoothCompactlySupported dF hdF
  have hdF_meas :
      ∀ K : Set X, IsCompact K →
        AEStronglyMeasurable dF.toFun (g.volume.restrict K) := by
    intro K hK
    exact (dF.memLp_restrict_compact (g := g) hK).aestronglyMeasurable
  have hS0_rep :
      HasPureH10ScalarRepresentative
        ((((greenSobolevH10SmoothCompactSupportCore g).toCompletion
            (greenSmoothCoreElement (g := g) PolePiece hPolePiece)) +
          (greenSobolevH10SmoothCompactSupportRieszVector source +
            (-1 : ℝ) • uFcorr)) +
          ((greenSobolevH10SmoothCompactSupportCore g).toCompletion
            (greenSmoothCoreElement (g := g) dF hdF)))
        (fun x : X ↦
          (PolePiece.toFun x +
            (corr x + (-1 : ℝ) * (F.toFun x * corr x))) +
            dF.toFun x) :=
    HasPureH10ScalarRepresentative.add
      hPole_corr_rep hdF_rep hPole_corr_meas hdF_meas
  have hS0_meas :
      ∀ K : Set X, IsCompact K →
        AEStronglyMeasurable
          (fun x : X ↦
            (PolePiece.toFun x +
              (corr x + (-1 : ℝ) * (F.toFun x * corr x))) +
              dF.toFun x)
          (g.volume.restrict K) := by
    intro K hK
    exact (hPole_corr_meas K hK).add (hdF_meas K hK)
  rcases
      fixedLevelSignedClip_of_pureH10_scalarRepresentative
        (g := g) hS0_rep hS0_meas hσ hb_pos hba with
    ⟨v, hv⟩
  refine ⟨v, HasPureH10ScalarRepresentative.ae_eq hv ?_⟩
  intro K hK
  exact Filter.Eventually.of_forall fun x : X ↦ by
    have hfun :
        (PolePiece.toFun x +
            (corr x + (-1 : ℝ) * (F.toFun x * corr x))) +
            dF.toFun x =
          (1 - F.toFun x) * raw x + d * F.toFun x := by
      by_cases hσ_one : σ = 1
      · simp [PolePiece, dF, η, corr, raw, d, localEnergyGreenPotential,
          SmoothCompactlySupportedGlobalSurfaceFunction.mul_of_left_support_subset_open,
          SmoothCompactlySupportedGlobalSurfaceFunction.smul, hσ_one]
        ring
      · simp [PolePiece, dF, η, corr, raw, d, localEnergyGreenPotential,
          SmoothCompactlySupportedGlobalSurfaceFunction.mul_of_left_support_subset_open,
          SmoothCompactlySupportedGlobalSurfaceFunction.smul, hσ_one]
        ring
    simp only [fixedLevelSignedClip]
    rw [hfun]

/--
%%handwave
name:
  Positive fixed-level clips are eventually one at the pole
statement:
  If a regular potential has the logarithmic singularity at the pole, then
  its positive fixed-level clip is eventually equal to one in the punctured
  neighbourhood of the pole.
proof:
  The logarithmic singularity implies that the potential tends to \(+\infty\)
  at the puncture.  Eventually it is at least the upper clipping level, so
  the clipping function is one.
-/
theorem fixedLevelSignedClip_pos_eventually_eq_one_near_pole
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [RiemannSurface X]
    [IsManifold SurfaceRealModel ∞ X] {p : X}
    (G : X → ℝ)
    (hlog :
      ∀ χ : PointedSurfaceCoordinate X p,
        ∃ H : X → ℝ,
          IsHarmonicOnSurface χ.chart.source H ∧
            ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
              G x + Real.log ‖χ.chart x - χ.chart p‖ = H x)
    {b a : ℝ} (hba : b < a) :
    ∀ᶠ x in 𝓝[≠] p, fixedLevelSignedClip G 1 b a x = 1 := by
  have hblow : Filter.Tendsto G (𝓝[≠] p) Filter.atTop :=
    logarithmic_singularity_tendsto_atTop X p hlog
  filter_upwards [hblow.eventually_ge_atTop a] with x hx
  simpa [fixedLevelSignedClip] using
    fixedLevelClip_eq_one_of_ge (b := b) (a := a) hba hx

/--
%%handwave
name:
  Negative fixed-level clips are eventually zero at the pole
statement:
  If a regular potential has the logarithmic singularity at the pole, then
  the fixed-level clip of its negative is eventually equal to zero in the
  punctured neighbourhood of the pole.
proof:
  The logarithmic singularity implies that the potential tends to \(+\infty\)
  at the puncture.  Eventually the negative potential lies below the lower
  clipping level, so the clipping function is zero.
-/
theorem fixedLevelSignedClip_neg_eventually_eq_zero_near_pole
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [RiemannSurface X]
    [IsManifold SurfaceRealModel ∞ X] {p : X}
    (G : X → ℝ)
    (hlog :
      ∀ χ : PointedSurfaceCoordinate X p,
        ∃ H : X → ℝ,
          IsHarmonicOnSurface χ.chart.source H ∧
            ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
              G x + Real.log ‖χ.chart x - χ.chart p‖ = H x)
    {b a : ℝ} (hb_pos : 0 < b) (hba : b < a) :
    ∀ᶠ x in 𝓝[≠] p, fixedLevelSignedClip G (-1) b a x = 0 := by
  have hblow : Filter.Tendsto G (𝓝[≠] p) Filter.atTop :=
    logarithmic_singularity_tendsto_atTop X p hlog
  filter_upwards [hblow.eventually_ge_atTop 0] with x hx
  have hle : (-1 : ℝ) * G x ≤ b := by
    nlinarith
  simpa [fixedLevelSignedClip] using
    fixedLevelClip_eq_zero_of_le (b := b) (a := a) hba hle

/--
%%handwave
name:
  Pure admissibility of signed fixed-level clips from pole constancy
statement:
  If the global signed fixed-level clip agrees with a constant in a punctured
  neighbourhood of the logarithmic pole, and it agrees almost everywhere with
  the regular energy potential away from the pole, then it represents a pure
  homogeneous zero-trace test.
proof:
  Excise a small pole neighbourhood on which the clip is constant.  On the
  complement the cutoff pole model is smooth and compactly supported, while
  the Riesz correction has a pure homogeneous zero-trace scalar
  representative.  Adding the smooth compactly supported part and applying
  the normal-contraction theorem gives the clipped representative; the local
  \(L^2\)-representative is unchanged by the almost-everywhere agreement with
  the Weyl-regular representative.
-/
theorem fixedLevelSignedClip_has_pureH10_scalarRepresentative_of_pole_constancy
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [RiemannSurface X]
    [MeasurableEq X] [SecondCountableTopology X] [ComplexOneManifold X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    (_hcap : HasPureDirichletCapacityAtInfinity g)
    (φ : LogarithmicCutoffPoleModel g p)
    (source : (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ)
    (hdata :
      GreenSobolevH10SmoothCompactSupportLocalWeakCorrectionData
        φ source)
    (G : X → ℝ)
    (hrep :
      ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X),
        (fun w : ℂ ↦ localEnergyGreenPotential φ hdata.correction
          (e.symm w))
          =ᵐ[MeasureTheory.volume.restrict
            (e.target ∩ e.symm ⁻¹' {x : X | x ≠ p})]
            (fun w : ℂ ↦ G (e.symm w)))
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    {b a : ℝ} (hb_pos : 0 < b) (hba : b < a)
    (hpole_const :
      ∀ᶠ x in 𝓝[≠] p,
        fixedLevelSignedClip G σ b a x =
          if σ = 1 then (1 : ℝ) else 0) :
    ∃ v : GreenSobolevH10SmoothCompactSupport g,
      HasPureH10ScalarRepresentative v
        (fixedLevelSignedClip G σ b a) := by
  classical
  rcases
      exists_smoothCompactlySupportedGlobalSurfaceFunction_eq_one_near_pole_of_eventually_nhdsWithin
        X p
        (P := fun x : X ↦
          fixedLevelSignedClip G σ b a x =
            if σ = 1 then (1 : ℝ) else 0)
        hpole_const with
    ⟨F, coordinate, innerRadius, hinner_pos, hsupport_const,
      _hsupport_source, hF_bounds, hF_eq_one⟩
  rcases
      fixedLevelSignedClip_spliced_localEnergyPotential_has_pureH10_scalarRepresentative
        φ source hdata F coordinate hinner_pos hF_eq_one hσ hb_pos hba with
    ⟨v, hv⟩
  refine ⟨v, HasPureH10ScalarRepresentative.ae_eq hv ?_⟩
  intro K hK
  have hraw_ae :
      localEnergyGreenPotential φ hdata.correction
        =ᵐ[g.volume.restrict K] G :=
    localEnergyGreenPotential_chartwise_ae_eq_compact
      φ hdata.correction G hrep K hK
  have hp_null :
      g.volume {p} = 0 :=
    smoothPositiveAreaMeasureOnSurface_measure_singleton
      g.volume (BackgroundSurfaceMetricOnSurface.volume_smooth_positive g) p
  have hp_null_restrict :
      (g.volume.restrict K) {p} = 0 := by
    exact le_antisymm
      (by
        simpa [hp_null] using
          (Measure.restrict_le_self (μ := g.volume) (s := K) {p}))
      bot_le
  have hp_ae : ∀ᵐ x ∂g.volume.restrict K, x ≠ p := by
    rw [ae_iff]
    simpa using hp_null_restrict
  filter_upwards [hraw_ae, hp_ae] with x hraw_eq hx_ne
  exact
    fixedLevelSignedClip_splice_eq_of_raw_eq
      (p := p)
      (raw := localEnergyGreenPotential φ hdata.correction)
      (G := G) (F := F.toFun)
      hσ hb_pos hba hF_bounds hsupport_const hx_ne hraw_eq

/--
%%handwave
name:
  Global signed fixed-level clip is an admissible pure zero-trace test
statement:
  For either sign of a regular energy potential produced by the pure Riesz
  construction, the global fixed-level clip represents a pure homogeneous
  zero-trace test.
proof:
  This is the common capacitary truncation input for positive and negative
  levels.  The clipped signed potential is constant near the pole, where the
  logarithmic singularity would otherwise be visible.  Away from the pole it
  is a Lipschitz contraction of the regular potential, and at infinity it
  inherits the homogeneous zero-trace condition from the pure Riesz
  correction together with compact support of the pole model.
-/
theorem fixedLevelSignedClip_has_pureH10_scalarRepresentative
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [RiemannSurface X]
    [MeasurableEq X] [SecondCountableTopology X] [ComplexOneManifold X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    (hcap : HasPureDirichletCapacityAtInfinity g)
    (φ : LogarithmicCutoffPoleModel g p)
    (source : (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ)
    (hdata :
      GreenSobolevH10SmoothCompactSupportLocalWeakCorrectionData
        φ source)
    (G : X → ℝ)
    (hrep :
      ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X),
        (fun w : ℂ ↦ localEnergyGreenPotential φ hdata.correction
          (e.symm w))
          =ᵐ[MeasureTheory.volume.restrict
            (e.target ∩ e.symm ⁻¹' {x : X | x ≠ p})]
            (fun w : ℂ ↦ G (e.symm w)))
    (hlog :
      ∀ χ : PointedSurfaceCoordinate X p,
        ∃ H : X → ℝ,
          IsHarmonicOnSurface χ.chart.source H ∧
            ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
              G x + Real.log ‖χ.chart x - χ.chart p‖ = H x)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    {b a : ℝ} (hb_pos : 0 < b) (hba : b < a) :
    ∃ v : GreenSobolevH10SmoothCompactSupport g,
      HasPureH10ScalarRepresentative v
        (fixedLevelSignedClip G σ b a) := by
  have hpole_const :
      ∀ᶠ x in 𝓝[≠] p,
        fixedLevelSignedClip G σ b a x =
          if σ = 1 then (1 : ℝ) else 0 := by
    rcases hσ with rfl | rfl
    · simpa using
        fixedLevelSignedClip_pos_eventually_eq_one_near_pole
          (X := X) (p := p) G hlog hba
    · have hneg_const :
          ∀ᶠ x in 𝓝[≠] p,
            fixedLevelSignedClip G (-1) b a x = 0 :=
        fixedLevelSignedClip_neg_eventually_eq_zero_near_pole
          (X := X) (p := p) G hlog hb_pos hba
      have hne : (-1 : ℝ) ≠ 1 := by norm_num
      filter_upwards [hneg_const] with x hx
      simpa [hne] using hx
  exact
    fixedLevelSignedClip_has_pureH10_scalarRepresentative_of_pole_constancy
      hcap φ source hdata G hrep hσ hb_pos hba hpole_const


/--
%%handwave
name:
  Measurable local \(L^2\) limits of explicit pure representatives are square-integrable
statement:
  If compactly supported smooth primitives converge compact-locally in
  \(L^2\) to an almost everywhere measurable scalar function, then the scalar
  limit is square-integrable on every compact subset.
proof:
  On each compact set, apply the standard \(L^p\)-closedness theorem: an
  \(L^2\)-limit of \(L^2\) functions is again \(L^2\), provided the limit is
  almost everywhere measurable.
-/
theorem pureH10ScalarRepresentative_explicit_memLp_local_of_aestronglyMeasurable
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [IsManifold SurfaceRealModel ∞ X]
    {g : BackgroundSurfaceMetricOnSurface X}
    (F : ℕ → SmoothCompactlySupportedGlobalSurfaceFunction X)
    {f : X → ℝ}
    (hF_local :
      ∀ K : Set X, IsCompact K →
        TendstoInLocalL2OnSurface g.volume K
          (fun n : ℕ ↦ (F n).toFun) f)
    (hf_meas :
      ∀ K : Set X, IsCompact K →
        AEStronglyMeasurable f (g.volume.restrict K)) :
    ∀ K : Set X, IsCompact K → MemLp f 2 (g.volume.restrict K) := by
  intro K hK
  exact
    MeasureTheory.Lp.memLp_of_cauchy_tendsto
      (μ := g.volume.restrict K)
      (p := (2 : ℝ≥0∞))
      (by norm_num : (1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞))
      (fun n : ℕ ↦ (F n).memLp_restrict_compact (g := g) hK)
      f (hf_meas K hK)
      (by simpa [TendstoInLocalL2OnSurface] using hF_local K hK)



/--
%%handwave
name:
  Differential pairings converge for explicit pure representatives
statement:
  If the pure differential classes of explicit compactly supported smooth
  primitives converge to a completed pure class, then their coordinate
  differential pairings against any compactly supported coordinate test
  converge to the pairing with the chosen square-integrable differential
  representative of that completed class.
proof:
  The coordinate test defines a continuous linear pairing on the intrinsic
  \(L^2\) differential Hilbert space.  Apply this continuous functional to
  the convergence of the differential classes.
-/
theorem pureH10ScalarRepresentative_explicit_differentialPairing_tendsto
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [SecondCountableTopology X] [ComplexOneManifold X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    {u : GreenSobolevH10SmoothCompactSupport g}
    (F : ℕ → SmoothCompactlySupportedGlobalSurfaceFunction X)
    (hF : ∀ n : ℕ,
      SurfaceDifferentialFieldMemHilbertSchmidtL2 g.metric g.volume
        (SurfaceDifferentialField.ofCoordinateField (F n).gradient))
    (hF_tendsto :
      Filter.Tendsto
        (fun n : ℕ ↦
          (greenSobolevH10SmoothCompactSupportCore g).toCompletion
            (greenSmoothCoreElement (g := g) (F n) (hF n)))
        Filter.atTop (𝓝 u))
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ atlas ℂ X)
    (φ : SmoothCompactlySupportedCoordinateFunction
      (surfaceChartRegion e (Set.univ : Set X))) (v : ℂ) :
    Integrable
        (fun z ↦
          (SurfaceDifferentialField.toCoordinateField
            (greenSobolevH10SmoothCompactSupportDifferentialRep u).toField
              (e.symm z))
            (surfaceChartTangentMap e z v) * φ z)
        (MeasureTheory.volume.restrict
          (surfaceChartRegion e (Set.univ : Set X))) ∧
      Filter.Tendsto
        (fun n : ℕ ↦
          ∫ z in surfaceChartRegion e (Set.univ : Set X),
            (F n).gradient (e.symm z)
              (surfaceChartTangentMap e z v) * φ z ∂MeasureTheory.volume)
        Filter.atTop
        (𝓝 (∫ z in surfaceChartRegion e (Set.univ : Set X),
          (SurfaceDifferentialField.toCoordinateField
            (greenSobolevH10SmoothCompactSupportDifferentialRep u).toField
              (e.symm z))
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
  let U : ℕ → (greenSobolevH10SmoothCompactSupportCore g).Core :=
    fun n ↦ greenSmoothCoreElement (g := g) (F n) (hF n)
  let duSeq : ℕ → SquareIntegrableSurfaceDifferentialField
      (X := X) (E := ℝ) g.metric g.volume :=
    fun n ↦
      { toSection :=
          SurfaceDifferentialField.ofCoordinateField (F n).gradient
        memL2 := hF n }
  let duLim : SquareIntegrableSurfaceDifferentialField
      (X := X) (E := ℝ) g.metric g.volume :=
    greenSobolevH10SmoothCompactSupportDifferentialRep u
  let duLimClass : GreenDifferentialL2Intrinsic g :=
    greenSobolevH10SmoothCompactSupportDifferentialClass u
  have hduLim_eq :
      (Quotient.mk
        (SquareIntegrableSurfaceDifferentialField.aeSetoid
          (X := X) (E := ℝ) (g := g.metric) (μ := g.volume)) duLim :
        GreenDifferentialL2Intrinsic g) =
        duLimClass := by
    simpa [duLim, duLimClass] using
      greenSobolevH10SmoothCompactSupportDifferentialRep_class_eq u
  have hU_diff :
      Filter.Tendsto (fun n : ℕ ↦ (U n).1) Filter.atTop
        (𝓝 (greenSobolevH10SmoothCompactSupportDifferentialClass u)) := by
    simpa [U] using
      greenSobolevH10SmoothCompactSupportCore_differentialClass_tendsto
        (g := g) U u (by simpa [U] using hF_tendsto)
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
                (U n).1 := by
            intro n
            rfl
          exact
            Filter.Tendsto.congr'
              (Filter.Eventually.of_forall fun n ↦ (hpoint n).symm)
              hU_diff)
        e he ψ v with
    ⟨hlim_int, htendsto⟩
  constructor
  · simpa [ψ, duLim, SurfaceDifferentialField.toCoordinateField,
      ManifoldDifferentialField.evalChart, manifoldChartRegion,
      surfaceChartRegion, smul_eq_mul, mul_comm] using hlim_int
  · simpa [ψ, duSeq, duLim, SurfaceDifferentialField.toCoordinateField,
      SurfaceDifferentialField.ofCoordinateField,
      ManifoldDifferentialField.evalChart, manifoldChartRegion,
      surfaceChartRegion, smul_eq_mul, mul_comm] using htendsto


/--
%%handwave
name:
  The completed pure differential preserves norm
statement:
  Passing from a completed homogeneous zero-trace class to its ambient
  \(L^2\)-cotangent differential class preserves the pure Dirichlet norm.
proof:
  On the dense smooth differential core this is the identity map into the
  ambient \(L^2\)-space, hence it preserves the norm.  The two norm functions
  are continuous on the completion, so equality extends from the dense core
  to the completed space.
-/
theorem greenSobolevH10SmoothCompactSupportDifferentialClass_norm_eq
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (u : GreenSobolevH10SmoothCompactSupport g) :
    ‖greenSobolevH10SmoothCompactSupportDifferentialClass u‖ = ‖u‖ := by
  let C := greenSobolevH10SmoothCompactSupportCore g
  let D :
      GreenSobolevH10SmoothCompactSupport g →L[ℝ]
        GreenDifferentialL2Intrinsic g :=
    greenSobolevH10SmoothCompactSupportDifferentialClass
  let e : C.Core →L[ℝ] GreenSobolevH10SmoothCompactSupport g :=
    UniformSpace.Completion.toComplL
  have hdense : DenseRange e := by
    simpa [e, UniformSpace.Completion.coe_toComplL] using
      (UniformSpace.Completion.denseRange_coe : DenseRange
        ((↑) : C.Core → UniformSpace.Completion C.Core))
  have hfun :
      (fun u : GreenSobolevH10SmoothCompactSupport g ↦ ‖D u‖) =
        (fun u : GreenSobolevH10SmoothCompactSupport g ↦ ‖u‖) := by
    refine hdense.equalizer ?_ ?_ ?_
    · exact continuous_norm.comp D.continuous
    · exact continuous_norm
    · funext v
      have hvD :
          D (C.toCompletion v) = v.1 :=
        greenSobolevH10SmoothCompactSupportDifferentialClass_toCompletion v
      have hev : e v = C.toCompletion v := by
        rfl
      calc
        ‖D (e v)‖ = ‖D (C.toCompletion v)‖ := by rw [hev]
        _ = ‖v.1‖ := by rw [hvD]
        _ = ‖v‖ := rfl
        _ = ‖e v‖ := by
          rw [hev]
          change ‖v‖ = ‖((v : C.Core) : UniformSpace.Completion C.Core)‖
          exact (UniformSpace.Completion.norm_coe v).symm
  exact congrFun hfun u

/--
%%handwave
name:
  Pure self-energy is the representative Dirichlet integral
statement:
  The pure self inner product of a completed homogeneous zero-trace class is
  the integral of the background Dirichlet density of any chosen
  square-integrable differential representative of its ambient differential
  class.
proof:
  The completed differential class preserves the pure norm.  The ambient
  \(L^2\)-norm of a representative is the square root of the integral of its
  fiberwise square norm, and for scalar surface differentials that square norm
  is exactly the background Dirichlet density.
-/
theorem greenSobolevH10SmoothCompactSupport_inner_self_eq_differentialRep_integral
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    (u : GreenSobolevH10SmoothCompactSupport g) :
    inner ℝ u u =
      ∫ x,
        g.gradientInner x
          (SurfaceDifferentialField.toCoordinateField
            (greenSobolevH10SmoothCompactSupportDifferentialRep u).toField x)
          (SurfaceDifferentialField.toCoordinateField
            (greenSobolevH10SmoothCompactSupportDifferentialRep u).toField x)
        ∂g.volume := by
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
  let du : SquareIntegrableSurfaceDifferentialField
      (X := X) (E := ℝ) g.metric g.volume :=
    greenSobolevH10SmoothCompactSupportDifferentialRep u
  let D :
      GreenSobolevH10SmoothCompactSupport g →L[ℝ]
        GreenDifferentialL2Intrinsic g :=
    greenSobolevH10SmoothCompactSupportDifferentialClass
  let DU : GreenDifferentialL2Intrinsic g :=
    (Quotient.mk
      (SquareIntegrableSurfaceDifferentialField.aeSetoid
        (X := X) (E := ℝ) (g := g.metric) (μ := g.volume)) du :
      GreenDifferentialL2Intrinsic g)
  have hDU : DU = D u := by
    simpa [DU, du, D] using
      greenSobolevH10SmoothCompactSupportDifferentialRep_class_eq u
  let diffG :=
    manifoldDifferentialHilbertBundleGeometry
      (I := SurfaceRealModel) (X := X) (E := ℝ) g.metric.toManifoldMetric
  let hG_inner :
      ∀ (x : X)
        (v w : ManifoldDifferentialBundleFiber
          (I := SurfaceRealModel) (X := X) (E := ℝ) x),
        diffG.fiberInner x v w = inner ℝ v w := by
    intro _ _ _
    rfl
  letI : NormedAddCommGroup (L2HilbertBundle diffG g.volume) :=
    l2HilbertBundleNormedAddCommGroup
      (I := SurfaceRealModel) (G := diffG) hG_inner g.volume
  have hnorm_D : ‖D u‖ = ‖u‖ :=
    greenSobolevH10SmoothCompactSupportDifferentialClass_norm_eq u
  have hnorm_DU : ‖DU‖ = ‖u‖ := by
    rw [hDU, hnorm_D]
  have hnorm_mk :
      ‖DU‖ =
        squareIntegrableHilbertBundleSectionL2Norm diffG g.volume du := by
    simpa [DU, du, diffG, hG_inner] using
      (l2HilbertBundle_norm_mk_eq_l2Norm
        (I := SurfaceRealModel) (G := diffG) (μ := g.volume)
        hG_inner du)
  have hsq_nonneg :
      0 ≤ squareIntegrableHilbertBundleSectionL2NormSq diffG g.volume du := by
    unfold squareIntegrableHilbertBundleSectionL2NormSq
    refine integral_nonneg fun x ↦ ?_
    rw [diffG.fiberNormSq_eq_inner, hG_inner]
    exact real_inner_self_nonneg
  have hnorm_sq_integral :
      ‖DU‖ ^ (2 : ℕ) =
        ∫ x,
          g.gradientInner x
            (SurfaceDifferentialField.toCoordinateField du.toField x)
            (SurfaceDifferentialField.toCoordinateField du.toField x)
          ∂g.volume := by
    calc
      ‖DU‖ ^ (2 : ℕ) =
          (squareIntegrableHilbertBundleSectionL2Norm diffG g.volume du) ^
            (2 : ℕ) := by rw [hnorm_mk]
      _ = squareIntegrableHilbertBundleSectionL2NormSq diffG g.volume du := by
        unfold squareIntegrableHilbertBundleSectionL2Norm
        exact Real.sq_sqrt hsq_nonneg
      _ =
          ∫ x,
            g.gradientInner x
              (SurfaceDifferentialField.toCoordinateField du.toField x)
              (SurfaceDifferentialField.toCoordinateField du.toField x)
            ∂g.volume := by
        unfold squareIntegrableHilbertBundleSectionL2NormSq
        apply integral_congr_ae
        filter_upwards [] with x
        simpa [diffG, du, SurfaceDifferentialField.toCoordinateField] using
          (surface_coordinate_cotangent_fiberNormSq_eq_gradientInner
            g x (SurfaceDifferentialField.toCoordinateField du.toField x))
  calc
    inner ℝ u u = ‖u‖ ^ (2 : ℕ) := real_inner_self_eq_norm_sq u
    _ = ‖DU‖ ^ (2 : ℕ) := by rw [hnorm_DU]
    _ =
        ∫ x,
          g.gradientInner x
            (SurfaceDifferentialField.toCoordinateField
              (greenSobolevH10SmoothCompactSupportDifferentialRep u).toField x)
            (SurfaceDifferentialField.toCoordinateField
              (greenSobolevH10SmoothCompactSupportDifferentialRep u).toField x)
          ∂g.volume := by
      simpa [du] using hnorm_sq_integral













/--
%%handwave
name:
  Escaping strict-superlevel components are fixed-level domains
statement:
  Let \(f\) be continuous and let \(b<a\).  If the connected component of
  \(\{f>b\}\) through a point where \(f\ge a\) escapes every compact set, then
  that component is an open connected fixed-level domain: it is contained in
  \(\{f>b\}\), its frontier is contained in \(\{f=b\}\), it contains a point
  where \(f\ge a\), and it escapes every compact set.
proof:
  The strict superlevel is open.  Local connectedness makes its connected
  component open and preconnected.  The frontier lies in the level set:
  closure of the component lies in \(\{f\ge b\}\), while any frontier point
  with \(f>b\) would still lie in the same connected component, contradicting
  openness of the component.
-/
theorem continuous_escaping_strictSuperlevel_component_yields_level_domain
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {f : X → ℝ} (hf_cont : Continuous f)
    {x : X} {b a : ℝ} (hba : b < a) (hx_high : a ≤ f x)
    (hescapes :
      ∀ K : Set X, IsCompact K →
        ∃ y ∈ connectedComponentIn {z : X | b < f z} x, y ∉ K) :
    ∃ Ω : Set X,
      IsOpen Ω ∧
        IsPreconnected Ω ∧
          Ω ⊆ {z : X | b < f z} ∧
            frontier Ω ⊆ {z : X | f z = b} ∧
              (∃ y ∈ Ω, a ≤ f y) ∧
                ∀ K : Set X, IsCompact K → ∃ y ∈ Ω, y ∉ K := by
  classical
  let U : Set X := {z : X | b < f z}
  let Ω : Set X := connectedComponentIn U x
  have hxU : x ∈ U := by
    exact lt_of_lt_of_le hba hx_high
  have hU_open : IsOpen U := by
    have hopen : IsOpen (f ⁻¹' Set.Ioi b) :=
      isOpen_Ioi.preimage hf_cont
    simpa [U, Set.preimage, Set.mem_Ioi] using hopen
  haveI : LocallyConnectedSpace X := ChartedSpace.locallyConnectedSpace ℂ X
  have hΩ_open : IsOpen Ω := by
    simpa [Ω] using hU_open.connectedComponentIn (x := x)
  have hΩ_preconnected : IsPreconnected Ω := by
    simpa [Ω] using (isPreconnected_connectedComponentIn (x := x) (F := U))
  have hΩ_subset : Ω ⊆ U := by
    simpa [Ω] using (connectedComponentIn_subset U x)
  have hxΩ : x ∈ Ω := by
    simpa [Ω] using mem_connectedComponentIn hxU
  have hfrontier : frontier Ω ⊆ {z : X | f z = b} := by
    intro y hy_frontier
    have hy_closure : y ∈ closure Ω := frontier_subset_closure hy_frontier
    have hclosed_ge : IsClosed (f ⁻¹' Set.Ici b) :=
      isClosed_Ici.preimage hf_cont
    have hΩ_subset_ge : Ω ⊆ f ⁻¹' Set.Ici b := by
      intro z hz
      exact le_of_lt (show b < f z from hΩ_subset hz)
    have hy_ge : b ≤ f y :=
      (closure_minimal hΩ_subset_ge hclosed_ge) hy_closure
    have hy_not_gt : ¬ b < f y := by
      intro hy_gt
      have hyU : y ∈ U := hy_gt
      have hyΩ : y ∈ Ω := by
        simpa [Ω, U] using
          mem_connectedComponentIn_of_mem_closure_of_mem
            (S := U) (x := x) (y := y) hxU hyU hy_closure
      have hy_empty : y ∈ Ω ∩ frontier Ω := ⟨hyΩ, hy_frontier⟩
      simp [hΩ_open.inter_frontier_eq] at hy_empty
    exact le_antisymm (le_of_not_gt hy_not_gt) hy_ge
  exact
    ⟨Ω, hΩ_open, hΩ_preconnected, hΩ_subset, hfrontier,
      ⟨x, hxΩ, hx_high⟩, by simpa [Ω, U] using hescapes⟩

/--
%%handwave
name:
  Locally continuous escaping strict-superlevel components are fixed-level domains
statement:
  Let \(f\) be continuous on the closure of the connected component of
  \(\{f>b\}\) through a point where \(f\ge a>b\).  If that strict-superlevel
  set is open and the component escapes every compact set, then the component
  is an open connected fixed-level domain with frontier contained in
  \(\{f=b\}\).
proof:
  This is the same component argument as for a globally continuous function,
  but only the closure of the chosen component is used to prove that frontier
  points satisfy \(f\ge b\).  Openness of the strict superlevel still gives an
  open component, and any frontier point with \(f>b\) would be pulled back
  into the same component by closedness of connected components inside the
  open superlevel.
-/
theorem continuousOn_escaping_strictSuperlevel_component_yields_level_domain
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {f : X → ℝ} {x : X} {b a : ℝ} (hba : b < a)
    (hx_high : a ≤ f x)
    (hU_open : IsOpen {z : X | b < f z})
    (hcont_closure :
      ContinuousOn f
        (closure (connectedComponentIn {z : X | b < f z} x)))
    (hescapes :
      ∀ K : Set X, IsCompact K →
        ∃ y ∈ connectedComponentIn {z : X | b < f z} x, y ∉ K) :
    ∃ Ω : Set X,
      IsOpen Ω ∧
        IsPreconnected Ω ∧
          Ω ⊆ {z : X | b < f z} ∧
            frontier Ω ⊆ {z : X | f z = b} ∧
              (∃ y ∈ Ω, a ≤ f y) ∧
                ∀ K : Set X, IsCompact K → ∃ y ∈ Ω, y ∉ K := by
  classical
  let U : Set X := {z : X | b < f z}
  let Ω : Set X := connectedComponentIn U x
  have hxU : x ∈ U := by
    exact lt_of_lt_of_le hba hx_high
  haveI : LocallyConnectedSpace X := ChartedSpace.locallyConnectedSpace ℂ X
  have hΩ_open : IsOpen Ω := by
    simpa [Ω, U] using hU_open.connectedComponentIn (x := x)
  have hΩ_preconnected : IsPreconnected Ω := by
    simpa [Ω] using (isPreconnected_connectedComponentIn (x := x) (F := U))
  have hΩ_subset : Ω ⊆ U := by
    simpa [Ω] using (connectedComponentIn_subset U x)
  have hxΩ : x ∈ Ω := by
    simpa [Ω] using mem_connectedComponentIn hxU
  have hfrontier : frontier Ω ⊆ {z : X | f z = b} := by
    intro y hy_frontier
    have hy_closure : y ∈ closure Ω := frontier_subset_closure hy_frontier
    have hclosed_ge : IsClosed (closure Ω ∩ f ⁻¹' Set.Ici b) := by
      simpa [Ω, U] using
        hcont_closure.preimage_isClosed_of_isClosed
          isClosed_closure isClosed_Ici
    have hΩ_subset_ge : Ω ⊆ closure Ω ∩ f ⁻¹' Set.Ici b := by
      intro z hz
      exact ⟨subset_closure hz, le_of_lt (show b < f z from hΩ_subset hz)⟩
    have hy_ge : b ≤ f y :=
      ((closure_minimal hΩ_subset_ge hclosed_ge) hy_closure).2
    have hy_not_gt : ¬ b < f y := by
      intro hy_gt
      have hyU : y ∈ U := hy_gt
      have hyΩ : y ∈ Ω := by
        simpa [Ω, U] using
          mem_connectedComponentIn_of_mem_closure_of_mem
            (S := U) (x := x) (y := y) hxU hyU hy_closure
      have hy_empty : y ∈ Ω ∩ frontier Ω := ⟨hyΩ, hy_frontier⟩
      simp [hΩ_open.inter_frontier_eq] at hy_empty
    exact le_antisymm (le_of_not_gt hy_not_gt) hy_ge
  exact
    ⟨Ω, hΩ_open, hΩ_preconnected, hΩ_subset, hfrontier,
      ⟨x, hxΩ, hx_high⟩, by simpa [Ω, U] using hescapes⟩

/--
%%handwave
name:
  Punctured-continuous escaping strict-superlevel components are pole-aware fixed-level domains
statement:
  Let \(f\) be continuous away from a point \(p\).  If a connected component
  of \(\{f>b\}\) contains a point where \(f\ge a>b\), is contained in the
  punctured surface, and escapes every compact set, then it is an open
  connected fixed-level domain whose frontier is contained in \(\{f=b\}\)
  away from \(p\).
proof:
  The component is open and preconnected because the strict superlevel is
  open and the surface is locally connected.  A frontier point different from
  \(p\) cannot have \(f>b\), since then it would lie in the same component;
  it also cannot have \(f<b\), by continuity away from \(p\) and closure of
  the component.  Thus every non-pole frontier point has \(f=b\).
-/
theorem continuousOn_punctured_escaping_strictSuperlevel_component_yields_poleAware_level_domain
    {X : Type} [TopologicalSpace X] [T1Space X] [ChartedSpace ℂ X]
    {p : X} {f : X → ℝ} {x : X} {b a : ℝ} (hba : b < a)
    (hx_high : a ≤ f x)
    (hU_open : IsOpen {z : X | b < f z})
    (hU_subset_punctured : {z : X | b < f z} ⊆ {z : X | z ≠ p})
    (hcont_punctured : ContinuousOn f {z : X | z ≠ p})
    (hescapes :
      ∀ K : Set X, IsCompact K →
        ∃ y ∈ connectedComponentIn {z : X | b < f z} x, y ∉ K) :
    ∃ Ω : Set X,
      IsOpen Ω ∧
        IsPreconnected Ω ∧
          Ω ⊆ {z : X | b < f z} ∧
            frontier Ω ⊆ {z : X | z = p ∨ f z = b} ∧
              (∃ y ∈ Ω, a ≤ f y) ∧
                ∀ K : Set X, IsCompact K → ∃ y ∈ Ω, y ∉ K := by
  classical
  let U : Set X := {z : X | b < f z}
  let Ω : Set X := connectedComponentIn U x
  have hxU : x ∈ U := by
    exact lt_of_lt_of_le hba hx_high
  haveI : LocallyConnectedSpace X := ChartedSpace.locallyConnectedSpace ℂ X
  have hΩ_open : IsOpen Ω := by
    simpa [Ω, U] using hU_open.connectedComponentIn (x := x)
  have hΩ_preconnected : IsPreconnected Ω := by
    simpa [Ω] using (isPreconnected_connectedComponentIn (x := x) (F := U))
  have hΩ_subset : Ω ⊆ U := by
    simpa [Ω] using (connectedComponentIn_subset U x)
  have hxΩ : x ∈ Ω := by
    simpa [Ω, U] using mem_connectedComponentIn hxU
  have hpunctured_open : IsOpen {z : X | z ≠ p} :=
    isOpen_ne (x := p)
  have hΩ_subset_punctured : Ω ⊆ {z : X | z ≠ p} :=
    hΩ_subset.trans hU_subset_punctured
  have hfrontier : frontier Ω ⊆ {z : X | z = p ∨ f z = b} := by
    intro y hy_frontier
    by_cases hyp : y = p
    · exact Or.inl hyp
    · right
      have hy_closure : y ∈ closure Ω :=
        frontier_subset_closure hy_frontier
      have hy_ge : b ≤ f y := by
        by_contra hnot
        have hy_lt : f y < b := lt_of_not_ge hnot
        have hcont_at : ContinuousAt f y :=
          (hcont_punctured.continuousWithinAt hyp).continuousAt
            (hpunctured_open.mem_nhds hyp)
        have hnear_lt : {z : X | f z < b} ∈ 𝓝 y :=
          hcont_at.preimage_mem_nhds (Iio_mem_nhds hy_lt)
        rcases mem_closure_iff_nhds.mp hy_closure
            {z : X | f z < b} hnear_lt with
          ⟨z, hz_lt, hzΩ⟩
        have hz_gt : b < f z := hΩ_subset hzΩ
        have hz_lt' : f z < b := hz_lt
        linarith
      have hy_not_gt : ¬ b < f y := by
        intro hy_gt
        have hyU : y ∈ U := hy_gt
        have hyΩ : y ∈ Ω := by
          simpa [Ω, U] using
            mem_connectedComponentIn_of_mem_closure_of_mem
              (S := U) (x := x) (y := y) hxU hyU hy_closure
        have hy_empty : y ∈ Ω ∩ frontier Ω := ⟨hyΩ, hy_frontier⟩
        simp [hΩ_open.inter_frontier_eq] at hy_empty
      exact le_antisymm (le_of_not_gt hy_not_gt) hy_ge
  exact
    ⟨Ω, hΩ_open, hΩ_preconnected, hΩ_subset, hfrontier,
      ⟨x, hxΩ, hx_high⟩, by simpa [Ω, U] using hescapes⟩

/--
%%handwave
name:
  Positive strict superlevels of a pole-normalized punctured harmonic function are open
statement:
  If a function is harmonic away from a pole and its normalized pole value is
  below a positive level \(b\), then \(\{G>b\}\) is open.
proof:
  The punctured surface is open and the harmonic function is continuous there.
  Since the normalized value at the pole is below \(b\), the strict
  superlevel is exactly the intersection of the punctured surface with the
  strict superlevel inside the continuity region.
-/
theorem harmonicOn_punctured_positive_strictSuperlevel_open
    {X : Type} [TopologicalSpace X] [T1Space X] [ChartedSpace ℂ X]
    {p : X} {G : X → ℝ}
    (hharmonic : IsHarmonicOnSurface {x : X | x ≠ p} G)
    {b : ℝ} (hpb : G p < b) :
    IsOpen {x : X | b < G x} := by
  let U : Set X := {x : X | x ≠ p}
  have hU_open : IsOpen U := by
    simpa [U] using (isOpen_ne (x := p) : IsOpen {x : X | x ≠ p})
  have hcont : ContinuousOn G U :=
    harmonicOnSurface_continuousOn hU_open hharmonic
  have hopen_inter : IsOpen (U ∩ G ⁻¹' Set.Ioi b) :=
    hcont.isOpen_inter_preimage hU_open isOpen_Ioi
  have hset :
      {x : X | b < G x} = U ∩ G ⁻¹' Set.Ioi b := by
    ext x
    constructor
    · intro hx
      have hx_ne : x ≠ p := by
        intro hxp
        have : b < G p := by simpa [hxp] using hx
        linarith
      exact ⟨hx_ne, hx⟩
    · intro hx
      exact hx.2
  simpa [hset]

/--
%%handwave
name:
  Signed fixed-level clip vanishes on the lower level
statement:
  If the signed potential has value \(b\) at a point, then its fixed-level
  clip at levels \(b<a\) is zero there.
proof:
  Substitute \(\sigma G(x)=b\) into the definition and apply [the fixed-level clip is zero whenever its argument is at most \(b\)](lean:JJMath.Uniformization.fixedLevelClip_eq_zero_of_le).
-/
theorem fixedLevelSignedClip_eq_zero_of_signed_level_eq
    {X : Type} {G : X → ℝ} {σ b a : ℝ} {x : X}
    (hba : b < a) (hlevel : σ * G x = b) :
    fixedLevelSignedClip G σ b a x = 0 := by
  simpa [fixedLevelSignedClip, hlevel] using
    fixedLevelClip_eq_zero_of_le (b := b) (a := a) hba le_rfl

/--
%%handwave
name:
  Signed fixed-level clip is one above the upper level
statement:
  If the signed potential is at least \(a\) at a point, then its fixed-level
  clip at levels \(b<a\) is one there.
proof:
  Apply [the fixed-level clip is one whenever its argument is at least \(a\)](lean:JJMath.Uniformization.fixedLevelClip_eq_one_of_ge) to the argument \(\sigma G(x)\).
-/
theorem fixedLevelSignedClip_eq_one_of_signed_level_ge
    {X : Type} {G : X → ℝ} {σ b a : ℝ} {x : X}
    (hba : b < a) (hlevel : a ≤ σ * G x) :
    fixedLevelSignedClip G σ b a x = 1 := by
  simpa [fixedLevelSignedClip] using
    fixedLevelClip_eq_one_of_ge (b := b) (a := a) hba hlevel

/--
%%handwave
name:
  Fixed-level frontier has zero clip away from the pole
statement:
  If the frontier of a domain is contained in the lower signed level, except
  possibly at the pole, then the signed fixed-level clip vanishes at every
  non-pole frontier point.
proof:
  At a frontier point \(x\ne p\), the frontier hypothesis forces
  \(\sigma G(x)=b\).  Apply [the signed fixed-level clip then vanishes](lean:JJMath.Uniformization.fixedLevelSignedClip_eq_zero_of_signed_level_eq).
-/
theorem fixedLevelSignedClip_frontier_eq_zero_of_level_frontier
    {X : Type} [TopologicalSpace X]
    {p : X} {G : X → ℝ} {σ b a : ℝ} {Ω : Set X}
    (hba : b < a)
    (hΩ_frontier : frontier Ω ⊆ {x : X | x = p ∨ σ * G x = b}) :
    ∀ x ∈ frontier Ω, x ≠ p →
      fixedLevelSignedClip G σ b a x = 0 := by
  intro x hx_frontier hx_ne
  rcases hΩ_frontier hx_frontier with hxp | hlevel
  · exact (hx_ne hxp).elim
  · exact fixedLevelSignedClip_eq_zero_of_signed_level_eq hba hlevel

/--
%%handwave
name:
  A high point has clip value one
statement:
  If a domain contains a point where the signed potential is at least \(a\),
  then the signed fixed-level clip at levels \(b<a\) takes the value one
  somewhere in the domain.
proof:
  Choose \(x\in\Omega\) with \(a\le \sigma G(x)\).  Then [the signed fixed-level clip has value one at \(x\)](lean:JJMath.Uniformization.fixedLevelSignedClip_eq_one_of_signed_level_ge).
-/
theorem fixedLevelSignedClip_exists_eq_one_of_high_point
    {X : Type} {G : X → ℝ} {σ b a : ℝ} {Ω : Set X}
    (hba : b < a)
    (hΩ_high : ∃ x ∈ Ω, a ≤ σ * G x) :
    ∃ x ∈ Ω, fixedLevelSignedClip G σ b a x = 1 := by
  rcases hΩ_high with ⟨x, hxΩ, hx_high⟩
  exact
    ⟨x, hxΩ,
      fixedLevelSignedClip_eq_one_of_signed_level_ge hba hx_high⟩

/--
%%handwave
name:
  Fixed-level clips of punctured harmonic potentials are locally measurable
statement:
  If \(G\) is harmonic away from the pole and the signed fixed-level clip is
  constant in a punctured neighbourhood of the pole, then the clip is
  measurable on every compact subset of the surface.
proof:
  Harmonic functions are continuous on the punctured surface.  The fixed-level
  clip is a continuous scalar function of \(G\) there.  Near the puncture the
  clip agrees with a constant, and changing values on the singleton pole does
  not affect compact-local almost-everywhere measurability.
-/
theorem fixedLevelSignedClip_aestronglyMeasurable_on_compacts_of_punctured_harmonic
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [RiemannSurface X]
    [MeasurableEq X] [SecondCountableTopology X] [ComplexOneManifold X]
    [IsManifold SurfaceRealModel ∞ X]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    (G : X → ℝ)
    (hharmonic : IsHarmonicOnSurface {x : X | x ≠ p} G)
    {σ : ℝ} (_hσ : σ = 1 ∨ σ = -1)
    {b a : ℝ} (hb_pos : 0 < b) (hba : b < a)
    (_hpole_const :
      ∀ᶠ x in 𝓝[≠] p,
        fixedLevelSignedClip G σ b a x =
          if σ = 1 then (1 : ℝ) else 0) :
    ∀ K : Set X, IsCompact K →
      AEStronglyMeasurable
        (fixedLevelSignedClip G σ b a)
        (g.volume.restrict K) := by
  classical
  intro K hK
  let U : Set X := {x : X | x ≠ p}
  have hU_open : IsOpen U := by
    simpa [U] using (isOpen_ne (x := p) : IsOpen {x : X | x ≠ p})
  have hG_cont : ContinuousOn G U :=
    harmonicOnSurface_continuousOn hU_open hharmonic
  rcases fixedLevelClip_normalContraction hb_pos hba with
    ⟨_hzero, L, hL_nonneg, hLip⟩
  have hclip_cont : Continuous (fixedLevelClip b a) :=
    continuous_of_real_lipschitz_bound hL_nonneg hLip
  have hσG_cont : ContinuousOn (fun x : X ↦ σ * G x) U := by
    exact continuousOn_const.mul hG_cont
  have hclip_cont_on :
      ContinuousOn (fixedLevelSignedClip G σ b a) (K ∩ U) := by
    have hclip_cont_univ :
        ContinuousOn (fixedLevelClip b a) (Set.univ : Set ℝ) :=
      hclip_cont.continuousOn
    have hcomp :
        ContinuousOn (fun x : X ↦ fixedLevelClip b a (σ * G x))
          (K ∩ U) :=
      hclip_cont_univ.comp'
        (hσG_cont.mono (by intro x hx; exact hx.2))
        (fun _ _ ↦ Set.mem_univ _)
    simpa [fixedLevelSignedClip] using hcomp
  have hKU_meas : MeasurableSet (K ∩ U) :=
    hK.measurableSet.inter hU_open.measurableSet
  have hpunct :
      AEStronglyMeasurable
        (fixedLevelSignedClip G σ b a)
        (g.volume.restrict (K ∩ U)) :=
    hclip_cont_on.aestronglyMeasurable hKU_meas
  have hp_null :
      g.volume ({p} : Set X) = 0 :=
    smoothPositiveAreaMeasureOnSurface_measure_singleton
      g.volume (BackgroundSurfaceMetricOnSurface.volume_smooth_positive g) p
  have hKp_null : g.volume (K ∩ ({p} : Set X)) = 0 :=
    measure_mono_null (by intro x hx; exact hx.2) hp_null
  have hpole :
      AEStronglyMeasurable
        (fixedLevelSignedClip G σ b a)
        (g.volume.restrict (K ∩ ({p} : Set X))) := by
    have hzero_measure :
        g.volume.restrict (K ∩ ({p} : Set X)) = 0 :=
      Measure.restrict_zero_set hKp_null
    rw [hzero_measure]
    exact aestronglyMeasurable_zero_measure _
  have hdecomp : (K ∩ U) ∪ (K ∩ ({p} : Set X)) = K := by
    ext x
    by_cases hxp : x = p
    · simp [U, hxp]
    · simp [U, hxp]
  rw [← hdecomp]
  exact (aestronglyMeasurable_union_iff).mpr ⟨hpunct, hpole⟩

/--
%%handwave
name:
  Almost-everywhere zero fixed-level clips forbid escaping domains
statement:
  Let the signed fixed-level clip of \(G\) vanish almost everywhere on every
  compact subset.  Then there is no escaping connected open domain contained
  in \(\sigma G>b\), with frontier on the level \(\sigma G=b\) away from the
  pole, which contains a point where \(\sigma G\ge a>b\).
proof:
  The frontier and high-point assumptions force a genuine fixed-level
  crossing.  Harmonicity and the local maximum principle make the set where
  the clip is positive contain a compact subset of positive area.  This
  contradicts the assumed almost-everywhere vanishing on compact sets.
-/
theorem fixedLevelSignedClip_ae_zero_forbidden_escaping_domain
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [RiemannSurface X]
    [MeasurableEq X] [SecondCountableTopology X] [ComplexOneManifold X]
    [IsManifold SurfaceRealModel ∞ X]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    (G : X → ℝ)
    (_hharmonic : IsHarmonicOnSurface {x : X | x ≠ p} G)
    {σ : ℝ} (_hσ : σ = 1 ∨ σ = -1)
    {Ω : Set X} {b a : ℝ}
    (_hb_pos : 0 < b) (hba : b < a)
    (hΩ_open : IsOpen Ω)
    (_hΩ_preconnected : IsPreconnected Ω)
    (hΩ_sublevel : Ω ⊆ {x : X | b < σ * G x})
    (_hΩ_frontier : frontier Ω ⊆ {x : X | x = p ∨ σ * G x = b})
    (hΩ_high : ∃ x ∈ Ω, a ≤ σ * G x)
    (_hΩ_escapes : ∀ K : Set X, IsCompact K → ∃ x ∈ Ω, x ∉ K)
    (_hpole_const :
      ∀ᶠ x in 𝓝[≠] p,
        fixedLevelSignedClip G σ b a x =
          if σ = 1 then (1 : ℝ) else 0)
    (hclip_ae_zero :
      ∀ K : Set X, IsCompact K →
        fixedLevelSignedClip G σ b a =ᵐ[g.volume.restrict K] 0) :
    False := by
  classical
  rcases hΩ_high with ⟨x₀, hx₀Ω, _hx₀_high⟩
  have hμ : SmoothPositiveAreaMeasureOnSurface X g.volume :=
    BackgroundSurfaceMetricOnSurface.volume_smooth_positive g
  rcases
    smoothPositiveAreaMeasureOnSurface_exists_compact_pos_measure_subset_open
      (μ := g.volume) hμ hΩ_open ⟨x₀, hx₀Ω⟩ with
    ⟨K, hK_compact, hKΩ, hK_pos⟩
  have hclip_pos_on_K :
      ∀ x ∈ K, 0 < fixedLevelSignedClip G σ b a x := by
    intro x hxK
    exact
      fixedLevelSignedClip_pos_of_signed_level_gt (G := G) (σ := σ)
        (b := b) (a := a) hba (hΩ_sublevel (hKΩ hxK))
  have hclip_zero_ae :
      ∀ᵐ x ∂g.volume.restrict K,
        fixedLevelSignedClip G σ b a x = 0 :=
    hclip_ae_zero K hK_compact
  have hclip_pos_ae :
      ∀ᵐ x ∂g.volume.restrict K,
        0 < fixedLevelSignedClip G σ b a x :=
    ae_restrict_of_forall_mem hK_compact.measurableSet hclip_pos_on_K
  have hfalse_ae : ∀ᵐ x ∂g.volume.restrict K, False := by
    filter_upwards [hclip_zero_ae, hclip_pos_ae] with x hx_zero hx_pos
    linarith
  have hbot : ae (g.volume.restrict K) = ⊥ :=
    Filter.eventually_false_iff_eq_bot.mp hfalse_ae
  have hnebot : (ae (g.volume.restrict K)).NeBot :=
    ae_restrict_neBot.2 (ne_of_gt hK_pos)
  exact hnebot.ne hbot

/--
%%handwave
name:
  Compact-local zero fixed-level clips forbid escaping domains
statement:
  Let the signed fixed-level clip of \(G\) vanish compact-locally in \(L^2\).
  Then there is no escaping connected open domain contained in
  \(\sigma G>b\), with frontier on the level \(\sigma G=b\) away from the
  pole, which contains a point where \(\sigma G\ge a>b\).
proof:
  The clip is zero on the level-\(b\) frontier and one at a high point.  The
  harmonic maximum principle and connectedness force a non-trivial compact
  subregion on which the fixed-level clip is positive.  This gives a positive
  compact-local \(L^2\) mass, contradicting compact-local \(L^2\) convergence
  of the clip to zero.
-/
theorem fixedLevelSignedClip_localL2_zero_forbidden_escaping_domain
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [RiemannSurface X]
    [MeasurableEq X] [SecondCountableTopology X] [ComplexOneManifold X]
    [IsManifold SurfaceRealModel ∞ X]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    (G : X → ℝ)
    (hharmonic : IsHarmonicOnSurface {x : X | x ≠ p} G)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    {Ω : Set X} {b a : ℝ}
    (hb_pos : 0 < b) (hba : b < a)
    (hΩ_open : IsOpen Ω)
    (hΩ_preconnected : IsPreconnected Ω)
    (hΩ_sublevel : Ω ⊆ {x : X | b < σ * G x})
    (hΩ_frontier : frontier Ω ⊆ {x : X | x = p ∨ σ * G x = b})
    (hΩ_high : ∃ x ∈ Ω, a ≤ σ * G x)
    (hΩ_escapes : ∀ K : Set X, IsCompact K → ∃ x ∈ Ω, x ∉ K)
    (hpole_const :
      ∀ᶠ x in 𝓝[≠] p,
        fixedLevelSignedClip G σ b a x =
          if σ = 1 then (1 : ℝ) else 0)
    (hclip_local_zero :
      ∀ K : Set X, IsCompact K →
        TendstoInLocalL2OnSurface g.volume K
          (fun _ : ℕ ↦ fun _ : X ↦ 0)
          (fixedLevelSignedClip G σ b a)) :
    False := by
  have hclip_meas :
      ∀ K : Set X, IsCompact K →
        AEStronglyMeasurable
          (fixedLevelSignedClip G σ b a)
          (g.volume.restrict K) :=
    fixedLevelSignedClip_aestronglyMeasurable_on_compacts_of_punctured_harmonic
      (g := g) (p := p) G hharmonic hσ hb_pos hba hpole_const
  have hclip_ae_zero :
      ∀ K : Set X, IsCompact K →
        fixedLevelSignedClip G σ b a =ᵐ[g.volume.restrict K] 0 := by
    intro K hK
    exact
      TendstoInLocalL2OnSurface.ae_eq_zero_of_const_zero
        (μ := g.volume) (K := K)
        (hclip_meas K hK)
        (hclip_local_zero K hK)
  exact
    fixedLevelSignedClip_ae_zero_forbidden_escaping_domain
      (g := g) (p := p) G hharmonic hσ hb_pos hba hΩ_open
      hΩ_preconnected hΩ_sublevel hΩ_frontier hΩ_high hΩ_escapes
      hpole_const hclip_ae_zero

/--
%%handwave
name:
  Zero pure fixed-level clips forbid escaping domains
statement:
  Let a signed fixed-level clip represent the zero pure homogeneous
  Dirichlet class.  Then there is no escaping connected open domain contained
  in the strict signed superlevel \(\sigma G>b\), with frontier on the level
  \(\sigma G=b\) away from the pole, which contains a point where
  \(\sigma G\ge a>b\).
proof:
  Positive pure capacity turns equality to the zero pure class into vanishing
  compact-local \(L^2\) trace for the clip.  On a fixed-level domain the clip
  vanishes on the level-\(b\) frontier and is one at a high point.  The
  local maximum principle and the fixed-level transition identity force a
  non-trivial compact-local \(L^2\) contribution on some compact subdomain,
  contradicting zero trace.
-/
theorem fixedLevelSignedClip_zero_completion_forbidden_escaping_domain
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [RiemannSurface X]
    [MeasurableEq X] [SecondCountableTopology X] [ComplexOneManifold X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    (hcap : HasPureDirichletCapacityAtInfinity g)
    (G : X → ℝ)
    (hharmonic : IsHarmonicOnSurface {x : X | x ≠ p} G)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    {Ω : Set X} {b a : ℝ}
    (hb_pos : 0 < b) (hba : b < a)
    (hΩ_open : IsOpen Ω)
    (hΩ_preconnected : IsPreconnected Ω)
    (hΩ_sublevel : Ω ⊆ {x : X | b < σ * G x})
    (hΩ_frontier : frontier Ω ⊆ {x : X | x = p ∨ σ * G x = b})
    (hΩ_high : ∃ x ∈ Ω, a ≤ σ * G x)
    (hΩ_escapes : ∀ K : Set X, IsCompact K → ∃ x ∈ Ω, x ∉ K)
    (hpole_const :
      ∀ᶠ x in 𝓝[≠] p,
        fixedLevelSignedClip G σ b a x =
          if σ = 1 then (1 : ℝ) else 0)
    (hzero_clip :
      ∃ v : GreenSobolevH10SmoothCompactSupport g,
        HasPureH10ScalarRepresentative v
          (fixedLevelSignedClip G σ b a) ∧ v = 0) :
    False := by
  rcases hzero_clip with ⟨v, hv_rep, hv_zero⟩
  have hclip_meas :
      ∀ K : Set X, IsCompact K →
        AEStronglyMeasurable
          (fixedLevelSignedClip G σ b a)
          (g.volume.restrict K) :=
    fixedLevelSignedClip_aestronglyMeasurable_on_compacts_of_punctured_harmonic
      (g := g) (p := p) G hharmonic hσ hb_pos hba hpole_const
  have hclip_local_zero :
      ∀ K : Set X, IsCompact K →
        TendstoInLocalL2OnSurface g.volume K
          (fun _ : ℕ ↦ fun _ : X ↦ 0)
          (fixedLevelSignedClip G σ b a) :=
    HasPureH10ScalarRepresentative.tendsto_localL2_zero_of_eq_zero
      (g := g) hcap hv_rep hv_zero hclip_meas
  exact
    fixedLevelSignedClip_localL2_zero_forbidden_escaping_domain
      (g := g) (p := p) G hharmonic hσ hb_pos hba hΩ_open
      hΩ_preconnected hΩ_sublevel hΩ_frontier hΩ_high hΩ_escapes
      hpole_const hclip_local_zero

/--
%%handwave
name:
  Component-local fixed-level clip
statement:
  The component-local fixed-level clip is the signed fixed-level clip on a
  chosen open component and is zero outside that component.
-/
noncomputable def escapingDomainFixedLevelClip {X : Type}
    (Ω : Set X) (G : X → ℝ) (σ b a : ℝ) : X → ℝ :=
  Ω.indicator (fixedLevelSignedClip G σ b a)

/--
%%handwave
name:
  Component-local clips vanish near the pole when the global clip does
statement:
  If a fixed-level clip is eventually zero in a punctured neighbourhood of the
  pole, then its restriction to any component is also eventually zero there.
proof:
  The component-local clip is either the original clip or zero pointwise.
-/
theorem escapingDomainFixedLevelClip_eventually_eq_zero_of_clip_eventually_eq_zero
    {X : Type} [TopologicalSpace X]
    {p : X} {Ω : Set X} {G : X → ℝ} {σ b a : ℝ}
    (hzero :
      ∀ᶠ x in 𝓝[≠] p,
        fixedLevelSignedClip G σ b a x = 0) :
    ∀ᶠ x in 𝓝[≠] p,
      escapingDomainFixedLevelClip Ω G σ b a x = 0 := by
  filter_upwards [hzero] with x hxzero
  by_cases hxΩ : x ∈ Ω
  · simpa [escapingDomainFixedLevelClip, hxΩ, hxzero] using hxzero
  · simp [escapingDomainFixedLevelClip, hxΩ]

/--
%%handwave
name:
  Component-local clips agree near the pole inside the component
statement:
  If a punctured neighbourhood of the pole lies in the chosen component, then
  the component-local clip agrees there with the original fixed-level clip.
proof:
  On that neighbourhood the indicator of the component acts as the identity.
-/
theorem escapingDomainFixedLevelClip_eventually_eq_clip_of_eventually_mem
    {X : Type} [TopologicalSpace X]
    {p : X} {Ω : Set X} {G : X → ℝ} {σ b a : ℝ}
    (hmem : ∀ᶠ x in 𝓝[≠] p, x ∈ Ω) :
    ∀ᶠ x in 𝓝[≠] p,
      escapingDomainFixedLevelClip Ω G σ b a x =
        fixedLevelSignedClip G σ b a x := by
  filter_upwards [hmem] with x hxΩ
  simp [escapingDomainFixedLevelClip, hxΩ]

/--
%%handwave
name:
  Component-local clips agree with the original clip on compact subdomains
statement:
  On every compact set contained in the chosen component, the component-local
  fixed-level clip agrees almost everywhere with the original signed
  fixed-level clip.
proof:
  On the compact subdomain, the escaping component indicator is eventually one on the relevant component.  Unfold both clips and use the component containment almost everywhere.
-/
theorem escapingDomainFixedLevelClip_eq_clip_ae_restrict_of_subset
    {X : Type} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} {Ω K : Set X} {G : X → ℝ} {σ b a : ℝ}
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    escapingDomainFixedLevelClip Ω G σ b a
      =ᵐ[μ.restrict K] fixedLevelSignedClip G σ b a := by
  exact
    ae_restrict_of_forall_mem hK.measurableSet fun x hxK ↦ by
      simpa [escapingDomainFixedLevelClip] using
        (Set.indicator_of_mem (hKΩ hxK)
          (fixedLevelSignedClip G σ b a))

/--
%%handwave
name:
  Component-local clips are locally measurable
statement:
  If the signed fixed-level clip is measurable on compact sets and the chosen
  component is open, then the component-local fixed-level clip is measurable
  on compact sets.
proof:
  On each compact subdomain the local clip agrees almost everywhere with the globally measurable fixed-level clip; strong measurability transfers across that equality and restriction.
-/
theorem escapingDomainFixedLevelClip_aestronglyMeasurable_on_compacts
    {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} {Ω : Set X} {G : X → ℝ} {σ b a : ℝ}
    (hΩ_open : IsOpen Ω)
    (hclip_meas :
      ∀ K : Set X, IsCompact K →
        AEStronglyMeasurable
          (fixedLevelSignedClip G σ b a) (μ.restrict K)) :
    ∀ K : Set X, IsCompact K →
      AEStronglyMeasurable
        (escapingDomainFixedLevelClip Ω G σ b a) (μ.restrict K) := by
  intro K hK
  simpa [escapingDomainFixedLevelClip] using
    (hclip_meas K hK).indicator hΩ_open.measurableSet

/--
%%handwave
name:
  Zero self-energy gives the zero pure class
statement:
  A pure homogeneous Dirichlet class whose self inner product is zero is the
  zero class.
proof:
  This is definiteness of the Hilbert inner product.
-/
theorem greenSobolevH10SmoothCompactSupport_eq_zero_of_inner_self_eq_zero
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableEq X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X}
    {v : GreenSobolevH10SmoothCompactSupport g}
    (hv : inner ℝ v v = 0) :
    v = 0 := by
  exact inner_self_eq_zero.mp hv

















/--
%%handwave
name:
  Positive high components with pole-free closure cannot be relatively compact
statement:
  Let \(G\) be harmonic away from the pole.  If a connected component of
  \(\{G>b\}\) has closure avoiding the pole and contains a point where
  \(G\ge a>b\), then that component is not contained in any compact subset of
  the surface.
proof:
  If the component had compact closure, \(G-b\) would be harmonic on it and
  continuous on its closure.  Any frontier point with \(G>b\) would still lie
  in the same connected component, so the frontier is bounded by the level
  \(b\).  The harmonic maximum principle contradicts the interior value at
  level at least \(a\).
-/
theorem positive_strictSuperlevel_component_escapes_of_harmonic_maximum_principle
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {p : X} {G : X → ℝ}
    (hharmonic : IsHarmonicOnSurface {x : X | x ≠ p} G)
    {b a : ℝ} (hba : b < a)
    {x : X} (hx_high : a ≤ G x)
    (hU_open : IsOpen {z : X | b < G z})
    (hclosureC :
      closure (connectedComponentIn {z : X | b < G z} x) ⊆
        {z : X | z ≠ p}) :
    ∀ K : Set X, IsCompact K →
      ∃ y ∈ connectedComponentIn {z : X | b < G z} x, y ∉ K := by
  classical
  let U : Set X := {z : X | b < G z}
  let C : Set X := connectedComponentIn U x
  have hxU : x ∈ U := by
    exact lt_of_lt_of_le hba hx_high
  have hpunctured_open : IsOpen {z : X | z ≠ p} :=
    isOpen_ne (x := p)
  have hG_cont_punctured : ContinuousOn G {z : X | z ≠ p} :=
    harmonicOnSurface_continuousOn hpunctured_open hharmonic
  haveI : LocallyConnectedSpace X := ChartedSpace.locallyConnectedSpace ℂ X
  have hC_open : IsOpen C := by
    simpa [C, U] using hU_open.connectedComponentIn (x := x)
  have hC_preconnected : IsPreconnected C := by
    simpa [C, U] using
      (isPreconnected_connectedComponentIn (x := x) (F := U))
  have hC_subsetU : C ⊆ U := by
    simpa [C, U] using (connectedComponentIn_subset U x)
  have hC_subset_punctured : C ⊆ {z : X | z ≠ p} := by
    intro y hyC
    exact hclosureC (subset_closure hyC)
  have hxC : x ∈ C := by
    simpa [C, U] using mem_connectedComponentIn hxU
  intro K hK
  by_contra hno_escape
  push Not at hno_escape
  have hC_subsetK : C ⊆ K := by
    intro y hyC
    exact hno_escape y hyC
  have hclosureC_subsetK : closure C ⊆ K :=
    hK.isClosed.closure_subset_iff.mpr hC_subsetK
  have hC_compact : IsCompact (closure C) :=
    hK.of_isClosed_subset isClosed_closure hclosureC_subsetK
  have hC_nonempty : C.Nonempty := ⟨x, hxC⟩
  have hC_ne_univ : C ≠ Set.univ := by
    intro hC_univ
    have hpC : p ∈ C := by
      rw [hC_univ]
      exact Set.mem_univ p
    exact (hC_subset_punctured hpC) rfl
  have hC_frontier_nonempty : (frontier C).Nonempty :=
    (nonempty_frontier_iff).2 ⟨hC_nonempty, hC_ne_univ⟩
  have hC_frontier_bound :
      ∀ y ∈ frontier C, (fun z : X ↦ G z - b) y ≤ 0 := by
    intro y hy_frontier
    by_contra hnot
    have hyU : y ∈ U := by
      have hy_gt : b < G y := by
        linarith
      exact hy_gt
    have hyC : y ∈ C := by
      simpa [C, U] using
        mem_connectedComponentIn_of_mem_closure_of_mem
          (S := U) (x := x) (y := y) hxU hyU
          (frontier_subset_closure hy_frontier)
    have hy_empty : y ∈ C ∩ frontier C := ⟨hyC, hy_frontier⟩
    simp [hC_open.inter_frontier_eq] at hy_empty
  have hdiff_harmonic :
      IsHarmonicOnSurface C (fun z : X ↦ G z - b) := by
    have hG_C : IsHarmonicOnSurface C G :=
      harmonicOnSurface_mono hC_subset_punctured hharmonic
    have hconst_C : IsHarmonicOnSurface C (fun _ : X ↦ b) :=
      harmonicOnSurface_const C b
    simpa [Pi.sub_apply] using harmonicOnSurface_sub hG_C hconst_C
  have hdiff_continuous :
      ContinuousOn (fun z : X ↦ G z - b) (closure C) := by
    have hG_cont_closure : ContinuousOn G (closure C) :=
      hG_cont_punctured.mono hclosureC
    simpa [Pi.sub_apply] using hG_cont_closure.sub continuousOn_const
  have hx_nonpos : (fun z : X ↦ G z - b) x ≤ 0 :=
    harmonic_nonpositive_of_boundary_nonpositive
      hC_open hC_preconnected hC_compact hC_frontier_nonempty
      hdiff_harmonic hdiff_continuous hC_frontier_bound x hxC
  have hx_pos : 0 < G x - b := by
    linarith
  linarith

/--
%%handwave
name:
  Positive high strict-superlevel components either escape or accumulate at the pole
statement:
  If \(G\) is harmonic away from the pole and a component of \(\{G>b\}\)
  contains a point where \(G\ge a>b\), then either that component escapes
  every compact set or the pole lies in its closure.
proof:
  If the closure avoids the pole, the harmonic maximum principle shows the
  component cannot be relatively compact, hence it escapes every compact set.
  If the closure does not avoid the pole, then the pole belongs to it.
-/
theorem positive_strictSuperlevel_high_component_escapes_or_pole_mem_closure
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {p : X} {G : X → ℝ}
    (hharmonic : IsHarmonicOnSurface {x : X | x ≠ p} G)
    {b a : ℝ} (hba : b < a)
    {x : X} (hx_high : a ≤ G x)
    (hU_open : IsOpen {z : X | b < G z}) :
    (∀ K : Set X, IsCompact K →
      ∃ y ∈ connectedComponentIn {z : X | b < G z} x, y ∉ K) ∨
      p ∈ closure (connectedComponentIn {z : X | b < G z} x) := by
  classical
  by_cases hclosure :
      closure (connectedComponentIn {z : X | b < G z} x) ⊆
        {z : X | z ≠ p}
  · exact Or.inl
      (positive_strictSuperlevel_component_escapes_of_harmonic_maximum_principle
        (p := p) (G := G) hharmonic hba hx_high hU_open hclosure)
  · rw [Set.subset_def] at hclosure
    push Not at hclosure
    rcases hclosure with ⟨y, hy_closure, hyp⟩
    have hyp_eq : y = p := not_not.mp hyp
    exact Or.inr (by simpa [hyp_eq] using hy_closure)

/--
%%handwave
name:
  Positive superlevels adjoined with the pole are closed
statement:
  If \(G\) is harmonic away from \(p\), then for every \(a>0\) the set
  \(\{p\}\cup\{G\ge a\}\) is closed.
proof:
  Away from \(p\), harmonicity implies continuity.  A point outside the
  adjoined superlevel is different from \(p\) and has \(G<a\), so a small
  punctured neighbourhood stays in \(\{G<a\}\).
-/
theorem harmonicOn_punctured_adjoined_positive_superlevel_closed
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {p : X} {G : X → ℝ}
    (hharmonic : IsHarmonicOnSurface {x : X | x ≠ p} G) :
    ∀ a : ℝ, 0 < a → IsClosed ({p} ∪ {x : X | a ≤ G x}) := by
  intro a _ha
  rw [← isOpen_compl_iff]
  refine isOpen_iff_mem_nhds.mpr ?_
  intro x hx
  have hnot_union : x ∉ ({p} ∪ {y : X | a ≤ G y}) := hx
  have hxp : x ≠ p := by
    intro hxeq
    exact hnot_union (Or.inl (by simp [hxeq]))
  have hxlt : G x < a := by
    have hnot_ge : ¬ a ≤ G x := by
      intro hge
      exact hnot_union (Or.inr hge)
    exact lt_of_not_ge hnot_ge
  have hpunc_open : IsOpen ({y : X | y ≠ p}) := by
    simpa using (isOpen_ne (x := p) : IsOpen {y : X | y ≠ p})
  have hpunc_mem : {y : X | y ≠ p} ∈ 𝓝 x :=
    hpunc_open.mem_nhds hxp
  have hcont_at : ContinuousAt G x :=
    ((harmonicOnSurface_continuousOn hpunc_open hharmonic).continuousWithinAt
        hxp).continuousAt hpunc_mem
  have hlt_mem : G ⁻¹' Set.Iio a ∈ 𝓝 x :=
    hcont_at.preimage_mem_nhds (Iio_mem_nhds hxlt)
  refine Filter.mem_of_superset (Filter.inter_mem hpunc_mem hlt_mem) ?_
  intro y hy
  rcases hy with ⟨hypunc, hylt⟩
  have hylt' : G y < a := hylt
  change y ∉ ({p} ∪ {z : X | a ≤ G z})
  intro hyunion
  rcases hyunion with hysing | hysup
  · exact hypunc (by simpa using hysing)
  · exact not_lt_of_ge hysup hylt'

/--
%%handwave
name:
  A bounded component containing all high points makes the adjoined superlevel compact
statement:
  If \(\{p\}\cup\{G\ge a\}\) is closed and all points with \(G\ge a\)
  lie in one strict-superlevel component contained in a compact set, then
  \(\{p\}\cup\{G\ge a\}\) is compact.
proof:
  The adjoined superlevel is a closed subset of the compact union of the pole
  and the compact set containing the component.
-/
theorem adjoined_superlevel_compact_of_high_subset_nonescaping_component
    {X : Type} [TopologicalSpace X]
    {p : X} {G : X → ℝ} {U : Set X} {x : X} {a : ℝ}
    (hclosed : IsClosed ({p} ∪ {z : X | a ≤ G z}))
    (hhigh_subset :
      {z : X | a ≤ G z} ⊆ connectedComponentIn U x)
    (hbounded :
      ∃ K : Set X, IsCompact K ∧ connectedComponentIn U x ⊆ K) :
    IsCompact ({p} ∪ {z : X | a ≤ G z}) := by
  rcases hbounded with ⟨K, hK_compact, hcomponent_subset_K⟩
  have hcompact_union : IsCompact ({p} ∪ K) :=
    isCompact_singleton.union hK_compact
  have hsubset : ({p} ∪ {z : X | a ≤ G z}) ⊆ {p} ∪ K := by
    intro z hz
    rcases hz with hzpole | hzhigh
    · exact Or.inl hzpole
    · exact Or.inr (hcomponent_subset_K (hhigh_subset hzhigh))
  exact hcompact_union.of_isClosed_subset hclosed hsubset

/--
%%handwave
name:
  A pole-accumulating punctured component meets every punctured pole neighbourhood
statement:
  If a set contained in the punctured surface has the pole in its closure,
  then it meets every punctured neighbourhood of the pole.
proof:
  Write the punctured neighbourhood as an ordinary neighbourhood intersected
  with the punctured surface.  Closure at the pole gives a point of the set
  in the ordinary neighbourhood, and containment in the punctured surface
  places it in the punctured neighbourhood.
-/
theorem punctured_set_meets_punctured_nhds_of_pole_mem_closure
    {X : Type} [TopologicalSpace X] {p : X} {C N : Set X}
    (hC_punctured : C ⊆ {x : X | x ≠ p})
    (hpC : p ∈ closure C)
    (hN_nhds : ∃ V : Set X, V ∈ 𝓝 p ∧ V ∩ {x : X | x ≠ p} ⊆ N) :
    (C ∩ N).Nonempty := by
  rcases hN_nhds with ⟨V, hV_nhds, hV_subset_N⟩
  rcases mem_closure_iff_nhds.mp hpC V hV_nhds with ⟨y, hyV, hyC⟩
  exact ⟨y, hyC, hV_subset_N ⟨hyV, hC_punctured hyC⟩⟩

/--
%%handwave
name:
  Strict-superlevel components accumulating at the pole are unique near a connected punctured pole neighbourhood
statement:
  Suppose a preconnected punctured neighbourhood of \(p\) lies in an open
  set \(U\subset X\setminus\{p\}\).  Then any two components of \(U\) whose
  closures contain \(p\) are equal.
proof:
  Each such component meets the punctured neighbourhood.  Since the
  neighbourhood is preconnected and contained in \(U\), all of it lies in the
  same component of \(U\).  Thus the two components share a point, hence are
  the same connected component.
-/
theorem strictSuperlevel_components_with_pole_closure_eq_of_preconnected_punctured_nhds
    {X : Type} [TopologicalSpace X]
    {p : X} {U N : Set X}
    (hN_preconnected : IsPreconnected N)
    (hN_subsetU : N ⊆ U)
    (hN_nhds : ∃ V : Set X, V ∈ 𝓝 p ∧ V ∩ {x : X | x ≠ p} ⊆ N)
    (hU_subset_punctured : U ⊆ {x : X | x ≠ p})
    {x y : X} (_hxU : x ∈ U) (_hyU : y ∈ U)
    (hpx : p ∈ closure (connectedComponentIn U x))
    (hpy : p ∈ closure (connectedComponentIn U y)) :
    connectedComponentIn U x = connectedComponentIn U y := by
  have hCx_punctured :
      connectedComponentIn U x ⊆ {z : X | z ≠ p} :=
    (connectedComponentIn_subset U x).trans hU_subset_punctured
  have hCy_punctured :
      connectedComponentIn U y ⊆ {z : X | z ≠ p} :=
    (connectedComponentIn_subset U y).trans hU_subset_punctured
  rcases
      punctured_set_meets_punctured_nhds_of_pole_mem_closure
        hCx_punctured hpx hN_nhds with
    ⟨nx, hnxCx, hnxN⟩
  rcases
      punctured_set_meets_punctured_nhds_of_pole_mem_closure
        hCy_punctured hpy hN_nhds with
    ⟨ny, hnyCy, hnyN⟩
  have hnyCnx : ny ∈ connectedComponentIn U nx :=
    (hN_preconnected.subset_connectedComponentIn hnxN hN_subsetU) hnyN
  calc
    connectedComponentIn U x = connectedComponentIn U nx :=
      connectedComponentIn_eq hnxCx
    _ = connectedComponentIn U ny :=
      connectedComponentIn_eq hnyCnx
    _ = connectedComponentIn U y :=
      (connectedComponentIn_eq hnyCy).symm

/--
%%handwave
name:
  Punctured complex disks are connected
statement:
  The punctured Euclidean disk \(0<|z-c|<R\) in the complex plane is
  preconnected whenever \(R>0\).
proof:
  Write the disk as the image of \((0,R)\times S^1\) under polar
  coordinates \(z=c+r\omega\).  Both factors are preconnected, and
  continuous images of preconnected sets are preconnected.
-/
theorem complex_punctured_ball_preconnected
    (c : ℂ) {R : ℝ} (_hR : 0 < R) :
    IsPreconnected {z : ℂ | 0 < ‖z - c‖ ∧ ‖z - c‖ < R} := by
  let S : Set (ℝ × ℂ) := Set.Ioo (0 : ℝ) R ×ˢ Metric.sphere (0 : ℂ) 1
  let F : ℝ × ℂ → ℂ := fun q ↦ c + q.1 • q.2
  have hsphere : IsPreconnected (Metric.sphere (0 : ℂ) 1) :=
    isPreconnected_sphere
      (Complex.rank_real_complex ▸ (by norm_num : (1 : Cardinal) < 2))
      (0 : ℂ) 1
  have hS : IsPreconnected S := isPreconnected_Ioo.prod hsphere
  have hcont : ContinuousOn F S := by
    dsimp [F]
    fun_prop
  have hpre : IsPreconnected (F '' S) := hS.image F hcont
  have himage :
      F '' S = {z : ℂ | 0 < ‖z - c‖ ∧ ‖z - c‖ < R} := by
    ext z
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases q with ⟨r, u⟩
      rcases hq with ⟨hr, hu⟩
      have hrpos : 0 < r := hr.1
      have hunorm : ‖u‖ = 1 := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hu
      have hnorm : ‖c + r • u - c‖ = r := by
        simp [sub_eq_add_neg, add_assoc, hunorm, abs_of_nonneg hrpos.le]
      change 0 < ‖c + r • u - c‖ ∧ ‖c + r • u - c‖ < R
      rw [hnorm]
      exact hr
    · intro hz
      let r : ℝ := ‖z - c‖
      rcases hz with ⟨hzpos, hzR⟩
      have hr_ne : r ≠ 0 := ne_of_gt hzpos
      let u : ℂ := (r⁻¹ : ℝ) • (z - c)
      have hu_sphere : u ∈ Metric.sphere (0 : ℂ) 1 := by
        have hunorm : ‖u‖ = 1 := by
          simp [u, r, inv_mul_cancel₀ hr_ne]
        simp [hunorm]
      refine ⟨(r, u), ⟨⟨hzpos, hzR⟩, hu_sphere⟩, ?_⟩
      have hscale : (r : ℝ) • u = z - c := by
        simp [u, hr_ne]
      dsimp [F]
      change c + r • u = z
      rw [hscale]
      simp [sub_eq_add_neg]
  simpa [himage] using hpre

/--
%%handwave
name:
  Punctured coordinate disks are connected
statement:
  A sufficiently small punctured disk in a pointed coordinate chart is
  preconnected.
proof:
  The coordinate chart identifies the punctured coordinate disk with the
  Euclidean punctured disk \(0<|z-z(p)|<R\), and preconnectedness is
  transported by the inverse chart.
-/
theorem pointedCoordinatePuncturedBall_preconnected
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X] {p : X}
    (χ : PointedSurfaceCoordinate X p) {R : ℝ}
    (hR : 0 < R)
    (hball : Metric.ball (χ.chart p) R ⊆ χ.chart.target) :
    IsPreconnected (pointedCoordinateAnnulus X χ 0 R) := by
  let A : Set ℂ :=
    {z : ℂ | 0 < ‖z - χ.chart p‖ ∧ ‖z - χ.chart p‖ < R}
  have hA_target : A ⊆ χ.chart.target := by
    intro z hz
    exact hball (by
      rw [Metric.mem_ball, dist_eq_norm]
      exact hz.2)
  have hU_image :
      pointedCoordinateAnnulus X χ 0 R = χ.chart.symm '' A := by
    ext x
    constructor
    · intro hx
      refine ⟨χ.chart x, ?_, χ.chart.left_inv hx.1⟩
      exact hx.2
    · rintro ⟨z, hz, rfl⟩
      have hz_target : z ∈ χ.chart.target := hA_target hz
      exact ⟨χ.chart.map_target hz_target, by
        change
          0 < ‖χ.chart (χ.chart.symm z) - χ.chart p‖ ∧
            ‖χ.chart (χ.chart.symm z) - χ.chart p‖ < R
        rw [χ.chart.right_inv hz_target]
        exact hz⟩
  rw [hU_image]
  exact (complex_punctured_ball_preconnected (χ.chart p) hR).image
    χ.chart.symm (χ.chart.continuousOn_symm.mono hA_target)

/--
%%handwave
name:
  Logarithmic blow-up contains a connected punctured pole neighbourhood in every positive superlevel
statement:
  If \(G\) has a logarithmic pole at \(p\), then for every \(b>0\) there is
  a preconnected punctured neighbourhood of \(p\) contained in \(\{G>b\}\).
proof:
  The logarithmic asymptotic gives \(G\to+\infty\) through the punctured
  neighbourhood filter.  Choose a small punctured coordinate disk on which
  \(G>b\); such a punctured disk is preconnected.
-/
theorem logarithmic_singularity_positive_strictSuperlevel_has_preconnected_punctured_nhds
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {p : X} {G : X → ℝ}
    (hlog :
      ∀ χ : PointedSurfaceCoordinate X p,
        ∃ H : X → ℝ,
          IsHarmonicOnSurface χ.chart.source H ∧
            ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
              G x + Real.log ‖χ.chart x - χ.chart p‖ = H x)
    {b : ℝ} (_hb_pos : 0 < b) :
    ∃ N : Set X,
      IsPreconnected N ∧
        N ⊆ {x : X | b < G x} ∧
          ∃ V : Set X, V ∈ 𝓝 p ∧ V ∩ {x : X | x ≠ p} ⊆ N := by
  let χ : PointedSurfaceCoordinate X p :=
    { chart := chartAt ℂ p
      chart_mem_atlas := chart_mem_atlas ℂ p
      base_mem_source := mem_chart_source ℂ p }
  have hblow : Filter.Tendsto G (𝓝[≠] p) Filter.atTop :=
    logarithmic_singularity_tendsto_atTop X p hlog
  have hnear_gt : {x : X | b < G x} ∈ 𝓝[≠] p :=
    hblow.eventually_gt_atTop b
  rcases
      mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hnear_gt with
    ⟨W, hW_nhds, hW_subset⟩
  have hc_target : χ.chart p ∈ χ.chart.target :=
    χ.chart.map_source χ.base_mem_source
  have hW_pre :
      χ.chart.symm ⁻¹' W ∈ 𝓝 (χ.chart p) :=
    χ.chart.continuousAt_symm hc_target
      (by simpa [χ.chart.left_inv χ.base_mem_source] using hW_nhds)
  rcases Metric.mem_nhds_iff.mp hW_pre with
    ⟨δW, hδW_pos, hδW⟩
  rcases Metric.mem_nhds_iff.mp (χ.chart.open_target.mem_nhds hc_target) with
    ⟨δT, hδT_pos, hδT⟩
  let R : ℝ := min δW δT / 2
  have hmin_pos : 0 < min δW δT := lt_min hδW_pos hδT_pos
  have hR_pos : 0 < R := by
    dsimp [R]
    linarith
  have hR_lt_min : R < min δW δT := by
    dsimp [R]
    linarith
  have hR_lt_δW : R < δW :=
    hR_lt_min.trans_le (min_le_left δW δT)
  have hR_lt_δT : R < δT :=
    hR_lt_min.trans_le (min_le_right δW δT)
  have hball_W :
      Metric.ball (χ.chart p) R ⊆ χ.chart.symm ⁻¹' W := by
    intro z hz
    exact hδW (by
      rw [Metric.mem_ball] at hz ⊢
      exact hz.trans hR_lt_δW)
  have hball_target :
      Metric.ball (χ.chart p) R ⊆ χ.chart.target := by
    intro z hz
    exact hδT (by
      rw [Metric.mem_ball] at hz ⊢
      exact hz.trans hR_lt_δT)
  refine ⟨pointedCoordinateAnnulus X χ 0 R, ?_, ?_, ?_⟩
  · exact pointedCoordinatePuncturedBall_preconnected X χ hR_pos hball_target
  · intro x hx
    have hxsource : x ∈ χ.chart.source := hx.1
    have hxball : χ.chart x ∈ Metric.ball (χ.chart p) R := by
      rw [Metric.mem_ball, dist_eq_norm]
      exact hx.2.2
    have hxW_symm : χ.chart.symm (χ.chart x) ∈ W :=
      hball_W hxball
    have hxW : x ∈ W := by
      simpa [χ.chart.left_inv hxsource] using hxW_symm
    have hxne : x ≠ p := by
      intro hxp
      have hzero : ‖χ.chart x - χ.chart p‖ = 0 := by
        simp [hxp]
      have hposnorm : 0 < ‖χ.chart x - χ.chart p‖ := hx.2.1
      rw [hzero] at hposnorm
      exact (lt_irrefl (0 : ℝ)) hposnorm
    exact hW_subset ⟨hxW, hxne⟩
  · let V : Set X :=
      χ.chart.source ∩ χ.chart ⁻¹' Metric.ball (χ.chart p) R
    have hsource_nhds : χ.chart.source ∈ 𝓝 p :=
      χ.chart.open_source.mem_nhds χ.base_mem_source
    have hball_nhds :
        χ.chart ⁻¹' Metric.ball (χ.chart p) R ∈ 𝓝 p :=
      (χ.chart.continuousAt χ.base_mem_source).preimage_mem_nhds
        (Metric.ball_mem_nhds (χ.chart p) hR_pos)
    have hV_nhds : V ∈ 𝓝 p :=
      Filter.inter_mem hsource_nhds hball_nhds
    refine ⟨V, hV_nhds, ?_⟩
    intro x hx
    rcases hx with ⟨hxV, hxne⟩
    rcases hxV with ⟨hxsource, hxball⟩
    have hpos : 0 < ‖χ.chart x - χ.chart p‖ := by
      refine norm_pos_iff.mpr ?_
      intro hzero
      have hEq : χ.chart x = χ.chart p := sub_eq_zero.mp hzero
      exact hxne (χ.chart.injOn hxsource χ.base_mem_source hEq)
    have hltR : ‖χ.chart x - χ.chart p‖ < R := by
      simpa [Metric.mem_ball, dist_eq_norm] using hxball
    exact ⟨hxsource, hpos, hltR⟩

/--
%%handwave
name:
  A noncompact positive superlevel has an escaping high strict-superlevel component
statement:
  If the adjoined positive superlevel \(\{p\}\cup\{G\ge a\}\) is noncompact
  for a nonnegative pole-normalized logarithmic potential, then some point
  with \(G\ge a\) lies in a connected component of \(\{G>a/2\}\) which
  escapes every compact subset.
proof:
  The logarithmic singularity gives a punctured neighbourhood of the pole
  contained in \(\{G>a/2\}\), hence there is a unique pole-adjacent
  strict-superlevel component.  If that component escapes, it already gives
  the conclusion.  Otherwise its high part is compact after adjoining the
  pole.  Noncompactness of \(\{p\}\cup\{G\ge a\}\) then gives a high point in
  another component; that component has closure avoiding the pole, so the
  harmonic maximum principle forces it to escape.
-/
theorem noncompact_poleNormalized_positive_superlevel_has_escaping_high_component
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [RiemannSurface X]
    [MeasurableEq X] [SecondCountableTopology X] [ComplexOneManifold X]
    [SimplyConnectedSpace X] [NoncompactSpace X]
    [IsManifold SurfaceRealModel ∞ X]
    {p : X} (G : X → ℝ)
    (hharmonic : IsHarmonicOnSurface {x : X | x ≠ p} G)
    (hlog :
      ∀ χ : PointedSurfaceCoordinate X p,
        ∃ H : X → ℝ,
          IsHarmonicOnSurface χ.chart.source H ∧
            ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
              G x + Real.log ‖χ.chart x - χ.chart p‖ = H x)
    (hp_zero : G p = 0)
    (_hnonnegative : ∀ x : X, 0 ≤ G x)
    {a : ℝ} (ha : 0 < a)
    (hnoncompact : ¬ IsCompact ({p} ∪ {x : X | a ≤ G x})) :
    ∃ x : X,
      a ≤ G x ∧
        ∀ K : Set X, IsCompact K →
          ∃ y ∈ connectedComponentIn {z : X | a / 2 < G z} x, y ∉ K := by
  classical
  let U : Set X := {z : X | a / 2 < G z}
  have hb_pos : 0 < a / 2 := by
    linarith
  have hba : a / 2 < a := by
    linarith
  have hpb : G p < a / 2 := by
    simpa [hp_zero] using hb_pos
  have hU_open : IsOpen U := by
    simpa [U] using
      harmonicOn_punctured_positive_strictSuperlevel_open
        (p := p) hharmonic hpb
  have hU_subset_punctured : U ⊆ {z : X | z ≠ p} := by
    intro z hz hzp
    have hz_at_p : a / 2 < G p := by
      simpa [U, hzp] using hz
    linarith
  have hclosedS :
      IsClosed ({p} ∪ {x : X | a ≤ G x}) :=
    harmonicOn_punctured_adjoined_positive_superlevel_closed
      (p := p) (G := G) hharmonic a ha
  rcases
      logarithmic_singularity_positive_strictSuperlevel_has_preconnected_punctured_nhds
        (X := X) (p := p) (G := G) hlog hb_pos with
    ⟨N, hN_preconnected, hN_subsetU_raw, hN_nhds⟩
  have hN_subsetU : N ⊆ U := by
    simpa [U] using hN_subsetU_raw
  have hhigh_nonempty : ∃ x : X, a ≤ G x := by
    by_contra hnone
    have hS_eq : ({p} ∪ {x : X | a ≤ G x}) = ({p} : Set X) := by
      ext x
      constructor
      · intro hx
        rcases hx with hx_pole | hx_high
        · exact hx_pole
        · exact False.elim (hnone ⟨x, hx_high⟩)
      · intro hx
        exact Or.inl hx
    exact hnoncompact (by simpa [hS_eq] using
      (isCompact_singleton : IsCompact ({p} : Set X)))
  rcases hhigh_nonempty with ⟨x₀, hx₀_high⟩
  by_contra hno_escape_high
  have hnot_escape_of_high :
      ∀ x : X, a ≤ G x →
        ¬ ∀ K : Set X, IsCompact K →
          ∃ y ∈ connectedComponentIn U x, y ∉ K := by
    intro x hx_high hesc
    exact hno_escape_high ⟨x, hx_high, by simpa [U] using hesc⟩
  have hbounded_of_high :
      ∀ x : X, a ≤ G x →
        ∃ K : Set X, IsCompact K ∧ connectedComponentIn U x ⊆ K := by
    intro x hx_high
    by_contra hnot_bounded
    have hesc :
        ∀ K : Set X, IsCompact K →
          ∃ y ∈ connectedComponentIn U x, y ∉ K := by
      intro K hK
      by_contra hno_y
      have hC_subsetK : connectedComponentIn U x ⊆ K := by
        intro y hyC
        by_contra hyK
        exact hno_y ⟨y, hyC, hyK⟩
      exact hnot_bounded ⟨K, hK, hC_subsetK⟩
    exact (hnot_escape_of_high x hx_high) hesc
  have hp_closure_of_high :
      ∀ x : X, a ≤ G x →
        p ∈ closure (connectedComponentIn U x) := by
    intro x hx_high
    have hdich :
        (∀ K : Set X, IsCompact K →
          ∃ y ∈ connectedComponentIn U x, y ∉ K) ∨
          p ∈ closure (connectedComponentIn U x) := by
      simpa [U] using
        positive_strictSuperlevel_high_component_escapes_or_pole_mem_closure
          (p := p) (G := G) hharmonic hba hx_high hU_open
    rcases hdich with hesc | hpcl
    · exact False.elim ((hnot_escape_of_high x hx_high) hesc)
    · exact hpcl
  have hx₀U : x₀ ∈ U := by
    exact lt_of_lt_of_le hba hx₀_high
  have hhigh_subset_component :
      {x : X | a ≤ G x} ⊆ connectedComponentIn U x₀ := by
    intro x hx_high
    have hxU : x ∈ U := lt_of_lt_of_le hba hx_high
    have hcomponent_eq :
        connectedComponentIn U x = connectedComponentIn U x₀ :=
      strictSuperlevel_components_with_pole_closure_eq_of_preconnected_punctured_nhds
        hN_preconnected hN_subsetU hN_nhds hU_subset_punctured
        hxU hx₀U (hp_closure_of_high x hx_high)
        (hp_closure_of_high x₀ hx₀_high)
    have hx_component : x ∈ connectedComponentIn U x :=
      mem_connectedComponentIn hxU
    simpa [hcomponent_eq] using hx_component
  have hbounded₀ :
      ∃ K : Set X, IsCompact K ∧ connectedComponentIn U x₀ ⊆ K :=
    hbounded_of_high x₀ hx₀_high
  exact hnoncompact
    (adjoined_superlevel_compact_of_high_subset_nonescaping_component
      (p := p) (G := G) (U := U) (x := x₀) (a := a)
      hclosedS hhigh_subset_component hbounded₀)

/--
%%handwave
name:
  A noncompact positive superlevel produces a pole-aware escaping level domain
statement:
  If an adjoined positive superlevel of the regular Green potential is not
  compact, then for the fixed levels \(a/2<a\) there is a connected open
  region of \(\{G>a/2\}\) escaping every compact set, whose frontier lies on
  the level \(a/2\) except possibly at the pole, and which contains a point
  where \(G\ge a\).
proof:
  On a noncompact simply connected surface, the unbounded part of a
  noncompact superlevel must determine an escaping strict-superlevel
  component.  Components whose closures avoid the pole are handled by the
  harmonic maximum principle.  If the escaping component is the pole-adjacent
  one, the logarithmic singularity makes the pole the only possible
  exceptional frontier point below the fixed level.
-/
theorem noncompact_poleNormalized_positive_superlevel_has_poleAware_escaping_level_domain
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [RiemannSurface X]
    [MeasurableEq X] [SecondCountableTopology X] [ComplexOneManifold X]
    [SimplyConnectedSpace X] [NoncompactSpace X]
    [IsManifold SurfaceRealModel ∞ X]
    {p : X} (G : X → ℝ)
    (hharmonic : IsHarmonicOnSurface {x : X | x ≠ p} G)
    (hlog :
      ∀ χ : PointedSurfaceCoordinate X p,
        ∃ H : X → ℝ,
          IsHarmonicOnSurface χ.chart.source H ∧
            ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
              G x + Real.log ‖χ.chart x - χ.chart p‖ = H x)
    (hp_zero : G p = 0)
    (hnonnegative : ∀ x : X, 0 ≤ G x)
    {a : ℝ} (ha : 0 < a)
    (hnoncompact : ¬ IsCompact ({p} ∪ {x : X | a ≤ G x})) :
    ∃ Ω : Set X,
      IsOpen Ω ∧
        IsPreconnected Ω ∧
          Ω ⊆ {x : X | a / 2 < G x} ∧
            frontier Ω ⊆ {x : X | x = p ∨ G x = a / 2} ∧
              (∃ x ∈ Ω, a ≤ G x) ∧
                ∀ K : Set X, IsCompact K → ∃ x ∈ Ω, x ∉ K := by
  rcases
      noncompact_poleNormalized_positive_superlevel_has_escaping_high_component
        G hharmonic hlog hp_zero hnonnegative ha hnoncompact with
    ⟨x, hx_high, hescapes⟩
  have hb_pos : 0 < a / 2 := by
    linarith
  have hba : a / 2 < a := by
    linarith
  have hpb : G p < a / 2 := by
    simpa [hp_zero] using hb_pos
  have hU_open : IsOpen {z : X | a / 2 < G z} :=
    harmonicOn_punctured_positive_strictSuperlevel_open
      (p := p) hharmonic hpb
  have hU_subset_punctured :
      {z : X | a / 2 < G z} ⊆ {z : X | z ≠ p} := by
    intro z hz hzp
    have hz_at_p : a / 2 < G p := by
      simpa [hzp] using hz
    linarith
  have hpunctured_open : IsOpen {z : X | z ≠ p} :=
    isOpen_ne (x := p)
  have hcont_punctured :
      ContinuousOn G {z : X | z ≠ p} :=
    harmonicOnSurface_continuousOn hpunctured_open hharmonic
  exact
    continuousOn_punctured_escaping_strictSuperlevel_component_yields_poleAware_level_domain
      (p := p) (f := G) hba hx_high hU_open hU_subset_punctured
      hcont_punctured hescapes

/--
%%handwave
name:
  Riesz-data form of the pole-aware escaping positive-level domain
statement:
  For the regular representative attached to the pure energy construction, a
  noncompact positive superlevel produces the same pole-aware escaping
  fixed-level domain.
proof:
  This is the function-theoretic extraction theorem applied to the regular
  representative; the variational data are carried only so the statement can
  be used directly in the energy-method proof.
-/
theorem noncompact_regular_positive_superlevel_has_high_component_away_from_pole
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [RiemannSurface X]
    [MeasurableEq X] [SecondCountableTopology X] [ComplexOneManifold X]
    [SimplyConnectedSpace X] [NoncompactSpace X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    (φ : LogarithmicCutoffPoleModel g p)
    (source : (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ)
    (hdata :
      GreenSobolevH10SmoothCompactSupportLocalWeakCorrectionData
        φ source)
    (G : X → ℝ)
    (_hrep :
      ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X),
        (fun w : ℂ ↦ localEnergyGreenPotential φ hdata.correction
          (e.symm w))
          =ᵐ[MeasureTheory.volume.restrict
            (e.target ∩ e.symm ⁻¹' {x : X | x ≠ p})]
            (fun w : ℂ ↦ G (e.symm w)))
    (hharmonic : IsHarmonicOnSurface {x : X | x ≠ p} G)
    (hlog :
      ∀ χ : PointedSurfaceCoordinate X p,
        ∃ H : X → ℝ,
          IsHarmonicOnSurface χ.chart.source H ∧
            ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
              G x + Real.log ‖χ.chart x - χ.chart p‖ = H x)
    (hp_zero : G p = 0)
    (hnonnegative : ∀ x : X, 0 ≤ G x)
    {a : ℝ} (ha : 0 < a)
    (hnoncompact : ¬ IsCompact ({p} ∪ {x : X | a ≤ G x})) :
    ∃ Ω : Set X,
      IsOpen Ω ∧
        IsPreconnected Ω ∧
          Ω ⊆ {x : X | a / 2 < G x} ∧
            frontier Ω ⊆ {x : X | x = p ∨ G x = a / 2} ∧
              (∃ x ∈ Ω, a ≤ G x) ∧
                ∀ K : Set X, IsCompact K → ∃ x ∈ Ω, x ∉ K :=
  noncompact_poleNormalized_positive_superlevel_has_poleAware_escaping_level_domain
    G hharmonic hlog hp_zero hnonnegative ha hnoncompact

/--
%%handwave
name:
  The Riesz correction is weakly harmonic outside the pole and the source support
statement:
  The scalar correction in the pure Riesz construction is weakly harmonic on
  the complement of the pole together with the closed support of the cutoff
  source.
proof:
  Restrict the stored opposite-source equation to the complement of the pole
  and of the closed source support.  On this open set the source is
  identically zero, so the weak source equation becomes weak harmonicity.
-/
theorem
    greenSobolevH10SmoothCompactSupportLocalWeakCorrectionData_correction_weaklyHarmonicOn_compl_pole_sourceSupport
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [RiemannSurface X]
    [T1Space X] [MeasurableEq X] [SecondCountableTopology X]
    [ComplexOneManifold X] [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    {φ : LogarithmicCutoffPoleModel g p}
    {source : (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ}
    (hdata :
      GreenSobolevH10SmoothCompactSupportLocalWeakCorrectionData
        φ source) :
    IsWeaklyHarmonicOnSurface g
      ({p}ᶜ ∩ (closure {x : X | φ.source x ≠ 0})ᶜ)
      hdata.correction.toFun := by
  classical
  letI : IsManifold SurfaceRealModel 1 X := inferInstance
  let U : Set X := {p}ᶜ ∩ (closure {x : X | φ.source x ≠ 0})ᶜ
  have hU_open : IsOpen U := by
    exact (isOpen_ne (x := p)).inter isClosed_closure.isOpen_compl
  have hU_subset_punctured : U ⊆ {x : X | x ≠ p} := by
    intro x hxU hxp
    exact hxU.1 (by simp [hxp])
  have hsource_zero : ∀ x ∈ U, φ.source x = 0 := by
    intro x hxU
    by_contra hnonzero
    exact hxU.2 (subset_closure hnonzero)
  have hweak_source :
      IsWeakLaplaceBeltramiSourceOnSurface g U
        hdata.correction.toFun (fun x : X ↦ -φ.source x) :=
    hdata.punctured_opposite_source.mono_set hU_open hU_subset_punctured
  have hweak_zero :
      IsWeakLaplaceBeltramiSourceOnSurface g U
        hdata.correction.toFun (fun _ : X ↦ 0) :=
    hweak_source.congr_source (by
      intro x hxU
      simp [hsource_zero x hxU])
  simpa [U] using
    weaklyHarmonicOnSurface_of_weakLaplaceBeltramiSource_zero hweak_zero

/--
%%handwave
name:
  Weak harmonicity restricts to smaller open sets
statement:
  If a scalar function is weakly harmonic on an open set, then it is weakly
  harmonic on every smaller open set.
proof:
  Restrict the local Sobolev representative and test the original weak
  equation with the same compactly supported coordinate test, viewed as a
  test on the larger chart region.
-/
theorem IsWeaklyHarmonicOnSurface.mono_set {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X]
    [BorelSpace X] [IsManifold SurfaceRealModel 1 X]
    {g : BackgroundSurfaceMetricOnSurface X} {V U : Set X}
    {u : X → ℝ}
    (hweak : IsWeaklyHarmonicOnSurface g U u)
    (hV_open : IsOpen V) (hVU : V ⊆ U) :
    IsWeaklyHarmonicOnSurface g V u := by
  rcases hweak with ⟨_hU_open, du, hlocal, htest⟩
  refine ⟨hV_open, du, hlocal.mono_set hVU, ?_⟩
  intro e he η
  let ΩV : Set ℂ := surfaceChartRegion e V
  let ΩU : Set ℂ := surfaceChartRegion e U
  have hΩVU : ΩV ⊆ ΩU := by
    intro z hz
    exact ⟨hz.1, hVU hz.2⟩
  let ψ : SmoothCompactlySupportedManifoldCoordinateFunction ΩU :=
    η.mono hΩVU
  rcases htest e he ψ with ⟨hgradΩ, heqΩ⟩
  let gradTerm : ℂ → ℝ :=
    fun z ↦
      surfaceMetricWeakGradientCoordinatePairingInChart g e z
        (du (e.symm z))
        (fderiv ℝ (η : ℂ → ℝ) z) *
          surfaceMetricVolumeDensityInChart g.metric e z
  have hgrad_int_V :
      Integrable gradTerm (MeasureTheory.volume.restrict ΩV) := by
    have hres := hgradΩ.restrict (s := ΩV)
    simpa [gradTerm, ψ, ΩV, ΩU,
      Measure.restrict_restrict_of_subset hΩVU] using hres
  have hgrad_zero_V : ∀ z : ℂ, z ∉ ΩV → gradTerm z = 0 := by
    intro z hzV
    have hdη_zero : fderiv ℝ (η : ℂ → ℝ) z = 0 := by
      ext v
      have hz_not :
          z ∉ tsupport (fun y : ℂ ↦ fderiv ℝ (η : ℂ → ℝ) y v) := by
        intro hz
        exact hzV <| η.support_subset <|
          (tsupport_fderiv_apply_subset (𝕜 := ℝ)
            (f := (η : ℂ → ℝ)) v) hz
      exact
        image_eq_zero_of_notMem_tsupport
          (f := fun y : ℂ ↦ fderiv ℝ (η : ℂ → ℝ) y v) hz_not
    simp [gradTerm, hdη_zero, surfaceMetricWeakGradientCoordinatePairingInChart]
  have hgrad_zero_U : ∀ z : ℂ, z ∉ ΩU → gradTerm z = 0 := by
    intro z hzU
    exact hgrad_zero_V z (fun hzV ↦ hzU (hΩVU hzV))
  have hgrad_V_eq_U :
      ∫ z in ΩV, gradTerm z ∂MeasureTheory.volume =
        ∫ z in ΩU, gradTerm z ∂MeasureTheory.volume := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hgrad_zero_V,
      setIntegral_eq_integral_of_forall_compl_eq_zero hgrad_zero_U]
  refine ⟨?_, ?_⟩
  · simpa [gradTerm, ΩV] using hgrad_int_V
  · calc
      ∫ z in surfaceChartRegion e V,
          surfaceMetricWeakGradientCoordinatePairingInChart g e z
            (du (e.symm z))
            (fderiv ℝ (η : ℂ → ℝ) z) *
              surfaceMetricVolumeDensityInChart g.metric e z
          ∂MeasureTheory.volume =
          ∫ z in ΩV, gradTerm z ∂MeasureTheory.volume := rfl
      _ = ∫ z in ΩU, gradTerm z ∂MeasureTheory.volume := hgrad_V_eq_U
      _ = 0 := by simpa [gradTerm, ψ, ΩU] using heqΩ




/--
%%handwave
name:
  Negative strict superlevels stay away from the logarithmic pole
statement:
  If a pole-normalized regular potential tends to \(+\infty\) at the pole,
  then the closure of every positive strict superlevel of \(-G\) avoids the
  pole.
proof:
  Near the puncture the logarithmic singularity makes \(G\) nonnegative.
  Together with the normalized value \(G(p)=0\), this gives a full
  neighbourhood of \(p\) disjoint from \(\{-G>b\}\) for every \(b>0\).
-/
theorem logarithmic_singularity_negative_strictSuperlevel_closure_subset_punctured
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [RiemannSurface X]
    [IsManifold SurfaceRealModel ∞ X]
    {p : X} (G : X → ℝ)
    (hlog :
      ∀ χ : PointedSurfaceCoordinate X p,
        ∃ H : X → ℝ,
          IsHarmonicOnSurface χ.chart.source H ∧
            ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
              G x + Real.log ‖χ.chart x - χ.chart p‖ = H x)
    (hp_zero : G p = 0) {b : ℝ} (hb_pos : 0 < b) :
    closure {x : X | b < -G x} ⊆ {x : X | x ≠ p} := by
  classical
  let U : Set X := {x : X | b < -G x}
  have hblow : Filter.Tendsto G (𝓝[≠] p) Filter.atTop :=
    logarithmic_singularity_tendsto_atTop X p hlog
  have hnear_within : ∀ᶠ x in 𝓝[≠] p, 0 ≤ G x :=
    hblow.eventually_ge_atTop 0
  have hnear_nhds :
      ∀ᶠ x in 𝓝 p, x ∈ {x : X | x ≠ p} → 0 ≤ G x :=
    eventually_nhdsWithin_iff.mp hnear_within
  have hnotU_nhds : Uᶜ ∈ 𝓝 p := by
    filter_upwards [hnear_nhds] with x hxnear hxU
    by_cases hxp : x = p
    · have hnot : ¬ b < -G x := by
        rw [hxp, hp_zero]
        linarith
      exact hnot hxU
    · have hx_nonneg : 0 ≤ G x := hxnear hxp
      have hnot : ¬ b < -G x := by
        linarith
      exact hnot hxU
  have hp_not_closure : p ∉ closure U := by
    intro hp_closure
    rcases mem_closure_iff_nhds.mp hp_closure Uᶜ hnotU_nhds with
      ⟨y, hy_notU, hyU⟩
    exact hy_notU hyU
  intro x hx_closure hxp
  have hp_closure : p ∈ closure U := by
    simpa [U, hxp] using hx_closure
  exact hp_not_closure hp_closure

/--
%%handwave
name:
  Negative high components cannot be relatively compact
statement:
  Let \(G\) be harmonic on the punctured surface.  If the closure of
  \(\{-G>b\}\) avoids the pole and a component of this strict superlevel
  contains a point where \(-G\ge a>b\), then that component is not contained
  in any compact subset of the surface.
proof:
  If the component had compact closure, \(-G\) would be harmonic on it and
  continuous on its closure.  The frontier is contained in the level
  \(-G=b\), while the component contains a point where \(-G\ge a>b\).  The
  harmonic maximum principle then gives a contradiction.
-/
theorem negative_strictSuperlevel_component_escapes_of_harmonic_minimum_principle
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [RiemannSurface X]
    {p : X} {G : X → ℝ}
    (hharmonic : IsHarmonicOnSurface {x : X | x ≠ p} G)
    {b a : ℝ} (_hb_pos : 0 < b) (hba : b < a)
    {x : X} (hx_high : a ≤ -G x)
    (hclosureU :
      closure {z : X | b < -G z} ⊆ {z : X | z ≠ p}) :
    ∀ K : Set X, IsCompact K →
      ∃ y ∈ connectedComponentIn {z : X | b < -G z} x, y ∉ K := by
  classical
  let U : Set X := {z : X | b < -G z}
  let C : Set X := connectedComponentIn U x
  have hxU : x ∈ U := by
    exact lt_of_lt_of_le hba hx_high
  have hU_subset_punctured : U ⊆ {z : X | z ≠ p} := by
    intro y hyU
    exact hclosureU (subset_closure hyU)
  have hneg_harmonic :
      IsHarmonicOnSurface {z : X | z ≠ p} (fun z : X ↦ -G z) :=
    harmonicOnSurface_neg hharmonic
  have hpunctured_open : IsOpen {z : X | z ≠ p} :=
    isOpen_ne (x := p)
  have hneg_cont_punctured :
      ContinuousOn (fun z : X ↦ -G z) {z : X | z ≠ p} :=
    harmonicOnSurface_continuousOn hpunctured_open hneg_harmonic
  have hU_open : IsOpen U := by
    have hopen_inter :
        IsOpen ({z : X | z ≠ p} ∩
          (fun z : X ↦ -G z) ⁻¹' Set.Ioi b) :=
      hneg_cont_punctured.isOpen_inter_preimage hpunctured_open isOpen_Ioi
    have hset :
        U = {z : X | z ≠ p} ∩
          (fun z : X ↦ -G z) ⁻¹' Set.Ioi b := by
      ext y
      constructor
      · intro hy
        exact ⟨hU_subset_punctured hy, hy⟩
      · intro hy
        exact hy.2
    simpa [hset] using hopen_inter
  haveI : LocallyConnectedSpace X := ChartedSpace.locallyConnectedSpace ℂ X
  have hC_open : IsOpen C := by
    simpa [C] using hU_open.connectedComponentIn (x := x)
  have hC_preconnected : IsPreconnected C := by
    simpa [C] using (isPreconnected_connectedComponentIn (x := x) (F := U))
  have hC_subsetU : C ⊆ U := by
    simpa [C] using (connectedComponentIn_subset U x)
  have hC_subset_punctured : C ⊆ {z : X | z ≠ p} :=
    hC_subsetU.trans hU_subset_punctured
  have hclosureC_subset_punctured : closure C ⊆ {z : X | z ≠ p} :=
    (closure_mono hC_subsetU).trans hclosureU
  have hxC : x ∈ C := by
    simpa [C] using mem_connectedComponentIn hxU
  intro K hK
  by_contra hno_escape
  push Not at hno_escape
  have hC_subsetK : C ⊆ K := by
    intro y hyC
    exact hno_escape y hyC
  have hclosureC_subsetK : closure C ⊆ K :=
    hK.isClosed.closure_subset_iff.mpr hC_subsetK
  have hC_compact : IsCompact (closure C) :=
    hK.of_isClosed_subset isClosed_closure hclosureC_subsetK
  have hC_nonempty : C.Nonempty := ⟨x, hxC⟩
  have hC_ne_univ : C ≠ Set.univ := by
    intro hC_univ
    have hpC : p ∈ C := by
      rw [hC_univ]
      exact Set.mem_univ p
    exact (hC_subset_punctured hpC) rfl
  have hC_frontier_nonempty : (frontier C).Nonempty :=
    (nonempty_frontier_iff).2 ⟨hC_nonempty, hC_ne_univ⟩
  have hC_frontier_bound :
      ∀ y ∈ frontier C, (fun z : X ↦ -G z - b) y ≤ 0 := by
    intro y hy_frontier
    by_contra hnot
    have hyU : y ∈ U := by
      have hy_gt : b < -G y := by
        linarith
      exact hy_gt
    have hyC : y ∈ C := by
      simpa [C] using
        mem_connectedComponentIn_of_mem_closure_of_mem
          (S := U) (x := x) (y := y) hxU hyU
          (frontier_subset_closure hy_frontier)
    have hy_empty : y ∈ C ∩ frontier C := ⟨hyC, hy_frontier⟩
    simp [hC_open.inter_frontier_eq] at hy_empty
  have hdiff_harmonic :
      IsHarmonicOnSurface C (fun z : X ↦ -G z - b) := by
    have hneg_C : IsHarmonicOnSurface C (fun z : X ↦ -G z) :=
      harmonicOnSurface_mono hC_subset_punctured hneg_harmonic
    have hconst_C : IsHarmonicOnSurface C (fun _ : X ↦ b) :=
      harmonicOnSurface_const C b
    simpa [Pi.sub_apply] using harmonicOnSurface_sub hneg_C hconst_C
  have hdiff_continuous :
      ContinuousOn (fun z : X ↦ -G z - b) (closure C) := by
    have hneg_cont_closure :
        ContinuousOn (fun z : X ↦ -G z) (closure C) :=
      hneg_cont_punctured.mono hclosureC_subset_punctured
    simpa [Pi.sub_apply] using hneg_cont_closure.sub continuousOn_const
  have hx_nonpos : (fun z : X ↦ -G z - b) x ≤ 0 :=
    harmonic_nonpositive_of_boundary_nonpositive
      hC_open hC_preconnected hC_compact hC_frontier_nonempty
      hdiff_harmonic hdiff_continuous hC_frontier_bound x hxC
  have hx_pos : 0 < -G x - b := by
    linarith
  linarith

/--
%%handwave
name:
  A negative value has an escaping negative strict-superlevel component
statement:
  Let \(G\) be pole-normalized, harmonic away from the pole, and logarithmic
  at the pole.  If \(-G\ge a>b>0\) somewhere, then the connected component of
  \(\{-G>b\}\) through some such point escapes every compact set and its
  closure avoids the pole.
proof:
  The pole normalization and logarithmic blow-up keep \(\{-G>b\}\) away from
  a neighbourhood of the pole.  If the component through a negative high
  point were relatively compact, the harmonic minimum principle on the
  punctured surface, with boundary level \(-b\), would contradict the
  existence of an interior value at most \(-a\).  Therefore that component is
  not contained in any compact set.
-/
theorem regular_negative_superlevel_has_escaping_component
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [RiemannSurface X]
    [MeasurableEq X] [SecondCountableTopology X] [ComplexOneManifold X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    (φ : LogarithmicCutoffPoleModel g p)
    (source : (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ)
    (hdata :
      GreenSobolevH10SmoothCompactSupportLocalWeakCorrectionData
        φ source)
    (G : X → ℝ)
    (_hrep :
      ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X),
        (fun w : ℂ ↦ localEnergyGreenPotential φ hdata.correction
          (e.symm w))
          =ᵐ[MeasureTheory.volume.restrict
            (e.target ∩ e.symm ⁻¹' {x : X | x ≠ p})]
            (fun w : ℂ ↦ G (e.symm w)))
    (hharmonic : IsHarmonicOnSurface {x : X | x ≠ p} G)
    (hlog :
      ∀ χ : PointedSurfaceCoordinate X p,
        ∃ H : X → ℝ,
          IsHarmonicOnSurface χ.chart.source H ∧
            ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
              G x + Real.log ‖χ.chart x - χ.chart p‖ = H x)
    (hp_zero : G p = 0)
    {b a : ℝ} (hb_pos : 0 < b) (hba : b < a)
    (hnegative_high : ∃ x : X, a ≤ -G x) :
    ∃ x : X,
      a ≤ -G x ∧
        closure (connectedComponentIn {z : X | b < -G z} x) ⊆
          {z : X | z ≠ p} ∧
          ∀ K : Set X, IsCompact K →
            ∃ y ∈ connectedComponentIn {z : X | b < -G z} x, y ∉ K := by
  rcases hnegative_high with ⟨x, hx_high⟩
  have hclosureU :
      closure {z : X | b < -G z} ⊆ {z : X | z ≠ p} :=
    logarithmic_singularity_negative_strictSuperlevel_closure_subset_punctured
      (X := X) (p := p) G hlog hp_zero hb_pos
  have hcomponent_subset :
      connectedComponentIn {z : X | b < -G z} x ⊆
        {z : X | b < -G z} :=
    connectedComponentIn_subset {z : X | b < -G z} x
  have hclosure_component :
      closure (connectedComponentIn {z : X | b < -G z} x) ⊆
        {z : X | z ≠ p} :=
    (closure_mono hcomponent_subset).trans hclosureU
  have hescapes :
      ∀ K : Set X, IsCompact K →
        ∃ y ∈ connectedComponentIn {z : X | b < -G z} x, y ∉ K :=
    negative_strictSuperlevel_component_escapes_of_harmonic_minimum_principle
      (p := p) (G := G) hharmonic hb_pos hba hx_high hclosureU
  exact ⟨x, hx_high, hclosure_component, hescapes⟩

/--
%%handwave
name:
  A negative value produces an escaping negative level domain
statement:
  If the regular Green potential takes a value at most \(-a\) for some
  \(0<b<a\), then there is a connected open component of \(\{-G>b\}\) which
  escapes every compact set, has frontier on \(\{-G=b\}\), and contains a
  point where \(-G\ge a\).
proof:
  Consider the component of the negative sublevel through the chosen point.
  If it were compact, the harmonic minimum principle, together with
  logarithmic blow-up at the pole, would rule it out.  Hence the component is
  not contained in any compact set and so escapes to infinity.
-/
theorem regular_negative_superlevel_yields_escaping_level_domain
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [RiemannSurface X]
    [MeasurableEq X] [SecondCountableTopology X] [ComplexOneManifold X]
    [IsManifold SurfaceRealModel ∞ X]
    [SecondCountableTopology (SurfaceDifferentialTotalSpace X ℝ)]
    [TopologicalSpace.PseudoMetrizableSpace
      (SurfaceDifferentialTotalSpace X ℝ)]
    {g : BackgroundSurfaceMetricOnSurface X} {p : X}
    (φ : LogarithmicCutoffPoleModel g p)
    (source : (greenSobolevH10SmoothCompactSupportCore g).Core →L[ℝ] ℝ)
    (hdata :
      GreenSobolevH10SmoothCompactSupportLocalWeakCorrectionData
        φ source)
    (G : X → ℝ)
    (hrep :
      ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X),
        (fun w : ℂ ↦ localEnergyGreenPotential φ hdata.correction
          (e.symm w))
          =ᵐ[MeasureTheory.volume.restrict
            (e.target ∩ e.symm ⁻¹' {x : X | x ≠ p})]
            (fun w : ℂ ↦ G (e.symm w)))
    (hharmonic : IsHarmonicOnSurface {x : X | x ≠ p} G)
    (hlog :
      ∀ χ : PointedSurfaceCoordinate X p,
        ∃ H : X → ℝ,
          IsHarmonicOnSurface χ.chart.source H ∧
            ∀ᶠ x in 𝓝[χ.chart.source ∩ {x : X | x ≠ p}] p,
              G x + Real.log ‖χ.chart x - χ.chart p‖ = H x)
    (hp_zero : G p = 0)
    {b a : ℝ} (hb_pos : 0 < b) (hba : b < a)
    (hnegative_high : ∃ x : X, a ≤ -G x) :
    ∃ Ω : Set X,
      IsOpen Ω ∧
        IsPreconnected Ω ∧
          Ω ⊆ {x : X | b < -G x} ∧
            frontier Ω ⊆ {x : X | -G x = b} ∧
              (∃ x ∈ Ω, a ≤ -G x) ∧
                ∀ K : Set X, IsCompact K → ∃ x ∈ Ω, x ∉ K := by
  rcases
      regular_negative_superlevel_has_escaping_component
        φ source hdata G hrep hharmonic hlog hp_zero hb_pos hba
        hnegative_high with
    ⟨x, hx_high, hclosure_punctured, hescapes⟩
  have hneg_harmonic :
      IsHarmonicOnSurface {z : X | z ≠ p} (fun z : X ↦ -G z) :=
    harmonicOnSurface_neg hharmonic
  have hpb : (fun z : X ↦ -G z) p < b := by
    simp [hp_zero, hb_pos]
  have hU_open : IsOpen {z : X | b < -G z} :=
    harmonicOn_punctured_positive_strictSuperlevel_open
      (p := p) hneg_harmonic hpb
  have hpunctured_open : IsOpen {z : X | z ≠ p} := by
    simpa using (isOpen_ne (x := p) : IsOpen {z : X | z ≠ p})
  have hcont_punctured :
      ContinuousOn (fun z : X ↦ -G z) {z : X | z ≠ p} :=
    harmonicOnSurface_continuousOn hpunctured_open hneg_harmonic
  have hcont_closure :
      ContinuousOn (fun z : X ↦ -G z)
        (closure (connectedComponentIn {z : X | b < -G z} x)) :=
    hcont_punctured.mono hclosure_punctured
  exact
    continuousOn_escaping_strictSuperlevel_component_yields_level_domain
      (f := fun z : X ↦ -G z) hba hx_high hU_open hcont_closure
      hescapes







end Uniformization

end JJMath
