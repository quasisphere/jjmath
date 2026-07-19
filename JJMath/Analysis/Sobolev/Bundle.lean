import JJMath.Analysis.Sobolev.Basic
import JJMath.RiemannianGeometry.Volume
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

/-!
# Bundle-valued Sobolev data on surfaces

This file contains an intrinsic cotangent-field version of the basic surface
Sobolev definitions.  The existing representative-level definitions use
coordinate tangent coordinates directly; the definitions here keep the
cotangent field in the tangent bundle and only trivialize it when testing
local integrability or weak derivatives.
-/

namespace JJMath

open MeasureTheory
open scoped Manifold Topology ENNReal ContDiff Bundle MatrixOrder

namespace Uniformization

noncomputable section

/--
%%handwave
name:
  Differential fiber with values in a normed space
statement:
  The differential fiber with values in a real normed vector space consists
  of continuous real-linear maps from the tangent space to that vector space.
-/
abbrev ManifoldDifferentialFiber {H : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I : ModelWithCorners ℝ H H) (X E : Type) [TopologicalSpace X]
    [ChartedSpace H X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : X) : Type :=
  TangentSpace I x →L[ℝ] E

/--
%%handwave
name:
  Surface differential fiber with values in a normed space
statement:
  On a real surface, the differential fiber with values in a real normed
  vector space consists of continuous real-linear maps from the tangent plane
  to that vector space.
-/
abbrev SurfaceDifferentialFiber (X E : Type) [TopologicalSpace X]
    [ChartedSpace ℂ X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : X) : Type :=
  ManifoldDifferentialFiber SurfaceRealModel X E x

/--
%%handwave
name:
  Differential field with values in a normed space
statement:
  A vector-valued differential field assigns to each point a continuous
  real-linear map from the tangent space to the target vector space.
-/
abbrev ManifoldDifferentialField {H : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I : ModelWithCorners ℝ H H) (X E : Type) [TopologicalSpace X]
    [ChartedSpace H X] [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Type :=
  ∀ x : X, ManifoldDifferentialFiber I X E x

/--
%%handwave
name:
  Surface differential field with values in a normed space
statement:
  A vector-valued differential field on a real surface assigns to each point a
  continuous real-linear map from the tangent plane to the target vector
  space.
-/
abbrev SurfaceDifferentialField (X E : Type) [TopologicalSpace X]
    [ChartedSpace ℂ X] [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Type :=
  ManifoldDifferentialField SurfaceRealModel X E

/--
%%handwave
name:
  Differential bundle fiber
statement:
  A vector-valued differential bundle may be represented as the bundle of
  continuous real-linear maps from tangent spaces to the trivial target
  bundle.
-/
abbrev ManifoldDifferentialBundleFiber {H : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I : ModelWithCorners ℝ H H) (X E : Type) [TopologicalSpace X]
    [ChartedSpace H X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : X) : Type :=
  TangentSpace I x →L[ℝ] Bundle.Trivial X E x

/--
%%handwave
name:
  Surface differential bundle fiber
statement:
  A vector-valued differential bundle on a real surface may be represented as
  the bundle of continuous real-linear maps from tangent planes to the trivial
  target bundle.
-/
abbrev SurfaceDifferentialBundleFiber (X E : Type) [TopologicalSpace X]
    [ChartedSpace ℂ X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : X) : Type :=
  ManifoldDifferentialBundleFiber SurfaceRealModel X E x

/--
%%handwave
name:
  Differentiable differential section
statement:
  A differentiable vector-valued differential section is a differentiable
  section of the bundle of continuous real-linear maps from tangent spaces to
  the trivial target bundle.
-/
abbrev ContMDiffManifoldDifferentialSection {H : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I : ModelWithCorners ℝ H H) (n : WithTop ℕ∞)
    (X E : Type) [TopologicalSpace X] [ChartedSpace H X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [IsManifold I 1 X] [IsManifold I n X] : Type :=
  Cₛ^n⟮I; H →L[ℝ] E,
    ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E)⟯

/--
%%handwave
name:
  Differentiable surface differential section
statement:
  A differentiable vector-valued differential section on a real surface is a
  differentiable section of the bundle of continuous real-linear maps from
  tangent planes to the trivial target bundle.
-/
abbrev ContMDiffSurfaceDifferentialSection (n : WithTop ℕ∞)
    (X E : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [IsManifold SurfaceRealModel 1 X] [IsManifold SurfaceRealModel n X] : Type :=
  ContMDiffManifoldDifferentialSection SurfaceRealModel n X E

/--
%%handwave
name:
  \(C^1\) surface differential section
statement:
  A \(C^1\) vector-valued differential section is a once continuously
  differentiable section of the vector-valued differential bundle.
-/
abbrev C1SurfaceDifferentialSection (X E : Type) [TopologicalSpace X]
    [ChartedSpace ℂ X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [IsManifold SurfaceRealModel 1 X] : Type :=
  ContMDiffSurfaceDifferentialSection 1 X E

/--
%%handwave
name:
  Smooth surface differential section
statement:
  A smooth vector-valued differential section is a smooth section of the
  vector-valued differential bundle.
-/
abbrev SmoothSurfaceDifferentialSection (X E : Type) [TopologicalSpace X]
    [ChartedSpace ℂ X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [IsManifold SurfaceRealModel ∞ X] : Type :=
  ContMDiffSurfaceDifferentialSection ∞ X E

/--
%%handwave
name:
  Classical differential field of a vector-valued map on a manifold
statement:
  The classical differential field of a vector-valued map is obtained by
  taking the manifold derivative at each point and identifying the tangent
  space of the target vector space with the target itself.
-/
noncomputable def manifoldDifferentialFieldOfMFDeriv {H X E : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I : ModelWithCorners ℝ H H) [TopologicalSpace X] [ChartedSpace H X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (u : X → E) :
    ManifoldDifferentialField I X E :=
  fun x ↦
    (NormedSpace.fromTangentSpace (u x)).toContinuousLinearMap.comp
      (mfderiv I 𝓘(ℝ, E) u x)

/--
%%handwave
name:
  Classical differential field of a vector-valued surface map
statement:
  The classical differential field of a vector-valued surface map is obtained
  by taking the manifold derivative at each point and identifying the tangent
  space of the target vector space with the target itself.
-/
noncomputable def surfaceDifferentialFieldOfMFDeriv {X E : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (u : X → E) :
    SurfaceDifferentialField X E :=
  manifoldDifferentialFieldOfMFDeriv SurfaceRealModel u

/--
%%handwave
name:
  Surface cotangent fiber
statement:
  The cotangent fiber at a point of a Riemann surface consists of the
  continuous real-linear functionals on the tangent plane at that point.
-/
abbrev SurfaceCotangentFiber {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (x : X) : Type :=
  SurfaceDifferentialFiber X ℝ x

/--
%%handwave
name:
  Surface cotangent bundle fiber
statement:
  The cotangent bundle may be represented as the bundle of continuous
  real-linear maps from tangent planes to the trivial real line bundle.
-/
abbrev SurfaceCotangentBundleFiber {X : Type} [TopologicalSpace X]
    [ChartedSpace ℂ X] (x : X) : Type :=
  SurfaceDifferentialBundleFiber X ℝ x

/--
%%handwave
name:
  Surface cotangent field
statement:
  A surface cotangent field assigns to each point a continuous real-linear
  functional on the tangent plane at that point.
-/
abbrev SurfaceCotangentField (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] :
    Type :=
  SurfaceDifferentialField X ℝ

/--
%%handwave
name:
  Differentiable surface cotangent section
statement:
  A differentiable cotangent section is a differentiable section of the
  cotangent bundle.
-/
abbrev ContMDiffSurfaceCotangentSection (n : WithTop ℕ∞)
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel 1 X] [IsManifold SurfaceRealModel n X] : Type :=
  ContMDiffSurfaceDifferentialSection n X ℝ

/--
%%handwave
name:
  \(C^1\) surface cotangent section
statement:
  A \(C^1\) cotangent section is a once continuously differentiable section
  of the cotangent bundle.
-/
abbrev C1SurfaceCotangentSection (X : Type) [TopologicalSpace X]
    [ChartedSpace ℂ X] [IsManifold SurfaceRealModel 1 X] : Type :=
  ContMDiffSurfaceCotangentSection 1 X

/--
%%handwave
name:
  Smooth surface cotangent section
statement:
  A smooth cotangent section is a smooth section of the cotangent bundle.
-/
abbrev SmoothSurfaceCotangentSection (X : Type) [TopologicalSpace X]
    [ChartedSpace ℂ X] [IsManifold SurfaceRealModel ∞ X] : Type :=
  ContMDiffSurfaceCotangentSection ∞ X

/--
%%handwave
name:
  Exterior derivative of a surface function
statement:
  The exterior derivative of a real-valued surface function is the cotangent
  field obtained by taking its manifold derivative at each point.
-/
noncomputable def surfaceCotangentFieldOfExtDerivFun {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] (u : X → ℝ) :
    SurfaceCotangentField X :=
  mvfderiv (I := SurfaceRealModel) u

/--
%%handwave
name:
  Exterior derivative evaluated at a surface point
statement:
  For a real-valued function \(u\) on a surface, its exterior-derivative cotangent field satisfies \((du)_x=D u(x)\).
proof:
  This is the pointwise form of the definition of the exterior derivative as the manifold derivative.
-/
@[simp]
theorem surfaceCotangentFieldOfExtDerivFun_apply {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] (u : X → ℝ) (x : X) :
    surfaceCotangentFieldOfExtDerivFun u x =
      mvfderiv (I := SurfaceRealModel) u x :=
  rfl

namespace ManifoldDifferentialField

variable {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]

/--
%%handwave
name:
  Coordinate evaluation of a vector-valued differential field on a manifold
statement:
  The coordinate evaluation of a vector-valued differential field applies the
  field at the represented manifold point to the corresponding coordinate
  tangent vector.
-/
noncomputable def evalChart (du : ManifoldDifferentialField I X E)
    (e : OpenPartialHomeomorph X H) (z v : H) : E :=
  du (e.symm z) (manifoldChartTangentVector (I := I) e z v)

/--
%%handwave
name:
  Coordinate evaluation of a manifold differential field
statement:
  If \(e\) is a chart and \(z,v\) are model coordinates, then the coordinate evaluation of a differential field \(A\) is
  \[
    A_{e^{-1}(z)}\big(D(e^{-1})(z)v\big).
  \]
proof:
  This is the definition of coordinate evaluation through the chart tangent map.
-/
@[simp]
theorem evalChart_eq (du : ManifoldDifferentialField I X E)
    (e : OpenPartialHomeomorph X H) (z v : H) :
    evalChart du e z v =
      du (e.symm z) (manifoldChartTangentVector (I := I) e z v) :=
  rfl

end ManifoldDifferentialField

namespace SurfaceDifferentialField

variable {X E : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]

/--
%%handwave
name:
  Coordinate evaluation of a vector-valued differential field
statement:
  The coordinate evaluation of a vector-valued differential field applies the
  field at the represented surface point to the corresponding coordinate
  tangent vector.
-/
noncomputable def evalChart (du : SurfaceDifferentialField X E)
    (e : OpenPartialHomeomorph X ℂ) (z v : ℂ) : E :=
  ManifoldDifferentialField.evalChart (I := SurfaceRealModel) du e z v

/--
%%handwave
name:
  Coordinate pullback of a vector-valued differential field
statement:
  The coordinate pullback of a vector-valued differential field is obtained by
  composing with the tangent map of the inverse coordinate chart.
-/
noncomputable def chartPullback (du : SurfaceDifferentialField X E)
    (e : OpenPartialHomeomorph X ℂ) : ℂ → ℂ →L[ℝ] E :=
  fun z ↦ (du (e.symm z)).comp (surfaceChartTangentMap e z)

/--
%%handwave
name:
  Coordinate evaluation of a surface differential field
statement:
  For a surface chart \(e\), a differential field \(A\), and \(z,v\in\mathbb C\), its coordinate evaluation is
  \[
    A_{e^{-1}(z)}\big(D(e^{-1})(z)v\big).
  \]
proof:
  Specialize the manifold coordinate-evaluation definition to the real model \(\mathbb C\).
-/
@[simp]
theorem evalChart_eq (du : SurfaceDifferentialField X E)
    (e : OpenPartialHomeomorph X ℂ) (z v : ℂ) :
    evalChart du e z v = du (e.symm z) (surfaceChartTangentVector e z v) :=
  rfl

/--
%%handwave
name:
  Coordinate pullback evaluated on a tangent vector
statement:
  The pullback of a surface differential field \(A\) through a chart \(e\) satisfies
  \[
    (e^\ast A)_z(v)=A_{e^{-1}(z)}\big(D(e^{-1})(z)v\big).
  \]
proof:
  Both sides are the definition of the coordinate evaluation of \(A\).
-/
@[simp]
theorem chartPullback_apply (du : SurfaceDifferentialField X E)
    (e : OpenPartialHomeomorph X ℂ) (z v : ℂ) :
    chartPullback du e z v = evalChart du e z v :=
  rfl

/--
%%handwave
name:
  Coordinate representation of a vector-valued differential field
statement:
  A vector-valued differential field can be read in the preferred tangent
  coordinates at each point.
-/
noncomputable def toCoordinateField (du : SurfaceDifferentialField X E) :
    X → ℂ →L[ℝ] E :=
  fun x ↦ du x

/--
%%handwave
name:
  Vector-valued differential field from coordinates
statement:
  A coordinate vector-valued differential field determines an intrinsic
  vector-valued differential field through the preferred tangent coordinates at
  each point.
-/
noncomputable def ofCoordinateField (du : X → ℂ →L[ℝ] E) :
    SurfaceDifferentialField X E :=
  fun x ↦ du x

/--
%%handwave
name:
  Recovering a coordinate differential field
statement:
  Converting a coordinate field \(A_x:\mathbb C\to E\) into an intrinsic surface differential field and then reading it in the preferred tangent coordinates recovers \(A\).
proof:
  Both conversions use the same pointwise linear maps, so the equality is definitional.
-/
@[simp]
theorem toCoordinateField_ofCoordinateField (du : X → ℂ →L[ℝ] E) :
    toCoordinateField (ofCoordinateField du) = du :=
  rfl

/--
%%handwave
name:
  Recovering an intrinsic differential field
statement:
  Reading an intrinsic surface differential field in the preferred tangent coordinates and then rebuilding the intrinsic field recovers the original field.
proof:
  The two pointwise coordinate conversions are inverse by definition.
-/
@[simp]
theorem ofCoordinateField_toCoordinateField (du : SurfaceDifferentialField X E) :
    ofCoordinateField (toCoordinateField du) = du :=
  rfl

end SurfaceDifferentialField

namespace ContMDiffSurfaceDifferentialSection

variable {n : WithTop ℕ∞} {X E : Type} [TopologicalSpace X]
    [ChartedSpace ℂ X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [IsManifold SurfaceRealModel 1 X] [IsManifold SurfaceRealModel n X]

/--
%%handwave
name:
  Differential field underlying a differentiable section
statement:
  A differentiable vector-valued differential section determines its
  underlying vector-valued differential field by evaluation at each point.
-/
noncomputable def toField (du : ContMDiffSurfaceDifferentialSection n X E) :
    SurfaceDifferentialField X E :=
  fun x ↦ du x

/--
%%handwave
name:
  Underlying field of a differentiable differential section
statement:
  The differential field underlying a \(C^n\) section \(A\) has value \(A(x)\) at every point \(x\).
proof:
  The underlying field is defined by pointwise evaluation of the section.
-/
@[simp]
theorem toField_apply (du : ContMDiffSurfaceDifferentialSection n X E) (x : X) :
    toField du x = du x :=
  rfl

end ContMDiffSurfaceDifferentialSection

/--
%%handwave
name:
  Hilbert bundle geometry
statement:
  A Hilbert bundle geometry on a measured base consists of a dependent fiber
  bundle together with a fiberwise real inner product and the associated
  pointwise square norm used to define \(L^2\)-sections.
-/
structure HilbertBundleGeometry (X F : Type) [MeasurableSpace X] (V : X → Type) where
  /-- The fiberwise real inner product. -/
  fiberInner : ∀ x : X, V x → V x → ℝ
  /-- The fiberwise square norm used in the \(L^2\) condition. -/
  fiberNormSq : ∀ x : X, V x → ℝ
  /-- The square norm is the diagonal value of the inner product. -/
  fiberNormSq_eq_inner : ∀ (x : X) (v : V x),
    fiberNormSq x v = fiberInner x v v

/--
%%handwave
name:
  Hilbert bundle geometry on a surface
statement:
  A Hilbert bundle geometry on a measured surface consists of a dependent
  fiber bundle together with a fiberwise real inner product and the associated
  pointwise square norm used to define \(L^2\)-sections.
-/
abbrev HilbertBundleGeometryOnSurface (X F : Type) [TopologicalSpace X]
    [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X] [IsManifold SurfaceRealModel 1 X]
    (V : X → Type) : Type :=
  HilbertBundleGeometry X F V

/--
%%handwave
name:
  Section of a Hilbert bundle
statement:
  A section of a dependent bundle assigns to each base point a vector in the
  fiber over that point.
-/
abbrev HilbertBundleSection (X : Type) (V : X → Type) : Type :=
  ∀ x : X, V x

/--
%%handwave
name:
  Section of a surface Hilbert bundle
statement:
  A section of a dependent bundle over a surface assigns to each base point a
  vector in the fiber over that point.
-/
abbrev HilbertBundleSectionOnSurface (X : Type) (V : X → Type) : Type :=
  HilbertBundleSection X V

namespace HilbertBundleSectionOnSurface

noncomputable instance bundleTotalSpaceMeasurableSpace {X F : Type} {V : X → Type}
    [TopologicalSpace (Bundle.TotalSpace F V)] :
    MeasurableSpace (Bundle.TotalSpace F V) :=
  borel (Bundle.TotalSpace F V)

instance bundleTotalSpaceBorelSpace {X F : Type} {V : X → Type}
    [TopologicalSpace (Bundle.TotalSpace F V)] :
    BorelSpace (Bundle.TotalSpace F V) :=
  ⟨rfl⟩

/--
%%handwave
name:
  Bundle section as a total-space map
statement:
  A section of a dependent bundle can be regarded as a map from the base into
  the bundle total space.
-/
noncomputable def toTotalSpace {X F : Type} {V : X → Type}
    (s : HilbertBundleSectionOnSurface X V) :
    X → Bundle.TotalSpace F V :=
  fun x ↦ Bundle.TotalSpace.mk' F x (s x)

/--
%%handwave
name:
  Base point of a bundle section in the total space
statement:
  If a bundle section \(s\) is regarded as a total-space-valued map, the base point of \(s(x)\) is \(x\).
proof:
  A section value is inserted into the total space as the pair \((x,s(x))\).
-/
@[simp]
theorem toTotalSpace_apply {X F : Type} {V : X → Type}
    (s : HilbertBundleSectionOnSurface X V) (x : X) :
    (toTotalSpace (F := F) s x).1 = x :=
  rfl

end HilbertBundleSectionOnSurface

/--
%%handwave
name:
  Square-integrable section of a Hilbert bundle
statement:
  A section of a surface Hilbert bundle is square-integrable when the
  corresponding total-space map is almost everywhere Borel measurable and the
  fiberwise square norm is integrable.
-/
def HilbertBundleSectionMemL2 {X F : Type} [TopologicalSpace X]
    [MeasurableSpace X]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    (G : HilbertBundleGeometry X F V) (μ : Measure X)
    (s : HilbertBundleSectionOnSurface X V) : Prop :=
  AEMeasurable
      (HilbertBundleSectionOnSurface.toTotalSpace (F := F) s) μ ∧
    Integrable (fun x ↦ G.fiberNormSq x (s x)) μ

namespace HilbertBundleSectionMemL2

variable {X F : Type} [TopologicalSpace X] [MeasurableSpace X]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    {G : HilbertBundleGeometry X F V} {μ : Measure X}
    {s t : HilbertBundleSectionOnSurface X V}

/--
%%handwave
name:
  Measurability of a square-integrable bundle section
statement:
  A square-integrable Hilbert-bundle section is almost everywhere measurable as a map into the bundle total space.
proof:
  This is the measurability component of the definition of square-integrability.
-/
theorem aemeasurable (h : HilbertBundleSectionMemL2 G μ s) :
    AEMeasurable
      (HilbertBundleSectionOnSurface.toTotalSpace (F := F) s) μ :=
  h.1

/--
%%handwave
name:
  Integrability of the fiberwise square norm
statement:
  If \(s\) is a square-integrable Hilbert-bundle section, then \(x\mapsto\|s(x)\|_x^2\) is integrable.
proof:
  This is the integrability component of the definition of square-integrability.
-/
theorem integrable_normSq (h : HilbertBundleSectionMemL2 G μ s) :
    Integrable (fun x ↦ G.fiberNormSq x (s x)) μ :=
  h.2

/--
%%handwave
name:
  Square-integrability is invariant under almost-everywhere equality
statement:
  If \(s\) is a square-integrable Hilbert-bundle section and \(s(x)=t(x)\) for almost every \(x\), then \(t\) is square-integrable.
proof:
  Almost-everywhere equality preserves both measurability of the total-space map and integrability of the fiberwise square norm.
-/
theorem congr_ae (hs : HilbertBundleSectionMemL2 G μ s)
    (hst : ∀ᵐ x ∂μ, s x = t x) :
    HilbertBundleSectionMemL2 G μ t := by
  refine ⟨?_, ?_⟩
  · refine hs.aemeasurable.congr ?_
    filter_upwards [hst] with x hx
    exact Bundle.TotalSpace.mk_inj.2 hx
  · refine hs.integrable_normSq.congr ?_
    filter_upwards [hst] with x hx
    rw [hx]

/--
%%handwave
name:
  Almost-everywhere invariance of square-integrability
statement:
  If bundle sections \(s\) and \(t\) agree almost everywhere, then \(s\) is square-integrable if and only if \(t\) is square-integrable.
proof:
  Transfer square-integrability in each direction using the given equality and its symmetry.
-/
theorem congr_ae_iff (hst : ∀ᵐ x ∂μ, s x = t x) :
    HilbertBundleSectionMemL2 G μ s ↔ HilbertBundleSectionMemL2 G μ t :=
  ⟨fun hs ↦ hs.congr_ae hst, fun ht ↦ ht.congr_ae (hst.mono fun _ hx ↦ hx.symm)⟩

end HilbertBundleSectionMemL2

/--
%%handwave
name:
  Square-integrable Hilbert-bundle section representative
statement:
  A square-integrable Hilbert-bundle section representative is a section with
  finite \(L^2\) energy for the chosen fiberwise Hilbert norm.
-/
structure SquareIntegrableHilbertBundleSection {X F : Type}
    [TopologicalSpace X] [MeasurableSpace X]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    (G : HilbertBundleGeometry X F V) (μ : Measure X) where
  /-- The underlying section. -/
  toSection : HilbertBundleSectionOnSurface X V
  /-- The section is square-integrable. -/
  memL2 : HilbertBundleSectionMemL2 G μ toSection

namespace SquareIntegrableHilbertBundleSection

variable {X F : Type} [TopologicalSpace X] [MeasurableSpace X]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    {G : HilbertBundleGeometry X F V} {μ : Measure X}

instance : CoeFun (SquareIntegrableHilbertBundleSection G μ)
    (fun _ ↦ HilbertBundleSectionOnSurface X V) where
  coe s := s.toSection

/--
%%handwave
name:
  Equality of square-integrable representatives
statement:
  Two square-integrable bundle-section representatives are equal if their
  underlying sections are pointwise equal.
proof:
  Destructure the two representatives.  Pointwise equality gives equality of the underlying sections by function extensionality, after which the stored square-integrability proofs are propositionally irrelevant.
-/
theorem ext {s t : SquareIntegrableHilbertBundleSection G μ}
    (h : ∀ x : X, s.toSection x = t.toSection x) : s = t := by
  cases s with
  | mk s hs =>
    cases t with
    | mk t ht =>
      have hst : s = t := funext h
      subst hst
      rfl

/--
%%handwave
name:
  Almost-everywhere equality of Hilbert-bundle sections
statement:
  Two square-integrable bundle-section representatives define the same
  \(L^2\)-section when they agree almost everywhere in their fibers.
-/
def AeEq (s t : SquareIntegrableHilbertBundleSection G μ) : Prop :=
  ∀ᵐ x ∂μ, s.toSection x = t.toSection x

/--
%%handwave
name:
  Reflexivity of almost-everywhere equality for bundle sections
statement:
  Every square-integrable bundle-section representative agrees almost everywhere with itself.
proof:
  Pointwise equality is reflexive at every base point.
-/
theorem AeEq.refl (s : SquareIntegrableHilbertBundleSection G μ) :
    AeEq s s :=
  Filter.Eventually.of_forall fun _ ↦ rfl

/--
%%handwave
name:
  Symmetry of almost-everywhere equality for bundle sections
statement:
  If square-integrable bundle-section representatives \(s\) and \(t\) agree almost everywhere, then \(t\) and \(s\) agree almost everywhere.
proof:
  Reverse the pointwise equality on the full-measure set where it holds.
-/
theorem AeEq.symm {s t : SquareIntegrableHilbertBundleSection G μ}
    (h : AeEq s t) : AeEq t s :=
  h.mono fun _ hx ↦ hx.symm

/--
%%handwave
name:
  Transitivity of almost-everywhere equality for bundle sections
statement:
  If \(s=t\) almost everywhere and \(t=r\) almost everywhere, then \(s=r\) almost everywhere.
proof:
  Intersect the two full-measure sets and use transitivity of pointwise equality.
-/
theorem AeEq.trans {s t r : SquareIntegrableHilbertBundleSection G μ}
    (h₁ : AeEq s t) (h₂ : AeEq t r) : AeEq s r := by
  filter_upwards [h₁, h₂] with x hx₁ hx₂
  exact hx₁.trans hx₂

instance aeSetoid : Setoid (SquareIntegrableHilbertBundleSection G μ) where
  r := AeEq
  iseqv := ⟨fun s ↦ AeEq.refl s, fun {_ _} h ↦ AeEq.symm h,
    fun {_ _ _} h₁ h₂ ↦ AeEq.trans h₁ h₂⟩

end SquareIntegrableHilbertBundleSection

/--
%%handwave
name:
  \(L^2\)-sections of a Hilbert bundle
statement:
  The space \(L^2\) of a surface Hilbert bundle consists of square-integrable
  section representatives modulo almost-everywhere equality.
-/
abbrev L2HilbertBundle {X F : Type} [TopologicalSpace X] [MeasurableSpace X]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    (G : HilbertBundleGeometry X F V) (μ : Measure X) : Type :=
  Quotient (SquareIntegrableHilbertBundleSection.aeSetoid (G := G) (μ := μ))

namespace L2HilbertBundle

variable {X F : Type} [TopologicalSpace X] [MeasurableSpace X]
    {V : X → Type} [TopologicalSpace (Bundle.TotalSpace F V)]
    {G : HilbertBundleGeometry X F V} {μ : Measure X}

/-- The \(L^2\)-class of a square-integrable representative. -/
abbrev mk (s : SquareIntegrableHilbertBundleSection G μ) : L2HilbertBundle G μ :=
  Quotient.mk (SquareIntegrableHilbertBundleSection.aeSetoid (G := G) (μ := μ)) s

/--
%%handwave
name:
  Equality of \(L^2\) bundle classes
statement:
  Two square-integrable bundle-section representatives determine the same \(L^2\) class if and only if they agree almost everywhere.
proof:
  This is the equality criterion for the quotient by almost-everywhere equality.
-/
@[simp]
theorem mk_eq_mk {s t : SquareIntegrableHilbertBundleSection G μ} :
    mk s = mk t ↔ SquareIntegrableHilbertBundleSection.AeEq s t :=
  Quotient.eq

/--
%%handwave
name:
  Almost-everywhere equal bundle sections have the same \(L^2\) class
statement:
  If two square-integrable bundle sections agree almost everywhere, their classes in the bundle \(L^2\) space are equal.
proof:
  Apply the quotient relation defining the \(L^2\) space.
-/
theorem sound {s t : SquareIntegrableHilbertBundleSection G μ}
    (h : SquareIntegrableHilbertBundleSection.AeEq s t) :
    mk s = mk t :=
  Quotient.sound h

/--
%%handwave
name:
  Representative induction for bundle \(L^2\) sections
statement:
  To prove a property of every \(L^2\) bundle section, it suffices to prove it for the class of each square-integrable representative.
proof:
  Use induction on the quotient by almost-everywhere equality.
-/
@[elab_as_elim]
protected theorem induction_on {C : L2HilbertBundle G μ → Prop}
    (u : L2HilbertBundle G μ)
    (h : ∀ s : SquareIntegrableHilbertBundleSection G μ, C (mk s)) : C u :=
  Quotient.inductionOn u h

end L2HilbertBundle

/--
%%handwave
name:
  Trivial Hilbert bundle geometry
statement:
  A fixed real Hilbert space determines the trivial Hilbert bundle over a
  measured base, with the same inner product on every fiber.
-/
noncomputable def trivialHilbertBundleGeometry (X E : Type)
    [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    HilbertBundleGeometry X E (Bundle.Trivial X E) where
  fiberInner := fun _ v w ↦ inner ℝ v w
  fiberNormSq := fun _ v ↦ inner ℝ v v
  fiberNormSq_eq_inner := by
    intro _ _
    rfl

/--
%%handwave
name:
  Trivial Hilbert bundle geometry on a surface
statement:
  A fixed real Hilbert space determines the trivial Hilbert bundle over a
  measured surface, with the same inner product on every fiber.
-/
noncomputable def trivialHilbertBundleGeometryOnSurface (X E : Type)
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [IsManifold SurfaceRealModel 1 X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    HilbertBundleGeometryOnSurface X E (Bundle.Trivial X E) :=
  trivialHilbertBundleGeometry X E

/--
%%handwave
name:
  \(L^2\)-sections of a trivial Hilbert bundle over a measured base
statement:
  The \(L^2\)-sections of the trivial bundle with fiber a Hilbert space are
  Hilbert-valued square-integrable functions, represented as bundle sections.
-/
abbrev ValueL2Section {X E : Type}
    [TopologicalSpace X] [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (μ : Measure X) : Type :=
  L2HilbertBundle (trivialHilbertBundleGeometry X E) μ

/--
%%handwave
name:
  \(L^2\)-sections of a trivial Hilbert bundle over a surface
statement:
  The \(L^2\)-sections of the trivial bundle with fiber a Hilbert space are
  Hilbert-valued square-integrable functions, represented as bundle sections.
-/
abbrev SurfaceValueL2Section {X E : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [IsManifold SurfaceRealModel 1 X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (μ : Measure X) : Type :=
  ValueL2Section (X := X) (E := E) μ

/--
%%handwave
name:
  Square-integrable section of the trivial Hilbert bundle over a measured base
statement:
  A representative of an \(L^2\) Hilbert-valued map is a square-integrable
  section of the trivial Hilbert bundle.
-/
abbrev SquareIntegrableValueSection {X E : Type}
    [TopologicalSpace X] [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (μ : Measure X) : Type :=
  SquareIntegrableHilbertBundleSection (trivialHilbertBundleGeometry X E) μ

namespace SquareIntegrableValueSection

variable {X E : Type} [TopologicalSpace X] [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {μ : Measure X}

/--
%%handwave
name:
  Trivial-bundle representative as a function
statement:
  A section representative of the trivial Hilbert bundle determines the
  corresponding Hilbert-valued function.
-/
abbrev toFunction
    (u : SquareIntegrableValueSection (X := X) (E := E) μ) : X → E :=
  u.toSection

/--
%%handwave
name:
  Almost-everywhere equality for trivial-bundle representatives
statement:
  Almost-everywhere equality of representatives of trivial-bundle
  \(L^2\)-sections is equality of the corresponding Hilbert-valued functions
  almost everywhere.
-/
abbrev aeSetoid :
    Setoid (SquareIntegrableValueSection (X := X) (E := E) μ) :=
  SquareIntegrableHilbertBundleSection.aeSetoid
    (G := trivialHilbertBundleGeometry X E) (μ := μ)

end SquareIntegrableValueSection

/--
%%handwave
name:
  Square-integrable section of the trivial Hilbert bundle over a surface
statement:
  A representative of an \(L^2\) Hilbert-valued map is a square-integrable
  section of the trivial Hilbert bundle.
-/
abbrev SquareIntegrableSurfaceValueSection {X E : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [IsManifold SurfaceRealModel 1 X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (μ : Measure X) : Type :=
  SquareIntegrableValueSection (X := X) (E := E) μ

namespace SquareIntegrableSurfaceValueSection

variable {X E : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold SurfaceRealModel 1 X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {μ : Measure X}

/--
%%handwave
name:
  Trivial-bundle representative as a function
statement:
  A section representative of the trivial Hilbert bundle determines the
  corresponding Hilbert-valued function.
-/
abbrev toFunction
    (u : SquareIntegrableSurfaceValueSection (X := X) (E := E) μ) : X → E :=
  SquareIntegrableValueSection.toFunction u

/--
%%handwave
name:
  Almost-everywhere equality for trivial-bundle representatives
statement:
  Almost-everywhere equality of representatives of trivial-bundle
  \(L^2\)-sections is equality of the corresponding Hilbert-valued functions
  almost everywhere.
-/
abbrev aeSetoid :
    Setoid (SquareIntegrableSurfaceValueSection (X := X) (E := E) μ) :=
  SquareIntegrableValueSection.aeSetoid (X := X) (E := E) (μ := μ)

end SquareIntegrableSurfaceValueSection

/--
%%handwave
name:
  Total space of the vector-valued differential bundle on a manifold
statement:
  The total space of the vector-valued differential bundle is the vector
  bundle whose fiber over \(x\) consists of continuous real-linear maps
  \(T_xX\to E\).
-/
abbrev ManifoldDifferentialTotalSpace {H : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I : ModelWithCorners ℝ H H) (X E : Type) [TopologicalSpace X]
    [ChartedSpace H X] [NormedAddCommGroup E] [NormedSpace ℝ E] : Type :=
  Bundle.TotalSpace (H →L[ℝ] E)
    (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E))

/--
%%handwave
name:
  Total space of the vector-valued differential bundle on a surface
statement:
  The total space of the vector-valued differential bundle is the vector
  bundle whose fiber over \(x\) consists of continuous real-linear maps
  \(T_xX\to E\).
-/
abbrev SurfaceDifferentialTotalSpace (X E : Type) [TopologicalSpace X]
    [ChartedSpace ℂ X] [NormedAddCommGroup E] [NormedSpace ℝ E] : Type :=
  ManifoldDifferentialTotalSpace SurfaceRealModel X E

namespace SurfaceDifferentialField

variable {X E : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]

/--
%%handwave
name:
  Differential field as a bundle section
statement:
  A vector-valued differential field determines a section of the differential
  bundle by pairing each base point with the linear map assigned to it.
-/
noncomputable def toTotalSpaceSection (du : SurfaceDifferentialField X E) :
    X → SurfaceDifferentialTotalSpace X E :=
  fun x ↦ Bundle.TotalSpace.mk' (ℂ →L[ℝ] E) x (du x)

/--
%%handwave
name:
  Base point of a differential field as a bundle section
statement:
  When a surface differential field \(A\) is viewed as a section of the differential-bundle total space, the base point of its value at \(x\) is \(x\).
proof:
  The total-space section is the pair \((x,A_x)\) by definition.
-/
@[simp]
theorem toTotalSpaceSection_apply (du : SurfaceDifferentialField X E) (x : X) :
    (toTotalSpaceSection du x).1 = x :=
  rfl

end SurfaceDifferentialField

/--
%%handwave
name:
  Model tangent basis vector
statement:
  The real model plane of a surface has the standard two-element basis
  \(1,i\), viewed in each tangent model fiber.
-/
noncomputable def surfaceTangentModelBasisVector {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] (x : X) (i : Fin 2) :
    TangentSpace SurfaceRealModel x :=
  if i = 0 then (1 : ℂ) else Complex.I

/--
%%handwave
name:
  Metric Gram determinant in the model tangent basis
statement:
  At a point of a Riemannian surface, the Gram determinant of the metric in
  the model tangent basis is the determinant of the \(2\times 2\) matrix of
  pairings of \(1\) and \(i\).
-/
noncomputable def surfaceMetricModelGramDetAt {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : SmoothRiemannianMetricOnSurface X) (x : X) : ℝ :=
  letI : IsManifold SurfaceRealModel ∞ X := g.isManifold_real
  let b := g.toContMDiffRiemannianMetric.inner x
  let e₁ : TangentSpace SurfaceRealModel x := surfaceTangentModelBasisVector x 0
  let e₂ : TangentSpace SurfaceRealModel x := surfaceTangentModelBasisVector x 1
  b e₁ e₁ * b e₂ e₂ - b e₁ e₂ * b e₂ e₁

/--
%%handwave
name:
  Inverse metric coefficients in the model tangent basis
statement:
  The inverse metric coefficients are the entries of the inverse of the
  \(2\times2\) Gram matrix of the Riemannian metric in the model tangent
  basis.
-/
noncomputable def surfaceMetricInverseGramCoeffAt {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : SmoothRiemannianMetricOnSurface X) (x : X) (i j : Fin 2) : ℝ :=
  letI : IsManifold SurfaceRealModel ∞ X := g.isManifold_real
  let b := g.toContMDiffRiemannianMetric.inner x
  let e₁ : TangentSpace SurfaceRealModel x := surfaceTangentModelBasisVector x 0
  let e₂ : TangentSpace SurfaceRealModel x := surfaceTangentModelBasisVector x 1
  let a : ℝ := b e₁ e₁
  let c : ℝ := b e₁ e₂
  let d : ℝ := b e₂ e₁
  let e : ℝ := b e₂ e₂
  let det : ℝ := surfaceMetricModelGramDetAt g x
  match i, j with
  | 0, 0 => det⁻¹ * e
  | 0, 1 => -det⁻¹ * c
  | 1, 0 => -det⁻¹ * d
  | 1, 1 => det⁻¹ * a

/--
%%handwave
name:
  Metric Gram determinant is positive in the model tangent basis
statement:
  The Gram determinant of a Riemannian metric in the two model tangent
  directions \(1,i\) is strictly positive.
proof:
  Complete the square in the positive definite quadratic form.  The first
  basis vector has positive square length, and the Schur complement is the
  square length of a nonzero vector, so the determinant is positive.
-/
theorem surfaceMetricModelGramDetAt_pos {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : SmoothRiemannianMetricOnSurface X) (x : X) :
    0 < surfaceMetricModelGramDetAt g x := by
  letI : IsManifold SurfaceRealModel ∞ X := g.isManifold_real
  let b : ℂ →L[ℝ] ℂ →L[ℝ] ℝ := g.toContMDiffRiemannianMetric.inner x
  let a : ℝ := b (1 : ℂ) (1 : ℂ)
  let c : ℝ := b (1 : ℂ) Complex.I
  let d : ℝ := b Complex.I Complex.I
  have ha : 0 < a :=
    g.toContMDiffRiemannianMetric.pos x
      (show TangentSpace SurfaceRealModel x from (1 : ℂ)) (by
        change (1 : ℂ) ≠ 0
        norm_num)
  let r : ℝ := c / a
  let v : ℂ := Complex.I - (r : ℝ) • (1 : ℂ)
  have hv_ne : v ≠ 0 := by
    intro hv
    have him := congr_arg Complex.im hv
    simp [v, r] at him
  have hv_pos : 0 < b v v := g.toContMDiffRiemannianMetric.pos x
    (show TangentSpace SurfaceRealModel x from v) hv_ne
  have hv_expand : b v v = d - r * c - r * c + r * r * a := by
    change b (Complex.I - (r : ℝ) • (1 : ℂ))
        (Complex.I - (r : ℝ) • (1 : ℂ)) =
      d - r * c - r * c + r * r * a
    have hsymm_b : b Complex.I (1 : ℂ) = b (1 : ℂ) Complex.I := by
      exact g.toContMDiffRiemannianMetric.symm x
        (show TangentSpace SurfaceRealModel x from Complex.I)
        (show TangentSpace SurfaceRealModel x from (1 : ℂ))
    rw [map_sub]
    simp only [ContinuousLinearMap.sub_apply, map_sub, map_smul, smul_eq_mul]
    rw [hsymm_b]
    simp [a, c, d]
    ring
  have hv_eval : b v v = d - c * c / a := by
    rw [hv_expand]
    simp [r]
    field_simp [ha.ne']
    ring
  rw [hv_eval] at hv_pos
  have hmul : 0 < a * (d - c * c / a) := mul_pos ha hv_pos
  have hdet : a * (d - c * c / a) = a * d - c * c := by
    field_simp [ha.ne']
  rw [hdet] at hmul
  have hsymm :
      (g.toContMDiffRiemannianMetric.inner x
        (show TangentSpace SurfaceRealModel x from Complex.I)
        (show TangentSpace SurfaceRealModel x from (1 : ℂ))) =
        (g.toContMDiffRiemannianMetric.inner x
          (show TangentSpace SurfaceRealModel x from (1 : ℂ))
          (show TangentSpace SurfaceRealModel x from Complex.I)) := by
    exact g.toContMDiffRiemannianMetric.symm x
      (show TangentSpace SurfaceRealModel x from Complex.I)
      (show TangentSpace SurfaceRealModel x from (1 : ℂ))
  simpa [surfaceMetricModelGramDetAt, surfaceTangentModelBasisVector, a, c, d,
    hsymm] using hmul

/--
%%handwave
name:
  Hilbert-Schmidt pairing of vector-valued differentials
statement:
  A Riemannian metric on the surface and an inner product on the target induce
  a Hilbert-Schmidt pairing on the fiber of \(T^\ast X\otimes E\).
-/
noncomputable def surfaceDifferentialHilbertSchmidtInnerAt {X E : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : SmoothRiemannianMetricOnSurface X) (x : X)
    (A B : SurfaceDifferentialFiber X E x) : ℝ :=
  letI : IsManifold SurfaceRealModel ∞ X := g.isManifold_real
  ∑ i : Fin 2, ∑ j : Fin 2,
    surfaceMetricInverseGramCoeffAt g x i j *
      inner ℝ (A (surfaceTangentModelBasisVector x i))
        (B (surfaceTangentModelBasisVector x j))

/--
%%handwave
name:
  Hilbert-Schmidt norm square of a vector-valued differential
statement:
  The pointwise square norm of a vector-valued differential is its
  Hilbert-Schmidt pairing with itself.
-/
noncomputable def surfaceDifferentialHilbertSchmidtNormSqAt {X E : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : SmoothRiemannianMetricOnSurface X) (x : X)
    (A : SurfaceDifferentialFiber X E x) : ℝ :=
  surfaceDifferentialHilbertSchmidtInnerAt g x A A

/--
%%handwave
name:
  Hilbert-Schmidt pairing as a continuous bilinear form
statement:
  The metric Hilbert-Schmidt pairing on the fiber of \(T^\ast X\otimes E\)
  is represented by a continuous real bilinear form.
proof:
  This follows from the finite-dimensionality of the tangent plane and the
  boundedness of the Hilbert inner product on the target.
-/
noncomputable def surfaceDifferentialHilbertSchmidtInnerCLMAt {X E : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : SmoothRiemannianMetricOnSurface X) (x : X) :
    SurfaceDifferentialBundleFiber (X := X) (E := E) x →L[ℝ]
      SurfaceDifferentialBundleFiber (X := X) (E := E) x →L[ℝ] ℝ := by
  let V := SurfaceDifferentialBundleFiber (X := X) (E := E) x
  let hVAdd : AddCommGroup V :=
    ContinuousLinearMap.addCommGroup
      (R := ℝ) (R₂ := ℝ)
      (M := TangentSpace SurfaceRealModel x) (M₂ := E)
      (σ₁₂ := RingHom.id ℝ)
  letI : AddCommGroup V := hVAdd
  letI : AddGroup V := AddCommGroup.toAddGroup
  letI : AddCommMonoid V := AddCommGroup.toAddCommMonoid
  let hVTop : IsTopologicalAddGroup V :=
    ContinuousLinearMap.topologicalAddGroup
      (𝕜₁ := ℝ) (𝕜₂ := ℝ)
      (σ := RingHom.id ℝ)
      (E := TangentSpace SurfaceRealModel x) (F := E)
  letI : IsTopologicalAddGroup V := hVTop
  let hDualAdd : AddCommGroup (V →L[ℝ] ℝ) :=
    ContinuousLinearMap.addCommGroup
      (R := ℝ) (R₂ := ℝ) (M := V) (M₂ := ℝ)
      (σ₁₂ := RingHom.id ℝ)
  letI : AddCommGroup (V →L[ℝ] ℝ) := hDualAdd
  letI : AddGroup (V →L[ℝ] ℝ) := AddCommGroup.toAddGroup
  letI : AddCommMonoid (V →L[ℝ] ℝ) := AddCommGroup.toAddCommMonoid
  letI : AddMonoid (V →L[ℝ] ℝ) := AddCommMonoid.toAddMonoid
  let hDualTop : IsTopologicalAddGroup (V →L[ℝ] ℝ) :=
    ContinuousLinearMap.topologicalAddGroup
      (𝕜₁ := ℝ) (𝕜₂ := ℝ) (σ := RingHom.id ℝ)
      (E := V) (F := ℝ)
  letI : IsTopologicalAddGroup (V →L[ℝ] ℝ) := hDualTop
  letI : ContinuousAdd (V →L[ℝ] ℝ) :=
    hDualTop.toContinuousAdd
  let hOuterAdd : AddCommGroup (V →L[ℝ] V →L[ℝ] ℝ) :=
    ContinuousLinearMap.addCommGroup
      (R := ℝ) (R₂ := ℝ) (M := V) (M₂ := V →L[ℝ] ℝ)
      (σ₁₂ := RingHom.id ℝ)
  letI : AddCommGroup (V →L[ℝ] V →L[ℝ] ℝ) := hOuterAdd
  letI : AddCommMonoid (V →L[ℝ] V →L[ℝ] ℝ) :=
    AddCommGroup.toAddCommMonoid
  letI : AddMonoid (V →L[ℝ] V →L[ℝ] ℝ) :=
    AddCommMonoid.toAddMonoid
  let innerReal : E →L[ℝ] E →L[ℝ] ℝ :=
    LinearMap.mkContinuous₂ (innerₗ E) 1 fun u v ↦ by
      simpa [innerₗ_apply_apply] using (norm_inner_le_norm (𝕜 := ℝ) u v)
  let eval (i : Fin 2) :
      V →L[ℝ] E :=
    { toLinearMap :=
        (ContinuousLinearMap.coeLM ℝ
          (M := TangentSpace SurfaceRealModel x) (N₃ := E)).flip
            (surfaceTangentModelBasisVector x i)
      cont := continuous_eval_const (surfaceTangentModelBasisVector x i) }
  exact
    ∑ i : Fin 2, ∑ j : Fin 2,
      surfaceMetricInverseGramCoeffAt g x i j •
        ((ContinuousLinearMap.precomp (G := ℝ) (eval j)).comp
          (innerReal.comp (eval i)))

/--
%%handwave
name:
  Continuous Hilbert-Schmidt pairing evaluates to the metric formula
statement:
  The continuous bilinear form representing the Hilbert-Schmidt pairing agrees
  with the coordinate formula obtained by contracting with the inverse
  Riemannian metric.
proof:
  Unfold the continuous bilinear form induced by the surface Hilbert--Schmidt metric; its evaluation is definitionally the stated fiber inner product.
-/
theorem surfaceDifferentialHilbertSchmidtInnerCLMAt_apply {X E : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : SmoothRiemannianMetricOnSurface X) (x : X)
    (A B : SurfaceDifferentialBundleFiber (X := X) (E := E) x) :
    surfaceDifferentialHilbertSchmidtInnerCLMAt g x A B =
      surfaceDifferentialHilbertSchmidtInnerAt g x A B := by
  let V := SurfaceDifferentialBundleFiber (X := X) (E := E) x
  let hVAdd : AddCommGroup V :=
    ContinuousLinearMap.addCommGroup
      (R := ℝ) (R₂ := ℝ)
      (M := TangentSpace SurfaceRealModel x) (M₂ := E)
      (σ₁₂ := RingHom.id ℝ)
  letI : AddCommGroup V := hVAdd
  letI : AddGroup V := AddCommGroup.toAddGroup
  letI : AddCommMonoid V := AddCommGroup.toAddCommMonoid
  let hVTop : IsTopologicalAddGroup V :=
    ContinuousLinearMap.topologicalAddGroup
      (𝕜₁ := ℝ) (𝕜₂ := ℝ)
      (σ := RingHom.id ℝ)
      (E := TangentSpace SurfaceRealModel x) (F := E)
  letI : IsTopologicalAddGroup V := hVTop
  let hDualAdd : AddCommGroup (V →L[ℝ] ℝ) :=
    ContinuousLinearMap.addCommGroup
      (R := ℝ) (R₂ := ℝ) (M := V) (M₂ := ℝ)
      (σ₁₂ := RingHom.id ℝ)
  letI : AddCommGroup (V →L[ℝ] ℝ) := hDualAdd
  letI : AddGroup (V →L[ℝ] ℝ) := AddCommGroup.toAddGroup
  letI : AddCommMonoid (V →L[ℝ] ℝ) := AddCommGroup.toAddCommMonoid
  letI : AddMonoid (V →L[ℝ] ℝ) := AddCommMonoid.toAddMonoid
  let hDualTop : IsTopologicalAddGroup (V →L[ℝ] ℝ) :=
    ContinuousLinearMap.topologicalAddGroup
      (𝕜₁ := ℝ) (𝕜₂ := ℝ) (σ := RingHom.id ℝ)
      (E := V) (F := ℝ)
  letI : IsTopologicalAddGroup (V →L[ℝ] ℝ) := hDualTop
  letI : ContinuousAdd (V →L[ℝ] ℝ) :=
    hDualTop.toContinuousAdd
  let hOuterAdd : AddCommGroup (V →L[ℝ] V →L[ℝ] ℝ) :=
    ContinuousLinearMap.addCommGroup
      (R := ℝ) (R₂ := ℝ) (M := V) (M₂ := V →L[ℝ] ℝ)
      (σ₁₂ := RingHom.id ℝ)
  letI : AddCommGroup (V →L[ℝ] V →L[ℝ] ℝ) := hOuterAdd
  letI : AddCommMonoid (V →L[ℝ] V →L[ℝ] ℝ) :=
    AddCommGroup.toAddCommMonoid
  letI : AddMonoid (V →L[ℝ] V →L[ℝ] ℝ) :=
    AddCommMonoid.toAddMonoid
  simp [surfaceDifferentialHilbertSchmidtInnerCLMAt,
    surfaceDifferentialHilbertSchmidtInnerAt]

/--
%%handwave
name:
  Hilbert-Schmidt pairing is symmetric
statement:
  The metric Hilbert-Schmidt pairing on vector-valued differentials is
  symmetric.
proof:
  Expand the Hilbert--Schmidt contraction and use symmetry of the inverse metric coefficients together with symmetry of the target inner product.
-/
theorem surfaceDifferentialHilbertSchmidtInnerAt_symm {X E : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : SmoothRiemannianMetricOnSurface X) (x : X)
    (A B : SurfaceDifferentialBundleFiber (X := X) (E := E) x) :
    surfaceDifferentialHilbertSchmidtInnerAt g x A B =
      surfaceDifferentialHilbertSchmidtInnerAt g x B A := by
  letI : IsManifold SurfaceRealModel ∞ X := g.isManifold_real
  simp [surfaceDifferentialHilbertSchmidtInnerAt,
    surfaceMetricInverseGramCoeffAt, surfaceMetricModelGramDetAt,
    real_inner_comm, g.toContMDiffRiemannianMetric.symm]
  ring_nf

/--
%%handwave
name:
  Hilbert-Schmidt square norm is positive
statement:
  A nonzero vector-valued differential has strictly positive
  Hilbert-Schmidt square norm.
proof:
  Write the differential by its values on \(1\) and \(i\).  The inverse
  metric contraction is the sum of a positive multiple of the first square
  norm and a positive multiple of a completed square.  If the differential is
  nonzero, at least one of its two coordinate values is nonzero.
-/
theorem surfaceDifferentialHilbertSchmidtInnerAt_pos {X E : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : SmoothRiemannianMetricOnSurface X) (x : X)
    (A : SurfaceDifferentialBundleFiber (X := X) (E := E) x)
    (hA : A ≠ 0) :
    0 < surfaceDifferentialHilbertSchmidtInnerAt g x A A := by
  letI : IsManifold SurfaceRealModel ∞ X := g.isManifold_real
  let b := g.toContMDiffRiemannianMetric.inner x
  let e₁ : TangentSpace SurfaceRealModel x := surfaceTangentModelBasisVector x 0
  let e₂ : TangentSpace SurfaceRealModel x := surfaceTangentModelBasisVector x 1
  let a : ℝ := b e₁ e₁
  let c : ℝ := b e₁ e₂
  let d : ℝ := b e₂ e₁
  let e : ℝ := b e₂ e₂
  let det : ℝ := surfaceMetricModelGramDetAt g x
  let u : E := A e₁
  let v : E := A e₂
  have hdet_pos : 0 < det := by
    simpa [det] using surfaceMetricModelGramDetAt_pos g x
  have ha_pos : 0 < a := by
    simpa [a, e₁, surfaceTangentModelBasisVector] using
      g.toContMDiffRiemannianMetric.pos x
        (show TangentSpace SurfaceRealModel x from (1 : ℂ)) (by
          change (1 : ℂ) ≠ 0
          norm_num)
  have hd_eq_c : d = c := by
    dsimp [d, c, e₁, e₂, surfaceTangentModelBasisVector]
    exact g.toContMDiffRiemannianMetric.symm x
      (show TangentSpace SurfaceRealModel x from Complex.I)
      (show TangentSpace SurfaceRealModel x from (1 : ℂ))
  have hdet_eq : det = a * e - c * c := by
    calc
      det = b e₁ e₁ * b e₂ e₂ - b e₁ e₂ * b e₂ e₁ := by
        simp [det, surfaceMetricModelGramDetAt, e₁, e₂, b]
      _ = a * e - c * c := by
        simp [a, c, d, e, hd_eq_c]
  have hcoord_ne : u ≠ 0 ∨ v ≠ 0 := by
    by_contra h
    push Not at h
    apply hA
    ext z
    let zc : ℂ := z
    have hz :
        z = (zc.re : ℝ) • e₁ + (zc.im : ℝ) • e₂ := by
      change zc = (zc.re : ℝ) • (1 : ℂ) + (zc.im : ℝ) • Complex.I
      apply Complex.ext <;> simp [zc]
    calc
      A z = A ((zc.re : ℝ) • e₁ + (zc.im : ℝ) • e₂) := by rw [hz]
      _ = (zc.re : ℝ) • u + (zc.im : ℝ) • v := by simp [u, v]
      _ = 0 := by simp [h.1, h.2]
  have hexpand :
      surfaceDifferentialHilbertSchmidtInnerAt g x A A =
        det⁻¹ *
          (e * inner ℝ u u -
            c * inner ℝ u v -
            d * inner ℝ v u +
            a * inner ℝ v v) := by
    simp [surfaceDifferentialHilbertSchmidtInnerAt,
      surfaceMetricInverseGramCoeffAt, surfaceMetricModelGramDetAt,
      surfaceTangentModelBasisVector, Fin.sum_univ_two, det, b, e₁, e₂, a, c, d, e,
      u, v]
    ring
  rw [hexpand]
  apply mul_pos (inv_pos.mpr hdet_pos)
  by_cases hu : u = 0
  · have hv : v ≠ 0 := hcoord_ne.resolve_left (by simp [hu])
    rw [hu]
    simp [hd_eq_c]
    exact mul_pos ha_pos (sq_pos_of_pos (norm_pos_iff.mpr hv))
  · have hnum_eq :
        e * inner ℝ u u -
            c * inner ℝ u v -
            d * inner ℝ v u +
            a * inner ℝ v v =
          (det / a) * inner ℝ u u +
            a * inner ℝ (v - (c / a) • u) (v - (c / a) • u) := by
      rw [hd_eq_c, real_inner_comm v u, hdet_eq]
      set α : ℝ := inner ℝ u u
      set β : ℝ := inner ℝ u v
      set γ : ℝ := inner ℝ v v
      have hinner :
          inner ℝ (v - (c / a) • u) (v - (c / a) • u) =
            γ - (c / a) * β - (c / a) * β + (c / a) * (c / a) * α := by
        calc
          inner ℝ (v - (c / a) • u) (v - (c / a) • u)
              = inner ℝ v v - inner ℝ v ((c / a) • u) -
                  inner ℝ ((c / a) • u) v +
                    inner ℝ ((c / a) • u) ((c / a) • u) := by
                simpa using (inner_sub_sub_self v ((c / a) • u) :
                  inner ℝ (v - (c / a) • u) (v - (c / a) • u) =
                    inner ℝ v v - inner ℝ v ((c / a) • u) -
                      inner ℝ ((c / a) • u) v +
                        inner ℝ ((c / a) • u) ((c / a) • u))
          _ = γ - (c / a) * β - (c / a) * β +
                (c / a) * (c / a) * α := by
              simp [real_inner_smul_left, real_inner_smul_right,
                real_inner_comm v u, α, β, γ, norm_smul, Real.norm_eq_abs,
                abs_of_pos ha_pos]
              rw [pow_two]
              calc
                |c| / a * ‖u‖ * (|c| / a * ‖u‖)
                    = (|c| * |c|) * (a⁻¹ * a⁻¹) * (‖u‖ * ‖u‖) := by
                      ring
                _ = c / a * (c / a) * ‖u‖ ^ 2 := by
                      rw [abs_mul_abs_self]
                      ring
      rw [hinner]
      rw [real_inner_comm u v]
      field_simp [ha_pos.ne']
      ring
    rw [hnum_eq]
    exact add_pos_of_pos_of_nonneg
      (mul_pos (div_pos hdet_pos ha_pos) (real_inner_self_pos.mpr hu))
      (mul_nonneg ha_pos.le (real_inner_self_nonneg))

/--
%%handwave
name:
  Model tangent basis vector
statement:
  A fixed finite basis of the model tangent space gives a basis vector in
  each tangent fiber.
-/
noncomputable def manifoldTangentModelBasisVector {H X : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I : ModelWithCorners ℝ H H) [TopologicalSpace X] [ChartedSpace H X]
    [FiniteDimensional ℝ H] (x : X) (i : Fin (Module.finrank ℝ H)) :
    TangentSpace I x :=
  show TangentSpace I x from Module.finBasis ℝ H i

/--
%%handwave
name:
  Metric Gram matrix in a model basis
statement:
  The Riemannian metric gives, in the fixed model tangent basis, a positive
  definite Gram matrix at each point.
-/
noncomputable def manifoldMetricModelGramMatrix {H X : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I : ModelWithCorners ℝ H H) [TopologicalSpace X] [ChartedSpace H X]
    [FiniteDimensional ℝ H]
    (g : SmoothRiemannianMetricOnManifold I X) (x : X) :
    Matrix (Fin (Module.finrank ℝ H)) (Fin (Module.finrank ℝ H)) ℝ :=
  letI : IsManifold I ∞ X := g.isManifold
  fun i j ↦
    g.toContMDiffRiemannianMetric.inner x
      (manifoldTangentModelBasisVector (I := I) (X := X) x i)
      (manifoldTangentModelBasisVector (I := I) (X := X) x j)

/--
%%handwave
name:
  Inverse metric coefficients in a model basis
statement:
  The inverse metric coefficients are the entries of the inverse Gram matrix
  of the Riemannian metric in the fixed model tangent basis.
-/
noncomputable def manifoldMetricInverseGramCoeffAt {H X : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I : ModelWithCorners ℝ H H) [TopologicalSpace X] [ChartedSpace H X]
    [FiniteDimensional ℝ H]
    (g : SmoothRiemannianMetricOnManifold I X) (x : X)
    (i j : Fin (Module.finrank ℝ H)) : ℝ :=
  (manifoldMetricModelGramMatrix (I := I) (X := X) g x)⁻¹ i j

/--
%%handwave
name:
  Hilbert-Schmidt pairing of vector-valued manifold differentials
statement:
  A Riemannian metric on the finite-dimensional base and an inner product on
  the target induce a Hilbert-Schmidt pairing on each fiber of
  \(T^\ast X\otimes E\).
-/
noncomputable def manifoldDifferentialHilbertSchmidtInnerAt {H X E : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I : ModelWithCorners ℝ H H) [TopologicalSpace X] [ChartedSpace H X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : SmoothRiemannianMetricOnManifold I X) (x : X)
    (A B : ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E) x) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ H), ∑ j : Fin (Module.finrank ℝ H),
    manifoldMetricInverseGramCoeffAt (I := I) (X := X) g x i j *
      inner ℝ (A (manifoldTangentModelBasisVector (I := I) (X := X) x i))
        (B (manifoldTangentModelBasisVector (I := I) (X := X) x j))

/--
%%handwave
name:
  Hilbert-Schmidt norm square of a manifold differential
statement:
  The pointwise square norm of a vector-valued differential is its
  Hilbert-Schmidt pairing with itself.
-/
noncomputable def manifoldDifferentialHilbertSchmidtNormSqAt {H X E : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I : ModelWithCorners ℝ H H) [TopologicalSpace X] [ChartedSpace H X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : SmoothRiemannianMetricOnManifold I X) (x : X)
    (A : ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E) x) : ℝ :=
  manifoldDifferentialHilbertSchmidtInnerAt (I := I) (X := X) g x A A

/--
%%handwave
name:
  Hilbert-Schmidt pairing as a continuous bilinear form over a manifold
statement:
  The metric Hilbert-Schmidt pairing on a fiber of \(T^\ast X\otimes E\) is
  represented by a continuous real bilinear form.
-/
noncomputable def manifoldDifferentialHilbertSchmidtInnerCLMAt {H X E : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I : ModelWithCorners ℝ H H) [TopologicalSpace X] [ChartedSpace H X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : SmoothRiemannianMetricOnManifold I X) (x : X) :
    ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E) x →L[ℝ]
      ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E) x →L[ℝ] ℝ := by
  let V := ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E) x
  let hVAdd : AddCommGroup V :=
    ContinuousLinearMap.addCommGroup
      (R := ℝ) (R₂ := ℝ)
      (M := TangentSpace I x) (M₂ := E)
      (σ₁₂ := RingHom.id ℝ)
  letI : AddCommGroup V := hVAdd
  letI : AddGroup V := AddCommGroup.toAddGroup
  letI : AddCommMonoid V := AddCommGroup.toAddCommMonoid
  let hVTop : IsTopologicalAddGroup V :=
    ContinuousLinearMap.topologicalAddGroup
      (𝕜₁ := ℝ) (𝕜₂ := ℝ)
      (σ := RingHom.id ℝ)
      (E := TangentSpace I x) (F := E)
  letI : IsTopologicalAddGroup V := hVTop
  let hDualAdd : AddCommGroup (V →L[ℝ] ℝ) :=
    ContinuousLinearMap.addCommGroup
      (R := ℝ) (R₂ := ℝ) (M := V) (M₂ := ℝ)
      (σ₁₂ := RingHom.id ℝ)
  letI : AddCommGroup (V →L[ℝ] ℝ) := hDualAdd
  letI : AddGroup (V →L[ℝ] ℝ) := AddCommGroup.toAddGroup
  letI : AddCommMonoid (V →L[ℝ] ℝ) := AddCommGroup.toAddCommMonoid
  letI : AddMonoid (V →L[ℝ] ℝ) := AddCommMonoid.toAddMonoid
  let hDualTop : IsTopologicalAddGroup (V →L[ℝ] ℝ) :=
    ContinuousLinearMap.topologicalAddGroup
      (𝕜₁ := ℝ) (𝕜₂ := ℝ) (σ := RingHom.id ℝ)
      (E := V) (F := ℝ)
  letI : IsTopologicalAddGroup (V →L[ℝ] ℝ) := hDualTop
  letI : ContinuousAdd (V →L[ℝ] ℝ) :=
    hDualTop.toContinuousAdd
  let hOuterAdd : AddCommGroup (V →L[ℝ] V →L[ℝ] ℝ) :=
    ContinuousLinearMap.addCommGroup
      (R := ℝ) (R₂ := ℝ) (M := V) (M₂ := V →L[ℝ] ℝ)
      (σ₁₂ := RingHom.id ℝ)
  letI : AddCommGroup (V →L[ℝ] V →L[ℝ] ℝ) := hOuterAdd
  letI : AddCommMonoid (V →L[ℝ] V →L[ℝ] ℝ) :=
    AddCommGroup.toAddCommMonoid
  letI : AddMonoid (V →L[ℝ] V →L[ℝ] ℝ) :=
    AddCommMonoid.toAddMonoid
  let innerReal : E →L[ℝ] E →L[ℝ] ℝ :=
    LinearMap.mkContinuous₂ (innerₗ E) 1 fun u v ↦ by
      simpa [innerₗ_apply_apply] using (norm_inner_le_norm (𝕜 := ℝ) u v)
  let eval (i : Fin (Module.finrank ℝ H)) :
      V →L[ℝ] E :=
    { toLinearMap :=
        (ContinuousLinearMap.coeLM ℝ
          (M := TangentSpace I x) (N₃ := E)).flip
            (manifoldTangentModelBasisVector (I := I) (X := X) x i)
      cont := continuous_eval_const
        (manifoldTangentModelBasisVector (I := I) (X := X) x i) }
  exact
    ∑ i : Fin (Module.finrank ℝ H), ∑ j : Fin (Module.finrank ℝ H),
      manifoldMetricInverseGramCoeffAt (I := I) (X := X) g x i j •
        ((ContinuousLinearMap.precomp (G := ℝ) (eval j)).comp
          (innerReal.comp (eval i)))

/--
%%handwave
name:
  Continuous Hilbert-Schmidt pairing evaluates to the metric formula
statement:
  The continuous bilinear form representing the manifold Hilbert-Schmidt
  pairing agrees with the coordinate formula obtained by contracting with the
  inverse Riemannian metric.
proof:
  Unfold the manifold differential-bundle metric and its associated continuous bilinear map.
-/
theorem manifoldDifferentialHilbertSchmidtInnerCLMAt_apply {H X E : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I : ModelWithCorners ℝ H H) [TopologicalSpace X] [ChartedSpace H X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : SmoothRiemannianMetricOnManifold I X) (x : X)
    (A B : ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E) x) :
    manifoldDifferentialHilbertSchmidtInnerCLMAt (I := I) (X := X) g x A B =
      manifoldDifferentialHilbertSchmidtInnerAt (I := I) (X := X) g x A B := by
  let V := ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E) x
  let hVAdd : AddCommGroup V :=
    ContinuousLinearMap.addCommGroup
      (R := ℝ) (R₂ := ℝ)
      (M := TangentSpace I x) (M₂ := E)
      (σ₁₂ := RingHom.id ℝ)
  letI : AddCommGroup V := hVAdd
  letI : AddGroup V := AddCommGroup.toAddGroup
  letI : AddCommMonoid V := AddCommGroup.toAddCommMonoid
  let hVTop : IsTopologicalAddGroup V :=
    ContinuousLinearMap.topologicalAddGroup
      (𝕜₁ := ℝ) (𝕜₂ := ℝ)
      (σ := RingHom.id ℝ)
      (E := TangentSpace I x) (F := E)
  letI : IsTopologicalAddGroup V := hVTop
  let hDualAdd : AddCommGroup (V →L[ℝ] ℝ) :=
    ContinuousLinearMap.addCommGroup
      (R := ℝ) (R₂ := ℝ) (M := V) (M₂ := ℝ)
      (σ₁₂ := RingHom.id ℝ)
  letI : AddCommGroup (V →L[ℝ] ℝ) := hDualAdd
  letI : AddGroup (V →L[ℝ] ℝ) := AddCommGroup.toAddGroup
  letI : AddCommMonoid (V →L[ℝ] ℝ) := AddCommGroup.toAddCommMonoid
  letI : AddMonoid (V →L[ℝ] ℝ) := AddCommMonoid.toAddMonoid
  let hDualTop : IsTopologicalAddGroup (V →L[ℝ] ℝ) :=
    ContinuousLinearMap.topologicalAddGroup
      (𝕜₁ := ℝ) (𝕜₂ := ℝ) (σ := RingHom.id ℝ)
      (E := V) (F := ℝ)
  letI : IsTopologicalAddGroup (V →L[ℝ] ℝ) := hDualTop
  letI : ContinuousAdd (V →L[ℝ] ℝ) :=
    hDualTop.toContinuousAdd
  let hOuterAdd : AddCommGroup (V →L[ℝ] V →L[ℝ] ℝ) :=
    ContinuousLinearMap.addCommGroup
      (R := ℝ) (R₂ := ℝ) (M := V) (M₂ := V →L[ℝ] ℝ)
      (σ₁₂ := RingHom.id ℝ)
  letI : AddCommGroup (V →L[ℝ] V →L[ℝ] ℝ) := hOuterAdd
  letI : AddCommMonoid (V →L[ℝ] V →L[ℝ] ℝ) :=
    AddCommGroup.toAddCommMonoid
  letI : AddMonoid (V →L[ℝ] V →L[ℝ] ℝ) :=
    AddCommMonoid.toAddMonoid
  simp [manifoldDifferentialHilbertSchmidtInnerCLMAt,
    manifoldDifferentialHilbertSchmidtInnerAt]

/--
%%handwave
name:
  The manifold metric Gram matrix is symmetric
statement:
  The Gram matrix of a Riemannian metric in a fixed model tangent basis is
  symmetric.
proof:
  Each matrix entry is a Riemannian metric pairing of two basis vectors, so symmetry of the metric swaps the indices.
-/
theorem manifoldMetricModelGramMatrix_isSymm {H X : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I : ModelWithCorners ℝ H H) [TopologicalSpace X] [ChartedSpace H X]
    [FiniteDimensional ℝ H]
    (g : SmoothRiemannianMetricOnManifold I X) (x : X) :
    (manifoldMetricModelGramMatrix (I := I) (X := X) g x).IsSymm := by
  letI : IsManifold I ∞ X := g.isManifold
  apply Matrix.IsSymm.ext
  intro i j
  exact
    g.toContMDiffRiemannianMetric.symm x
      (manifoldTangentModelBasisVector (I := I) (X := X) x j)
      (manifoldTangentModelBasisVector (I := I) (X := X) x i)

/--
%%handwave
name:
  The manifold metric Gram matrix is positive definite
statement:
  The Gram matrix of a Riemannian metric in a fixed model tangent basis is
  positive definite.
proof:
  Register the Riemannian metric as the inner product on the tangent fiber.
  The fixed model tangent vectors form a basis of the tangent fiber, hence are
  linearly independent; the standard Gram-matrix theorem then gives positive
  definiteness.
-/
theorem manifoldMetricModelGramMatrix_posDef {H X : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I : ModelWithCorners ℝ H H) [TopologicalSpace X] [ChartedSpace H X]
    [FiniteDimensional ℝ H]
    (g : SmoothRiemannianMetricOnManifold I X) (x : X) :
    (manifoldMetricModelGramMatrix (I := I) (X := X) g x).PosDef := by
  letI : IsManifold I ∞ X := g.isManifold
  let metric := g.toContMDiffRiemannianMetric.toRiemannianMetric
  letI : Bundle.RiemannianBundle (fun x : X ↦ TangentSpace I x) := ⟨metric⟩
  let v : Fin (Module.finrank ℝ H) → TangentSpace I x :=
    fun i ↦ manifoldTangentModelBasisVector (I := I) (X := X) x i
  have hv : LinearIndependent ℝ v := by
    change LinearIndependent ℝ (fun i : Fin (Module.finrank ℝ H) ↦
      (Module.finBasis ℝ H i : TangentSpace I x))
    exact (Module.finBasis ℝ H).linearIndependent
  have hgram : (Matrix.gram ℝ v).PosDef :=
    Matrix.posDef_gram_of_linearIndependent hv
  convert hgram using 1

/--
%%handwave
name:
  The inverse manifold metric Gram matrix is positive definite
statement:
  The inverse of the Riemannian metric Gram matrix in a fixed model tangent
  basis is positive definite.
proof:
  The Gram matrix of a positive-definite metric in a basis is positive definite; its inverse is therefore positive definite as well.
-/
theorem manifoldMetricModelGramMatrix_inv_posDef {H X : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I : ModelWithCorners ℝ H H) [TopologicalSpace X] [ChartedSpace H X]
    [FiniteDimensional ℝ H]
    (g : SmoothRiemannianMetricOnManifold I X) (x : X) :
    ((manifoldMetricModelGramMatrix (I := I) (X := X) g x)⁻¹).PosDef :=
  (manifoldMetricModelGramMatrix_posDef (I := I) (X := X) g x).inv

/--
%%handwave
name:
  Positive definite contraction with a nonzero positive semidefinite matrix
statement:
  Contracting a positive definite matrix with a nonzero positive semidefinite
  matrix has strictly positive trace.
proof:
  Factor the positive definite matrix as \(B^\ast B\).  Cyclicity of trace
  rewrites the contraction as the trace of \(BKB^\ast\).  This matrix is
  positive semidefinite and nonzero, hence its trace is strictly positive.
-/
theorem Matrix.PosDef.trace_mul_pos_of_posSemidef_ne_zero
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {C K : Matrix ι ι ℝ} (hC : C.PosDef) (hK : K.PosSemidef)
    (hKne : K ≠ 0) :
    0 < (C * K).trace := by
  classical
  obtain ⟨B, hBunit, hCeq⟩ :=
    CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp hC.isStrictlyPositive
  have hBKpsd : (B * K * Matrix.conjTranspose B).PosSemidef :=
    hK.mul_mul_conjTranspose_same B
  have hBKne : B * K * Matrix.conjTranspose B ≠ 0 := by
    intro hzero
    apply hKne
    have hBstar : IsUnit (Matrix.conjTranspose B) := by
      simpa [Matrix.star_eq_conjTranspose] using hBunit.star
    have hleft : K * Matrix.conjTranspose B = 0 := by
      apply hBunit.mul_right_inj.mp
      simpa [Matrix.mul_assoc] using hzero
    apply hBstar.mul_left_inj.mp
    simpa using hleft
  have htrace_pos : 0 < (B * K * Matrix.conjTranspose B).trace :=
    hBKpsd.trace_nonneg.lt_of_ne' fun htrace_zero ↦
      hBKne ((hBKpsd.trace_eq_zero_iff).mp htrace_zero)
  calc
    0 < (B * K * Matrix.conjTranspose B).trace := htrace_pos
    _ = (Matrix.conjTranspose B * (B * K)).trace := by
      exact Matrix.trace_mul_comm (B * K) (Matrix.conjTranspose B)
    _ = ((Matrix.conjTranspose B * B) * K).trace := by rw [← Matrix.mul_assoc]
    _ = (C * K).trace := by
      rw [hCeq]
      simp [Matrix.star_eq_conjTranspose]

/--
%%handwave
name:
  Coordinate contraction and trace
statement:
  Contracting a matrix with a symmetric matrix entrywise is the trace of their
  product.
proof:
  Expand the trace and matrix product as finite sums, use symmetry to swap the relevant indices, and commute the scalar factors.
-/
theorem Matrix.sum_mul_of_isSymm_eq_trace_mul
    {ι : Type} [Fintype ι] {C K : Matrix ι ι ℝ} (hK : K.IsSymm) :
    (∑ i, ∑ j, C i j * K i j) = (C * K).trace := by
  classical
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [← hK.apply i j]

/--
%%handwave
name:
  Hilbert-Schmidt pairing on manifold differentials is symmetric
statement:
  The metric Hilbert-Schmidt pairing on vector-valued differentials over a
  manifold is symmetric.
proof:
  Write the contraction in basis coordinates, swap the two differential fields, and use symmetry of both the inverse Gram matrix and the target inner product.
-/
theorem manifoldDifferentialHilbertSchmidtInnerAt_symm {H X E : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I : ModelWithCorners ℝ H H) [TopologicalSpace X] [ChartedSpace H X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : SmoothRiemannianMetricOnManifold I X) (x : X)
    (A B : ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E) x) :
    manifoldDifferentialHilbertSchmidtInnerAt (I := I) (X := X) g x A B =
      manifoldDifferentialHilbertSchmidtInnerAt (I := I) (X := X) g x B A := by
  classical
  let C := (manifoldMetricModelGramMatrix (I := I) (X := X) g x)⁻¹
  have hC : C.IsSymm := (manifoldMetricModelGramMatrix_isSymm
    (I := I) (X := X) g x).inv
  simp only [manifoldDifferentialHilbertSchmidtInnerAt,
    manifoldMetricInverseGramCoeffAt]
  calc
    (∑ i : Fin (Module.finrank ℝ H), ∑ j : Fin (Module.finrank ℝ H),
        C i j *
          inner ℝ
            (A (manifoldTangentModelBasisVector (I := I) (X := X) x i))
            (B (manifoldTangentModelBasisVector (I := I) (X := X) x j)))
        =
      ∑ j : Fin (Module.finrank ℝ H), ∑ i : Fin (Module.finrank ℝ H),
        C i j *
          inner ℝ
            (A (manifoldTangentModelBasisVector (I := I) (X := X) x i))
            (B (manifoldTangentModelBasisVector (I := I) (X := X) x j)) := by
          rw [Finset.sum_comm]
    _ =
      ∑ j : Fin (Module.finrank ℝ H), ∑ i : Fin (Module.finrank ℝ H),
        C j i *
          inner ℝ
            (A (manifoldTangentModelBasisVector (I := I) (X := X) x i))
            (B (manifoldTangentModelBasisVector (I := I) (X := X) x j)) := by
          refine Finset.sum_congr rfl ?_
          intro j _
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [hC.apply i j]
    _ =
      ∑ j : Fin (Module.finrank ℝ H), ∑ i : Fin (Module.finrank ℝ H),
        C j i *
          inner ℝ
            (B (manifoldTangentModelBasisVector (I := I) (X := X) x j))
            (A (manifoldTangentModelBasisVector (I := I) (X := X) x i)) := by
          simp [real_inner_comm]

/--
%%handwave
name:
  Continuous Hilbert-Schmidt pairing on manifold differentials is symmetric
statement:
  The continuous bilinear form representing the metric Hilbert-Schmidt pairing
  on vector-valued differentials is symmetric in the two differential
  arguments.
proof:
  Evaluate both continuous bilinear forms on arbitrary fields and apply symmetry of the underlying Hilbert--Schmidt inner product.
-/
theorem manifoldDifferentialHilbertSchmidtInnerCLMAt_symm {H X E : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I : ModelWithCorners ℝ H H) [TopologicalSpace X] [ChartedSpace H X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : SmoothRiemannianMetricOnManifold I X) (x : X)
    (A B : ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E) x) :
    manifoldDifferentialHilbertSchmidtInnerCLMAt (I := I) (X := X) g x A B =
      manifoldDifferentialHilbertSchmidtInnerCLMAt (I := I) (X := X) g x B A := by
  rw [manifoldDifferentialHilbertSchmidtInnerCLMAt_apply,
    manifoldDifferentialHilbertSchmidtInnerCLMAt_apply]
  exact manifoldDifferentialHilbertSchmidtInnerAt_symm (I := I) (X := X) g x A B

/--
%%handwave
name:
  Hilbert-Schmidt norm on manifold differentials is positive definite
statement:
  The metric Hilbert-Schmidt square norm of a nonzero vector-valued
  differential is strictly positive.
proof:
  The inverse Gram matrix of a Riemannian metric is positive definite, and
  contracting it against the positive semidefinite matrix of target inner
  products gives a nonnegative quantity.  If the differential is nonzero, one
  coefficient in any basis is nonzero, and the resulting contraction is
  strictly positive.
-/
theorem manifoldDifferentialHilbertSchmidtInnerAt_pos {H X E : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I : ModelWithCorners ℝ H H) [TopologicalSpace X] [ChartedSpace H X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : SmoothRiemannianMetricOnManifold I X) (x : X)
    (A : ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E) x)
    (hA : A ≠ 0) :
    0 < manifoldDifferentialHilbertSchmidtInnerAt (I := I) (X := X) g x A A := by
  classical
  let ι := Fin (Module.finrank ℝ H)
  let C : Matrix ι ι ℝ := (manifoldMetricModelGramMatrix (I := I) (X := X) g x)⁻¹
  let v : ι → TangentSpace I x :=
    fun i ↦ manifoldTangentModelBasisVector (I := I) (X := X) x i
  let u : ι → Bundle.Trivial X E x := fun i ↦ A (v i)
  let K : Matrix ι ι ℝ := Matrix.gram ℝ u
  have hC : C.PosDef :=
    manifoldMetricModelGramMatrix_inv_posDef (I := I) (X := X) g x
  have hK : K.PosSemidef := by
    simpa [K] using Matrix.posSemidef_gram (𝕜 := ℝ) u
  have hKsymm : K.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    simp [K, real_inner_comm]
  have hu_ne_zero : u ≠ 0 := by
    intro hu
    apply hA
    ext w
    let bT : Module.Basis ι ℝ (TangentSpace I x) := Module.finBasis ℝ H
    have hcoord : ∀ i : ι, A (bT i) = 0 := by
      intro i
      have hi := congrFun hu i
      simpa [u, v, bT, manifoldTangentModelBasisVector] using hi
    calc
      A w = A (∑ i : ι, bT.repr w i • bT i) := by
        rw [bT.sum_repr w]
      _ = ∑ i : ι, A (bT.repr w i • bT i) := by
        rw [map_sum]
      _ = ∑ i : ι, bT.repr w i • A (bT i) := by
        simp
      _ = 0 := by
        simp [hcoord]
  have hKne : K ≠ 0 := by
    obtain ⟨i, hi⟩ : ∃ i : ι, u i ≠ 0 := by
      by_contra h
      apply hu_ne_zero
      ext i
      exact not_not.mp (not_exists.mp h i)
    intro hKzero
    apply hi
    have hii : inner ℝ (u i) (u i) = 0 := by
      simpa [K] using congrFun (congrFun hKzero i) i
    exact inner_self_eq_zero.mp hii
  have htrace_pos : 0 < (C * K).trace :=
    Matrix.PosDef.trace_mul_pos_of_posSemidef_ne_zero hC hK hKne
  have hformula :
      manifoldDifferentialHilbertSchmidtInnerAt (I := I) (X := X) g x A A =
        ∑ i : ι, ∑ j : ι, C i j * K i j := by
    dsimp [manifoldDifferentialHilbertSchmidtInnerAt,
      manifoldMetricInverseGramCoeffAt, C, K, u, v, Matrix.gram]
  rw [hformula, Matrix.sum_mul_of_isSymm_eq_trace_mul hKsymm]
  exact htrace_pos

/--
%%handwave
name:
  Gram contraction after a square-root factorization
statement:
  For a real matrix \(B\) and vectors \(u_i\) in a real inner-product space,
  \[
    \sum_{i,j}(B^\mathsf{T}B)_{ij}\langle u_i,u_j\rangle
    =\sum_a\left\langle\sum_iB_{ai}u_i,\sum_jB_{aj}u_j\right\rangle.
  \]
proof:
  Expand the matrix product and both inner products, then interchange the three finite sums.
-/
theorem Matrix.conjTranspose_mul_self_inner_sum
    {ι E : Type} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (B : Matrix ι ι ℝ) (u : ι → E) :
    (∑ i : ι, ∑ j : ι,
        (Matrix.conjTranspose B * B) i j * inner ℝ (u i) (u j)) =
      ∑ a : ι, inner ℝ (∑ i : ι, B a i • u i)
        (∑ j : ι, B a j • u j) := by
  classical
  let f : ι → ι → ι → ℝ :=
    fun i j a ↦ (B a i * B a j) * inner ℝ (u i) (u j)
  calc
    (∑ i : ι, ∑ j : ι,
        (Matrix.conjTranspose B * B) i j * inner ℝ (u i) (u j))
        = ∑ i : ι, ∑ j : ι, ∑ a : ι, f i j a := by
          simp [f, Matrix.mul_apply, Finset.sum_mul, mul_assoc]
    _ = ∑ i : ι, ∑ a : ι, ∑ j : ι, f i j a := by
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ a : ι, ∑ i : ι, ∑ j : ι, f i j a := by
      rw [Finset.sum_comm]
    _ = ∑ a : ι, inner ℝ (∑ i : ι, B a i • u i)
        (∑ j : ι, B a j • u j) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          symm
          simp_rw [inner_sum, sum_inner, real_inner_smul_left, real_inner_smul_right]
          simp [f, real_inner_comm, mul_assoc, mul_left_comm]

/--
%%handwave
name:
  Inverting a scalar matrix acting on a vector-valued family
statement:
  If \(B^{-1}B=I\), then for every finite family \(u_k\) in a real module,
  \[
    \sum_a(B^{-1})_{ia}\left(\sum_kB_{ak}u_k\right)=u_i.
  \]
proof:
  Distribute scalar multiplication through the sums, interchange the finite sums, and use the \((i,k)\)-entry of \(B^{-1}B=I\).
-/
theorem Matrix.inv_mul_smulVec_apply
    {ι E : Type} [Fintype ι] [DecidableEq ι]
    [AddCommMonoid E] [Module ℝ E]
    (B : Matrix ι ι ℝ) (hB : B⁻¹ * B = 1) (u : ι → E) (i : ι) :
    ∑ a : ι, B⁻¹ i a • (∑ k : ι, B a k • u k) = u i := by
  classical
  calc
    ∑ a : ι, B⁻¹ i a • (∑ k : ι, B a k • u k)
        = ∑ a : ι, ∑ k : ι, (B⁻¹ i a * B a k) • u k := by
          simp [Finset.smul_sum, smul_smul]
    _ = ∑ k : ι, ∑ a : ι, (B⁻¹ i a * B a k) • u k := by
      rw [Finset.sum_comm]
    _ = ∑ k : ι, ((B⁻¹ * B) i k) • u k := by
      refine Finset.sum_congr rfl ?_
      intro k _
      simp [Matrix.mul_apply, Finset.sum_smul]
    _ = u i := by
      rw [hB]
      simp [Matrix.one_apply]

/--
%%handwave
name:
  Hilbert-Schmidt unit ball is bounded in the model topology
statement:
  The unit ball of the metric Hilbert-Schmidt norm on a fiber of
  \(T^\ast X\otimes E\) is bounded for the vector-bundle model topology.
proof:
  On each finite-dimensional tangent fiber, the Hilbert-Schmidt norm induced by
  the Riemannian metric is equivalent to the operator norm obtained from the
  local vector-bundle model.  Boundedness of the Hilbert-Schmidt unit ball
  therefore follows from norm equivalence.
-/
theorem manifoldDifferentialHilbertSchmidtInnerCLMAt_isVonNBounded
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I : ModelWithCorners ℝ H H) [TopologicalSpace X] [ChartedSpace H X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : SmoothRiemannianMetricOnManifold I X) (x : X) :
    Bornology.IsVonNBounded ℝ
      {A : ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E) x |
        manifoldDifferentialHilbertSchmidtInnerCLMAt (I := I) (X := X) g x A A < 1} := by
  classical
  letI : NormedAddCommGroup (TangentSpace I x) := by
    change NormedAddCommGroup H
    infer_instance
  letI : NormedSpace ℝ (TangentSpace I x) := by
    change NormedSpace ℝ H
    infer_instance
  letI : T2Space (TangentSpace I x) := by
    change T2Space H
    infer_instance
  letI : NormedAddCommGroup (Bundle.Trivial X E x) :=
    inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (Bundle.Trivial X E x) :=
    inferInstanceAs (NormedSpace ℝ E)
  letI : T2Space (Bundle.Trivial X E x) :=
    inferInstanceAs (T2Space E)
  letI : SeminormedAddCommGroup (TangentSpace I x →L[ℝ] Bundle.Trivial X E x) :=
    ContinuousLinearMap.toSeminormedAddCommGroup
  letI : NormedSpace ℝ (TangentSpace I x →L[ℝ] Bundle.Trivial X E x) :=
    ContinuousLinearMap.toNormedSpace
  change Bornology.IsVonNBounded ℝ
      {A : TangentSpace I x →L[ℝ] Bundle.Trivial X E x |
        manifoldDifferentialHilbertSchmidtInnerCLMAt (I := I) (X := X) g x A A < 1}
  let ι := Fin (Module.finrank ℝ H)
  let bT : Module.Basis ι ℝ (TangentSpace I x) := Module.finBasis ℝ H
  let C : Matrix ι ι ℝ :=
    (manifoldMetricModelGramMatrix (I := I) (X := X) g x)⁻¹
  have hC : C.PosDef :=
    manifoldMetricModelGramMatrix_inv_posDef (I := I) (X := X) g x
  obtain ⟨B, hBunit, hCeq⟩ :=
    CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp hC.isStrictlyPositive
  obtain ⟨opC, hopC_pos, hopC⟩ :=
    bT.exists_opNorm_le (F := Bundle.Trivial X E x)
  let coordinateBound : ℝ := ∑ i : ι, ∑ a : ι, |B⁻¹ i a|
  let M : ℝ := max 1 coordinateBound
  refine (NormedSpace.isVonNBounded_iff'
    (𝕜 := ℝ)
    (E := TangentSpace I x →L[ℝ] Bundle.Trivial X E x)).2 ?_
  refine ⟨opC * M, ?_⟩
  intro A hA
  let u : ι → Bundle.Trivial X E x := fun i ↦ A (bT i)
  let w : ι → Bundle.Trivial X E x := fun a ↦ ∑ i : ι, B a i • u i
  have hformula :
      manifoldDifferentialHilbertSchmidtInnerAt (I := I) (X := X) g x A A =
        ∑ i : ι, ∑ j : ι, C i j * inner ℝ (u i) (u j) := by
    dsimp [manifoldDifferentialHilbertSchmidtInnerAt,
      manifoldMetricInverseGramCoeffAt, C, u, bT, manifoldTangentModelBasisVector]
    rfl
  have hCeq' : C = Matrix.conjTranspose B * B := by
    rw [hCeq]
    simp [Matrix.star_eq_conjTranspose]
  have hsum_eq :
      (∑ i : ι, ∑ j : ι, C i j * inner ℝ (u i) (u j)) =
        ∑ a : ι, inner ℝ (w a) (w a) := by
    rw [hCeq']
    simpa [w] using Matrix.conjTranspose_mul_self_inner_sum B u
  have hsum_lt : ∑ a : ι, inner ℝ (w a) (w a) < 1 := by
    have hA' :
        manifoldDifferentialHilbertSchmidtInnerAt (I := I) (X := X) g x A A < 1 := by
      simpa [manifoldDifferentialHilbertSchmidtInnerCLMAt_apply] using hA
    rw [hformula, hsum_eq] at hA'
    exact hA'
  have hw_le_one (a : ι) : ‖w a‖ ≤ 1 := by
    have hterm_le :
        inner ℝ (w a) (w a) ≤ ∑ b : ι, inner ℝ (w b) (w b) :=
      Finset.single_le_sum
        (s := Finset.univ)
        (f := fun b : ι ↦ inner ℝ (w b) (w b))
        (fun b _ ↦ real_inner_self_nonneg (x := w b))
        (Finset.mem_univ a)
    have hterm_lt : inner ℝ (w a) (w a) < 1 :=
      lt_of_le_of_lt hterm_le hsum_lt
    have hsq : ‖w a‖ ^ 2 < 1 := by
      simpa [real_inner_self_eq_norm_sq] using hterm_lt
    have hnorm_nonneg : 0 ≤ ‖w a‖ := norm_nonneg _
    nlinarith
  have hBleft : B⁻¹ * B = 1 := by
    exact B.nonsing_inv_mul (Matrix.isUnit_iff_isUnit_det B |>.mp hBunit)
  have hu_recover (i : ι) : u i = ∑ a : ι, B⁻¹ i a • w a := by
    symm
    simpa [w] using Matrix.inv_mul_smulVec_apply (B := B) hBleft u i
  have hM_nonneg : 0 ≤ M := by
    exact le_trans zero_le_one (le_max_left (1 : ℝ) coordinateBound)
  have hu_bound (i : ι) : ‖u i‖ ≤ M := by
    rw [hu_recover i]
    calc
      ‖∑ a : ι, B⁻¹ i a • w a‖
          ≤ ∑ a : ι, ‖B⁻¹ i a • w a‖ := norm_sum_le _ _
      _ = ∑ a : ι, |B⁻¹ i a| * ‖w a‖ := by
        simp [norm_smul, Real.norm_eq_abs]
      _ ≤ ∑ a : ι, |B⁻¹ i a| * 1 := by
        refine Finset.sum_le_sum ?_
        intro a _
        exact mul_le_mul_of_nonneg_left (hw_le_one a) (abs_nonneg _)
      _ = ∑ a : ι, |B⁻¹ i a| := by
        simp
      _ ≤ coordinateBound := by
        dsimp [coordinateBound]
        exact Finset.single_le_sum
          (fun j _ ↦ Finset.sum_nonneg fun a _ ↦ abs_nonneg (B⁻¹ j a))
          (Finset.mem_univ i)
      _ ≤ M := le_max_right _ _
  exact hopC hM_nonneg (by simpa [u] using hu_bound)

/--
%%handwave
name:
  Local coordinates for the Hilbert-Schmidt bundle metric
statement:
  In a local trivialization of the bundle of vector-valued differentials, the
  Hilbert-Schmidt metric at a nearby point evaluates on model vectors by first
  transporting those model vectors back to the two differential fibers and then
  applying the fiberwise Hilbert-Schmidt pairing.
proof:
  Unfold transport through the local differential-bundle trivialization and evaluate the resulting coordinate bilinear form.
-/
theorem manifoldDifferentialHilbertSchmidtInnerCLMAt_inCoordinates_apply
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I : ModelWithCorners ℝ H H) [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold I 1 X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : SmoothRiemannianMetricOnManifold I X) (x₀ y : X)
    (hy : y ∈
      (trivializationAt (H →L[ℝ] E)
        (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E)) x₀).baseSet)
    (A B : H →L[ℝ] E) :
    ContinuousLinearMap.inCoordinates (H →L[ℝ] E)
        (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E))
        ((H →L[ℝ] E) →L[ℝ] ℝ)
        (fun x : X ↦
          ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E) x →L[ℝ]
            Bundle.Trivial X ℝ x)
        x₀ y x₀ y
        (manifoldDifferentialHilbertSchmidtInnerCLMAt
          (I := I) (X := X) (E := E) g y) A B =
      manifoldDifferentialHilbertSchmidtInnerCLMAt
        (I := I) (X := X) (E := E) g y
        ((trivializationAt (H →L[ℝ] E)
          (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E)) x₀).symm y A)
        ((trivializationAt (H →L[ℝ] E)
          (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E)) x₀).symm y B) := by
  rw [inCoordinates_apply_eq₂ hy hy (by simp)]
  simp

/--
%%handwave
name:
  Coordinate formula for the Hilbert-Schmidt bundle metric
statement:
  In local coordinates, evaluating the Hilbert-Schmidt bundle metric on two
  model differentials is the finite contraction of the inverse metric
  coefficients with the target inner products of the transported
  differentials.
proof:
  Expand the coordinate model and obtain the double finite contraction of inverse metric coefficients with the target inner products of basis evaluations.
-/
theorem manifoldDifferentialHilbertSchmidtInnerCLMAt_inCoordinates_apply_eq_sum
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I : ModelWithCorners ℝ H H) [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold I 1 X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : SmoothRiemannianMetricOnManifold I X) (x₀ y : X)
    (hy : y ∈
      (trivializationAt (H →L[ℝ] E)
        (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E)) x₀).baseSet)
    (A B : H →L[ℝ] E) :
    ContinuousLinearMap.inCoordinates (H →L[ℝ] E)
        (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E))
        ((H →L[ℝ] E) →L[ℝ] ℝ)
        (fun x : X ↦
          ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E) x →L[ℝ]
            Bundle.Trivial X ℝ x)
        x₀ y x₀ y
        (manifoldDifferentialHilbertSchmidtInnerCLMAt
          (I := I) (X := X) (E := E) g y) A B =
      ∑ i : Fin (Module.finrank ℝ H), ∑ j : Fin (Module.finrank ℝ H),
        manifoldMetricInverseGramCoeffAt (I := I) (X := X) g y i j *
          inner ℝ
            (((trivializationAt (H →L[ℝ] E)
              (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E)) x₀).symm y A)
                (manifoldTangentModelBasisVector (I := I) (X := X) y i))
            (((trivializationAt (H →L[ℝ] E)
              (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E)) x₀).symm y B)
                (manifoldTangentModelBasisVector (I := I) (X := X) y j)) := by
  rw [manifoldDifferentialHilbertSchmidtInnerCLMAt_inCoordinates_apply
    (I := I) (X := X) (E := E) g x₀ y hy A B]
  rw [manifoldDifferentialHilbertSchmidtInnerCLMAt_apply]
  rfl

/--
%%handwave
name:
  Coordinate Riemannian matrix for a manifold metric
statement:
  In a tangent-bundle trivialization, the Riemannian metric is represented by
  its Gram matrix on the fixed model basis.
-/
noncomputable def manifoldMetricCoordinateGramMatrix {H X : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I : ModelWithCorners ℝ H H) [TopologicalSpace X] [ChartedSpace H X]
    [IsManifold I 1 X] [FiniteDimensional ℝ H]
    (g : SmoothRiemannianMetricOnManifold I X) (x₀ y : X) :
    Matrix (Fin (Module.finrank ℝ H)) (Fin (Module.finrank ℝ H)) ℝ :=
  fun i j ↦
    ContinuousLinearMap.inCoordinates H
      (TangentSpace I : X → Type)
      (H →L[ℝ] ℝ)
      (fun x : X ↦ TangentSpace I x →L[ℝ] ℝ)
      x₀ y x₀ y
      (g.toContMDiffRiemannianMetric.inner y)
      (Module.finBasis ℝ H i)
      (Module.finBasis ℝ H j)

/--
%%handwave
name:
  The metric in tangent coordinates is continuous
statement:
  The coordinate expression of a smooth Riemannian metric in any local tangent
  trivialization is continuous at the base point.
proof:
  In a fixed local trivialization, continuity of the Riemannian bundle metric gives continuity of its coordinate bilinear form at the base point.
-/
theorem manifoldMetricInCoordinates_continuousAt {H X : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I : ModelWithCorners ℝ H H) [TopologicalSpace X] [ChartedSpace H X]
    [IsManifold I 1 X]
    (g : SmoothRiemannianMetricOnManifold I X) (x₀ : X) :
    ContinuousAt
      (fun y : X ↦
        ContinuousLinearMap.inCoordinates H
          (TangentSpace I : X → Type)
          (H →L[ℝ] ℝ)
          (fun x : X ↦ TangentSpace I x →L[ℝ] ℝ)
          x₀ y x₀ y
          (g.toContMDiffRiemannianMetric.inner y))
      x₀ := by
  letI : IsManifold I ∞ X := g.isManifold
  have hcont :=
    g.toContMDiffRiemannianMetric.contMDiff.continuous.continuousAt (x := x₀)
  rw [continuousAt_hom_bundle] at hcont
  exact hcont.2

/--
%%handwave
name:
  Coordinate Riemannian matrices are continuous
statement:
  The Gram matrix of a smooth Riemannian metric in local tangent coordinates
  varies continuously at the base point.
proof:
  Each Gram-matrix entry is evaluation of the continuous coordinate metric on two constant basis vectors.
-/
theorem manifoldMetricCoordinateGramMatrix_continuousAt {H X : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I : ModelWithCorners ℝ H H) [TopologicalSpace X] [ChartedSpace H X]
    [IsManifold I 1 X] [FiniteDimensional ℝ H]
    (g : SmoothRiemannianMetricOnManifold I X) (x₀ : X) :
    ContinuousAt
      (fun y : X ↦ manifoldMetricCoordinateGramMatrix
        (I := I) (X := X) g x₀ y)
      x₀ := by
  have hmetric :=
    manifoldMetricInCoordinates_continuousAt
      (I := I) (X := X) g x₀
  refine continuousAt_pi.2 ?_
  intro i
  refine continuousAt_pi.2 ?_
  intro j
  exact (hmetric.clm_apply continuousAt_const).clm_apply continuousAt_const

/--
%%handwave
name:
  Coordinate and fiber Gram matrices agree at the base point
statement:
  At the center of a tangent trivialization, the coordinate Gram matrix of a
  Riemannian metric is the Gram matrix in the model tangent basis.
proof:
  At the chart base point, the coordinate trivialization is the identity on the model tangent fiber, so the coordinate Gram matrix is the model Gram matrix.
-/
theorem manifoldMetricCoordinateGramMatrix_self {H X : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I : ModelWithCorners ℝ H H) [TopologicalSpace X] [ChartedSpace H X]
    [IsManifold I 1 X] [FiniteDimensional ℝ H]
    (g : SmoothRiemannianMetricOnManifold I X) (x₀ : X) :
    manifoldMetricCoordinateGramMatrix (I := I) (X := X) g x₀ x₀ =
      manifoldMetricModelGramMatrix (I := I) (X := X) g x₀ := by
  ext i j
  rw [manifoldMetricCoordinateGramMatrix]
  rw [inCoordinates_apply_eq₂
    (FiberBundle.mem_baseSet_trivializationAt' x₀)
    (FiberBundle.mem_baseSet_trivializationAt' x₀)
    (by simp)]
  let eT := trivializationAt H (TangentSpace I : X → Type) x₀
  have hb : x₀ ∈ eT.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
  have heT :
      eT.continuousLinearMapAt ℝ x₀ = ContinuousLinearMap.id ℝ H := by
    rw [TangentBundle.continuousLinearMapAt_trivializationAt
      (I := I) (x₀ := x₀) (x := x₀) (by simp)]
    exact mfderiv_extChartAt_self
  have hsymm (k : Fin (Module.finrank ℝ H)) :
      eT.symm x₀ ((Module.finBasis ℝ H) k) =
        (show TangentSpace I x₀ from (Module.finBasis ℝ H) k) := by
    have h :=
      eT.continuousLinearMapAt_symmL (R := ℝ) hb
        ((Module.finBasis ℝ H) k)
    rw [heT] at h
    simpa [Bundle.Trivialization.coe_symmₗ] using h
  rw [hsymm i, hsymm j]
  simp [manifoldMetricModelGramMatrix, manifoldTangentModelBasisVector]

/--
%%handwave
name:
  Inverse coordinate metric coefficients are continuous
statement:
  The inverse Gram coefficients of a smooth Riemannian metric in local tangent
  coordinates vary continuously at the base point.
proof:
  Matrix inversion is continuous near an invertible positive-definite Gram matrix; compose it with continuity of the coordinate Gram matrix and evaluate the chosen entry.
-/
theorem manifoldMetricCoordinateInverseGramCoeff_continuousAt {H X : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I : ModelWithCorners ℝ H H) [TopologicalSpace X] [ChartedSpace H X]
    [IsManifold I 1 X] [FiniteDimensional ℝ H]
    (g : SmoothRiemannianMetricOnManifold I X) (x₀ : X)
    (i j : Fin (Module.finrank ℝ H)) :
    ContinuousAt
      (fun y : X ↦
        (manifoldMetricCoordinateGramMatrix (I := I) (X := X) g x₀ y)⁻¹ i j)
      x₀ := by
  classical
  have hM :=
    manifoldMetricCoordinateGramMatrix_continuousAt
      (I := I) (X := X) g x₀
  have hdet_ne :
      (manifoldMetricCoordinateGramMatrix (I := I) (X := X) g x₀ x₀).det ≠ 0 := by
    rw [manifoldMetricCoordinateGramMatrix_self (I := I) (X := X) g x₀]
    exact ne_of_gt
      ((manifoldMetricModelGramMatrix_posDef (I := I) (X := X) g x₀).det_pos)
  have hinv :
      ContinuousAt
        (fun A : Matrix (Fin (Module.finrank ℝ H)) (Fin (Module.finrank ℝ H)) ℝ ↦ A⁻¹)
        (manifoldMetricCoordinateGramMatrix (I := I) (X := X) g x₀ x₀) := by
    exact continuousAt_matrix_inv
      (manifoldMetricCoordinateGramMatrix (I := I) (X := X) g x₀ x₀)
      (NormedRing.inverse_continuousAt
        (Units.mk0
          (manifoldMetricCoordinateGramMatrix (I := I) (X := X) g x₀ x₀).det
          hdet_ne))
  exact (continuous_apply_apply i j).continuousAt.comp (hinv.comp hM)

/--
%%handwave
name:
  Rank-one Hilbert-Schmidt model form
statement:
  Two model tangent vectors determine a continuous bilinear form on
  model differentials by evaluating the two differentials on those vectors and
  pairing the resulting target vectors.
-/
noncomputable def modelDifferentialEvalInnerCLM {H E : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v w : H) :
    (H →L[ℝ] E) →L[ℝ] (H →L[ℝ] E) →L[ℝ] ℝ := by
  let innerReal : E →L[ℝ] E →L[ℝ] ℝ :=
    LinearMap.mkContinuous₂ (innerₗ E) 1 fun u z ↦ by
      simpa [innerₗ_apply_apply] using (norm_inner_le_norm (𝕜 := ℝ) u z)
  let eval (u : H) : (H →L[ℝ] E) →L[ℝ] E :=
    ContinuousLinearMap.apply ℝ E u
  exact
    (ContinuousLinearMap.precomp (G := ℝ) (eval w)).comp
      (innerReal.comp (eval v))

/--
%%handwave
name:
  Rank-one model form evaluation
statement:
  The rank-one model Hilbert-Schmidt form evaluates by applying the two
  model differentials and taking the target inner product.
proof:
  Unfold the continuous bilinear map that pairs evaluations of two model differentials on fixed basis vectors.
-/
theorem modelDifferentialEvalInnerCLM_apply {H E : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v w : H) (A B : H →L[ℝ] E) :
    modelDifferentialEvalInnerCLM (E := E) v w A B =
      inner ℝ (A v) (B w) := by
  simp [modelDifferentialEvalInnerCLM, innerₗ_apply_apply]

set_option synthInstance.maxHeartbeats 80000 in
/--
%%handwave
name:
  Coordinate model Hilbert-Schmidt form
statement:
  In a tangent-coordinate trivialization, the Hilbert-Schmidt form is the
  finite contraction of the inverse coordinate metric coefficients with the
  target inner products of the coordinate components of the differentials.
-/
noncomputable def manifoldDifferentialHilbertSchmidtCoordinateModelCLM
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I : ModelWithCorners ℝ H H) [TopologicalSpace X] [ChartedSpace H X]
    [IsManifold I 1 X] [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : SmoothRiemannianMetricOnManifold I X) (x₀ y : X) :
    (H →L[ℝ] E) →L[ℝ] (H →L[ℝ] E) →L[ℝ] ℝ :=
  ∑ i : Fin (Module.finrank ℝ H), ∑ j : Fin (Module.finrank ℝ H),
    (manifoldMetricCoordinateGramMatrix (I := I) (X := X) g x₀ y)⁻¹ i j •
      modelDifferentialEvalInnerCLM
        (E := E) (Module.finBasis ℝ H i) (Module.finBasis ℝ H j)

/--
%%handwave
name:
  Coordinate model Hilbert-Schmidt form evaluation
statement:
  Evaluating the coordinate Hilbert-Schmidt form on two model differentials is
  the finite inverse-metric contraction of their coordinate values.
proof:
  Unfold the coordinate Hilbert--Schmidt form and distribute its finite sum of inverse metric coefficients times evaluation inner products.
-/
theorem manifoldDifferentialHilbertSchmidtCoordinateModelCLM_apply
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I : ModelWithCorners ℝ H H) [TopologicalSpace X] [ChartedSpace H X]
    [IsManifold I 1 X] [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : SmoothRiemannianMetricOnManifold I X) (x₀ y : X)
    (A B : H →L[ℝ] E) :
    manifoldDifferentialHilbertSchmidtCoordinateModelCLM
        (I := I) (X := X) (E := E) g x₀ y A B =
      ∑ i : Fin (Module.finrank ℝ H), ∑ j : Fin (Module.finrank ℝ H),
        (manifoldMetricCoordinateGramMatrix (I := I) (X := X) g x₀ y)⁻¹ i j *
          inner ℝ (A (Module.finBasis ℝ H i)) (B (Module.finBasis ℝ H j)) := by
  classical
  simp [manifoldDifferentialHilbertSchmidtCoordinateModelCLM,
    modelDifferentialEvalInnerCLM_apply]

/--
%%handwave
name:
  Coordinate model Hilbert-Schmidt forms vary continuously
statement:
  The coordinate model Hilbert-Schmidt form is continuous at the center of the
  trivialization.
proof:
  Every inverse Gram coefficient is continuous and every evaluation pairing is a fixed continuous bilinear form; finite sums and scalar products preserve continuity.
-/
theorem manifoldDifferentialHilbertSchmidtCoordinateModelCLM_continuousAt
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I : ModelWithCorners ℝ H H) [TopologicalSpace X] [ChartedSpace H X]
    [IsManifold I 1 X] [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : SmoothRiemannianMetricOnManifold I X) (x₀ : X) :
    ContinuousAt
      (fun y : X ↦
        manifoldDifferentialHilbertSchmidtCoordinateModelCLM
          (I := I) (X := X) (E := E) g x₀ y)
      x₀ := by
  classical
  let V := H →L[ℝ] E
  let hVAdd : AddCommGroup V :=
    ContinuousLinearMap.addCommGroup
      (R := ℝ) (R₂ := ℝ) (M := H) (M₂ := E)
      (σ₁₂ := RingHom.id ℝ)
  letI : AddCommGroup V := hVAdd
  letI : AddGroup V := AddCommGroup.toAddGroup
  letI : AddCommMonoid V := AddCommGroup.toAddCommMonoid
  let hVTop : IsTopologicalAddGroup V :=
    ContinuousLinearMap.topologicalAddGroup
      (𝕜₁ := ℝ) (𝕜₂ := ℝ) (σ := RingHom.id ℝ)
      (E := H) (F := E)
  letI : IsTopologicalAddGroup V := hVTop
  let D := V →L[ℝ] ℝ
  let hDAdd : AddCommGroup D :=
    ContinuousLinearMap.addCommGroup
      (R := ℝ) (R₂ := ℝ) (M := V) (M₂ := ℝ)
      (σ₁₂ := RingHom.id ℝ)
  letI : AddCommGroup D := hDAdd
  letI : AddGroup D := AddCommGroup.toAddGroup
  letI : AddCommMonoid D := AddCommGroup.toAddCommMonoid
  letI : AddMonoid D := AddCommMonoid.toAddMonoid
  let hDTop : IsTopologicalAddGroup D :=
    ContinuousLinearMap.topologicalAddGroup
      (𝕜₁ := ℝ) (𝕜₂ := ℝ) (σ := RingHom.id ℝ)
      (E := V) (F := ℝ)
  letI : IsTopologicalAddGroup D := hDTop
  letI : ContinuousAdd D := hDTop.toContinuousAdd
  let hOuterAdd : AddCommGroup (V →L[ℝ] D) :=
    ContinuousLinearMap.addCommGroup
      (R := ℝ) (R₂ := ℝ) (M := V) (M₂ := D)
      (σ₁₂ := RingHom.id ℝ)
  letI : AddCommGroup (V →L[ℝ] D) := hOuterAdd
  letI : AddGroup (V →L[ℝ] D) := AddCommGroup.toAddGroup
  letI : AddCommMonoid (V →L[ℝ] D) := AddCommGroup.toAddCommMonoid
  letI : AddMonoid (V →L[ℝ] D) := AddCommMonoid.toAddMonoid
  let hOuterTop : IsTopologicalAddGroup (V →L[ℝ] D) :=
    ContinuousLinearMap.topologicalAddGroup
      (𝕜₁ := ℝ) (𝕜₂ := ℝ) (σ := RingHom.id ℝ)
      (E := V) (F := D)
  letI : IsTopologicalAddGroup (V →L[ℝ] D) := hOuterTop
  letI : ContinuousAdd (V →L[ℝ] D) := hOuterTop.toContinuousAdd
  dsimp [manifoldDifferentialHilbertSchmidtCoordinateModelCLM]
  refine tendsto_finsetSum _ ?_
  intro i _
  refine tendsto_finsetSum _ ?_
  intro j _
  exact
    (manifoldMetricCoordinateInverseGramCoeff_continuousAt
      (I := I) (X := X) g x₀ i j).smul continuousAt_const

/--
Turn a continuous bilinear map into the corresponding algebraic bilinear map.
This is useful for applying matrix lemmas about bilinear forms.
-/
def continuousBilinearMap_toLinearMap₂ {V W G : Type}
    [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace W] [AddCommGroup W] [Module ℝ W]
    [TopologicalSpace G] [AddCommGroup G] [Module ℝ G]
    [IsTopologicalAddGroup G] [ContinuousConstSMul ℝ G]
    (B : V →L[ℝ] W →L[ℝ] G) : V →ₗ[ℝ] W →ₗ[ℝ] G where
  toFun v := (B v).toLinearMap
  map_add' v w := by
    ext z
    simp
  map_smul' c v := by
    ext z
    simp

/--
%%handwave
name:
  Evaluation of the algebraic form of a continuous bilinear map
statement:
  Viewing a continuous bilinear map \(B:V\times W\to G\) as an algebraic bilinear map does not change its values: the resulting map sends \((v,w)\) to \(B(v,w)\).
proof:
  The conversion only forgets continuity and retains the same underlying functions.
-/
@[simp]
theorem continuousBilinearMap_toLinearMap₂_apply {V W G : Type}
    [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace W] [AddCommGroup W] [Module ℝ W]
    [TopologicalSpace G] [AddCommGroup G] [Module ℝ G]
    [IsTopologicalAddGroup G] [ContinuousConstSMul ℝ G]
    (B : V →L[ℝ] W →L[ℝ] G) (v : V) (w : W) :
    continuousBilinearMap_toLinearMap₂ B v w = B v w :=
  rfl

/--
%%handwave
name:
  Transported model differential
statement:
  In the local trivialization of the differential bundle, transporting a model
  differential back to the fiber composes it with the tangent-coordinate map.
proof:
  The inverse bundle trivialization transports a model differential to the fiber by precomposing it with the chart tangent-coordinate map.
-/
theorem manifoldDifferentialBundle_trivialization_symm_apply
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I : ModelWithCorners ℝ H H) [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold I 1 X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x₀ y : X)
    (hy : y ∈
      (trivializationAt (H →L[ℝ] E)
        (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E)) x₀).baseSet)
    (A : H →L[ℝ] E) :
    ((trivializationAt (H →L[ℝ] E)
      (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E)) x₀).symm y A) =
      A.comp
        ((trivializationAt H (TangentSpace I : X → Type) x₀).continuousLinearMapAt ℝ y) := by
  let eT := trivializationAt H (TangentSpace I : X → Type) x₀
  let eE := trivializationAt E (Bundle.Trivial X E) x₀
  have hyTE : y ∈ eT.baseSet ∩ eE.baseSet := by
    simpa [eT, eE, ManifoldDifferentialBundleFiber, hom_trivializationAt_baseSet] using hy
  rw [hom_trivializationAt]
  change
    (Bundle.Pretrivialization.continuousLinearMap (RingHom.id ℝ) eT eE).symm y A =
      A.comp (eT.continuousLinearMapAt ℝ y)
  rw [Bundle.Pretrivialization.continuousLinearMap_symm_apply'
    (σ := RingHom.id ℝ) (e₁ := eT) (e₂ := eE)
    hyTE A]
  ext v
  simp [eE]

/--
%%handwave
name:
  Expansion of target inner products after a linear coordinate change
statement:
  If two model vectors are expanded in a basis using the columns of a matrix,
  then the inner product of their images under two linear maps expands as the
  corresponding double sum of matrix coefficients and target inner products.
proof:
  Expand each vector in the finite basis, use bilinearity of the inner product, and interchange the resulting finite sums.
-/
theorem inner_apply_basis_matrix_sum {ι H E : Type} [Fintype ι]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : Module.Basis ι ℝ H) (A B : H →L[ℝ] E)
    (P : Matrix ι ι ℝ) (i j : ι) :
    inner ℝ (A (∑ a : ι, P a i • b a))
        (B (∑ b' : ι, P b' j • b b')) =
      ∑ a : ι, ∑ b' : ι,
        P a i * P b' j * inner ℝ (A (b a)) (B (b b')) := by
  rw [map_sum, map_sum, inner_sum]
  simp only [sum_inner, ContinuousLinearMap.map_smul, real_inner_smul_left,
    real_inner_smul_right]
  rw [Finset.sum_comm]
  simp [mul_assoc, mul_left_comm]

/--
%%handwave
name:
  Double contraction after a coordinate change
statement:
  Expanding both arguments of a bilinear coefficient matrix through a change
  of coordinates transforms the coefficient matrix by \(P C P^T\).
proof:
  Expand the two matrix products and the double contraction, then rearrange the finite sums and scalar factors.
-/
theorem matrix_double_contraction_mul_transpose {ι : Type} [Fintype ι]
    (P C K : Matrix ι ι ℝ) :
    (∑ i : ι, ∑ j : ι,
        C i j * (∑ a : ι, ∑ b : ι, P a i * P b j * K a b)) =
      ∑ a : ι, ∑ b : ι, (P * C * P.transpose) a b * K a b := by
  classical
  calc
    (∑ i : ι, ∑ j : ι,
        C i j * (∑ a : ι, ∑ b : ι, P a i * P b j * K a b)) =
        ∑ p : (ι × ι) × (ι × ι),
          C p.1.1 p.1.2 * P p.2.1 p.1.1 * P p.2.2 p.1.2 *
            K p.2.1 p.2.2 := by
      simp [Fintype.sum_prod_type, Finset.mul_sum, mul_left_comm, mul_comm]
    _ = ∑ q : (ι × ι) × (ι × ι),
          P q.1.1 q.2.2 * C q.2.2 q.2.1 * P q.1.2 q.2.1 *
            K q.1.1 q.1.2 := by
      let e : (ι × ι) × (ι × ι) ≃ (ι × ι) × (ι × ι) :=
        { toFun := fun p ↦ ((p.2.1, p.2.2), (p.1.2, p.1.1))
          invFun := fun p ↦ ((p.2.2, p.2.1), (p.1.1, p.1.2))
          left_inv := by rintro ⟨⟨i, j⟩, ⟨a, b⟩⟩; rfl
          right_inv := by rintro ⟨⟨a, b⟩, ⟨j, i⟩⟩; rfl }
      refine Fintype.sum_equiv e _ _ ?_
      rintro ⟨⟨i, j⟩, ⟨a, b⟩⟩
      simp [e]
      ring_nf
      exact Or.inl (Or.inl trivial)
    _ = ∑ a : ι, ∑ b : ι, (P * C * P.transpose) a b * K a b := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_prod_type,
        Finset.sum_mul]

/--
%%handwave
name:
  Inverse of a Gram matrix after a coordinate change
statement:
  If \(Q\) and \(P\) are inverse change-of-basis matrices, then the inverse
  of \(Q^T G Q\) is \(P G^{-1} P^T\).
proof:
  Use the inverse identities and transpose/conjugate rules for real matrices to simplify the product to the identity matrix.
-/
theorem matrix_inv_transpose_mul_conj {ι : Type} [Fintype ι] [DecidableEq ι]
    (P Q G : Matrix ι ι ℝ) (hQP : Q * P = 1) :
    (Q.transpose * G * Q)⁻¹ = P * G⁻¹ * P.transpose := by
  have hQinv : Q⁻¹ = P := Matrix.inv_eq_right_inv hQP
  have hQTinv : Q.transpose⁻¹ = P.transpose := by
    rw [← Matrix.transpose_nonsing_inv Q, hQinv]
  calc
    (Q.transpose * G * Q)⁻¹ = Q⁻¹ * (Q.transpose * G)⁻¹ := by
      rw [Matrix.mul_inv_rev]
    _ = Q⁻¹ * (G⁻¹ * Q.transpose⁻¹) := by
      rw [Matrix.mul_inv_rev]
    _ = P * (G⁻¹ * P.transpose) := by
      rw [hQinv, hQTinv]
    _ = P * G⁻¹ * P.transpose := by
      rw [Matrix.mul_assoc]

/--
%%handwave
name:
  Inverse coordinate metric under tangent-coordinate transport
statement:
  In a tangent-bundle trivialization, the inverse coordinate Gram matrix is
  obtained from the inverse fiber Gram matrix by contravariant conjugation with
  the tangent-coordinate map.
proof:
  The coordinate Gram matrix is the Gram matrix of the transported basis
  \(Qe_i\), hence is \(Q^T G Q\).  The matrix of the tangent-coordinate map is
  inverse to the matrix \(Q\) of the inverse transport, so the preceding matrix
  identity gives the formula for the inverse Gram matrix.
-/
theorem manifoldMetricCoordinateInverseGramMatrix_eq_conj
    {H X : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I : ModelWithCorners ℝ H H) [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold I 1 X]
    [FiniteDimensional ℝ H]
    (g : SmoothRiemannianMetricOnManifold I X) (x₀ y : X)
    (hyT : y ∈ (trivializationAt H (TangentSpace I : X → Type) x₀).baseSet) :
    (manifoldMetricCoordinateGramMatrix (I := I) (X := X) g x₀ y)⁻¹ =
      (LinearMap.toMatrix
        (show Module.Basis (Fin (Module.finrank ℝ H)) ℝ (TangentSpace I y) from
          Module.finBasis ℝ H)
        (Module.finBasis ℝ H)
        ((trivializationAt H (TangentSpace I : X → Type) x₀).continuousLinearMapAt
          ℝ y).toLinearMap) *
        (manifoldMetricModelGramMatrix (I := I) (X := X) g y)⁻¹ *
        (LinearMap.toMatrix
          (show Module.Basis (Fin (Module.finrank ℝ H)) ℝ (TangentSpace I y) from
            Module.finBasis ℝ H)
          (Module.finBasis ℝ H)
          ((trivializationAt H (TangentSpace I : X → Type) x₀).continuousLinearMapAt
            ℝ y).toLinearMap).transpose := by
  let eT := trivializationAt H (TangentSpace I : X → Type) x₀
  let bT : Module.Basis (Fin (Module.finrank ℝ H)) ℝ (TangentSpace I y) :=
    Module.finBasis ℝ H
  let bH : Module.Basis (Fin (Module.finrank ℝ H)) ℝ H := Module.finBasis ℝ H
  let L : TangentSpace I y →L[ℝ] H := eT.continuousLinearMapAt ℝ y
  let S : H →L[ℝ] TangentSpace I y := eT.symmL ℝ y
  let P : Matrix (Fin (Module.finrank ℝ H)) (Fin (Module.finrank ℝ H)) ℝ :=
    LinearMap.toMatrix bT bH L.toLinearMap
  let Q : Matrix (Fin (Module.finrank ℝ H)) (Fin (Module.finrank ℝ H)) ℝ :=
    LinearMap.toMatrix bH bT S.toLinearMap
  let beta : TangentSpace I y →ₗ[ℝ] TangentSpace I y →ₗ[ℝ] ℝ :=
    continuousBilinearMap_toLinearMap₂ (g.toContMDiffRiemannianMetric.inner y)
  have hcoord0 :
      manifoldMetricCoordinateGramMatrix (I := I) (X := X) g x₀ y =
        LinearMap.toMatrix₂ bH bH (beta.compl₁₂ S.toLinearMap S.toLinearMap) := by
    ext i j
    rw [manifoldMetricCoordinateGramMatrix]
    rw [inCoordinates_apply_eq₂ hyT hyT (by simp)]
    simp [beta, S, eT, bH, Bundle.Trivialization.symmL_apply]
  have hG :
      LinearMap.toMatrix₂ bT bT beta =
        manifoldMetricModelGramMatrix (I := I) (X := X) g y := by
    ext i j
    simp [beta, manifoldMetricModelGramMatrix, manifoldTangentModelBasisVector, bT]
    rfl
  have hcoord :
      manifoldMetricCoordinateGramMatrix (I := I) (X := X) g x₀ y =
        Q.transpose * manifoldMetricModelGramMatrix (I := I) (X := X) g y * Q := by
    rw [hcoord0]
    rw [LinearMap.toMatrix₂_compl₁₂ bT bT bH bH]
    rw [hG]
  have hcomp : S.toLinearMap.comp L.toLinearMap = LinearMap.id := by
    ext v
    exact eT.symmL_continuousLinearMapAt (R := ℝ) hyT v
  have hQP : Q * P = 1 := by
    rw [← LinearMap.toMatrix_comp bT bH bT S.toLinearMap L.toLinearMap]
    simp [hcomp]
  rw [hcoord]
  exact matrix_inv_transpose_mul_conj P Q
    (manifoldMetricModelGramMatrix (I := I) (X := X) g y) hQP

/--
%%handwave
name:
  Hilbert-Schmidt contraction is invariant under tangent-coordinate change
statement:
  On the base set of a tangent trivialization, the Hilbert-Schmidt contraction
  computed in the transported model coordinates agrees with the same
  contraction computed in the original fiber coordinates.
proof:
  This is the finite-dimensional change-of-basis formula for the inverse Gram
  matrix.  If \(L:T_yX\to H\) is the tangent-coordinate map, the coordinate Gram
  matrix is the Gram matrix of the transported basis \(L^{-1}e_i\), while the
  transported differential evaluates a vector \(v\in T_yX\) as \(A(Lv)\).
  The inverse Gram tensor transforms contravariantly, so the double
  contraction is unchanged.
-/
theorem manifoldDifferentialHilbertSchmidt_coordinate_change_sum
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I : ModelWithCorners ℝ H H) [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold I 1 X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : SmoothRiemannianMetricOnManifold I X) (x₀ y : X)
    (hy : y ∈
      (trivializationAt (H →L[ℝ] E)
        (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E)) x₀).baseSet)
    (A B : H →L[ℝ] E) :
    (∑ i : Fin (Module.finrank ℝ H), ∑ j : Fin (Module.finrank ℝ H),
        manifoldMetricInverseGramCoeffAt (I := I) (X := X) g y i j *
          inner ℝ
            (((trivializationAt (H →L[ℝ] E)
              (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E)) x₀).symm y A)
                (manifoldTangentModelBasisVector (I := I) (X := X) y i))
            (((trivializationAt (H →L[ℝ] E)
              (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E)) x₀).symm y B)
                (manifoldTangentModelBasisVector (I := I) (X := X) y j))) =
      ∑ i : Fin (Module.finrank ℝ H), ∑ j : Fin (Module.finrank ℝ H),
        (manifoldMetricCoordinateGramMatrix (I := I) (X := X) g x₀ y)⁻¹ i j *
          inner ℝ (A (Module.finBasis ℝ H i)) (B (Module.finBasis ℝ H j)) := by
  classical
  let eT := trivializationAt H (TangentSpace I : X → Type) x₀
  let eE := trivializationAt E (Bundle.Trivial X E) x₀
  have hyTE : y ∈ eT.baseSet ∩ eE.baseSet := by
    simpa [eT, eE, ManifoldDifferentialBundleFiber, hom_trivializationAt_baseSet] using hy
  have hyT : y ∈ eT.baseSet := hyTE.1
  let ι := Fin (Module.finrank ℝ H)
  let bT : Module.Basis ι ℝ (TangentSpace I y) := Module.finBasis ℝ H
  let bH : Module.Basis ι ℝ H := Module.finBasis ℝ H
  let L : TangentSpace I y →L[ℝ] H := eT.continuousLinearMapAt ℝ y
  let P : Matrix ι ι ℝ := LinearMap.toMatrix bT bH L.toLinearMap
  let C : Matrix ι ι ℝ := (manifoldMetricModelGramMatrix (I := I) (X := X) g y)⁻¹
  let K : Matrix ι ι ℝ := fun a b ↦ inner ℝ (A (bH a)) (B (bH b))
  have hP_basis : P = bH.toMatrix (fun k : ι ↦ L (bT k)) := by
    ext a k
    simp [P, Module.Basis.toMatrix_apply, LinearMap.toMatrix_apply]
  have hL_expand (i : ι) : L (bT i) = ∑ a : ι, P a i • bH a := by
    rw [hP_basis]
    exact (bH.sum_toMatrix_smul_self (fun k : ι ↦ L (bT k)) i).symm
  calc
    (∑ i : Fin (Module.finrank ℝ H), ∑ j : Fin (Module.finrank ℝ H),
        manifoldMetricInverseGramCoeffAt (I := I) (X := X) g y i j *
          inner ℝ
            (((trivializationAt (H →L[ℝ] E)
              (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E)) x₀).symm y A)
                (manifoldTangentModelBasisVector (I := I) (X := X) y i))
            (((trivializationAt (H →L[ℝ] E)
              (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E)) x₀).symm y B)
                (manifoldTangentModelBasisVector (I := I) (X := X) y j)))
        = ∑ i : ι, ∑ j : ι, C i j * inner ℝ (A (L (bT i))) (B (L (bT j))) := by
      simp_rw [manifoldDifferentialBundle_trivialization_symm_apply
        (I := I) (X := X) (E := E) x₀ y hy A,
        manifoldDifferentialBundle_trivialization_symm_apply
        (I := I) (X := X) (E := E) x₀ y hy B]
      simp [C, L, eT, bT, manifoldMetricInverseGramCoeffAt,
        manifoldTangentModelBasisVector]
      rfl
    _ = ∑ i : ι, ∑ j : ι,
          C i j * (∑ a : ι, ∑ b : ι, P a i * P b j * K a b) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro j _
      congr 1
      rw [hL_expand i, hL_expand j]
      exact inner_apply_basis_matrix_sum bH A B P i j
    _ = ∑ a : ι, ∑ b : ι, (P * C * P.transpose) a b * K a b := by
      exact matrix_double_contraction_mul_transpose P C K
    _ = ∑ a : ι, ∑ b : ι,
          (manifoldMetricCoordinateGramMatrix (I := I) (X := X) g x₀ y)⁻¹ a b * K a b := by
      have hInv := manifoldMetricCoordinateInverseGramMatrix_eq_conj
        (I := I) (X := X) g x₀ y hyT
      dsimp [P, C] at hInv
      rw [← hInv]
    _ = ∑ i : Fin (Module.finrank ℝ H), ∑ j : Fin (Module.finrank ℝ H),
        (manifoldMetricCoordinateGramMatrix (I := I) (X := X) g x₀ y)⁻¹ i j *
          inner ℝ (A (Module.finBasis ℝ H i)) (B (Module.finBasis ℝ H j)) := by
      simp [K, bH]
      rfl

/--
%%handwave
name:
  Local Hilbert-Schmidt form equals the coordinate contraction
statement:
  On the base set of a differential-bundle trivialization, the local
  coordinate expression of the Hilbert-Schmidt metric is the coordinate
  inverse-metric contraction.
proof:
  The differential-bundle trivialization precomposes model differentials with
  the tangent-coordinate map.  The inverse Gram matrix transforms
  contravariantly under this tangent-coordinate change, so the contraction in
  the original fiber basis is exactly the contraction in the coordinate basis.
-/
theorem manifoldDifferentialHilbertSchmidtInnerCLMAt_inCoordinates_eq_coordinateModel
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I : ModelWithCorners ℝ H H) [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold I 1 X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : SmoothRiemannianMetricOnManifold I X) (x₀ y : X)
    (hy : y ∈
      (trivializationAt (H →L[ℝ] E)
        (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E)) x₀).baseSet) :
    ContinuousLinearMap.inCoordinates (H →L[ℝ] E)
        (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E))
        ((H →L[ℝ] E) →L[ℝ] ℝ)
        (fun x : X ↦
          ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E) x →L[ℝ]
            Bundle.Trivial X ℝ x)
        x₀ y x₀ y
        (manifoldDifferentialHilbertSchmidtInnerCLMAt
          (I := I) (X := X) (E := E) g y) =
      manifoldDifferentialHilbertSchmidtCoordinateModelCLM
        (I := I) (X := X) (E := E) g x₀ y := by
  ext A B
  rw [manifoldDifferentialHilbertSchmidtInnerCLMAt_inCoordinates_apply_eq_sum
    (I := I) (X := X) (E := E) g x₀ y hy A B]
  rw [manifoldDifferentialHilbertSchmidtCoordinateModelCLM_apply
    (I := I) (X := X) (E := E) g x₀ y A B]
  exact
    manifoldDifferentialHilbertSchmidt_coordinate_change_sum
      (I := I) (X := X) (E := E) g x₀ y hy A B

/--
%%handwave
name:
  Local coordinate continuity of the Hilbert-Schmidt bundle metric
statement:
  In every local trivialization of the differential bundle, the
  Hilbert-Schmidt metric is a continuous family of model bilinear forms.
proof:
  After evaluating on model differentials \(A\) and \(B\), the coordinate
  expression is a finite sum of inverse Riemannian metric coefficients times
  target inner products of the locally transported differentials.  The inverse
  coefficients are continuous because the base metric is smooth and matrix
  inversion is continuous on invertible matrices; the transported
  differentials vary continuously by the Hom-bundle trivialization.
-/
theorem manifoldDifferentialHilbertSchmidtInnerCLMAt_inCoordinates_continuousAt
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I : ModelWithCorners ℝ H H) [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold I 1 X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : SmoothRiemannianMetricOnManifold I X) (x₀ : X) :
    ContinuousAt
      (fun y : X ↦
        ContinuousLinearMap.inCoordinates (H →L[ℝ] E)
          (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E))
          ((H →L[ℝ] E) →L[ℝ] ℝ)
          (fun x : X ↦
            ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E) x →L[ℝ]
              Bundle.Trivial X ℝ x)
          x₀ y x₀ y
          (manifoldDifferentialHilbertSchmidtInnerCLMAt
            (I := I) (X := X) (E := E) g y))
      x₀ := by
  have hmodel :
      ContinuousAt
        (fun y : X ↦
          manifoldDifferentialHilbertSchmidtCoordinateModelCLM
            (I := I) (X := X) (E := E) g x₀ y)
        x₀ :=
    manifoldDifferentialHilbertSchmidtCoordinateModelCLM_continuousAt
      (I := I) (X := X) (E := E) g x₀
  refine hmodel.congr_of_eventuallyEq ?_
  have hbase :
      x₀ ∈
        (trivializationAt (H →L[ℝ] E)
          (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E)) x₀).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x₀
  filter_upwards [
    (trivializationAt (H →L[ℝ] E)
      (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E)) x₀).open_baseSet.mem_nhds
      hbase] with y hy
  exact
    manifoldDifferentialHilbertSchmidtInnerCLMAt_inCoordinates_eq_coordinateModel
      (I := I) (X := X) (E := E) g x₀ y hy

/--
%%handwave
name:
  Hilbert geometry on the differential bundle
statement:
  A Riemannian metric on the surface and a Hilbert inner product on the target
  make the vector-valued differential bundle into a fiberwise Hilbert bundle,
  with the Hilbert-Schmidt inner product on each fiber.
-/
noncomputable def surfaceDifferentialHilbertBundleGeometry {X E : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [IsManifold SurfaceRealModel 1 X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : SmoothRiemannianMetricOnSurface X) :
    HilbertBundleGeometryOnSurface X (ℂ →L[ℝ] E)
      (SurfaceDifferentialBundleFiber (X := X) (E := E)) where
  fiberInner := fun x A B ↦
    surfaceDifferentialHilbertSchmidtInnerAt g x A B
  fiberNormSq := fun x A ↦
    surfaceDifferentialHilbertSchmidtNormSqAt g x A
  fiberNormSq_eq_inner := by
    intro _ _
    rfl

set_option synthInstance.maxHeartbeats 80000 in
/--
%%handwave
name:
  Hilbert-Schmidt geometry on a differential bundle over a manifold
statement:
  On a finite-dimensional Riemannian manifold, a Riemannian metric on the
  tangent bundle and a real Hilbert structure on the target induce a continuous
  Hilbert-Schmidt Riemannian metric on the bundle \(T^\ast X\otimes E\).
proof:
  In local trivializations this is the tensor product of the dual Riemannian
  metric with the target Hilbert inner product.  Finite-dimensionality of the
  tangent model ensures that every continuous linear map \(T_xX\to E\) is
  Hilbert-Schmidt, and smoothness of the base metric gives continuity of the
  induced bundle metric.
-/
noncomputable def manifoldDifferentialHilbertSchmidtContinuousRiemannianMetric
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I : ModelWithCorners ℝ H H) [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold I 1 X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : SmoothRiemannianMetricOnManifold I X) :
    Bundle.ContinuousRiemannianMetric (H →L[ℝ] E)
      (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E)) where
  inner := manifoldDifferentialHilbertSchmidtInnerCLMAt (I := I) (X := X) g
  symm := by
    intro x A B
    exact manifoldDifferentialHilbertSchmidtInnerCLMAt_symm
      (I := I) (X := X) g x A B
  pos := by
    intro x A hA
    rw [manifoldDifferentialHilbertSchmidtInnerCLMAt_apply]
    exact manifoldDifferentialHilbertSchmidtInnerAt_pos
      (I := I) (X := X) g x A hA
  isVonNBounded := by
    intro x
    exact manifoldDifferentialHilbertSchmidtInnerCLMAt_isVonNBounded
      (I := I) (X := X) (E := E) g x
  continuous := by
    rw [continuous_iff_continuousAt]
    intro x₀
    rw [continuousAt_hom_bundle]
    exact ⟨continuousAt_id,
      manifoldDifferentialHilbertSchmidtInnerCLMAt_inCoordinates_continuousAt
        (I := I) (X := X) (E := E) g x₀⟩

@[reducible]
noncomputable def manifoldDifferentialHilbertSchmidtNormedAddCommGroup
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I : ModelWithCorners ℝ H H) [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold I 1 X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (metric : Bundle.ContinuousRiemannianMetric (H →L[ℝ] E)
      (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E)))
    (x : X) :
    NormedAddCommGroup (ManifoldDifferentialBundleFiber
      (I := I) (X := X) (E := E) x) :=
  (metric.toRiemannianMetric.toCore x).toNormedAddCommGroupOfTopology
    (metric.toRiemannianMetric.continuousAt x)
    (metric.toRiemannianMetric.isVonNBounded x)

@[reducible]
noncomputable def manifoldDifferentialHilbertSchmidtInnerProductSpace
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I : ModelWithCorners ℝ H H) [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold I 1 X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (metric : Bundle.ContinuousRiemannianMetric (H →L[ℝ] E)
      (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E)))
    (x : X) :
    letI : NormedAddCommGroup
        (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E) x) :=
      manifoldDifferentialHilbertSchmidtNormedAddCommGroup
        (I := I) (X := X) (E := E) metric x
    InnerProductSpace ℝ
      (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E) x) :=
  letI : NormedAddCommGroup
      (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E) x) :=
    manifoldDifferentialHilbertSchmidtNormedAddCommGroup
      (I := I) (X := X) (E := E) metric x
  InnerProductSpace.ofCoreOfTopology
    (metric.toRiemannianMetric.toCore x)
    (metric.toRiemannianMetric.continuousAt x)
    (metric.toRiemannianMetric.isVonNBounded x)

/--
%%handwave
name:
  Differential fibers over a manifold are complete for the registered norm
statement:
  If the Hilbert target is complete, then the fibers of \(T^\ast X\otimes E\),
  equipped with the metric Hilbert-Schmidt norm, are complete metric vector
  spaces.
proof:
  The registered fiberwise Hilbert norm induces the same uniform structure as
  the continuous-linear-map topology on each fiber, and continuous linear maps
  into a complete normed space form a complete space.
-/
theorem manifoldDifferentialHilbertSchmidt_completeSpace_of_inner
    {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I : ModelWithCorners ℝ H H) [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold I 1 X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (metric : Bundle.ContinuousRiemannianMetric (H →L[ℝ] E)
      (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E))) :
    ∀ x : X,
      letI : NormedAddCommGroup
          (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E) x) :=
        manifoldDifferentialHilbertSchmidtNormedAddCommGroup
          (I := I) (X := X) (E := E) metric x
      CompleteSpace
        (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E) x) := by
  intro x
  letI : NormedAddCommGroup
      (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E) x) :=
    manifoldDifferentialHilbertSchmidtNormedAddCommGroup
      (I := I) (X := X) (E := E) metric x
  change CompleteSpace (H →L[ℝ] E)
  infer_instance

/--
%%handwave
name:
  Hilbert geometry on the differential bundle is continuous
statement:
  The Riemannian metric on a real surface and the Hilbert structure on the
  target induce a continuous Riemannian metric on the bundle
  \(T^\ast X\otimes E\).
proof:
  This is the specialization of the finite-dimensional manifold
  Hilbert-Schmidt metric to the real two-dimensional model.
-/
noncomputable def surfaceDifferentialHilbertSchmidtContinuousRiemannianMetric {X E : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [IsManifold SurfaceRealModel 1 X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : SmoothRiemannianMetricOnSurface X) :
    Bundle.ContinuousRiemannianMetric (ℂ →L[ℝ] E)
      (SurfaceDifferentialBundleFiber (X := X) (E := E)) :=
  manifoldDifferentialHilbertSchmidtContinuousRiemannianMetric
    (I := SurfaceRealModel) (X := X) (E := E) g.toManifoldMetric

/--
%%handwave
name:
  Hilbert-Schmidt fiber pairing is the induced inner product
statement:
  After registering the canonical Hilbert-Schmidt Riemannian metric on
  \(T^\ast X\otimes E\), the fiberwise inner product is exactly the metric
  Hilbert-Schmidt pairing.
proof:
  In the preferred complex tangent basis, the surface Hilbert--Schmidt contraction is exactly the declared inner product on the two coordinate components.
-/
theorem surfaceDifferentialHilbertSchmidtInnerAt_eq_inner {X E : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [IsManifold SurfaceRealModel 1 X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : SmoothRiemannianMetricOnSurface X) (x : X)
    (A B : SurfaceDifferentialBundleFiber (X := X) (E := E) x) :
    letI : Bundle.RiemannianBundle
        (SurfaceDifferentialBundleFiber (X := X) (E := E)) :=
      ⟨(surfaceDifferentialHilbertSchmidtContinuousRiemannianMetric
        (X := X) (E := E) g).toRiemannianMetric⟩
    manifoldDifferentialHilbertSchmidtInnerAt
      (I := SurfaceRealModel) (X := X) g.toManifoldMetric x A B =
        inner ℝ A B := by
  letI : Bundle.RiemannianBundle
      (SurfaceDifferentialBundleFiber (X := X) (E := E)) :=
    ⟨(surfaceDifferentialHilbertSchmidtContinuousRiemannianMetric
      (X := X) (E := E) g).toRiemannianMetric⟩
  rw [← manifoldDifferentialHilbertSchmidtInnerCLMAt_apply
    (I := SurfaceRealModel) (X := X) (E := E) g.toManifoldMetric x A B]
  rfl

/--
%%handwave
name:
  Hilbert-Schmidt differential fibers are complete for the registered norm
statement:
  If the target Hilbert space is complete, then every fiber of
  \(T^\ast X\otimes E\), equipped with the supplied metric Hilbert-Schmidt
  norm, is a complete metric vector space.
proof:
  The tangent plane is finite-dimensional, so the Hilbert-Schmidt norm is
  equivalent to any fixed operator norm on the continuous linear maps into the
  complete target.
-/
theorem surfaceDifferentialHilbertSchmidt_completeSpace_of_inner {X E : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [IsManifold SurfaceRealModel 1 X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (g : SmoothRiemannianMetricOnSurface X) :
    letI : Bundle.RiemannianBundle
        (SurfaceDifferentialBundleFiber (X := X) (E := E)) :=
      ⟨(surfaceDifferentialHilbertSchmidtContinuousRiemannianMetric
        (X := X) (E := E) g).toRiemannianMetric⟩
    ∀ x : X,
      @CompleteSpace (SurfaceDifferentialBundleFiber (X := X) (E := E) x)
        PseudoMetricSpace.toUniformSpace := by
  letI : Bundle.RiemannianBundle
      (SurfaceDifferentialBundleFiber (X := X) (E := E)) :=
    ⟨(surfaceDifferentialHilbertSchmidtContinuousRiemannianMetric
      (X := X) (E := E) g).toRiemannianMetric⟩
  intro x
  change @CompleteSpace (SurfaceDifferentialBundleFiber (X := X) (E := E) x)
    PseudoMetricSpace.toUniformSpace
  let U0 : UniformSpace (SurfaceDifferentialBundleFiber (X := X) (E := E) x) :=
    ContinuousLinearMap.uniformSpace
      (𝕜₁ := ℝ) (𝕜₂ := ℝ) (σ := RingHom.id ℝ)
      (E := TangentSpace SurfaceRealModel x) (F := E)
  have hU : PseudoMetricSpace.toUniformSpace = U0 := by
    apply UniformSpace.ext
    rw [@uniformity_eq_comap_nhds_zero
      (SurfaceDifferentialBundleFiber (X := X) (E := E) x)
      PseudoMetricSpace.toUniformSpace inferInstance inferInstance]
    letI : UniformSpace (SurfaceDifferentialBundleFiber (X := X) (E := E) x) := U0
    rw [@uniformity_eq_comap_nhds_zero
      (SurfaceDifferentialBundleFiber (X := X) (E := E) x)
      U0 inferInstance inferInstance]
  rw [hU]
  change CompleteSpace (ℂ →L[ℝ] E)
  infer_instance

/--
%%handwave
name:
  Hilbert geometry from a supplied differential-bundle metric
statement:
  A continuous Hilbert metric on \(T^\ast X\otimes E\) determines the
  fiberwise inner product and square norm used to define its \(L^2\)-sections.
-/
noncomputable def manifoldDifferentialHilbertBundleGeometryOfMetric {H X E : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I : ModelWithCorners ℝ H H) [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold I 1 X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (metric : Bundle.ContinuousRiemannianMetric (H →L[ℝ] E)
      (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E))) :
    HilbertBundleGeometry X (H →L[ℝ] E)
      (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E)) where
  fiberInner := fun x A B ↦ metric.inner x A B
  fiberNormSq := fun x A ↦ metric.inner x A A
  fiberNormSq_eq_inner := by
    intro _ _
    rfl

/--
%%handwave
name:
  Hilbert geometry on the differential bundle over a manifold
statement:
  A finite-dimensional Riemannian manifold and a Hilbert target make
  \(T^\ast X\otimes E\) into a fiberwise Hilbert bundle with the
  Hilbert-Schmidt inner product.
-/
noncomputable def manifoldDifferentialHilbertBundleGeometry {H X E : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I : ModelWithCorners ℝ H H) [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold I 1 X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : SmoothRiemannianMetricOnManifold I X) :
    HilbertBundleGeometry X (H →L[ℝ] E)
      (ManifoldDifferentialBundleFiber (I := I) (X := X) (E := E)) :=
  manifoldDifferentialHilbertBundleGeometryOfMetric
    (I := I) (X := X) (E := E)
    (manifoldDifferentialHilbertSchmidtContinuousRiemannianMetric
      (I := I) (X := X) (E := E) g)

/--
%%handwave
name:
  Intrinsic square-integrability of a manifold differential field
statement:
  A vector-valued differential field on a Riemannian manifold is
  square-integrable when it is a measurable section of \(T^\ast X\otimes E\)
  and its Hilbert-Schmidt square norm is integrable.
-/
def ManifoldDifferentialFieldMemHilbertSchmidtL2 {H X E : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I : ModelWithCorners ℝ H H) [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold I 1 X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : SmoothRiemannianMetricOnManifold I X) (μ : Measure X)
    (du : ManifoldDifferentialField I X E) : Prop :=
  HilbertBundleSectionMemL2
    (manifoldDifferentialHilbertBundleGeometry (I := I) (X := X) (E := E) g) μ du

/--
%%handwave
name:
  \(L^2\)-sections of the differential bundle over a manifold
statement:
  The \(L^2\)-sections of \(T^\ast X\otimes E\) over a finite-dimensional
  Riemannian manifold are square-integrable differential representatives
  modulo almost-everywhere equality.
-/
abbrev ManifoldDifferentialL2Section {H X E : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I : ModelWithCorners ℝ H H) [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold I 1 X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : SmoothRiemannianMetricOnManifold I X) (μ : Measure X) : Type :=
  L2HilbertBundle
    (manifoldDifferentialHilbertBundleGeometry (I := I) (X := X) (E := E) g) μ

/--
%%handwave
name:
  Square-integrable differential representative on a manifold
statement:
  A square-integrable differential representative is a measurable section of
  \(T^\ast X\otimes E\) with finite metric Hilbert-Schmidt energy.
-/
abbrev SquareIntegrableManifoldDifferentialField {H X E : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I : ModelWithCorners ℝ H H) [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold I 1 X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : SmoothRiemannianMetricOnManifold I X) (μ : Measure X) : Type :=
  SquareIntegrableHilbertBundleSection
    (manifoldDifferentialHilbertBundleGeometry (I := I) (X := X) (E := E) g) μ

namespace SquareIntegrableManifoldDifferentialField

variable {H X E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold I 1 X]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {g : SmoothRiemannianMetricOnManifold I X} {μ : Measure X}

/-- The underlying differential field. -/
abbrev toField
    (du : SquareIntegrableManifoldDifferentialField (I := I) (X := X) (E := E) g μ) :
    ManifoldDifferentialField I X E :=
  du.toSection

/-- The field is square-integrable for the metric Hilbert-Schmidt norm. -/
abbrev memHilbertSchmidtL2
    (du : SquareIntegrableManifoldDifferentialField (I := I) (X := X) (E := E) g μ) :
    ManifoldDifferentialFieldMemHilbertSchmidtL2 (I := I) g μ du.toField :=
  du.memL2

instance : CoeFun
    (SquareIntegrableManifoldDifferentialField (I := I) (X := X) (E := E) g μ)
    (fun _ ↦ ManifoldDifferentialField I X E) where
  coe du := du.toField

/--
%%handwave
name:
  Almost-everywhere equality of square-integrable differential representatives
statement:
  Two square-integrable differential representatives define the same
  \(L^2\)-section when their values agree almost everywhere.
-/
def AeEq
    (du dv :
      SquareIntegrableManifoldDifferentialField (I := I) (X := X) (E := E) g μ) :
    Prop :=
  SquareIntegrableHilbertBundleSection.AeEq du dv

/--
%%handwave
name:
  Reflexivity of almost-everywhere equality for manifold differential fields
statement:
  Every square-integrable manifold differential representative agrees almost everywhere with itself.
proof:
  This is reflexivity of almost-everywhere equality for the underlying Hilbert-bundle section.
-/
theorem AeEq.refl
    (du :
      SquareIntegrableManifoldDifferentialField (I := I) (X := X) (E := E) g μ) :
    AeEq du du :=
  SquareIntegrableHilbertBundleSection.AeEq.refl du

/--
%%handwave
name:
  Symmetry of almost-everywhere equality for manifold differential fields
statement:
  If two square-integrable manifold differential representatives agree almost everywhere, they also agree in the reverse order.
proof:
  Apply symmetry of almost-everywhere equality for the underlying bundle sections.
-/
theorem AeEq.symm
    {du dv :
      SquareIntegrableManifoldDifferentialField (I := I) (X := X) (E := E) g μ}
    (h : AeEq du dv) : AeEq dv du :=
  SquareIntegrableHilbertBundleSection.AeEq.symm h

/--
%%handwave
name:
  Transitivity of almost-everywhere equality for manifold differential fields
statement:
  If \(A=B\) almost everywhere and \(B=C\) almost everywhere, then \(A=C\) almost everywhere as manifold differential fields.
proof:
  Apply transitivity of almost-everywhere equality for the underlying bundle sections.
-/
theorem AeEq.trans
    {du dv dw :
      SquareIntegrableManifoldDifferentialField (I := I) (X := X) (E := E) g μ}
    (h₁ : AeEq du dv) (h₂ : AeEq dv dw) : AeEq du dw := by
  exact SquareIntegrableHilbertBundleSection.AeEq.trans h₁ h₂

abbrev aeSetoid :
    Setoid
      (SquareIntegrableManifoldDifferentialField (I := I) (X := X) (E := E) g μ) :=
  SquareIntegrableHilbertBundleSection.aeSetoid
    (G := manifoldDifferentialHilbertBundleGeometry (I := I) (X := X) (E := E) g)
    (μ := μ)

end SquareIntegrableManifoldDifferentialField

/--
%%handwave
name:
  Square-integrability of a vector-valued differential field in charts
statement:
  A vector-valued differential field is square-integrable in charts if every
  coordinate pullback is square-integrable with respect to the coordinate
  pushforward of the surface measure.
-/
def SurfaceDifferentialFieldMemLpInCharts {X E : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [IsManifold SurfaceRealModel 1 X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X) (du : SurfaceDifferentialField X E) : Prop :=
  ∀ (e : OpenPartialHomeomorph X ℂ), e ∈ atlas ℂ X →
    MemLp (SurfaceDifferentialField.chartPullback du e) 2
      (Measure.map e (μ.restrict e.source))

/--
%%handwave
name:
  Intrinsic square-integrability of a differential field
statement:
  A vector-valued differential field is square-integrable when it is a
  measurable section of \(T^\ast X\otimes E\) and its metric
  Hilbert-Schmidt square norm is integrable.
-/
def SurfaceDifferentialFieldMemHilbertSchmidtL2 {X E : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [IsManifold SurfaceRealModel 1 X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : SmoothRiemannianMetricOnSurface X) (μ : Measure X)
    (du : SurfaceDifferentialField X E) : Prop :=
  ManifoldDifferentialFieldMemHilbertSchmidtL2
    (I := SurfaceRealModel) g.toManifoldMetric μ du

/--
%%handwave
name:
  Square-integrable differential representative
statement:
  A square-integrable differential representative is a measurable section of
  \(T^\ast X\otimes E\) with finite metric Hilbert-Schmidt energy.
-/
abbrev SquareIntegrableSurfaceDifferentialField {X E : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [IsManifold SurfaceRealModel 1 X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : SmoothRiemannianMetricOnSurface X) (μ : Measure X) : Type :=
  SquareIntegrableManifoldDifferentialField
    (I := SurfaceRealModel) (X := X) (E := E) g.toManifoldMetric μ

namespace SquareIntegrableSurfaceDifferentialField

variable {X E : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold SurfaceRealModel 1 X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {g : SmoothRiemannianMetricOnSurface X} {μ : Measure X}

/-- The underlying differential field. -/
abbrev toField
    (du : SquareIntegrableSurfaceDifferentialField (X := X) (E := E) g μ) :
    SurfaceDifferentialField X E :=
  du.toSection

/-- The field is square-integrable for the metric Hilbert-Schmidt norm. -/
abbrev memHilbertSchmidtL2
    (du : SquareIntegrableSurfaceDifferentialField (X := X) (E := E) g μ) :
    SurfaceDifferentialFieldMemHilbertSchmidtL2 g μ du.toField :=
  du.memL2

instance : CoeFun
    (SquareIntegrableSurfaceDifferentialField (X := X) (E := E) g μ)
    (fun _ ↦ SurfaceDifferentialField X E) where
  coe du := du.toField

/--
%%handwave
name:
  Almost-everywhere equality of square-integrable differential representatives
statement:
  Two square-integrable differential representatives define the same
  \(L^2\)-section when their values agree almost everywhere.
-/
def AeEq
    (du dv : SquareIntegrableSurfaceDifferentialField (X := X) (E := E) g μ) :
    Prop :=
  SquareIntegrableHilbertBundleSection.AeEq du dv

/--
%%handwave
name:
  Reflexivity of almost-everywhere equality for surface differential fields
statement:
  Every square-integrable surface differential representative agrees almost everywhere with itself.
proof:
  This is reflexivity for its underlying Hilbert-bundle section.
-/
theorem AeEq.refl
    (du : SquareIntegrableSurfaceDifferentialField (X := X) (E := E) g μ) :
    AeEq du du :=
  SquareIntegrableHilbertBundleSection.AeEq.refl du

/--
%%handwave
name:
  Symmetry of almost-everywhere equality for surface differential fields
statement:
  Almost-everywhere equality of square-integrable surface differential representatives is symmetric.
proof:
  Reverse the fiberwise equality on the full-measure set where it holds.
-/
theorem AeEq.symm
    {du dv : SquareIntegrableSurfaceDifferentialField (X := X) (E := E) g μ}
    (h : AeEq du dv) : AeEq dv du :=
  SquareIntegrableHilbertBundleSection.AeEq.symm h

/--
%%handwave
name:
  Transitivity of almost-everywhere equality for surface differential fields
statement:
  Almost-everywhere equality of square-integrable surface differential representatives is transitive.
proof:
  Combine the two fiberwise equalities on the intersection of their full-measure sets.
-/
theorem AeEq.trans
    {du dv dw : SquareIntegrableSurfaceDifferentialField (X := X) (E := E) g μ}
    (h₁ : AeEq du dv) (h₂ : AeEq dv dw) : AeEq du dw := by
  exact SquareIntegrableHilbertBundleSection.AeEq.trans h₁ h₂

abbrev aeSetoid :
    Setoid (SquareIntegrableSurfaceDifferentialField (X := X) (E := E) g μ) :=
  SquareIntegrableManifoldDifferentialField.aeSetoid
    (I := SurfaceRealModel) (X := X) (E := E) (g := g.toManifoldMetric) (μ := μ)

end SquareIntegrableSurfaceDifferentialField

/--
%%handwave
name:
  \(L^2\)-sections of the differential bundle
statement:
  The \(L^2\)-sections of \(T^\ast X\otimes E\) are square-integrable
  differential representatives modulo almost-everywhere equality.
-/
def SurfaceDifferentialL2Section {X E : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [IsManifold SurfaceRealModel 1 X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : SmoothRiemannianMetricOnSurface X) (μ : Measure X) : Type :=
  ManifoldDifferentialL2Section
    (I := SurfaceRealModel) (X := X) (E := E) g.toManifoldMetric μ

/--
%%handwave
name:
  Vector-valued weak derivative on a manifold region
statement:
  A vector-valued differential field is the weak derivative of a
  vector-valued map on a manifold region if, after pulling back to each
  coordinate chart, it satisfies the integration-by-parts identity against all
  compactly supported scalar coordinate tests and all model tangent
  directions.
-/
def IsWeakDerivativeOnManifoldRegionBundle {H X E : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H]
    [IsManifold I 1 X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set X) (u : X → E) (du : ManifoldDifferentialField I X E) : Prop :=
  ∀ (e : OpenPartialHomeomorph X H) (_he : e ∈ atlas H X)
    (φ : SmoothCompactlySupportedManifoldCoordinateFunction
      (manifoldChartRegion e U))
    (v : H),
    Integrable
        (fun z ↦ (fderiv ℝ (φ : H → ℝ) z v) • u (e.symm z))
        (MeasureTheory.volume.restrict (manifoldChartRegion e U)) ∧
      Integrable
        (fun z ↦ φ z • ManifoldDifferentialField.evalChart du e z v)
        (MeasureTheory.volume.restrict (manifoldChartRegion e U)) ∧
        ∫ z in manifoldChartRegion e U,
            (fderiv ℝ (φ : H → ℝ) z v) • u (e.symm z) ∂MeasureTheory.volume =
          -∫ z in manifoldChartRegion e U,
            φ z • ManifoldDifferentialField.evalChart du e z v ∂MeasureTheory.volume

/--
%%handwave
name:
  Vector-valued weak derivative on a manifold
statement:
  A vector-valued differential field is the weak derivative of a
  vector-valued map on the whole manifold if it is the weak derivative on the
  full manifold region.
-/
def IsWeakDerivativeOnManifoldBundle {H X E : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {I : ModelWithCorners ℝ H H} [TopologicalSpace X] [ChartedSpace H X]
    [MeasureSpace H]
    [MeasurableSpace X]
    [IsManifold I 1 X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (_μ : Measure X) (u : X → E) (du : ManifoldDifferentialField I X E) : Prop :=
  IsWeakDerivativeOnManifoldRegionBundle (I := I) (Set.univ : Set X) u du

/--
%%handwave
name:
  Vector-valued weak derivative on a surface region
statement:
  A vector-valued differential field is the weak derivative of a
  vector-valued map on a surface region if, after pulling back to each
  coordinate chart, it satisfies the integration-by-parts identity against all
  compactly supported scalar coordinate tests and all coordinate directions.
-/
def IsWeakDerivativeOnRegionBundle {X E : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel 1 X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set X) (u : X → E) (du : SurfaceDifferentialField X E) : Prop :=
  ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
    (φ : SmoothCompactlySupportedCoordinateFunction (surfaceChartRegion e U))
    (v : ℂ),
    Integrable
        (fun z ↦ (fderiv ℝ (φ : ℂ → ℝ) z v) • u (e.symm z))
        (MeasureTheory.volume.restrict (surfaceChartRegion e U)) ∧
      Integrable
        (fun z ↦ φ z • SurfaceDifferentialField.evalChart du e z v)
        (MeasureTheory.volume.restrict (surfaceChartRegion e U)) ∧
        ∫ z in surfaceChartRegion e U,
            (fderiv ℝ (φ : ℂ → ℝ) z v) • u (e.symm z) ∂MeasureTheory.volume =
          -∫ z in surfaceChartRegion e U,
            φ z • SurfaceDifferentialField.evalChart du e z v ∂MeasureTheory.volume

/--
%%handwave
name:
  Vector-valued weak derivative on a surface
statement:
  A vector-valued differential field is the weak derivative of a
  vector-valued map on the whole surface if it is the weak derivative on the
  full surface region.
-/
def IsWeakDerivativeOnSurfaceBundle {X E : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [IsManifold SurfaceRealModel 1 X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (_μ : Measure X) (u : X → E) (du : SurfaceDifferentialField X E) : Prop :=
  IsWeakDerivativeOnRegionBundle (Set.univ : Set X) u du

/--
%%handwave
name:
  Vector-valued surface \(W^{1,2}\) map
statement:
  A vector-valued representative-level surface \(W^{1,2}\) map is an
  \(L^2\) map into a real normed vector space together with a chartwise
  square-integrable vector-valued differential field which is its weak
  derivative.
-/
structure SobolevH1OnSurfaceWithValues {X E : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    [IsManifold SurfaceRealModel 1 X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X) where
  /-- The Sobolev representative. -/
  toFun : X → E
  /-- The weak derivative as a vector-valued differential field. -/
  weakDerivative : SurfaceDifferentialField X E
  /-- The map is square-integrable. -/
  memLp_toFun : MemLp toFun 2 μ
  /-- The weak derivative is square-integrable in coordinate charts. -/
  memLp_weakDerivative : SurfaceDifferentialFieldMemLpInCharts μ weakDerivative
  /-- The stored differential field is the weak derivative of the map. -/
  weakDerivative_is_derivative :
    IsWeakDerivativeOnSurfaceBundle μ toFun weakDerivative

namespace SobolevH1OnSurfaceWithValues

variable {X E : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [MeasurableSpace X] [BorelSpace X] [IsManifold SurfaceRealModel 1 X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure X}

instance : CoeFun (SobolevH1OnSurfaceWithValues (X := X) (E := E) μ)
    (fun _ ↦ X → E) where
  coe u := u.toFun

end SobolevH1OnSurfaceWithValues

namespace SurfaceCotangentField

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]

/--
%%handwave
name:
  Coordinate evaluation of a cotangent field
statement:
  The coordinate evaluation of a cotangent field applies the field at the
  surface point represented by a coordinate point to the corresponding
  coordinate tangent vector.
-/
noncomputable def evalChart (du : SurfaceCotangentField X)
    (e : OpenPartialHomeomorph X ℂ) (z v : ℂ) : ℝ :=
  du (e.symm z) (surfaceChartTangentVector e z v)

/--
%%handwave
name:
  Coordinate pullback of a cotangent field
statement:
  The coordinate pullback of a cotangent field is the cotangent field on the
  coordinate plane obtained by composing with the tangent map of the inverse
  coordinate chart.
-/
noncomputable def chartPullback (du : SurfaceCotangentField X)
    (e : OpenPartialHomeomorph X ℂ) : ℂ → ℂ →L[ℝ] ℝ :=
  fun z ↦ (du (e.symm z)).comp (surfaceChartTangentMap e z)

/--
%%handwave
name:
  Coordinate evaluation of a surface cotangent field
statement:
  For a surface chart \(e\), cotangent field \(\alpha\), and \(z,v\in\mathbb C\),
  \[
    \alpha^{e}_z(v)=\alpha_{e^{-1}(z)}\big(D(e^{-1})(z)v\big).
  \]
proof:
  This is the definition of coordinate evaluation of the cotangent field.
-/
@[simp]
theorem evalChart_eq (du : SurfaceCotangentField X)
    (e : OpenPartialHomeomorph X ℂ) (z v : ℂ) :
    evalChart du e z v = du (e.symm z) (surfaceChartTangentVector e z v) :=
  rfl

/--
%%handwave
name:
  Coordinate pullback of a cotangent field evaluated on a vector
statement:
  The coordinate pullback of a cotangent field \(\alpha\) satisfies
  \[
    (e^\ast\alpha)_z(v)=\alpha_{e^{-1}(z)}\big(D(e^{-1})(z)v\big).
  \]
proof:
  Expand the pullback as composition with the tangent map of the inverse chart.
-/
@[simp]
theorem chartPullback_apply (du : SurfaceCotangentField X)
    (e : OpenPartialHomeomorph X ℂ) (z v : ℂ) :
    chartPullback du e z v = evalChart du e z v :=
  rfl

/--
%%handwave
name:
  Coordinate representation of an intrinsic cotangent field
statement:
  An intrinsic cotangent field can be read in the preferred tangent
  coordinates at each point.
-/
noncomputable def toCoordinateField (du : SurfaceCotangentField X) :
    X → ℂ →L[ℝ] ℝ :=
  fun x ↦ du x

/--
%%handwave
name:
  Intrinsic cotangent field from coordinates
statement:
  A coordinate cotangent field determines an intrinsic cotangent field through
  the preferred tangent coordinates at each point.
-/
noncomputable def ofCoordinateField (du : X → ℂ →L[ℝ] ℝ) :
    SurfaceCotangentField X :=
  fun x ↦ du x

/--
%%handwave
name:
  Recovering a coordinate cotangent field
statement:
  Converting a coordinate cotangent field into an intrinsic field and then reading its preferred tangent coordinates recovers the original coordinate field.
proof:
  The two conversions leave every pointwise linear functional unchanged.
-/
@[simp]
theorem toCoordinateField_ofCoordinateField (du : X → ℂ →L[ℝ] ℝ) :
    toCoordinateField (ofCoordinateField du) = du :=
  rfl

/--
%%handwave
name:
  Recovering an intrinsic cotangent field
statement:
  Reading an intrinsic cotangent field in preferred tangent coordinates and rebuilding the intrinsic field recovers the original field.
proof:
  The pointwise coordinate conversions are inverse by definition.
-/
@[simp]
theorem ofCoordinateField_toCoordinateField (du : SurfaceCotangentField X) :
    ofCoordinateField (toCoordinateField du) = du :=
  rfl

end SurfaceCotangentField

namespace SmoothSurfaceCotangentSection

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold SurfaceRealModel ∞ X]

/--
%%handwave
name:
  Cotangent field underlying a smooth section
statement:
  A smooth cotangent section determines the underlying cotangent field by
  evaluating the section at each point.
-/
noncomputable def toField (du : SmoothSurfaceCotangentSection X) :
    SurfaceCotangentField X :=
  fun x ↦ du x

/--
%%handwave
name:
  Underlying field of a smooth cotangent section
statement:
  The cotangent field underlying a smooth cotangent section \(\alpha\) has value \(\alpha(x)\) at every point \(x\).
proof:
  The underlying field is obtained by pointwise evaluation.
-/
@[simp]
theorem toField_apply (du : SmoothSurfaceCotangentSection X) (x : X) :
    toField du x = du x :=
  rfl

end SmoothSurfaceCotangentSection

/--
%%handwave
name:
  Square-integrability of a cotangent field in charts
statement:
  A cotangent field is square-integrable in charts if every coordinate
  pullback is square-integrable with respect to the coordinate pushforward of
  the surface measure.
-/
def SurfaceCotangentFieldMemLpInCharts {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (du : SurfaceCotangentField X) : Prop :=
  ∀ (e : OpenPartialHomeomorph X ℂ), e ∈ atlas ℂ X →
    MemLp (SurfaceCotangentField.chartPullback du e) 2
      (Measure.map e (μ.restrict e.source))

/--
%%handwave
name:
  Intrinsic weak gradient on a surface region
statement:
  A cotangent field is the weak gradient of a function on a surface region if,
  after pulling it back to each coordinate chart, its coordinate components
  are the distributional first derivatives of the coordinate representative.
-/
def IsWeakGradientOnRegionBundle {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (U : Set X) (u : X → ℝ) (du : SurfaceCotangentField X) : Prop :=
  ∀ (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X)
    (φ : SmoothCompactlySupportedCoordinateFunction (surfaceChartRegion e U))
    (v : ℂ),
    Integrable
        (fun z ↦ u (e.symm z) * fderiv ℝ (φ : ℂ → ℝ) z v)
        (MeasureTheory.volume.restrict (surfaceChartRegion e U)) ∧
      Integrable
        (fun z ↦ SurfaceCotangentField.evalChart du e z v * φ z)
        (MeasureTheory.volume.restrict (surfaceChartRegion e U)) ∧
        ∫ z in surfaceChartRegion e U,
            u (e.symm z) * fderiv ℝ (φ : ℂ → ℝ) z v ∂MeasureTheory.volume =
          -∫ z in surfaceChartRegion e U,
            SurfaceCotangentField.evalChart du e z v * φ z ∂MeasureTheory.volume

/--
%%handwave
name:
  Intrinsic weak gradient on a surface
statement:
  A cotangent field is the weak gradient of a function on the whole surface if
  it is the weak gradient on the full surface region.
-/
def IsWeakGradientOnSurfaceBundle {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    (_μ : Measure X) (u : X → ℝ) (du : SurfaceCotangentField X) : Prop :=
  IsWeakGradientOnRegionBundle (Set.univ : Set X) u du

/--
%%handwave
name:
  Coordinate and intrinsic weak gradients on a region agree
statement:
  A coordinate cotangent field \(A_x:\mathbb C\to\mathbb R\) is a weak gradient of \(u\) on \(U\) exactly when the corresponding intrinsic cotangent field is.
proof:
  The intrinsic definition is the coordinate weak-gradient identity after the pointwise coordinate identification, so the two propositions coincide.
-/
@[simp]
theorem isWeakGradientOnRegionBundle_ofCoordinateField_iff {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (U : Set X) (u : X → ℝ) (du : X → ℂ →L[ℝ] ℝ) :
    IsWeakGradientOnRegionBundle U u (SurfaceCotangentField.ofCoordinateField du) ↔
      IsWeakGradientOnRegion U u du :=
  Iff.rfl

/--
%%handwave
name:
  Intrinsic weak gradients are characterized by their coordinate fields
statement:
  An intrinsic cotangent field \(\alpha\) is a weak gradient of \(u\) on \(U\) if and only if its preferred coordinate field is a coordinate weak gradient there.
proof:
  Unfold the intrinsic weak-gradient definition and the coordinate representation of \(\alpha\).
-/
@[simp]
theorem isWeakGradientOnRegionBundle_toCoordinateField_iff {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    (U : Set X) (u : X → ℝ) (du : SurfaceCotangentField X) :
    IsWeakGradientOnRegionBundle U u du ↔
      IsWeakGradientOnRegion U u (SurfaceCotangentField.toCoordinateField du) :=
  Iff.rfl

/--
%%handwave
name:
  Coordinate and intrinsic weak gradients on a surface agree
statement:
  A coordinate cotangent field is a weak gradient of \(u\) on the whole measured surface exactly when its associated intrinsic cotangent field is.
proof:
  Specialize the regional equivalence to the full surface.
-/
@[simp]
theorem isWeakGradientOnSurfaceBundle_ofCoordinateField_iff {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (u : X → ℝ) (du : X → ℂ →L[ℝ] ℝ) :
    IsWeakGradientOnSurfaceBundle μ u (SurfaceCotangentField.ofCoordinateField du) ↔
      IsWeakGradientOnSurface μ u du :=
  Iff.rfl

/--
%%handwave
name:
  Surface weak gradients are characterized by their coordinate fields
statement:
  An intrinsic cotangent field is a weak gradient of \(u\) on the measured surface if and only if its preferred coordinate field is a coordinate weak gradient.
proof:
  Unfold the whole-surface definition and apply the coordinate identification pointwise.
-/
@[simp]
theorem isWeakGradientOnSurfaceBundle_toCoordinateField_iff {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (u : X → ℝ) (du : SurfaceCotangentField X) :
    IsWeakGradientOnSurfaceBundle μ u du ↔
      IsWeakGradientOnSurface μ u (SurfaceCotangentField.toCoordinateField du) :=
  Iff.rfl

/--
%%handwave
name:
  Intrinsic surface \(W^{1,2}\) function
statement:
  An intrinsic representative-level surface \(W^{1,2}\) function is an
  \(L^2\) real-valued function together with a square-integrable cotangent
  field which is its weak gradient.
-/
structure SobolevH1OnSurfaceBundle {X : Type}
    [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) where
  /-- The Sobolev representative. -/
  toFun : X → ℝ
  /-- The weak gradient as a cotangent field. -/
  weakGradient : SurfaceCotangentField X
  /-- The function is square-integrable. -/
  memLp_toFun : MemLp toFun 2 μ
  /-- The weak gradient is square-integrable in coordinate charts. -/
  memLp_weakGradient : SurfaceCotangentFieldMemLpInCharts μ weakGradient
  /-- The stored cotangent field is the weak gradient of the function. -/
  weakGradient_is_gradient : IsWeakGradientOnSurfaceBundle μ toFun weakGradient

namespace SobolevH1OnSurfaceBundle

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X}

instance : CoeFun (SobolevH1OnSurfaceBundle μ) (fun _ ↦ X → ℝ) where
  coe u := u.toFun

end SobolevH1OnSurfaceBundle

end

end Uniformization
end JJMath
