import JJMath.ComplexProjective.Prerequisites.RiemannSurface
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.Topology.Algebra.GroupWithZero

/-!
# $(p,q)$-differentials on complex one-manifolds

This file constructs the complex line bundle
$K^p\otimes\overline K^{\,q}$ for arbitrary integer weights $p,q$.
The construction uses the derivative cocycle of the complex tangent bundle.
Beltrami differentials and quadratic differentials are the special cases
$(-1,1)$ and $(2,0)$, respectively.
-/

namespace JJMath

open Bundle MeasureTheory Set
open scoped Bundle Manifold Topology

noncomputable section

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [ComplexOneManifold X]

/--
%%handwave
name:
  Complex tangent transition scalar
statement:
  For two complex charts $z_i,z_j$ on a complex one-manifold, the
  transition map on the complex tangent line is multiplication by a scalar
  $a_{ij}(x)$. In coordinates this scalar is the complex derivative
  $$
    a_{ij}(x)=\frac{d(z_j\circ z_i^{-1})}{dz_i}(z_i(x)).
  $$
-/
noncomputable def complexTangentTransitionScalar
    (i j : atlas ℂ X) (x : X) : ℂ :=
  (tangentBundleCore 𝓘(ℂ) X).coordChange i j x 1

/--
%%handwave
name:
  Complex tangent transition is scalar multiplication
statement:
  The tangent-coordinate transition from a chart $i$ to a chart $j$
  sends $v\in\mathbb C$ to $v\,a_{ij}(x)$.
proof:
  A complex-linear map of the one-dimensional complex vector space
  $\mathbb C$ is determined by its value at $1$.
-/
theorem complexTangentTransition_apply
    (i j : atlas ℂ X) (x : X) (v : ℂ) :
    (tangentBundleCore 𝓘(ℂ) X).coordChange i j x v =
      v * complexTangentTransitionScalar i j x := by
  change _ =
    v * ((tangentBundleCore 𝓘(ℂ) X).coordChange i j x 1)
  simpa only [smul_eq_mul, mul_one] using
    ((tangentBundleCore 𝓘(ℂ) X).coordChange i j x).map_smul v 1

/--
%%handwave
name:
  Identity complex tangent transition scalar
statement:
  On the source of a complex chart $i$, its transition scalar to itself is
  $a_{ii}=1$.
proof:
  This is the identity-coordinate-change axiom of the tangent bundle.
-/
theorem complexTangentTransitionScalar_self
    (i : atlas ℂ X) {x : X} (hx : x ∈ i.1.source) :
    complexTangentTransitionScalar i i x = 1 := by
  exact (tangentBundleCore 𝓘(ℂ) X).coordChange_self i x hx 1

/--
%%handwave
name:
  Cocycle law for complex tangent transition scalars
statement:
  At a point common to three complex charts $i,j,k$, their tangent
  transition scalars satisfy
  $$
    a_{ij}(x)a_{jk}(x)=a_{ik}(x).
  $$
proof:
  Evaluate the tangent-bundle coordinate-change cocycle at $1$, and use
  that every complex-linear endomorphism of $\mathbb C$ is scalar
  multiplication.
-/
theorem complexTangentTransitionScalar_mul
    (i j k : atlas ℂ X) {x : X}
    (hx : x ∈ i.1.source ∩ j.1.source ∩ k.1.source) :
    complexTangentTransitionScalar i j x *
        complexTangentTransitionScalar j k x =
      complexTangentTransitionScalar i k x := by
  have h :=
    (tangentBundleCore 𝓘(ℂ) X).coordChange_comp i j k x hx 1
  rw [complexTangentTransition_apply] at h
  simpa [complexTangentTransitionScalar, mul_comm] using h

/--
%%handwave
name:
  Nonvanishing of a complex chart-transition derivative
statement:
  On the overlap of two complex charts $i,j$, the transition scalar
  $a_{ij}(x)$ is nonzero.
proof:
  Compose the transition from $i$ to $j$ with the reverse transition.
  Their scalar product is the identity scalar $1$.
-/
theorem complexTangentTransitionScalar_ne_zero
    (i j : atlas ℂ X) {x : X}
    (hx : x ∈ i.1.source ∩ j.1.source) :
    complexTangentTransitionScalar i j x ≠ 0 := by
  intro hzero
  have hmul :=
    complexTangentTransitionScalar_mul i j i
      (x := x) ⟨hx, hx.1⟩
  rw [hzero, zero_mul] at hmul
  have hself := complexTangentTransitionScalar_self i hx.1
  exact zero_ne_one (hmul.trans hself)

/--
%%handwave
name:
  Continuity of complex tangent transition scalars
statement:
  The scalar $a_{ij}$ associated with a complex chart transition is
  continuous on the overlap of the two charts.
proof:
  Tangent-bundle coordinate changes are continuous families of
  complex-linear maps. Evaluate that family continuously at $1$.
-/
theorem complexTangentTransitionScalar_continuousOn
    (i j : atlas ℂ X) :
    ContinuousOn (complexTangentTransitionScalar i j)
      (i.1.source ∩ j.1.source) := by
  exact
    ((tangentBundleCore 𝓘(ℂ) X).continuousOn_coordChange i j).clm_apply
      continuousOn_const

/--
%%handwave
name:
  Transition scalar of the $(p,q)$-differential line
statement:
  For $p,q\in\mathbb Z$, the coordinate change on
  $K^p\otimes\overline K^{\,q}$ from chart $i$ to chart $j$ is
  multiplication by
  $$
    a_{ij}^{-p}\overline{a_{ij}}^{-q}.
  $$
  Thus a coefficient written in chart $i$ is converted to its coefficient
  in chart $j$.
-/
noncomputable def pqDifferentialTransitionScalar
    (p q : ℤ) (i j : atlas ℂ X) (x : X) : ℂ :=
  (complexTangentTransitionScalar i j x) ^ (-p) *
    (starRingEnd ℂ (complexTangentTransitionScalar i j x)) ^ (-q)

/--
%%handwave
name:
  Identity transition for the $(p,q)$-differential line
statement:
  The transition scalar of $K^p\otimes\overline K^{\,q}$ from a chart to
  itself is $1$.
proof:
  Substitute $a_{ii}=1$ into the integer-power transition formula.
-/
theorem pqDifferentialTransitionScalar_self
    (p q : ℤ) (i : atlas ℂ X) {x : X}
    (hx : x ∈ i.1.source) :
    pqDifferentialTransitionScalar p q i i x = 1 := by
  simp [pqDifferentialTransitionScalar,
    complexTangentTransitionScalar_self i hx]

/--
%%handwave
name:
  Cocycle law for $(p,q)$-differential transitions
statement:
  On a triple chart overlap, the transition scalars of
  $K^p\otimes\overline K^{\,q}$ satisfy
  $$
    t_{ij}^{p,q}(x)t_{jk}^{p,q}(x)=t_{ik}^{p,q}(x).
  $$
proof:
  Apply integer powers and complex conjugation to
  $a_{ij}a_{jk}=a_{ik}$, then rearrange the scalar factors.
-/
theorem pqDifferentialTransitionScalar_mul
    (p q : ℤ) (i j k : atlas ℂ X) {x : X}
    (hx : x ∈ i.1.source ∩ j.1.source ∩ k.1.source) :
    pqDifferentialTransitionScalar p q i j x *
        pqDifferentialTransitionScalar p q j k x =
      pqDifferentialTransitionScalar p q i k x := by
  have ha := complexTangentTransitionScalar_mul i j k hx
  simp only [pqDifferentialTransitionScalar]
  rw [← ha]
  simp only [map_mul, mul_zpow]
  ring

/--
%%handwave
name:
  Continuity of $(p,q)$-differential transitions
statement:
  The transition scalar of $K^p\otimes\overline K^{\,q}$ is continuous on
  every complex chart overlap.
proof:
  The tangent transition scalar is continuous and nowhere zero. Integer
  powers, complex conjugation, and multiplication therefore preserve
  continuity on the overlap.
-/
theorem pqDifferentialTransitionScalar_continuousOn
    (p q : ℤ) (i j : atlas ℂ X) :
    ContinuousOn (pqDifferentialTransitionScalar p q i j)
      (i.1.source ∩ j.1.source) := by
  have ha := complexTangentTransitionScalar_continuousOn i j
  have hane :
      ∀ x ∈ i.1.source ∩ j.1.source,
        complexTangentTransitionScalar i j x ≠ 0 :=
    fun _ hx ↦ complexTangentTransitionScalar_ne_zero i j hx
  exact
    (ha.zpow₀ (-p) (fun x hx ↦ Or.inl (hane x hx))).mul
      ((ha.star).zpow₀ (-q)
        (fun x hx ↦ Or.inl (by simpa using hane x hx)))

/--
%%handwave
name:
  The $(p,q)$-differential line bundle
statement:
  For a complex one-manifold $X$ and $p,q\in\mathbb Z$, the line bundle
  $K^p\otimes\overline K^{\,q}$ is the complex line bundle whose chart
  transition from $i$ to $j$ is multiplication by
  $a_{ij}^{-p}\overline{a_{ij}}^{-q}$.
-/
noncomputable def pqDifferentialBundleCore (p q : ℤ) :
    VectorBundleCore ℂ X ℂ (atlas ℂ X) where
  baseSet i := i.1.source
  isOpen_baseSet i := i.1.open_source
  indexAt := achart ℂ
  mem_baseSet_at x := mem_chart_source ℂ x
  coordChange i j x :=
    ContinuousLinearMap.lsmul ℂ ℂ
      (pqDifferentialTransitionScalar p q i j x)
  coordChange_self i x hx v := by
    simp [pqDifferentialTransitionScalar_self p q i hx]
  continuousOn_coordChange i j :=
    (ContinuousLinearMap.lsmul ℂ ℂ).continuous.comp_continuousOn
      (pqDifferentialTransitionScalar_continuousOn p q i j)
  coordChange_comp i j k x hx v := by
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    rw [← mul_assoc,
      mul_comm (pqDifferentialTransitionScalar p q j k x)
        (pqDifferentialTransitionScalar p q i j x),
      pqDifferentialTransitionScalar_mul p q i j k hx]

/--
%%handwave
name:
  Fiber of the $(p,q)$-differential line
statement:
  The fiber of $K^p\otimes\overline K^{\,q}$ at $x$ is a
  one-dimensional complex vector space.
-/
abbrev PQDifferentialFiber (p q : ℤ) (X : Type*)
    [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexOneManifold X]
    (x : X) : Type :=
  (pqDifferentialBundleCore (X := X) p q).Fiber x

/--
%%handwave
name:
  $(p,q)$-differential on a complex one-manifold
statement:
  A $(p,q)$-differential on $X$ is a section of the complex line bundle
  $K^p\otimes\overline K^{\,q}$.
-/
abbrev PQDifferential (p q : ℤ) (X : Type*)
    [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexOneManifold X] : Type _ :=
  ∀ x : X, PQDifferentialFiber p q X x

namespace PQDifferential

/--
%%handwave
name:
  Coordinate coefficient of a $(p,q)$-differential at a point
statement:
  If $x$ lies in a complex chart $i$, the coefficient of a
  $(p,q)$-differential $\omega$ at $x$ in chart $i$ is obtained by
  applying the line-bundle trivialization associated with $i$.
-/
noncomputable def inChartAt {p q : ℤ}
    (ω : PQDifferential p q X) (i : atlas ℂ X) (x : X) : ℂ :=
  (pqDifferentialBundleCore (X := X) p q).coordChange
    ((pqDifferentialBundleCore (X := X) p q).indexAt x) i x (ω x)

/--
%%handwave
name:
  Coordinate representative of a $(p,q)$-differential
statement:
  In a complex chart $i$, a $(p,q)$-differential $\omega$ is
  represented by the scalar field
  $$
    z\longmapsto \omega_i(z)
  $$
  obtained by trivializing $\omega$ at $i^{-1}(z)$.
-/
noncomputable def inChart {p q : ℤ}
    (ω : PQDifferential p q X) (i : atlas ℂ X) (z : ℂ) : ℂ :=
  inChartAt ω i (i.1.symm z)

/--
%%handwave
name:
  Coordinate transition of a $(p,q)$-differential
statement:
  At a point $x$ common to complex charts $i,j$, the coordinate
  coefficients of a $(p,q)$-differential satisfy
  $$
    \omega_j(x)
      =a_{ij}(x)^{-p}\overline{a_{ij}(x)}^{-q}\omega_i(x).
  $$
proof:
  Apply the line-bundle coordinate-change cocycle from the preferred
  trivialization at $x$, through chart $i$, to chart $j$.
-/
theorem inChartAt_transition {p q : ℤ}
    (ω : PQDifferential p q X) (i j : atlas ℂ X) {x : X}
    (hxi : x ∈ i.1.source) (hxj : x ∈ j.1.source) :
    pqDifferentialTransitionScalar p q i j x * inChartAt ω i x =
      inChartAt ω j x := by
  let Z := pqDifferentialBundleCore (X := X) p q
  have hidx : x ∈ Z.baseSet (Z.indexAt x) := Z.mem_baseSet_at x
  have hcomp :=
    Z.coordChange_comp (Z.indexAt x) i j x
      ⟨⟨hidx, hxi⟩, hxj⟩ (ω x)
  simpa [Z, inChartAt, pqDifferentialBundleCore] using hcomp

/--
%%handwave
name:
  Global $(p,q)$-differential induced from one chart
statement:
  A scalar field $f$ in a complex chart $i$ determines a global
  $(p,q)$-differential by using $f$ on the source of $i$, transporting
  it into the intrinsic line fiber, and taking the zero section outside that
  chart source.
-/
noncomputable def ofChart {p q : ℤ}
    (i : atlas ℂ X) (f : ℂ → ℂ) : PQDifferential p q X := by
  classical
  let Z := pqDifferentialBundleCore (X := X) p q
  exact fun x ↦
    if hx : x ∈ i.1.source then
      Z.coordChange i (Z.indexAt x) x (f (i.1 x))
    else 0

/--
%%handwave
name:
  Coordinate representative of a differential induced from a chart
statement:
  If the global $(p,q)$-differential induced from a scalar field $f$ in
  chart $i$ is written again in chart $i$, its coefficient is $f(z)$
  at every $z$ in the chart target.
proof:
  The transport from chart $i$ to the preferred trivialization and back to
  chart $i$ cancels by the line-bundle cocycle.
-/
theorem inChart_ofChart {p q : ℤ}
    (i : atlas ℂ X) (f : ℂ → ℂ) {z : ℂ}
    (hz : z ∈ i.1.target) :
    inChart (ofChart i f : PQDifferential p q X) i z = f z := by
  let Z := pqDifferentialBundleCore (X := X) p q
  have hx : i.1.symm z ∈ i.1.source := i.1.map_target hz
  have hidx : i.1.symm z ∈ Z.baseSet (Z.indexAt (i.1.symm z)) :=
    Z.mem_baseSet_at _
  change
    Z.coordChange (Z.indexAt (i.1.symm z)) i (i.1.symm z)
      ((ofChart i f : PQDifferential p q X) (i.1.symm z)) = f z
  rw [show
    (ofChart i f : PQDifferential p q X) (i.1.symm z) =
      Z.coordChange i (Z.indexAt (i.1.symm z)) (i.1.symm z)
        (f (i.1 (i.1.symm z))) by
      simp [ofChart, Z, hx]]
  rw [Z.coordChange_comp i (Z.indexAt (i.1.symm z)) i]
  · rw [Z.coordChange_self]
    · rw [i.1.right_inv hz]
    · exact hx
  · exact ⟨⟨hx, hidx⟩, hx⟩

/--
%%handwave
name:
  Measurable $(p,q)$-differential
statement:
  A $(p,q)$-differential is measurable when its scalar representative in
  every complex chart is measurable up to planar null sets on that chart's
  coordinate domain.
-/
def IsAEStronglyMeasurable {p q : ℤ}
    (ω : PQDifferential p q X) : Prop :=
  ∀ i : atlas ℂ X,
    AEStronglyMeasurable (inChart ω i)
      (volume.restrict i.1.target)

end PQDifferential

/--
%%handwave
name:
  Beltrami differential on a complex one-manifold
statement:
  A Beltrami differential on $X$ is a section of
  $K^{-1}\otimes\overline K$, equivalently a $(-1,1)$-differential.
  In a coordinate $z$, it is written
  $$
    \mu(z)\,\frac{d\overline z}{dz}.
  $$
-/
abbrev BeltramiDifferential (X : Type*)
    [TopologicalSpace X] [ChartedSpace ℂ X] [ComplexOneManifold X] : Type _ :=
  PQDifferential (-1) 1 X

namespace BeltramiDifferential

/--
%%handwave
name:
  Measurable Beltrami differential
statement:
  A Beltrami differential is measurable when its scalar coefficient is
  measurable up to planar null sets in every complex coordinate.
-/
def IsAEStronglyMeasurable
    (μ : BeltramiDifferential X) : Prop :=
  PQDifferential.IsAEStronglyMeasurable μ

/--
%%handwave
name:
  Almost-everywhere convergence of Beltrami differentials
statement:
  A family of Beltrami differentials $\mu_\alpha$ converges almost
  everywhere to $\mu$ along a filter $\mathcal F$ when, in every complex
  chart $i$,
  $$
    (\mu_\alpha)_i(z)\longrightarrow\mu_i(z)
  $$
  along $\mathcal F$ for almost every coordinate point $z$ in the chart.
-/
def AETendsto {ι : Type*}
    (μs : ι → BeltramiDifferential X) (l : Filter ι)
    (μ : BeltramiDifferential X) : Prop :=
  ∀ i : atlas ℂ X,
    ∀ᵐ z ∂(volume.restrict i.1.target),
      Filter.Tendsto (fun a ↦ PQDifferential.inChart (μs a) i z) l
        (nhds (PQDifferential.inChart μ i z))

/--
%%handwave
name:
  Essential norm bound for a Beltrami differential
statement:
  A Beltrami differential $\mu$ has essential norm at most $k$ when
  $$
    |\mu_i(z)|\le k
  $$
  almost everywhere in every complex chart $i$. The condition is
  coordinate-independent because the transition factor
  $a_{ij}/\overline{a_{ij}}$ has norm $1$.
-/
def HasEssentialNormLE
    (μ : BeltramiDifferential X) (k : ℝ) : Prop :=
  ∀ i : atlas ℂ X,
    ∀ᵐ z ∂(volume.restrict i.1.target),
      ‖PQDifferential.inChart μ i z‖ ≤ k

end BeltramiDifferential

end

end JJMath
